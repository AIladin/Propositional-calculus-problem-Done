from enum import Enum
from collections import namedtuple, deque


_op = namedtuple('OperatorsInfo', ['name', 'call'])


def _obj(x):
    assert type(x) == bool, 'Wrong objection argument'
    return not x


def _imp(x, y):
    assert type(x) == type(y) == bool, 'Wrong implication argument'
    if not x or y:
        return True
    else:
        return False


class Operators(Enum):
    Objection = _op('!', _obj)
    Implication = _op('->', _imp)


class PCF:
    """
    Propositional calculus formula
    """
    def __init__(self, *variables, main_op=None, by_mp=False, is_axiom=False, left=None, right=None,
                 clauses=(), index=None, is_hypot=False):
        self.main_op = main_op

        self.variables = set(variables)

        self.left_sub_formula = left
        self.right_sub_formula = right

        self.is_by_MP = by_mp
        self.is_axiom = is_axiom
        self.is_hypot = is_hypot

        self.clauses = clauses

        self.index = index

        self._str_rep = None
        self._hash = None
        self._stack = deque()

    def obj(self):
        return PCF(*self.variables, main_op=Operators.Objection, right=self)

    def imp(self, other):
        return PCF(*self.variables.union(other.variables), main_op=Operators.Implication, left=self, right=other)

    def __call__(self, vector, variable_order: list):
        if not self.main_op:
            try:
                return vector[variable_order.index(*self.variables)]
            except (ValueError, IndexError):
                raise ValueError('Wrong vector {} or variable order {}'.format(vector, variable_order))
        elif self.main_op == Operators.Objection:
            return self.main_op.value.call(self.right_sub_formula(vector, variable_order))
        elif self.main_op == Operators.Implication:
            return self.main_op.value.call(self.left_sub_formula(vector, variable_order),
                                           self.right_sub_formula(vector, variable_order))

    def __str__(self):
        if not self._str_rep:
            if not self.main_op:
                self._str_rep = str(*self.variables)

            elif self.main_op == Operators.Objection:
                self._str_rep = self.main_op.value.name+str(self.right_sub_formula)

            elif self.main_op == Operators.Implication:
                self._str_rep = '('+str(self.left_sub_formula) + self.main_op.value.name\
                                + str(self.right_sub_formula) + ')'
        return self._str_rep

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.__hash__() == other.__hash__()

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        if not self._hash:
            self._hash = str(self).__hash__()
        return self._hash

    def get_info(self):
        _t = self.clauses

        if self.is_axiom:
            return 'F_{}={}: {} for {}\n'.format(
                str(self.index), str(self), str(_t[0]), str(_t[1]))

        if self.is_by_MP:
            return 'F_{}={}: {} for F_{} and F_{}\n'.format(
                str(self.index), str(self), str(_t[0]), str(_t[1][0].index), str(_t[1][1].index))

        if self.is_hypot:
            return 'F_{}={}: hypothesis\n'.format(
                str(self.index), str(self))

    def get_stack(self):
        if len(self._stack) == 0:
            self._stack.appendleft(self)

            if self.left_sub_formula:
                self._stack = self.left_sub_formula.get_stack() + self._stack
            if self.right_sub_formula:
                self._stack = self.right_sub_formula.get_stack() + self._stack
        return self._stack


if __name__ == '__main__':
    a = PCF('a')
    t = a.obj()
    t = a.imp(t)
    z = PCF('z').imp(t).obj()
    for e in z.get_stack():
        print(e)
