from collections import namedtuple
from enum import Enum
from PCF.PropCalcFormula import PCF, Operators
from copy import deepcopy
from itertools import product

proof = []

# ------------------------------Axiom Block------------------------------ #
_enum_helper = namedtuple('AxiomInfo', ['name', 'call'])


def _a1(f: PCF, g: PCF, indexation=False):
    t = f.imp(g.imp(f))
    t.is_axiom = True
    t.clauses = (Axioms.A1.value.name, (f, g))
    if indexation:
        t.index = len(proof)
        proof.append(t)
    return t


def _a2(f: PCF, g: PCF, h: PCF, indexation=False):
    t = f.imp(g.imp(h)).imp(f.imp(g).imp(f.imp(h)))
    t.is_axiom = True
    t.clauses = (Axioms.A2.value.name, (f, g, h))
    if indexation:
        t.index = len(proof)
        proof.append(t)
    return t


def _a3(g: PCF, f: PCF, indexation=False):
    t = g.obj().imp(f.obj()).imp((g.obj().imp(f)).imp(g))
    t.is_axiom = True
    t.clauses = (Axioms.A3.value.name, (g, f))
    if indexation:
        t.index = len(proof)
        proof.append(t)
    return t


class Axioms(Enum):
    A1 = _enum_helper('A1', _a1)
    A2 = _enum_helper('A2', _a2)
    A3 = _enum_helper('A3', _a3)

# ------------------------------MP Block------------------------------ #


def _mp(f: PCF, g: PCF, indexation=False):
    if g.main_op == Operators.Implication:
        if f == g.left_sub_formula:
            t = g.right_sub_formula
            t.is_by_MP = True
            t.clauses = (Rules.MP.value.name, (f, g))
            if indexation:
                t.index = len(proof)
                proof.append(t)
            return t
        else:
            raise ValueError('Wrong MP usage')
    else:
        raise ValueError('Wrong MP usage')


class Rules(Enum):
    MP = _enum_helper('MP', _mp)
# ------------------------------L-teorem Block------------------------------ #


def _l(f: PCF, indexation=False):
    proof_seq = []
    if f.main_op == Operators.Implication and f.left_sub_formula == f.right_sub_formula:
        proof_seq.append(Axioms.A2.value.call(f.left_sub_formula, f,
                                              f.left_sub_formula, indexation=indexation))
        proof_seq.append(Axioms.A1.value.call(f.left_sub_formula, f, indexation=indexation))
        proof_seq.append(Rules.MP.value.call(proof_seq[1], proof_seq[0], indexation=indexation))
        proof_seq.append(Axioms.A1.value.call(f.left_sub_formula, f.left_sub_formula, indexation=indexation))
        proof_seq.append(Rules.MP.value.call(proof_seq[3], proof_seq[2], indexation=indexation))
        return proof_seq
    else:
        raise ValueError("wrong L usage")
# ------------------------------S1-S2 Block------------------------------ #


def _deduction(hypot, f: PCF, given_proof_seq, indexation=False):
    if indexation:
        for i in range(len(hypot)):
            if not hypot[i].is_by_MP or not hypot[i].is_axiom:
                if hypot[i] in proof:
                    element = deepcopy(hypot[i])
                else:
                    element = hypot[i]
                element.index = len(proof)
                element.is_hypot = True
            # FAKE REFERENCE BEFORE ASSIGNMENT WARNING
            proof.append(element)

    new_proof_seq = []

    for Fi in given_proof_seq:
        if Fi in hypot or Fi.is_axiom:
            if indexation:
                Fi.index = len(proof)
                proof.append(Fi)
            new_proof_seq.append(Fi)
            new_proof_seq.append(Axioms.A1.value.call(Fi, f, indexation=indexation))
            new_proof_seq.append(Rules.MP.value.call(Fi, new_proof_seq[-1], indexation=indexation))

        elif Fi == f:
            new_proof_seq += Theorem.L.value.call(Fi.imp(Fi), indexation=indexation)

        elif Fi.is_by_MP:
            prev_fr, prev_fs = Fi.clauses[1]
            found_fr = False
            found_fs = False
            for element in reversed(new_proof_seq):
                if element.main_op == Operators.Implication:
                    if element.right_sub_formula == prev_fr and element.left_sub_formula == f:
                        f_fr = element
                        found_fr = True

                    if element.right_sub_formula == prev_fs and element.left_sub_formula == f:
                        f_fs = element
                        found_fs = True

                    if found_fs and found_fr:
                        break

            new_proof_seq.append(Axioms.A2.value.call(f, prev_fr, Fi, indexation=indexation))
            # I NEED HERE REFERENCE BEFORE ASSIGNMENT WARNING
            try:
                new_proof_seq.append(Rules.MP.value.call(f_fs, new_proof_seq[-1], indexation=indexation))
                new_proof_seq.append(Rules.MP.value.call(f_fr, new_proof_seq[-1], indexation=indexation))
            except ValueError:
                raise ValueError('Wrong Deduction usage')

    return new_proof_seq


# ------------------------------S1-S2 Block------------------------------ #

def _s1(a: PCF, b: PCF, indexation=False):
    if a.main_op == b.main_op == Operators.Implication and a.right_sub_formula == b.left_sub_formula:
        proof_seq = []
        _a = a.left_sub_formula
        hypot = [a, b]
        proof_seq += hypot
        proof_seq.append(_a)
        proof_seq.append(Rules.MP.value.call(_a, a))
        proof_seq.append(Rules.MP.value.call(proof_seq[-1], b))
        return Theorem.Deduction.value.call(hypot, _a, proof_seq, indexation=indexation)

    else:
        raise ValueError("Wrong S1 usage")


def _s2(a: PCF, b: PCF, indexation=False):
    if a.main_op == a.right_sub_formula.main_op == Operators.Implication and a.right_sub_formula.left_sub_formula == b:
        proof_seq = []
        hypot = [a, b]
        _a = a.left_sub_formula
        proof_seq += hypot
        proof_seq.append(_a)
        proof_seq.append(Rules.MP.value.call(proof_seq[2], proof_seq[0]))
        proof_seq.append(Rules.MP.value.call(proof_seq[1], proof_seq[3]))
        return Theorem.Deduction.value.call(hypot, _a, proof_seq, indexation=indexation)

    else:
        raise ValueError("Wrong S2 usage")


class Syllogism(Enum):
    S1 = _enum_helper('S1', _s1)
    S2 = _enum_helper('S2', _s2)

# ------------------------------T1-T7 Block------------------------------ #


def _t1(a: PCF, indexation=False):

    if a.main_op == Operators.Implication and\
         a.left_sub_formula.right_sub_formula.right_sub_formula == a.right_sub_formula\
         and a.left_sub_formula.main_op == a.left_sub_formula.right_sub_formula.main_op == Operators.Objection:

        proof_seq = list()
        proof_seq.append(Axioms.A3.value.call(a.right_sub_formula, a.right_sub_formula.obj(), indexation=indexation))
        proof_seq += Theorem.L.value.call(a.right_sub_formula.obj().imp(a.right_sub_formula.obj()),
                                          indexation=indexation)
        proof_seq += Syllogism.S2.value.call(proof_seq[0], proof_seq[-1], indexation=indexation)
        proof_seq.append(Axioms.A1.value.call(a.right_sub_formula.obj().obj(),
                                              a.right_sub_formula.obj(), indexation=indexation))
        proof_seq += Syllogism.S1.value.call(proof_seq[-1], proof_seq[-2], indexation=indexation)
        return proof_seq
    else:
        raise ValueError("Wrong T1 usage")


def _t2(a: PCF, indexation=False):
    if a.main_op == Operators.Implication and\
         a.left_sub_formula == a.right_sub_formula.right_sub_formula.right_sub_formula and\
         a.right_sub_formula.main_op == a.right_sub_formula.right_sub_formula.main_op == Operators.Objection:
        proof_seq = []
        _a = a.left_sub_formula
        proof_seq.append(Axioms.A3.value.call(a.right_sub_formula, a.left_sub_formula, indexation=indexation))
        proof_seq += Theorem.T1.value.call(_a.obj().obj().obj().imp(_a.obj()), indexation=indexation)
        proof_seq.append(Rules.MP.value.call(proof_seq[-1], proof_seq[0], indexation=indexation))
        tmp = proof_seq[-1]
        proof_seq.append(Axioms.A1.value.call(_a, a.right_sub_formula.obj(), indexation=indexation))
        proof_seq += Syllogism.S1.value.call(proof_seq[-1], tmp, indexation=indexation)
        return proof_seq
    else:
        raise ValueError("Wrong T2 usage")


def _t3(a: PCF, indexation=False):
    if a.main_op == a.right_sub_formula.main_op == Operators.Implication and\
          a.left_sub_formula.main_op == Operators.Objection and\
          a.left_sub_formula.right_sub_formula == a.right_sub_formula.left_sub_formula:
        _a = a.right_sub_formula.left_sub_formula
        _b = a.right_sub_formula.right_sub_formula
        hypot = [a.left_sub_formula]
        proof_seq = hypot[:]
        proof_seq.append(a.right_sub_formula.left_sub_formula)
        proof_seq.append(Axioms.A1.value.call(_a, _b.obj()))
        proof_seq.append(Rules.MP.value.call(proof_seq[1], proof_seq[-1]))
        proof_seq.append(Axioms.A1.value.call(_a.obj(), _b.obj()))
        proof_seq.append(Rules.MP.value.call(proof_seq[0], proof_seq[-1]))
        proof_seq.append(Axioms.A3.value.call(_b, _a))
        proof_seq.append(Rules.MP.value.call(proof_seq[-2], proof_seq[-1]))
        proof_seq.append(Rules.MP.value.call(proof_seq[3], proof_seq[7]))
        proof_seq = Theorem.Deduction.value.call(hypot, _a, proof_seq)
        proof_seq = Theorem.Deduction.value.call([], a.left_sub_formula, proof_seq, indexation=indexation)
        return proof_seq

    else:
        raise ValueError("Wrong T3 usage")


def _t4(a: PCF, indexation=False):

    if a.main_op == a.left_sub_formula.main_op == a.right_sub_formula.main_op == Operators.Implication and\
         a.left_sub_formula.left_sub_formula.right_sub_formula == a.right_sub_formula.right_sub_formula and\
         a.left_sub_formula.right_sub_formula.right_sub_formula == a.right_sub_formula.left_sub_formula:
        hypot = [a.left_sub_formula]
        _a = a.right_sub_formula.left_sub_formula
        _b = a.right_sub_formula.right_sub_formula
        proof_seq = hypot[:]
        proof_seq.append(a.right_sub_formula.left_sub_formula)
        proof_seq.append(Axioms.A3.value.call(_b, _a))
        proof_seq.append(Rules.MP.value.call(proof_seq[0], proof_seq[2]))
        proof_seq.append(Axioms.A1.value.call(_a, _b.obj()))
        proof_seq += Syllogism.S1.value.call(proof_seq[4], proof_seq[3])
        proof_seq.append(Rules.MP.value.call(proof_seq[1], proof_seq[-1]))
        proof_seq = Theorem.Deduction.value.call(hypot, _a, proof_seq)
        t = proof_seq
        proof_seq = Theorem.Deduction.value.call([], a.left_sub_formula, t, indexation=indexation)
        return proof_seq

    else:
        raise ValueError("Wrong T4 usage")


def _t5(a: PCF, indexation=False):
    if a.main_op == a.left_sub_formula.main_op == a.right_sub_formula.main_op == Operators.Implication and\
         a.right_sub_formula.left_sub_formula.right_sub_formula == a.left_sub_formula.right_sub_formula and\
         a.right_sub_formula.right_sub_formula.right_sub_formula == a.left_sub_formula.left_sub_formula and\
         a.right_sub_formula.left_sub_formula.main_op ==\
         a.right_sub_formula.right_sub_formula.main_op == Operators.Objection:
        _a = a.left_sub_formula.left_sub_formula
        _b = a.left_sub_formula.right_sub_formula
        proof_seq = list()
        proof_seq.append(a.left_sub_formula)
        proof_seq += Theorem.T1.value.call(_a.obj().obj().imp(_a))
        proof_seq += Syllogism.S1.value.call(proof_seq[-1], proof_seq[0])
        tmp = proof_seq[-1]
        proof_seq += Theorem.T2.value.call(_b.imp(_b.obj().obj()))
        proof_seq += Syllogism.S1.value.call(tmp, proof_seq[-1])
        tmp = proof_seq[-1]
        x = (_a.obj().obj().imp(_b.obj().obj())).imp(a.right_sub_formula)
        proof_seq += Theorem.T4.value.call(x)
        proof_seq.append(Rules.MP.value.call(tmp, proof_seq[-1]))
        proof_seq = Theorem.Deduction.value.call([], a.left_sub_formula, proof_seq, indexation=indexation)
        return proof_seq
    else:
        raise ValueError("Wrong T5 usage")


def _t6(a: PCF, indexation=False):
    if a.left_sub_formula == a.right_sub_formula.right_sub_formula.right_sub_formula.left_sub_formula and\
         a.right_sub_formula.left_sub_formula.right_sub_formula\
         == a.right_sub_formula.right_sub_formula.right_sub_formula.right_sub_formula and\
         a.main_op == a.right_sub_formula.main_op == a.right_sub_formula.right_sub_formula.right_sub_formula.main_op\
         == Operators.Implication:
        _f = a.left_sub_formula
        _g = a.right_sub_formula.left_sub_formula.right_sub_formula
        proof_seq = []
        hypot = [a.left_sub_formula]
        proof_seq += hypot
        proof_seq.append(a.right_sub_formula.left_sub_formula)
        x = (_f.imp(_g).imp(_g)).imp(_g.obj().imp((_f.imp(_g)).obj()))
        proof_seq += Theorem.T5.value.call(x)
        tmp = proof_seq[-1]
        proof_seq += Theorem.L.value.call(_f.imp(_g).imp(_f.imp(_g)))
        proof_seq += Syllogism.S2.value.call(proof_seq[-1], _f)
        proof_seq.append(Rules.MP.value.call(proof_seq[-1], tmp))
        proof_seq.append(Rules.MP.value.call(proof_seq[1], proof_seq[-1]))
        proof_seq = Theorem.Deduction.value.call(hypot, a.right_sub_formula.left_sub_formula, proof_seq)
        proof_seq = Theorem.Deduction.value.call([], _f, proof_seq, indexation=indexation)
        return proof_seq

    else:
        raise ValueError('T6 wrong usage')


def _t7(a: PCF, indexation=False):
    if a.main_op == Operators.Implication == a.left_sub_formula.main_op\
             == a.right_sub_formula.main_op == a.right_sub_formula.left_sub_formula.main_op and\
             a.left_sub_formula.left_sub_formula ==\
             a.right_sub_formula.left_sub_formula.left_sub_formula.right_sub_formula and\
             a.left_sub_formula.right_sub_formula ==\
            a.right_sub_formula.right_sub_formula == a.right_sub_formula.left_sub_formula.right_sub_formula:
        _a = a.left_sub_formula.left_sub_formula
        _b = a.left_sub_formula.right_sub_formula
        hypot = [a.left_sub_formula]
        proof_seq = hypot[:]
        proof_seq.append(a.right_sub_formula.left_sub_formula)
        x = a.left_sub_formula.imp((_b.obj().imp(_a.obj())))
        y = (_a.obj().imp(_b)).imp(_b.obj().imp(_a.obj().obj()))
        proof_seq += Theorem.T5.value.call(x)
        proof_seq.append(Rules.MP.value.call(proof_seq[0], proof_seq[-1]))
        tmp = proof_seq[-1]
        proof_seq += Theorem.T5.value.call(y)
        proof_seq.append(Rules.MP.value.call(proof_seq[1], proof_seq[-1]))
        proof_seq.append(Axioms.A3.value.call(_b, _a.obj()))
        proof_seq.append(Rules.MP.value.call(proof_seq[-2], proof_seq[-1]))
        proof_seq.append(Rules.MP.value.call(tmp, proof_seq[-1]))
        proof_seq = Theorem.Deduction.value.call(hypot, a.right_sub_formula.left_sub_formula, proof_seq)
        proof_seq = Theorem.Deduction.value.call([], a.left_sub_formula, proof_seq, indexation=indexation)
        return proof_seq
    else:
        raise ValueError('T7 wrong usage')


def _find_up(a: PCF, proof_seq):
    for el in proof_seq:
        if el == a:
            return el


def _calmar(a: PCF, vector: list, var_order: list, indexation=False):
    proof_seq = []
    for current_f in a.get_stack():

        if not current_f.main_op:

            if current_f(vector, var_order):
                current_f.is_hypot = True

                proof_seq.append(current_f)
                if indexation:
                    current_f.index = len(proof)
                    proof.append(current_f)

            else:
                t = current_f.obj()
                t.is_hypot = True
                proof_seq.append(t)
                if indexation:
                    t.index = len(proof)
                    proof.append(t)

        elif current_f.main_op == Operators.Objection:
            if not current_f(vector, var_order):
                proof_seq += Theorem.T2.value.call(current_f.right_sub_formula.imp(current_f.obj()),
                                                   indexation=indexation)
                proof_seq.append(Rules.MP.value.call(current_f.right_sub_formula, proof_seq[-1],
                                                     indexation=indexation))

        elif current_f.main_op == Operators.Implication:
            _g = current_f.left_sub_formula
            _h = current_f.right_sub_formula

            if not _g(vector, var_order):
                proof_seq += Theorem.T3.value.call(_g.obj().imp(_g.imp(_h)), indexation=indexation)
                proof_seq.append(Rules.MP.value.call(_find_up(_g.obj(), proof_seq),
                                                     proof_seq[-1], indexation=indexation))  # TODO find!!

            elif _h(vector, var_order):
                proof_seq.append(Axioms.A1.value.call(_h, _g, indexation=indexation))
                proof_seq.append(Rules.MP.value.call(_find_up(_h, proof_seq),
                                                     proof_seq[-1], indexation=indexation))

            elif _g(vector, var_order) and not _h(vector, var_order):
                x = _g.imp(_h.obj().imp((_g.imp(_h)).obj()))
                proof_seq += Theorem.T6.value.call(x, indexation=indexation)
                proof_seq.append(Rules.MP.value.call(_find_up(_g, proof_seq),
                                                     proof_seq[-1], indexation=indexation))
                proof_seq.append(Rules.MP.value.call(_find_up(_h.obj(), proof_seq),
                                                     proof_seq[-1], indexation=indexation))

    return proof_seq


def _get_axioms(vector, var_order):
    rez = []
    for i in range(len(var_order)):
        if not vector[i]:
            rez.append(PCF(var_order[i]).obj())
        else:
            rez.append(PCF(var_order[i]))
    return rez


def _adequacy(f: PCF):
    var_order = list(f.variables)

    c_dict = {}
    for _vect in product([True, False], repeat=len(var_order)):
        c_dict[_vect] = Theorem.Calmar.value.call(f, list(_vect), var_order)

    for i in range(len(var_order), 0, -1):

        pairs = []

        for vector, p_seq in c_dict.items():
            for vector1, p_seq1 in c_dict.items():
                if vector[:-1] == vector1[:-1] and vector[-1] and not vector1[-1]:
                    pairs.append(((vector, p_seq), (vector1, p_seq1)))

        c_dict = {}
        for (vector, c_proof), (vector1, c_proof1) in pairs:
            tmp_proof = []
            # True
            x_n = PCF(var_order[i-1])
            tmp_proof += Theorem.Deduction.value.call(_get_axioms(vector, var_order[:i-1]), x_n,  c_proof)
            tmp = tmp_proof[-1]
            # False
            x_n_obj = PCF(var_order[i-1]).obj()
            tmp_proof += Theorem.Deduction.value.call(_get_axioms(vector1, var_order[:i-1]), x_n_obj,  c_proof1)
            tmp1 = tmp_proof[-1]

            x = x_n.imp(f).imp((x_n_obj.imp(f)).imp(f))
            tmp_proof += Theorem.T7.value.call(x)
            tmp_proof.append(Rules.MP.value.call(tmp, tmp_proof[-1]))
            tmp_proof.append(Rules.MP.value.call(tmp1, tmp_proof[-1]))

            c_dict[vector[:-1]] = tmp_proof

    proof_seq = c_dict[()]
    for i in range(len(proof_seq)):
        proof_seq[i].index = i
    return proof_seq


class Theorem(Enum):
    L = _enum_helper('L-theorem', _l)
    Deduction = _enum_helper('Deduction', _deduction)
    T1 = _enum_helper('T1', _t1)
    T2 = _enum_helper('T2', _t2)
    T3 = _enum_helper('T3', _t3)
    T4 = _enum_helper('T4', _t4)
    T5 = _enum_helper('T5', _t5)
    T6 = _enum_helper('T6', _t6)
    T7 = _enum_helper('T7', _t7)
    Calmar = _enum_helper('Calmar', _calmar)
    Adequacy = _enum_helper('Adequacy', _adequacy)
