import csv
from PCF.PropCalcFormula import PCF
from PCF.theorems_and_axioms import Axioms, Rules, Theorem, Syllogism, proof

if __name__ == '__main__':

    # ---A1 test---
    with open('test_results/A1.txt', 'w') as f:
        t = Axioms.A1.value.call(PCF('F'), PCF('G'))
        f.writelines([str(t), str(t.clauses)])

    # ---A2 test---
    with open('test_results/A2.txt', 'w') as f:
        t = Axioms.A2.value.call(PCF('F'), PCF('G'), PCF('H'))
        f.writelines([str(t), str(t.clauses)])

    # ---A3 test---
    with open('test_results/A3.txt', 'w') as f:
        t = Axioms.A3.value.call(PCF('G'), PCF('F'))
        f.writelines([str(t), str(t.clauses)])

    # ---MP test---
    with open('test_results/MP.txt', 'w') as f:
        t = Rules.MP.value.call(PCF('G'), PCF('G').imp(PCF('F')))
        f.writelines([str(t), str(t.clauses)])

    # ---L test---
    with open('test_results/L.txt', 'w') as f:
        Theorem.L.value.call(PCF("F").imp(PCF("F")), indexation=True)
        f.write(str(PCF("F").imp(PCF("F"))) + ' '+proof[-1].get_info())
        for i in proof:
            f.write(i.get_info())

    # ---Deduction test---
    proof.clear()

    given_proof = list()
    given_proof.append(PCF('B', is_hypot=True))
    given_proof.append(PCF('A', is_hypot=True))
    x = PCF('A').imp(PCF('B').imp(PCF('C')))
    x.is_hypot = True
    given_proof.append(x)
    given_proof.append(Rules.MP.value.call(given_proof[1], given_proof[-1]))
    given_proof.append(Rules.MP.value.call(given_proof[0], given_proof[-1]))
    with open('test_results/Deduction.txt', 'w') as f:
        g_p = Theorem.Deduction.value.call([PCF('A').imp(PCF('B').imp(PCF('C'))), PCF('B')], PCF('A'), given_proof)
        t = Theorem.Deduction.value.call([PCF('A').imp(PCF('B').imp(PCF('C')))],  PCF('B'), g_p)
        Theorem.Deduction.value.call([], PCF('A').imp(PCF('B').imp(PCF('C'))), t, indexation=True)
        for i in proof:
            f.write('Triple deduction usage')
            f.write(i.get_info())

    proof.clear()

    # ---S1 test---
    with open('test_results/S1.csv', 'w') as f:
        Syllogism.S1.value.call(PCF('F').imp(PCF('G')), PCF('G').imp(PCF('H')), indexation=True)
        w = csv.writer(f)
        w.writerow([str(PCF('F').imp(PCF('G'))), str(PCF('G').imp(PCF('H'))), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    proof.clear()

    # ---S2 test---
    with open('test_results/S2.csv', 'w') as f:
        Syllogism.S2.value.call(PCF('A').imp(PCF('B').imp(PCF('C'))), PCF('B'), indexation=True)
        w = csv.writer(f)
        w.writerow([str(PCF('A').imp(PCF('B').imp(PCF('C')))), str(PCF('B')), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    proof.clear()

    # ---T1 test---
    with open('test_results/T1.csv', 'w') as f:
        Theorem.T1.value.call(PCF('F').obj().obj().imp(PCF('F')), indexation=True)
        w = csv.writer(f)
        w.writerow([str(PCF('F').obj().obj().imp(PCF('F'))), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    proof.clear()

    # ---T2 test---
    with open('test_results/T2.csv', 'w') as f:
        Theorem.T2.value.call(PCF('F').imp(PCF('F').obj().obj()), indexation=True)
        w = csv.writer(f)
        w.writerow([str(PCF('F').imp(PCF('F').obj().obj())), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    proof.clear()

    # ---T3 test---
    with open('test_results/T3.csv', 'w') as f:
        Theorem.T3.value.call(PCF('A').obj().imp(PCF('A').imp(PCF('B'))), indexation=True)
        w = csv.writer(f)
        w.writerow([str(PCF('A').obj().imp(PCF('A').imp(PCF('B')))), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    proof.clear()

    # ---T4 test---
    with open('test_results/T4.csv', 'w') as f:
        Theorem.T4.value.call((PCF('B').obj().imp(PCF('A').obj())).imp(PCF('A').imp(PCF('B'))), indexation=True)
        w = csv.writer(f)
        w.writerow([str((PCF('B').obj().imp(PCF('A').obj())).imp(PCF('A').imp(PCF('B')))), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    proof.clear()

    # ---T5 test---
    with open('test_results/T5.csv', 'w') as f:
        Theorem.T5.value.call(PCF('A').imp(PCF('B')).imp(PCF('B').obj().imp(PCF('A').obj())), indexation=True)
        w = csv.writer(f)
        w.writerow([str(PCF('A').imp(PCF('B')).imp(PCF('B').obj().imp(PCF('A').obj()))), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    proof.clear()

    # ---T6 test---
    with open('test_results/T6.csv', 'w') as f:
        Theorem.T6.value.call(PCF('F').imp(PCF('G').obj().imp((PCF('F').imp(PCF('G'))).obj())), indexation=True)
        w = csv.writer(f)
        w.writerow([str(PCF('F').imp(PCF('G').obj().imp((PCF('F').imp(PCF('G'))).obj()))), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    proof.clear()

    # ---T7 test---
    with open('test_results/T7.csv', 'w') as f:
        Theorem.T7.value.call(PCF('F').imp(PCF('G')).imp((PCF('F').obj().imp(PCF('G'))).imp(PCF('G'))), indexation=True)
        w = csv.writer(f)
        w.writerow(
            [str(PCF('F').imp(PCF('G')).imp((PCF('F').obj().imp(PCF('G'))).imp(PCF('G')))), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    proof.clear()
    # ---Calmar test---
    with open('test_results/Calmar.csv', 'w') as f:
        _a = PCF('A')
        _b = PCF('B')
        Theorem.Calmar.value.call(_a.imp(_a).imp(_b), [False, True], ['A', 'B'], indexation=True)
        w = csv.writer(f)
        w.writerow([str(_a.imp(_a).imp(_b)), str([False, True]), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])
    # ---Adequacy test---

    with open('test_results/Adequacy_L.csv', 'w') as f:
        proof = Theorem.Adequacy.value.call(PCF('A').imp(PCF('A')))
        w = csv.writer(f)
        w.writerow([str(PCF('A').imp(PCF('A'))), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    with open('test_results/Adequacy_A1.csv', 'w') as f:
        proof = Theorem.Adequacy.value.call(PCF('A').imp(PCF('B').imp(PCF('A'))))
        w = csv.writer(f)
        w.writerow([str(PCF('A').imp(PCF('B').imp(PCF('A')))), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])

    with open('test_results/Adequacy_A3.csv', 'w') as f:
        proof = Theorem.Adequacy.value.call(
            PCF('G').obj().imp(PCF('F').obj()).imp((PCF('G').obj().imp(PCF('F'))).imp(PCF('G'))))
        w = csv.writer(f)
        w.writerow([str(PCF('A').imp(PCF('B').imp(PCF('A')))), proof[-1].get_info()])
        for i in proof:
            w.writerow([i.get_info()])
