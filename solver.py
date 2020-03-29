from propositional_logic.syntax import Formula as PropositionalFormula
from first_order_logic.syntax import Formula as FO_Formula
from sat_solver import sat_solver
from smt_solver import smt_solver
from utils.formula_utils import *

def main():
    p_formula1 = PropositionalFormula.parse('((p&~q)&(p<->q))')
    p_formula2 = PropositionalFormula.parse('(~p2&(p2|((p1<->p3)->p2)))')
    p_formula3 = PropositionalFormula.parse('(x1&((~x1|x2)&((~x3|x4)&((~x5|~x6)&((~x1|(~x5|x7))&((~x2|~x5)|(x6|~x7)))))))')
    p_formulae = {p_formula1, p_formula2, p_formula3}

    print("Verify sat_solver by running it on propositional formulae.\n\n")
    for formula in p_formulae:
        print("Checking satisfiability of formula " + str(formula))
        state, model, new_formula = sat_solver(formula)
        while state == SAT_UNKNOWN:
            state, model, new_formula = sat_solver(new_formula, model)
        if formula == p_formula1:
            assert state == UNSAT
            print("The formula" + str(formula) + ", has no satisfiable assignment.")
        else:
            assert state == SAT
            if formula == p_formula2:
                assert (not model['p2']) and model['p1'] != model['p3']
            else:
                assert model['x1'] and model['x2'] and (not model['x5']) and (model['x4'] or (not model['x3']))
            print("The formula " + str(formula) + ", is satisfiable with the assignment: " + str(model))

    print("\n\n")
    fo_formula1 = FO_Formula.parse('((f(a,c)=b|f(a,g(b))=b)&~c=g(b))')
    fo_formula2 = FO_Formula.parse('(f(x)=f(y)&~x=y)')
    fo_formula3 = FO_Formula.parse('(f(f(f(a)))=a&(f(f(f(f(f(a)))))=a&~f(a)=a))')
    fo_formula4 = FO_Formula.parse('(g(a)=c&((~f(g(a))=f(c)|g(a)=d)&~c=d))')
    fo_formula5 = FO_Formula.parse('((multiply(a,plus(abs(b),c))=d&~multiply(b,plus(abs(a),c))=d)&a=b)')
    sat_fo_formulae = {fo_formula1, fo_formula2}
    unsat_fo_formulae = {fo_formula3, fo_formula4, fo_formula5}
    print("Verify smt_solver by running it on Tuf formulae.\n\n")
    for formula in sat_fo_formulae:
        state, model = smt_solver(formula)
        assert state == SAT
    for formula in unsat_fo_formulae:
        state, model = smt_solver(formula)
        assert state == UNSAT


if __name__ == '__main__':
    main()
