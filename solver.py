from cnf_syntax import UNSAT, SAT, SAT_UNKNOWN
from propositional_logic.semantics import is_contradiction, evaluate, is_satisfiable
from first_order_logic.syntax import Formula as FO_Formula
from sat_solver import sat_solver
from smt_solver import smt_solver
from utils.formula_utils import *


def test_sat_solver_on_single_formula(formula, correct_state):
    state, model, new_formula = sat_solver(formula)
    while state == SAT_UNKNOWN:
        print("Making another round :)")
        state, model, new_formula = sat_solver(new_formula, model)  # Don't use max_decision_levels for debugging

    assert state == correct_state, "Got state: " + state
    if state == UNSAT:
        print("Correct - The formula" + str(formula) + " has no satisfiable assignment.")
    else:
        assert evaluate(formula, model), "Got model: " + str(model)
        print("Correct - The formula " + str(formula) + " is satisfiable with the assignment: " + str(model))


def test_sat_solver():
    # For writing new tests, can use the function is_satisfiable for calculating the correct_state

    formula_1 = PropositionalFormula.parse('((p&~q)&(p<->q))')
    correct_state_1 = UNSAT
    assert is_contradiction(formula_1)
    test_1 = formula_1, correct_state_1

    formula_2 = PropositionalFormula.parse('(~p2&(p2|((p1<->p3)->p2)))')
    correct_state_2 = SAT
    assert is_satisfiable(formula_2)
    test_2 = formula_2, correct_state_2

    formula_3 = PropositionalFormula.parse('(x1&((~x1|x2)&((~x3|x4)&((~x5|~x6)&((~x1|(~x5|x7))&((~x2|~x5)|(x6|~x7)))))))')
    correct_state_3 = SAT
    assert is_satisfiable(formula_2)
    test_3 = formula_3, correct_state_3

    tests = [test_1, test_2, test_3]

    print("\n\n\nVerify sat_solver by running it on propositional formulae.")
    for test_index, (formula, correct_state) in enumerate(tests):
        print("\n\nTest number: " + str(test_index))
        print("Checking that " + str(formula) + " is found to be " + correct_state)
        test_sat_solver_on_single_formula(formula, correct_state)


def test_smt_solver():
    print("\n\n\nVerify smt_solver by running it on Tuf formulae.")
    fo_formula1 = FO_Formula.parse('((f(a,c)=b|f(a,g(b))=b)&~c=g(b))')
    fo_formula2 = FO_Formula.parse('(f(x)=f(y)&~x=y)')
    fo_formula3 = FO_Formula.parse('(f(f(f(a)))=a&(f(f(f(f(f(a)))))=a&~f(a)=a))')
    fo_formula4 = FO_Formula.parse('(g(a)=c&((~f(g(a))=f(c)|g(a)=d)&~c=d))')
    fo_formula5 = FO_Formula.parse('((multiply(a,plus(abs(b),c))=d&~multiply(b,plus(abs(a),c))=d)&a=b)')
    sat_fo_formulae = {fo_formula1, fo_formula2}
    unsat_fo_formulae = {fo_formula3, fo_formula4, fo_formula5}

    for formula in sat_fo_formulae:
        print("Checking Tuf-satisfiability of formula " + str(formula))
        state, model = smt_solver(formula)
        assert state == SAT
        print("The formula " + str(formula) + ", is Tuf-satisfiable.")

    for formula in unsat_fo_formulae:
        print("Checking T-satisfiability of formula " + str(formula))
        state, model = smt_solver(formula)
        assert state == UNSAT
        print("The formula " + str(formula) + ", is not Tuf-satisfiable.")


def main(test_sat=True, test_smt=True):
    if test_sat:
        test_sat_solver()

    print("\n\n")

    if test_smt:
        test_smt_solver()


if __name__ == '__main__':
    main(test_sat=True, test_smt=True)
