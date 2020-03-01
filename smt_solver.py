from sat_solver import *
from first_order_logic.syntax import *
from disjoint_set_tree import *

def solver(formula):
    skeleton, sub_map = formula.propositional_skeleton()
    partial_assignment = t_propagate(formula, skeleton, sub_map)
    propositional_assignment = check_sat(skeleton, partial_assignment)
    if not propositional_assignment:
        return False
    else:
        assignment = assign_in_formula(propositional_assignment, formula)
        congruence_closer = get_congruence_closer(formula)



def get_subterms(formula):
    if is_equality(formula.root):
        return {formula.arguments[0], formula.arguments[1]}
    elif is_unary(formula.root):
        return get_subterms(formula.first)
    return get_subterms(formula.first) | get_subterms(formula.second)


def make_set(subterms):


