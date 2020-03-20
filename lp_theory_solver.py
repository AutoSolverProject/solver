
from sat_solver import *
from smt_solver import assign_in_formula
from typing import List


def dantzig_selection_rule(variables: List, coefficients: List):
    max_val = max(coefficients)
    if coefficients.count(max_val) > 1:
        max_variables = []
        for i in range(len(variables)):
            if coefficients[i] == max_val:
                max_variables.append(variables[i])
        return bland_selection_rule(max_variables)
    index = coefficients.index(max_val)
    return variables[index]


def bland_selection_rule(variables: List):
    return sorted(variables)[0]


def lp_solver(objective: Formula, constraints: Formula):
    """
    this is the main solver for this part of the project, it gets 2 formulas in first order logic
    and checks if there is a feasible solution for objective under constraints

    :param objective: first order logic formula of the form: z=_, where '_' is some term
    :param constraints: first order logic formula in cnf, where every clause may be atomic or a
                        disjunction of atomic clause.
                        An atomic clause is of shape: _#b or ~_#b, where b is some rational constant, '_' is some term
                        and # is one of these: '=', '<', '>', '<=' and '>='
    :return: UNSAT - if no feasible solution exist, SAT - if there is one
    """
    skeleton, sub_map = constraints.propositional_skeleton()
    state, partial_assignment = sat_solver(skeleton)
    still_checking = True
    while still_checking:

        if state == UNSAT:
            return UNSAT
        else:
            assignment = assign_in_formula(partial_assignment, sub_map)
            curr_constraints = set()
            for ass in assignment:
                if assignment[ass]:                                     # notice that x1+x2 is actually plus(x1,x2), and -x1-x2 is plus(neg(x1),neg(x2))
                    curr_constraints.add(translate_to_le(ass))  # ToDo: implement function: for example make x1+x2>4 into -x1-x2<=-4.00001
                else:                                                       # ToDo: for both functions (the one above and the one below) check the forum for explanation
                    curr_constraints.add(translate_negative_constraint(ass))  # ToDo: implement function: for example make ~x1+x2<=4 into -x1-x2<=-4.00001, first change it to x1+x2>4, then use previous function for the rest
            need_aux_problem = False
            for constraint in curr_constraints:
                if not constraint.arguments[1].root.isdigit():  # b_i for this constraint is negative
                    need_aux_problem = True
                    break
            if need_aux_problem:                                        # ToDo: implement function, use presentation 11 slides 46-48 inclusive
                problem_matrices = initialize_problem_matrices_for_aux(objective, curr_constraints)
                problem_matrices = auxiliary_problem(problem_matrices)
            else:
                problem_matrices = initialize_problem_matrices(objective, curr_constraints)  # ToDo: implement function, use presentation 12 slide 22
            is_sat = revised_simplex(problem_matrices)
            if not is_sat:




def revised_simplex():
    # ToDo
    pass


def auxiliary_problem():
    #ToDo
    pass


def lu_basis_factorization():
    #ToDo
    pass


def refactorize():
    #ToDo
    pass

