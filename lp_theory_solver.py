import numpy as np
from sat_solver import *
from smt_solver import assign_in_formula, get_conflict
from typing import List
from first_order_logic.syntax import *

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
    state, partial_assignment, TOMER_new_formula = sat_solver(skeleton)

    while state != UNSAT:

        assignment = assign_in_formula(partial_assignment, sub_map)
        curr_constraints = set()
        for ass in assignment:
            if assignment[ass]:
                curr_constraints.add(translate_to_le(ass))
            else:
                if ass.root == '=':
                    continue
                curr_constraints.add(translate_negative_constraint(ass))
        need_aux_problem = False
        for constraint in curr_constraints:
            if not constraint.arguments[1].root.isdigit():  # b_i for this constraint is negative
                need_aux_problem = True
                break
        if need_aux_problem:                                        # ToDo: implement function, use presentation 11 slides 46-48 inclusive
            problem_matrices = initialize_problem_matrices_for_aux(curr_constraints)
            problem_matrices = auxiliary_problem(problem_matrices, objective)
        else:
            problem_matrices = initialize_problem_matrices(objective, curr_constraints)  # ToDo: implement function, use presentation 12 slide 22
        is_sat = revised_simplex(problem_matrices)
        if not is_sat:
            conflict = get_conflict(assignment)
            state, partial_assignment, TOMER_new_formula = \
                sat_solver(skeleton, partial_model=partial_assignment, conflict=conflict)
        else:
            if len(partial_assignment.keys()) == len(skeleton.variables()):
                return SAT, partial_assignment, TOMER_new_formula
            else:
                state, partial_assignment, TOMER_new_formula = sat_solver(skeleton, partial_model=partial_assignment)
    return state, partial_assignment, TOMER_new_formula



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


def translate_to_le(inequality: Formula):
    root = inequality.root
    if root == '<=':
        return inequality
    else:
        if root == '<':
            if is_function(inequality.arguments[1].root):  # right side of this inequality is a negative number
                right = Term('neg', [Term(inequality.arguments[1].arguments[0].root + 'dot0001')])
            else:
                right = Term(inequality.arguments[1].arguments[0].root + 'dot9999')
            return Formula('<=', [inequality.arguments[0], right])
        elif root == '=':
            if is_function(inequality.arguments[1].root):  # right side of this inequality is a negative number
                right = Term('neg', [Term(inequality.arguments[1].arguments[0].root + 'dot9999')])
            else:
                right = Term(inequality.arguments[1].arguments[0].root + 'dot0001')
            return Formula('<=', [inequality.arguments[0], right])
        elif root == '>' or root == '>=':
            if is_function(inequality.arguments[1].root):  # right side of this inequality is a negative number
                right = Term(inequality.arguments[1].arguments[0].root)
            else:
                right = Term('neg', [Term(inequality.arguments[1].arguments[0].root)])
            if not is_function(inequality.arguments[0].root):  # left side of the inequality is just a variable
                left = Term('neg', [inequality.arguments[0]])
            elif inequality.arguments[0].root == 'neg':  # left side of the inequality is a negated variable
                left = inequality.arguments[0].arguments[0]
            else:   # left side is sum of several variables
                new_args = []
                for arg in inequality.arguments[0].arguments:
                    if is_function(arg.root):   # arg is a negated variable
                        new_args.append(arg.arguments[0])
                    else:   # arg is just a variable
                        new_args.append(Term('neg', [arg]))
                left = Term('plus', new_args)
            if root == '>':
                root = '<'
            else:
                root = '<='
            new_inequality = Formula(root, [left, right])
            return new_inequality if root == '<=' else translate_to_le(new_inequality)


def translate_negative_constraint(inequality: Formula):
    root = inequality.root
    if root == '>':
        return Formula('<=', inequality.arguments)
    else:
        if root == '<=':
            root = '>'
        elif root == '<':
            root = '>='
        else:
            root = '<'
        return translate_to_le(Formula(root, inequality.arguments))


def initialize_problem_matrices_for_aux(constraints):
    base_matrix = np.zeros((len(constraints), len(constraints)))
    for i in range(len(constraints)):
        base_matrix[i][i] = 1
    for constraint in constraints:
        left_side_expressions = []
        if not is_function(constraint.arguments[0].root):  # just one variable on the left side of constraint (possibly with coefficient)
            left_side_expressions.append(constraint.arguments[0].root)
        elif constraint.arguments[0].root == 'neg': # just one negated variable
            left_side_expressions.append('-' + constraint.arguments[0].root)
        else:   # left side is a sum of several variables with their coefficients
            for arg in constraint.arguments[0].arguments:
                if is_function(arg.root):   # arg is a negated variable (possibly with coefficient
                    left_side_expressions.append('-' + arg.arguments[0].root)
                else:   # arg is simply a variable possibly with a coefficient
                    left_side_expressions.append(arg.root)



