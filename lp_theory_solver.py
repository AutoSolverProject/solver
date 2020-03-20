import numpy as np
from sat_solver import *
from smt_solver import model_over_skeleton_to_model_over_formula, get_conflict
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

        assignment = model_over_skeleton_to_model_over_formula(partial_assignment, sub_map)
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
        if need_aux_problem:
            is_sat = auxiliary_problem(initialize_problem_matrices_for_aux(curr_constraints))
        else:
            is_sat = revised_simplex(initialize_problem_matrices(objective, curr_constraints))
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


def revised_simplex(base_matrix, xb_matrix, an_matrix, xn_matrix, b_matrix, cb_matrix, cn_matrix):
    # ToDo
    return True


def auxiliary_problem(base_matrix, xb_matrix, an_matrix, xn_matrix, b_matrix, cb_matrix, cn_matrix):
    #ToDo
    return True


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


def initialize_common_matrices(constraints):
    base_matrix = np.zeros((len(constraints), len(constraints)))
    for i in range(len(constraints)):
        base_matrix[i][i] = 1
    variables_set = set()
    list_left_side_expressions = []
    right_side_expressions = []
    for constraint in constraints:
        left_side_expressions = []
        if not is_function(constraint.arguments[0].root):  # just one variable on the left side of constraint (possibly with coefficient)
            left_side_expressions.append(constraint.arguments[0].root)
        elif constraint.arguments[0].root == 'neg':     # just one negated variable
            left_side_expressions.append('-' + constraint.arguments[0].root)
        else:   # left side is a sum of several variables with their coefficients
            for arg in constraint.arguments[0].arguments:
                if is_function(arg.root):   # arg is a negated variable (possibly with coefficient
                    left_side_expressions.append('-' + arg.arguments[0].root)
                else:   # arg is simply a variable possibly with a coefficient
                    left_side_expressions.append(arg.root)
        for expression in left_side_expressions:
            i = 0
            while expression[i] != 'x':
                i += 1
            variables_set.add(int(expression[i+1]))
        list_left_side_expressions.append(left_side_expressions)
        arg = constraint.arguments[1]
        if is_function(arg.root):
            right_side_expressions.append(float('-' + arg.arguments[0].root.replace('dot', '.')))
        else:
            right_side_expressions.append(float(arg.arguments[0].root.replace('dot', '.')))
    max_variable = max(variables_set)
    an_matrix = np.zeros((len(constraints), max_variable))
    for i in range(len(constraints)):
        for expression in list_left_side_expressions[i]:
            j = 0
            while expression[j] != 'x':
                j += 1
            if j == 0:
                an_matrix[i][int(expression[i+1:])] = 1.
            elif j == 1:
                an_matrix[i][int(expression[i+1:])] = -1.
            else:
                an_matrix[i][int(expression[i+1:])] = float(expression[:i])
    b_matrix = np.zeros((len(constraints),))
    for i in range(len(right_side_expressions)):
        b_matrix[i] = right_side_expressions[i]
    xb_matrix = np.zeros((len(constraints),))
    cb_matrix = np.zeros((len(constraints),))
    for i in range(len(constraints)):
        xb_matrix[i] = i+1+len(variables_set)
    xn_matrix = np.zeros((len(variables_set),))
    for var in variables_set:
        xn_matrix[var-1] = var
    return [base_matrix, xb_matrix, an_matrix, xn_matrix, b_matrix, cb_matrix]


def initialize_problem_matrices_for_aux(constraints):
    base_matrix, xb_matrix, an_matrix, xn_matrix, b_matrix, cb_matrix = initialize_common_matrices(constraints)
    cn_matrix = np.zeros((len(xn_matrix)+1,))
    cn_matrix[0] = -1.
    tmp_matrix = xn_matrix
    xn_matrix = np.zeros((len(xn_matrix)+1,))
    for i in range(len(tmp_matrix)):
        xn_matrix[i+1] = tmp_matrix[i]
    tmp_matrix = an_matrix
    an_matrix = np.zeros((an_matrix.shape[0], an_matrix.shape[1]+1))
    for i in range(an_matrix.shape[0]):
        an_matrix[i][0] = -1.
        for j in range(1, an_matrix.shape[1]):
            an_matrix[i][j] = tmp_matrix[i][j-1]
    return [base_matrix, xb_matrix, an_matrix, xn_matrix, b_matrix, cb_matrix, cn_matrix]


def initialize_problem_matrices(objective, constraints):
    base_matrix, xb_matrix, an_matrix, xn_matrix, b_matrix, cb_matrix = initialize_common_matrices(constraints)
    cn_matrix = np.zeros((len(xn_matrix),))
    term = objective.arguments[1]
    if not is_function(term.root) or term.root == 'neg':
        is_neg = False
        if term.root == 'neg':
            is_neg = True
            term = term.arguments[0]
        i = 0
        while term.root[i] != 'x':
            i += 1
        if i == 0:
            coefficient = 1
        else:
            coefficient = term.root[:i]
        if is_neg:
            coefficient = -coefficient
        cn_matrix[int(term.root[i+1:])] = coefficient
    else:
        for arg in term.arguments:
            is_neg = False
            if is_function(arg.root):
                is_neg = True
                arg = arg.arguments[0]
            i = 0
            while arg.root[i] != 'x':
                i += 1
            if i == 0:
                coefficient = 1
            else:
                coefficient = arg.root[:i]
            if is_neg:
                coefficient = -coefficient
            cn_matrix[int(arg.root[i+1:])] = coefficient
    return [base_matrix, xb_matrix, an_matrix, xn_matrix, b_matrix, cb_matrix, cn_matrix]





