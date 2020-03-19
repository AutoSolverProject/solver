from first_order_logic.syntax import *
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


def revised_simplex(objective, constraints):
    pass


def auxiliary_problem(objective, constraints):
    pass


def lu_basis_factorization():
    pass


def refactorize():
    pass

