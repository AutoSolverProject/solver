from cnfformula import CNFFormula, CNFClause
from propositional_logic.syntax import *


UNSAT = "UNSAT"

SAT = "SAT"

SAT_UNKNOWN = "UNKNOWN"


def find_closure(formula):

    closure = set()

    def find_closure_helper(sub_formula):
        if is_constant(sub_formula.root) or is_variable(sub_formula.root):
            closure.add(sub_formula)

        elif is_unary(sub_formula.root):
            closure.add(sub_formula)
            find_closure_helper(sub_formula.first)

        elif is_binary(sub_formula.root):
            closure.add(sub_formula)
            find_closure_helper(sub_formula.first)
            find_closure_helper(sub_formula.second)

    find_closure_helper(formula)
    return closure


def is_constant_or_variable(formula):
    return is_constant(formula.root) or is_variable(formula.root)


def is_literal(formula):
    return is_constant_or_variable(formula) or (is_unary(formula.root) and is_constant_or_variable(formula.first))


def propositional_formula_to_CNFFormula(formula: Formula) -> CNFFormula:
    formula_str = formula.__repr__()
    return parse_CNFFormula(formula_str)


def parse_CNFFormula(formula_str) -> CNFFormula:
    """ Since we gat a string representation of a valid propositional formula, we can make this very simple """

    no_parentheses = formula_str.replace('(', '').replace(')', '')

    clauses_str = no_parentheses.split('&')
    clauses = list()

    for clause in clauses_str:
        variables = clause.split("|")
        positive_variables = [variable for variable in variables if not is_unary(variable[0])]
        negative_variables = [variable for variable in variables if is_unary(variable[0])]
        new_clause = CNFClause(positive_variables, negative_variables)
        clauses.append(new_clause)

    return CNFFormula(clauses)


