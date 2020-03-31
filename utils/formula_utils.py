from cnf_syntax import CNFFormula, CNFClause
from propositional_logic.syntax import Formula as PropositionalFormula
from propositional_logic.syntax import *


def find_closure(propositional_formula: PropositionalFormula):

    closure = set()

    def find_closure_helper(sub_formula: PropositionalFormula):
        if is_constant(sub_formula.root) or is_variable(sub_formula.root):
            closure.add(sub_formula)

        elif is_unary(sub_formula.root):
            closure.add(sub_formula)
            find_closure_helper(sub_formula.first)

        elif is_binary(sub_formula.root):
            closure.add(sub_formula)
            find_closure_helper(sub_formula.first)
            find_closure_helper(sub_formula.second)

    find_closure_helper(propositional_formula)
    return closure


def is_constant_or_variable(propositional_formula: PropositionalFormula):
    return is_constant(propositional_formula.root) or is_variable(propositional_formula.root)


def is_literal(propositional_formula: PropositionalFormula):
    return is_constant_or_variable(propositional_formula) or (is_unary(propositional_formula.root) and is_constant_or_variable(propositional_formula.first))


def propositional_formula_to_CNFFormula(propositional_formula: PropositionalFormula) -> CNFFormula:
    formula_str = str(propositional_formula)
    return parse_CNFFormula(formula_str)


def parse_CNFFormula(formula_str: str) -> CNFFormula:
    """ Since we gat a string representation of a valid propositional formula, we can make this very simple """

    no_parentheses = formula_str.replace('(', '').replace(')', '')

    clauses_str = no_parentheses.split('&')
    clauses = list()

    for clause in clauses_str:
        variables = clause.split("|")
        positive_variables = {variable for variable in variables if not is_unary(variable[0])}
        negative_variables = {variable[1:] for variable in variables if is_unary(variable[0])}
        new_clause = CNFClause(positive_variables, negative_variables)
        clauses.append(new_clause)

    return CNFFormula(clauses)


