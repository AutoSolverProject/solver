
from propositional_logic.syntax import *


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
