
from propositional_logic.syntax import *


def find_all_sub_formulae(formula, include_variables=False, include_constants=False):

    sub_formulae = set()

    def find_all_sub_formulas_helper(sub_formula):
        if is_constant(sub_formula.root):
            if include_constants:
                sub_formulae.add(sub_formulae)
            else:
                return

        if is_variable(sub_formula.root):
            if include_variables:
                sub_formulae.add(sub_formulae)
            else:
                return

        elif is_unary(sub_formula.root):
            sub_formulae.add(sub_formula)
            find_all_sub_formulae(sub_formula.first)

        elif is_binary(sub_formula.root):
            sub_formulae.add(sub_formula)
            find_all_sub_formulae(sub_formula.first)
            find_all_sub_formulae(sub_formula.second)

    find_all_sub_formulas_helper(formula)
    return sub_formulae




