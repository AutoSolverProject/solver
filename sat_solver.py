
from propositional_logic.syntax import *
from logic_utils import *


def tseitin_transformation():
    pass


def find_all_sub_formulas(formula):

    sub_formulas = set()

    def find_all_sub_formulas_helper(sub_formula):
        if is_variable(sub_formula.root) or is_constant(sub_formula.root):
            return

        elif is_unary(sub_formula.root):
            sub_formulas.add(sub_formula)
            find_all_sub_formulas(sub_formula.first)

        elif is_binary(sub_formula.root):
            sub_formulas.add(sub_formula)
            find_all_sub_formulas(sub_formula.first)
            find_all_sub_formulas(sub_formula.second)

    return find_all_sub_formulas(formula)


def give_representation_to_subformulas(formula):
    all_sub_formulas = find_all_sub_formulas(formula)
    representation = {sub_formula: next(fresh_variable_name_generator) for sub_formula in all_sub_formulas}
    return representation


def bind_represntation_to_subformulas(formula):
    pass


def preprocess():
    pass


def deduction_steps():
    pass


def case_splitting():
    pass


def conflict_analysis():
    pass


def learn_conflict_clauses():
    pass


def decision_heuristic():
    pass


def watch_literals():
    pass
