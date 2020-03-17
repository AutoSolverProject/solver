
from formula_utils import find_all_sub_formulae
from logic_utils import __prefix_with_index_sequence_generator
from propositional_logic.syntax import *


def tseitin_transformation():
    pass


def give_representation_to_subformulas(formula):
    all_sub_formulae = find_all_sub_formulae(formula)
    rep_generator = __prefix_with_index_sequence_generator('pg')
    representation = {sub_formula: next(rep_generator) for sub_formula in all_sub_formulae}
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
