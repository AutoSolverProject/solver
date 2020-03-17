from cnfformula import *
from formula_utils import *
from logic_utils import __prefix_with_index_sequence_generator
from normal_forms import *
from propositional_logic.syntax import *


def tseitin_transformation(formula):
    nnf_formula = to_nnf(formula)  # Simplifying assumption
    representations = give_representation_to_sub_formulae(nnf_formula)

    first_clause = CNFClause(representations[nnf_formula])
    clauses = [first_clause]

    for sub_formula, rep in representations.items():
        if is_literal(sub_formula):
            continue

        first_repped = representations[sub_formula.first]
        second_repped = representations[sub_formula.second]
        sub_formula_repped = Formula(sub_formula.root, first_repped, second_repped)
        binding_formula = Formula('<->', rep, sub_formula_repped)
        binding_formula_in_cnf_form = to_cnf(binding_formula)
        clauses += binding_formula_in_cnf_form.clauses

    return CNFFormula(clauses)


def give_representation_to_sub_formulae(formula):
    all_sub_formulae = find_closure(formula)
    rep_generator = __prefix_with_index_sequence_generator('pg')
    representation = dict()

    for sub_formula in all_sub_formulae:
        representation[sub_formula] = sub_formula if is_literal(sub_formula) else Formula(next(rep_generator))

    return representation


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
