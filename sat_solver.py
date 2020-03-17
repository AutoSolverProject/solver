from cnfformula import *
from formula_utils import *
from logic_utils import __prefix_with_index_sequence_generator
from normal_forms import *
from propositional_logic.syntax import *


# region Tseitin transformation

def tseitin_transformation(propositional_formula):
    nnf_formula = to_nnf(propositional_formula)  # Simplifying assumption
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


def give_representation_to_sub_formulae(propositional_formula):
    all_sub_formulae = find_closure(propositional_formula)
    rep_generator = __prefix_with_index_sequence_generator('pg')
    representation = dict()

    for sub_formula in all_sub_formulae:
        representation[sub_formula] = sub_formula if is_literal(sub_formula) else Formula(next(rep_generator))

    return representation

# endregion


# region Pre-processing

def preprocess(cnf_formula):
    new_clauses = list()

    for clause in cnf_formula.clauses:
        if is_trivial_clause(clause):
            continue
        new_clause = remove_redundant_literals(clause)
        new_clauses.append(new_clause)

    return CNFFormula(new_clauses)


def remove_redundant_literals(cnf_clause):
    return CNFClause(list(set(cnf_clause.literals)))


def is_trivial_clause(cnf_clause):
    positive_set = set(cnf_clause.positive_literals)
    negative_set = set(cnf_clause.negative_literals)
    intersection = positive_set & negative_set
    return len(intersection) != 0

# endregion


# region Deduction steps

def deduction_steps():
    pass


def unit_propagation():
    pass

# endregion


# region Case splitting

def case_splitting():
    pass

# endregion


# region Conflict analysis

def conflict_analysis():
    pass

# endregion


# region Learning conflict clauses

def learn_conflict_clauses():
    pass

# endregion


# region Decision heuristics

def decision_heuristic():
    pass

# endregion


# region Watch literals

def watch_literals():
    pass

# endregion
