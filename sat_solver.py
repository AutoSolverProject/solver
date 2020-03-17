from cnfformula import *
from formula_utils import *
from logic_utils import __prefix_with_index_sequence_generator
from normal_forms import *
from propositional_logic.semantics import Model
from propositional_logic.syntax import *
from typing import Dict, Tuple


# region Tseitin transformation

def tseitin_transformation(propositional_formula: Formula) -> CNFFormula :
    nnf_formula = to_nnf(propositional_formula)  # Simplifying assumption
    representations = give_representation_to_sub_formulae(nnf_formula)

    p_g = representations[nnf_formula].root
    first_clause = CNFClause([p_g])
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


def give_representation_to_sub_formulae(propositional_formula: Formula) -> Dict[Formula, Formula] :
    all_sub_formulae = find_closure(propositional_formula)
    rep_generator = __prefix_with_index_sequence_generator('pg')
    representation = dict()

    for sub_formula in all_sub_formulae:
        representation[sub_formula] = sub_formula if is_literal(sub_formula) else Formula(next(rep_generator))

    return representation

# endregion


# region Pre-processing

def preprocess(cnf_formula: CNFFormula) -> CNFFormula :
    new_clauses = list()

    for clause in cnf_formula.clauses:
        if is_trivial_clause(clause):
            continue
        new_clause = remove_redundant_literals(clause)
        new_clauses.append(new_clause)

    return CNFFormula(new_clauses)


def remove_redundant_literals(cnf_clause: CNFClause) -> CNFClause :
    return CNFClause(list(set(cnf_clause.literals)))


def is_trivial_clause(cnf_clause: CNFClause) -> bool :
    positive_set = set(cnf_clause.positive_literals)
    negative_set = set(cnf_clause.negative_literals)
    intersection = positive_set & negative_set
    return len(intersection) != 0

# endregion


# region Deduction steps

def deduction_steps(cnf_formula: CNFFormula, partial_model: Model):
    for clause in cnf_formula.clauses:



def unit_propagation(cnf_formula: CNFFormula, partial_model: Model) -> Model :
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


def dlis():
    pass


def vsids():
    pass

# endregion
