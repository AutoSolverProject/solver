from cnfformula import *
from formula_utils import *
from logic_utils import __prefix_with_index_sequence_generator
from normal_forms import *
from propositional_logic.semantics import Model
from propositional_logic.syntax import *
from typing import Dict, Tuple


sat_solver_UNSAT = "UNSAT"

sat_solver_SAT = "SAT"

sat_solver_UNKNOWN = "UNKNOWN"


def sat_solver(formula, partial_model=None, conflict=None):
    if partial_model is None:
        partial_model = dict()
    if conflict is None:
        conflict = CNFClause()

    cnf_formula = preprocess(formula)

    if len(cnf_formula.clauses) == 0:
        return sat_solver_SAT
    for clause in cnf_formula.clauses:
        if len(clause) == 0:
            return sat_solver_UNSAT

    return decide(cnf_formula, partial_model)


# region Pre-processing

def preprocess(formula: Formula) -> CNFFormula:
    cnf_formula = tseitin_transformation(formula)

    new_clauses = list()

    for clause in cnf_formula.clauses:
        if is_trivial_clause(clause):
            continue
        new_clause = remove_redundant_literals(clause)
        new_clauses.append(new_clause)

    return CNFFormula(new_clauses)


def remove_redundant_literals(cnf_clause: CNFClause) -> CNFClause:
    return CNFClause(list(set(cnf_clause.literals)))


def is_trivial_clause(cnf_clause: CNFClause) -> bool:
    positive_set = set(cnf_clause.positive_literals)
    negative_set = set(cnf_clause.negative_literals)
    intersection = positive_set & negative_set
    return len(intersection) != 0


# region Tseitin transformation

def tseitin_transformation(propositional_formula: Formula) -> CNFFormula:
    nnf_formula = to_nnf(propositional_formula)  # Simplifying assumption - no cases like: ~~~~~~~~~p<->q
    representations = give_representation_to_sub_formulae(nnf_formula)

    p_g = representations[nnf_formula]
    first_clause = CNFClause([p_g.root])
    clauses = [first_clause]

    for sub_formula, rep in representations.items():
        if is_literal(sub_formula):
            continue

        first_repped = representations[sub_formula.first]
        second_repped = representations[sub_formula.second]
        sub_formula_repped = Formula(sub_formula.root, first_repped, second_repped)
        binding_formula = Formula('<->', rep, sub_formula_repped)
        binding_formula_in_cnf_form = to_cnf(binding_formula)
        binding_CNFFormula = propositional_formula_to_CNFFormula(binding_formula_in_cnf_form)
        clauses += binding_CNFFormula.clauses

    return CNFFormula(clauses)


def give_representation_to_sub_formulae(propositional_formula: Formula) -> Dict[Formula, Formula]:
    all_sub_formulae = find_closure(propositional_formula)
    rep_generator = __prefix_with_index_sequence_generator('pg')
    representation = dict()

    for sub_formula in all_sub_formulae:
        representation[sub_formula] = sub_formula if is_literal(sub_formula) else Formula(next(rep_generator))

    return representation

# endregion

# endregion


def DLIS():
    pass


def decide(cnf_formula, partial_model, decision_heuristic=DLIS):
    cnf_formula.update_with_model(partial_model)

    sat_value = sat_solver_UNKNOWN
    new_partial_model = partial_model

    while sat_value == sat_solver_UNKNOWN:
        sat_value, new_partial_model = BCP(cnf_formula, partial_model)

    return sat_value, new_partial_model



def BCP(cnf_formula, partial_model):

    if cnf_formula.isSAT():
        return sat_solver_SAT, partial_model

    if sat_value == sat_solver_UNSAT:
        return sat_solver_UNSAT, new_partial_model

    implication_graph = None
    for literal, assignment in partial_model:
        implication_graph.add_literal_assignment(literal, assignment)


def analyze_conflict():
    pass




