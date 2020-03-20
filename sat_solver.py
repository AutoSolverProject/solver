from cnfformula import *
from logic_utils import __prefix_with_index_sequence_generator
from utils.normal_forms import *
from propositional_logic.syntax import Formula as PropositionalFormula
from typing import Dict, Tuple


def sat_solver(propositional_formula: PropositionalFormula, partial_model=None, conflict=None, max_decision_levels: int = 5) \
        -> Tuple[str, Model, PropositionalFormula]:
    if partial_model is None:
        partial_model = Model()

    cnf_formula = preprocess(propositional_formula)

    if conflict is not None:
        assert test_is_cnf(conflict)
        conflict_CNFFormula = propositional_formula_to_CNFFormula(conflict)
        assert True or len(conflict_CNFFormula.clauses) == 1  # TODO: check if needed
        for conflict_CNFClause in conflict_CNFFormula.clauses:
            cnf_formula.add_clause(conflict_CNFClause)

    if len(cnf_formula.clauses) == 0:
        return SAT, partial_model, propositional_formula
    for clause in cnf_formula.clauses:
        if len(clause) == 0:
            return UNSAT, partial_model, propositional_formula

    result, model, equisatisfiable_CNFFormula = decide(cnf_formula, partial_model, max_decision_levels=max_decision_levels)
    equisatisfiable_PropositionalFormula = equisatisfiable_CNFFormula.to_PropositionalFormula()
    return result, model, equisatisfiable_PropositionalFormula


# region Pre-processing

def preprocess(propositional_formula: PropositionalFormula) -> CNFFormula:
    cnf_formula = tseitin_transformation(propositional_formula)

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

def tseitin_transformation(propositional_formula: PropositionalFormula) -> CNFFormula:
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
        sub_formula_repped = PropositionalFormula(sub_formula.root, first_repped, second_repped)
        binding_formula = PropositionalFormula('<->', rep, sub_formula_repped)
        binding_formula_in_cnf_form = to_cnf(binding_formula)
        binding_CNFFormula = propositional_formula_to_CNFFormula(binding_formula_in_cnf_form)
        clauses += binding_CNFFormula.clauses

    return CNFFormula(clauses)


def give_representation_to_sub_formulae(propositional_formula: PropositionalFormula) -> Dict[PropositionalFormula, PropositionalFormula]:
    all_sub_formulae = find_closure(propositional_formula)
    rep_generator = __prefix_with_index_sequence_generator('pg')
    representation = dict()

    for sub_formula in all_sub_formulae:
        representation[sub_formula] = sub_formula if is_literal(sub_formula) else PropositionalFormula(next(rep_generator))

    return representation

# endregion

# endregion


def DLIS(cnf_formula: CNFFormula, model: Model) -> Tuple[str, bool]:
    working_model = dict(model)
    possible_assignments = (True, False)
    candidates = cnf_formula.all_variables - set(model.keys())  # Starting with all unassigned variables

    best_candidate = UNSAT
    best_candidate_assignment = UNSAT
    best_candidate_score = 0  # If a variable and it's negation don't satisfy any clause, they're not in the formula! Se we must get better results than 0

    for cur_candidate in candidates:
        for cur_assignment in possible_assignments:
            working_model[cur_candidate] = cur_assignment
            cur_score = cnf_formula.count_clauses_satisfied_by_model(working_model)
            if cur_score != UNSAT and cur_score > best_candidate_score:  # Taking the best decision that won't make a clause UNSAT
                best_candidate = cur_candidate
                best_candidate_assignment = cur_assignment
                best_candidate_score = cur_score

        del working_model[cur_candidate]

    assert best_candidate != UNSAT
    assert best_candidate_assignment != UNSAT
    return best_candidate, best_candidate_assignment


def decide(cnf_formula: CNFFormula, partial_model: Model, max_decision_levels: int = 5, decision_heuristic=DLIS) -> Tuple[str, Model, CNFFormula]:
    implication_graph = ImplicationGraph(partial_model)

    # Decision level zero:
    sat_value, implication_graph = BCP(cnf_formula, implication_graph)
    if sat_value in (SAT, UNSAT):
        return sat_value, implication_graph.total_model, cnf_formula

    for decision_level in range(1, max_decision_levels + 1):
        chosen_variable, chosen_assignment = decision_heuristic(cnf_formula, implication_graph.total_model)
        implication_graph.add_decision(chosen_variable, chosen_assignment)
        sat_value, implication_graph, conflict_clause = BCP(cnf_formula, implication_graph)

        if sat_value == UNSAT:
            if implication_graph.curr_level == 0:
                break
            else:
                backjump_level, conflict_clause = analyze_conflict(cnf_formula, implication_graph)
                implication_graph.backjump_to_level(backjump_level)
                cnf_formula.add_clause(conflict_clause)

        elif sat_value == SAT:
            break

    return sat_value, implication_graph.total_model, cnf_formula


def BCP(cnf_formula: CNFFormula, implication_graph: ImplicationGraph):
    result, conflict_clause = cnf_formula.update_with_model(implication_graph.total_model)

    if result in [SAT, SAT_UNKNOWN]:
        return result, implication_graph

    elif result == UNSAT:
        implication_graph.conflict_clause = conflict_clause
        return result, implication_graph

    else:
        variable, assignment, causing_clause = result
        implication_graph.add_inference(variable, assignment, causing_clause)
        return BCP(cnf_formula, implication_graph)  # Return result of BCP on the model that includes the inference


def analyze_conflict(cnf_formula: CNFFormula, implication_graph: ImplicationGraph) -> Tuple[int, CNFClause]:
    conflict_clause = implication_graph.learn_conflict_clause(cnf_formula)

    decision_levels_of_clause_vars = {implication_graph.get_decision_level_of_variable(variable) for variable in conflict_clause.get_all_variables()}

    # Need to return the second highest decision level that appears in the conflict clause, or level 0, if it only has 1 decision level
    if len(decision_levels_of_clause_vars) == 1:
        return 0, conflict_clause

    decision_levels_of_clause_vars_sorted = sorted(list(decision_levels_of_clause_vars))
    backjump_level = decision_levels_of_clause_vars_sorted[-2]

    return backjump_level, conflict_clause

