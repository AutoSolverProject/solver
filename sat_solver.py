from cnfformula import *
from logic_utils import __prefix_with_index_sequence_generator
from normal_forms import *
from propositional_logic.syntax import *
from typing import Dict, Tuple


def sat_solver(formula, partial_model=None, conflict=None) -> Tuple[str, Model]:
    if partial_model is None:
        partial_model = dict()

    cnf_formula = preprocess(formula)

    if conflict is not None:
        assert test_is_cnf(conflict)
        cnflict_CNFFormula = propositional_formula_to_CNFFormula(conflict)
        assert len(cnflict_CNFFormula.clauses) == 1
        cnflict_CNFClause = cnflict_CNFFormula.clauses[0]
        cnf_formula.add_clause(cnflict_CNFClause)

    if len(cnf_formula.clauses) == 0:
        return SAT
    for clause in cnf_formula.clauses:
        if len(clause) == 0:
            return UNSAT

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


def DLIS(cnf_formula: CNFFormula, model: Model) -> Tuple[str, bool]:
    working_model = dict(model)
    possible_assignments = (True, False)
    candidates = cnf_formula.all_variables - set(model.keys())  # Starting with all unassigned variables

    best_candidate = UNSAT
    best_candidate_assignment = UNSAT
    best_candidate_score = 0

    for cur_candidate in candidates:
        for cur_assignment in possible_assignments:

            working_model[cur_candidate] = cur_assignment
            cur_score = cnf_formula.count_clauses_satisfied_by_model(working_model)
            if cur_score != UNSAT and cur_score > best_candidate_score:
                best_candidate = cur_candidate
                best_candidate_assignment = cur_assignment
                best_candidate_score = cur_score

        del working_model[cur_candidate]

    return best_candidate, best_candidate_assignment


def decide(cnf_formula, partial_model, max_decision_rounds=1, decision_heuristic=DLIS) -> Tuple[str, Model]:
    implication_graph = ImplicationGraph(partial_model)

    curr_decision_round = 0
    while curr_decision_round <= max_decision_rounds:
        curr_decision_round += 1
        prev_implication_graph = implication_graph

        sat_value, implication_graph = BCP(cnf_formula, prev_implication_graph)

        if sat_value == SAT:
            return sat_value, implication_graph.get_total_model()

        elif sat_value == UNSAT:
            if implication_graph.curr_level == 0:
                return UNSAT, implication_graph.get_total_model()
            else:
                backjump_level, conflict_clause = analyze_conflict(cnf_formula, implication_graph)
                implication_graph.backjump_to_level(backjump_level)
                cnf_formula.add_clause(conflict_clause)

        #  TODO: when curr_decision_round == max_decision_rounds put values to return from outside the while

        elif sat_value == SAT_UNKNOWN:
            chosen_variable, chosen_assignment = decision_heuristic(cnf_formula, implication_graph.get_total_model())
            assert chosen_variable != UNSAT
            assert chosen_assignment != UNSAT
            implication_graph.add_decision(chosen_variable, chosen_assignment)


def BCP(cnf_formula: CNFFormula, implication_graph: ImplicationGraph):
    is_sat = True
    inferred_assignment = None

    for clause in cnf_formula.clauses:
        result = clause.update_with_model(implication_graph.get_total_model())
        if result == SAT:
            continue
        elif result == SAT_UNKNOWN:
            is_sat = False
            continue
        elif result == UNSAT:
            is_sat = False
            return  # TODO: ?

        else:  # result is a inferred assignment
            is_sat = False
            inferred_assignment = result

    if is_sat:
        return SAT, implication_graph

    if inferred_assignment is not None:
        variable = inferred_assignment[0]
        assignment = inferred_assignment[1]
        implication_graph.add_inference(variable, assignment)
        return BCP(cnf_formula, implication_graph)



def analyze_conflict(cnf_formula: CNFFormula, implication_graph: ImplicationGraph) -> Tuple[int, CNFClause]:
    # find clause to add ; find level to jump back to
    clause_to_add = implication_graph.learn_conflict_clause()
    level_to_back_jump = implication_graph.find_level_to_backjump()
    return 0, None






