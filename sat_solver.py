from cnfformula import *
from logic_utils import __prefix_with_index_sequence_generator
from normal_forms import *
from propositional_logic.syntax import *
from typing import Dict, Tuple


def sat_solver(formula, partial_model=None, conflict=None):
    if partial_model is None:
        partial_model = dict()
    if conflict is None:
        conflict = CNFClause()

    cnf_formula = preprocess(formula)

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


def DLIS(cnf_formula, model) -> Tuple[str, bool]:
    pass  # TODO: complete!


def decide(cnf_formula, partial_model, decision_heuristic=DLIS):
    implication_graph = ImplicationGraph(partial_model)

    while True:
        sat_value, new_implication_graph = BCP(cnf_formula, implication_graph)
        implication_graph = new_implication_graph
        if sat_value != SAT_UNKNOWN:
            return sat_value, implication_graph.get_total_model()

        chosen_variable, chosen_assignment = decision_heuristic(cnf_formula, implication_graph.get_total_model())
        implication_graph.add_decision(chosen_variable, chosen_assignment)


def BCP(cnf_formula: CNFFormula, implication_graph: ImplicationGraph):
    """
    Gets a formula and a model. Deducts all it can about the model.
    If during it finds the formula SAT - Returns.
    If during it finds the formula UNSAT -
            If on level 0 - returns UNSAT.
            Else - analyzes conflict and adds clause; finds when to backjump and backjumps; Returns UNKNOWN.
    Else - Returns UNKNOWN.
    """

    is_sat = True
    inferred_assignment = None

    for clause in cnf_formula.clauses:
        result = clause.update_with_model(implication_graph.get_total_model())
        if result == SAT:
            continue
        elif result == UNSAT:
            if implication_graph.curr_level == 0:
                return UNSAT, implication_graph

            is_sat = False
            analyze_conflict(cnf_formula, implication_graph)

        elif result == SAT_UNKNOWN:
            is_sat = False
            continue
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



def analyze_conflict(cnf_formula: CNFFormula, implication_graph: ImplicationGraph):
    # find clause to add ; find level to jump back to
    uip = implication_graph.find_uip()

    conflict_clause = implication_graph.conflict_clause
    clause = implication_graph.






