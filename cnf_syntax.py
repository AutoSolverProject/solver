import copy
import math
from collections import defaultdict

from typing import List, Set
from propositional_logic.syntax import Formula as PropositionalFormula, is_variable
from propositional_logic.semantics import Model


UNSAT = "UNSAT"
SAT = "SAT"
SAT_UNKNOWN = "SAT_UNKNOWN"


class CNFClause:

    def __init__(self, positive_literals: Set[str] = None, negative_literals: Set[str] = None):
        self.positive_literals = positive_literals if positive_literals is not None else set()
        self.negative_literals = negative_literals if negative_literals is not None else set()

        self.all_literals = dict.fromkeys(self.positive_literals, True)
        self.all_literals.update(dict.fromkeys(self.negative_literals, False))

        for pos_var in self.positive_literals:
            assert is_variable(pos_var)
        for neg_var in self.negative_literals:
            assert is_variable(neg_var)

        self.is_sat = UNSAT if len(self) == 0 else SAT_UNKNOWN
        self.inferred_assignment = None
        self.watched_literals = set()
        self.update_watched_literals_and_maybe_propagate(dict())


    def __repr__(self) -> str:
        if len(self) == 0:
            return ""

        my_repr = "(" * (len(self) - 1)
        first_pos = 0
        first_neg = 0

        pos_literals_list = list(self.positive_literals)
        neg_literals_list = list(self.negative_literals)

        if len(pos_literals_list) > 0:
            my_repr += str(pos_literals_list[0])
            first_pos = 1
        elif len(neg_literals_list) > 0:
            my_repr += str(neg_literals_list[0])
            first_neg = 1

        for pos_index in range(first_pos, len(pos_literals_list)):
            my_repr += "|" + str(pos_literals_list[pos_index]) + ")"

        for neg_index in range(first_neg, len(neg_literals_list)):
            my_repr += "|" + "~" + str(neg_literals_list[neg_index]) + ")"

        return my_repr


    def __eq__(self, other: object) -> bool:
        return isinstance(other, CNFClause) \
               and self.positive_literals == other.positive_literals \
               and self.negative_literals == other.negative_literals


    def __ne__(self, other: object) -> bool:
        return not self == other


    def __hash__(self) -> int:
        return hash(str(self))


    def __len__(self):
        return len(self.all_literals)


    def to_PropositionalFormula(self) -> PropositionalFormula:
        return PropositionalFormula.parse(str(self))


    def is_contain_negation_of_literal(self, variable: str, assignment: bool) -> bool:
        return self.all_literals.get(variable, assignment) != assignment


    def get_all_variables(self) -> Set[str]:
        return set(self.all_literals.keys())


    def get_all_literals(self) -> Set[str]:
        return {pos for pos in self.positive_literals} | {'~' + neg for neg in self.negative_literals}


    def on_backjump(self, model: Model):
        self.update_watched_literals_and_maybe_propagate(model)
        self.update_with_new_model(model)
        return self.inferred_assignment if self.inferred_assignment is not None else self.is_sat


    def update_with_new_model(self, model: Model):
        for pos in self.positive_literals:  # Assuming we have small clauses, but big models
            if model.get(pos, False):
                self.watched_literals = set()
                self.inferred_assignment = None
                self.is_sat = SAT
                return

        for neg in self.negative_literals:
            if not model.get(neg, True):
                self.watched_literals = set()
                self.inferred_assignment = None
                self.is_sat = SAT
                return

        # No literal was satisfied, so SAT_UNKNOWN unless all of them are in the model, and then there's no chance for SAT
        if self.get_all_variables().issubset(model.keys()):
            self.is_sat = UNSAT
            self.watched_literals = set()
            self.inferred_assignment = None
        else:
            self.is_sat = SAT_UNKNOWN


    def is_satisfied_under_assignment(self, variable: str, assignment: bool):
        if self.is_sat in (SAT, UNSAT) or variable not in self.all_literals:
            return self.inferred_assignment if self.inferred_assignment is not None else self.is_sat

        elif self.inferred_assignment is not None:  # We have only one shot to get SAT
            return SAT if self.inferred_assignment == (variable, assignment) else UNSAT

        elif self.all_literals.get(variable, not assignment) == assignment:
            return SAT

        return SAT_UNKNOWN


    def update_with_new_assignment(self, variable: str, assignment: bool, model: Model):
        if self.is_sat in (SAT, UNSAT):
            return self.is_sat  # No new assignment will change this state, so spare the check

        if self.all_literals.get(variable, not assignment) == assignment:
            self.is_sat = SAT
            self.inferred_assignment = None
            self.watched_literals = set()
            return SAT

        # NOTE: If we're here, the assigned variable is either not in our clause, OR the assignment is not satisfying us

        if self.inferred_assignment is not None and self.inferred_assignment[0] == variable:
            self.is_sat = UNSAT  # When we have an inferred variable, the only chance we'll be SAT is if it's assigned correctly
            self.inferred_assignment = None
            self.watched_literals = set()
            return UNSAT

        if variable in self.watched_literals:  # We got an un-satisfying assignment to one of out watch literals
            self.update_watched_literals_and_maybe_propagate(model)

        assert self.is_sat == SAT_UNKNOWN  # If we got here, we MUST be SAT_UNKNOWN
        return self.inferred_assignment if self.inferred_assignment is not None else self.is_sat


    def update_watched_literals_and_maybe_propagate(self, model: Model):
        self.watched_literals = set()  # Finding 1 watch literals is as difficult as finding 2, so don't keep the old watched_literals
        self.inferred_assignment = None

        if self.is_sat in (SAT, UNSAT):
            return

        candidates = self.get_all_variables() - model.keys()
        num_to_take = min(2, len(candidates))

        if num_to_take >= 1:  # Update watched_literals
            the_chosen_ones = list(candidates)[:num_to_take]
            self.watched_literals = set(the_chosen_ones)
            if num_to_take == 1:  # Also update inferred_assignment (i.e. propagate)
                inferred_variable = the_chosen_ones[0]
                self.inferred_assignment = inferred_variable, self.all_literals[inferred_variable]


class CNFFormula:

    def __init__(self, clauses: List[CNFClause]):
        self.clauses = clauses
        self.variable_to_containing_clause = dict()
        self.last_result = SAT_UNKNOWN

        for clause in self.clauses:
            for var in clause.get_all_variables():
                current_clauses = self.variable_to_containing_clause.get(var, set())
                current_clauses.add(clause)
                self.variable_to_containing_clause[var] = current_clauses


    def __repr__(self) -> str:
        if len(self.clauses) == 0:
            return ""

        my_repr = "(" * (len(self.clauses) - 1)
        my_repr += str(self.clauses[0])

        for clause_index in range(1, len(self.clauses)):
            my_repr += "&" + str(self.clauses[clause_index]) + ")"

        return my_repr


    def __eq__(self, other: object) -> bool:
        return isinstance(other, CNFFormula) and self.clauses == other.clauses


    def __ne__(self, other: object) -> bool:
        return not self == other


    def __hash__(self) -> int:
        return hash(str(self))


    def __len__(self):
        return len(self.clauses)


    def to_PropositionalFormula(self) -> PropositionalFormula:
        return PropositionalFormula.parse(str(self))


    def get_all_variables(self) -> Set[str]:
        return set(self.variable_to_containing_clause.keys())


    def count_clauses_satisfied_by_assignment(self, variable: str, assignment: bool):
        assert is_variable(variable)
        sat_counter = 0
        for clause in self.variable_to_containing_clause[variable]:
            sat_value = clause.is_satisfied_under_assignment(variable, assignment)
            if sat_value == SAT:
                sat_counter += 1
            elif sat_value == UNSAT:
                return UNSAT
        return sat_counter


    def add_clause(self, new_clause: CNFClause):
        self.clauses.append(new_clause)
        for var in new_clause.get_all_variables():
            current_clauses = self.variable_to_containing_clause.get(var, set())
            current_clauses.add(new_clause)
            self.variable_to_containing_clause[var] = current_clauses


    def on_backjump(self, model: Model):
        sat_counter = 0
        found_unsat = None
        inferred_assignment = SAT_UNKNOWN  # If we got one inferred assignment, we'll return it. Otherwise, we'll return SAT_UNKNOWN

        for clause in self.clauses:
            result = clause.on_backjump(model)

            if result == UNSAT:
                found_unsat = clause  # Just a precaution, if it happens entire formula UNSAT, and we'll catch that in other places

            elif result == SAT:
                sat_counter += 1

            elif result == SAT_UNKNOWN:
                continue

            else:  # Just a precaution, as backjumping preserves propagated assignments
                inferred_assignment = result + (clause,)

        if found_unsat is not None:
            self.last_result = UNSAT, found_unsat
        elif sat_counter == len(self.clauses):
            self.last_result = SAT
        else:
            self.last_result = inferred_assignment


    def update_with_new_assignment(self, variable: str, assignment: bool, model: Model):
        assert is_variable(variable)
        are_all_sat = True
        found_unsat = None
        inferred_assignment = SAT_UNKNOWN  # If we got one inferred assignment, we'll return it. Otherwise, we'll return SAT_UNKNOWN

        for clause in self.variable_to_containing_clause[variable]:
            result = clause.update_with_new_assignment(variable, assignment, model)

            if result == UNSAT:
                found_unsat = clause  # Maybe can return here, but won't make big difference
                are_all_sat = False

            elif result == SAT:
                continue

            elif result == SAT_UNKNOWN:
                are_all_sat = False

            else:  # Result is a inferred assignment. Continue looping to make sure not UNSAT. Note that means inferred_assignment might change
                inferred_assignment = result + (clause,)
                are_all_sat = False

        if found_unsat is not None:
            self.last_result = UNSAT, found_unsat
        elif are_all_sat:
            self.last_result = SAT
        else:
            self.last_result = inferred_assignment


class ImplicationGraph:

    CAUSING_CLAUSE_OF_DECIDED_VARIABLES = -1


    def __init__(self, decided_variables: Model = None):
        decided_variables = dict(decided_variables) if decided_variables is not None else dict()

        self.curr_level = 0
        self.conflict_clause = None
        self.decision_variables = [decided_variables]
        self.inferred_variables = [dict()]
        self.total_model = dict()
        self.total_model.update(decided_variables)
        # Map each inferred variable to the clause that caused it, and at which level that was
        self.causing_clauses = {variable: (ImplicationGraph.CAUSING_CLAUSE_OF_DECIDED_VARIABLES, self.curr_level) for variable in decided_variables.keys()}


    def __repr__(self) -> str:
        my_repr = ""
        for i in range(self.curr_level):
            my_repr += "LEVEL " + str(i) + ": " + "\n" \
                        + "Decided: " + str(self.decision_variables[i]) + "\n" \
                        + "Inferred: " + str(self.inferred_variables[i]) + "\n"
        return my_repr


    def __eq__(self, other: object) -> bool:
        return isinstance(other, ImplicationGraph) \
               and self.decision_variables == other.decision_variables \
               and self.inferred_variables == other.inferred_variables \
               and self.curr_level == other.curr_level \
               and self.causing_clauses == other.causing_clauses


    def __ne__(self, other: object) -> bool:
        return not self == other


    def __hash__(self) -> int:
        return hash(str(self))


    def __len__(self):
        return self.curr_level


    def add_decision(self, variable, assignment):
        assert is_variable(variable)
        assert variable not in self.total_model.keys()

        self.curr_level += 1
        self.decision_variables.append({variable: assignment})
        self.inferred_variables.append(dict())
        self.total_model[variable] = assignment
        self.causing_clauses[variable] = (ImplicationGraph.CAUSING_CLAUSE_OF_DECIDED_VARIABLES, self.curr_level)


    def add_inference(self, variable: str, assignment: bool, causing_clause: int):
        assert is_variable(variable)
        assert variable not in self.total_model.keys()

        self.inferred_variables[-1].update({variable: assignment})
        self.total_model[variable] = assignment
        self.causing_clauses[variable] = (causing_clause, self.curr_level)


    def get_index_of_causing_clause_of_variable(self, variable: str) -> int:
        assert is_variable(variable)
        return self.causing_clauses[variable][0]


    def get_decision_level_of_variable(self, variable: str) -> int:
        assert is_variable(variable)
        return self.causing_clauses[variable][1]


    def get_causing_variables(self, cnf_formula: CNFFormula, variable: str) -> Set[str]:
        assert is_variable(variable)
        causing_variables = set()
        causing_clause_index = self.get_index_of_causing_clause_of_variable(variable)

        if causing_clause_index != ImplicationGraph.CAUSING_CLAUSE_OF_DECIDED_VARIABLES:
            causing_clause = cnf_formula.clauses[causing_clause_index]
            causing_variables = causing_clause.get_all_variables()

        return causing_variables


    def learn_conflict_clause(self, cnf_formula: CNFFormula) -> CNFClause:
        uip = self.find_uip(cnf_formula)
        uip_assignment = self.total_model[uip]
        conflict_clause = self.conflict_clause

        while not conflict_clause.is_contain_negation_of_literal(uip, uip_assignment):
            conflict_clause = self.resolve(cnf_formula, conflict_clause)

        return conflict_clause


    def find_uip(self, cnf_formula: CNFFormula) -> str:
        # todo: fix
        assert self.conflict_clause is not None
        assert self.curr_level >= 1

        last_decision_variable = list(self.decision_variables[-1].keys())[0]  # List of dict only for level 0. From lvl. 1 always 1 decision var per level
        potential_uips = set(self.total_model.keys())
        potential_uips_distances = {potential_uip: math.inf for potential_uip in potential_uips}
        current_path = list()

        def dfs_helper(current_node):  # Finds all uips we must go through and their min distances from the conflict
            nonlocal potential_uips, potential_uips_distances

            current_path.append(current_node)
            if current_node == last_decision_variable:
                potential_uips.intersection_update(set(current_path))
                for node_index in range(len(current_path)):
                    curr_node = current_path[node_index]
                    curr_node_dist = node_index
                    if curr_node_dist < potential_uips_distances[curr_node]:
                        potential_uips_distances[curr_node] = curr_node_dist

            else:
                for parent in self.get_causing_variables(cnf_formula, current_node):
                    if parent not in current_path:  # Avoid loop, even though we shouldn't have any - just in case
                        dfs_helper(parent)
                current_path.pop()


        dfs_helper(self.conflict_clause)  # Now we have all uips, and their distances

        assert len(potential_uips) >= 1  # The decision variable is a UIP, so there's at least one

        closest_uip = None
        closest_uip_dist = math.inf
        for potential_uip in potential_uips:
            if 0 < potential_uips_distances[potential_uip] < closest_uip_dist:
                closest_uip = potential_uip
                closest_uip_dist = potential_uips_distances[closest_uip]

        assert closest_uip is not None
        return closest_uip


    def resolve(self, cnf_formula: CNFFormula, clause_to_resolve: CNFClause) -> CNFClause:
        last_assigned_var = self.get_last_assigned_var(clause_to_resolve)
        last_assigned_var_causing_clause_index = self.get_index_of_causing_clause_of_variable(last_assigned_var)
        last_assigned_var_causing_clause = cnf_formula.clauses[last_assigned_var_causing_clause_index]

        vars_to_resolve = (clause_to_resolve.positive_literals & last_assigned_var_causing_clause.negative_literals) | \
                          (clause_to_resolve.negative_literals & last_assigned_var_causing_clause.positive_literals)
        assert len(vars_to_resolve) > 0

        new_pos_vars = (clause_to_resolve.positive_literals | last_assigned_var_causing_clause.positive_literals) - vars_to_resolve
        new_neg_vars = (clause_to_resolve.negative_literals | last_assigned_var_causing_clause.negative_literals) - vars_to_resolve
        return CNFClause(new_pos_vars, new_neg_vars)


    def get_last_assigned_var(self, clause_to_resolve: CNFClause) -> str:
        last_assigned_var = None
        last_assigned_var_decision_level = 0
        for cur_var in clause_to_resolve.get_all_variables():
            cur_decision_level = self.get_decision_level_of_variable(cur_var)
            if (cur_decision_level > last_assigned_var_decision_level) \
                    or (cur_decision_level == last_assigned_var_decision_level and cur_var < last_assigned_var):
                last_assigned_var = cur_var
                last_assigned_var_decision_level = cur_decision_level

        assert last_assigned_var is not None
        return last_assigned_var


    def backjump_to_level(self, new_level):
        assert 0 <= new_level
        assert new_level < self.curr_level

        self.curr_level = new_level
        self.conflict_clause = None
        self.decision_variables = self.decision_variables[:self.curr_level + 1]
        self.inferred_variables = self.inferred_variables[:self.curr_level + 1]

        all_vars_before_backjump = set(self.total_model.keys())
        self.total_model = dict()
        for i in range(self.curr_level):
            self.total_model.update(self.decision_variables[i])
            self.total_model.update(self.inferred_variables[i])
        all_vars_after_backjump = set(self.total_model.keys())

        lost_vars = all_vars_before_backjump - all_vars_after_backjump
        for var in lost_vars:
            del self.causing_clauses[var]

