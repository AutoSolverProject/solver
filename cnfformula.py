import copy
import math

from utils.formula_utils import *
from logic_utils import frozen
from typing import List, Dict
from propositional_logic.syntax import Formula as PropositionalFormula
from propositional_logic.semantics import Model


@frozen
class CNFClause:

    def __init__(self, positive_literals: List[str] = None, negative_literals: List[str] = None):
        self.positive_literals = copy.deepcopy(positive_literals) if positive_literals else list()
        self.positive_literals.sort()

        self.negative_literals = copy.deepcopy(negative_literals) if negative_literals else list()
        self.negative_literals.sort()

        self.watch_literals = self.find_watch_literals(Model())


    def __repr__(self) -> str:
        if len(self) == 0:
            return "F"

        my_repr = "(" * (len(self) - 1)
        first_pos = 0
        first_neg = 0

        if len(self.positive_literals) > 0:
            my_repr += str(self.positive_literals[0])
            first_pos = 1
        else:
            my_repr += "~" + str(self.negative_literals[0])
            first_neg = 1

        for pos_index in range(first_pos, len(self.positive_literals)):
            my_repr += "|" + str(self.positive_literals[pos_index]) + ")"

        for neg_index in range(first_neg, len(self.negative_literals)):
            my_repr += "|" + "~" + str(self.negative_literals[neg_index]) + ")"

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
        return len(self.positive_literals) + len(self.negative_literals)


    def to_PropositionalFormula(self) -> PropositionalFormula:
        return PropositionalFormula.parse(str(self))


    def is_contain_negation_of_literal(self, variable: str, assignment: bool) -> bool:
        if assignment and variable in self.negative_literals:
            return True
        if not assignment and variable in self.positive_literals:
            return True
        return False


    def get_all_variables(self) -> Set[str]:
        return set(self.positive_literals + self.negative_literals)


    def is_satisfied_under_model(self, model: Model) -> str:
        # TODO: use watch literals for efficiency
        for pos in self.positive_literals:
            if model.get(pos, False):
                return SAT

        for neg in self.negative_literals:
            if not model.get(neg, True):
                return SAT

        # No literal was satisfied, so SAT_UNKNOWN unless all of them are in the model, and then there's no chance for SAT
        return UNSAT if self.get_all_variables().issubset(model.keys()) else SAT_UNKNOWN


    def update_with_model(self, model: Model):
        # TODO: implement!
        # Check if any watch literal was assigned, and only if so bother to check if can deduce an assignment
        for watch_literal, watch_literal_sign in self.watch_literals:
            if watch_literal not in model.keys():
                continue
            elif (model[watch_literal] == True and watch_literal_sign == False) \
                    or (model[watch_literal] == False and watch_literal_sign == True):
                self.watch_literals = self.find_watch_literals(model)

        if len(self.watch_literals) == 1:
            return {self.watch_literals[0]: self.watch_literals[1]}
        break


    def find_watch_literals(self, model: Model) -> str:
        pass  # TODO: implement!


@frozen
class CNFFormula:

    def __init__(self, clauses: List[CNFClause]):
        self.clauses = clauses
        self.all_variables = set()
        for clause in self.clauses:
            clause_variables = clause.positive_literals + clause.negative_literals
            self.all_variables |= set(clause_variables)


    def __repr__(self) -> str:
        if len(self.clauses) == 0:
            return "T"

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


    def count_clauses_satisfied_by_model(self, model: Model) -> int:
        sat_counter = 0
        for clause in self.clauses:
            sat_value = clause.is_satisfied_under_model(model)
            if sat_value == SAT:
                sat_counter += 1
            elif sat_value == UNSAT:
                return UNSAT
        return sat_counter


    def is_satisfied_under_model(self, model: Model) -> str:
        num_satisfied = self.count_clauses_satisfied_by_model(model)
        if num_satisfied == UNSAT:
            return UNSAT

        return SAT if num_satisfied == len(self.clauses) else SAT_UNKNOWN


    def add_clause(self, new_clause: CNFClause):
        self.clauses.append(new_clause)
        clause_variables = new_clause.positive_literals + new_clause.negative_literals
        self.all_variables |= set(clause_variables)


    def update_with_model(self, model: Model):
        sat_counter = 0
        inferred_assignment = SAT_UNKNOWN

        for clause in self.clauses:
            result = clause.update_with_model(model)

            if result == UNSAT:
                return UNSAT, clause

            elif result == SAT:
                sat_counter += 1

            elif result == SAT_UNKNOWN:
                continue

            else:  # Result is a inferred assignment. Continue looping to make sure not UNSAT. Note that inferred_assignment might change
                inferred_assignment = result

        return SAT, None if sat_counter == len(self.clauses) else inferred_assignment, None


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
        # Map each inferred variable to the clause that caused it, at at which level that was
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
        assert variable not in self.total_model.keys()

        self.curr_level += 1
        self.decision_variables.append({variable: assignment})
        self.inferred_variables.append(dict())
        self.total_model[variable] = assignment
        self.causing_clauses[variable] = (ImplicationGraph.CAUSING_CLAUSE_OF_DECIDED_VARIABLES, self.curr_level)


    def add_inference(self, variable: str, assignment: bool, causing_clause: int):
        assert variable not in self.total_model.keys()

        self.inferred_variables[-1].update({variable: assignment})
        self.total_model[variable] = assignment
        self.causing_clauses[variable] = (causing_clause, self.curr_level)


    def get_index_of_causing_clause_of_variable(self, variable: str) -> int:
        return self.causing_clauses[variable][0]


    def get_decision_level_of_variable(self, variable: str) -> int:
        return self.causing_clauses[variable][1]


    def get_causing_variables(self, cnf_formula: CNFFormula, variable: str) -> Set[str]:
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
        assert self.conflict_clause is not None
        assert self.curr_level >= 1

        last_decision_variable = list(self.decision_variables[-1].keys())[0]  # List of dict only for level 0. From lvl. 1 always 1 decision var per level
        potential_uips = set(copy.deepcopy(self.total_model.keys()))
        potential_uips_distances = {potential_uip: math.inf for potential_uip in potential_uips}
        current_path = list()

        def dfs_helper(current_node):  # Finds all uips we must go through and their min distances from the conflict
            nonlocal potential_uips, potential_uips_distances

            current_path.append(current_node)
            if current_node == last_decision_variable:
                potential_uips = potential_uips.intesect(set(current_path))
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

        vars_to_resolve = (set(clause_to_resolve.positive_literals) & set(last_assigned_var_causing_clause.negative_literals)) | \
                          (set(clause_to_resolve.negative_literals) & set(last_assigned_var_causing_clause.positive_literals))
        assert len(vars_to_resolve) > 0

        new_pos_vars = list(set(clause_to_resolve.positive_literals + last_assigned_var_causing_clause.positive_literals) - vars_to_resolve)
        new_neg_vars = list(set(clause_to_resolve.negative_literals + last_assigned_var_causing_clause.negative_literals) - vars_to_resolve)
        return CNFClause(new_pos_vars, new_neg_vars)


    def get_last_assigned_var(self, clause_to_resolve: CNFClause) -> str:
        last_assigned_var = None
        last_assigned_var_decision_level = 0
        for cur_var in clause_to_resolve.get_all_variables():
            cur_decision_level = self.get_decision_level_of_variable(cur_var)
            if cur_decision_level > last_assigned_var_decision_level:
                last_assigned_var = cur_var
                last_assigned_var_decision_level = cur_decision_level

        assert last_assigned_var is not None
        return last_assigned_var


    def backjump_to_level(self, new_level) -> None:
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

