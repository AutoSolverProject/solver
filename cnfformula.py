import copy
import math

from formula_utils import *
from logic_utils import frozen
from typing import List, Dict, Tuple

from propositional_logic.semantics import Model


@frozen
class CNFClause:

    def __init__(self, positive_literals: List[str] = None, negative_literals: List[str] = None):
        self.positive_literals = copy.deepcopy(positive_literals) if positive_literals else list()
        self.positive_literals.sort()

        self.negative_literals = copy.deepcopy(negative_literals) if negative_literals else list()
        self.negative_literals.sort()

        self.watch_literals = self.find_watch_literals(dict())


    def __repr__(self) -> str:
        my_repr = ""
        for pos in self.positive_literals:
            my_repr += str(pos) + " "

        for neg in self.negative_literals:
            my_repr += "~" + str(neg) + " "


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


    def update_with_model(self, model: Model):

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



    def is_satisfied_under_model(self, model: Model) -> str:
        for pos in self.positive_literals:
            if model.get(pos, False):
                return SAT

        for neg in self.negative_literals:
            if not model.get(neg, True):
                return SAT

        # No literal was satisfied, so SAT_UNKNOWN unless all of them are in the model, and then there's no chance for SAT
        all_literals = set(self.positive_literals + self.negative_literals)
        return UNSAT if all_literals.issubset(model.keys()) else SAT_UNKNOWN


    def find_watch_literals(self, model: Model) -> str:
        pass  # TODO: implement!


@frozen
class CNFFormula:

    def __init__(self, clauses: List[CNFClause]):
        self.clauses = clauses


    def __repr__(self) -> str:
        return self.clauses.__repr__()


    def __eq__(self, other: object) -> bool:
        return isinstance(other, CNFFormula) and self.clauses == other.clauses


    def __ne__(self, other: object) -> bool:
        return not self == other


    def __hash__(self) -> int:
        return hash(str(self))


    def __len__(self):
        return len(self.clauses)


    def update_with_model(self, model: Model):
        for clause in self.clauses:
            clause.update_with_model(model)


class ImplicationGraph:

    def __init__(self, decided_variables: Dict[str, bool] = None):
        decided_variables = copy.deepcopy(decided_variables) if decided_variables is not None else dict()

        self.curr_level = 0
        self.conflict_clause = None
        self.decision_variables = [decided_variables]
        self.inferred_variables = [dict()]
        self.total_model = decided_variables


    def __repr__(self) -> str:
        my_repr = ""
        for i in range(len(self.decision_variables)):
            my_repr += "LEVEL " + str(i) + ": " + "\n" \
                        + "Decided: " + str(self.decision_variables[i]) + "\n" \
                        + "Inferred: " + str(self.inferred_variables[i]) + "\n"
        return my_repr


    def __eq__(self, other: object) -> bool:
        return isinstance(other, ImplicationGraph) \
               and self.decision_variables == other.decision_variables \
               and self.inferred_variables == other.inferred_variables \
               and self.curr_level == other.curr_level


    def __ne__(self, other: object) -> bool:
        return not self == other


    def __hash__(self) -> int:
        return hash(str(self))


    def __len__(self):
        return self.curr_level


    def backjump_to_level(self, new_level):
        assert 0 <= new_level <= self.curr_level

        self.curr_level = new_level
        self.conflict_clause = None
        self.decision_variables = self.decision_variables[:self.curr_level + 1]
        self.inferred_variables = self.inferred_variables[:self.curr_level + 1]

        self.total_model = dict()
        for i in range(self.curr_level):
            self.total_model.update(self.decision_variables[i])
            self.total_model.update(self.inferred_variables[i])


    def add_inference(self, variable, assignment):
        assert variable not in self.total_model.keys()

        self.inferred_variables[-1][variable] = assignment
        self.total_model[variable] = assignment


    def add_decision(self, variable, assignment):
        assert variable not in self.total_model.keys()

        self.curr_level += 1
        self.decision_variables.append({variable: assignment})
        self.inferred_variables.append(dict())
        self.total_model[variable] = assignment


    def find_uip(self):
        assert self.conflict_clause is not None
        assert self.curr_level >= 1

        last_decision_variable = list(self.decision_variables[-1].keys())[0]
        potential_uips = set(copy.deepcopy(self.total_model.keys()))
        potential_uips_distances = {potential_uip: math.inf for potential_uip in potential_uips}
        current_path = list()

        def dfs_helper(current_node):  # Finds all uips we must go through and their min distances from the conflict
            nonlocal potential_uips, potential_uips_distances

            if current_node == self.conflict_clause:
                potential_uips = potential_uips.intesect(set(current_path))
                for node_index in range(len(current_path)):
                    curr_node = current_path[node_index]
                    curr_node_dist = len(current_path) - 1 - node_index
                    if curr_node_dist < potential_uips_distances[curr_node]:
                        potential_uips_distances[curr_node] = curr_node_dist

            else:
                current_path.add(current_node)
                for child in my_children:  # Todo: implement!
                    dfs_helper(child)
                current_path.pop()


        dfs_helper(last_decision_variable)  # Now we have all uips, and their distances

        closest_uip = None
        closest_uip_dist = math.inf
        for potential_uip in potential_uips:
            if 0 < potential_uips_distances[potential_uip] < closest_uip_dist:
                closest_uip = potential_uip
                closest_uip_dist = potential_uips_distances[closest_uip]

        return closest_uip


    def get_total_model(self) -> Model:
        return self.total_model
