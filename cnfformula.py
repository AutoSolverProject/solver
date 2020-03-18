import copy
import math

from logic_utils import frozen
from typing import List, Dict

from propositional_logic.semantics import Model


@frozen
class CNFClause:

    def __init__(self, positive_literals: List[str] = None, negative_literals: List[str] = None):
        self.positive_literals = copy.deepcopy(positive_literals) if positive_literals else list()
        self.positive_literals.sort()

        self.negative_literals = copy.deepcopy(negative_literals) if negative_literals else list()
        self.negative_literals.sort()

        self.watch_literals = get_watch_literals(dict())


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
        for clause in self.clauses:
            clause.update_with_model(model)


    def get_watch_literals(self, model):
        pass


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

    def __init__(self, decision_variables: List[Dict[str, bool]], inferred_variables: List[Dict[str, bool]]):
        assert len(inferred_variables) == len(decision_variables)
        self.all_variables = set()  # TODO: fill
        assert len(
            set(decision_variables.keys()).intersection(set(inferred_variables.keys()))) == 0

        self.decision_variables = copy.deepcopy(decision_variables)
        self.inferred_variables = copy.deepcopy(inferred_variables)
        self.curr_level = len(self.decision_variables) - 1  # Minus 1 because the first level doesn't involve deciding

        self.conflict = None


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
               and self.inferred_variables == other.inferred_variables


    def __ne__(self, other: object) -> bool:
        return not self == other


    def __hash__(self) -> int:
        return hash(str(self))


    def __len__(self):
        return len(self.decision_variables)


    def backjump_to_level(self, new_level):
        assert 0 <= new_level <= self.curr_level
        self.curr_level = new_level
        self.decision_variables = self.decision_variables[:self.curr_level + 1]
        self.inferred_variables = self.inferred_variables[:self.curr_level + 1]


    def add_inference(self, variable, assignment):
        assert variable not in self.all_variables
        self.inferred_variables[-1][variable] = assignment


    def find_uip(self):
        assert self.conflict is not None
        assert self.curr_level >= 1

        last_decision_variable = list(self.decision_variables[-1].keys())[0]
        potential_uips = copy.deepcopy(self.all_variables)
        potential_uips_distances = {potential_uip: math.inf for potential_uip in potential_uips}
        current_path = list()

        def dfs_helper(current_node):  # Finds all uips we must go through and their min distances from the conflict
            nonlocal potential_uips, potential_uips_distances

            if current_node == self.conflict:
                potential_uips = potential_uips.intesect(set(current_path))
                for node_index in range(len(current_path)):
                    curr_node = current_path[node_index]
                    curr_node_dist = len(current_path) - 1 - node_index
                    if curr_node_dist < potential_uips_distances[curr_node]:
                        potential_uips_distances[curr_node] = curr_node_dist

            else:
                current_path.add(current_node)
                for child in my_children:
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
