import copy

from logic_utils import frozen
from typing import List

from propositional_logic.semantics import Model


@frozen
class CNFClause:

    def __init__(self, positive_literals: List[str] = None, negative_literals: List[str] = None):
        self.positive_literals = copy.deepcopy(positive_literals) if positive_literals else list()
        self.positive_literals.sort()

        self.negative_literals = copy.deepcopy(negative_literals) if negative_literals else list()
        self.negative_literals.sort()

        self.watch_literals = literals[0: max_literal_index]


    def __repr__(self) -> str:
        return self.literals.__repr__()


    def __eq__(self, other: object) -> bool:
        return isinstance(other, CNFClause) and self.literals == other.literals


    def __ne__(self, other: object) -> bool:
        return not self == other


    def __hash__(self) -> int:
        return hash(str(self))


    def __len__(self):
        return len(self.literals)


    def get_propagation(self):
        pass


    def update_with_model(self, model: Model):
        for clause in self.clauses:
            clause.update_with_model(model)




@frozen
class CNFFormula:

    def __init__(self, clauses: List[CNFClause]):
        self.clauses = clauses


    def __repr__(self) -> str:
        my_repr = ""
        for i in range(len(self.clauses)):
            my_repr += str(i) + self.clauses[i].__repr__() + "\n"
        return my_repr


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
