import copy

from logic_utils import frozen
from typing import List


@frozen
class CNFVariable:

    def __init__(self, name: str, is_negated: bool):
        self.name = name
        self.is_negated = is_negated


    def __repr__(self) -> str:
        return "~" + str(self.name) if self.is_negated else str(self.name)


    def __lt__(self, other: object):
        if not isinstance(other, CNFVariable):
            return True
        if self.name == other.name:
            return self.is_negated and not other.is_negated
        else:
            return self.name < other.name


    def __le__(self, other: object):
        return self < other or self == other


    def __eq__(self, other: object) -> bool:
        return isinstance(other, CNFVariable) and str(self) == str(other)


    def __ne__(self, other: object) -> bool:
        return not self == other


    def __gt__(self, other):
        return not self <= other


    def __ge__(self, other):
        return not self < other


    def __hash__(self) -> int:
        return hash(str(self))


@frozen
class CNFClause:

    def __init__(self, literals: List[CNFVariable]):
        self.literals = copy.deepcopy(literals)
        self.literals.sort()

        self.positive_literals = [literal for literal in literals if not literal.is_negated]
        self.positive_literals.sort()

        self.negative_literals = [literal for literal in literals if literal.is_negated]
        self.negative_literals.sort()


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
