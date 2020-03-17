
from logic_utils import frozen
from typing import List


@frozen
class CNFClause:

    def __init__(self, variables: List[str]):
        self.variables = variables


    def __repr__(self) -> str:
        return self.variables.__repr__()


    def __eq__(self, other: object) -> bool:
        return isinstance(other, CNFClause) and str(self) == str(other)


    def __ne__(self, other: object) -> bool:
        return not self == other


    def __hash__(self) -> int:
        return hash(str(self))


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
        return isinstance(other, CNFFormula) and str(self) == str(other)


    def __ne__(self, other: object) -> bool:
        return not self == other


    def __hash__(self) -> int:
        return hash(str(self))
