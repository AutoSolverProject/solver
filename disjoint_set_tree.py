from first_order_logic.syntax import Term


# ToDo: define this class for a DAG according to the congruence closure algorithm
class Node:
    def __init__(self, term):
        self.term = term
        self.parent = self
        self.size = 1

    def __eq__(self, other):
        return Term.__eq__(self.term, other.term)

