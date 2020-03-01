

class Tree:
    class Node:
        def __init__(self, term):
            self.term = term
            self.parent = self
            self.rank = 0
            self.size = 1

    def __init__(self, root):
        self.root = root
        self.size = root.size
