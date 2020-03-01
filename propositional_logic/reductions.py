# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositional_logic/reductions.py

"""Reduction between computational search problems."""

from __future__ import annotations
from typing import Mapping, Optional, Set, Tuple, Union

from propositions.syntax import *
from propositions.semantics import *

#: A graph on a vertex set of the form (1, ..., `n_vertices`\ ), represented by
#: the number of vertices `n_vertices` and a set of edges over the vertices.
Graph = Tuple[int, Set[Tuple[int, int]]] 

def is_valid_3coloring(graph: Graph, coloring: Mapping[int, int]) -> bool:
    """Checks whether the given coloring is a valid coloring of the given graph
    by the colors 1, 2, and 3.

    Parameters:
        graph: graph to check.
        coloring: mapping from the edges of the given graph to colors, to check.

    Returns:
        ``True`` if the given coloring is a valid coloring of the given graph by
        the colors 1, 2, and 3, ``False`` otherwise.
    """
    (n_vertices, edges) = graph
    for edge in edges:
        assert len(edge) == 2
        for vertex in edge:
            assert 1 <= vertex <= n_vertices
    for vertex in range(1, n_vertices + 1):
        if vertex not in coloring.keys() or coloring[vertex] not in {1, 2, 3}:
            return False
    for edge in edges:
        if coloring[edge[0]] == coloring[edge[1]]:
            return False
    return True

def graph3coloring_to_formula(graph: Graph) -> Formula:
    """Efficiently reduces the 3-coloring problem of the given graph into a
    satisfiability problem.

    Parameters:
        graph: graph whose 3-coloring problem to reduce.
       
    Returns:
        A propositional Formula that is satisfiable if and only if the given
        graph is 3-colorable.
    """
    (n_vertices, edges) = graph
    for edge in edges:
        assert len(edge) == 2
        for vertex in edge:
            assert 1 <= vertex <= n_vertices
    # Optional Task 2.8a

def assignment_to_3coloring(graph: Graph, assignment: Model) -> \
    Mapping[int, int]:
    """Efficiently transforms an assignment to the formula corresponding to the
    3-coloring problem of the given graph, into a 3-coloring of the given graph
    so that the 3-coloring is valid if and only if the given assignment is
    satisfying.

    Parameters:
        graph: graph to produce a 3-coloring for.
        assignment: an assignment to the variables of the formula returned by
            `graph3coloring_to_formula`\ ``(``\ `graph`\ ``)``.

    Returns:
        A 3-coloring of the given graph by the colors 1, 2, and 3 that is valid
        if and only if the given assignment satisfies the formula
        `graph3coloring_to_formula`\ ``(``\ `graph`\ ``)``.
    """
    (n_vertices, edges) = graph
    formula = graph3coloring_to_formula(graph)
    assert evaluate(formula, assignment)
    # Optional Task 2.8b

def tricolor_graph(graph: Graph) -> Union[Mapping[int, int], None]:
    """Computes a 3-coloring of the given graph.

    Parameters:
        graph: graph to 3-color.

    Returns:
        An arbitrary 3-coloring of the given graph if it is 3-colorable,
        ``None`` otherwise.
    """
    formula = graph3coloring_to_formula(graph)
    for assignment in all_models(list(formula.variables())):
        if evaluate(formula, assignment):
            return assignment_to_3coloring(graph, assignment)
    return None
