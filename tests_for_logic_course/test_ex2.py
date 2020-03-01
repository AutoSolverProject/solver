# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: test_ex2.py

"""Tests all Chapter 2 tasks."""

from propositional_logic.semantics_test import *
from propositional_logic.reductions_test import *

def test_task1(debug=False):
    test_evaluate(debug)

def test_task2(debug=False):
    test_all_models(debug)

def test_task3(debug=False):
    test_truth_values(debug)

def test_task4(debug=False):
    test_print_truth_table(debug)   

def test_task5(debug=False):
    test_is_tautology(debug)
    test_is_contradiction(debug)
    test_is_satisfiable(debug)

def test_task6(debug=False):
    test_synthesize_for_model(debug)

def test_task7(debug=False):
    test_synthesize(debug)

def test_task8(debug=False):
    test_graph3coloring_to_formula(debug)
    test_assignment_to_3coloring(debug)
    test_tricolor_graph(debug)

test_task1(True)
test_task2(True)
test_task3(True)
test_task4(True)
test_task5(True)
test_task6(True)
test_task7(True)
#test_task8(True) # Optional
