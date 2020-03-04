from sat_solver import *
from first_order_logic.syntax import *
from disjoint_set_tree import *


def solver(formula):
    skeleton, sub_map = formula.propositional_skeleton()
    partial_assignment = get_assignment(skeleton)
    if partial_assignment == "UNSAT":
        return "UNSAT"
    else:
        assignment = assign_in_formula(partial_assignment, sub_map)
        cc_value = check_congruence_closure(assignment, formula)



def check_congruence_closure(assignment, formula):
    subterms = get_subterms(formula)
    disjoint_set = make_set(subterms)
    equalities = get_equalities(formula)
    inequalities = get_inequalities(formula)
    inequals = set()
    for equality in equalities:
        if assignment[equality]:
            node1, node2 = get_nodes(equality, disjoint_set)
            union(node1, node2)
        else:
            inequals.add(equality)
    for equality in inequalities:
        if assignment[equality]:
            node1, node2 = get_nodes(equality, disjoint_set)
            union(node1, node2)
        else:
            inequals.add(equality)
    for equality in inequals:
        node1, node2 = get_nodes(equality, disjoint_set)
        if find(node1) == find(node2):
            return False
    return True


def get_subterms(formula):
    if is_equality(formula.root):
        return {formula.arguments[0], formula.arguments[1]}
    elif is_unary(formula.root):
        return get_subterms(formula.first)
    return get_subterms(formula.first) | get_subterms(formula.second)


def get_equalities(formula):
    if is_equality(formula.root):
        return {formula}
    elif is_binary(formula.root):
        return get_equalities(formula.first) | get_equalities(formula.second)
    elif is_unary(formula):
        return get_inequalities(formula.first)


def get_inequalities(formula):
    if is_equality(formula.root):
        return set()
    elif is_binary(formula.root):
        return get_equalities(formula.first) | get_equalities(formula.second)
    elif is_unary(formula):
        return get_equalities(formula.first)


def make_set(subterms):
    disjoint_sets = set()
    for term in subterms:
        disjoint_sets.add(Node(term))
    return disjoint_sets


def find(term):
    if term.parent != term:
        term.parent = find(term.parent)
    return term.parent


def union(term1, term2):
    x_root = find(term1)
    y_root = find(term2)

    if x_root == y_root:
        pass
    if x_root.size < y_root.size:
        x_root, y_root = y_root, x_root
    y_root.parent = x_root
    x_root.size = x_root.size + y_root.size


def get_nodes(equality, disjoint_set):
    node1, node2 = None, None
    for node in disjoint_set:
        if node.term == equality.arguments[0]:
            node1 = node
        elif node.term == equality.arguments[1]:
            node2 = node
        if node1 is not None and node2 is not None:
            break
    return node1, node2
