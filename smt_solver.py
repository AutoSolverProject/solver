from sat_solver import *
from first_order_logic.syntax import *
from propositional_logic.syntax import Formula as PropositionalFormula
from disjoint_set_tree import *


def smt_solver(formula) -> Tuple[str, Model]:
    skeleton, substitution_map = formula.propositional_skeleton()
    state = SAT_UNKNOWN
    partial_assignment = Model()

    while state == SAT_UNKNOWN:
        state, partial_assignment = sat_solver(skeleton)

        assignment = assign_in_formula(partial_assignment, substitution_map)
        cc_value = check_congruence_closure(assignment, formula)
        if cc_value and len(partial_assignment.keys()) == len(skeleton.variables()):
            return SAT, assignment
        elif not cc_value:
            conflict = get_conflict(assignment)
            partial_assignment = sat_solver(skeleton, partial_model=partial_assignment, conflict=conflict)
        else:
            assignment = t_propagate(assignment, formula)
            for k, v in substitution_map.items():
                if v in assignment.keys() and assignment[v]:
                    partial_assignment[k] = True
            partial_assignment = sat_solver(skeleton, partial_model=partial_assignment)

    return state, partial_assignment


def assign_in_formula(partial_assignment, sub_map):
    assignment = dict()
    for a, v in partial_assignment.items():
        assignment[sub_map[a]] = v
    return assignment


def check_congruence_closure(assignment, formula):
    subterms = sort_by_length(get_subterms(formula))
    disjoint_set = make_set(subterms)
    equalities = get_equalities(assignment)
    inequalities = get_inequalities(assignment)
    for equality in equalities:
        node1, node2 = get_nodes(equality, disjoint_set)
        union(node1, node2)
    for equality in inequalities:
        node1, node2 = get_nodes(equality, disjoint_set)
        if find(node1) == find(node2):
            return False
    return True


def t_propagate(assignment, formula):
    subterms = sort_by_length(get_subterms(formula))
    disjoint_set = make_set(subterms)
    unassigned_equalities = get_equalities_in_formula(formula)
    equalities = get_equalities(assignment)
    for equality in equalities:
        node1, node2 = get_nodes(equality, disjoint_set)
        union(node1, node2)
    for equality in unassigned_equalities:
        args = equality.arguments
        left, right = args[0], args[1]
        if find(left) == find(right):
            assignment[equality] = True
    return assignment


def get_equalities_in_formula(formula):
    if is_equality(formula.root):
        return {formula}
    elif is_binary(formula.root) or is_unary(formula.root):
        equalities = get_equalities_in_formula(formula.first)
        if is_binary(formula.root):
            equalities = equalities | get_equalities_in_formula(formula.second)
        return equalities


def get_conflict(assignment):
    formula = '('
    num_vars = len(assignment.keys())
    i = 1
    for a, v in assignment.items():
        if v:
            formula += '~' + a
        else:
            formula += a
        if i == num_vars:
            formula += ')'*(num_vars-1)
        else:
            formula += '|'
            if i < num_vars - 1:
                formula += '('
        i += 1
    return PropositionalFormula.parse(formula)


def get_subterms(formula):
    if is_equality(formula.root):
        return get_subterms_in_term(formula.arguments[0]).union(get_subterms_in_term(formula.arguments[1]))
    elif is_unary(formula.root):
        return get_subterms(formula.first)
    return get_subterms(formula.first) | get_subterms(formula.second)


def get_subterms_in_term(term):
    if is_function(term.root):
        subs = {term}
        for arg in term.arguments:
            subs.update(get_subterms_in_term(arg))
        return subs
    return {term}


def sort_by_length(subterms):
    subterms = list(subterms)
    subterms = sorted(subterms)
    return set(subterms)


def get_equalities(assignment):
    equalities = set()
    for equality in assignment:
        if assignment[equality]:
            equalities.add(equality)
    return equalities


def get_inequalities(assignment):
    equalities = set()
    for equality in assignment:
        if not assignment[equality]:
            equalities.add(equality)
    return equalities


def make_set(subterms):
    nodes = dict()
    for term in subterms:
        nodes[term] = (Node(term))
        if is_function(term.root): # ToDo : fix this to make a correct DAG
            for arg in term.arguments:
                nodes[arg].parent = nodes[term]
    return nodes.values()


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


def get_primitives_in_formula(quantifier_free):
    root = quantifier_free.root
    if is_relation(root) or is_equality(root):
        primitives = set()
        for arg in quantifier_free.argument:
            primitives.update(get_primitives_in_term(arg))
        return primitives
    elif is_unary(root):
        return get_primitives_in_formula(quantifier_free.first)
    return get_primitives_in_formula(quantifier_free.first) | (
        get_primitives_in_formula(quantifier_free.second))


def get_primitives_in_term(term):
    primitives = set()
    if is_function(term.root):
        primitives.add(term)
        for arg in term.arguments:
            primitives.update(get_primitives_in_term(arg))
    return primitives


def test1():
    formula = Formula.parse('((f(a,c)=b&f(a,g(b))=b)|~c=g(b))')
    subs = get_subterms(formula)
    sort_by_length(subs)


def main():
    test1()


if __name__ == '__main__':
    main()
