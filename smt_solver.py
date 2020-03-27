from sat_solver import *
from first_order_logic.syntax import Formula as FO_Formula
from first_order_logic.syntax import *
from propositional_logic.syntax import Formula as PropositionalFormula
from disjoint_set_tree import *


def smt_solver(formula: FO_Formula) -> Tuple[str, Model]:
    skeleton, substitution_map = formula.propositional_skeleton()
    state, model_over_skeleton, updated_skeleton = sat_solver(skeleton)

    while state != UNSAT:

        model_over_formula = model_over_skeleton_to_model_over_formula(model_over_skeleton, substitution_map)
        congruence_closure_unviolated = check_congruence_closure(model_over_formula, formula)

        if state == SAT and congruence_closure_unviolated and len(model_over_skeleton.keys()) == len(updated_skeleton.variables()):
            return state, model_over_formula

        elif not congruence_closure_unviolated:
            conflict = get_conflict(model_over_formula)
            state, model_over_skeleton, updated_skeleton = \
                sat_solver(skeleton, model_over_skeleton, conflict=conflict)

        else:
            model_over_formula = t_propagate(model_over_formula, formula)
            model_over_skeleton = dict(model_over_skeleton)
            for k, v in substitution_map.items():
                if v in model_over_formula.keys() and model_over_formula[v]:
                    model_over_skeleton[k] = True
            state, model_over_skeleton, updated_skeleton = sat_solver(skeleton, model_over_skeleton)
    return UNSAT



def model_over_skeleton_to_model_over_formula(partial_assignment, sub_map):
    assignment = {sub_map[skeleton_var]: skeleton_var_assignment for skeleton_var, skeleton_var_assignment in partial_assignment.items()}
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
    inequalities = get_inequalities(assignment)
    for equality in equalities:
        node1, node2 = get_nodes(equality, disjoint_set)
        union(node1, node2)
    for equality in unassigned_equalities:
        left, right = get_nodes(equality, disjoint_set)
        if find(left) == find(right):
            assignment[equality] = True
        else:
            for inequality in inequalities:
                left_term, right_term = get_nodes(inequality, disjoint_set)
                if left == left_term or left == right_term:
                    common_term, uncommon_term = left, right
                elif right == left_term or right == right_term:
                    common_term, uncommon_term = right, left
                else:
                    continue
                if common_term == left_term:
                    suspect_term = right_term
                else:
                    suspect_term = left_term
                if find(uncommon_term) == find(suspect_term):
                    assignment[equality] = False
                    break
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
    subs = {term}
    if is_function(term.root):
        for arg in term.arguments:
            subs.update(get_subterms_in_term(arg))
    return subs


def sort_by_length(subterms):
    return sorted(list(subterms))


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
        if is_function(term.root):
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
    formula1 = Formula.parse('((f(a,c)=b|f(a,g(b))=b)&~c=g(b))')
    subs = get_subterms(formula1)
    sort_by_length(subs)


def test2():
    formula2 = Formula.parse('(f(f(f(a)))=a&(f(f(f(f(f(a)))))=a&~f(a)=a))')
    model2 = {Formula.parse('f(f(f(a)))=a'): True, Formula.parse('f(f(f(f(f(a)))))=a'): True, Formula.parse('f(a)=a'): False}
    check_congruence_closure(model2, formula2)


def test3():
    formula3 = Formula.parse('(g(a)=c&((~f(g(a))=f(c)|g(a)=d)&~c=d))')
    model3 = {Formula.parse('g(a)=c'): True, Formula.parse('c=d'): False}
    t_propagate(model3, formula3)


def main():
    test3()


if __name__ == '__main__':
    main()
