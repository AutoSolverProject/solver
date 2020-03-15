from first_order_logic.syntax import *
from first_order_logic.semantics import *
from logic_utils import __prefix_with_index_sequence_generator


x_gen = __prefix_with_index_sequence_generator('x')
y_gen = __prefix_with_index_sequence_generator('y')


class Tuf(Model):
    reflex = Formula.parse('Ax[x=x]')
    symmetry = Formula.parse('Ax[Ay[(x=y->y=x)]]')
    trans = Formula.parse('Ax[Ay[Az[((x=y&y=z)->x=z)]]]')
    axioms = {reflex, symmetry, trans}

    def __init__(self, universe, constants, relations, functions):
        super(Tuf, self).__init__({str(elem) for elem in universe},
                                  {c: str(c) for c in constants}, relations, functions)
        for func, arity in self.function_arities.items():
            x, y = [], []
            conjunct = None
            for i in range(arity):
                x.append(next(x_gen))
                y.append(next(y_gen))
                if conjunct is None:
                    conjunct = Formula('=', [Term(x[i]), Term(y[i])])
                else:
                    conjunct = Formula('&', conjunct, Formula('=', [Term(x[i]), Term(y[i])]))
            func_x = Formula(func, [Term(v) for v in x])
            func_y = Formula(func, [Term(v) for v in y])
            formula = Formula('->', conjunct, Formula('=', func_x, func_y))
            for v in y[::-1]:
                formula = Formula('A', v, formula)
            for v in x[::-1]:
                formula = Formula('A', v, formula)
            self.axioms.add(formula)
        if self.is_model_of(self.axioms):
            print('T-model')
        else:
            print('not T-model')
    
