from first_order_logic.syntax import *



class Tuf:
    reflex = Formula.parse('Ax[x=x]')
    symmetry = Formula.parse('Ax[Ay[(x=y->y=x)]]')
    trans = Formula.parse('Ax[Ay[Az[((x=y&y=z)->x=z)]]]')

    def __init__(self, ):
