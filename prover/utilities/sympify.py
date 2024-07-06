from sympy.core import Tuple, sympify
from sympy.utilities.iterables import iterable

def sympified_tuple(w):
    if not iterable(w):
        return Tuple(sympify(w))
    return Tuple(*map(sympify, w))
