from typing import Union, List

import sympy as sp

def radsimp(expr: Union[sp.Expr, List[sp.Expr]]) -> sp.Expr:
    """
    Rationalize the denominator by removing square roots. Wrapper of sympy.radsimp.
    Also refer to sympy.simplify.
    """
    if isinstance(expr, (list, tuple)):
        return [radsimp(e) for e in expr]
    if not isinstance(expr, sp.Expr):
        expr = sp.sympify(expr)

    numer, denom = expr.as_numer_denom()
    n, d = sp.fraction(sp.radsimp(1/denom, symbolic=False, max_terms=1))
    # if n is not S.One:
    expr = (numer*n).expand()/d
    return expr


def rational_between(x, y):
    """
    Find a rational number between x and y.
    """
    tolerance = min(abs(y - x) / sp.S(4) * 3, sp.Rational(1,100))
    prec = sp.floor(-sp.log(tolerance, 10))
    middle = ((x + y) / sp.S(2)).n(prec)
    return sp.nsimplify(middle, tolerance = tolerance, rational = True)