from typing import Union

import sympy as sp

from .approximation import prove_approx
from ..proof import Proof


def _is_a_func_and_a_rational(formula):
    """
    Check whether formula == r*f(p) + q where r,p,q are rational and f is a function.
    Return r,f,p,q if True. Otherwise return None.
    """
    if not isinstance(formula, sp.Expr) or len(formula.args) != 2:
        return False
    if isinstance(formula, sp.Add) and isinstance(formula.args[0], sp.Rational):
        other = formula.args[1]
        def _is_a_func_of_rational(x):
            """Check whether formula == f(p) where p is rational and f is a function."""
            if len(x.args) == 1 and isinstance(x.args[0], sp.Rational):
                from sympy.functions.elementary.exponential import log, exp
                from sympy.functions.elementary.trigonometric import sin, cos, atan
                if isinstance(x, (log, exp, sin, cos, atan)):
                    return (x.func, x.args[0])
            elif len(x.args) == 0:
                if x == sp.E:
                    return (sp.exp, sp.S(1))

        check_func1 = _is_a_func_of_rational(other)
        if check_func1:
            return (sp.S(1), check_func1[0], check_func1[1], formula.args[0])

        if isinstance(other, sp.Mul) and len(other.args) == 2:
            r = other.args[0]
            if isinstance(r, sp.Rational):
                check_func2 = _is_a_func_of_rational(other.args[1])
                if check_func2:
                    return (r, check_func2[0], check_func2[1], formula.args[0])

    return False

def solve(formula: Union[sp.Expr, str], **kwargs):
    """
    A heuristic solver for arbitrary input. It automatically
    check the input and use the appropriate method to solve it.
    """
    if isinstance(formula, str):
        formula = sp.sympify(formula)

    check_func = _is_a_func_and_a_rational(formula)
    if check_func != False:
        r, func, a, b = check_func
        solution = prove_approx(func, a, -b/r, **kwargs)
        if solution is not None:
            return solution

    if formula.is_constant():
        return Proof('$$%s\\approx %s$$'%(sp.latex(formula), formula.n(40)))