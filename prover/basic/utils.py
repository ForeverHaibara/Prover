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


def congruence(M: sp.Matrix) -> Union[None, tuple]:
    """
    Write a symmetric matrix as a sum of squares.
    M = U.T @ S @ U where U is upper triangular and S is diagonal.

    Returns
    -------
    U : sp.Matrix | np.ndarray
        Upper triangular matrix.
    S : sp.Matrix | np.ndarray
        Diagonal vector (1D array).

    Return None if M is not positive semidefinite.
    """
    M = M.copy()
    n = M.shape[0]
    if isinstance(M[0,0], sp.Expr):
        U, S = sp.Matrix.zeros(n), sp.Matrix.zeros(n, 1)
        One = sp.S.One
    else:
        U, S = np.zeros((n,n)), np.zeros(n)
        One = 1
    for i in range(n-1):
        if M[i,i] > 0:
            S[i] = M[i,i]
            U[i,i+1:] = M[i,i+1:] / (S[i])
            U[i,i] = One
            M[i+1:,i+1:] -= U[i:i+1,i+1:].T @ (U[i:i+1,i+1:] * S[i])
        elif M[i,i] < 0:
            return None
        elif M[i,i] == 0 and any(_ for _ in M[i+1:,i]):
            return None
    U[-1,-1] = One
    S[-1] = M[-1,-1]
    if S[-1] < 0:
        return None
    return U, S

