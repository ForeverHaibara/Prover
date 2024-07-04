from typing import Union

import sympy as sp


def taylor(
        f: Union[str, sp.Expr, sp.core.FunctionClass], 
        n = 3,
        x0 = 0,
    ) -> sp.Poly:
    """
    Return the taylor expansion of f at x = x0.
    """
    x = None
    if isinstance(f, str):
        try:
            f = getattr(sp, f)
        except AttributeError:
            raise AttributeError('Function %s is not supported.'%f)
    if isinstance(f, sp.core.function.FunctionClass):
        x = sp.symbols('x')
        f = f(x)

    if x is None:
        x = f.free_symbols.pop()

    poly = f.series(x, x0, n + 1).removeO().as_poly(x)
    if poly is None:
        raise ValueError('Failed to compute taylor expansion of %s at x = %s.'%(f, x0))
    return poly


def pade(f, m = 3, n = None):
    """
    Compute pade expansion of a function at x = 0.

    References
    ----------
    [1] https://math.stackexchange.com/questions/860293 
    
    [2] https://zhuanlan.zhihu.com/p/92873681 
    """
    
    if n is None: n = m
    if isinstance(f, str):
        return pade(f = taylor(f, m + n), m = m, n = n)
    elif (isinstance(f, sp.Expr) and not isinstance(f, sp.Poly)) or isinstance(f, sp.core.function.FunctionClass):
        return pade(f = taylor(f, m + n), m = m, n = n)
    else:
        t = sp.symbols('x')
    
    if isinstance(f, sp.Poly):
        f = f.all_coeffs()[::-1]
    
    if len(f) < m + n + 1:
        f = f + [0] * (m + n + 1 - len(f))


    A = sp.Matrix.zeros(n)
    b = sp.Matrix.zeros(n, 1)
    for i in range(n):
        for j in range(n):
            A[i,j] = f[m+i-j]
    for i in range(n):
        b[i] = -f[m+i+1]
    
    # denominator / numerator
    q = [1] + list(A.solve(b))
    p = [0] * (m+1)
    for i in range(m+1):
        p[i] = sum(f[i-j] * q[j] for j in range(min(n+1,i+1)))

    v = sp.cancel(sum([p[i] * t ** i for i in range(m+1)]) / 
                    sum([q[i] * t ** i for i in range(n+1)]))

    return v