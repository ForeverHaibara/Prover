import sympy as sp

from ...basic.expansions import pade as _pade
from ..proof import Proof

class _prove_pade:
    def __new__(cls, *args, **kwargs):
        return cls._solve(*args, **kwargs)
    
    @classmethod
    def _solve(cls, f, m = 3, n = None):
        if n is None:
            n = m
        if isinstance(f, str):
            try:
                f = getattr(sp, f)
            except AttributeError:
                raise  AttributeError("Function '%s' is not supported."%f)

        try:
            func = getattr(cls, f.__name__)
        except AttributeError:
            return None

        if func is not None:
            txt = func(f, m, n)
            txt = '$$\\begin{aligned}%s\\end{aligned}$$'%(txt)
            return Proof(txt)

    @classmethod
    def exp(cls, f, m, n):
        pade = _pade(f, m, n)
        result = 'f(x) &= \\ln\\left(%s\\right) - x\\\\\n'%(sp.latex(pade))
        derv = sp.cancel(pade.diff() / pade - 1)
        result += 'f\'(x) &= %s \\%ceqslant 0'%(
            sp.latex(derv), 'g' if m <= n+1 else 'l')
        return result

    @classmethod
    def log(cls, f, m, n):
        t = sp.symbols('x')
        assert m >= n, 'Only support m >= n for log(x).'
        pade = _pade(sp.log(t+1), m, n)
        result = 'f(x) &= %s - \\ln(x+1)\\\\\n'%(sp.latex(pade))
        derv = sp.cancel(-(t+1)**(-1) + pade.diff(t))
        result += 'f\'(x) &= %s \\%ceqslant 0'%(
            sp.latex(derv), 'g' if (m - n) % 2 == 1 else 'l')
        return result

    @classmethod
    def sin(cls, f, m, n):    
        t = sp.symbols('x')
        assert m == n and m % 2 == 1, 'Only support m = n are equal odd numbers for sin(x).'
        
        pade = _pade(f, m, n)
        p , q = sp.fraction(pade)

        if m % 4 == 1:
            p , q = -p, -q
        # f(x) = qsinx - p
        result = 'f(x) &= \\left(%s\\right)\\sin x -\\left(%s\\right)\quad (x\\geqslant 0)\\\\\n'%(
                    sp.latex(q), sp.latex(p))

        w = p
        p = sp.S(0)
        for i in range(m + 1):
            # qsinx + pcosx -> (q' - p)sinx + (q + p')cosx
            q , p = q.diff(t) - p , q + p.diff(t)
            # if verbose >= 1 and i < m:
            #     w = w.diff(t)
            #     result += 'f^{(%d)}(x) &= \\left(%s\\right)\\sin x + \\left(%s\\right)\\cos x - \\left(%s\\right)\\\\\n'%(
            #         i + 1, sp.latex(q), sp.latex(p), sp.latex(w))

        result += 'f^{(%d)}(x) &= \\left(%s\\right)\\sin x + \\left(%s\\right)\\cos x\\\\\n'%(
                    m + 1, sp.latex(q), sp.latex(p))

        result += 'g(x) &= x + \\arctan\\frac{%s}{%s}\\quad (x\\geqslant 0)\\\\\n'%(sp.latex(p), sp.latex(q))
        derv    = sp.cancel(1 + 1 / (1 + p * p / q / q) * (p / q).diff(t))
        result += 'g\'(x) &= %s\\geqslant 0\\\\\n'%(sp.latex(derv))

        result += '\\Rightarrow g(x)&\\geqslant 0\ (x\\geqslant 0)\\Rightarrow f^{(%d)}(x)'%(m + 1)
        result += '\\geqslant 0\\Rightarrow \\cdots \\Rightarrow f(x)\\geqslant 0\\ (x\\geqslant 0)\\\\\n'

        p , q = sp.fraction(pade)
        result += '\\Rightarrow \\sin x&\\%ceqslant \\frac{%s}{%s}\\quad (x\\geqslant 0)'%(
                        'g' if m % 4 == 3 else 'l', sp.latex(p), sp.latex(q))
        return result

    @classmethod
    def cos(cls, f, m, n):
        t = sp.symbols('x')        
        assert m == n and m % 2 == 0, 'Only support m = n are equal even numbers for cos(x).'

        pade = _pade(f, m, n)
        p , q = sp.fraction(pade)#, power = power)

        if m % 4 == 0:
            p , q = -p, -q
        # f(x) = qcosx - p
        result = 'f(x) &= \\left(%s\\right)\\cos x -\\left(%s\\right)\quad (x\\geqslant 0)\\\\\n'%(
                    sp.latex(q), sp.latex(p))

        w = p
        p = t - t # = 0
        for i in range(m + 1):
            # qcosx + psinx -> (q' + p)cosx + (-q + p')sinx
            q , p = q.diff(t) + p , p.diff(t) - q
            # if verbose >= 1 and i < m:
            #     w = w.diff(t)
            #     result += 'f^{(%d)}(x) &= \\left(%s\\right)\\cos x + \\left(%s\\right)\\sin x - \\left(%s\\right)\\\\\n'%(
            #         i + 1, sp.latex(q), sp.latex(p), sp.latex(w))

        result += 'f^{(%d)}(x) &= \\left(%s\\right)\\cos x + \\left(%s\\right)\\sin x\\\\\n'%(
                    m + 1, sp.latex(q), sp.latex(p))

        result += 'g(x) &= x + \\arctan\\frac{%s}{%s}\\quad (x\\geqslant 0)\\\\\n'%(sp.latex(q), sp.latex(p))
        derv    = sp.cancel(1 + 1 / (1 + q * q / p / p) * (q / p).diff(t))
        result += 'g\'(x) &= %s\\geqslant 0\\\\\n'%(sp.latex(derv))

        result += '\\Rightarrow g(x)&\\geqslant 0\ (x\\geqslant 0)\\Rightarrow f^{(%d)}(x)'%(m + 1)
        result += '\\geqslant 0\\Rightarrow \\cdots \\Rightarrow f(x)\\geqslant 0\\ (x\\geqslant 0)\\\\\n'

        p , q = sp.fraction(pade)
        result += '\\Rightarrow \\cos x&\\%ceqslant \\frac{%s}{%s}\\quad (x\\geqslant 0)'%(
                        'g' if m % 4 == 2 else 'l', sp.latex(p), sp.latex(q))
        return result

    @classmethod
    def tan(cls, f, m, n):
        t = sp.symbols('x')
        assert m == n and m % 2 == 1, 'Only support m = n are equal odd numbers for tan(x).'
        pade = _pade(f, m, n)

        result  = 'f(x) &= x - \\arctan %s\\\\\n'%(sp.latex(pade))
        derv = sp.cancel(1 - pade.diff(t) / (1 + pade * pade))
        result += 'f\'(x) &= %s \\geqslant 0'%(sp.latex(derv))
        return result


prove_pade = _prove_pade._solve