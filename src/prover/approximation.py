import sympy as sp

from ..basic.expansions import pade as _pade
from .proof import Proof

def prove_approx(
        x,
        y,
        f = 'exp',
        maxiter = 200,
    ):
    """
    Prove f(x) >= y or f(x) <= y.

    Parameters
    -------
    f: str
        one of ['e', 'exp', 'ln', 'log']
    """

    functions = ['e', 'exp', 'ln', 'log']
    assert f in functions, 'Function f should be one of %s, but received %s.'%(functions, f)

    def lt(x, b = False):
        t = sp.latex(x) 
        if b:
            if x < 0 or '.' in t or 'f' in t:
                t = '\\left(' + t + '\\right)'
        return t
        
    x, y = sp.Rational(x), sp.Rational(y)
    
    original_f = f
    original_x = x
    original_y = y 

    if f[0] == 'l': # log x ~ y <=> x ~ e^y
        x, y = y, x
        f = 'e'

    if f[0] == 'e':
        if x < 0:
            x, y = -x, 1 / y
        ytext = lt(y)

        great = y <= 0 or x > sp.log(y)
        if great:
            t = sp.Rational(0)
            c = sp.Rational(1)
            for i in range(maxiter):
                t += c 
                c = c * x / (i + 1)
                if t > y:
                    break 
            else:
                assert False, 'Proof failed within %d steps. Please use more iterations.'%(maxiter)

            txt = '$$e^{%s} > \\sum_{k=0}^{%d} \\frac{%s^k}{k!} = %s > %s$$'%(
                        lt(x),i,lt(x,1),lt(t),ytext)
        else:
            t = sp.Rational(0)
            c = sp.Rational(1)
            for i in range(maxiter):
                t += c 
                c = c * x / (i + 1)
                if c < 1 and t < y * (1 - c):
                    break 
            else:
                assert False, 'Proof failed within %d steps. Please use more iterations.'%(maxiter)

            txt = '$$e^{%s} < \\sum_{k=0}^{%d} \\frac{%s^k}{k!}  + \\frac{%s^{%d}}{%d!}e^{%s}'%(
                        lt(x),i,lt(x,1),lt(x,1),i+1,i+1,lt(x)) + \
                '=%s + %se^{%s}\ \\Rightarrow\ e^{%s} < %s < %s$$'%(
                        lt(t),lt(c),lt(x),lt(x),lt(t / (1 - c)),ytext)
            if len(txt) > 450:
                txt = '$$e^{%s} < \\sum_{k=0}^{%d} \\frac{%s^k}{k!}  + \\frac{%s^{%d}}{%d!}e^{%s}'%(
                        lt(x),i,lt(x,1),lt(x,1),i+1,i+1,lt(x)) + \
                '=%s + \\frac{%s^{%d}}{%d!}e^{%s}\\\\ \\Rightarrow\ e^{%s} < %s < %s$$'%(
                        lt(t),lt(x,1),i+1,i+1,lt(x),lt(x),lt(t / (1 - c)),ytext)

    if original_f[0] == 'e' and original_x < 0:
        txt = txt.rstrip('$')
        txt += '\ \\Rightarrow\ e^{%s} %s %s$$'%(lt(original_x), '<' if great == 1 else '>', lt(original_y))
    elif original_f[0] == 'l':
        txt = txt.rstrip('$')
        sgn = '>' if (original_y > 0) ^ (great == 1) else '<'
        txt += '\ \\Rightarrow\ \ln%s %s %s$$'%(lt(original_x), sgn, lt(original_y))

    return Proof(txt)


def prove_pade(f = 'exp', m = 3, n = None):
    """
    0
    """
    if n is None: n = m

    f = f.lower()
    if f.startswith('e'):
        result = _prove_pade_exp(m, n)
    elif f in ('ln', 'log'):
        result = _prove_pade_log(m, n)
    elif f in ('sin', 'cos', 'tan'):
        result = _prove_pade_trig(m, n, f = f)

    result = '$$\\begin{aligned}%s\\end{aligned}$$'%(result)

    return Proof(result)



def _prove_pade_exp(m, n):
    pade = _pade('exp', m, n)
    result = 'f(x) &= \\ln\\left(%s\\right) - x\\\\\n'%(sp.latex(pade))
    derv = sp.cancel(pade.diff() / pade - 1)
    result += 'f\'(x) &= %s \\%ceqslant 0'%(
        sp.latex(derv), 'g' if m <= n+1 else 'l')
    return result

def _prove_pade_log(m, n):
    t = sp.symbols('x')
    pade = _pade('ln', m, n)
    result = 'f(x) &= %s - \\ln(x+1)\\\\\n'%(sp.latex(pade))
    derv = sp.cancel(-(t+1)**(-1) + pade.diff(t))
    result += 'f\'(x) &= %s \\%ceqslant 0'%(
        sp.latex(derv), 'g' if m > n else 'l')
    return result

def _prove_pade_trig(m, n, f):
    t = sp.symbols('x')
    if f.startswith('sin'):
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
                    
    elif f.startswith('cos'):
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
    
    elif f == 'tan':
        pade = _pade(f, m, n)
        assert pade is not sp.nan, 'Unexisted Pade orders for tan(x). Try m = n = odd numbers.'

        result  = 'f(x) &= x - \\arctan %s\\\\\n'%(sp.latex(pade))
        derv = sp.cancel(1 - pade.diff(t) / (1 + pade * pade))
        result += 'f\'(x) &= %s \\geqslant 0'%(sp.latex(derv))

    return result