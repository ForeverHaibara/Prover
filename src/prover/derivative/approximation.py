from typing import Callable, Union

import sympy as sp

from ...basic.expansions import pade as _pade
from ..proof import Proof

def lt(x, b = 0):
    """
    Add parentheses to the latex string of x if necessary.
    """
    t = sp.latex(x) 
    if b == 1:
        if x < 0 or '.' in t or 'f' in t:
            t = '\\left(' + t + '\\right)'
    elif b == 2:
        if x < 0 or '.' in t:
            t = '\\left(' + t + '\\right)'
    return t

def racomp(x, y):
    """
    When x > y, return the string "x > y". When x < y return the string "x < y".
    When x = y, return the string "x".
    """
    if x == y:
        return lt(x)
    sgn = '>' if x > y else '<'
    return '%s %s %s'%(lt(x), sgn, lt(y))

def greatsgn(x, y):
    return '>' if x > y else ('=' if x == y else '<')


class _prove_approx:
    """
    Prove f(x) >= y or f(x) <= y where x and y are both rational numbers.

    If err is not None, prove that |f(x) - y| <= err.

    Parameters
    -------
    f: callable or str
    """
    def __new__(cls, *args, **kwargs):
        return cls._solve(*args, **kwargs)

    @classmethod
    def _lipschitz(cls, f, x, y, z, L, fz, r = None, fname = None, flip = 1):
        """
        Prove f(x) >= y by showing that
        f(x) >= f(z) - L|x - z| >= fz - r >= y

        f(x) <= y is also supported.
        If flip == -1, then it proves -f(x) ~ -y
        """
        assert flip == 1 or flip == -1, 'Parameter flip should be 1 or -1.'
        if r is None:
            r = L * abs(x - z)
        if fname is None:
            fname = '\\' + f.__name__

        great = greatsgn(f(x), y)
        if flip == -1:
            great = chr(122 - ord(great))
        flipsgn = '' if flip == 1 else '-'
        sgn = '-' if great=='>' else '+'

        txt = '%s%s\\left(%s\\right) %s %s%s\\left(%s\\right) %s'\
                '%s\\left|%s - %s\\right|'\
                '%s %s %s %s = %s'%(
                flipsgn, fname, lt(x), great, flipsgn, fname, lt(z), sgn, 
                lt(L) if L != 1 else '', lt(x), lt(z), 
                great, lt(flip * fz), sgn, lt(r), 
                racomp(flip * fz + (- r if sgn == '-' else r), flip * y)
            )
        return txt

    @classmethod
    def _trivial(cls, f, x, y, fx = None, err = None):
        """
        Prove very trivial inequality, i.e. e^2 > -5.
        """
        if fx is None:
            fx = f(x)

        if isinstance(fx, sp.Rational):
            # f(x) is directly computable, i.e. exp(0) = 1
            name = {
                sp.exp: 'e^{%s}'%lt(x,1), 
                sp.sin: '\\sin %s'%lt(x,2),
                sp.cos: '\\cos %s'%lt(x,2),
            }.get(f, f.__name__)
            if name is None:
                return '%s = %s'%(f(sp.UnevaluatedExpr(x)), racomp(fx, y))
            return '%s = %s'%(name, racomp(fx, y))

        if f == sp.exp:
            if y <= 0:
                return 'e^{%s} > %s'%(lt(x), racomp(0, y))

        elif f == sp.sin or f == sp.cos:
            if y <= -1 or y >= 1:    
                great = greatsgn(fx, y)
                return '\\%s %s %s %s'%('sin' if f == sp.sin else 'cos', lt(x,2), great, lt(y))

    @classmethod
    def _get_method_func(cls, method):
        return {
            'taylor': _prove_approx_taylor,
            'integral': _prove_approx_integral,
        }[method]

    @classmethod
    def _solve(
        cls,
        f: Union[Callable, str],
        x: Union[int, float, sp.Rational],
        y: Union[int, float, sp.Rational],
        err: Union[int, float, sp.Rational] = None,
        method: str = 'taylor',
        maxiter = 10000,
    ):
        if isinstance(f, str):
            functions = {'e': sp.exp, 'exp': sp.exp, 'ln': sp.ln, 'log': sp.ln, 'sin': sp.sin, 'cos': sp.cos}
            f = functions.get(f, None)
            assert f is not None, 'Function f should be one of %s, but received %s.'%(list(functions.keys()), f)

            
        x, y = sp.Rational(x), sp.Rational(y)

        _txt_wrapper = lambda txt: Proof('$$\\begin{aligned}& %s\\end{aligned}$$'%(txt))

        txt = cls._trivial(f, x, y, err = err)
        if txt is not None:
            return _txt_wrapper(txt)

        try:
            func = getattr(cls, f.__name__)
        except AttributeError:
            return None

        if func is not None:
            fx = f(x)
            great = greatsgn(fx, y)
            txt = func(f, x, y, err, great, method = method)

        if txt is None:
            return None
        return _txt_wrapper(txt)


    @classmethod
    def exp(cls, f, x, y, err, great, method = 'taylor'):
        method_func = cls._get_method_func(method)
        if method == 'taylor':
            if x >= 0 or y <= 0:
                txt = method_func(f, x, y, err)
            else:
                txt = method_func(f, -x, 1 / y, err)
                txt += '\\\\ & \\Rightarrow\ e^{%s} %s %s'%(lt(x), great, lt(y))
        elif method == 'integral':
            txt = method_func(f, x, y, err)
        return txt

    @classmethod
    def log(cls, f, x, y, err, great, method = 'taylor'):
        method_func = cls._get_method_func(method)
        if x <= 0:
            return None
        # ln(x) ~ y <=> x ~ e^y
        if y >= 0:
            txt = method_func(sp.exp, y, x, err)
        else:
            txt = method_func(sp.exp, -y, 1 / x, err)
        txt += '\\\\ & \\Rightarrow\ \\ln%s %s %s'%(lt(x), great, lt(y))
        return txt

    @classmethod
    def sin(cls, f, x, y, err, great, method = 'taylor'):
        return cls._sin_or_cos_handler(f, x, y, err, great, method = method)

    @classmethod
    def cos(cls, f, x, y, err, great, method = 'taylor'):
        return cls._sin_or_cos_handler(f, x, y, err, great, method = method)

    @classmethod
    def _sin_or_cos_handler(cls, f, x, y, err, great, method = 'taylor'):
        method_func = cls._get_method_func(method)
        if (0 <= x <= 2 * sp.pi) or (y <= -1 or y >= 1):
            txt = method_func(f, x, y, err)
        elif -2 * sp.pi <= x < 0:
            txt = method_func(f, -x, y if f == sp.cos else -y, err)
            if f == sp.sin:
                txt += '\\\\ & \\Rightarrow\ \\sin{%s} %s %s'%(lt(x,2), great, lt(y))
            elif f == sp.cos:
                txt = '\\cos{%s} = %s'%(lt(x,2), txt)
        else:
            # When |x| > 2pi, convergence is slow. We need to use sin(x-kpi) = (-1)^k sin(x).
            # If we have pi ~ t, then |sin(x-kt) - sin(x-kpi)| <= |k||pi - t| by Lagrange's theorem.
            # So we can use sin(x-kt) to approximate sin(x-kpi).
            k = sp.floor(x / sp.pi)
            n = 1
            t, c1, c2 = sp.S(0), sp.Rational(1,5), sp.Rational(1,239)
            flip = (-1)**k
            if great == '>':
                criterion = lambda t, err: flip * f(x - k*t) >= y + abs(k) * err
            else:
                criterion = lambda t, err: flip * f(x - k*t) <= y - abs(k) * err

            while True:
                # approximate pi = 16atan(1/5) - 4atan(1/239) (Machin formula)
                t += (16*c1 - 4*c2) / n
                err2 = abs(c1) * 5 / 6 / (n + 2)
                c1 = -c1 / 25
                c2 = -c2 / 57121
                # t is too complicated, we need another simplification
                t2 = sp.nsimplify(t + err2 * 1e-10, tolerance = err2, rational = True)
                diff = abs(t - t2)
                if diff < err2 and criterion(t2, 2 * err2):
                    break
                n += 2

            r = n // 2 + 1
            txt = '\\left|\\pi - %s\\right| = \\left|%s + \\sum_{k=%d}^{\\infty}'\
                '\\frac{16\\cdot 5^{-2k-1}-4\\cdot 239^{-2k-1}}{2k+1}\\right|'\
                '\\leqslant %s + \\frac{20}{%d}\\sum_{k=%d}^{\\infty}5^{-2k-1} = %s'%(
                lt(t2), lt(t2 - t), r, lt(err2), 2*r + 1, r, lt(2*err2)
            )
            err3 = abs(k * 2 * err2)
            target = flip * (y + err3) if great == '>' else flip * (y - err3)
            middle = _prove_approx_taylor(f, x - k*t2, target, err)

            lipschitz = cls._lipschitz(f, x-k*sp.pi, flip * y, x-k*t2, 1, target, err3, flip = flip)
            txt += '\\\\ & %s\\\\ & \\Rightarrow \\%s %s = %s'%(
                middle, f.__name__, lt(x,2), lipschitz
            )
        return txt

    @classmethod
    def atan(cls, f, x, y, err, great, method = 'taylor'):
        method_func = cls._get_method_func(method)
        if abs(x) <= sp.pi / 2:
            # guarantee convergence
            txt = method_func(f, x, y, err)
            return txt
        else:
            # atan(x) = pi/2 - atan(1/x)
            0


class _prove_approx_taylor:
    """
    Supports a small range of case proving f(x) >= y or f(x) <= y
    where x and y are both rational numbers using Taylor expansion
    Lagrange's mean value theorem might be implicitly
    used for estimating truncation error.

    When f == sp.exp, only supports x >= 0.

    When f == sp.sin, only supports 0 <= x <= 2pi.

    No checking is performed for the validity of the input, as this is
    not expected to be used by end users. Please refer to the main
    handler prove_approx() for more details.
    """
    def __new__(cls, *args, **kwargs):
        return cls._solve(*args, **kwargs)

    @classmethod
    def _solve(cls, f, x, y, err = None):
        fx = f(x)
        great = greatsgn(fx, y)

        try:
            func = getattr(cls, f.__name__)
        except AttributeError:
            return None

        if func is not None:
            return func(f, x, y, err, fx, great)

    @classmethod
    def exp(cls, f, x, y, err, fx, great):
        t, c, n = sp.S(0), sp.S(1), 0
        if great == '>':
            criterion = lambda c, t, y: t >= y
        else:
            # e^x < t + c*e^x => e^x < t / (1 - c) < y
            criterion = lambda c, t, y: c < 1 and t <= y * (1 - c)
        
        while True:
            t += c 
            c = c * x / (n + 1)
            if criterion(c, t, y):
                break
            n += 1

        if great == '>':
            txt = 'e^{%s} > \\sum_{k=0}^{%d} \\frac{%s^k}{k!} = %s'%(
                        lt(x), n, lt(x,1), racomp(t,y))
        else:
            txt = 'e^{%s} < \\sum_{k=0}^{%d} \\frac{%s^k}{k!}  + \\frac{%s^{%d}}{%d!}e^{%s}'%(
                    lt(x), n, lt(x,1), lt(x,1), n+1, n+1, lt(x)) + \
            '=%s + \\frac{%s^{%d}}{%d!}e^{%s}\\\\ & \\Rightarrow\ e^{%s} < %s'%(
                    lt(t), lt(x,1), n+1, n+1, lt(x), lt(x), racomp(t / (1 - c), y))
        return txt

    @classmethod
    def sin(cls, f, x, y, err, fx, great):
        if great == '>':
            criterion = lambda n, t, y: t >= y and (n // 2) % 2 == 1
        else:
            criterion = lambda n, t, y: t <= y and (n // 2) % 2 == 0
        t, c, n = sp.S(0), x, 1
        t, c, n = cls._sin_or_cos_iterator(x, y, t, c, n, criterion)

        txt = '\\sin{%s} %s \\sum_{k=0}^{%d} \\frac{(-1)^k%s^{2k+1}}{(2k+1)!} = %s'%(
            lt(x), great, n//2, lt(x,1), racomp(t, y))
        return txt

    @classmethod
    def cos(cls, f, x, y, err, fx, great):
        if great == '>':
            criterion = lambda n, t, y: t >= y and (n // 2) % 2 == 1
        else:
            criterion = lambda n, t, y: t <= y and (n // 2) % 2 == 0
        t, c, n = sp.S(0), sp.S(1), 0
        t, c, n = cls._sin_or_cos_iterator(x, y, t, c, n, criterion)

        txt = '\\cos{%s} %s \\sum_{k=0}^{%d} \\frac{(-1)^k%s^{2k}}{(2k)!} = %s'%(
            lt(x), great, n//2, lt(x,1), racomp(t, y))
        return txt

    @classmethod
    def _sin_or_cos_iterator(cls, x, y, t, c, n, criterion):
        while True:
            if (n // 2) % 2 == 0:
                t += c
            else:
                t -= c
            c = c * (x**2 / (n+1) / (n+2))
            if criterion(n, t, y):
                break
            n += 2
        return t, c, n


class _prove_approx_integral:
    """
    Consider F(n,m) = Integral(x^n*(1-x)^m*g(t,x), (x,0,1)) = a + b*f(t)
    where a, b are rational numbers and f is the given function.
    Then f(t) can be expressed as linear combination of many F(n,m).
    We compute that -a/b - f(t) = - I/b. Hence it converges when I/b -> 0.

    For example, when f(t) == exp(t), we use g(t,x) = exp(x*t).

    Be careful: sometimes the method does not converge. Please ensure 
    the input is valid. Please refer to each function for more details.

    References
    ----------
    [1] https://zhuanlan.zhihu.com/p/669285539

    [2] https://mathoverflow.net/questions/67384/
    """
    _is_equal_sgn = lambda u, v: (u >= 0 and v >= 0) or (u <= 0 and v <= 0)

    def __new__(cls, *args, **kwargs):
        return cls._solve(*args, **kwargs)

    @classmethod
    def _lin_comb(cls, f, x, y, values, id1, id2, criterion = _is_equal_sgn):
        a1, b1 = values[id1]
        a2, b2 = values[id2]
        # a1u + a2v = -y
        # b1u + b2v = 1
        d = a1*b2 - a2*b1
        if d != 0:
            u = (-y*b2 - a2)/d
            v = (a1 + b1*y)/d
            if criterion(u, v):
                return u, v
        return None

    @classmethod
    def _solve(cls, f, x, y, err = None):
        fx = f(x)
        great = greatsgn(fx, y)

        try:
            func = getattr(cls, f.__name__)
        except AttributeError:
            return None

        if func is not None:
            return func(f, x, y, err, fx, great)

    @classmethod
    def exp(cls, f, x, y, err, fx, great):
        # g(k,x) = exp(kx)
        # Consider F(n,m) = Integral(x^n*(1-x)^m*exp(kx), (x,0,1))
        # F(n,m) = m/k F(n,m-1) - n/k F(n-1,m) + (x^n*(1-x)^m*exp(kx)/k)|_0^1
        # deine F(n,m) = a + b*exp(k) where values[(n,m)] = (a,b)
        values = {(0,0): (-1/x, 1/x)}
        n = 1
        def recur(n, m):
            a1, b1 = values.get((n,m-1), (0,0))
            a2, b2 = values.get((n-1,m), (0,0))
            a, b = m/x * a1 - n/x * a2, m/x * b1 - n/x * b2
            if n == 0: a -= 1/x
            if m == 0: b += 1/x
            return a, b

        while True:
            for m in range(n + 1):
                values[(n,m)] = recur(n, m)
                values[(m,n)] = recur(m, n)

            for comb_type, index in ((0, (n-1,n)), (1, (n,n-1))):
                uv = cls._lin_comb(f, x, y, values, index, (n,n))
                if uv is not None:
                    break
            if uv is not None:
                break
            n += 1

        u, v = uv
        if u <= 0 and v <= 0:
            u, v = -u, -v
        z = sp.symbols('x')
        if comb_type == 0:
            integrand = z**(n-1)*(1-z)**n * (u + v*z).together() * sp.exp(x*z)
        else:
            integrand = z**n*(1-z)**(n-1) * (u + v*(1-z)).together() * sp.exp(x*z)
        txt = '%s = \\int_0^1 %s \\text{d}x > 0'%(
            lt(fx - y) if great == '>' else lt(y - fx), lt(integrand))
        return txt
            

    @classmethod
    def atan(cls, f, x, y, err, fx, great):
        # Consider F(n,m) = Integral(x^(2n)*(1-x^2)^m/(1+(kx)^2), (x,0,1))
        # F(n,m) = 1/k^2 * [-F(n-1, m) + Integral(x^(2n-2)*(1-x^2)^m, (x,0,1))]
        # where Integral(x^(2n-2)*(1-x^2)^m, (x,0,1)) = B(n - 1/2, m + 1) / 2
        values = {(0,0): (sp.S(0), 1/x)} # F(0,0) = 0 + atan(x) / x
        n = 1
        def _half_beta(n, m):
            """Return B(n - 1/2, m + 1)"""
            return sp.gamma(n - sp.S.Half) * sp.factorial(m) / sp.gamma(n + m + sp.S.Half)
        _criteria = [
            lambda u, v: cls._is_equal_sgn(u + v, v),
            lambda u, v: cls._is_equal_sgn(u, u + v),
        ]

        while True:
            # we only focus on F(n,n) and F(n+1,n)
            for r in range(2*n - 1, 2*n + 1):
                a1, b1 = values[(r-1,0)]
                a2, b2 = (-a1 + 1 / sp.S(2*r - 1)) / x**2, -b1 / x**2
                values[(r,0)] = (a2, b2)

            a, b = sp.S(0), sp.S(0)
            for k in range(n + 1):
                # expand (1-x^2)^m where m == n
                a1, b1 = values[(n+k, 0)]
                coeff = sp.binomial(n, k) * (-1)**(k)
                a, b = a + coeff * a1, b + coeff * b1
            values[(n,n)] = (a, b)

            a2, b2 = (-a + _half_beta(n+1,n)/2) / x**2, -b / x**2
            values[(n+1,n)] = (a2, b2)

            a2, b2 = _half_beta(n,n)/2 - x**2*a, -x**2*b
            values[(n-1,n)] = (a2, b2)

            for comb_type, index in ((0, (n+1,n)), (1, (n-1,n))):
                uv = cls._lin_comb(f, x, y, values, index, (n,n), criterion=_criteria[comb_type])
                if uv is not None:
                    break
            if uv is not None:
                break

            n += 1

        u, v = uv
        if u <= 0 and v <= 0:
            u, v = -u, -v
        z = sp.symbols('x')
        if comb_type == 0:
            integrand = z**(2*n)*(1-z**2)**n * (u*z**2 + v).together() / (1 + (x*z)**2)
        else:
            integrand = z**(2*(n-1))*(1-z**2)**n * (u + v*z**2).together() / (1 + (x*z)**2)
        txt = '%s = \\int_0^1 %s \\text{d}x > 0'%(
            lt(fx - y) if great == '>' else lt(y - fx), lt(integrand))
        return txt




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


prove_approx = _prove_approx._solve