from typing import Callable, Union

import sympy as sp

from ...basic.utils import rational_between, radsimp
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


class Constants:
    """
    Wrap a sympy constant to a function.
    """
    def __new__(cls, *args, **kwargs):
        return cls.get(*args, **kwargs)

    @classmethod
    def get(cls, x):
        """See details at sympy.core.singleton."""
        if x is sp.E:
            return cls.exp
        elif x is sp.pi:
            return cls.exp_pi
        elif x is sp.EulerGamma:
            return cls.exp_EulerGamma
        elif x is sp.Catalan:
            return cls.exp_Catalan

    @classmethod
    def exp(cls, x):
        return sp.exp(x)

    @classmethod
    def exp_pi(cls, x):
        return sp.pi ** x

    @classmethod
    def exp_EulerGamma(cls, x):
        return sp.EulerGamma ** x

    @classmethod
    def exp_Catalan(cls, x):
        return sp.Catalan ** x


class _prove_approx:
    """
    Prove f(x) >= y or f(x) <= y where x and y are both rational numbers.

    Parameters
    -------
    f: callable or str
        Sympy function.
    x: Rational
        The input of f.
    y: Rational
        The target value.
    method: str
        One of 'series' or 'integral'.
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
    def _trivial(cls, f, x, y, fx = None):
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
            }.get(f, None)
            if name is None:
                return '%s = %s'%(lt(f(sp.UnevaluatedExpr(x))), racomp(fx, y))
            return '%s = %s'%(name, racomp(fx, y))

        if f == sp.exp or f.__name__ == 'exp_pi':
            if y <= 0:
                return '%s > %s'%(lt(f(x)), racomp(0, y))

        elif f == sp.sin or f == sp.cos:
            if y <= -1 or y >= 1:    
                great = greatsgn(fx, y)
                return '\\%s %s %s %s'%('sin' if f == sp.sin else 'cos', lt(x,2), great, lt(y))

        if f in (sp.asin, sp.atan):
            if x > 0 and y <= 0:
                return '\\operatorname{%s} %s > %s'%(f.__name__, lt(x), racomp(0, y))
            elif x < 0 and y >= 0:
                return '\\operatorname{%s}\\left(%s\\right) < %s'%(f.__name__, lt(x), racomp(0, y))

    @classmethod
    def _get_method_func(cls, method):
        return {
            'series': _prove_approx_series,
            'integral': _prove_approx_integral,
        }[method]

    @classmethod
    def _solve(
        cls,
        f: Union[Callable, str],
        x: Union[int, float, sp.Rational],
        y: Union[int, float, sp.Rational],
        method: str = 'series',
    ):
        if isinstance(f, str):
            try:
                f = getattr(sp, f)
            except AttributeError:
                raise  AttributeError("Function '%s' is not supported."%f)

        x, y = sp.Rational(x), sp.Rational(y)

        _txt_wrapper = lambda txt: Proof('$$\\begin{aligned}& %s\\end{aligned}$$'%(txt))

        txt = cls._trivial(f, x, y)
        if txt is not None:
            return _txt_wrapper(txt)

        try:
            func = getattr(cls, f.__name__)
        except AttributeError:
            return None

        if func is not None:
            fx = f(x)
            great = greatsgn(fx, y)
            txt = func(f, x, y, great, method = method)

        if txt is None:
            return None
        return _txt_wrapper(txt)


    @classmethod
    def exp(cls, f, x, y, great, method = 'series'):
        method_func = cls._get_method_func(method)
        if method == 'series':
            if x >= 0 or y <= 0:
                txt = method_func(f, x, y)
            else:
                txt = method_func(f, -x, 1 / y)
                txt += '\\\\ & \\Rightarrow\ e^{%s} %s %s'%(lt(x), great, lt(y))
        elif method == 'integral':
            txt = method_func(f, x, y)
        return txt

    @classmethod
    def log(cls, f, x, y, great, method = 'series'):
        method_func = cls._get_method_func(method)
        if x <= 0:
            return None
        # ln(x) ~ y <=> x ~ e^y
        if y >= 0:
            txt = method_func(sp.exp, y, x)
        else:
            txt = method_func(sp.exp, -y, 1 / x)
        txt += '\\\\ & \\Rightarrow\ \\ln%s %s %s'%(lt(x), great, lt(y))
        return txt

    @classmethod
    def exp_pi(cls, f, x, y, great, method = 'series'):
        method_func = cls._get_method_func(method)
        return method_func(f, x, y)

    @classmethod
    def exp_EulerGamma(cls, f, x, y, great, method = 'series'):
        method_func = cls._get_method_func(method)
        return method_func(f, x, y)

    @classmethod
    def exp_Catalan(cls, f, x, y, great, method = 'series'):
        method_func = cls._get_method_func(method)
        return method_func(f, x, y)

    @classmethod
    def sin(cls, f, x, y, great, method = 'series'):
        return cls._sin_or_cos_handler(f, x, y, great, method = method)

    @classmethod
    def cos(cls, f, x, y, great, method = 'series'):
        return cls._sin_or_cos_handler(f, x, y, great, method = method)

    @classmethod
    def _sin_or_cos_handler(cls, f, x, y, great, method = 'series'):
        method_func = cls._get_method_func(method)
        if (0 <= x <= 2 * sp.pi) or (y <= -1 or y >= 1):
            txt = method_func(f, x, y)
        elif -2 * sp.pi <= x < 0:
            txt = method_func(f, -x, y if f == sp.cos else -y)
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
            middle = _prove_approx_series(f, x - k*t2, target)

            lipschitz = cls._lipschitz(f, x-k*sp.pi, flip * y, x-k*t2, 1, target, err3, flip = flip)
            txt += '\\\\ & %s\\\\ & \\Rightarrow \\%s %s = %s'%(
                middle, f.__name__, lt(x,2), lipschitz
            )
        return txt

    @classmethod
    def tan(cls, f, x, y, great, method = 'series'):
        method_func = cls._get_method_func(method)
        if abs(x) <= 1 or (abs(x) <= sp.pi / 2 and sp.sign(x) != sp.sign(y)):
            return method_func(f, x, y)
        elif abs(x) <= sp.pi / 2:
            # also sgn(x) == sgn(y) != 0
            # use tan(x) = 2/(cot(x/2) - tan(x/2))
            # solve 2z / (1-z^2) = y  =>  z = (sqrt(y^2+1) - 1) / y
            z = (sp.sqrt(y**2 + 1) - 1) / abs(y)
            # compare tan(x/2) and z
            x1 = abs(x) / 2
            mid = rational_between(f(x1), z)
            txt = method_func(f, x1, mid)
            txt += '\\\\ & \\Rightarrow\ \\tan\\left(%s\\right) = %s\\frac{2}'\
                '{\\cot %s - \\tan %s} %s %s\\frac{2}{%s - %s} = %s'%(
                    lt(x), '-' if x < 0 else '',
                    lt(x1,1), lt(x1,1), great, '-' if x < 0 else '', 
                    lt(1/mid), lt(mid), racomp(2*mid/(1-mid**2)*sp.sign(x), y)
            )
            return txt
        else:
            # tan(x) = tan(x - kpi)
            k = round(x / sp.pi)
            z = x - k * sp.pi
            mid = rational_between(z, sp.atan(y))
            # compare x-k*pi ~ mid ~ atan(y)
            if sp.sign(z) != sp.sign(y):
                prove_pi1 = method_func(Constants.exp_pi, sp.S(1), x / k)
                prove_pi2 = method_func(Constants.exp_pi, sp.S(1), x / (sp.sign(z) / 2 + k))
                if z < 0:
                    txt = '-\\frac{\\pi}{2} < %s < 0'%lt(z)
                else:
                    txt = '0 < %s < \\frac{\\pi}{2}'%lt(z)
                txt = '%s\\\\ & %s\\\\ & \\Rightarrow\ %s\ \\Rightarrow\ '\
                        '\\tan\\left(%s\\right) = \\tan\\left(%s\\right) %s %s'%(
                            prove_pi1, prove_pi2, txt, 
                            lt(x), lt(z), great, lt(y)
                )
                return txt
            
            else:
                # if sgn(z) == sgn(y)
                prove_pi1 = method_func(Constants.exp_pi, sp.S(1), (x - mid) / k)
                if mid > z:
                    prove_pi2 = method_func(Constants.exp_pi, sp.S(1), x / (k - sp.S(1)/2))
                    txt = '-\\frac{\\pi}{2} < %s < %s'%(lt(z), lt(mid))
                else:
                    prove_pi2 = method_func(Constants.exp_pi, sp.S(1), x / (k + sp.S(1)/2))
                    txt = '%s < %s < \\frac{\\pi}{2}'%(lt(mid), lt(z))
                final = method_func(sp.tan, abs(mid), abs(y))
                if final is None:
                    return None
                txt = '%s\\\\ & %s\\\\ & %s\\\\ & \\Rightarrow\ %s\ \\Rightarrow\ '\
                        '\\tan\\left(%s\\right) = \\tan\\left(%s\\right) %s'\
                        '\\tan\\left(%s\\right) %s %s'%(
                            prove_pi1, prove_pi2, final, txt,
                            lt(x), lt(z), great,
                            lt(mid), great, lt(y)
                )
                return txt


    @classmethod
    def asin(cls, f, x, y, great, method = 'series'):
        method_func = cls._get_method_func(method)
        if (method == 'series' and abs(x) < 1) or (method == 'integral' and abs(x**2) <= sp.S(1)/2):
            txt = method_func(f, x, y)
            return txt
        elif abs(y) >= sp.pi / 2 or abs(x) == 1:
            prove_pi = method_func(Constants.exp_pi, sp.S(1), abs(y) * 2)
            if abs(x) == 1:
                txt = '%s\\\\ & \\Rightarrow\ \\operatorname{asin}\\left(%s\\right) = %s\\frac{\\pi}{2} %s %s'%(
                    prove_pi, lt(x), '-' if x < 0 else '', great, lt(y)
                )
            else:
                txt = '%s\\\\ & \\Rightarrow\ \\operatorname{asin}\\left(%s\\right) %s %s\\frac{\\pi}{2} %s %s'%(
                    prove_pi, lt(x), great, '-' if great == '>' else '', great, lt(y)
                )
            return txt
        else:
            # asin(x) = pi/2 - asin(sqrt(1-x^2)) (x > 0)
            # we need to compare sqrt(1-x^2) and sin(pi/2 - y) = cos(y)
            x_ = sp.sqrt(1-x**2)
            if isinstance(x_, sp.Rational):
                mid = x_
            else:
                mid = rational_between(x_, sp.cos(y))
            mid2 = rational_between(sp.asin(mid), sp.pi / 2 - abs(y))
            # asin(mid) ~ mid2
            txt = method_func(f, mid, mid2)
            v = abs(y) + mid2
            txt2 = method_func(Constants.exp_pi, sp.S(1), 2*v)
            txt = '%s\\\\ & %s\\\\ & \\Rightarrow\ \\operatorname{asin}\\left(%s\\right)'\
                ' = %s\\frac{\\pi}{2} %s\\operatorname{asin}\\left(%s\\right)'\
                '%s'\
                ' %s %s %s %s = %s'%(
                    txt, txt2, lt(x),
                    '-' if x < 0 else '', '+' if x < 0 else '-', lt(x_),
                    ' %s %s\\frac{\\pi}{2} %s\\operatorname{asin}\\left(%s\\right)'%(
                        great, '-' if x < 0 else '', '+' if x < 0 else '-', lt(mid)
                    ) if not isinstance(x_, sp.Rational) else '',
                    great, lt(-v if x < 0 else v), '-' if x > 0 else '+', lt(mid2), lt(y)
            )
            return txt

    @classmethod
    def atan(cls, f, x, y, great, method = 'series'):
        method_func = cls._get_method_func(method)
        if abs(x) <= 1:
            # guarantee convergence
            txt = method_func(f, x, y)
            return txt
        elif abs(y) >= sp.pi / 2:
            prove_pi = method_func(Constants.exp_pi, sp.S(1), abs(y) * 2)
            txt = '%s\\\\ & \\Rightarrow\ \\operatorname{atan}\\left(%s\\right) %s %s\\frac{\\pi}{2} %s %s'%(
                prove_pi, lt(x), great, '-' if great == '>' else '', great, lt(y)
            )
            return txt
        else:
            # atan(x) = pi/2 - atan(1/x) (x > 0)
            # first we find a rational number between atan(1/x) and pi/2 - y
            # we assume sgn(x) == sgn(y)
            mid = rational_between(f(abs(1/x)), sp.pi / 2 - abs(y))
            txt = method_func(f, abs(1/x), mid)
            v = abs(y) + mid
            txt2 = method_func(Constants.exp_pi, sp.S(1), 2*v)
            txt = '%s\\\\ & %s\\\\ & \\Rightarrow\ \\operatorname{atan}\\left(%s\\right)'\
                ' = %s\\frac{\\pi}{2} %s\\operatorname{atan}\\left(%s\\right)'\
                '%s %s %s %s = %s'%(
                    txt, txt2, lt(x), 
                    '-' if x < 0 else '', '+' if x < 0 else '-', lt(abs(1/x)),
                    great, lt(-v if x < 0 else v), '-' if x > 0 else '+', lt(mid), lt(y)
            )
            return txt



class _prove_approx_series:
    """
    Supports a small range of case proving f(x) >= y or f(x) <= y
    where x and y are both rational numbers using Taylor expansion
    Lagrange's mean value theorem might be implicitly
    used for estimating truncation error.

    No checking is performed for the validity of the input, as this is
    not expected to be used by end users. Please refer to the main
    handler prove_approx() for more details.
    """
    def __new__(cls, *args, **kwargs):
        return cls._solve(*args, **kwargs)

    @classmethod
    def _solve(cls, f, x, y):
        fx = f(x)
        great = greatsgn(fx, y)

        try:
            func = getattr(cls, f.__name__)
        except AttributeError:
            return None

        if func is not None:
            return func(f, x, y, fx, great)

    @classmethod
    def exp(cls, f, x, y, fx, great):
        """Only supports x > 0."""
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
    def exp_pi(cls, f, x, y, fx, great):
        """
        Currently only supports positive integer x.

        For even numbers, we use the following idea:
        pi^(2k) = C * zeta(2n+2k) / zeta(2n) for arbitrary integer n
        where C = |B_{2n}|/|B_{2n+2k}| * (2n+2k)!/(2n)!/2^(2k)
        Thus, C > pi^(2k) > C / (1 + 3/2^{2n})
        """
        if (not x.is_integer) or x <= 0:
            return None
        if x % 2 == 0:
            n = 1
            def _compute_C(n):
                return abs(sp.bernoulli(2*n)) / abs(sp.bernoulli(2*n + x)) * \
                    sp.factorial(2*n + x) / sp.factorial(2*n) / 2**(x)
            if great == '>':
                criterion = lambda n, c, y: c / (1 + sp.S(3)*sp.S(2)**(-2*n)) >= y
            else:
                criterion = lambda n, c, y: c <= y
            while True:
                c = _compute_C(n)
                if criterion(n, c, y):
                    break
                n += 1

            C_ = '\\frac{%d!|B_{%d}|}{%d!|B_{%d}|}\\cdot 2^{%d}'%(2*n+x, 2*n, 2*n, 2*n+x, -x)
            if great == '>':
                txt = '\\pi^{%d} = %s\\cdot\\frac{\\zeta(%d)}{\\zeta(%d)} > %s \\cdot \\frac{1}{1 + \\frac{3}{2^{%d}}} = %s'%(
                    x, C_, 2*n+x, 2*n, C_, 2*n, racomp(c / (1 + sp.S(3)*sp.S(2)**(-2*n)), y)
                )
            else:
                txt = '\\pi^{%d} = %s\\frac{\\zeta(%d)}{\\zeta(%d)} < %s = %s'%(
                    x, C_, 2*n+x, 2*n, C_, racomp(c, y)
                )
            return txt

        elif x % 2 == 1:
            y_sq = y**2
            txt = cls.exp_pi(f, x*2, y_sq, fx, great)
            txt += '\\\\ & \\Rightarrow\ %s %s \\sqrt{%s} = %s'%(lt(Constants.exp_pi(x)), great, lt(y_sq), lt(y))
            return txt

    @classmethod
    def exp_EulerGamma(cls, f, x, y, fx, great):
        """
        Using Euler-Maclaurin formula, we have for even number n that
        gamma = Sum_{k=1}^n (1/k) - ln(n) + Sum_{k=1}^n B_k / (kn^k) + r_n
        where
        r_n = 2 * n!/(2*pi*I)^n * Integral(x^{-n-1}Sum(k^(-n)*cos(2*pi*k*x), (k,1,oo)), (x,n,oo))
        and |r_n| <= 2 * n!/(2*pi)^n * zeta(n) / n^(n+1) = |B_n| / n^(n+1) = R_n

        The approximated convergence speed is given by
        |R_n| ~ 2*sqrt(2*pi) / (2*pi*E)^n / sqrt(n).

        It suffices to find sufficiently large N such that |S_N - y| >= R_N.
        However, if we compute the approximant by n = 1,2,3,..... It will take O(N^2) time.
        We shall determine n by bisection, which is at most O(NlogN) time.

        First we yield an upper bound for R_N. When 2R_N < |gamma - y|. We must have
        |S_N - y| <= |S_N - gamma| + |gamma - y| < 2R_N, which is a stop.

        Also, R_N > 2 / (2*pi*E)^n / n.
        """
        if x != 1:
            return None
        def _compute_sr(n):
            s = 0
            nk = 1
            for k in range(1, n + 1):
                nk *= n
                s += sp.Rational(1,k) + (sp.bernoulli(k) if k > 1 else -sp.S.Half) / (k * nk)
                # Warning:
                # Sympy changes bernoulli(1) from -1/2 to 1/2 since version 1.12.
                # See details at https://github.com/sympy/sympy/pull/23926
                # So do not trust the result of bernoulli(1)!
            rem = abs(sp.bernoulli(n)) / n**(n+1)
            return s, rem

        def _satisfy_rough_bound(n):
            rem = abs(sp.bernoulli(n)) / n**(n+1)
            return bool(2 * rem <= abs(sp.EulerGamma - y))

        def _satisfy_bound(n):
            s, rem = _compute_sr(n)
            return bool(abs(s - sp.log(n) - y) >= rem)

        def f(n):
            # keep n even
            return n + 1 if n % 2 == 1 else n

        N0 = round(-sp.log(abs(sp.EulerGamma - y) / 4) / (sp.log(2*sp.pi) + 1))
        N0 = max(N0, sp.S(1))
        while N0 > 1 and _satisfy_rough_bound(N0):
            N0 = N0 // 2
        N0 = N0 * 2
        while not _satisfy_rough_bound(N0):
            N0 = N0 * 2
        # now that N0 must succeed, also N0/2 must fail
        l, r = f(N0 // 2), f(N0)
        while l + 2 < r:
            m = (l + r) // 2
            if _satisfy_bound(m):
                r = m
            else:
                l = m
        n = r
        s, rem = _compute_sr(n)
        comp = s - rem if great == '>' else s + rem
        int_part = '\\int_{%d}^{\\infty}x^{-%d}\\sum_{k=1}^{\\infty}\\frac{\\cos(2\pi kx)}{k^{%d}}\\text{d}x'%(
            n, n+1, n
        )
        prove_ln = _prove_approx_series(sp.exp, comp - y, n) + '\\\\ & ' if comp > y else '' # log(n) ~ comp - y
        txt = '%s\\gamma = \\sum_{k=1}^{%d} \\frac{1}{k} - \\ln{%d} + \\sum_{k=1}^{%d} \\frac{B_k}{k\\cdot %d^k} '\
                ' %s \\frac{2\\cdot %d!}{(2\\pi)^{%d}} %s'\
                ' %s \\sum_{k=1}^{%d} \\frac{1}{k} - \\ln{%d} + \\sum_{k=1}^{%d} \\frac{B_k}{k\\cdot %d^k}'\
                ' %s \\frac{2\\cdot %d! \\zeta(%d)}{(2\\pi)^{%d}\\cdot %d^{%d}} = %s - \\ln %s %s %s'%(
                prove_ln, n, n, n, n,
                '+' if n % 4 == 0 else '-', n, n, int_part,
                great, n, n, n, n,
                '-' if great == '>' else '+', n, n, n, n, n+1, lt(comp), n, great, lt(y)
        )
        return txt

    @classmethod
    def sin(cls, f, x, y, fx, great):
        """Only supports x > 0."""
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
    def cos(cls, f, x, y, fx, great):
        """Only supports x > 0."""
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

    @classmethod
    def tan(cls, f, x, y, fx, great):
        """
        Only supports -pi/2 < x < pi/2. 
        This is because pi/2 is the first singularity of tan(x).
        The Taylor expansion of tan(x) is given by
        tan(x) = Sum_{k=1}^{inf} (2^(2k)-1)*2^(2k)/(2k)! * |B_{2k}| * x^{2k-1}
               = Sum_{k=1}^{inf} (2^(2k)-1)/pi^(2k) * 2 * zeta(2k) * x^{2k-1}
        where B_{2k} are Bernoulli numbers and zeta is the Riemann zeta function.
        There is relation that |B_{2k}|/(2k)! = 2 * zeta(2k) / (2*pi)^(2k)

        Clearly the coefficient is monotonically decreasing from the definition of zeta.
        The remainder term is bounded by
        R_n = (2^(2n+1)-1)/pi^(2n) * zeta(2n) * x^(2n)
            Sum_{k>n} (2^(2k)-1)/(2^(2n+1)-1) / pi^(2(k-n)) * 2 * zeta(2k)/zeta(2n) * x^{2(k-n)-1}
            < (2^(2n+1)-1)/pi^(2n) * zeta(2n) * x^(2n) * tan(x)
        """
        if x < 0:
            x, y, sgn, great = -x, -y, -1, chr(122 - ord(great))
        else:
            sgn = 1
        # z = 2^(2n), w = x^(2n-1) / (2n)!
        t, c, n, z, w = sp.S(0), x, 1, 4, x / 2
        if great == '>':
            criterion = lambda n, t, y: t >= y
        else:
            def criterion(n, t, y):
                coeff = (2**(2*n+1)-1) * (sp.zeta(2*n)/sp.pi**(2*n)) * x**(2*n)
                return coeff < 1 and t / (1 - coeff) <= y

        while True:
            t += c
            if criterion(n, t, y):
                break
            z *= 4
            w *= x**2 / (2*n + 1) / (2*n + 2)
            c  = (z - 1) * z * w * abs(sp.bernoulli(2*n + 2))
            n += 1

        if great == '>':
            txt = '\\tan\\left(%s\\right) > \\sum_{k=1}^{%d} \\frac{(2^{2k+1}-2)\\zeta(2k)}{\\pi^{2k}}%s^k = %s'%(
                        lt(x), n, lt(x,1), racomp(t,y))
        else:
            coeff_ = (2**(2*n+1)-1) * (sp.zeta(2*n)/sp.pi**(2*n)) * x**(2*n)
            main = '\\sum_{k=1}^{%d} \\frac{2(2^{2k}-1)\\zeta(2k)}{\\pi^{2k}}%s^{2k-1}'%(n, lt(x,1))
            remain_coeff = '\\frac{(2^{%d}-1)\\zeta(%d)}{\\pi^{%d}}%s^{%d}'%(
                                2*n + 1, 2*n, 2*n, lt(x,1), 2*n
            )
            remainder = '\\sum_{k=%d}^{\\infty}\\frac{2(2^{2k}-1)}{(2^{%d}-1)\\pi^{2(k-%d)}}'\
                        '\cdot\\frac{\\zeta(2k)}{\\zeta(%d)}%s^{2(k-%d)-1}'%(
                            n + 1, 2*n + 1, n, 2*n, lt(x,1), n
            )
            txt = '\\tan\\left(%s\\right) = %s + %s%s'\
                '<%s + %s\\tan\\left(%s\\right)\\\ & \\Rightarrow\ \\tan\\left(%s\\right) < %s'%(
                    lt(x), main, remain_coeff , remainder, 
                    main, remain_coeff, lt(x), lt(x), racomp(t / (1 - coeff_), y)
            )
        if sgn == -1:
            txt += '\\\\ & \\Rightarrow\ \\tan\\left(%s\\right) = -\\tan\\left(%s\\right) %s %s'%(
                lt(-x), lt(x), chr(122 - ord(great)), lt(-y)
            )
        return txt

    @classmethod
    def asin(cls, f, x, y, fx, great):
        """Only supports -1 < x < 1."""
        if x < 0:
            x, y, sgn, great = -x, -y, -1, chr(122 - ord(great))
        else:
            sgn = 1
        t, c, n = sp.S(0), x, 0
        if great == '>':
            criterion = lambda c, t, y: t >= y
        else:
            # asin(x) < t + c * (1 + x^2 + x^4 + ...) = t + c / (1 - x^2)
            criterion = lambda c, t, y: t + c / (1 - x**2) <= y

        while True:
            t += c
            c *= sp.S((2*n + 1)**2) / (2*n + 2) / (2*n + 3) * x**2
            if criterion(c, t, y):
                break
            n += 1

        if great == '>':
            txt = '\\operatorname{asin}\\left(%s\\right) > \\sum_{k=0}^{%d} \\frac{(2k-1)!!}{(2k)!!(2k+1)}%s^{2k+1} = %s'%(
                        lt(x), n, lt(x,1), racomp(t,y))
        else:
            txt = '\\operatorname{asin}\\left(%s\\right) < \\sum_{k=0}^{%d} \\frac{(2k-1)!!}{(2k)!!(2k+1)}%s^{2k-1}'\
                '+ \\frac{%d!!}{%d!!\\cdot %d}\\cdot \\frac{%s^{%d}}{1 - %s^{2}} = %s'%(
                    lt(x), n, lt(x,1), 
                    2*n+1, 2*n+2, 2*n+3, lt(x,1), 2*n+1, lt(x,1), racomp(t + c / (1 - x**2), y)
            )
        if sgn == -1:
            txt += '\\\\ & \\Rightarrow\ \\operatorname{asin}\\left(%s\\right) = -\\operatorname{asin}\\left(%s\\right) %s %s'%(
                lt(-x), lt(x), chr(122 - ord(great)), lt(-y)
            )
        return txt

    @classmethod
    def atan(cls, f, x, y, fx, great):
        """
        We shall use the series given by Euler that:
        atan(x) = z / x * Sum_{k=0} (2k)!!/(2k+1)!! * z^k
        where z = x^2 / (1 + x^2) < 1.

        This ensures global convergence. However, it is still suggested
        x be small.
        """
        if x < 0:
            x, y, sgn, great = -x, -y, -1, chr(122 - ord(great))
        else:
            sgn = 1
        z = x**2 / (1 + x**2)
        t, c, n = sp.S(0), z / x, 0
        if great == '>':
            criterion = lambda c, t, y: t >= y
        else:
            # asin(x) < t + c * (1 + z + z^2 + ...) = t + c / (1 - z)
            criterion = lambda c, t, y: t + c / (1 - z) <= y

        while True:
            t += c
            c *= sp.S(2*n + 2) / (2*n + 3) * z
            if criterion(c, t, y):
                break
            n += 1

        if great == '>':
            txt = '\\operatorname{atan}\\left(%s\\right) > \\frac{1}{%s + %s}\\sum_{k=0}^{%d}'\
                    '\\frac{(2k)!!}{(2k+1)!!}\\left(\\frac{1}{1+%s^{-2}}\\right)^{k} = %s'%(
                        lt(x), lt(x), lt(1/x), n, lt(x,1), racomp(t,y))
        else:
            txt = '\\operatorname{atan}\\left(%s\\right) < \\frac{1}{%s + %s}\\left[\\sum_{k=0}^{%d}'\
                    '\\frac{(2k)!!}{(2k+1)!!}\\left(\\frac{1}{1+%s^{-2}}\\right)^{k}'\
                    '+ \\frac{%d!!}{%d!!}\\sum_{k=%d}^{\\infty}\\left(\\frac{1}{1+%s^{-2}}\\right)^{k}\\right] = %s'%(
                    lt(x), lt(x), lt(1/x), n,
                    lt(x,1),
                    2*n+2, 2*n+3, n+1, lt(x,1), racomp(t + c / (1 - z), y)
            )
        if sgn == -1:
            txt += '\\\\ & \\Rightarrow\ \\operatorname{atan}\\left(%s\\right) = -\\operatorname{atan}\\left(%s\\right) %s %s'%(
                lt(-x), lt(x), chr(122 - ord(great)), lt(-y)
            )
        return txt


class _prove_approx_integral:
    """
    Consider F(n,m) = Integral(t^n*(1-t)^m*g(x,t), (t,0,1)) = a + b*f(x)
    where a, b are rational numbers and f is the given function.
    Then f(x) can be expressed as linear combination of many F(n,m).
    We compute that -a/b - f(x) = - I/b. Hence it converges when I/b -> 0.

    For example, when f(x) == exp(x), we use g(x,t) = exp(x*t).

    Be careful: sometimes the method does not converge. Please ensure 
    the input is valid. Please refer to each function for more details.

    References
    ----------
    [1] https://zhuanlan.zhihu.com/p/669285539

    [2] https://zhuanlan.zhihu.com/p/670472865

    [3] https://mathoverflow.net/questions/67384/
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
    def _binomial(cls, values, n, m, d = 1, r = sp.S(-1), mul = 1):
        """
        Return mul * Sum_{k=0}^m C(m,k) * r^k * values[(n+kd,0)]
        """
        a, b, rk = sp.S(0), sp.S(0), sp.S(1)
        for k in range(m + 1):
            a1, b1 = values[(n + k*d, 0)]
            coeff = sp.binomial(m, k) * rk
            a, b, rk = a + coeff * a1, b + coeff * b1, rk * r
        return a * mul, b * mul

    @classmethod
    def _solve(cls, f, x, y):
        fx = f(x)
        great = greatsgn(fx, y)

        try:
            func = getattr(cls, f.__name__)
        except AttributeError:
            return None

        if func is not None:
            return func(f, x, y, fx, great)

    @classmethod
    def exp(cls, f, x, y, fx, great):
        """
        Consider F(n,m) = Integral(t^n*(1-t)^m*exp(xt), (t,0,1))
        F(n,m) = m/x F(n,m-1) - n/x F(n-1,m) + (t^n*(1-t)^m*exp(xt)/x)|_0^1
        deine F(n,m) = a + b*exp(x) where values[(n,m)] = (a,b)

        It converges for all x with factorial convergence rate.
        Actually it can be shown that for x > 0,
        (-1)^(n+1) * b_{n,m} = Sum_{j=0}^m C(m,j) * (n+j)! / x^{n+j} * Sum_{k=0}^{n+j}(-x)^{k-1}/k!
                             ~ Sum_{j=0}^m C(m,j) * (n+j)! / x^{n+j+1} * exp(-x)
                             > (n+m)!/x^(n+m+1) * exp(-x)
        Therefore, |-a/b - I| = I/b = o((x/2)^(2n) / (2n)!) when m == n.
        """
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
    def exp_pi(cls, f, x, y, fx, great):
        """
        This is a special function defined here. f(x) = pi^x.
        It only supports x == positive integer.

        Consider F(n,m) = Integral((t-1)^m*log(t)^(x-1)/(t^n*(1+t^2)), (t,1,oo)).
        F(n,0) = -F(n-2,0) + (x-1)! * (n-1)^(-x)

        Let w = 2m/n, then |-a/b - I| ~ C / sqrt(n) * (w/2)^w * (1-w)^(1-w)
        The best choice is w = 2/3, with convergence rate ~ 3^(-n)/sqrt(n).

        For odd x, the initial value F(0,0) is given by MMA that:
        F(0,0) = 4^(-x) * Gamma(x) * [Zeta(x,1/4) - Zeta(x,3/4)]
               = Gamma(x) * Im(PolyLog(x,i))
               = 2^(x-1) * pi^x * abs(B_x(1/4)) / x    (using [2] when x is odd)

        For even z, MMA outputs:
        F(1,0) = 4^(-z) * (2^z - 2) * Gamma(z) * Zeta(z)  (when z is even)

        References
        ----------
        [1] https://mathworld.wolfram.com/HurwitzZetaFunction.html

        [2] https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/17/02/01/01/0005/
        """
        if (not x.is_integer) or x <= 0:
            return None

        _gammax = sp.factorial(x-1)
        R = 3 # suggest R = 2 or R = 3
        if x % 2 == 1:
            values = {(0,0): (sp.S(0), 2**(x - 1) * abs(sp.bernoulli(x, sp.S(1)/4)) / x)}
            base = 2*R
        elif x % 2 == 0:
            values = {(1,0): (sp.S(0), 4**(-x) * (2**x - 2) * _gammax * (sp.zeta(x) / sp.pi**x))}
            base = 2*R + 1

        n = 1
        while True:
            for r in range(3 if base % 2 == 1 else 2, base + 1, 2):
                a1, b1 = values[(r-2,0)]
                a2, b2 = -a1 + _gammax*(r-1)**(-x), -b1
                values[(r,0)] = (a2, b2)

            for m in (2*n, 2*n - 1):
                values[(base,m)] = cls._binomial(values, base, m, d = -2, mul = (-1)**m)

            uv = cls._lin_comb(f, x, y, values, (base,2*n-1), (base,2*n))
            if uv is not None:
                break

            n += 1
            base += 2*R
            # when x is odd, base = 2R*n;  when x is even, base = 2R*n + 1

        u, v = uv
        if u <= 0 and v <= 0:
            u, v = -u, -v
        z = sp.symbols('x')
        integrand = (z**2-1)**(2*n-1) * (u + v*(z**2-1)).together() / z**base / (1 + z**2) * sp.log(z)**(x-1)
        txt = '%s = \\int_1^{\\infty} %s \\text{d}x > 0'%(
            lt(fx - y) if great == '>' else lt(y - fx), lt(integrand))
        return txt

    @classmethod
    def exp_Catalan(cls, f, x, y, fx, great):
        """
        This is a special function defined here. f(x) = Catalan^x.
        Currently it only supports x == 1.

        Consider F(n,m) = Integral((t-1)^m*log(t)/(t^n*(1+t^2)), (t,1,oo)).
        F(n,0) = -F(n-2,0) + (n-1)^(-2)

        Let w = 2m/n, then |-a/b - I| ~ C / sqrt(n) * (w/2)^w * (1-w)^(1-w)
        The best choice is w = 2/3, with convergence rate ~ 3^(-n)/sqrt(n).

        The initial value is given by F(0,0) = Catalan.

        References
        ----------
        [1] https://mathworld.wolfram.com/CatalansConstant.html
        """
        if x != 1:
            return None

        R = 3 # suggest R = 2 or R = 3
        values = {(0,0): (sp.S(0), sp.S(1))}

        n = 1
        base = 2*R
        while True:
            for r in range(3 if base % 2 == 1 else 2, base + 1, 2):
                a1, b1 = values[(r-2,0)]
                a2, b2 = -a1 + sp.S(r-1)**(-2), -b1
                values[(r,0)] = (a2, b2)

            for m in (2*n, 2*n - 1):
                values[(base,m)] = cls._binomial(values, base, m, d = -2, mul = (-1)**m)

            uv = cls._lin_comb(f, x, y, values, (base,2*n-1), (base,2*n))
            if uv is not None:
                break

            n += 1
            base += 2*R
            # when x is odd, base = 2R*n;  when x is even, base = 2R*n + 1

        u, v = uv
        if u <= 0 and v <= 0:
            u, v = -u, -v
        z = sp.symbols('x')
        integrand = (z**2-1)**(2*n-1) * (u + v*(z**2-1)).together() / z**base / (1 + z**2) * sp.log(z)
        txt = '%s = \\int_1^{\\infty} %s \\text{d}x > 0'%(
            lt(fx - y) if great == '>' else lt(y - fx), lt(integrand))
        return txt


    @classmethod
    def log(cls, f, x, y, fx, great):
        """
        WLOG we assume x > 1 to compute log(x).
        Consider F(n,m) = Integral(t^n*(1-t)^m/(1+(x-1)t), (t,0,1))
        F(n,0) = -1/(x-1) * F(n-1,0) + 1/[n(x-1)]

        If fixing the ratio of m/n = a, we have
        |-a/b - I| = I/b ~ sqrt(pi/n) * (x-1) / (x + sqrt(a)) * z^n
        where z = [x^(-a) * (x-1)^(a+1)] / [sqrt(a)^a * (sqrt(a) + 1)^(a+1)].

        To ensure convergence, a needs to be sufficiently large, e.g. a >= x^2.
        This requires very high degree and is therefore impractical. DO NOT USE IT.
        """
        raise NotImplementedError

    @classmethod
    def asin(cls, f, x, y, fx, great):
        """
        Consider F(n,m) = Integral(t^(n)*(1-t^2)^m/sqrt(1-x^2t^2), (t,0,1))
        It can be shown that F(n,m) = a * sqrt(1-x^2) + b * arcsin(a) when n is even.
        Whilst F(n,m) = a * sqrt(1-x^2) + b when n is odd.

        Actually we have recurrsion that
        t^(n-1)*sqrt(1-x^2t^2)|_0^1 = (n-1)*F(n-2,0) - x^2*n*F(n,0).

        b_{2n,m} = Sum_{j=0}^m * C(m,j) * (-1)^j * (2n+2j)!!/(2n+2j-1)!! / x^(2n+2j+1).

        To ensure convergence, x needs to be small. The exact convergence radius is sqrt(2sqrt(2)-2).
        However, since arcsin(x) = pi/2 - arcsin(sqrt(1-x^2)), 
        we can assume x <= 1/sqrt(2) to compute arcsin(x).
        """
        values = {(0,0): (sp.S(0), 1/x), (1,0): (-1/x**2, 1/x**2), (0,1): (1/x**2/2, (2*x**2-1)/(2*x**3))}
        n = 1
        # K = sp.sqrt(1 - x**2)
        while True:
            for r in range(4*n - 3, 4*n + 3):
                if values.get((r, 0)) is not None:
                    continue
                a1, b1 = values[(r-2, 0)]
                a2, b2 = ((r-1) * a1 - 1) / r / x**2, ((r-1) * b1) / r / x**2
                values[(r, 0)] = (a2, b2)

            values[(2*n, n)] = cls._binomial(values, 2*n, n, d = 2)
            values[(2*n, n-1)] = cls._binomial(values, 2*n, n-1, d = 2)
            values[(2*n-1, n)] = cls._binomial(values, 2*n-1, n, d = 2)

            (a1, b1), (a2, b2), (a3, b3) = values[(2*n,n-1)], values[(2*n-1,n)], values[(2*n,n)]
            M = sp.Matrix([
                [a1, 0, b1], [a2, b2, 0], [a3, 0, b3]
            ]).T # three columns are coeffs of (sqrt(1-x^2), rational, arcsin(x))
            if M.det() != 0:
                u, v, w = M.solve(sp.Matrix([0, -y, 1]))
                if (u>=0 and v>=0 and w>=0) or (u<=0 and v<=0 and w<=0):
                    break

            n += 1

        if u <= 0 and v <= 0 and w <= 0:
            u, v, w = -u, -v, -w
        z = sp.symbols('x')
        mz = sp.UnevaluatedExpr(1-z**2)
        integrand = z**(2*n-1)*(1-z**2)**(n-1) * (u*z + v*mz + w*z*mz).together() / sp.sqrt(1 - (x*z)**2)
        txt = '%s = \\int_0^1 %s \\text{d}x > 0'%(
            lt(fx - y) if great == '>' else lt(y - fx), lt(integrand))
        return txt

    @classmethod
    def atan(cls, f, x, y, fx, great):
        """
        Consider F(n,m) = Integral(t^(2n)*(1-t^2)^m/(1+(xt)^2), (t,0,1))
        F(n,m) = 1/x^2 * [-F(n-1, m) + Integral(t^(2n-2)*(1-t^2)^m, (t,0,1))]
        where Integral(t^(2n-2)*(1-t^2)^m, (t,0,1)) = B(n - 1/2, m + 1) / 2

        We can actually compute that 
        F(n,n) = (-1)^n(x^2+1)^n / x^(4n+1) * arctan(x) + q
        And |-a/b - I| ~ (x/2)^(2n) / (1 + x^2/2) * sqrt(pi/2/n).
        Hence the method converges only when |x| <= sqrt(2sqrt(2) + 2).
        """
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

            # expand (1-x^2)^m where m == n
            a, b = cls._binomial(values, n, n)
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


prove_approx = _prove_approx._solve
