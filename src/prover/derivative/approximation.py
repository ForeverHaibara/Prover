from typing import Callable, Union

import sympy as sp

from ...basic.utils import rational_between
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

def exp_pi(x):
    return sp.pi ** x



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

        elif f == sp.atan or f == sp.asin:
            if x > 0 and y <= 0:
                return '\\operatorname{%s} %s > %s'%(f.__name__, lt(x), racomp(0, y))
            elif x < 0 and y >= 0:
                return '\\operatorname{%s}\\left(%s\\right) < %s'%(f.__name__, lt(x), racomp(0, y))

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
            try:
                f = getattr(sp, f)
            except AttributeError:
                raise  AttributeError("Function '%s' is not supported."%f)

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
    def exp_pi(cls, f, x, y, err, great, method = 'taylor'):
        method_func = cls._get_method_func(method)
        return method_func(f, x, y, err)

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
        if abs(x) <= 1:
            # guarantee convergence
            txt = method_func(f, x, y, err)
            return txt
        elif abs(y) >= sp.pi / 2:
            prove_pi = method_func(exp_pi, sp.S(1), abs(y) * 2, err)
            txt = '%s\\\\ & \\Rightarrow\ %s %s %s\\frac{\\pi}{2} %s %s'%(
                prove_pi, lt(f(x)), great, '-' if great == '>' else '', great, lt(y)
            )
            return txt
        else:
            # atan(x) = pi/2 - atan(1/x) (x > 0)
            # first we find a rational number between atan(1/x) and pi/2 - y
            # we assume sgn(x) == sgn(y)
            mid = rational_between(f(abs(1/x)), sp.pi / 2 - abs(y))
            txt = method_func(f, abs(1/x), mid, err)
            v = abs(y) + mid
            txt2 = method_func(exp_pi, sp.S(1), 2*v)
            txt = '%s\\\\ & %s\\\\ & \\Rightarrow\ \\operatorname{atan}\\left(%s\\right)'\
                ' = %s\\frac{\\pi}{2} %s\\operatorname{atan}\\left(%s\\right)'\
                '%s %s %s %s = %s'%(
                    txt, txt2, lt(x), 
                    '-' if x < 0 else '', '+' if x < 0 else '-', lt(abs(1/x)),
                    great, lt(-v if x < 0 else v), '-' if x > 0 else '+', lt(mid), lt(y)
            )
            return txt



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
    def exp_pi(cls, f, x, y, err, fx, great):
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
        if x % 2 == 1:
            values = {(0,0): (sp.S(0), 2**(x - 1) * abs(sp.bernoulli(x, sp.S(1)/4)) / x)}
            base = 6
        elif x % 2 == 0:
            values = {(1,0): (sp.S(0), 4**(-x) * (2**x - 2) * _gammax * (sp.zeta(x) / sp.pi**x))}
            base = 7

        n = 1
        while True:
            for r in range(base - 4, base + 1, 2):
                a1, b1 = values[(r-2,0)]
                a2, b2 = -a1 + _gammax*(r-1)**(-x), -b1
                values[(r,0)] = (a2, b2)

            for m in (2*n, 2*n - 1):
                a, b = sp.S(0), sp.S(0)
                for k in range(m + 1):
                    # expand (x^2-1)^m
                    a1, b1 = values[(base-2*k, 0)]
                    coeff = sp.binomial(m, k) * (-1)**(m-k)
                    a, b = a + coeff * a1, b + coeff * b1
                values[(base,m)] = (a, b)

            uv = cls._lin_comb(f, x, y, values, (base,2*n-1), (base,2*n))
            if uv is not None:
                break

            n += 1
            base += 6
            # when x is odd, base = 6*n;  when x is even, base = 6*n + 1

        u, v = uv
        if u <= 0 and v <= 0:
            u, v = -u, -v
        z = sp.symbols('x')
        integrand = (z**2-1)**(2*n-1) * (u + v*(z**2-1)).together() / z**base / (1 + z**2) * sp.log(z)**(x-1)
        txt = '%s = \\int_1^{\\infty} %s \\text{d}x > 0'%(
            lt(fx - y) if great == '>' else lt(y - fx), lt(integrand))
        return txt

    @classmethod
    def log(cls, f, x, y, err, fx, great):
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
    def atan(cls, f, x, y, err, fx, great):
        """
        Consider F(n,m) = Integral(t^(2n)*(1-t^2)^m/(1+(xt)^2), (t,0,1))
        F(n,m) = 1/x^2 * [-F(n-1, m) + Integral(t^(2n-2)*(1-t^2)^m, (t,0,1))]
        where Integral(t^(2n-2)*(1-t^2)^m, (t,0,1)) = B(n - 1/2, m + 1) / 2

        We can actually compute that 
        F(n,n) = (-1)^n(x^2+1)^n / x^(4n+1) * arctan(x) + q
        And |-a/b - I| ~ (x/2)^(2n) / (1 + x^2/2) * sqrt(pi/2/n).
        Hence the method converges only when |x| <= 2.
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


prove_approx = _prove_approx._solve