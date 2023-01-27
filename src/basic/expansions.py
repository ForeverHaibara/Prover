import sympy as sp


def taylor(f, n = 1):
    assert n >= 1 and n == int(n), 'n should be a positive integer'

    poly = None

    if isinstance(f, str):
        vals = [sp.S(0)]
        f = f.lower()
        if f.startswith('e') or f.startswith('sin') or f.startswith('cos'):
            vals[0] = sp.S(1)
            for i in range(1, n + 1):
                vals.append(vals[-1] / i)
            
            if f.startswith('sin'):
                for i in range(0, n + 1, 2):
                    vals[i] = 0
                for i in range(3, n + 1, 4):
                    vals[i] = -vals[i]
            elif f.startswith('cos'):
                for i in range(1, n + 1, 2):
                    vals[i] = 0
                for i in range(2, n + 1, 4):
                    vals[i] = -vals[i]
        elif f.startswith('ln'):
            vals += [(sp.Rational(1,i+1) if i%2==0 else -sp.Rational(1,i+1)) for i in range(n)]
        
        elif f.startswith('tan'):
            # https://math.stackexchange.com/questions/2098941/bernoulli-numbers-taylor-series-expansion-of-tan-x 
            
            # bernoulli[i] = C(n,i) * B(2i)
            #bernoulli = sp.polys.polytools.Poly(sp.bernoulli(3, 'x')).coeffs()

            t = sp.S(1)   # 2 ** (2i)
            s = sp.S(1)   # (2i)!
            # coeff of x^(2i-1) in tanx = 2^(2i) * (2^(2i) - 1) /  (2i)! * (-1)^(i-1) * B(2i)
            for i in range(1, n + 1):
                t = t * 4
                s = s * (2 * i) * (2 * i - 1)
                vals.append(t / s * (t - 1) * sp.bernoulli(2 * i))
                if i % 2 == 0:
                    vals[-1] = -vals[-1]
                vals.append(0)
            
            if len(vals) > n + 1: 
                vals.pop()

        elif f.startswith('lambert'):
            # https://mathworld.wolfram.com/LagrangeInversionTheorem.html
            # https://math.stackexchange.com/questions/333217/expansion-of-lambert-w-for-negative-values 
            # lamberw(x) = sum k^(k-1) / k! * x^k   (|x|< 1/e)
            s = sp.S(1)
            for i in range(1, n + 1):
                s = s * i
                vals.append((-i) ** (i - 1) / s)
        else:
            assert False, 'Function %s not supported.'%f
    
        t = sp.symbols('x')
        poly = sum((t**i * v for i, v in enumerate(vals))).as_poly(t)


    elif isinstance(f, sp.Expr):
        assert False, 'Function %s not supported.'%f
        return None

    return poly


def pade(f, m = 3, n = None):
    # https://math.stackexchange.com/questions/860293 
    # https://zhuanlan.zhihu.com/p/92873681 
    
    if n is None: n = m
    if isinstance(f, str):
        return pade(f = taylor(f, m + n), m = m, n = n)
    elif isinstance(f, sp.Expr):
        f = f.as_poly()
    
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

    t = sp.symbols('x')
    v = sp.cancel(sum([p[i] * t ** i for i in range(m+1)]) / 
                    sum([q[i] * t ** i for i in range(n+1)]))

    return v