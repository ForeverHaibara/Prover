import sympy as sp

def is_rational_quadratic_roots(x):
    """
    Check whether x is a root of rational quadratic polynomial,
    which is in the form of (p1/q1) + (p2/q2) * sqrt(Δ)
    E.g. 3+sqrt(5),   sqrt(3)+2
    """
    if isinstance(x, sp.Rational):
        return False
    
    elif isinstance(x, sp.Pow):
        if x.args[1] == sp.S(1) / 2 and isinstance(x.args[0], sp.Rational):
            return True
    
    elif isinstance(x, sp.Mul):
        if len(x.args) == 2:
            if isinstance(x.args[0], sp.Rational):
                return is_rational_quadratic_roots(x.args[1])
            
            elif isinstance(x.args[1], sp.Rational):
                return is_rational_quadratic_roots(x.args[0])

    elif isinstance(x, sp.Add):
        if len(x.args) == 2:
            if isinstance(x.args[0], sp.Rational):
                return is_rational_quadratic_roots(x.args[1])
            
            elif isinstance(x.args[1], sp.Rational):
                return is_rational_quadratic_roots(x.args[0])

    return False


if __name__ == '__main__':
    x = sp.sympify('sqrt(3)-sqrt(2)')
    print(is_rational_quadratic_roots(x))