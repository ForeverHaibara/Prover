from sympy.calculus.util import continuous_domain
from sympy.core import S
from sympy.sets.sets import Interval, FiniteSet, Union

from .solveset import wrap_relational

def _range_from_all_points(points, skip_sort=False):
    """
    Find the range of a function given all its critical points and boundaries.

    Parameters
    ==========
    points : list
        A list of tuples (x, y, closed) where x is the critical point, y is the
        value of the function at x, and closed is a boolean indicating if the
        point is attained.

    Returns
    =======
    Set
        The range of the function.
    """
    if not points:
        return S.EmptySet
    if not skip_sort:
        points = sorted(points)

    intervals = []
    for i in range(len(points) - 1):
        (x1, y1, closed1), (x2, y2, closed2) = points[i][1], points[i + 1][1]
        if x1 == x2:
            intervals.append(FiniteSet(x1))
        if y1 > y2:
            x1, y1, closed1, x2, y2, closed2 = x2, y2, closed2, x1, y1, closed1
        creator = {
            (True, False): Interval.Ropen,
            (False, True): Interval.Lopen,
            (True, True): Interval,
            (False, False): Interval.open
        }[(bool(closed1), bool(closed2))]
        intervals.append(creator(y1, y2))
    return Union(*intervals)

def _range_from_critical_points(flim, critical_points, domain=S.Reals):
    """
    Find the range of a function given its critical points.

    Parameters
    ==========
    flim: callable
        A function to evaluate f(x) where function limit is considered.
    critical_points : list
        A list of critical points (x, y) where x is the critical point and y
        is the value of the function at x.
    domain : Set
        The domain of the function.
    """
    intervals = []
    if domain is S.EmptySet:
        return domain
    elif domain is S.Reals:
        intervals = [Interval(S.NegativeInfinity, S.Infinity)]
    elif isinstance(domain, Union):
        intervals = domain.args
    else: # if isinstance(domain, Interval):
        intervals = [domain]

    def _extract_candidates(candidates, interval: Interval, sort=True):
        extracted = []
        remains = []
        for x, y in candidates:
            if interval.contains(x):
                extracted.append((x, y))
            else:
                remains.append((x, y))
        if sort:
            extracted = sorted(extracted)
        return extracted, remains

    candidates = critical_points
    frange = []

    for interval in intervals:
        if isinstance(interval, FiniteSet):
            # take care of discrete points
            frange.append(FiniteSet(*[flim(x, dir='+-') for x in interval.args]))
        elif isinstance(interval, Interval):
            extracted, candidates = _extract_candidates(candidates, interval)

            extracted = [(interval.left, flim(interval.left, dir='+'))] + extracted \
                            + [(interval.right, flim(interval.right, dir='-'))]
            is_open = [interval.left_open] + [False] * len(extracted) + [interval.right_open]
            for i in range(len(extracted) - 1):
                y1, y2, op1, op2 = extracted[i][1], extracted[i+1][1], is_open[i], is_open[i+1]
                if y1 > y2:
                    y1, y2, op1, op2 = y2, y1, op2, op1

                frange.append(Interval(y1, y2, left_open=op1, right_open=op2))

        else:
            raise TypeError("Unsupported domain %s."%interval)

    return Union(*frange)