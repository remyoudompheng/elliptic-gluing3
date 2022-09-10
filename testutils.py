from sage.all import EllipticCurve

def make_curve(t):
    K = t.parent()
    p3 = 4 * (t**3 - 1) / 3
    p2 = -3 * t**2
    p1 = 2 * t
    p0 = 1 / K(-3)
    return EllipticCurve(K, [0, p2 / p3**2, 0, p1 / p3**3, p0 / p3**4])


def torsion_basis(E):
    P3 = E.division_polynomial(3)
    roots = P3.roots(multiplicities=False)
    if len(roots) < 2:
        raise ValueError("not enough 3-torsion")
    r1, r2 = roots[:2]
    T1 = E.lift_x(r1)
    T2 = E.lift_x(r2)
    assert 2*T1 == -T1
    assert 2*T2 == -T2
    assert T1.weil_pairing(T2, 3) != 1
    return T1, T2
