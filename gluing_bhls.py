"""
Implementation of triple covers following

Genus-2 curves and Jacobians with a given number of points
Reinier Bröker, Everett W. Howe, Kristin E. Lauter, Peter Stevenhagen
https://arxiv.org/abs/1403.6911
"""

from sage.all import EllipticCurve, CRT, GF, HyperellipticCurve, proof
from sage.schemes.hyperelliptic_curves.jacobian_morphism import (
    cantor_reduction,
    cantor_reduction_simple,
)

# No strict primality proof
proof.arithmetic(False)
# Speed hack
def speed_hack():
    from sage.all import cached_method

    p = 2**127 - 1  # Arbitrary large prime
    to_patch = [GF(3), GF(3**2), GF(p), GF(p**2)]
    for x in to_patch:
        type(x).vector_space = cached_method(type(x).vector_space)


speed_hack()


def solve_params(j1, j2):
    k = j1.parent()
    R = k["w", "x", "y", "z"]
    w, x, y, z = R.gens()
    # fmt:off
    g1 = 1728*(w*w*y + 4*w*x*z - 4*x*x*y*y)**3 - j1*(w**3 + x**2)**2 * (y**3 + z**2)
    g2 = 1728*(w*y*y + 4*x*y*z - 4*w*w*z*z)**3 - j2*(w**3 + x**2) * (y**3 + z**2)**2
    g3 = 12*w*y + 16*x*z - 1
    # fmt:on

    I = R.ideal([g1, g2, g3])
    # Solve w=x
    Iwx = I.subs(w=x).elimination_ideal([y, z])
    for v in _uniroots(Iwx.basis[0]):
        Iy = I.subs(w=v, x=v).elimination_ideal(z)
        for vy in _uniroots(Iy.basis[0]):
            for vz in _uniroots(g3(w=v, x=v, y=vy)):
                # print(v, v, vy, vz)
                yield v, v, vy, vz
    # Solve y=z
    Iyz = I.subs(y=z).elimination_ideal([w, x])
    for v in _uniroots(Iyz.basis[0]):
        Iw = I.subs(y=v, z=v).elimination_ideal(x)
        for vw in _uniroots(Iw.basis[0]):
            for vx in _uniroots(g3(w=vw, y=v, z=v)):
                # print(vw, vx, v, v)
                yield vw, vx, v, v


def _uniroots(p):
    return p.univariate_polynomial().roots(multiplicities=False)


def bhls_curves(a, b, c, d):
    k = a.parent()
    x = k["x"].gen()
    D1 = a**3 + b**2
    D2 = c**3 + d**2
    if D1 == 0 or D2 == 0:
        return None, None, None, None, None
    # fmt:off
    H = (x**3 + 3*a*x + 2*b)*(2*d*x**3 + 3*c*x**2 + 1)
    E1 = x**3 + 12*(2*a*a*d-b*c)*x**2 + 12*(16*a*d*d+3*c**2)*D1*x + 512*D1**2*d**3
    E2 = x**3 + 12*(2*c*c*b-a*d)*x**2 + 12*(16*c*b*b+3*a**2)*D2*x + 512*D2**2*b**3
    def f1(x, y):
        den = x**3+3*a*x+2*b
        return 12*D1*(-2*d*x+c)/den, y*D1*(16*d*x**3-12*c*x**2-1)/den**2
    def f2(x, y):
        den = 2*d*x**3+3*c*x**2+1
        return 12*D2*(a*x**3-2*b*x*x)/den, y*D2*(x**3+12*a*x-16*b)/den**2
    # fmt:on
    return H, E1, E2, f1, f2


def divisor(a, b, c, d, h, pt1, pt2, check=False):
    "Divisor on H obtained from first projection"
    k = a.parent()
    x = k["x"].gen()
    den1 = x**3 + 3 * a * x + 2 * b
    den2 = 2 * d * x**3 + 3 * c * x**2 + 1
    D1 = a**3 + b**2
    D2 = c**3 + d**2
    # Point 1
    x1, y1 = pt1[0], pt1[1]
    mumX1 = 12 * D1 * (-2 * d * x + c) - x1 * den1  # degree 3
    _, inv, _ = (16 * d * x**3 - 12 * c * x**2 - 1).xgcd(mumX1)
    denred = den1 % mumX1
    mumY1 = y1 * denred**2 * inv / D1  # degree 6

    # Point 2
    x2, y2 = pt2[0], pt2[1]
    mumX2 = 12 * D2 * (a * x**3 - 2 * b * x * x) - x2 * den2  # degree 3
    _, inv, _ = (x**3 + 12 * a * x - 16 * b).xgcd(mumX2)
    denred = den2 % mumX2
    mumY2 = y2 * denred**2 * inv / D2  # degree 6

    mumX = mumX1 * mumX2
    mumY = CRT([mumY1, mumY2], [mumX1, mumX2])

    if check:
        print("check1", (mumY1**2 - h) % mumX1)
        print("check2", (mumY2**2 - h) % mumX2)
        print("check1+2", (mumY**2 - h) % mumX)
    mumX, mumY = cantor_reduction_simple(mumX, mumY, h, 2)
    if check:
        print("sum", mumX, mumY)
        print("check1+2", (mumY**2 - h) % mumX)
    return mumX, mumY


def triple_cover(E1, T11, T12, E2, T21, T22, check=False):
    # If E1 and E2 have rational 3-torsion there are 24 possible
    # anti isometries between E1[3] and E2[3].
    j = T11.weil_pairing(T12, 3)
    if j == T21.weil_pairing(T22, 3):
        T22 = -T22
    assert j**3 == 1

    # Twisting coefficient
    k = j.parent()
    if k.order() % 4 == -1:
        tw = k(-1)
    else:
        for _ in range(1000):
            x = k.random_element()
            if not x.is_square():
                tw = x
                break

    j1 = E1.j_invariant()
    j2 = E2.j_invariant()
    for a, b, c, d in solve_params(j1, j2):
        # print("== PARAMS", a, b, c, d, "==")
        h, e1, e2, f1, f2 = bhls_curves(a, b, c, d)
        if h is None:
            continue
        try:
            ell1 = EllipticCurve([0, e1[2], 0, e1[1], e1[0]])
            iso1 = E1.isomorphism_to(ell1)
            ell2 = EllipticCurve([0, e2[2], 0, e2[1], e2[0]])
            iso2 = E2.isomorphism_to(ell2)
            twist = False
        except ValueError:
            # Quadratic twist
            # (x, y) -> (tw*x, tw^(3/2)*y)
            ell1 = EllipticCurve([0, tw * e1[2], 0, tw**2 * e1[1], tw**3 * e1[0]])
            iso1 = E1.isomorphism_to(ell1)
            ell2 = EllipticCurve([0, tw * e2[2], 0, tw**2 * e2[1], tw**3 * e2[0]])
            iso2 = E2.isomorphism_to(ell2)
            twist = True
            h = tw * h
            # Twisted morphisms: (x, y) = tw*f(x, y)

        if check:
            for _ in range(20):
                x = k.random_element()
                if h(x).is_square():
                    y = h(x).sqrt()
                    try:
                        x1, y1 = f1(x, y)
                        x2, y2 = f2(x, y)
                    except ZeroDivisionError:
                        continue
                    if twist:
                        x1, y1, x2, y2 = tw * x1, tw * y1, tw * x2, tw * y2
                    assert (x1, y1) in ell1
                    assert (x2, y2) in ell2

        # print(iso1.rational_maps())
        # print(iso2.rational_maps())
        # Validate isogeny kernel
        t11 = iso1(T11)
        t21 = iso2(T21)
        if check:
            assert t11 in ell1
            assert t21 in ell2
            print("t11 =", t11)
            print("t21 =", t21)
        if twist:
            t11 = (t11[0] / tw, t11[1] / tw)
            t21 = (t21[0] / tw, t21[1] / tw)
        DX1, DY1 = divisor(a, b, c, d, h, t11, t21, check=check)
        t12 = iso1(T12)
        t22 = iso2(T22)
        if twist:
            t12 = (t12[0] / tw, t12[1] / tw)
            t22 = (t22[0] / tw, t22[1] / tw)
        DX2, DY2 = divisor(a, b, c, d, h, t12, t22, check=check)

        if DX1 == 1 and DX2 == 1:
            # Return morphisms as:
            # (x, y) -> (R1(x), y * R2(x))
            # {y²=h} => twisted e1 => E1
            x = k["x"].gen()
            rx, ry = f1(x, 1)
            # ry^2 h == e1(rx)
            if twist:
                rx, ry = tw * rx, tw * ry
            elif check:
                assert ry**2 * h == e1(rx)
            # print("dual", iso1.dual().rational_maps())
            # print(rx, ry)
            rx, ry = [r(rx, ry) for r in iso1.dual().rational_maps()]
            if check:
                print(rx, ry)
                p1 = -E1.defining_polynomial()
                assert ry**2 * h == p1(rx, 0, 1)
            proj1 = (rx, ry)

            rx, ry = f2(x, 1)
            if twist:
                rx, ry = tw * rx, tw * ry
            rx, ry = [r(rx, ry) for r in iso2.dual().rational_maps()]
            if check:
                p2 = -E2.defining_polynomial()
                assert ry**2 * h == p2(rx, 0, 1)
            proj2 = (rx, ry)

            return h, proj1, proj2

    return None, None, None
