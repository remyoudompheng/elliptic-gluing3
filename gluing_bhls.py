"""
Implementation of triple covers following

Genus-2 curves and Jacobians with a given number of points
Reinier Bröker, Everett W. Howe, Kristin E. Lauter, Peter Stevenhagen
https://arxiv.org/abs/1403.6911

The algorithm described in this article enumerates isomorphism
classes of triple covers (H→E1,H→E2) without specifying
an anti-isometry of group schemes between E1[3] and E2[3].

The result of the algorithm is adapted to answer the problem with
specified anti-isometry (between k-rational 3-torsion).
"""

from sage.all import EllipticCurve, CRT, GF, HyperellipticCurve, PolynomialRing, proof
from sage.schemes.hyperelliptic_curves.jacobian_morphism import (
    cantor_reduction,
    cantor_reduction_simple,
    cantor_composition_simple,
)

# No strict primality proof
proof.arithmetic(False)
# Speed hack for Sage < 9.7
def speed_hack():
    from sage.all import cached_method

    p = 2**127 - 1  # Arbitrary large prime
    to_patch = [GF(3), GF(3**2), GF(p), GF(p**2)]
    for x in to_patch:
        type(x).vector_space = cached_method(type(x).vector_space)


speed_hack()


def debug(*args):
    if False:
        print(*args)


def solve_params(j1, j2):
    """
    Enumerate (possibly duplicate) parameters from the universal family
    with prescribed j-invariants.
    """
    k = j1.parent()
    if k.degree() == 1 and k.characteristic() < 2**31:
        solve = solve_params1
    elif k.characteristic() < 2**29:
        solve = solve_params1
    else:
        solve = solve_params2
    for params in solve(k, j1, j2):
        yield params
    if j1 == 0 and j2 == 0:
        yield k(0), k(2), k(0), 1 / k(32)
    if j1 == k(1728) and j2 == k(1728):
        yield k(2), k(0), 1 / k(24), k(0)


def solve_params1(k, j1, j2):
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
                # assert all(g(v, v, vy, vz) == 0 for g in (g1, g2, g3))
                yield v, v, vy, vz
    # Solve y=z
    Iyz = I.subs(y=z).elimination_ideal([w, x])
    for v in _uniroots(Iyz.basis[0]):
        Iw = I.subs(y=v, z=v).elimination_ideal(x)
        for vw in _uniroots(Iw.basis[0]):
            for vx in _uniroots(g3(w=vw, y=v, z=v)):
                # print(vw, vx, v, v)
                # assert all(g(vw, vx, v, v) == 0 for g in (g1, g2, g3))
                yield vw, vx, v, v


def solve_params2(k, j1, j2):
    vars = ["w", "x", "y", "z"]
    R = PolynomialRing(k, names=vars)
    w, x, y, z = R.gens()
    if k.degree() > 1 and k.characteristic() >= 2**29:
        # Singular does not support it
        gb_algo = "toy"
        Rinvlex = PolynomialRing(
            k, names=vars, implementation="generic", order="invlex"
        )
        Rlex = PolynomialRing(k, names=vars, implementation="generic", order="lex")
    else:
        gb_algo = ""
        Rinvlex = R.change_ring(order="invlex")
        Rlex = R.change_ring(order="lex")
    # fmt:off
    g1 = 1728*(w*w*y + 4*w*x*z - 4*x*x*y*y)**3 - j1*(w**3 + x**2)**2 * (y**3 + z**2)
    g2 = 1728*(w*y*y + 4*x*y*z - 4*w*w*z*z)**3 - j2*(w**3 + x**2) * (y**3 + z**2)**2
    g3 = 12*w*y + 16*x*z - 1
    # fmt:on

    # Solve w=x
    I = R.ideal([g1, g2, g3])
    Iwx = I.subs(x=w).change_ring(Rinvlex).groebner_basis(algorithm=gb_algo)
    # assert Iwx[-1].variables() == (w,)
    for v in _uniroots(Iwx[-1]):
        for _p in reversed(Iwx):
            if _p.degree(y) > 0:
                py = _p.subs(w=v)
                if not py.is_constant():
                    # assert py.variables() == (y,)
                    break
        for vy in _uniroots(py):
            for vz in _uniroots(g3(w=v, x=v, y=vy)):
                # assert all(g(v, v, vy, vz) == 0 for g in (g1, g2, g3))
                yield v, v, vy, vz
    # Solve y=z
    Iyz = I.subs(y=z).change_ring(Rlex).groebner_basis(algorithm=gb_algo)
    # assert Iyz[-1].variables() == (z,)
    for v in _uniroots(Iyz[-1]):
        for _p in reversed(Iyz):
            if _p.degree(x) > 0:
                px = _p.subs(z=v)
                if not px.is_constant():
                    # assert px.variables() == (x,)
                    break
        for vx in _uniroots(px):
            for vw in _uniroots(g3(x=vx, y=v, z=v)):
                # assert all(g(vw, vx, v, v) == 0 for g in (g1, g2, g3))
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

    mumX, mumY = cantor_composition_simple([mumX1, mumY1], [mumX2, mumY2], h, 2)

    if check:
        # debug("check1", (mumY1**2 - h) % mumX1)
        assert (mumY1**2 - h) % mumX1 == 0
        # debug("check2", (mumY2**2 - h) % mumX2)
        assert (mumY2**2 - h) % mumX2 == 0
        # debug("check1+2", (mumY**2 - h) % mumX)
        assert (mumY**2 - h) % mumX == 0
    mumX, mumY = cantor_reduction_simple(mumX, mumY, h, 2)
    if check:
        debug("====> SUM", mumX, mumY)
        assert (mumY**2 - h) % mumX == 0
        # debug("check1+2", (mumY**2 - h) % mumX)
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

    def isomorphisms_to(ell1, ell2):
        isos1 = [
            f for f in E1.isomorphisms(ell1) if f(T11).weil_pairing(f(T12), 3) == j
        ]
        isos2 = [
            f for f in E2.isomorphisms(ell2) if f(T21).weil_pairing(f(T22), 3) == j * j
        ]
        for iso1 in isos1:
            for iso2 in isos2:
                yield iso1, iso2

    def covers():
        """
        Iterator over triple covers of E1 and E2.
        Due to automorphisms, an single isomorphism class of triple covers
        can correspond to several triple covers with specified anti-isometry.
        """
        for a, b, c, d in solve_params(j1, j2):
            debug("== PARAMS", a, b, c, d, "=======================")
            pars = (a, b, c, d)
            h, e1, e2, f1, f2 = bhls_curves(a, b, c, d)
            if h is None:
                continue
            ell1 = EllipticCurve([0, e1[2], 0, e1[1], e1[0]])
            ell2 = EllipticCurve([0, e2[2], 0, e2[1], e2[0]])
            twist = False
            for iso1, iso2 in isomorphisms_to(ell1, ell2):
                yield h, pars, f1, f2, iso1, iso2, twist
            # Quadratic twist
            # (x, y) -> (tw*x, tw^(3/2)*y)
            ell1 = EllipticCurve([0, tw * e1[2], 0, tw**2 * e1[1], tw**3 * e1[0]])
            ell2 = EllipticCurve([0, tw * e2[2], 0, tw**2 * e2[1], tw**3 * e2[0]])
            twist = True
            # Twisted morphisms: (x, y) = tw*f(x, y)
            for iso1, iso2 in isomorphisms_to(ell1, ell2):
                yield tw * h, pars, f1, f2, iso1, iso2, twist

    for h, pars, f1, f2, iso1, iso2, twist in covers():
        a, b, c, d = pars
        ell1, ell2 = iso1.codomain(), iso2.codomain()
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
                    assert iso1.dual()(ell1(x1, y1)) in E1
                    assert iso2.dual()(ell2(x2, y2)) in E2

        # print(iso1.rational_maps())
        # print(iso2.rational_maps())
        # Validate isogeny kernel
        t11 = iso1(T11)
        t21 = iso2(T21)
        if check:
            assert t11 in ell1
            assert t21 in ell2
            debug("t11 =", t11)
            debug("t21 =", t21)
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

        if (DX1 == 1 and DX2 == 1) or check:
            # Return morphisms as:
            # (x, y) -> (R1(x), y * R2(x))
            # {y²=h} => twisted e1 => E1
            x = k["x"].gen()
            rx, ry = f1(x, 1)
            # ry^2 h == e1(rx)
            if twist:
                rx, ry = tw * rx, tw * ry
            elif check:
                e1 = -iso1.codomain().defining_polynomial().subs(y=0, z=1)
                assert ry**2 * h == e1(x=rx)
            # print("dual", iso1.dual().rational_maps())
            # print(rx, ry)
            rx, ry = [r(rx, ry) for r in iso1.dual().rational_maps()]
            if check:
                debug(rx, ry)
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

            if DX1 == 1 and DX2 == 1:
                return h, proj1, proj2

    return None, None, None
