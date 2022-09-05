"""
Full computation of triple cover

0. Input is 2 Weierstrass curves with rational 3-torsion basis
1. Compute associated Hesse parameters
2. Compute normalized cubic polynomial
3. Compute sextic equation
4. Determine rational parameterisation
5. Determine hyperelliptic form and morphisms
"""

from sage.all import (
    Curve,
    EllipticCurve,
    EllipticCurve_from_cubic,
    GF,
    Matrix,
    ProjectiveSpace,
    derivative,
    factor,
    proof,
    vector,
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


def triple_cover(E1, T11, T12, E2, T21, T22):
    K = E1.base_field()
    j = T11.weil_pairing(T12, 3)
    t1, P1, a1, b1, c1 = normalize_curve(E1, j, T11, T12)
    t2, P2, a2, b2, c2 = normalize_curve(E2, j, T21, T22)
    # Beware: exchanging t1/t2 also exchanges j and j2
    XD0, XD1, XD2, XD3 = double_coords(j, t1, t2)
    YD0, YD1, YD2, YD3 = double_coords(j**2, t2, t1)
    nodes = [(XD0, YD0), (XD1, YD1), (XD2, YD2), (XD3, YD3)]
    S = make_sextic(P1.monic(), P2.monic(), nodes)
    # w1s = P1.roots(multiplicities=False)
    # w2s = P2.roots(multiplicities=False)
    X, Y = resolve_sing(S, nodes, None, None)
    NX = X.numerator()
    DX = X.denominator()
    NY = Y.numerator()
    DY = Y.denominator()
    PPX, rem = (P1[3]*NX**3 + P1[2]*NX**2*DX + P1[1]*NX*DX**2 + P1[0]* DX**3).quo_rem(DY)
    assert rem == 0
    const1 = PPX.lc()
    PX = const1 * PPX.monic().sqrt()
    PPY, rem = (P2[3]*NY**3 + P2[2]*NY**2*DY + P2[1]*NY*DY**2 + P2[0]* DY**3).quo_rem(DX)
    assert rem == 0
    const2 = PPY.lc()
    PY = const2 * PPY.monic().sqrt()
    # (x, y) => (NX/DX, PX/DX*y)
    #assert (PX / DX**2) ** 2 * (DX * DY) == const1 * P1(NX / DX)
    # (x, y) => (NY/DY, PY/DY*y)
    #assert (PY / DY**2) ** 2 * (DX * DY) == const2 * P2(NY / DY)

    c12 = (const1 * const2).sqrt()

    def f1(x, y):
        return (a1 * NX(x) / DX(x) + b1, PX(x) / DX(x) ** 2 * y * c1 / const1)

    def f2(x, y):
        return (a2 * NY(x) / DY(x) + b2, PY(x) / DY(x) ** 2 * y * c2 / c12)

    H = const1 * DX * DY
    return H, f1, f2


def make_morphism(eqH, f):
    K = eqH.base_ring()
    P = ProjectiveSpace(K, 2, names=["x", "y", "z"])
    x, y, z = P.coordinate_ring().gens()
    H = Curve([y**2 * z**4 - eqH(x).homogenize(var=z)], P)
    Xf, Yf = f(x, y)
    X = Xf.numerator() * Yf.denominator() // Xf.denominator()
    Y, Z = Yf.numerator(), Yf.denominator()
    X = X.homogenize(var=z)
    Y = Y.homogenize(var=z) * z ** (6 - Y.total_degree())
    Z = Z.homogenize(var=z)
    proj = H.hom([X, Y, Z], P)
    return proj


def hesse_j(t):
    return ((3 * t * (t**3 + 8)) / (t**3 - 1)) ** 3


def normalize_curve(E, j, T1, T2):
    """
    Given an elliptic curve E, a cubic root of 1 and (T1, T2) a basis of 3-torsion
    compute:
    - the corresponding Hesse parameter
    - a normalized Weierstrass polynomial for E': y^2 = P(x)
    - a morphism (x -> ax+b) from E' to E
    """
    xT1 = T1[0]  # 1/(t-1)
    xT2 = T2[0]  # 0
    w = T1.weil_pairing(T2, 3)
    if w == j:  # Is it a symplectic basis?
        xT12 = (T1 + T2)[0]  # -j/1-jt
    else:
        xT12 = (T1 - T2)[0]  # -j/1-jt
    # 1-jt = T2-T1 / (T1+T2)-T1
    t = (-j - 2) * (xT12 - xT2) / (xT12 - xT1) + 1
    a = (xT1 - xT2) * (t - 1)
    b = xT2
    c = (1 - t) * T1[1]  # y(T1) = -x(T1)

    a1, a2, a3, a4, a6 = E.a_invariants()
    assert a1 == 0 and a3 == 0
    x = E.base_field()["x"].gen()
    P = (a * x + b) ** 3 + a2 * (a * x + b) ** 2 + a4 * (a * x + b) + a6
    P /= c**2
    # (x,y) -> (ax+b,cy) maps E_norm(y^2=P) to E
    return t, P, a, b, c


def double_coords(j, t1, t2):
    # fmt:off
    d0 = (t1**2 - t2) / (t1**3 - 1)
    num1 = j*(t1*t2 - 1)
    den1 = num1*t1 - (t1**2 - j**2*t1*t2 - t2 + j**2)
    num2 = j**2*(t1*t2 - 1)
    den2 = num2*t1 - (t1**2 - j*t1*t2 - t2 + j)
    num3 = t1*t2 - 1
    den3 = num3*t1 - (t1**2 - t1*t2 - t2 + 1)
    # fmt:on
    return d0, num1 / den1, num2 / den2, num3 / den3


def make_sextic(P1, P2, nodes):
    K = P1.base_ring()
    assert P1[3] == 1 and P2[3] == 1
    R = K["u", "v"]
    u, v = R.gens()

    known = (
        (u**3 * v**3)
        + (v**3 * (u**2 * P1[2] + u * P1[1] + P1[0]))
        + (u**3 * (v**2 * P2[2] + v * P2[1] + P2[0]))
    )
    known_du = derivative(known, u)
    known_dv = derivative(known, v)
    rows = []
    vals = []

    # write equations from double points
    degrees = [(i, j) for i in range(3) for j in range(3)]
    for i, (xN, yN) in enumerate(nodes):
        if (xN, yN) in nodes[:i]:
            continue
        # Equations for P, dP/du, dP/dv
        vals.append(-K(known(u=xN, v=yN)))
        rows.append([xN**i * yN**j for i, j in degrees])
        vals.append(-K(known_du(u=xN, v=yN)))
        rows.append([i * xN ** max(0, i - 1) * yN**j for i, j in degrees])
        vals.append(-K(known_dv(u=xN, v=yN)))
        rows.append([j * xN**i * yN ** max(0, j - 1) for i, j in degrees])
        if (xN, yN) in nodes[i + 1 :]:
            vals.append(-K(derivative(known, u, u)(u=xN, v=yN)))
            rows.append([2 * yN**j if i == 2 else 0 for i, j in degrees])
            vals.append(-K(derivative(known, u, v)(u=xN, v=yN)))
            rows.append(
                [
                    i * xN ** (i - 1) * j * yN ** (j - 1) if i and j else 0
                    for i, j in degrees
                ]
            )
            vals.append(-K(derivative(known, v, v)(u=xN, v=yN)))
            rows.append([2 * xN**i if j == 2 else 0 for i, j in degrees])

    M = Matrix(K, rows)
    coef = M.solve_right(vector(K, vals))
    rest = sum(c * u**i * v**j for c, (i, j) in zip(coef, degrees))
    return known + rest


def resolve_sing(S, nodes, w1s, w2s):
    """
    Resolution of singularities for a (3,3)-curve with 4 nodes
    Optional points (w1, infty) or (infty, w2) are provided
    """
    N0, N1, N2, N3 = nodes
    if any(nodes[i] == nodes[j] for i in range(3) for j in range(i + 1, 4)):
        # triple point, arrange for N0 to be the triple point
        # and N1 to be the other one
        if N0 != N1:
            if N0 != N2:
                N0, N1 = N1, N0
        else:  # N0 is the triple point
            N1 = N2 if N2 != N0 else N3
    # Resolve N0
    K = S.base_ring()
    R = K["x", "y", "z"]

    def div_monom(f, q):
        res = 0
        for c, m in zip(f.coefficients(), f.monomials()):
            if not R.monomial_divides(q, m):
                raise ValueError(f"{f} not divisible by {q}")
            res += c * R.monomial_quotient(m, q)
        return res

    RT = K["T"]
    x, y, z = R.gens()
    T = RT.gen()
    # Center on N0
    x0, y0 = N0
    S = S(x, y).homogenize(var=z)
    S1 = S(x + x0 * z, y + y0 * z, z)

    Q = div_monom(S1(y * z, z * x, x * y), x**3 * y**3 * z**2)
    if N0 in (N2, N3):
        # Special case of triple ramification.
        Q = div_monom(Q, z)
        x1, y1 = N1
        qx1, qy1, qz1 = (y1 - y0, x1 - x0, (x1 - x0) * (y1 - y0))
        QT = Q(qx1 * z + x, qy1 * z + y, qz1 * z)
        num = QT[2, 0, 1] + QT[1, 1, 1] * T + QT[0, 2, 1] * T**2
        den = QT[3, 0, 0] + QT[0, 3, 0] * T**3
        xQT, yQT, zQT = -num, -num * T, den
        xQ, yQ, zQ = qx1 * zQT + xQT, qy1 * zQT + yQT, qz1 * zQT
        x_S1, y_S1, z_S1 = yQ * zQ, zQ * xQ, xQ * yQ
        X = x0 + x_S1 / z_S1
        Y = y0 + y_S1 / z_S1
        assert S(X, Y, 1) == 0
        return X, Y

    (x1, y1), (x2, y2), (x3, y3) = N1, N2, N3
    # fmt:off
    M = Matrix(K, [
        [y1-y0, x1-x0, (x1-x0)*(y1-y0)],
        [y2-y0, x2-x0, (x2-x0)*(y2-y0)],
        [y3-y0, x3-x0, (x3-x0)*(y3-y0)],
    ]).transpose()
    # fmt:on

    u, v, w = M * vector([x, y, z])
    QT = Q(u, v, w)
    C = div_monom(QT(y * z, z * x, y * x), (x * y * z) ** 2)
    assert C.total_degree() == 2
    # print("C", C // (x*y*z)**2)
    if w1s or w2s:
        if w1s:
            rat = (1 / (w1s[0] - x0), 0, 1)  # use x=w1
        else:
            rat = (0, 1 / (w2s[0] - y0), 1)  # use y=w2
        rat = M.inverse() * vector(rat)
        rat = (rat[2] / rat[0], rat[2] / rat[1], 1)  # normalized (yz,zx,xy)
    else:
        # Try to find a rational point on a finite field
        for xval in range(20):
            ys = C(x=xval, z=1).univariate_polynomial().roots(multiplicities=False)
            if ys:
                # print("rational point", (xval, ys[0], 1))
                rat = (xval, ys[0], 1)
                break
    CT = C(rat[0] * z + x, rat[1] * z + y, z)
    # a x^2 + b xy + c y^2 + dx + ey = 0 and y = ux => x=-(d+et)/(a+bt+ct^2)
    num = CT[1, 0, 1] + CT[0, 1, 1] * T
    den = CT[2, 0, 0] + CT[1, 1, 0] * T + CT[0, 2, 0] * T**2
    x_CT, y_CT, z_CT = -num, -T * num, den
    # Pull back
    x_C = x_CT + rat[0] * z_CT
    y_C = y_CT + rat[1] * z_CT
    z_C = z_CT
    x_QT, y_QT, z_QT = y_C * z_C, z_C * x_C, x_C * y_C
    x_Q, y_Q, z_Q = M * vector([x_QT, y_QT, z_QT])
    x_S1, y_S1, z_S1 = y_Q * z_Q, z_Q * x_Q, x_Q * y_Q
    X = x0 + x_S1 / z_S1
    Y = y0 + y_S1 / z_S1
    return X, Y
