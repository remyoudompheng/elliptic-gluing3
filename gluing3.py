"""
Full computation of triple cover

0. Input is 2 Weierstrass curves with rational 3-torsion basis
1. Compute associated Hesse parameters
2. Compute normalized cubic polynomial
3. Compute sextic equation
4. Determine rational parameterisation
5. Determine hyperelliptic form and morphisms

For large F_q (log q > 750 bits) the cost starts
being dominated by the 2 square roots.
"""

from sage.all import (
    Curve,
    GF,
    Matrix,
    ProjectiveSpace,
    derivative,
    proof,
    vector,
)

# No strict primality proof
proof.arithmetic(False)
# Speed hack for Sage < 9.7
def speed_hack():
    from sage.misc.banner import require_version
    from sage.all import cached_method
    if require_version(9, 7):
        return

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
    if nodes[0] == nodes[1]:
        nodes = [nodes[0]] + [n for n in nodes if n != nodes[0]]
    elif nodes[2] == nodes[3]:
        nodes = [nodes[2]] + [n for n in nodes if n != nodes[2]]
    S = make_sextic(P1.monic(), P2.monic(), nodes)
    ramif = ramif1_coords(S, t1, t2)
    assert ramif is not None
    X, Y = resolve_sing(S, nodes, ramif=ramif)
    NX = X.numerator()
    DX = X.denominator()
    NY = Y.numerator()
    DY = Y.denominator()
    if all(pol.degree() <= 2 for pol in [NX, DX, NY, DY]):
        raise ValueError("H is singular")
    # fmt:off
    PPX, remX = (P1[3]*NX**3 + P1[2]*NX**2*DX + P1[1]*NX*DX**2 + P1[0]*DX**3).quo_rem(DY)
    PPY, remY = (P2[3]*NY**3 + P2[2]*NY**2*DY + P2[1]*NY*DY**2 + P2[0]*DY**3).quo_rem(DX)
    # fmt:on
    assert remX == 0 and remY == 0
    alpha1, alpha2 = PPX.lc(), PPY.lc()
    u1, u2 = NX[3] / DX[3], NY[3] / DY[3]
    PX = alpha1 * PPX.monic().sqrt()
    PY = alpha2 * PPY.monic().sqrt()

    # fmt:off
    den12 = (t1**3-1)*(t2**3-1)
    c12 = t1*u1+t2*u2-u1*u2*(t1*t2+2) - (1 + 2*(t1*t2-1)**3/den12)/K(3)
    assert c12*c12 == alpha1*alpha2

    def f1(x, y):
        return (a1 * NX(x)/DX(x) + b1, PX(x)/DX(x)**2 * y * c1 / alpha1)

    def f2(x, y):
        return (a2 * NY(x)/DY(x) + b2, PY(x)/DY(x)**2 * y * c2 / c12)
    # fmt:on

    H = alpha1 * DX * DY
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
    j2 = j*j
    d0 = (t1**2 - t2) / (t1**3 - 1)
    num = t1*t2 - 1
    den1 = (t1-1)*(t1-j2)*(t2-j2)
    den2 = (t1-1)*(t1-j)*(t2-j)
    den3 = (t2-1)*(t1-j)*(t1-j2)
    # fmt:on
    return d0, num / den1, num / den2, num / den3


def ramif1_coords(S, t1, t2):
    # fmt:off
    num = 4*t1**2*t2**3  - t1**2 - t2**4 - 6*t1*t2**2 + 4*t2
    den = 4*(t1**3-1)*(t2**3-1)
    deny = t2**3 - 3*t1*t2 + 2
    # fmt:on
    x = num / den
    return (x, (t2**2 - t1)/deny if deny != 0 else None)

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


def resolve_sing(S, nodes, ramif):
    """
    Resolution of singularities for a (3,3)-curve with 4 nodes
    Optional points (w1, infty) or (infty, w2) are provided
    """
    if ramif in nodes:
        nodes = [ramif] + [n for n in nodes if n != ramif]

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
    x0, y0 = nodes[0]
    S = S(x, y).homogenize(var=z)
    S1 = S(x + x0 * z, y + y0 * z, z)

    Q = div_monom(S1(y * z, z * x, x * y), x**3 * y**3 * z**2)
    if len(nodes) == 2:
        N0, N1 = nodes
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

    (x1, y1), (x2, y2), (x3, y3) = nodes[1:]
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

    if ramif == (x0, y0):
        rat = (1, 0, 0)  # vertical tangent
    elif ramif[1] is None:
        rat = (1 / (ramif[0] - x0), 0, 1)  # at infinity
    else:
        rat = (1 / (ramif[0] - x0), 1 / (ramif[1] - y0), 1)
    assert Q(*rat) == 0
    rat = M.inverse() * vector(rat)
    assert QT(*rat) == 0
    rat = (rat[2] / rat[0], rat[2] / rat[1])

    CT = C(rat[0] * z + x, rat[1] * z + y, z)
    # a x^2 + b xy + c y^2 + dx + ey = 0 and y = ux => x=-(d+et)/(a+bt+ct^2)
    for Tparam in [T] + [K(a) + 1 / T for a in range(7)]:
        num = CT[1, 0, 1] + CT[0, 1, 1] * Tparam
        den = CT[2, 0, 0] + CT[1, 1, 0] * Tparam + CT[0, 2, 0] * Tparam**2
        x_CT, y_CT, z_CT = -num, -Tparam * num, den
        if Tparam != T:
            x_CT = (x_CT * T**2).numerator()
            y_CT = (y_CT * T**2).numerator()
            z_CT = (z_CT * T**2).numerator()
        x_C, y_C, z_C = x_CT + rat[0] * z_CT, y_CT + rat[1] * z_CT, z_CT
        x_QT, y_QT, z_QT = y_C * z_C, z_C * x_C, x_C * y_C
        x_Q, y_Q, z_Q = M * vector([x_QT, y_QT, z_QT])
        if z_Q.degree() == 4:
            xQinf, yQinf = x_Q[4] / z_Q[4], y_Q[4] / z_Q[4]
            if Q(xQinf, 0, 1) != 0 and Q(0, yQinf, 1) != 0:
                break

    x_S1, y_S1, z_S1 = y_Q * z_Q, z_Q * x_Q, x_Q * y_Q
    X = x0 + x_S1 / z_S1
    Y = y0 + y_S1 / z_S1
    return X, Y
