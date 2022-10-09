# Only verified equations in this script

from sage.all import (
    AffineSpace,
    EllipticCurve,
    EllipticCurve_from_cubic,
    GF,
    Matrix,
    ProjectiveSpace,
    QQ,
    ZZ,
    vector,
)


def P2():
    P = ProjectiveSpace(QQ, 2, names=["x", "y", "z"])
    return P


def hesse(R, t):
    x, y, z = R.gens()
    return x**3 + y**3 + z**3 - 3 * t * x * y * z


def dual_hesse(R, t):
    x, y, z = R.gens()
    return (
        x**6
        + y**6
        + z**6
        + (4 * t**3 - 2) * (x**3 * y**3 + y**3 * z**3 + z**3 * x**3)
        - 6 * t**2 * x * y * z * (x**3 + y**3 + z**3)
        + (12 * t - 3 * t**4) * (x * y * z) ** 2
    )


def halphen_coords(x, y, z):
    X = x**6 * y**3 + y**6 * z**3 + z**6 * x**3 - 3 * (x * y * z) ** 3
    Y = x**3 * y**6 + y**3 * z**6 + z**3 * x**6 - 3 * (x * y * z) ** 3
    Z = (x * y * z) * (
        x**6 + y**6 + z**6 - x**3 * y**3 - y**3 * z**3 - z**3 * x**3
    )
    return X, Y, Z


def test_dual_hesse():
    P = P2()
    R = P.coordinate_ring()
    x, y, z = R.gens()
    for t in range(20, 40):
        h = hesse(R, t)
        hd = P.subscheme(h).dual().defining_polynomials()[0]
        assert hd(x, y, z) == dual_hesse(R, t)
    print("Test dual hesse")
    print("t =", t)
    print(hd(x, y, z))
    print(dual_hesse(R, t))


def test_halphen_coordinates():
    P = P2()
    R = P.coordinate_ring()
    R = R["t"].flattening_morphism().codomain()
    x, y, z, t = R.gens()
    u = x * y * z
    v = x**6 * y**3 + y**6 * z**3 + z**6 * x**3
    w = x**3 * y**6 + y**3 * z**6 + z**3 * x**6
    X, Y, Z = halphen_coords(x, y, z)
    # (X,Y,Z) can be expressed from u,v,w
    assert X == v - 3 * u**3
    assert Y == w - 3 * u**3
    I = R.ideal(x**3 + y**3 + z**3 - 3 * t * x * y * z)
    assert I.reduce(3 * t * Z) == I.reduce(
        (3 * t * u) ** 3 - 3 * v - 3 * w - 9 * u**3
    )
    # (X,Y,Z) is an endomorphism of each curve
    I = R.ideal(x**3 + y**3 + z**3 - 3 * t * x * y * z)
    assert I.reduce(X**3 + Y**3 + Z**3 - 3 * t * X * Y * Z) == 0


def test_halphen_coordinates2():
    P = P2()
    R = P.coordinate_ring()
    R = R["t"].flattening_morphism().codomain()
    x, y, z, t = R.gens()
    u = x * y * z
    v = x**2 * y + y**2 * z + z**2 * x
    w = x * y**2 + y * z**2 + z * x**2
    X, Y, Z = halphen_coords(x, y, z)
    # (X,Y,Z) can be expressed from u,v,w
    assert X == v**3 - 3 * u * v * w
    assert Y == w**3 - 3 * u * v * w
    I = R.ideal(x**3 + y**3 + z**3 - 3 * t * x * y * z)
    assert I.reduce(Z) == I.reduce(3 * (t + 1) * u * v * w - v**3 - w**3)
    assert I.reduce(Z) == I.reduce(9 * (t**2 + t + 1) * u**3 - 3 * u * v * w)


def test_ramification_deg():
    "E1 intersects dual(E2) in 18 points"
    P = P2()
    R = P.coordinate_ring()
    for t1 in range(10, 20):
        for t2 in range(30, 40):
            I = P.subscheme([hesse(R, t1), dual_hesse(R, t2)])
            assert I.degree() == 18


def test_ramification_quot():
    P = P2()
    R = P.coordinate_ring()
    X, Y, Z = halphen_coords(*R.gens())

    for t1 in range(10, 20):
        for t2 in range(30, 40):
            I = R.ideal(hesse(R, t1), dual_hesse(R, t2))
            tau = t2**4 + 6 * t1 * t2**2 + t1**2 - 4 * t2
            ram = (X + Y) * (4 * t1**2 * t2**3 - tau) - Z * (
                tau * t1 - 4 * t1**3 + 4 - 4 * t2**3
            )
            assert I.reduce(ram) == 0


def test_twisted_duals():
    j = QQ["j"].gen()
    Qj = QQ.extension(j**2 + j + 1, names=["j"])
    j = Qj.gen()
    R = Qj["t", "x", "y", "z"]
    t, x, y, z = R.gens()
    E = x**3 + y**3 + z**3 - 3 * t * x * y * z

    # Dual 0
    # (x, y, z) /\ (x, jy, jjz)
    u = (j * j - j) * (y * z)
    v = (1 - j * j) * (z * x)
    w = (j - 1) * (x * y)
    # fmt:off
    D = 3*t*u**2*v**2*w**2 - u**3*v**3 - u**3*w**3 - v**3*w**3
    # fmt:on
    assert R.ideal(E).reduce(D) == 0

    # Dual 1
    # (x, y, z) /\ (z, jx, jjy)
    u = j * j * y * y - j * x * z
    v = z * z - j * j * x * y
    w = j * x * x - y * z
    # fmt:off
    D = (u**6+v**6+w**6) \
        + (3*j*t-1)*(u**3*v**3 + v**3*w**3+w**3*u**3) \
        - 3*j*(j*t+1)*(u**4*v*w+v**4*w*u+w**4*u*v) \
        + (3*j*u*v*w)**2
    # fmt:on
    assert R.ideal(E).reduce(D) == 0

    # Dual 2
    # (x, y, z) /\ (z, j²x, jy)
    u = j * y * y - j * j * x * z
    v = z * z - j * x * y
    w = j * j * x * x - y * z
    # fmt:off
    D = (u**6+v**6+w**6) \
        + (3*j**2*t-1)*(u**3*v**3 + v**3*w**3+w**3*u**3) \
        - 3*j**2*(j**2*t+1)*(u**4*v*w+v**4*w*u+w**4*u*v) \
        + (3*j**2*u*v*w)**2
    # fmt:on
    assert R.ideal(E).reduce(D) == 0

    # Dual 3
    # (x, y, z) /\ (y, z, x)
    u = x * y - z * z
    v = y * z - x * x
    w = z * x - y * y
    # fmt:off
    D = (u**6+v**6+w**6) \
        + (3*t-1)*(u**3*v**3 + v**3*w**3+w**3*u**3) \
        - 3*(t+1)*(u**4*v*w+v**4*w*u+w**4*u*v) \
        + (3*u*v*w)**2
    # fmt:on
    assert R.ideal(E).reduce(D) == 0


def test_double_points():
    "Test coordinates of the double points"
    j = QQ["j"].gen()
    Qj = QQ.extension(j**2 + j + 1, names=["j"])
    j = Qj.gen()
    R = Qj["t1", "t2", "x", "y", "z"]
    t1, t2, x, y, z = R.gens()

    E = x**3 + y**3 + z**3 - 3 * t1 * x * y * z
    # fmt:off
    u, v, w = x, y, z
    t = t2
    D0 = 3*t*u**2*v**2*w**2 - u**3*v**3 - u**3*w**3 - v**3*w**3
    D1 = (u**6+v**6+w**6) \
        + (3*j*t-1)*(u**3*v**3 + v**3*w**3+w**3*u**3) \
        - 3*j*(j*t+1)*(u**4*v*w+v**4*w*u+w**4*u*v) \
        + (3*j*u*v*w)**2
    D2 = (u**6+v**6+w**6) \
        + (3*j**2*t-1)*(u**3*v**3 + v**3*w**3+w**3*u**3) \
        - 3*j**2*(j**2*t+1)*(u**4*v*w+v**4*w*u+w**4*u*v) \
        + (3*j**2*u*v*w)**2
    D3 = (u**6+v**6+w**6) \
        + (3*t-1)*(u**3*v**3 + v**3*w**3+w**3*u**3) \
        - 3*(t+1)*(u**4*v*w+v**4*w*u+w**4*u*v) \
        + (3*u*v*w)**2
    # fmt:on

    X, Y, Z = halphen_coords(x, y, z)
    V = X + Y + t1 * Z

    # Z/(X+Y+t1*Z) == n0/d0
    n0, d0 = t1**2 - t2, t1**3 - 1
    assert R.ideal([E, D0]).reduce(n0 * V - d0 * Z) == 0
    n1, d1 = t1 * t2 - 1, (t1 - 1) * (t1 - j**2) * (t2 - j**2)
    assert R.ideal([E, D1]).reduce(n1 * V - d1 * Z) == 0
    n2, d2 = t1 * t2 - 1, (t1 - 1) * (t1 - j) * (t2 - j)
    assert R.ideal([E, D2]).reduce(n2 * V - d2 * Z) == 0
    n3, d3 = t1 * t2 - 1, (t2 - 1) * (t1 - j) * (t1 - j**2)
    assert R.ideal([E, D3]).reduce(n3 * V - d3 * Z) == 0

    # Extra identities
    assert j * d1 == j * t1 * (t1 * t2 - 1) - (t1**2 - j**2 * t1 * t2 - t2 + j**2)
    assert j**2 * d2 == j**2 * t1 * (t1 * t2 - 1) - (t1**2 - j * t1 * t2 - t2 + j)
    assert d3 == t1 * (t1 * t2 - 1) - (t1**2 - t1 * t2 - t2 + 1)

def test_polarity_quot():
    "Verifies formulas for the quotient projective transformation"
    R = ZZ["x1", "y1", "z1", "x2", "y2", "z2", "t1", "t2"]
    x1, y1, z1, x2, y2, z2, t1, t2 = R.gens()
    E1 = hesse(QQ[x1, y1, z1], t1)
    E2 = hesse(QQ[x2, y2, z2], t2)
    I = R.ideal(E1, E2, x1 * x2 + y1 * y2 + z1 * z2)

    xA, yA, zA = halphen_coords(x1, y1, z1)
    xB, yB, zB = halphen_coords(x2, y2, z2)

    # fmt:off
    m00 = 3*t1**3*t2**3 - 3*t1**2*t2**2 - 2*t1**3 - 2*t2**3 + 3*t1*t2 + 1
    m01 = -3*t1**2*t2**2 + t1**3 + t2**3 + 3*t1*t2 - 2
    m02 = -3*t1**3*t2**2 + t1**4 + t1*t2**3 + 3*t1**2*t2 - 2*t1
    m20 = -3*t1**2*t2**3 + t2**4 + t1**3*t2 + 3*t1*t2**2 - 2*t2
    m22 = t1**4*t2 + t1*t2**4 + 3*t1**2*t2**2 - 3*t1**3 - 3*t2**3 - 2*t1*t2 + 3

    M = Matrix(R, [
        [m00, m01, m02],
        [m01, m00, m02],
        [m20, m20, m22],
    ])
    # fmt:on
    pol = vector(R, [xB, yB, zB]) * M * vector(R, [xA, yA, zA])

    # Test on GF(5) (15625 elements)
    A6 = AffineSpace(GF(5), 6)
    for x1, y1, x2, y2, t1, t2 in A6:
        if all(g(x1, y1, 1, x2, y2, 1, t1, t2) == 0 for g in I.gens()):
            assert pol(x1, y1, 1, x2, y2, 1, t1, t2) == 0

    # Check ideal
    assert I.reduce(pol) == 0


def test_sym_polarity():
    # Properties of the symmetrized polarity
    R = ZZ["t1", "t2"]
    t1, t2 = R.gens()
    m00 = (
        3 * t1**3 * t2**3
        - 3 * t1**2 * t2**2
        - 2 * t1**3
        - 2 * t2**3
        + 3 * t1 * t2
        + 1
    )
    m01 = -3 * t1**2 * t2**2 + t1**3 + t2**3 + 3 * t1 * t2 - 2
    m02 = -3 * t1**3 * t2**2 + t1**4 + t1 * t2**3 + 3 * t1**2 * t2 - 2 * t1
    m20 = -3 * t1**2 * t2**3 + t2**4 + t1**3 * t2 + 3 * t1 * t2**2 - 2 * t2
    m22 = (
        t1**4 * t2
        + t1 * t2**4
        + 3 * t1**2 * t2**2
        - 3 * t1**3
        - 3 * t2**3
        - 2 * t1 * t2
        + 3
    )

    M = Matrix(
        R,
        [
            [m00, m01, m02],
            [m01, m00, m02],
            [m20, m20, m22],
        ],
    )
    S = M + M.transpose()
    tau = (t1**3 - 1) * (t2**3 - 1) - (t1 * t2 - 1) ** 3
    S2 = Matrix(
        R,
        [
            [6 * (t1**3 - 1) * (t2**3 - 1) - 2 * tau, -2 * tau, -tau * (t1 + t2)],
            [-2 * tau, 6 * (t1**3 - 1) * (t2**3 - 1) - 2 * tau, -tau * (t1 + t2)],
            [
                -tau * (t1 + t2),
                -tau * (t1 + t2),
                2 * t1**4 * t2
                + 2 * t1 * t2**4
                + 6 * t1**2 * t2**2
                - 6 * t1**3
                - 6 * t2**3
                - 4 * t1 * t2
                + 6,
            ],
        ],
    )
    assert S == S2


def test_normalize():
    K = GF(379)
    j = K(327)
    assert j**3 == 1
    E = EllipticCurve(GF(379), [0, 378, 0, 152, 94])
    T1, T2 = E(138, 322), E(166, 60)
    assert 3 * T1 == 0 and 3 * T2 == 0 and T1 not in (T2, 2 * T2)
    # Compute t
    xT1 = T1[0]
    xT2 = T2[0]
    xT12 = (T1 - T2)[0]  # FIXME?????
    # t = (-j-2)*(T12-T2)/(T12-T1) - 1
    t = (-j - 2) * (xT12 - xT2) / (xT12 - xT1) + 1
    R = K["x", "y", "z"]
    Eh = EllipticCurve_from_cubic(hesse(R, t), P=(1, -1, 0), morphism=False)
    print(E.j_invariant())
    print(Eh.j_invariant())
    j_formula = ((3 * t * (t**3 + 8)) / (t**3 - 1)) ** 3
    assert Eh.j_invariant() == j_formula
    assert Eh.j_invariant() == E.j_invariant()

    a1, a2, a3, a4, a6 = E.a_invariants()
    assert a1 == 0 and a3 == 0
    Rt = K["t"]
    x = Rt.gen()
    a = (xT1 - xT2) * (1 / t - 1)
    b = xT2 - a
    assert a / (1 - t) + b == xT1
    assert a * 1 + b == xT2
    P = (a * x + b) ** 3 + a2 * (a * x + b) ** 2 + a4 * (a * x + b) + a6
    Pm = P.monic()
    Ep = EllipticCurve(K, [0, Pm[2], 0, Pm[1], Pm[0]])
    print(Ep.j_invariant())
    assert Ep.j_invariant() == E.j_invariant()


def test_hesse_to_weierstrass():
    R = QQ["t", "x", "y", "z"]
    t, x, y, z = R.gens()
    E = x**3 + y**3 + z**3 - 3 * t * x * y * z

    # fmt:off
    u = z
    v = x-y
    w = x+y+t*z

    W = 3*v**2*w - (4*(t**3-1)*u**3 - 9*t**2*u**2*w + 6*t*u*w**2 - w**3)
    # fmt:on
    assert R.ideal(E).reduce(W) == 0


if __name__ == "__main__":
    import pytest

    pytest.main(["-v", __file__])
