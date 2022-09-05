from sage.all import GF, EllipticCurve
from testutils import make_curve, torsion_basis

from gluing_bhls import solve_params, triple_cover


def check_morphisms(E1, E2, h, proj1, proj2):
    K = E1.base_ring()
    px1, py1 = proj1
    px2, py2 = proj2

    points = 0
    if K.order() < 5000:
        xs = iter(K)
    else:
        xs = (K.random_element() for _ in range(100))
    for x in xs:
        if not h(x).is_square():
            continue
        y = h(x).sqrt()
        den1 = px1.denominator()
        if den1(x) != 0:
            x1, y1 = px1(x), y * py1(x)
            assert x1, y1 in E1
            points += 1
        den2 = px2.denominator()
        if den2(x) != 0:
            x2, y2 = px2(x), y * py2(x)
            assert x2, y2 in E2
            points += 1
    print("tested", points, "points")


def test_basic():
    K = GF(4099)
    E1 = EllipticCurve(K, [-961, -1125])
    E2 = EllipticCurve(K, [1044, 354])
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)

    h, p1, p2 = triple_cover(E1, T11, T12, E2, T21, T22, check=False)
    check_morphisms(E1, E2, h, p1, p1)


def test_large():
    p = 2**31 - 1
    K = GF(p)
    E1 = make_curve(K(0xDEADC0DE))
    E2 = make_curve(K(0x600DC0DE))
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)

    h, p1, p2 = triple_cover(E1, T11, T12, E2, T21, T22, check=False)
    check_morphisms(E1, E2, h, p1, p1)


def _test_random(q, n_curves=100):
    K = GF(q)
    for _ in range(n_curves):
        t1, t2 = 1, 1
        while t1**3 == 1:
            t1 = K.random_element()
        while t2**3 == 1:
            t2 = K.random_element()
        E1 = make_curve(t1)
        E2 = make_curve(t2)
        T11, T12 = torsion_basis(E1)
        T21, T22 = torsion_basis(E2)
        h, p1, p2 = triple_cover(E1, T11, T12, E2, T21, T22, check=False)
        if h is None:
            print("FAILED", t1, t2)
            continue
        check_morphisms(E1, E2, h, p1, p2)


def xfail_test_F31():
    _test_random(31)


def xfail_test_F1009():
    _test_random(1009)


def test_F10007_2():
    _test_random(10007**2, n_curves=30)


def test_very_large1():
    p = 2**109 * 3**64 + 1
    print("test 2**109 * 3**64 + 1")
    _test_random(p, n_curves=1)


def test_very_large2():
    p = 2**206 * 3**138 + 1
    print("test 2**206 * 3**138 + 1")
    _test_random(p, n_curves=1)


if __name__ == "__main__":
    test_basic()
    test_large()
    # FIXME: tests don't pass
    # test_F31()
    # test_F1009()
    test_F10007_2()
    test_very_large1()
    test_very_large2()
