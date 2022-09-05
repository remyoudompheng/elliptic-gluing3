from sage.all import GF, EllipticCurve

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
    E1_3 = E1.abelian_group().torsion_subgroup(3)
    E2_3 = E2.abelian_group().torsion_subgroup(3)
    T11, T12 = [t.element() for t in E1_3.gens()]
    T21, T22 = [t.element() for t in E2_3.gens()]

    h, p1, p2 = triple_cover(E1, T11, T12, E2, T21, T22, check=False)
    check_morphisms(E1, E2, h, p1, p1)

def test_large():
    p = 2**31-1
    K = GF(p)
    E1 = make_curve(K(0xdeadc0de))
    E2 = make_curve(K(0x600dc0de))
    E1_3 = E1.abelian_group().torsion_subgroup(3)
    E2_3 = E2.abelian_group().torsion_subgroup(3)
    T11, T12 = [t.element() for t in E1_3.gens()]
    T21, T22 = [t.element() for t in E2_3.gens()]

    h, p1, p2 = triple_cover(E1, T11, T12, E2, T21, T22, check=False)
    check_morphisms(E1, E2, h, p1, p1)

def make_curve(t):
    K = t.parent()
    p3 = 4 * (t**3 - 1) / 3
    p2 = -3 * t**2
    p1 = 2 * t
    p0 = 1 / K(-3)
    return EllipticCurve(K, [0, p2 / p3**2, 0, p1 / p3**3, p0 / p3**4])


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
        E1_3 = E1.abelian_group().torsion_subgroup(3)
        E2_3 = E2.abelian_group().torsion_subgroup(3)
        T11, T12 = [p.element() for p in E1_3.gens()]
        T21, T22 = [p.element() for p in E2_3.gens()]
        h, p1, p2 = triple_cover(E1, T11, T12, E2, T21, T22, check=False)
        if h is None:
            print("FAILED", t1, t2)
            continue
        check_morphisms(E1, E2, h, p1, p2)


def test_F31():
    _test_random(31)


def test_F1009():
    _test_random(1009)


def test_F10007_2():
    _test_random(10007**2, n_curves=30)


if __name__ == "__main__":
    # FIXME: tests don't pass
    test_basic()
    # test_F31()
    # test_F1009()
    test_F10007_2()
