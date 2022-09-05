from sage.all import proof, EllipticCurve, GF, Integer
from testutils import make_curve, torsion_basis
from gluing_paper import triple_cover

proof.arithmetic(False)


def validate_morphisms(H, f1, f2, E1, E2, checks=1000):
    P1 = E1.defining_polynomial()
    P2 = E2.defining_polynomial()
    K = H.base_ring()
    ok = 0
    if K.order() < checks:
        elems = list(K)
    else:
        elems = [K.random_element() for _ in range(checks)]
    for xH in elems:
        if H(xH) != 0 and H(xH).is_square():
            yH = H(xH).sqrt()
            x1, y1 = f1(xH, yH)
            assert P1(x1, y1, 1) == 0
            x2, y2 = f2(xH, yH)
            assert P2(x2, y2, 1) == 0
        ok += 1
    assert ok > len(elems) // 3


def _test_small_field(q):
    K = GF(q)
    elems = [t for t in K if t**3 != 1]
    for i, t1 in enumerate(elems):
        for t2 in elems[: i + 1]:
            E1 = make_curve(t1)
            E2 = make_curve(t2)
            T11, T12 = torsion_basis(E1)
            T21, T22 = torsion_basis(E2)
            H, f1, f2 = triple_cover(E1, T11, T12, E2, T21, T22)
            if f1 is not None:
                validate_morphisms(H, f1, f2, E1, E2)
                print(f"GF({q}) t1={t1} t2={t2}", "OK")
            else:
                print(f"GF({q}) t1={t1} t2={t2}", H)


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
        H, f1, f2 = triple_cover(E1, T11, T12, E2, T21, T22)
        if f1 is not None:
            validate_morphisms(H, f1, f2, E1, E2, checks=100)
            print(f"GF({q}) t1={t1} t2={t2}", "OK")
        else:
            print(f"GF({q}) t1={t1} t2={t2}", H)


def test_F7():
    _test_small_field(7)


def test_F13():
    _test_small_field(13)


def test_F19():
    _test_small_field(19)


def test_F25():
    _test_random(25)


def test_F31():
    _test_random(31)


def test_F1009():
    _test_random(1009)


def test_F10007_2():
    _test_random(10007**2, n_curves=30)


if __name__ == "__main__":
    test_F7()
    test_F13()
    test_F19()
    test_F25()
    test_F31()
    # for q in range(37, 100, 3):
    for q in range(67, 200, 3):
        if q % 2 == 1 and Integer(q).is_prime_power():
            _test_small_field(q)

    test_F1009()
    test_F10007_2()
