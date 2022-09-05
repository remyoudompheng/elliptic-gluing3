from sage.all import (
    Curve,
    EllipticCurve,
    EllipticCurve_from_cubic,
    GF,
)
from testutils import make_curve, torsion_basis

from gluing3 import triple_cover, make_morphism


def random_curve():
    "Returns curves with rational 3-torsion"
    K = GF(4099)  # 3k+1
    while True:
        a = K.random_element()
        b = K.random_element()
        if 4 * a**3 + 27 * b**2 == 0:
            continue
        E = EllipticCurve(K, [a, b])
        try:
            T1, T2 = torsion_basis(E)
            return E, T1, T2
        except ValueError:
            continue


def random_point(H):
    K = H.base_ring()
    while True:
        x = K.random_element()
        if H(x).is_square():
            return (x, H(x).sqrt())


def main():
    from sage.all import timeit

    # Example from equation.sage
    K = GF(2011)
    E1 = EllipticCurve(K, [0, -20, 0, 696, -232])
    T11, T12 = torsion_basis(E1)
    E2 = EllipticCurve(K, [0, 674 * 2, 0, 441 * 4, -147 * 8])
    T21, T22 = torsion_basis(E2)

    print(f"=== {K} ===")
    triple_cover(E1, T11, T12, E2, T21, T22)

    # SIKE-like
    p = 2**110 * 3**67 - 1
    K = GF(p**2)
    print(f"=== {K} ===")
    E = EllipticCurve(K, [0, 1])
    E1 = E.isogenies_prime_degree(13)[1].codomain()
    E2 = E.isogenies_prime_degree(17)[1].codomain()
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)

    print("curves are ready.")
    triple_cover(E1, T11, T12, E2, T21, T22)


def stress():
    from tqdm import trange, tqdm

    data = []
    print("Generate data")
    for i in trange(100):
        E1, T11, T12 = random_curve()
        E2, T21, T22 = random_curve()
        data.append([E1, T11, T12, E2, T21, T22])
    print("Compute triple covers")
    for args in tqdm(data):
        E1, T11, T12, E2, T21, T22 = args
        H, f1, f2 = triple_cover(E1, T11, T12, E2, T21, T22)
        for _ in range(40):
            xH, yH = random_point(H)
            if H(xH) == 0:
                continue  # weierstrass points go to infinity
            assert f1(xH, yH) in E1
            assert f2(xH, yH) in E2


def dorandom(q):
    K = GF(q)
    t1, t2 = 1, 1
    while t1**3 == 1 or t1 == 0:
        t1 = K.random_element()
    while t2**3 == 1 or t2 == 0:
        t2 = K.random_element()
    compute(t1, t2)


def compute(t1, t2):
    K = t1.parent()
    R = K["x", "y", "z"]
    x, y, z = R.gens()
    E1 = make_curve(t1)
    E2 = make_curve(t2)
    print(E1)
    print(E2)
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)
    H, f1, f2 = triple_cover(E1, T11, T12, E2, T21, T22)
    print(H)
    print("=== First projection ===")
    p1 = make_morphism(H, f1)
    print(p1)
    print(p1.image())
    print("=== Second projection ===")
    p2 = make_morphism(H, f2)
    print(p2)
    print(p2.image())


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
        try:
            H, f1, f2 = triple_cover(E1, T11, T12, E2, T21, T22)
            validate_morphisms(H, f1, f2, E1, E2, checks=100)
            print(f"GF({q}) t1={t1} t2={t2}", "OK")
        except ValueError as e:
            print(f"GF({q}) t1={t1} t2={t2}", e)


def triple():
    K = GF(13)
    R = K["x", "y", "z"]
    x, y, z = R.gens()
    E1 = EllipticCurve(K, [7, 0])
    E2 = EllipticCurve(K, [0, 3])
    print(E1)
    print(E2)
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)
    H, f1, f2 = triple_cover(E1, T11, T12, E2, T21, T22)
    print(H)
    print("=== First projection ===")
    p1 = make_morphism(H, f1)
    print(p1)
    print(p1.image())
    print("=== Second projection ===")
    p2 = make_morphism(H, f2)
    print(p2)
    print(p2.image())


if __name__ == "__main__":
    import sys

    match sys.argv[1:]:
        case ["stress", *_]:
            stress()
        case ["random", q, *_]:
            dorandom(int(q))
        case ["testrandom", q, *_]:
            _test_random(int(q))
        case ["triple"]:
            triple()
        case _:
            main()
