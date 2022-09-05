import time
from sage.all import GF, EllipticCurve

import gluing3
import gluing_bhls


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
    assert T1.weil_pairing(T2, 3) != 1
    return T1, T2


def _bench_curves(E1, T11, T12, E2, T21, T22, n=5):
    print("testing gluing3")
    t0 = time.time()
    for _ in range(10 * n):
        gluing3.triple_cover(E1, T11, T12, E2, T21, T22)
    avg = (time.time() - t0) / (10 * n)
    print(f"{10*n} iters, {avg*100:.1f}ms/iter")

    if E1.base_ring().characteristic() >= 2**31:
        return
    print("testing BHLS")
    try:
        t0 = time.time()
        for _ in range(n):
            gluing_bhls.triple_cover(E1, T11, T12, E2, T21, T22)
        avg = (time.time() - t0) / n
        print(f"{n} iters, {avg*100:.1f}ms/iter")
    except Exception as e:
        print("ERROR", e)


def bench_basic():
    K = GF(4099)
    print(f"=== {K} ===")
    E1 = EllipticCurve(K, [-961, -1125])
    E2 = EllipticCurve(K, [1044, 354])
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)

    print("curves are ready.")
    _bench_curves(E1, T11, T12, E2, T21, T22, n=20)


def bench_sikelike():
    p = 2**12 * 3**5 - 1
    K = GF(p**2)
    print(f"=== {K} ===")
    E = EllipticCurve(K, [0, 1])
    E1 = E.isogenies_prime_degree(7)[0].codomain()
    print("E1:", E1)

    for i, edge in enumerate(E.isogenies_prime_degree(11)[:3]):
        E2 = edge.codomain()
        print("E2:", E2)
        T11, T12 = torsion_basis(E1)
        T21, T22 = torsion_basis(E2)
        _bench_curves(E1, T11, T12, E2, T21, T22, n=10)


def bench_largep():
    p = 2**31 - 1
    K = GF(p)
    print(f"=== {K} ===")
    E = EllipticCurve(K, [0, 1])
    E1 = make_curve(K(0xDEADC0DE))
    E2 = make_curve(K(0xF00D900D))
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)
    _bench_curves(E1, T11, T12, E2, T21, T22, n=10)


def bench_largep2():
    p = 65 * 2**22 - 1
    x = GF(p)["x"].gen()
    K = GF(p**2, names="i", modulus=x**2 + 1)
    print(f"=== {K} ===")
    E = EllipticCurve(K, [0, 1])
    E1 = E.isogenies_prime_degree(7)[0].codomain()
    T11, T12 = torsion_basis(E1)
    for f2 in E.isogenies_prime_degree(19)[:3]:
        E2 = f2.codomain()
        T21, T22 = torsion_basis(E2)
        print("E2:", E2)
        _bench_curves(E1, T11, T12, E2, T21, T22, n=5)


def bench_bigp():
    p = 2**109 * 3**64 + 1
    K = GF(p)
    print(f"=== {K} ===")
    E = EllipticCurve(K, [0, 1])
    E1 = make_curve(K(7) ** 0xDEADC0DE)
    E2 = make_curve(K(11) ** 0xF00D900D)
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)
    _bench_curves(E1, T11, T12, E2, T21, T22, n=10)


def bench_bigp2():
    p = 2**110 * 3**67 - 1
    x = GF(p)["x"].gen()
    K = GF(p**2, names="i", modulus=x**2 + 1)
    print(f"=== {K} ===")
    E = EllipticCurve(K, [0, 1])
    E1 = E.isogenies_prime_degree(7)[0].codomain()
    E2 = E.isogenies_prime_degree(11)[0].codomain()
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)
    _bench_curves(E1, T11, T12, E2, T21, T22, n=10)


def bench_verybigp():
    p = 2**372 * 3**236 + 1
    K = GF(p)
    print("=== GF(2^372*3^236 + 1) ===")
    E = EllipticCurve(K, [0, 1])
    E1 = make_curve(K(7) ** 0xDEADC0DE)
    E2 = make_curve(K(11) ** 0xF00D900D)
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)
    _bench_curves(E1, T11, T12, E2, T21, T22, n=5)


def bench_verybigp2():
    p = 2**372 * 3**239 - 1
    x = GF(p)["x"].gen()
    K = GF(p**2, names="i", modulus=x**2 + 1)
    print("=== GF((2^372*3^239-1)^2) ===")
    E = EllipticCurve(K, [0, 1])
    E1 = E.isogenies_prime_degree(7)[0].codomain()
    E2 = E.isogenies_prime_degree(11)[0].codomain()
    T11, T12 = torsion_basis(E1)
    T21, T22 = torsion_basis(E2)
    _bench_curves(E1, T11, T12, E2, T21, T22, n=2)


if __name__ == "__main__":
    import cProfile

    with cProfile.Profile() as pr:
        bench_basic()
        bench_sikelike()
        bench_largep()
        bench_largep2()
        bench_bigp()
        bench_bigp2()
        bench_verybigp()
        bench_verybigp2()
        pr.dump_stats("bench.prof")
