import time
from sage.all import GF, EllipticCurve
from sage.misc.sage_timeit import sage_timeit

from testutils import make_curve, torsion_basis
import gluing3
import gluing_bhls


def _bench_field(K):
    # Field ops benchmark
    x1 = K.random_element()
    x2 = K.random_element()**2
    tsmul = sage_timeit('x1*x2', {"x1": x1, "x2": x2}, preparse=False)
    tsqrt = sage_timeit('x2.sqrt()', {"x1": x1, "x2": x2}, preparse=False)
    print(f"mul: {tsmul}, sqrt: {tsqrt}")

def _bench_curves(E1, T11, T12, E2, T21, T22, n=5):
    print("testing gluing3")
    t0 = time.time()
    for _ in range(10 * n):
        gluing3.triple_cover(E1, T11, T12, E2, T21, T22)
    avg = (time.time() - t0) / (10 * n)
    print(f"{10*n} iters, {avg*1000:.1f}ms/iter")

    K = E1.base_ring()
    if K.degree() > 1 and K.characteristic() >= 2**29:
        print("skip BHLS")
        return
    if K.characteristic() >= 2**31:
        n = 1
    print("testing BHLS")
    t0 = time.time()
    for _ in range(n):
        gluing_bhls.triple_cover(E1, T11, T12, E2, T21, T22)
    avg = (time.time() - t0) / n
    print(f"{n} iters, {avg*1000:.1f}ms/iter")


def bench_basic():
    K = GF(4099)
    print(f"=== {K} ===")
    _bench_field(K)
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
    _bench_field(K)
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
    _bench_field(K)
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
    _bench_field(K)
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
    _bench_field(K)
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
    _bench_field(K)
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
    _bench_field(K)
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
    _bench_field(K)
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
