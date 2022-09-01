from sage.all import (
    Curve,
    EllipticCurve,
    EllipticCurve_from_cubic,
    GF,
)
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
        EG = E.abelian_group()
        invs = EG.invariants()
        if len(invs) == 2 and all(x % 3 == 0 for x in invs):
            T1, T2 = EG.torsion_subgroup(3).gens()
            return E, T1.element(), T2.element()


def random_point(H):
    K = H.base_ring()
    while True:
        x = K.random_element()
        if H(x).is_square():
            return (x, H(x).sqrt())


def main():
    from sage.all import timeit, cached_method

    # Example from equation.sage
    K = GF(2011)
    E1 = EllipticCurve(K, [0, -20, 0, 696, -232])
    T11, T12 = E1.abelian_group().torsion_subgroup(3).gens()
    E2 = EllipticCurve(K, [0, 674 * 2, 0, 441 * 4, -147 * 8])
    T21, T22 = E2.abelian_group().torsion_subgroup(3).gens()

    print(f"=== {K} ===")
    print(
        timeit(
            "triple_cover(E1, T11.element(), T12.element(), E2, T21.element(), T22.element())",
            globals=locals() | globals(),
            number=200,
        )
    )

    # SIKE-like, benchmark
    # p = 2**110 * 3**67 - 1
    p = 2**33 * 3**19 - 1
    K = GF(p**2)
    print(f"=== {K} ===")
    # Speed hack
    type(K).vector_space = cached_method(type(K).vector_space)
    E = EllipticCurve(K, [0, 1])
    E1 = E.isogenies_prime_degree(13)[1].codomain()
    E2 = E.isogenies_prime_degree(17)[1].codomain()
    T11, T12 = E1.abelian_group().torsion_subgroup(3).gens()
    T21, T22 = E2.abelian_group().torsion_subgroup(3).gens()

    print("curves are ready.")
    print(
        timeit(
            "triple_cover(E1, T11.element(), T12.element(), E2, T21.element(), T22.element())",
            globals=locals() | globals(),
            number=20,
        )
    )


def stress():
    from tqdm import trange, tqdm

    data = []
    print("Generate data")
    for i in trange(100):
        E1, T11, T12 = random_curve()
        E2, T21, T22 = random_curve()
        data.append([E1, T11, T12, E2, T21, T22])
    print("Compute triple covers")
    for args in tqdm(data * 100):
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
    E1 = EllipticCurve_from_cubic(
        x**3 + y**3 + z**3 - 3 * t1 * x * y * z, [1, -1, 0]
    )
    E2 = EllipticCurve_from_cubic(
        x**3 + y**3 + z**3 - 3 * t2 * x * y * z, [1, -1, 0]
    )
    E1 = E1.codomain().short_weierstrass_model()
    E2 = E2.codomain().short_weierstrass_model()
    print(E1)
    print(E2)
    E1_3 = E1.abelian_group().torsion_subgroup(3)
    E2_3 = E2.abelian_group().torsion_subgroup(3)
    T11, T12 = [p.element() for p in E1_3.gens()]
    T21, T22 = [p.element() for p in E2_3.gens()]
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

def triple():
    K = GF(13)
    R = K["x", "y", "z"]
    x, y, z = R.gens()
    E1 = EllipticCurve(K, [7, 0])
    E2 = EllipticCurve(K, [0, 3])
    print(E1)
    print(E2)
    E1_3 = E1.abelian_group().torsion_subgroup(3)
    E2_3 = E2.abelian_group().torsion_subgroup(3)
    T11, T12 = [p.element() for p in E1_3.gens()]
    T21, T22 = [p.element() for p in E2_3.gens()]
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
        case ["triple"]:
            triple()
        case _:
            main()
