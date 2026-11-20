"""Exact finite checks supplementary to the written proofs; no network access."""

from itertools import combinations
from math import gcd, lcm

from sympy import Poly, cyclotomic_poly, symbols


x = symbols("x")
cache = {}


def powers(n):
    if n not in cache:
        phi = Poly(cyclotomic_poly(n, x), x)
        degree = phi.degree()
        cache[n] = [
            tuple(int(Poly(x**j, x).rem(phi).nth(k)) for k in range(degree))
            for j in range(n)
        ]
    return cache[n]


def determinant_zero(n, u1, v1, u2, v2):
    p = powers(n)
    terms = (
        (1, u1 + v2), (-1, u1), (-1, v2),
        (-1, u2 + v1), (1, u2), (1, v1),
    )
    return all(
        sum(sign * p[index % n][k] for sign, index in terms) == 0
        for k in range(len(p[0]))
    )


cyclic_checks = 0
for n in range(3, 25):
    powers(n)
    for d, e in combinations(range(1, n), 2):
        g = gcd(n, gcd(d, e))
        m = n // g
        for s, t in combinations(range(1, n), 2):
            predicted = len({0, s % m, t % m}) <= 2 or any(
                (a * s) % n == 0 and (a * t) % n == 0
                for a in (d, e, e - d)
            )
            actual = determinant_zero(n, d * s, e * s, d * t, e * t)
            assert actual == predicted, (n, d, e, s, t, actual, predicted)
            cyclic_checks += 1
print("Exact cyclic determinant checks, N=3..24:", cyclic_checks, flush=True)

cover_checks = 0
product_checks = 0
for m, n in ((2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4), (2, 6)):
    modulus = lcm(m, n)
    chars = [
        (a, b) for a in range(m) for b in range(n) if (a, b) != (0, 0)
    ]
    images = set()
    for (a, b), (c, d) in combinations(chars, 2):
        image = frozenset(
            (
                (a * i * (modulus // m) + b * j * (modulus // n)) % modulus,
                (c * i * (modulus // m) + d * j * (modulus // n)) % modulus,
            )
            for i in range(m) for j in range(n)
        )
        images.add(image)
    for image in images:
        sizes = [
            sum(u == 0 for u, v in image),
            sum(v == 0 for u, v in image),
            sum(u == v for u, v in image),
        ]
        good = [(u, v) for u, v in image if u != 0 and v != 0 and u != v]
        is_v4 = len(image) == 4 and all(
            (2 * u) % modulus == 0 and (2 * v) % modulus == 0
            for u, v in image
        )
        assert (not good) == is_v4, (m, n, image)
        assert len(good) == len(image) - sum(sizes) + 2
        cover_checks += 1
        for (u1, v1), (u2, v2) in combinations(image - {(0, 0)}, 2):
            predicted = (
                (u1 == u2 == 0)
                or (v1 == v2 == 0)
                or (u1 == v1 and u2 == v2)
            )
            actual = determinant_zero(modulus, u1, v1, u2, v2)
            assert actual == predicted, (m, n, image, (u1, v1), (u2, v2))
            product_checks += 1
print("Exact subgroup-cover checks on product groups:", cover_checks)
print("Exact determinant checks on product groups:", product_checks)
print("All checks passed. The written proofs do not depend on this computation.")
