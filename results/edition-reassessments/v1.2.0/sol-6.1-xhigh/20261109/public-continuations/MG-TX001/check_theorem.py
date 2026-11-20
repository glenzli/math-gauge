from itertools import combinations
from math import comb
from time import monotonic


def balanced(a, p, r):
    for level in range(1, r + 1):
        q = p ** level
        counts = [0] * q
        for x in a:
            counts[x % q] += 1
        if max(counts) - min(counts) > 1:
            return False
    return True


def det_is_zero(a, b, p, r):
    """Exact determinant at a primitive p**r root, using integer polynomials."""
    n = p ** r
    k = len(a)
    states = {0: [1] + [0] * (n - 1)}
    for row in range(k):
        next_states = {}
        for mask, coeffs in states.items():
            for j, exponent in enumerate(a):
                if mask & (1 << j):
                    continue
                new_mask = mask | (1 << j)
                out = next_states.setdefault(new_mask, [0] * n)
                sign = -1 if (mask >> (j + 1)).bit_count() % 2 else 1
                shift = b[row] * exponent % n
                for degree, value in enumerate(coeffs):
                    out[(degree + shift) % n] += sign * value
        states = next_states
    coeffs = states[(1 << k) - 1]
    step = n // p
    return all(
        coeffs[t + j * step] == coeffs[t]
        for t in range(step)
        for j in range(1, p)
    )


def vp(x, p):
    value = 0
    while x % p == 0:
        x //= p
        value += 1
    return value


start = monotonic()
for p, r in [(2, 2), (2, 3), (3, 2)]:
    n = p ** r
    minors = 0
    for k in range(1, n + 1):
        subsets = list(combinations(range(n), k))
        for a in subsets:
            expected = balanced(a, p, r)
            any_zero = False
            for b in subsets:
                zero = det_is_zero(a, b, p, r)
                minors += 1
                if zero:
                    any_zero = True
                assert not (expected and zero), (p, r, a, b)
            assert expected == (not any_zero), (p, r, a)
    print(f'N={n}: all {minors} square minors checked exactly', flush=True)

for p, r in [(2, 4), (3, 2)]:
    n = p ** r
    supports = 0
    for k in range(1, n + 1):
        denominator_v = sum(vp(j - i, p) for i in range(k) for j in range(i + 1, k))
        for a in combinations(range(n), k):
            numerator_v = sum(vp(y - x, p) for x, y in combinations(a, 2))
            assert numerator_v >= denominator_v
            assert balanced(a, p, r) == (numerator_v == denominator_v), (p, r, a)
            supports += 1
    print(f'N={n}: balance/valuation equivalence checked for {supports} supports', flush=True)

print(f'All exact checks passed in {monotonic() - start:.2f}s', flush=True)
