from itertools import combinations, product
from math import comb, gcd
from collections import Counter, defaultdict


def antichain(w, a, b):
    rows = [i + 1 for i in range(a) if w[i]]
    cols = [j + 1 for j in range(b) if not w[a + j]]
    return tuple(zip(rows, reversed(cols)))


def encode(A, a, b):
    return tuple(int(any(p == i for p, q in A)) for i in range(1, a + 1)) + tuple(int(not any(q == j for p, q in A)) for j in range(1, b + 1))


def rowmotion(A, a, b):
    P = tuple(product(range(1, a + 1), range(1, b + 1)))
    C = [u for u in P if not any(u[0] <= v[0] and u[1] <= v[1] for v in A)]
    return tuple(u for u in C if not any(v != u and v[0] <= u[0] and v[1] <= u[1] for v in C))


def words(n, b):
    for S in combinations(range(n), b):
        S = set(S)
        yield tuple(int(i in S) for i in range(n))


def windows(w, a):
    n = len(w)
    return tuple(sum(w[(s + r) % n] for r in range(a)) for s in range(n))


def reconstruct(h, a, b):
    n = a + b
    g = gcd(a, b)
    m = n // g
    if sum(h) != a * b:
        return []
    delta = [h[(s + 1) % n] - h[s] for s in range(n)]
    offsets, choices = [], []
    for c in range(g):
        q = [0]
        for j in range(m):
            q.append(q[-1] + delta[(c + j * a) % n])
        if q[-1] != 0:
            return []
        offsets.append(q[:-1])
        E = [e for e in (0, 1) if all(e + v in (0, 1) for v in q[:-1])]
        if not E:
            return []
        choices.append(E)
    result = []
    for eps in product(*choices):
        w = [0] * n
        for c in range(g):
            for j in range(m):
                w[(c + j * a) % n] = eps[c] + offsets[c][j]
        if sum(w) == b:
            result.append(tuple(w))
    return result


def mobius(n):
    factors = 0
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            factors += 1
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        factors += 1
    return (-1) ** factors


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


checked = 0
for a, b in product(range(2, 7), repeat=2):
    n = a + b
    buckets = defaultdict(list)
    periods = Counter()
    for w in words(n, b):
        A = antichain(w, a, b)
        R = rowmotion(A, a, b)
        assert encode(R, a, b) == w[-1:] + w[:-1], (a, b, w, A, R)
        F = lambda B: sum(a*b+a+b-b*i-a*j for i, j in B)
        assert F(R) - F(A) == a*b - n*len(A)
        L = next(l for l in range(1, n + 1) if all(w[i] == w[(i - l) % n] for i in range(n)))
        periods[L] += 1
        buckets[windows(w, a)].append(w)
        checked += 1
    g = gcd(a, b)
    assert set(periods) == {n // d for d in divisors(g)}
    for d in divisors(g):
        L = n // d
        P = sum(mobius(e) * comb(n // (d*e), b // (d*e)) for e in divisors(g // d))
        assert periods[L] == P
    for h, ws in buckets.items():
        x = ws[0]
        zero = sum(all(x[c + j*g] == 0 for j in range(n // g)) for c in range(g))
        one = sum(all(x[c + j*g] == 1 for j in range(n // g)) for c in range(g))
        assert len(ws) == comb(zero + one, one)
        assert set(reconstruct(h, a, b)) == set(ws)
    if a <= 3 and b <= 3:
        for h in product(range(min(a, b) + 1), repeat=n):
            assert set(reconstruct(h, a, b)) == set(buckets.get(h, []))
    print(f'a={a}, b={b}: {comb(n, b)} states; all assertions passed')

x = tuple(map(int, '01110100'))
y = tuple(map(int, '10111000'))
assert windows(x, 4) == windows(y, 4)
assert all(y != x[t:] + x[:t] for t in range(8))
print('Nonconjugate example:', antichain(x, 4, 4), antichain(y, 4, 4), windows(x, 4))
print(f'Total checked states: {checked}')
