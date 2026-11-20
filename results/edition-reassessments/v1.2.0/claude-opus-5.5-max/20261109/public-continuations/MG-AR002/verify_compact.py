import itertools as it, random

def rank(rows, p):
    M, r = [list(x) for x in rows], 0
    for c in range(len(M[0]) if M else 0):
        piv = next((i for i in range(r, len(M)) if M[i][c] % p), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p); M[r] = [v * inv % p for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c]; M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        r += 1
    return r

def check(p, n, rows, b, A):
    dot = lambda u, v: sum(x * y for x, y in zip(u, v)) % p
    pts = list(it.product(range(p), repeat=n))
    S = [x for x in pts if all(dot(r, x) == c for r, c in zip(rows, b))]
    if not S: return None
    dW = rank(rows, p); dWU = rank(rows + [[int(k == i) for k in range(n)] for i in A], p)
    beta, ok = {}, True                      # beta(sum c_j a_j) = sum c_j b_j; well-definedness checked
    for c in it.product(range(p), repeat=len(rows)):
        w = tuple(sum(cj * r[i] for cj, r in zip(c, rows)) % p for i in range(n))
        v = sum(cj * bj for cj, bj in zip(c, b)) % p
        ok &= beta.setdefault(w, v) == v
    WU = [w for w in beta if all(w[i] == 0 for i in range(n) if i not in A)]   # W ∩ U_A
    dWcU = rank([list(w) for w in WU], p)
    img = {}
    for x in S: img.setdefault(tuple(x[i] for i in A), []).append(x)
    ys = list(it.product(range(p), repeat=len(A)))
    ev = lambda w, y: sum(w[i] * t for i, t in zip(A, y)) % p
    ok &= len(S) == p ** (n - dW) and len(img) == p ** (dWU - dW)               # S2
    ok &= all(len(f) == p ** (n - dWU) for f in img.values()) and dWU == dW + len(A) - dWcU
    ok &= all((y in img) == all(ev(w, y) == beta[w] for w in WU) for y in ys)  # S1 / S4 image
    inj, surj = all(len(f) == 1 for f in img.values()), len(img) == p ** len(A)
    ok &= inj == (dWU == n) and surj == (dWcU == 0)                             # S4 table
    basis = []
    for w in WU:
        if rank([list(u) for u in basis + [w]], p) > len(basis): basis.append(w)
    for mu in range(len(basis)):                                                # S6 non-redundancy
        ok &= any(ev(basis[mu], y) != beta[basis[mu]] and
                  all(ev(w, y) == beta[w] for l, w in enumerate(basis) if l != mu) for y in ys)
    img0 = {tuple(x[i] for i in A) for x in pts if all(dot(r, x) == 0 for r in rows)}
    ok &= img0 == {y for y in ys if all(ev(w, y) == 0 for w in WU)}             # pi_A(W^perp) = (W∩U_A)^perp
    return ok, inj, surj

def run(p, trials, maxI, maxJ, seed):
    rng, st = random.Random(seed), dict(tests=0, fails=0, inj=0, surj=0)
    while st['tests'] < trials:
        n, m = rng.randint(1, maxI), rng.randint(0, maxJ)
        rows = [[rng.randrange(p) for _ in range(n)] for _ in range(m)]
        if m >= 2 and rng.random() < 0.3: rows[1] = list(rows[0])               # force dependent rows
        x0 = [rng.randrange(p) for _ in range(n)]
        b = [sum(a * x for a, x in zip(r, x0)) % p for r in rows]
        if rng.random() < 0.5: b = [rng.randrange(p) for _ in rows]             # random rhs, kept if consistent
        res = check(p, n, rows, b, [i for i in range(n) if rng.random() < 0.5])
        if res is None: continue
        st['tests'] += 1; st['fails'] += not res[0]; st['inj'] += res[1]; st['surj'] += res[2]
    return st

for p, trials, mI, mJ in [(2, 3000, 6, 6), (3, 2000, 5, 5), (5, 500, 4, 3)]:
    print('F_%d' % p, run(p, trials, mI, mJ, seed=p))
print('a1=a2=e1, b=(1,1), A={2}: surjective =', check(2, 2, [[1, 0], [1, 0]], [1, 1], [1])[2])
N = 10                                        # S5: rows x1=1, x_{j-1}-x_j=0 restricted to 1..N
rowsS5 = [[int(i == 0) for i in range(N)]] + [[int(i == j - 2) - int(i == j - 1) for i in range(N)] for j in range(2, N + 1)]
bS5 = [1] + [0] * (N - 1)
print('S5 finite subsystems solved by 1_[1,max F]:', all(
    all(sum(a * x for a, x in zip(rowsS5[j - 1], [int(i < max(F, default=0)) for i in range(N)])) == bS5[j - 1] for j in F)
    for m in range(N + 1) for F in it.combinations(range(1, N + 1), m)))
