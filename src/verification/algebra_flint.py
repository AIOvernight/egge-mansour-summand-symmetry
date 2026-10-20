#!/usr/bin/env python3
"""Exact generic algebra audit using FLINT multivariate integer polynomials.

The rational-function identities follow the independent reviewer oracle
review_symbolic.py; this implementation adds a native FLINT backend,
parallel permutations, repeated-node specialization, and the t=k negative control.
"""

import argparse
from concurrent.futures import ProcessPoolExecutor
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
import time
import flint
from flint import fmpz_mpoly_ctx

CTX = None


class Rat:
    def __init__(self, n=0, d=1):
        n = CTX.constant(n) if isinstance(n, int) else n
        d = CTX.constant(d) if isinstance(d, int) else d
        assert d
        if not n:
            self.n, self.d = CTX.constant(0), CTX.constant(1)
            return
        g = n.gcd(d)
        n = n // g
        d = d // g
        if d.leading_coefficient() < 0:
            n = -n
            d = -d
        self.n, self.d = n, d

    @staticmethod
    def coerce(a):
        return a if isinstance(a, Rat) else Rat(a)

    def __add__(a, b):
        b = Rat.coerce(b)
        return Rat(a.n * b.d + b.n * a.d, a.d * b.d)

    __radd__ = __add__

    def __neg__(a):
        return Rat(-a.n, a.d)

    def __sub__(a, b):
        return a + -Rat.coerce(b)

    def __rsub__(a, b):
        return Rat.coerce(b) + -a

    def __mul__(a, b):
        b = Rat.coerce(b)
        return Rat(a.n * b.n, a.d * b.d)

    __rmul__ = __mul__

    def __truediv__(a, b):
        b = Rat.coerce(b)
        return Rat(a.n * b.d, a.d * b.n)

    def __rtruediv__(a, b):
        return Rat.coerce(b) / a

    def __pow__(a, k):
        return Rat(a.n**k, a.d**k)

    def __eq__(a, b):
        b = Rat.coerce(b)
        return a.n == b.n and a.d == b.d

    def compose(a, values):
        return Rat(a.n.compose(*values), a.d.compose(*values))


def configure(k):
    global CTX
    CTX = fmpz_mpoly_ctx.get(["q", "s"] + ["c%d" % i for i in range(k)], "lex")
    return [Rat(g) for g in CTX.gens()]


def recurrence(c, q, s):
    k = len(c)
    r = [[Rat() for _ in c] for _ in c]
    for i in range(k):
        r[i][i] = c[i]
    for d in range(1, k):
        for i in range(k - d):
            j = i + d
            v = c[i] + (1 - s * c[i]) * r[i + 1][j]
            for z in range(i + 1, j):
                v += q * c[i] * r[i][z] * (r[z][j] - r[z + 1][j])
            r[i][j] = v / (1 - q * c[i] * c[j])
    return r


def mm(a, b):
    k = len(a)
    return [
        [sum((a[i][t] * b[t][j] for t in range(k)), Rat()) for j in range(k)]
        for i in range(k)
    ]


def sub(a, b, c=1):
    return [[x - c * y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def identities(k):
    start = time.monotonic()
    q, s, *cs = configure(k)
    z = Rat()
    one = Rat(1)
    r = recurrence(cs, q, s)
    eye = [[one if i == j else z for j in range(k)] for i in range(k)]
    e = [
        [one if i == j else -one if j == i + 1 else z for j in range(k)]
        for i in range(k)
    ]
    einv = [[one if i <= j else z for j in range(k)] for i in range(k)]
    alpha = [1 / c + q * c for c in cs]
    a = [
        [alpha[i] if i == j else s - alpha[i] if j == i + 1 else z for j in range(k)]
        for i in range(k)
    ]
    w = mm(r, e)
    assert sub(mm(a, r), mm(mm(r, e), r), q) == einv
    assert sub(mm(a, w), mm(w, w), q) == eye
    assert mm(a, w) == mm(w, a)
    value = z
    pA = [[z for _ in cs] for _ in cs]
    for i in range(k):
        term = cs[i]
        matrix = [[cs[i] * x for x in row] for row in eye]
        for j in range(k):
            if i != j:
                term *= (s - alpha[j]) / (alpha[i] - alpha[j])
                matrix = mm(matrix, sub(a, eye, alpha[j]))
                matrix = [[x / (alpha[i] - alpha[j]) for x in row] for row in matrix]
        value += term
        pA = sub(pA, matrix, -one)
    assert value == r[0][-1]
    assert pA == w
    at = eye
    for t in range(k):
        assert sum(at[0], z) == s**t
        at = mm(at, a)
    assert sum(at[0], z) != s**k
    allowed = [(1 - q * cs[i] * cs[j]).n for i in range(k) for j in range(i + 1, k)]
    denominators = []
    for i in range(k):
        for j in range(i, k):
            coeff, factors = r[i][j].d.factor()
            assert abs(coeff) == 1
            for f, power in factors:
                assert any(f == a or f == -a for a in allowed)
            denominators.append(
                {
                    "i": i,
                    "j": j,
                    "factors": [[str(f), int(power)] for f, power in factors],
                }
            )
    repeated = False
    if k in (3, 4):
        vals = list(CTX.gens())
        vals[3] = vals[2]
        reduced = [c.compose(vals) for c in cs]
        direct = recurrence(reduced, q, s)[0][-1]
        assert r[0][-1].compose(vals) == direct
        assert value.compose(vals) == direct
        repeated = True
    report = {
        "kind": "identities",
        "k": k,
        "seconds": time.monotonic() - start,
        "checks": [
            "AR-qRER=E^-1",
            "AW-qW^2=I",
            "AW=WA",
            "W=p(A)",
            "R_1k=p(s)",
            "moments_t<k",
            "moment_t=k_fails",
            "allowed_denominators",
        ],
        "repeated_c1_c0": repeated,
        "denominators": denominators,
        "full_numerator_terms": len(r[0][-1].n),
        "full_denominator_terms": len(r[0][-1].d),
    }
    print("identity k=%d PASS %.3fs" % (k, report["seconds"]), flush=True)
    return report


def orders(task):
    k, chunk, chunks = task
    start = time.monotonic()
    q, s, *cs = configure(k)
    target = recurrence(cs, q, s)[0][-1]
    checked = 0
    for j, p in enumerate(permutations(cs)):
        if j % chunks != chunk:
            continue
        assert recurrence(p, q, s)[0][-1] == target
        checked += 1
    report = {
        "kind": "permutations",
        "k": k,
        "chunk": chunk,
        "orders": checked,
        "seconds": time.monotonic() - start,
    }
    print(
        "orders k=%d chunk=%d PASS n=%d %.3fs" % (k, chunk, checked, report["seconds"]),
        flush=True,
    )
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--max-k", type=int, default=6)
    p.add_argument("--output", required=True)
    p.add_argument("--workers", type=int, default=16)
    args = p.parse_args()
    start = time.monotonic()
    results = []
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        future = [pool.submit(identities, k) for k in range(1, args.max_k + 1)]
        for k in range(1, args.max_k + 1):
            chunks = 16 if k >= 5 else 1
            future.extend(pool.submit(orders, (k, j, chunks)) for j in range(chunks))
        for f in future:
            results.append(f.result())
    for k in range(1, args.max_k + 1):
        import math

        assert sum(
            r.get("orders", 0) for r in results if r["k"] == k
        ) == math.factorial(k)
    report = {
        "status": "PASS",
        "max_k": args.max_k,
        "arithmetic": "exact rational functions over Z[q,s,c0,...] with FLINT polynomial gcd normalization",
        "flint_version": flint.__version__,
        "workers": args.workers,
        "seconds": time.monotonic() - start,
        "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "results": results,
        "gpu_assessment": "native exact multivariate polynomial gcd/factorization; independent CPU tasks; no floating point and no GPU",
    }
    path = Path(args.output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n")
    print("ALL PASS", report["seconds"], flush=True)


if __name__ == "__main__":
    main()
