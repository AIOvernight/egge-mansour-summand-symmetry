#!/usr/bin/env python3
"""Exact rational-function audit of the generic recurrence for k<=4."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
import time
from sympy import QQ, symbols, factor_list, cancel
from sympy.polys.fields import field


def verify(k):
    start = time.monotonic()
    ff, q, s, *cs = field('q,s,' + ','.join('c%d' % i for i in range(k)), QQ)
    zero, one = ff.zero, ff.one

    def recurrence(c):
        r = [[zero for _ in c] for _ in c]
        for i in range(k):
            r[i][i] = c[i]
        for d in range(1, k):
            for i in range(k - d):
                j = i + d
                value = c[i] + (1 - s * c[i]) * r[i + 1][j]
                for z in range(i + 1, j):
                    value += q * c[i] * r[i][z] * (r[z][j] - r[z + 1][j])
                r[i][j] = value / (1 - q * c[i] * c[j])
        return r

    def mm(a, b):
        return [[sum((a[i][t] * b[t][j] for t in range(k)), zero)
                 for j in range(k)] for i in range(k)]

    def sub(a, b, coeff=one):
        return [[a[i][j] - coeff * b[i][j] for j in range(k)] for i in range(k)]

    r = recurrence(cs)
    eye = [[one if i == j else zero for j in range(k)] for i in range(k)]
    e = [[(one if i == j else -one if j == i + 1 else zero)
          for j in range(k)] for i in range(k)]
    einv = [[one if i <= j else zero for j in range(k)] for i in range(k)]
    alpha = [1 / c + q * c for c in cs]
    a = [[(alpha[i] if i == j else s - alpha[i] if j == i + 1 else zero)
          for j in range(k)] for i in range(k)]
    w = mm(r, e)
    assert sub(mm(a, r), mm(mm(r, e), r), q) == einv
    assert sub(mm(a, w), mm(w, w), q) == eye
    assert mm(a, w) == mm(w, a)

    interpolation = zero
    matrix_interpolation = [[zero for _ in cs] for _ in cs]
    for i in range(k):
        term = cs[i]
        matrix_term = [[cs[i] * x for x in row] for row in eye]
        for j in range(k):
            if i != j:
                term *= (s - alpha[j]) / (alpha[i] - alpha[j])
                matrix_term = mm(matrix_term, sub(a, eye, alpha[j]))
                matrix_term = [[x / (alpha[i] - alpha[j]) for x in row]
                               for row in matrix_term]
        interpolation += term
        matrix_interpolation = sub(matrix_interpolation, matrix_term, -one)
    assert interpolation == r[0][-1]
    assert matrix_interpolation == w
    at = eye
    for t in range(k):
        assert sum(at[0], zero) == s ** t
        at = mm(at, a)

    orders = 0
    for perm in permutations(cs):
        assert recurrence(perm)[0][-1] == r[0][-1]
        orders += 1
    allowed = [1 - q * cs[i] * cs[j] for i in range(k) for j in range(i + 1, k)]
    denominators = []
    for i in range(k):
        for j in range(i, k):
            coefficient, factors = factor_list(r[i][j].denom.as_expr())
            for factor, power in factors:
                assert any(cancel(factor / f.as_expr()) in (1, -1) for f in allowed)
            denominators.append([i, j, str(r[i][j].denom.as_expr())])
    return {'k': k, 'orders_checked': orders,
            'identities': ['AR-qRER=E^-1', 'AW-qW^2=I', 'AW=WA',
                           'W=p(A)', 'R_1k=p(s)', 'moments', 'all_permutations',
                           'denominator_factorization'],
            'elapsed_seconds': time.monotonic() - start,
            'denominators': denominators}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-k', type=int, default=4)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    start = time.monotonic()
    with ProcessPoolExecutor(max_workers=min(16, args.max_k)) as pool:
        results = list(pool.map(verify, range(1, args.max_k + 1)))
    report = {'results': results, 'elapsed_seconds': time.monotonic() - start,
              'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
              'arithmetic': 'exact Q(q,s,c_0,...,c_(k-1)); all variables independent',
              'gpu_assessment': 'exact sparse rational-function symbolic algebra; CPU algebra backend, independent jobs by k'}
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({**report, 'results': [{k:v for k,v in r.items() if k!='denominators'} for r in results]}, indent=2))


if __name__ == '__main__':
    main()
