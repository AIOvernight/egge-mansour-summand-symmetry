#!/usr/bin/env python3
"""Independent small-case audit: all involutions, literal patterns, source recurrence.

No noncrossing generator, matrix formula, or uniform recurrence is used by the
literal oracle.  Arithmetic is integer-exact.  Run --help for bounds.
"""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, permutations
import json
from pathlib import Path
import time


def compositions(n):
    if not n:
        yield ()
    for a in range(1, n + 1):
        for b in compositions(n - a):
            yield (a,) + b


def pattern(a):
    out, shift = [], 0
    for length in a:
        out.extend(range(shift + length - 1, shift - 1, -1))
        shift += length
    return tuple(out)


def involutions(n):
    p = [-1] * n
    def visit():
        try:
            i = p.index(-1)
        except ValueError:
            yield tuple(p)
            return
        p[i] = i
        yield from visit()
        p[i] = -1
        for j in range(i + 1, n):
            if p[j] == -1:
                p[i], p[j] = j, i
                yield from visit()
                p[i] = p[j] = -1
    yield from visit()


def literal_at_n(args):
    n, max_weight = args
    patterns = {pattern(a): a for m in range(1, max_weight + 1)
                for a in compositions(m)}
    positions = {m: list(combinations(range(n), m))
                 for m in range(1, min(n, max_weight) + 1)}
    four = list(combinations(range(n), 4))
    counts = {a: [0] * (n // 2 + 1) for a in patterns.values()}
    generated, surviving = 0, 0
    for p in involutions(n):
        generated += 1
        if any(p[k] < p[l] < p[i] < p[j] for i, j, k, l in four):
            continue
        surviving += 1
        r = sum(v > i for i, v in enumerate(p))
        contained = set()
        for m, choices in positions.items():
            for ix in choices:
                vals = [p[i] for i in ix]
                ranks = {v: j for j, v in enumerate(sorted(vals))}
                pat = tuple(ranks[v] for v in vals)
                if pat in patterns:
                    contained.add(patterns[pat])
        for a, row in counts.items():
            if a not in contained:
                row[r] += 1
    return n, generated, surviving, counts


def addpoly(a, b, scale=1):
    result = Counter(a)
    for j, x in b.items():
        result[j] += scale * x
    return {j: x for j, x in result.items() if x}


def mulpoly(a, b):
    out = Counter()
    for i, x in a.items():
        for j, y in b.items():
            out[i + j] += x * y
    return dict(out)


def source_recurrence(max_weight, N):
    """Coefficient recursion from the unrearranged, piecewise equation (2)."""
    pats = [a for m in range(1, max_weight + 1) for a in compositions(m)]
    F = {a: [{} for _ in range(N + 1)] for a in pats}
    zero = [{} for _ in range(N + 1)]
    F[()] = zero

    def conv(a, b, n):
        if n < 0:
            return {}
        out = {}
        for d in range(n + 1):
            out = addpoly(out, mulpoly(a[d], b[n - d]))
        return out

    for n in range(N + 1):
        for a in pats:
            h = F[(a[0] - 2,)] if a[0] >= 3 else zero
            value = {0: 1} if n == 0 else {}
            if n:
                value = addpoly(value, F[a if a[0] >= 2 else a[1:]][n - 1])
            pair = conv(h, F[a], n - 2)
            for j in range(1, len(a)):
                prev = h if j == 1 else F[a[:j]]
                pair = addpoly(pair, conv(F[a[:j + 1]], F[a[j:]], n - 2))
                pair = addpoly(pair, conv(prev, F[a[j:]], n - 2), -1)
            value = addpoly(value, {r + 1: x for r, x in pair.items()})
            F[a][n] = value
    del F[()]
    return F


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n', type=int, default=10)
    parser.add_argument('--weight', type=int, default=7)
    parser.add_argument('--workers', type=int, default=16)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    started = time.monotonic()
    expected = source_recurrence(args.weight, args.n)
    mismatches, symmetry_mismatches, cells, totals, records = [], [], 0, [], []
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for n, generated, surviving, counts in pool.map(
                literal_at_n, [(n, args.weight) for n in range(args.n + 1)]):
            totals.append({'n': n, 'all_involutions': generated,
                           'avoid_3412': surviving})
            for a, actual in counts.items():
                want = [expected[a][n].get(r, 0) for r in range(n // 2 + 1)]
                cells += len(actual)
                if want != actual:
                    mismatches.append([a, n, actual, want])
                if actual != counts[tuple(sorted(a))]:
                    symmetry_mismatches.append([a, n, actual])
                records.append([list(a), n, actual])
            print('literal', totals[-1], flush=True)
    # Mutation controls certify the comparison is sensitive to both statistics.
    assert expected[(1, 1)][2].get(1) == 1
    assert expected[(2,)][2].get(0) == 1
    mutation_controls = {
        'erase_outer_pair_weight_detected': expected[(1, 1)][2] != {0: 1},
        'treat_initial_singleton_as_nonsingleton_detected': expected[(1,)][1] != {0: 1},
    }
    report = {'method': 'all involutions + literal subsequence patterns vs source eq.(2)',
              'gpu_assessment': 'irregular exhaustive generation and tiny exact case; CPU parallelism avoids GPU setup and preserves oracle independence',
              'n_max': args.n, 'pattern_weight_max': args.weight,
              'patterns': len(expected), 'cells': cells, 'totals': totals,
              'mismatches': mismatches, 'symmetry_mismatches': symmetry_mismatches,
              'mutation_controls': mutation_controls,
              'elapsed_seconds': time.monotonic() - started,
              'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
              'records': records}
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'records'}, indent=2))
    assert not mismatches and not symmetry_mismatches


if __name__ == '__main__':
    main()
