#!/usr/bin/env python3
"""Literal audit for permutations of arbitrary direct-sum indecomposable blocks."""
import argparse
from hashlib import sha256
from itertools import combinations, permutations
import json
from pathlib import Path
import time
from review_independent import involutions


def direct(blocks):
    out = []
    for block in blocks:
        offset = len(out)
        out.extend(offset + x for x in block)
    return tuple(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n', type=int, default=9)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    start = time.monotonic()
    groups = [[(1,), (2, 3, 1), (2, 1)],
              [(2, 4, 1, 3), (1,), (2, 1)],
              [(3, 1, 2), (2, 1), (1,)],
              [(3, 1, 4, 2), (2, 3, 1)],
              [(1,), (1,), (2, 3, 1)],
              [(2, 3, 4, 1), (2, 1)]]
    for blocks in groups:
        for b in blocks:
            assert sorted(b) == list(range(1, len(b) + 1))
            assert all(set(b[:j]) != set(range(1, j + 1)) for j in range(1, len(b)))
    patterns = {direct(order): gi for gi, group in enumerate(groups)
                for order in permutations(group)}
    records, mismatches = [], []
    for n in range(args.n + 1):
        counts = {p: [0] * (n // 2 + 1) for p in patterns}
        choices = {m: list(combinations(range(n), m)) for m in {len(p) for p in patterns}}
        four = list(combinations(range(n), 4))
        for p in involutions(n):
            if any(p[k] < p[l] < p[i] < p[j] for i, j, k, l in four):
                continue
            r = sum(v > i for i, v in enumerate(p))
            seen = set()
            for ixes in choices.values():
                for ix in ixes:
                    vals = [p[i] for i in ix]
                    rank = {v: j + 1 for j, v in enumerate(sorted(vals))}
                    pat = tuple(rank[v] for v in vals)
                    if pat in patterns:
                        seen.add(pat)
            for pat, row in counts.items():
                if pat not in seen:
                    row[r] += 1
        for gi in range(len(groups)):
            rows = [row for p, row in counts.items() if patterns[p] == gi]
            if len({tuple(row) for row in rows}) != 1:
                mismatches.append([n, gi, rows])
        records.append({'n': n, 'counts': {str(k): v for k, v in counts.items()}})
    result = {'groups': groups, 'patterns': len(patterns), 'n_max': args.n,
              'mismatches': mismatches, 'seconds': time.monotonic() - start,
              'records': records,
              'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
              'generator_sha256': sha256(Path(__file__).with_name('review_independent.py').read_bytes()).hexdigest(),
              'resources': 'small independent literal CPU control; elapsed wall time in seconds; no GPU run'}
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(result, indent=2) + '\n')
    print({k: v for k, v in result.items() if k != 'records'})
    assert not mismatches


if __name__ == '__main__':
    main()
