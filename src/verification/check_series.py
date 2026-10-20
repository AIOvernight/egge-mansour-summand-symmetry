#!/usr/bin/env python3
"""Exact integer bivariate series recurrence, independent of object generator."""

import argparse, csv, functools, json, time, hashlib, math, re, platform
from pathlib import Path

P = argparse.ArgumentParser()
P.add_argument("--directory", default="./results/literal")
P.add_argument("--maxn", type=int, default=22)
args = P.parse_args()
N = args.maxn
ZERO = {}
ONE = {(0, 0): 1}
X = {(1, 0): 1}
Q = {(2, 1): 1}
S = {(0, 0): 1, (1, 0): -1}


def add(a, b, sign=1):
    d = a.copy()
    for k, v in b.items():
        d[k] = d.get(k, 0) + sign * v
        if not d[k]:
            del d[k]
    return d


def mul(a, b):
    d = {}
    for (n, r), v in a.items():
        for (m, t), w in b.items():
            if n + m <= N:
                d[n + m, r + t] = d.get((n + m, r + t), 0) + v * w
    return {k: v for k, v in d.items() if v}


def inv(a):
    assert a.get((0, 0)) == 1
    rest = add(ONE, a, -1)
    d = ONE.copy()
    power = ONE
    for _ in range(N):
        power = mul(power, rest)
        if not power:
            break
        d = add(d, power)
    return d


@functools.lru_cache(None)
def single(a):
    if a == 0:
        return ZERO
    if a == 1:
        return ONE
    return inv(add(S, mul(Q, single(a - 2)), -1))


@functools.lru_cache(None)
def F(a):
    if len(a) == 1:
        return single(a[0])
    c = single(a[0])
    last = single(a[-1])
    d = add(c, mul(add(ONE, mul(S, c), -1), F(a[1:])))
    for h in range(1, len(a) - 1):
        d = add(d, mul(mul(Q, c), mul(F(a[: h + 1]), add(F(a[h:]), F(a[h + 1 :]), -1))))
    return mul(d, inv(add(ONE, mul(Q, mul(c, last)), -1)))


start = time.time()
directory = Path(args.directory)
checked = 0
rows = 0
discrepancies = []
mutation = None
tables = {}
for mode in ["A", "B", "G"]:
    path = directory / f"counts-{mode}.csv"
    if not path.exists():
        raise FileNotFoundError(path)
    tables[mode] = {}
    with path.open() as fh:
        for row in csv.DictReader(fh):
            a = tuple(map(int, row["pattern"].split("-")))
            n = int(row["n"])
            r = int(row["r"])
            observed = int(row["count"])
            if n > N:
                continue
            expected = F(a).get((n, r), 0)
            rows += 1
            tables[mode][a, n, r] = observed
            if expected != observed:
                discrepancies.append(dict(row, expected=expected))
            # Removing y from q moves all mass to r=0: this must fail.
            mutated = sum(v for (nn, rr), v in F(a).items() if nn == n) if r == 0 else 0
            if mutation is None and mutated != observed:
                mutation = dict(pattern=a, n=n, r=r, observed=observed, mutated=mutated)
    checked += 1
assert tables["A"] == tables["G"], "Unrestricted and noncrossing generators disagree"
assert len(tables["A"]) == 255 * sum(
    n // 2 + 1 for n in range(17)
), "Incomplete A/G domain"
assert len(tables["B"]) == 34 * sum(
    n // 2 + 1 for n in range(23)
), "Incomplete B domain"
summary = {
    "maxn_series": N,
    "files_checked": checked,
    "coefficients_compared": rows,
    "distinct_vectors": F.cache_info().currsize,
    "discrepancies": discrepancies,
    "mutation_counterexample": mutation,
    "seconds": time.time() - start,
    "arithmetic": "Python arbitrary precision integers; sparse bivariate polynomials",
    "hashes": {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in directory.glob("counts-*.csv")
    },
}
summary["domains"] = {
    "A": {
        "vectors": 255,
        "max_n": 16,
        "method": "explicit noncrossing partial matchings",
    },
    "G": {
        "vectors": 255,
        "max_n": 16,
        "method": "all involutions; direct four-entry 3412 filter",
    },
    "B": {
        "vectors": 34,
        "max_n": 22,
        "method": "explicit noncrossing partial matchings",
    },
}
summary["generator_comparison"] = "A == G for every coefficient"
summary["timings"] = {
    mode: [
        dict(n=int(n), seconds=float(sec))
        for n, sec in re.findall(
            r"n=(\d+).*?seconds=([0-9.e+-]+)", (directory / f"{mode}.log").read_text()
        )
    ]
    for mode in ["A", "B", "G"]
}
summary["source_hashes"] = {
    p.name: hashlib.sha256(p.read_bytes()).hexdigest()
    for p in Path(__file__).parent.glob("*")
    if p.is_file()
}
assert (directory / "selftest.log").read_text().endswith("SELFTEST PASS\n")
summary["generic_detector_control"] = {
    "max_n": 10,
    "vectors": 261,
    "status": "PASS",
    "objects": "all general involutions, filtered by direct 3412 comparisons",
}
with (directory / "counts.csv").open("w") as out:
    out.write("mode,pattern,n,r,count\n")
    for mode in ["A", "B", "G"]:
        with (directory / f"counts-{mode}.csv").open() as f:
            next(f)
            out.write(f.read())
summary["hashes"]["counts.csv"] = hashlib.sha256(
    (directory / "counts.csv").read_bytes()
).hexdigest()
(directory / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
assert not discrepancies
assert mutation
