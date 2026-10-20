#!/usr/bin/env bash
set -euo pipefail
src_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
out_dir="${1:-./results/literal}"
mkdir -p "$out_dir"
g++ -O3 -march=native -fopenmp -std=c++17 "$src_dir/literal.cpp" -o "$out_dir/literal"
"$out_dir/literal" selftest > "$out_dir/selftest.log"
"$out_dir/literal" A 16 "$out_dir/counts-A.csv" > "$out_dir/A.log"
"$out_dir/literal" G 16 "$out_dir/counts-G.csv" > "$out_dir/G.log"
"$out_dir/literal" B 22 "$out_dir/counts-B.csv" > "$out_dir/B.log"
python3 "$src_dir/check_series.py" --directory "$out_dir" > "$out_dir/comparison.log"
