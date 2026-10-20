# AI use and provenance

## How this was produced

The mathematics, the manuscript, the code, the Lean formalization and the documentation in this repository were produced by AI agents — models **Claude** (Anthropic) and **GPT** (OpenAI) — coordinated by the owner of the handle [@AIOvernight](https://x.com/AIOvernight). The proof was found without knowledge of the 2026 announcements by Burstein, Egge and Elizalde described in [`docs/BIBLIOGRAPHY.md`](BIBLIOGRAPHY.md); those announcements were located afterwards during the literature search.

This is AI-assisted work, not human or institutional review. The mathematical result is a theorem proved from the definitions and machine-checked by the Lean kernel; the production method does not change that status.

## What is independent, and in what sense

The independence below is independence **of implementation** (separately written programs, separate arithmetic backends, a proof assistant), not independence of authorship: all components were produced within the same AI-assisted project.

| Component | Independent implementations |
|---|---|
| Enumeration of layered patterns | Two object generators that share no generation code: non-crossing partial matchings generated directly, and all involutions filtered by a literal four-entry 3412 test (identical counts to n = 16). A structural layered-pattern detector, validated against literal subsequence tests for n ≤ 10. A separately written enumerator for all compositions with sum ≤ 7 and n ≤ 10. |
| Comparison target | An integer implementation of the pole-free recurrence (sparse bivariate series) that does not use the enumerators; a negative control (weight x² instead of x²y) is detected. |
| General indecomposable summands | Two separately written brute-force programs working directly from the definitions (subsequence tests), one for pairs and triples, one for 25 further patterns. |
| Generic algebra | Two exact arithmetic backends: FLINT multivariate polynomials (k ≤ 6) and SymPy rational functions (k ≤ 4), running the same list of identities. |
| The proof | The Lean 4 / Mathlib kernel check of the whole theorem from the combinatorial definitions, with axiom audit and a source scan. The exact final theorem statements and their correspondence with the manuscript are documented in the formalization map. |
| Formal definitions | Executable enumerations from the Lean definitions (all permutations of length ≤ 5) compared with known counts; kernel-checked examples of the constructions on small permutations. The formal definitions and their mathematical interpretation are documented in [`docs/FORMALIZATION.md`](FORMALIZATION.md). |
| Manuscript | The combinatorial lemmas (decomposition, containment, recurrence) were tested from one-line permutations for small lengths by a separately written program and are proved in Lean. Manuscript v4 describes the complete formalization. |

## What is preserved and what changed in release 2.0.0

- The complete Lean proof from the combinatorial definitions is retained. The algebraic modules are applied to the proved Egge–Mansour weighted recurrence, with no combinatorial hypothesis assumed. The declaration map is in [`docs/FORMALIZATION.md`](FORMALIZATION.md).
- Manuscript v4 adds the formal-verification section, its summary in the abstract and introduction, the principal Lean statements, axiom dependencies and reproduction instructions. No new mathematical result is added to the previously proved scope.
- The README, status and citation metadata describe the theorem release. The unresolved priority issue concerning the documented 2026 announcements remains explicit.
- The computational source code, data and computational evidence are retained. Earlier packaging changed output paths, directory layout and interpreter selection without changing algorithms, bounds or checks; [`evidence/CHANGES.md`](../evidence/CHANGES.md) records those changes. The computational evidence was regenerated for the earlier packaged release; it is not described as newly rerun for 2.0.0. Two supplementary algebra files (`data/algebra/small.json`, `data/algebra/factored-small.json`) were retained from an earlier run; the k ≤ 6 result supersedes their scope.
- The complete Lean project is rebuilt and its axiom dependencies audited for this release. Build logs, source hashes, environment and timings are in [`evidence/lean/`](../evidence/lean/). Matching pinned prebuilt dependencies are used; downloading and rebuilding all third-party dependencies from source is outside that reproduction.
- [`MANIFEST.json`](../MANIFEST.json) records the distributed files, SHA-256 hashes and byte sizes, including the current manuscript source and PDF. The repository contains standalone mathematics, methods, documentation and evidence.

## Credit

Project initiation and coordination: **[@AIOvernight](https://x.com/AIOvernight)**. The mathematical results of the cited authors belong to them; see [`docs/BIBLIOGRAPHY.md`](BIBLIOGRAPHY.md).
