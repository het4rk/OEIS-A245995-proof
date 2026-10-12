# Proof of Hardin's empirical column recurrences for OEIS A245995

[![Lean build](https://github.com/het4rk/OEIS-A245995-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/OEIS-A245995-proof/actions/workflows/lean.yml)

**Author:** Hetark Shah, AI-assisted by Grok  
**Date:** October 12, 2026

## Result

Let `T(n,k)` be the number of length `n+2` arrays over `0..k` with no pair in any three consecutive terms summing to exactly `k` ([A245995](https://oeis.org/A245995), R. H. Hardin, 2014). We prove, for all `n ≥ 0`:

- `k` odd: `T(n+2,k) = (k−1)·T(n+1,k) + T(n,k)`
- `k ≥ 2` even: `T(n+4,k) = (k−2)·T(n+3,k) + T(n+2,k) + (k−1)²·T(n+1,k) + (k−1)·T(n,k)`
- `k = 2`: `T(n+3,2) = T(n+2,2) + T(n,2)`; `k = 1`: the column is constant.

These give all nine of Hardin's "Empirical for column k" recurrences (k = 1..9; columns 2–7 are A245989–A245994, with conjectured g.f.s by Colin Barker and R. J. Mathar). Row 1 (A245996) was already proved by Pontus von Brömssen (2022). The method is a standard transfer-matrix argument on four pair types; what this repo adds is the uniform-in-`k` statement and a machine-checked proof.

## Status

**Complete proof** of all column recurrences, for every `k`. Machine-checked.

## Theorems and Lean names

| Lean name | Statement |
|---|---|
| `good_cons`, `N_succ` | prepending a letter (one-step recursion) |
| `N_eq_typ`, `row_sum` | counts depend only on the pair type (E/D/P/Q) |
| `T_eq_F` | `T` in terms of the type counts |
| `T_odd`, `T_even`, `T_two`, `T_one` | the general recurrences |
| `T_col1` … `T_col9` | Hardin's formulas verbatim, e.g. `5 ≤ n → T n 4 = 2T(n−1) + T(n−2) + 9T(n−3) + 3T(n−4)` |

No `sorry`, no `native_decide`. `Values.lean` checks a few table values by kernel evaluation.

## Build

Toolchain `leanprover/lean4:v4.35.0-rc4`; Mathlib `v4.35.0-rc4` (pinned in `lake-manifest.json`).

```bash
cd A245995
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Axioms output

All 13 theorems in `Axioms.lean` report `[propext, Classical.choice, Quot.sound]` (see `verification/axioms.txt`).

## Machine-check attestation

- [`verification/`](verification/): `build-log.txt`, `axioms.txt`, and [`VERIFICATION.md`](verification/VERIFICATION.md) (toolchain, Mathlib commit, reproduce steps, SHA-256 of sources).
- [CI](https://github.com/het4rk/OEIS-A245995-proof/actions/workflows/lean.yml) does a clean build on every push, fails on any `sorry`, checks the axiom whitelist (`scripts/check_axioms.sh`), and uploads the `lean-attestation` artifact.

## Paper

[`paper/main.tex`](paper/main.tex) and [`paper/paper.pdf`](paper/paper.pdf).

## Citation

See [`CITATION.cff`](CITATION.cff):

> Hetark Shah (AI-assisted by Grok), *Proof of Hardin's empirical column recurrences for OEIS A245995*, 2026. https://github.com/het4rk/OEIS-A245995-proof

## License

Apache-2.0 (the same as Mathlib). See [`LICENSE`](LICENSE).
