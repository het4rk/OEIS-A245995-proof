# Verification record

| Item | Value |
|---|---|
| Date | 2026-10-12 |
| Verified commit | `8bec6d46d452a762d7ec3724c24585b9f8f1b6a6` |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc4` |
| Mathlib | `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| Build result | `Build completed successfully` (see [`build-log.txt`](build-log.txt)) |
| Axioms | 13 declarations, all `[propext, Classical.choice, Quot.sound]` (see [`axioms.txt`](axioms.txt)) |
| CI | [![Lean build](https://github.com/het4rk/OEIS-A245995-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/OEIS-A245995-proof/actions/workflows/lean.yml) |

## Reproduce

```bash
git clone https://github.com/het4rk/OEIS-A245995-proof
cd OEIS-A245995-proof
git checkout 8bec6d46d452a762d7ec3724c24585b9f8f1b6a6
cd A245995
lake exe cache get
lake build
lake env lean Axioms.lean
grep -rnw sorry A245995 --include=*.lean   # expect no output
```

## No-sorry check

`grep -rnw sorry A245995/A245995 --include=*.lean` gave no matches, and the build log has no `declaration uses 'sorry'` warnings. No `native_decide` is used.

Fresh clone of that commit: `lake exe cache get`, `lake build` (success), `lake env lean Axioms.lean` checked by `scripts/check_axioms.sh` (OK, 13 declarations).

## SHA-256 of the Lean sources (at the verified commit)

```
197e81192eb90547c22f63a46552ba275eb03f41d74e39f43647f081a76db730  A245995.lean
b413d6f07467b0a3f26be408b2c55d5dfa513b9f963c4a225089af26314b5d31  Axioms.lean
58342d79db1fe1a86eee06600e0749a98ae3731cc79da641dbd5146e485367b6  A245995/Basic.lean
71135a145805b38618bbed87b259e309aeb185b145b3b2a4443ea45fdfe3bb82  A245995/Main.lean
5481d8c8f12b4d0d45b3aafaa6062980ecd9a1e09352de31a99fa1a065976724  A245995/Types.lean
36a8c456879cf35913f0289791d21ee003132c86555b929a0ca33f9591c54ae8  A245995/Values.lean
f87e2a12c573480ae57395209204ec57eba8c7494cf523a6b9fc373620226516  lakefile.toml
67ce6e8b16aed0d157225af576d6390ba4cd90cdd4bbacca45430d449f948e1c  lake-manifest.json
8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7  lean-toolchain
```
