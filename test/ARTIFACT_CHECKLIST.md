# Artifact Checklist

## Toolchain

| Component | Version | Pinned? |
|-----------|---------|---------|
| Lean | `v4.29.0-rc6` | Yes (`lean-toolchain`) |
| Mathlib4 | `fde0cc508f` | Yes (`lakefile.lean` + `lake-manifest.json`) |
| Lake | bundled with Lean | Yes |

## Build

```bash
# Prerequisites: elan (https://github.com/leanprover/elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build (first run fetches Mathlib, ~20 minutes)
lake build

# Subsequent builds: ~2 minutes (incremental)
```

**Expected build time (clean):** 15-25 minutes (dominated by Mathlib compilation).

**Expected build time (cached Mathlib):** 1-3 minutes.

**Expected output:** 0 errors, ~2999 jobs completed.

## Sorry Inventory

Exactly 2 `sorry` tactics exist in the kernel. Both are on the critical path and are blocked by published results absent from Mathlib.

| # | File | Theorem | Blocked by | Citation |
|---|------|---------|-----------|----------|
| 1 | `FLT_Proofs/Complexity/Generalization.lean:1903` | `vcdim_finite_imp_compression` | Approximate minimax on bounded-VC binary matrices | Moran-Yehudayoff 2016 (arXiv:1503.06960) |
| 2 | `FLT_Proofs/Theorem/Extended.lean:39` | `bhmz_middle_branch` | One-inclusion graph learners + doubling aggregation | Bousquet-Hanneke-Moran-Zhivotovskiy, STOC 2021 |

**CI enforcement:** The GitHub Actions workflow fails if the sorry count exceeds 2.

## Verification Commands

```bash
# Count sorrys (should print exactly 2 lines)
grep -rn "sorry" --include="*.lean" FLT_Proofs/ | grep -v "^.*--.*sorry" | grep -v "//-"

# Verify no new files with sorry
grep -rl "sorry" --include="*.lean" FLT_Proofs/
# Expected: Complexity/Generalization.lean, Theorem/Extended.lean

# Full build from clean state
rm -rf .lake/build
lake build
```

## Default Target

The default Lake target is `FLT_Proofs` (all 31 files). It **does** permit `sorry` (Lean's default). The CI workflow enforces the sorry ceiling independently.

## File Inventory

- 31 `.lean` files in `FLT_Proofs/`
- 14,945 lines of Lean4
- 210 theorem/lemma statements
- 150 definitions
- 46 structures
