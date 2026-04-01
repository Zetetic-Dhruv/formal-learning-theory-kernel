# Bridge Tactic — Future Direction (Under Construction)

**Status**: Paradigm classifier works. Environment search does not yet find bridge
lemmas on real FLT goals. The tactic compiles, degrades gracefully, and produces
structured BridgeReports — but the search-and-apply pipeline needs further work.

## Architecture

The bridge tactic is the **planning layer (RCA)** above the proof operad world model
**(SCM)**. It operationalizes the typed calculus by:

1. Inspecting live Lean4 proof goals via `MetaM`
2. Classifying them by paradigm using the operad's `Paradigm` type
3. Searching the environment for lemmas whose conclusion unifies with the goal
4. Applying the lemma if found, or reporting a structured `BridgeReport` if not

## Current State

### What Works

- `StepQuality` four-gate model (calibrated against First Proof Benchmark)
- `GapType` classification (bridge vs. open-ended)
- `BridgeReport` structured output on failure
- `classifyExpr` paradigm classifier — correctly identifies PAC, Online, Gold, DST,
  Bayes, Separation goals by checking the raw Expr head BEFORE whnf
- `quality_funnel_monotone` theorem (compliance ≥ validity ≥ completion ≥ robustness)
- `bridge_failure_implies_gap` theorem (failure implies typed gap in the operad)
- Graceful degradation: tactic never crashes, always leaves goal open on failure
- All smoke tests pass (BridgeTests.lean: 10 + 7 bonus)

### What Does Not Work Yet

- `searchBridgeLemmaRestricted` finds 0 matches on real FLT goals
- **Root cause diagnosed** (2026-04-02):
  1. The kernel doesn't use Lean4 namespaces — theorems like `uc_imp_pac` are at the
     TOP LEVEL, not under `FLT_Proofs.Theorem.PAC.uc_imp_pac`
  2. `env.constants.map₁.fold` iterates ALL 188K constants (including Mathlib)
  3. The library-namespace filter correctly excludes Mathlib but ~188K `isDefEq` calls
     via `goal.apply` is slow (48s build time) and none succeed
  4. Hypothesis: `mkConstWithFreshMVarLevels` + `goal.apply` fails because the
     theorems have typeclass arguments (`[MeasurableConceptClass X C]`,
     `[IsProbabilityMeasure D]`) that can't be synthesized in the search context

### Next Steps

1. Use `Lean.Meta.DiscrTree` (Mathlib's library search infrastructure) instead of
   brute-force environment iteration — indexes lemmas by head symbol for O(1) lookup
2. Pre-populate the DiscrTree with kernel-specific theorems at tactic init time
3. Handle typeclass arguments via `synthInstance` fallback during the search
4. Test on the 5 real goals in `tests/BridgeRealTests.lean`

## Files

```
bridge_tactic/
├── README.md                    This file
├── BridgeTactic.lean            The tactic source (also in FLT_Proofs/Meta/)
└── tests/
    ├── BridgeRealTests.lean     5 real FLT goals (PAC, versionSpace, LDim, MeasurableSet)
    └── BridgeDiagnostic.lean    Diagnostic tactic for debugging the search
```

## Test Results (2026-04-02)

### Smoke Tests (pass)

| Test | Goal | Paradigm Detected | Bridge Found | Result |
|------|------|-------------------|--------------|--------|
| T10 | `True` | structural | No | PASS (graceful) |
| NT13 | `1 + 1 = 2` | structural | No | PASS (graceful) |

### Real Tests (search fails — under construction)

| Test | Goal | Paradigm Detected | Expected Bridge | Found | Status |
|------|------|-------------------|-----------------|-------|--------|
| BRT1 | `PACLearnable X C` | pac | `uc_imp_pac` | No | BLOCKED |
| BRT2 | `versionSpace C h ⊆ C` | structural | `versionSpace_subset` | No | BLOCKED |
| BRT3 | `LDim(VS) ≤ LDim(C)` | structural | `ldim_versionSpace_le` | No | BLOCKED |
| BRT4 | `MeasurableSet (A ∩ B)` | structural | `MeasurableSet.inter` | No | BLOCKED (Mathlib filtered) |
| BRT5 | `PACLearnable X C` | pac | `vcdim_finite_imp_pac` | No | BLOCKED |

Paradigm classifier is correct for BRT1/BRT5 (pac). BRT2/BRT3/BRT4 show `structural`
because `HasSubset.Subset` and `LE.le` are not paradigm-specific head constants.
