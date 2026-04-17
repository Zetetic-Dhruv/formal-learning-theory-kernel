# Experiment: `MeasurableConceptClass.all_measurable` is packaging, not load-bearing

**Date:** 2026-04-18
**Method:** Isolated git worktree, removed the `all_measurable` field from `MeasurableConceptClass`, built `FLT_Proofs` against a warm Mathlib cache.
**Toolchain:** `leanprover/lean4:v4.29.0-rc6`
**Worktree:** discarded after experiment

## Question

Is `all_measurable : ∀ c : Concept X Bool, Measurable c` (the second field of `MeasurableConceptClass`) doing load-bearing mathematical work in the kernel, or is it a packaging convenience?

## Change applied

Removed three things from `FLT_Proofs/Complexity/Measurability.lean`:

1. The `all_measurable` field in the `MeasurableConceptClass` class body.
2. The `MeasurableConceptClass.hc_meas` bridge theorem.
3. The `all_measurable := ...` line from the two `MeasurableConceptClass` instances (`ofUniversallyMeasurable`, `ofKrappWirth`).

No changes to any theorem statement, signature, or proof body elsewhere in the kernel.

## Result

**3011/3015 FLT_Proofs modules built clean.** Build failed at exactly 4 sites in 2 files:

| Site | File | Line | Error |
|------|------|------|-------|
| Bridge | `FLT_Proofs/Complexity/GeneralizationResults.lean` | 222 | Unknown constant `MeasurableConceptClass.hc_meas` |
| Bridge | `FLT_Proofs/Complexity/GeneralizationResults.lean` | 266 | Unknown constant `MeasurableConceptClass.hc_meas` |
| Bridge | `FLT_Proofs/Complexity/GeneralizationResults.lean` | 307 | Unknown constant `MeasurableConceptClass.hc_meas` |
| Bridge | `FLT_Proofs/Theorem/Separation.lean` | 137 | Unknown constant `MeasurableConceptClass.hc_meas` (inside `online_imp_pac`) |

Every failure is at a typeclass-to-explicit-hypothesis bridge. The caller has `[MeasurableConceptClass X C]` and extracts `hc_meas` from the projection to pass to a downstream theorem whose signature takes `(hc_meas : ∀ c : Concept X Bool, Measurable c)` as an explicit argument.

## What BUILT successfully

- Entire `Symmetrization.lean` chain (`vcdim_finite_imp_uc'`, `symmetrization_uc_bound`, `uc_bad_event_le_delta_proved`, Hoeffding tail bounds). These take `hc_meas` as an explicit argument in their signatures; the argument is still threaded through, just not sourced from the typeclass projection.
- `Theorem/PAC.lean` including `fundamental_theorem` at line 293.
- `BorelAnalyticSeparation.lean` (independent of `MeasurableConceptClass` — uses only `mem_measurable` on the singleton class witness).
- `Compression.lean`, `Rademacher.lean`, all of `PureMath/`, `FiniteSupportUC.lean`, `Amalgamation.lean`, `Interpolation.lean`.
- All of `Learner/`, `Criterion/`, `Theorem/Online.lean`, `Theorem/Gold.lean`.

## Interpretation

1. **`all_measurable` is a packaging convenience, not a mathematical load.** The mathematical content lives in the explicit-hypothesis signatures of the underlying theorems (`vcdim_finite_imp_uc'`, etc.). The typeclass field is a bundling mechanism that lets 4 bridge sites source the hypothesis through a typeclass projection instead of passing it as an explicit argument.

2. **No headline theorem's mathematical content depends on `all_measurable`.** `fundamental_theorem`, `vc_characterization`, `pac_imp_vcdim_finite`, `vcdim_finite_imp_pac`, all compiled. The Hoeffding + symmetrization proofs that I predicted would break did not: their explicit `hc_meas` argument is unchanged.

3. **The 4 bridge sites can source `hc_meas` through alternative channels.** On discrete domains with `MeasurableSingletonClass`, `hc_meas` could be derived from domain-level measurability. On Polish domains, a separate `[MeasurableBoolSpace X]` typeclass argument could be introduced at the 4 sites where the strong domain hypothesis is actually needed.

4. **Borel-analytic separation is mechanically independent.** `BorelAnalyticSeparation.lean` built without touching the change, confirming that the separation theorem `analytic_nonborel_set_gives_measTarget_separation` lives in `(WellBehavedVCMeasTarget, KrappWirthWellBehaved)` space and does not depend on `MeasurableConceptClass` in any form.

## Consequence for the paper

The honest statement for a reviewer: `MeasurableConceptClass` factors as class-level (`mem_measurable`, `wellBehaved`) plus a domain-level field (`all_measurable`) that is bundled for ergonomic convenience at 4 bridge sites. The domain-level field is automatic on `MeasurableSingletonClass` + `MeasurableBoolSpace` (discrete regime) and is the substantive commitment on Polish/standard-Borel domains. The fundamental theorem's mathematical content does not depend on which of these regimes the domain is in.

The "corrects Krapp-Wirth 2024" claim in the README refers to the `wellBehaved` field only (NullMeasurableSet weakening of the UC bad-event condition). This is confirmed by `BorelAnalyticSeparation.lean` compiling without the change: the separation lives in a different lattice (`WellBehavedVCMeasTarget ↔ KrappWirthWellBehaved`), not in `MeasurableConceptClass`.

## Decision

Not fixing the 4 bridge sites. The experiment's purpose was diagnostic (confirm packaging vs load-bearing), not refactoring. The finding is documented here; the `main` branch retains `all_measurable` for ergonomic reasons at those 4 bridge sites. Future work: if a Polish-domain extension needs a cleaner separation between domain and class hypotheses, refactor the 4 sites to take `[MeasurableBoolSpace X]` explicitly.
