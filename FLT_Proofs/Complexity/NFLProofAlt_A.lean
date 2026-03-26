/-
Copyright (c) 2024-2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

NFL Proof Route A: Complement Approach via le_map_apply
========================================================

COUNTERFACTUAL FILE — NOT IN BUILD
This file is a swappable skeleton for the NFL proof using the complement approach.

ROUTE SUMMARY:
Work with the complement of the "good" set. Use `le_map_apply` to get a lower bound
on the complement's measure, then derive an upper bound on the good set.

STATUS: BLOCKED — Route A does NOT work without MeasurableSingletonClass X.

OBSTRUCTION ANALYSIS:
The complement approach requires: mu(good) = 1 - mu(bad) (for complementary sets).
This equality requires MeasurableSet(good) OR MeasurableSet(bad).
Without MeasurableSingletonClass X, neither set is provably measurable.

The inequality mu(good) + mu(bad) >= 1 (always true for outer measure) gives
mu(good) >= 1 - mu(bad), which is the WRONG direction. We need mu(good) <= bound.

For probability measures on non-measurable sets, mu(A) + mu(A^c) >= 1 but possibly > 1.
So mu(A^c) >= 1/2 does NOT imply mu(A) <= 1/2.

RESOLUTION: This route is viable ONLY if combined with Route C (adding MeasurableSingletonClass X).
With that hypothesis, all sets defined by Boolean predicates on X are measurable,
and mu(good) + mu(bad) = 1 holds exactly.

SWAPPABILITY: To use this skeleton, add [MeasurableSingletonClass X] to the theorem
hypotheses, then the sorry bodies below become provable.
-/

import FLT_Proofs.Complexity.Generalization

/-! Route A proof skeleton for vcdim_infinite_not_pac substep B (measure bridge).

Given:
- hcount : 2 * |{good xs_T}| <= Fintype.card (Fin m -> ↥T)
- D = D_sub.map val where D_sub = uniformMeasure ↥T
- D_sub has MeasurableSingletonClass on ↥T (discrete)

The complement approach:

Step 1: From counting bound, Measure.pi D_sub {bad_T} >= 1/2
  where bad_T = {xs_T | D_sub{t | c₀(↑t) ≠ h(↑t)} > 1/4}.
  Proof: pi_uniformMeasure gives Measure.pi D_sub A = |A|/d^m.
  |bad_T| >= d^m / 2 (complement of counting bound). So >= 1/2.

Step 2: Push forward to X.
  Measure.pi D {bad_X} >= Measure.pi D_sub (valProd⁻¹ {bad_X}) by le_map_apply.
  valProd⁻¹ {bad_X} ⊇ {bad_T} (because D(error) >= D_sub(error on T) by le_map_apply).
  So Measure.pi D {bad_X} >= 1/2.

Step 3: Complement arithmetic.
  mu(good_X) = 1 - mu(bad_X) <= 1 - 1/2 = 1/2 < 3/4.
  *** THIS STEP REQUIRES MeasurableSet(good_X) OR MeasurableSet(bad_X) ***

Step 2 detail on "D(error) >= D_sub(error on T)":
  D {x | c₀(x) ≠ h(x)} = (D_sub.map val) {x | c₀(x) ≠ h(x)}
  >= D_sub (val⁻¹ {x | c₀(x) ≠ h(x)})   [by le_map_apply]
  = D_sub {t : ↥T | c₀(↑t) ≠ h(↑t)}     [by preimage computation]

So if D_sub{error on T} > 1/4, then D{error} > 1/4. Hence bad_T ⊆ valProd⁻¹ (bad_X).
This gives the le_map_apply chain: mu_sub(bad_T) <= mu_sub(valProd⁻¹ bad_X) <= mu(bad_X).

SORRY INVENTORY (if MeasurableSingletonClass X added):
- sorry_complement_arithmetic: mu(good) = 1 - mu(bad) for measurable complement
  Mathlib API: MeasureTheory.prob_compl_eq_one_sub or measure_compl
  LOC estimate: ~10

- sorry_pi_counting: Measure.pi D_sub {bad_T} >= 1/2 from Finset counting
  Mathlib API: pi_singleton, Fintype.card product, ENNReal arithmetic
  LOC estimate: ~30

- sorry_le_map_chain: the le_map_apply composition through pi_map_pi
  Mathlib API: le_map_apply, pi_map_pi, measure_mono
  LOC estimate: ~20
-/

-- This file is intentionally NOT added to the lakefile or any import chain.
-- It serves as documentation of Route A's proof structure and obstructions.
