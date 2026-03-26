/-
Copyright (c) 2024-2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

NFL Proof Route B: Purely Combinatorial on Fin m -> ↥T (UU_1 Conversion)
=========================================================================

COUNTERFACTUAL FILE — NOT IN BUILD
This file is a swappable skeleton for the NFL proof using the purely combinatorial
approach on the Fintype product Fin m -> ↥T, converting to Fin m -> X only at the end.

ROUTE SUMMARY (UU_1 from D2_Proof_URS):
Do ALL counting and probability on Fin m -> ↥T where ↥T has discrete MeasurableSpace (⊤).
This gives MeasurableSingletonClass on ↥T automatically. The product Fin m -> ↥T is also
discrete, so ALL sets are measurable. The counting argument and probability bounds work
perfectly on this side. Only convert to Fin m -> X at the very last step via pushforward.

STATUS: BLOCKED at the conversion step. Classified as KU (articulated unknown -> known obstruction).

UU_1 -> KU CONVERSION ANALYSIS:
================================

The obstruction is at the EXACT step where we convert from T to X.

Available infrastructure:
- pi_map_pi (Mathlib): (Measure.pi mu).map (fun x i => f i (x i)) = Measure.pi (fun i => (mu i).map (f i))
  Applied: Measure.pi D = (Measure.pi D_sub).map valProd where valProd xs i = (xs i).val.
- le_map_apply (Mathlib): mu(f⁻¹ S) <= mu.map f S for any set S.
- map_apply (Mathlib): mu(f⁻¹ S) = mu.map f S when S is MeasurableSet.
- MeasurableEmbedding.map_apply: mu.map f S = mu(f⁻¹ S) for ALL sets S, but requires
  MeasurableSet(range f) in the codomain.

The conversion requires showing:
  (Measure.pi D_sub).map valProd {good_X} = Measure.pi D_sub {good_T}

where:
  good_X = {xs : Fin m -> X | D{x | c₀(x) ≠ h(x)} <= eps}
  good_T = {xs_T : Fin m -> ↥T | D_sub{t | c₀(↑t) ≠ h(↑t)} <= eps}

Translation: good_T = valProd⁻¹ good_X iff D{error(xs)} = D_sub{error_T(xs_T)} for xs = valProd(xs_T).

Sub-obstruction 1: D{error_set} = D_sub(val⁻¹ error_set)?
  D = D_sub.map val. By map_apply: D S = D_sub(val⁻¹ S) when S is MeasurableSet.
  error_set = {x | c₀(x) ≠ h(x)} — NOT necessarily MeasurableSet in X.
  le_map_apply gives D S >= D_sub(val⁻¹ S) (wrong direction for equality).
  For atomic measures: D S = sum_{t : ↥T, val(t) ∈ S} D_sub{t}. This requires decomposing
  the map measure into atoms, which needs MeasurableSingletonClass on the codomain (X).

Sub-obstruction 2: Even if good_T = valProd⁻¹ good_X, need map_apply for {good_X}.
  (mu_sub.map valProd) {good_X} = mu_sub(valProd⁻¹ {good_X}) = mu_sub(good_T).
  This uses map_apply which requires MeasurableSet(good_X) in Fin m -> X.
  Alternatively, MeasurableEmbedding.map_apply works for ALL sets but requires
  MeasurableSet(range valProd), i.e., {xs : Fin m -> X | ∀ i, xs i ∈ T} is measurable.
  This is Set.pi Set.univ (fun _ => (T : Set X)), which is measurable iff (T : Set X) is measurable,
  which requires MeasurableSingletonClass X (finite set measurability).

CONCLUSION: Route B (UU_1) reaches the SAME obstruction as Route A at the conversion step.
The measurability issue is FUNDAMENTAL to any approach that needs to bound Measure.pi D
on a non-measurable set defined in Fin m -> X.

INVARIANCE ANALYSIS:
Route B has HIGHER invariance than Route A on the combinatorial core (everything works
perfectly on discrete products). The obstruction is LOWER (single point of failure at
conversion, vs Route A's more complex complement arithmetic). But the obstruction is
the SAME mathematical issue: non-measurability of the error predicate in X.

WHAT WOULD MAKE THIS ROUTE WORK:
1. Add MeasurableSingletonClass X (= Route C, the primary route)
2. Prove that for purely atomic pushforward measures, map f S = mu(f⁻¹ S) for all S
   (this would be a new Mathlib lemma; true mathematically but may not be formalized)
3. Find a measurable superset of good_X with the same measure (requires structural
   analysis of the measure, which circles back to atomicity)

SWAPPABILITY:
If Route C is applied (MeasurableSingletonClass X added), then Route B's skeleton
can be used for the proof by working on Fin m -> ↥T for the counting core and
using map_apply (now available since good_X becomes measurable) for the conversion.
This is actually the RECOMMENDED approach within Route C — the counting argument
is cleaner on the discrete product.

SORRY INVENTORY (assuming MeasurableSingletonClass X):

sorry_counting_core: ~80 LOC
  The double-counting + pigeonhole on Fin m -> ↥T.
  For each xs_T : Fin m -> ↥T, the pairing argument on unseen coordinates:
  - Group f : ↥T -> Bool by f|_{range(xs_T)} (2^m groups)
  - Within each group, h₀ is fixed (same training data)
  - Pair f_unseen with !f_unseen: sum of disagreements = |unseen|
  - |unseen| = d - |range(xs_T) ∩ T| >= d - m > d/2
  - At most one per pair has <= d/4 disagreements
  - Per xs_T: #{good f} <= 2^{d-1}
  - Swap sums: sum_{f₀} #{good xs_T} = sum_{xs_T} #{good f} <= card(Fin m -> ↥T) · 2^{d-1}
  - Pigeonhole: ∃ f₀ with #{good xs_T} <= card(Fin m -> ↥T) / 2
  Mathlib APIs: Finset.sum_comm, Finset.card_filter, pigeonhole_finset

sorry_pi_counting_bridge: ~30 LOC
  Convert: 2 * |{good_T}| <= card(Fin m -> ↥T) to Measure.pi D_sub {good_T} <= 1/2.
  On discrete product: Measure.pi D_sub = (1/d)^m · count.
  Measure.pi D_sub A = |A| · (1/d)^m = |A| / d^m.
  card(Fin m -> ↥T) = d^m. So Measure.pi D_sub {good_T} <= d^m/2 / d^m = 1/2.
  Mathlib APIs: pi_singleton, Fintype.card_fun, ENNReal arithmetic.

sorry_measure_bridge: ~25 LOC
  Convert Measure.pi D_sub {good_T} <= 1/2 to Measure.pi D {good_X} <= 1/2.
  With MeasurableSingletonClass X:
  - good_X is MeasurableSet (finite Boolean predicate)
  - pi_map_pi: Measure.pi D = (Measure.pi D_sub).map valProd
  - map_apply: (Measure.pi D_sub).map valProd {good_X} = Measure.pi D_sub (valProd⁻¹ {good_X})
  - valProd⁻¹ {good_X} = good_T (by D S = D_sub(val⁻¹ S) for measurable S)
  Mathlib APIs: pi_map_pi, map_apply, Measure.map_apply.

sorry_final_bound: ~10 LOC
  Measure.pi D {good_X} <= 1/2 < 3/4 (or 6/7 for the other sorrys).
  Pure ENNReal arithmetic.
-/

-- This file is intentionally NOT added to the lakefile or any import chain.
-- It serves as documentation of Route B's proof structure, UU_1->KU conversion,
-- and the specific obstruction blocking the purely combinatorial approach.
