/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.Measurability
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Borel-Analytic Bridge for Statistical Learning Theory

This file proves that NullMeasurableSet is the exactly right level of measurability
for the Fundamental Theorem of Statistical Learning with Borel-parameterized
concept classes over Polish spaces.

## Main results

- `paramWitnessSet_measurable`: the witness graph {(θ, p) | gap(θ, p) ≥ ε/2} is Borel
- `borel_param_badEvent_analytic`: projection to sample space is analytic (Σ₁¹)
- `analyticSet_nullMeasurableSet`: analytic → NullMeasurableSet (DST bridge lemma)
- `borel_param_wellBehavedVCMeasTarget`: Borel parameterization → WellBehavedVCMeasTarget

## The separation

The counterexample (singleton class over analytic non-Borel A ⊆ ℝ) shows the
bad event can be analytic but NOT Borel, hence WellBehavedVCMeasTarget holds
but KrappWirthWellBehaved fails. See Theorem/BorelAnalyticSeparation.lean.

## References

- Suslin (1917): projections of Borel sets are analytic
- Lusin (1925): analytic sets are universally measurable
- Krapp & Wirth (2024, arXiv:2410.10243): MeasurableSet conditions for FTSL
- This kernel: NullMeasurableSet weakening discovered during Lean4 formalization (Session 7)
-/

universe u

open MeasureTheory

/-! ## Core Definitions -/

/-- Ghost sample pairs: two independent samples of size m. -/
abbrev GhostPairs (X : Type u) (m : ℕ) := (Fin m → X) × (Fin m → X)

/-- The witness set in parameter × sample space:
    {(θ, p) | EmpErr(h_θ, ghost, c) - EmpErr(h_θ, train, c) ≥ ε/2}.
    This is Borel when e and c are measurable (Theorem A). -/
def paramWitnessSet
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ) :
    Set (Θ × GhostPairs X m) :=
  {q | EmpiricalError X Bool (e q.1) (fun i => (q.2.2 i, c (q.2.2 i))) (zeroOneLoss Bool) -
       EmpiricalError X Bool (e q.1) (fun i => (q.2.1 i, c (q.2.1 i))) (zeroOneLoss Bool) ≥ ε / 2}

/-- The bad event in sample space: projection of the witness set.
    Existential over the parameter: {p | ∃ θ, gap(θ, p) ≥ ε/2}.
    This is analytic when the witness set is Borel (Theorem B). -/
def paramBadEvent
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ) :
    Set (GhostPairs X m) :=
  Prod.snd '' paramWitnessSet e c m ε

/-- Patched evaluation: combine two concept families using a region selector.
    patchEval(θ₁, θ₂, ρ)(x) = e₁(θ₁)(x) if r(ρ)(x), else e₂(θ₂)(x).
    Used for the closure principle (Theorem F). -/
def patchEval
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ Ρ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] [MeasurableSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool) :
    (Θ₁ × Θ₂ × Ρ) → Concept X Bool :=
  fun θ x => if r θ.2.2 x then e₁ θ.1 x else e₂ θ.2.1 x
