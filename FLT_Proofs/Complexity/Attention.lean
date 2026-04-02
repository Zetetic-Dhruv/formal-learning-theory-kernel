/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.Amalgamation

/-!
# Attention Mechanisms as Measurable Routing

This file formalizes binary attention routers as measurable concept routing
and proves they satisfy the kernel's measurability framework
(`WellBehavedVCMeasTarget`).

## Main results

- `MeasurableRouterFamily`: a measurable family of Boolean routers (weaker than BorelRouterCode)
- `BinaryAttentionRouterCode`: attention via score comparison (scoreL vs scoreR)
- `route_measurable`: the induced Boolean router is jointly measurable
- `attentionOfRouter_route_eq`: every measurable router family is representable as attention
- `sharedRouterAmalgClass`: amalgamation class with shared router parameter
- `binaryAttentionPatch_wellBehaved`: attention patching satisfies WellBehavedVCMeasTarget

## References

- BorelAnalyticBridge.lean (patchEval, patch_borel_param_wellBehavedVCMeasTarget)
- Amalgamation.lean (amalgClass, agreementRel)
- Interpolation.lean (BorelRouterCode, piecewiseConcept)
-/

universe u

open Classical
open MeasureTheory Set

/-! ## Item 1: MeasurableRouterFamily -/

/-- A measurable family of Boolean routers. Weaker than BorelRouterCode
    (no surjectivity requirement, no StandardBorelSpace on Ρ required for definition,
    though it is included for downstream use). -/
structure MeasurableRouterFamily (X : Type u) [MeasurableSpace X] where
  Ρ : Type u
  instMeasΡ : MeasurableSpace Ρ
  instStdΡ : @StandardBorelSpace Ρ instMeasΡ
  eval : Ρ → Concept X Bool
  eval_meas : @Measurable (Ρ × X) Bool (instMeasΡ.prod ‹MeasurableSpace X›)
    inferInstance (fun p => eval p.1 p.2)

attribute [instance] MeasurableRouterFamily.instMeasΡ
attribute [instance] MeasurableRouterFamily.instStdΡ

/-! ## Item 2: BinaryAttentionRouterCode -/

/-- A binary attention router: routes via score comparison.
    For each parameter ρ and input x, the router outputs `true` when
    scoreL ρ x ≤ scoreR ρ x, else `false`. -/
structure BinaryAttentionRouterCode (X : Type u) [MeasurableSpace X] where
  Ρ : Type u
  instMeasΡ : MeasurableSpace Ρ
  instStdΡ : @StandardBorelSpace Ρ instMeasΡ
  scoreL : Ρ → X → ℝ
  scoreR : Ρ → X → ℝ
  scoreL_meas : @Measurable (Ρ × X) ℝ (instMeasΡ.prod ‹MeasurableSpace X›)
    inferInstance (fun p => scoreL p.1 p.2)
  scoreR_meas : @Measurable (Ρ × X) ℝ (instMeasΡ.prod ‹MeasurableSpace X›)
    inferInstance (fun p => scoreR p.1 p.2)

attribute [instance] BinaryAttentionRouterCode.instMeasΡ
attribute [instance] BinaryAttentionRouterCode.instStdΡ

/-- The Boolean route induced by score comparison: true when scoreL ≤ scoreR. -/
noncomputable def BinaryAttentionRouterCode.route
    {X : Type u} [MeasurableSpace X]
    (A : BinaryAttentionRouterCode X) : A.Ρ → Concept X Bool :=
  fun ρ x => if A.scoreL ρ x ≤ A.scoreR ρ x then true else false

/-! ## Item 3: route_measurable -/

/-- The route induced by score comparison is jointly measurable. -/
theorem BinaryAttentionRouterCode.route_measurable
    {X : Type u} [MeasurableSpace X]
    (A : BinaryAttentionRouterCode X) :
    Measurable (fun p : A.Ρ × X => A.route p.1 p.2) := by
  letI := A.instMeasΡ
  -- The set {p | scoreL p.1 p.2 ≤ scoreR p.1 p.2} is MeasurableSet
  have hpair : Measurable (fun p : A.Ρ × X => (A.scoreL p.1 p.2, A.scoreR p.1 p.2)) :=
    Measurable.prodMk A.scoreL_meas A.scoreR_meas
  have hclosed : MeasurableSet {q : ℝ × ℝ | q.1 ≤ q.2} :=
    (isClosed_le continuous_fst continuous_snd).measurableSet
  have hset : MeasurableSet {p : A.Ρ × X | A.scoreL p.1 p.2 ≤ A.scoreR p.1 p.2} :=
    hpair hclosed
  -- route is piecewise constant on this set
  exact Measurable.piecewise hset measurable_const measurable_const

/-! ## Item 4: toMeasurableRouterFamily -/

/-- Every BinaryAttentionRouterCode induces a MeasurableRouterFamily. -/
noncomputable def BinaryAttentionRouterCode.toMeasurableRouterFamily
    {X : Type u} [MeasurableSpace X]
    (A : BinaryAttentionRouterCode X) : MeasurableRouterFamily X where
  Ρ := A.Ρ
  instMeasΡ := A.instMeasΡ
  instStdΡ := A.instStdΡ
  eval := A.route
  eval_meas := A.route_measurable

/-! ## Item 5: attentionOfRouter (representation theorem) -/

/-- Every MeasurableRouterFamily can be represented as a BinaryAttentionRouterCode.
    The construction uses score 0 vs 1 (or 1 vs 0) to encode the Boolean decision. -/
noncomputable def attentionOfRouter
    {X : Type u} [MeasurableSpace X]
    (R : MeasurableRouterFamily X) : BinaryAttentionRouterCode X where
  Ρ := R.Ρ
  instMeasΡ := R.instMeasΡ
  instStdΡ := R.instStdΡ
  scoreL := fun ρ x => if R.eval ρ x then (0 : ℝ) else 1
  scoreR := fun ρ x => if R.eval ρ x then (1 : ℝ) else 0
  scoreL_meas := by
    letI := R.instMeasΡ
    have hs : MeasurableSet {p : R.Ρ × X | R.eval p.1 p.2 = true} :=
      R.eval_meas (measurableSet_singleton true)
    exact Measurable.piecewise hs measurable_const measurable_const
  scoreR_meas := by
    letI := R.instMeasΡ
    have hs : MeasurableSet {p : R.Ρ × X | R.eval p.1 p.2 = true} :=
      R.eval_meas (measurableSet_singleton true)
    exact Measurable.piecewise hs measurable_const measurable_const

/-! ## Item 6: attentionOfRouter_route_eq -/

/-- The attention representation is faithful: routing through attentionOfRouter
    recovers the original router evaluation. -/
theorem attentionOfRouter_route_eq
    {X : Type u} [MeasurableSpace X]
    (R : MeasurableRouterFamily X) :
    (attentionOfRouter R).route = R.eval := by
  funext ρ; funext x
  show (if (if R.eval ρ x = true then (0 : ℝ) else 1) ≤
        (if R.eval ρ x = true then (1 : ℝ) else 0) then true else false) = R.eval ρ x
  cases h : R.eval ρ x <;> norm_num

/-! ## Item 7: sharedRouterAmalgClass -/

/-- The amalgamation class where two concept families share a router parameter.
    The agreement relation forces the router parameter to be shared (ρ₁ = ρ₂),
    yielding the class of patchEval(e₁, e₂, r)(θ₁, θ₂, ρ). -/
noncomputable def sharedRouterAmalgClass
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ Ρ : Type*}
    [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] [MeasurableSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool) : ConceptClass X Bool :=
  amalgClass (Prod.snd : Θ₁ × Ρ → Ρ) (Prod.snd : Θ₂ × Ρ → Ρ)
    (fun p : (Θ₁ × Ρ) × (Θ₂ × Ρ) => patchEval e₁ e₂ r (p.1.1, p.2.1, p.1.2))

/-- The shared-router amalgamation class equals the range of patchEval. -/
theorem sharedRouterAmalgClass_eq_patchRange
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ Ρ : Type*}
    [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] [MeasurableSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool) :
    sharedRouterAmalgClass e₁ e₂ r = Set.range (patchEval e₁ e₂ r) := by
  ext h
  simp only [sharedRouterAmalgClass, amalgClass, relParamClass, agreementRel,
    Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have heq : p.1.2 = p.2.2 := hp
    exact ⟨(p.1.1, p.2.1, p.1.2), by simp [heq]⟩
  · rintro ⟨⟨θ₁, θ₂, ρ⟩, rfl⟩
    exact ⟨((θ₁, ρ), (θ₂, ρ)), rfl, rfl⟩

/-! ## Item 8: binaryAttentionPatch_wellBehaved -/

/-- Patching two Borel-parameterized concept families via a binary attention router
    yields a concept class satisfying WellBehavedVCMeasTarget. -/
theorem binaryAttentionPatch_wellBehaved
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    (A : BinaryAttentionRouterCode X)
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2)) :
    WellBehavedVCMeasTarget X (Set.range (patchEval e₁ e₂ A.route)) := by
  letI := A.instMeasΡ
  letI := A.instStdΡ
  exact patch_borel_param_wellBehavedVCMeasTarget e₁ e₂ A.route he₁ he₂ A.route_measurable

/-! ## Item 9: routerInterpolation_eq_binaryAttention -/

/-- Interpolation via a MeasurableRouterFamily equals interpolation via its
    attention representation. This follows directly from attentionOfRouter_route_eq. -/
theorem routerInterpolation_eq_binaryAttention
    {X : Type u} [MeasurableSpace X] {Θ₁ Θ₂ : Type*}
    [MeasurableSpace Θ₁] [MeasurableSpace Θ₂]
    (R : MeasurableRouterFamily X)
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool) :
    Set.range (patchEval e₁ e₂ R.eval) =
      Set.range (patchEval e₁ e₂ (attentionOfRouter R).route) := by
  congr 1
  funext ⟨θ₁, θ₂, ρ⟩; funext x
  simp only [patchEval, attentionOfRouter_route_eq]
