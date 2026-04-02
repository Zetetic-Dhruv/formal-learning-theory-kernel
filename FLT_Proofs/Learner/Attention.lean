/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Learner.Closure
import FLT_Proofs.Complexity.Attention
import FLT_Proofs.Complexity.FiniteRouting

/-!
# Attention-Based Learners

Parametric learner families whose hypothesis selection is jointly measurable,
and their specialization to binary attention routing.

## Main results

- `ParametricLearnerFamily`: a learner parameterized by a measurable space
- `ParametricLearnerFamily.toBatchLearner`: conversion to BatchLearner
- `ParametricLearnerFamily.instMeasurableBatchLearner`: the induced learner is measurable
- `ParametricBinaryAttentionLearner`: attention-routed parametric learner
- `ParametricBinaryAttentionLearner.instMBL`: measurability of attention learner

## References

- Learner/Core.lean (BatchLearner, MeasurableBatchLearner)
- Learner/Closure.lean (combineLearner, concatLearner)
- Complexity/Attention.lean (BinaryAttentionRouterCode, route_measurable)
-/

universe u

open Classical
open MeasureTheory Set

/-! ## Item 10: ParametricLearnerFamily -/

/-- A parametric learner family: a measurable parameter space with a jointly
    measurable evaluation map and a measurable parameter selection rule. -/
structure ParametricLearnerFamily (X : Type u) [MeasurableSpace X] where
  Params : Type u
  instMeasParams : MeasurableSpace Params
  eval : Params → Concept X Bool
  eval_meas : @Measurable (Params × X) Bool (instMeasParams.prod ‹MeasurableSpace X›)
    inferInstance (fun p => eval p.1 p.2)
  param_of_sample : {m : ℕ} → (Fin m → X × Bool) → Params
  param_meas : ∀ m, @Measurable (Fin m → X × Bool) Params inferInstance instMeasParams
    (fun S => @param_of_sample m S)

attribute [instance] ParametricLearnerFamily.instMeasParams

/-! ## Item 11: toBatchLearner + MeasurableBatchLearner -/

/-- Convert a ParametricLearnerFamily to a BatchLearner. -/
noncomputable def ParametricLearnerFamily.toBatchLearner
    {X : Type u} [MeasurableSpace X]
    (P : ParametricLearnerFamily X) : BatchLearner X Bool where
  hypotheses := Set.range P.eval
  learn := fun {m} S => P.eval (@P.param_of_sample m S)
  output_in_H := fun {m} S => ⟨@P.param_of_sample m S, rfl⟩

/-- The BatchLearner induced by a ParametricLearnerFamily is measurable. -/
instance ParametricLearnerFamily.instMeasurableBatchLearner
    {X : Type u} [MeasurableSpace X]
    (P : ParametricLearnerFamily X) :
    MeasurableBatchLearner X P.toBatchLearner where
  eval_measurable m := by
    -- Goal: Measurable (fun p : (Fin m → X × Bool) × X => P.eval (P.param_of_sample p.1) p.2)
    -- = P.eval_meas ∘ (P.param_meas m ∘ fst, snd)
    letI := P.instMeasParams
    show Measurable (fun p : (Fin m → X × Bool) × X => P.eval (P.param_of_sample p.1) p.2)
    exact P.eval_meas.comp
      (Measurable.prodMk ((P.param_meas m).comp measurable_fst) measurable_snd)

/-! ## Item 12: ParametricBinaryAttentionLearner -/

/-- A parametric learner that uses binary attention routing to combine two experts.
    All parameters (router scores, expert evaluations) come from a single parameter
    space, representing the full parameter vector of a transformer-like architecture. -/
structure ParametricBinaryAttentionLearner (X : Type u) [MeasurableSpace X] where
  Params : Type u
  instMeasParams : MeasurableSpace Params
  instStdParams : @StandardBorelSpace Params instMeasParams
  leftScore : Params → X → ℝ
  rightScore : Params → X → ℝ
  leftScore_meas : @Measurable (Params × X) ℝ (instMeasParams.prod ‹MeasurableSpace X›)
    inferInstance (fun p => leftScore p.1 p.2)
  rightScore_meas : @Measurable (Params × X) ℝ (instMeasParams.prod ‹MeasurableSpace X›)
    inferInstance (fun p => rightScore p.1 p.2)
  leftExpert : Params → Concept X Bool
  rightExpert : Params → Concept X Bool
  leftExpert_meas : @Measurable (Params × X) Bool (instMeasParams.prod ‹MeasurableSpace X›)
    inferInstance (fun p => leftExpert p.1 p.2)
  rightExpert_meas : @Measurable (Params × X) Bool (instMeasParams.prod ‹MeasurableSpace X›)
    inferInstance (fun p => rightExpert p.1 p.2)
  param_of_sample : {m : ℕ} → (Fin m → X × Bool) → Params
  param_meas : ∀ m, @Measurable (Fin m → X × Bool) Params inferInstance instMeasParams
    (fun S => @param_of_sample m S)

attribute [instance] ParametricBinaryAttentionLearner.instMeasParams
attribute [instance] ParametricBinaryAttentionLearner.instStdParams

/-- Extract the BinaryAttentionRouterCode from a ParametricBinaryAttentionLearner. -/
noncomputable def ParametricBinaryAttentionLearner.routerCode
    {X : Type u} [MeasurableSpace X]
    (T : ParametricBinaryAttentionLearner X) : BinaryAttentionRouterCode X where
  Ρ := T.Params
  instMeasΡ := T.instMeasParams
  instStdΡ := T.instStdParams
  scoreL := T.leftScore
  scoreR := T.rightScore
  scoreL_meas := T.leftScore_meas
  scoreR_meas := T.rightScore_meas

/-- Convert a ParametricBinaryAttentionLearner to a ParametricLearnerFamily.
    The evaluation map routes through attention: if the router selects left,
    use the left expert; otherwise use the right expert. All use the same
    parameter θ (diagonal embedding into the triple (θ, θ, θ)). -/
noncomputable def ParametricBinaryAttentionLearner.toParametricLearnerFamily
    {X : Type u} [MeasurableSpace X]
    (T : ParametricBinaryAttentionLearner X) : ParametricLearnerFamily X where
  Params := T.Params
  instMeasParams := T.instMeasParams
  eval := fun θ x => if T.routerCode.route θ x then T.leftExpert θ x else T.rightExpert θ x
  eval_meas := by
    letI := T.instMeasParams
    -- The routing set: {p : Params × X | route p.1 p.2 = true}
    have hroute : MeasurableSet {p : T.Params × X | T.routerCode.route p.1 p.2 = true} :=
      T.routerCode.route_measurable (measurableSet_singleton true)
    exact Measurable.piecewise hroute T.leftExpert_meas T.rightExpert_meas
  param_of_sample := T.param_of_sample
  param_meas := T.param_meas

/-- The attention-based learner satisfies MeasurableBatchLearner. -/
instance ParametricBinaryAttentionLearner.instMBL
    {X : Type u} [MeasurableSpace X]
    (T : ParametricBinaryAttentionLearner X) :
    MeasurableBatchLearner X T.toParametricLearnerFamily.toBatchLearner :=
  ParametricLearnerFamily.instMeasurableBatchLearner T.toParametricLearnerFamily

/-! ## Item 17: ParametricFiniteHeadAttentionLearner -/

/-- A parametric learner that uses k-head attention routing to combine k experts.
    All parameters (router scores, expert evaluations) come from a single parameter
    space Params, with diagonal embedding into (Params, Params) for the
    multiPatchEval interface. -/
structure ParametricFiniteHeadAttentionLearner (X : Type u) [MeasurableSpace X] (k : ℕ) where
  Params : Type u
  instMeasParams : MeasurableSpace Params
  instStdParams : @StandardBorelSpace Params instMeasParams
  score : Params → X → Fin k → ℝ
  score_meas : ∀ (i : Fin k), @Measurable (Params × X) ℝ
    (instMeasParams.prod ‹MeasurableSpace X›) inferInstance (fun p => score p.1 p.2 i)
  expert : Params → Fin k → Concept X Bool
  expert_meas : ∀ (i : Fin k), @Measurable (Params × X) Bool
    (instMeasParams.prod ‹MeasurableSpace X›) inferInstance (fun p => expert p.1 i p.2)
  param_of_sample : {m : ℕ} → (Fin m → X × Bool) → Params
  param_meas : ∀ m, @Measurable (Fin m → X × Bool) Params inferInstance instMeasParams
    (fun S => @param_of_sample m S)

attribute [instance] ParametricFiniteHeadAttentionLearner.instMeasParams
attribute [instance] ParametricFiniteHeadAttentionLearner.instStdParams

/-- Extract the FiniteScoreRouterCode from a ParametricFiniteHeadAttentionLearner. -/
noncomputable def ParametricFiniteHeadAttentionLearner.routerCode
    {X : Type u} [MeasurableSpace X] {k : ℕ}
    (T : ParametricFiniteHeadAttentionLearner X k) : FiniteScoreRouterCode X k where
  Ρ := T.Params
  instMeasΡ := T.instMeasParams
  instStdΡ := T.instStdParams
  score := T.score
  score_meas := T.score_meas

/-! ## Item 18: Conversion to ParametricLearnerFamily + MeasurableBatchLearner -/

/-- Convert a ParametricFiniteHeadAttentionLearner to a ParametricLearnerFamily.
    Uses diagonal embedding θ ↦ (θ, θ) for multiPatchEval(expert, route)(θ, θ). -/
noncomputable def ParametricFiniteHeadAttentionLearner.toParametricLearnerFamily
    {X : Type u} [MeasurableSpace X] {k : ℕ}
    (T : ParametricFiniteHeadAttentionLearner X k) (hk : 0 < k) :
    ParametricLearnerFamily X where
  Params := T.Params
  instMeasParams := T.instMeasParams
  eval := fun θ x => multiPatchEval T.expert (T.routerCode.route hk) (θ, θ) x
  eval_meas := by
    letI := T.instMeasParams
    -- multiPatchEval_measurable gives: Measurable (fun p : (Params × Params) × X => ...)
    -- We need: Measurable (fun p : Params × X => multiPatchEval expert route (p.1, p.1) p.2)
    -- = (multiPatchEval_measurable ...).comp (diagonal embedding)
    have hmulti := multiPatchEval_measurable T.expert (T.routerCode.route hk)
      T.expert_meas (T.routerCode.route_measurable hk)
    -- diagonal embedding: Params × X → (Params × Params) × X
    -- (θ, x) ↦ ((θ, θ), x)
    have hdiag : Measurable (fun p : T.Params × X => ((p.1, p.1), p.2) :
        T.Params × X → (T.Params × T.Params) × X) :=
      (measurable_fst.prodMk measurable_fst).prodMk measurable_snd
    exact hmulti.comp hdiag
  param_of_sample := T.param_of_sample
  param_meas := T.param_meas

/-- The finite-head attention-based learner satisfies MeasurableBatchLearner. -/
instance ParametricFiniteHeadAttentionLearner.instMBL'
    {X : Type u} [MeasurableSpace X] {k : ℕ}
    (T : ParametricFiniteHeadAttentionLearner X k) (hk : 0 < k) :
    MeasurableBatchLearner X (T.toParametricLearnerFamily hk).toBatchLearner :=
  ParametricLearnerFamily.instMeasurableBatchLearner (T.toParametricLearnerFamily hk)
