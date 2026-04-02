/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Learner.Core
import FLT_Proofs.Complexity.Generalization

/-!
# Closure of Measurable Learners under Combiners and Selection

The algebra of `MeasurableBatchLearner`s is closed under:
- arbitrary Boolean combiners (`combineLearner`)
- majority-vote boosting (`boostLearner`)
- measurable-set interpolation (`interpLearner`)
- countable selection (`concatLearner`)

-/

open Classical

universe u

/-! ## Part 1: combineLearner -/

noncomputable def combineLearner
    {X : Type u} [MeasurableSpace X]
    (k : ℕ) (F : X → (Fin k → Bool) → Bool)
    (L : Fin k → BatchLearner X Bool) : BatchLearner X Bool where
  hypotheses := {h | ∃ hs : Fin k → Concept X Bool,
    (∀ i, hs i ∈ (L i).hypotheses) ∧
    h = fun x => F x (fun i => hs i x)}
  learn := fun {m} S x => F x (fun i => (L i).learn S x)
  output_in_H := fun {m} S => by
    simp only [Set.mem_setOf_eq]
    exact ⟨fun i => (L i).learn S, fun i => (L i).output_in_H S, rfl⟩

/-! ## Part 2: Measurability of combineLearner -/

theorem measurableBatchLearner_combine
    {X : Type u} [MeasurableSpace X]
    (k : ℕ) (F : X → (Fin k → Bool) → Bool)
    (hF : Measurable (fun p : X × (Fin k → Bool) => F p.1 p.2))
    (L : Fin k → BatchLearner X Bool)
    (hL : ∀ i, MeasurableBatchLearner X (L i)) :
    MeasurableBatchLearner X (combineLearner k F L) where
  eval_measurable m := by
    show Measurable (fun p : (Fin m → X × Bool) × X => F p.2 (fun i => (L i).learn p.1 p.2))
    have hg : Measurable (fun p : (Fin m → X × Bool) × X =>
        (p.2, fun i => (L i).learn p.1 p.2) : (Fin m → X × Bool) × X → X × (Fin k → Bool)) :=
      Measurable.prodMk measurable_snd
        (measurable_pi_lambda _ (fun i => (hL i).eval_measurable m))
    exact hF.comp hg

/-! ## Part 3: Boost learner via majority vote -/

noncomputable def boostLearner
    {X : Type u} [MeasurableSpace X]
    (k : ℕ) (L : Fin k → BatchLearner X Bool) : BatchLearner X Bool :=
  combineLearner k (fun _ v => majority_vote k v) L

theorem measurableBatchLearner_boost
    {X : Type u} [MeasurableSpace X]
    (k : ℕ) (L : Fin k → BatchLearner X Bool)
    (hL : ∀ i, MeasurableBatchLearner X (L i)) :
    MeasurableBatchLearner X (boostLearner k L) := by
  apply measurableBatchLearner_combine
  · show Measurable (fun p : X × (Fin k → Bool) => majority_vote k p.2)
    have : Measurable (fun v : Fin k → Bool => majority_vote k v) := measurable_of_finite _
    exact this.comp measurable_snd
  · exact hL

/-! ## Part 4: Interpolation learner -/

noncomputable def interpLearner
    {X : Type u} [MeasurableSpace X]
    (A : Set X) (L₁ L₂ : BatchLearner X Bool) : BatchLearner X Bool :=
  combineLearner 2
    (fun x v => if x ∈ A then v 0 else v 1)
    (fun i => if i = 0 then L₁ else L₂)

theorem measurableBatchLearner_interp
    {X : Type u} [MeasurableSpace X]
    (A : Set X) (hA : MeasurableSet A)
    (L₁ L₂ : BatchLearner X Bool)
    (h₁ : MeasurableBatchLearner X L₁)
    (h₂ : MeasurableBatchLearner X L₂) :
    MeasurableBatchLearner X (interpLearner A L₁ L₂) := by
  apply measurableBatchLearner_combine
  · -- Measurable (fun p : X × (Fin 2 → Bool) => if p.1 ∈ A then p.2 0 else p.2 1)
    show Measurable (fun p : X × (Fin 2 → Bool) => if p.1 ∈ A then p.2 0 else p.2 1)
    apply Measurable.ite (measurable_fst hA)
    · exact (measurable_pi_apply 0).comp measurable_snd
    · exact (measurable_pi_apply 1).comp measurable_snd
  · intro i
    fin_cases i <;> simp <;> assumption

/-! ## Part 5: Uniform measurability for indexed families -/

class UniformMeasurableBatchFamily {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool) : Prop where
  eval_measurable : ∀ (m : ℕ),
    Measurable (fun p : ℕ × (Fin m → X × Bool) × X => (L p.1).learn p.2.1 p.2.2)

theorem UniformMeasurableBatchFamily.pointwise
    {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool) [hL : UniformMeasurableBatchFamily L]
    (n : ℕ) : MeasurableBatchLearner X (L n) where
  eval_measurable m :=
    (hL.eval_measurable m).comp (Measurable.prodMk measurable_const measurable_id)

/-! ## Part 6: Concat learner with measurable selection -/

noncomputable def concatLearner
    {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool)
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ) : BatchLearner X Bool where
  hypotheses := ⋃ n, (L n).hypotheses
  learn := fun S x => (L (sel S)).learn S x
  output_in_H := fun S => Set.mem_iUnion.mpr ⟨sel S, (L (sel S)).output_in_H S⟩

theorem measurableBatchLearner_concat
    {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool)
    [hL : UniformMeasurableBatchFamily L]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    (hsel : ∀ m, Measurable (fun S : Fin m → X × Bool => @sel m S)) :
    MeasurableBatchLearner X (concatLearner L sel) where
  eval_measurable m := by
    show Measurable (fun p : (Fin m → X × Bool) × X => (L (sel p.1)).learn p.1 p.2)
    -- Factor: (hL.eval_measurable m) ∘ (fun p => (sel p.1, p.1, p.2))
    exact (hL.eval_measurable m).comp
      (Measurable.prodMk ((hsel m).comp measurable_fst)
        (Measurable.prodMk measurable_fst measurable_snd))
