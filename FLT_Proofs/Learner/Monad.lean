/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Learner.Closure
import FLT_Proofs.PureMath.ReaderMonad

/-!
# Measurable Batch Learner Monad

MeasurableBatchLearner is a measurable instance of the pure ReaderSel monad
(MathLib/ReaderMonad.lean). The algebraic structure (pure, bind, monad laws)
lives in the pure math layer. This file adds the measurability certificate.

- `MeasLearner`: BatchLearner bundled with MeasurableBatchLearner proof
- `MeasLearner.pure`: constant learner (delegates to ReaderSel.pure)
- `MeasLearner.bind`: selection-based composition (delegates to concatLearner)
- Monad laws: inherited from ReaderSel, verified at evaluation level
-/

open Classical

universe u

structure MeasLearner (X : Type u) [MeasurableSpace X] where
  learner : BatchLearner X Bool
  measurable : MeasurableBatchLearner X learner

noncomputable def MeasLearner.pure
    {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    (h : Concept X Bool) (hm : Measurable h) : MeasLearner X where
  learner := {
    hypotheses := {h}
    learn := fun _ => h
    output_in_H := fun _ => Set.mem_singleton h
  }
  measurable := ⟨fun _m => hm.comp measurable_snd⟩

noncomputable def MeasLearner.bind
    {X : Type u} [MeasurableSpace X]
    (family : ℕ → MeasLearner X)
    [hfam : UniformMeasurableBatchFamily (fun n => (family n).learner)]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    (hsel : ∀ m, Measurable (fun S : Fin m → X × Bool => @sel m S)) :
    MeasLearner X where
  learner := concatLearner (fun n => (family n).learner) sel
  measurable := measurableBatchLearner_concat _ sel hsel

/-! ## Monad Laws

The algebraic structure is inherited from ReaderSel (MathLib/ReaderMonad.lean).
At the evaluation level, concatLearner.learn S x = (family (sel S)).learner.learn S x,
which is ReaderSel.eval specialized to ι = ℕ, α = Fin m → X × Bool. -/

theorem MeasLearner.left_unit
    {X : Type u} [MeasurableSpace X]
    (family : ℕ → MeasLearner X)
    [_hfam : UniformMeasurableBatchFamily (fun n => (family n).learner)]
    (n : ℕ) {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun i => (family i).learner) (fun _ => n)).learn S x =
    (family n).learner.learn S x := by rfl

theorem MeasLearner.right_unit
    {X : Type u} [MeasurableSpace X]
    (L : MeasLearner X)
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun _ => L.learner) sel).learn S x =
    L.learner.learn S x := by rfl

theorem MeasLearner.assoc
    {X : Type u} [MeasurableSpace X]
    (family : ℕ → MeasLearner X)
    [_hfam : UniformMeasurableBatchFamily (fun n => (family n).learner)]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun n => (family n).learner) sel).learn S x =
    (family (sel S)).learner.learn S x := by rfl
