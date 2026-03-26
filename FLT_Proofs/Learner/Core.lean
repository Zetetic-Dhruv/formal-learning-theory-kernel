/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Basic
import FLT_Proofs.Data
import FLT_Proofs.Computation

/-!
# Core Learner Types (BP₁: No Common Parent)

The three paradigm-specific learner types with incompatible signatures.
This is Break Point BP₁ — the type system cannot express "learner"
without choosing a paradigm.

## Break Point BP₁: No Common Learner Parent

- **PAC learner**: `{m : ℕ} → (Fin m → X × Y) → Concept X Y` (batch)
- **Online learner**: `State → X → Y` (sequential with internal state)
- **Gold learner**: `List (X × Y) → Concept X Y` (sequential, extensible)

No common parent captures all three without erasing the structure
that makes their theorems non-trivial.
-/

universe u v

-- BREAK POINT BP₁: No common learner parent type.
-- The three structures below share nothing in their Lean4 types.

/-- A batch learner (PAC paradigm): takes a finite sample, returns a hypothesis. -/
structure BatchLearner (X : Type u) (Y : Type v) where
  /-- The learner's hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- The learning algorithm: given a sample, produce a hypothesis -/
  learn : {m : ℕ} → (Fin m → X × Y) → Concept X Y
  /-- Output is in the hypothesis space -/
  output_in_H : ∀ {m : ℕ} (S : Fin m → X × Y), learn S ∈ hypotheses

/-- An online learner: receives instances one at a time, makes predictions sequentially. -/
structure OnlineLearner (X : Type u) (Y : Type v) where
  /-- Internal state type -/
  State : Type
  /-- Initial state -/
  init : State
  /-- Predict: given current state and new instance, output a prediction -/
  predict : State → X → Y
  /-- Update: given current state, instance, and revealed true label, update state -/
  update : State → X → Y → State

/-- A Gold-style learner (identification in the limit): receives a stream of data
    and at each step conjectures a hypothesis. -/
structure GoldLearner (X : Type u) (Y : Type v) where
  /-- The learner's conjecture given data seen so far -/
  conjecture : List (X × Y) → Concept X Y
