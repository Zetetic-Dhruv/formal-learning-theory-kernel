/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Basic
import FLT_Proofs.Complexity.Symmetrization

/-!
# Measurability Infrastructure for Learning Theory

This file defines the `MeasurableConceptClass` typeclass, which bundles
the measure-theoretic regularity conditions needed for PAC learning theory.

## Background

The Fundamental Theorem of Statistical Learning (PAC ↔ finite VC dimension)
requires measurability assumptions that are often left implicit in pen-and-paper
proofs. Krapp & Wirth (2024, arXiv:2410.10243) systematically extract these
conditions. This file formalizes them as Lean4 typeclass infrastructure.

The three bundled conditions are:
1. `mem_measurable`: every concept in C is a measurable function
2. `all_measurable`: all concepts X → Bool are measurable (for disagreement sets)
3. `wellBehaved`: the uniform convergence bad event is NullMeasurableSet
   (the `WellBehavedVC` condition from Symmetrization.lean)

Condition 3 is the non-trivial one. For countable concept classes, it holds
automatically. For uncountable classes, the existential quantifier in the UC event
{∃ h ∈ C, |TrueErr - EmpErr| ≥ ε} does not preserve MeasurableSet, and the
NullMeasurableSet weakening is needed. This was discovered during the Lean4
formalization (Session 7) and is a genuine measure-theoretic subtlety absent
from standard textbook presentations.

## Relationship to ad hoc predicates

This typeclass replaces explicit hypothesis threading in theorem signatures:
- `(hmeas_C : ∀ h ∈ C, Measurable h)` → `MeasurableConceptClass.mem_measurable`
- `(hc_meas : ∀ c : Concept X Bool, Measurable c)` → `MeasurableConceptClass.all_measurable`
- `(hWB : WellBehavedVC X C)` → `MeasurableConceptClass.wellBehaved`

Combined with `MeasurableBatchLearner` (Learner/Core.lean), these two typeclasses
provide the complete regularity infrastructure for PAC learning proofs.
-/

universe u

/-- A concept class with the measure-theoretic regularity needed for PAC theory.

    Bundles three conditions:
    1. Every concept in C is measurable
    2. All concepts are measurable (needed for disagreement set measurability)
    3. The UC bad event satisfies NullMeasurableSet (WellBehavedVC)

    Condition 3 is the deep one: for uncountable C, the existential
    {∃ h ∈ C, |TrueErr - EmpErr| ≥ ε} is NOT MeasurableSet in general.
    WellBehavedVC asserts it is NullMeasurableSet, which suffices for
    integration (lintegral_indicator_one₀). -/
class MeasurableConceptClass (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop where
  /-- Every concept in C is measurable -/
  mem_measurable : ∀ h ∈ C, Measurable h
  /-- All concepts X → Bool are measurable (for disagreement sets) -/
  all_measurable : ∀ c : Concept X Bool, Measurable c
  /-- Uniform convergence bad event is NullMeasurableSet -/
  wellBehaved : WellBehavedVC X C

/-! ## Bridge API: typeclass → explicit hypotheses

These bridge lemmas allow incremental migration of existing theorems.
Each theorem currently takes explicit `hmeas_C`, `hc_meas`, `hWB` arguments.
With these bridges, callers can write:
  `MeasurableConceptClass.hmeas_C C`
instead of threading the hypothesis manually. -/

theorem MeasurableConceptClass.hmeas_C
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : MeasurableConceptClass X C] :
    ∀ c ∈ C, Measurable c :=
  h.mem_measurable

theorem MeasurableConceptClass.hc_meas
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : MeasurableConceptClass X C] :
    ∀ c : Concept X Bool, Measurable c :=
  h.all_measurable

theorem MeasurableConceptClass.hWB
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : MeasurableConceptClass X C] :
    WellBehavedVC X C :=
  h.wellBehaved

/-! ## Instances

TODO: Add automatic instances for common cases:
- Finite concept classes (WellBehavedVC holds automatically)
- Concept classes over MeasurableSingletonClass spaces
- Countable concept classes (existential preserves measurability)
-/
