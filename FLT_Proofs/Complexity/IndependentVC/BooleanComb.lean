/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.VCDimension
import FLT_Proofs.Complexity.IndependentVC.Relabel

/-!
# Boolean combinations of concept classes

A fixed Boolean combiner `φ : (Fin k → Bool) → Bool` applied pointwise to `k` concept classes
produces a new class `booleanComb φ C`. Union and intersection are the cases where `φ` is the
join (`Finset.univ.sup`) and the meet (`Finset.univ.inf`).

This file records the algebra of these combinations against complementation. The two facts that do
the work later are:

* complementation is an involution (`negClass_negClass`), and
* complementing a combination is the same as combining with the complemented combiner
  (`negClass_booleanComb`).

Together with the join/meet De Morgan law for `Bool` these give the De Morgan duality between union
and intersection classes, so a bound proved for one transfers to the other.

## Main results

* `booleanComb`, `unionClass`, `interClass`: the pointwise combinations.
* `xorShift_xorShift`, `negClass_negClass`: the exclusive-or shift and complement are involutions.
* `negClass_booleanComb`: `negClass (booleanComb φ C) = booleanComb (!∘φ) C`.
-/

universe u

variable {X : Type u} {k : ℕ}

/-- The pointwise `k`-ary Boolean combination of classes `C` by a fixed combiner `φ`. -/
def booleanComb (φ : (Fin k → Bool) → Bool) (C : Fin k → ConceptClass X Bool) :
    ConceptClass X Bool :=
  { c | ∃ g : Fin k → (X → Bool), (∀ i, g i ∈ C i) ∧ c = fun x => φ (fun i => g i x) }

/-- The pointwise union of `k` classes (combine by the join). -/
def unionClass (C : Fin k → ConceptClass X Bool) : ConceptClass X Bool :=
  booleanComb (fun b => Finset.univ.sup b) C

/-- The pointwise intersection of `k` classes (combine by the meet). -/
def interClass (C : Fin k → ConceptClass X Bool) : ConceptClass X Bool :=
  booleanComb (fun b => Finset.univ.inf b) C

private theorem xor_xor_self (b u : Bool) : Bool.xor b (Bool.xor b u) = u := by
  cases b <;> cases u <;> rfl

/-- An exclusive-or shift by a fixed pattern is an involution on concept classes. -/
theorem xorShift_xorShift (a : X → Bool) (C : ConceptClass X Bool) :
    xorShift a (xorShift a C) = C := by
  unfold xorShift
  simp only [Set.image_image, xor_xor_self, Set.image_id']

/-- Complementation is an involution on concept classes. -/
theorem negClass_negClass (C : ConceptClass X Bool) : negClass (negClass C) = C :=
  xorShift_xorShift _ C

/-- Complementing a Boolean combination is the same as combining with the complemented combiner:
`negClass (booleanComb φ C) = booleanComb (fun b => !(φ b)) C`. -/
theorem negClass_booleanComb (φ : (Fin k → Bool) → Bool) (C : Fin k → ConceptClass X Bool) :
    negClass (booleanComb φ C) = booleanComb (fun b => !(φ b)) C := by
  unfold negClass xorShift booleanComb
  ext c
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c', ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨g, hg, ?_⟩
    funext x
    exact Bool.true_xor _
  · rintro ⟨g, hg, rfl⟩
    refine ⟨fun x => φ (fun i => g i x), ⟨g, hg, rfl⟩, ?_⟩
    funext x
    exact Bool.true_xor _
