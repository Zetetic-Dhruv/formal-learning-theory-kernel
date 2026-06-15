/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.BooleanComb

/-!
# The input side of De Morgan duality for Boolean combinations

Combining the complemented classes is the same as combining the original classes with a combiner
whose inputs are negated. Together with `negClass_booleanComb` (which negates the output), this
gives the full De Morgan calculus relating unions and intersections of concept classes.

## Main results

* `booleanComb_negClass_inputs`: combining negated classes negates the combiner's inputs.
-/

universe u

variable {X : Type u} {k : ℕ}

/-- Combining the complemented classes is combining the original classes with the input-negated
combiner: `booleanComb φ (negClass ∘ C) = booleanComb (fun b => φ (! ∘ b)) C`. -/
theorem booleanComb_negClass_inputs (φ : (Fin k → Bool) → Bool) (C : Fin k → ConceptClass X Bool) :
    booleanComb φ (fun i => negClass (C i)) = booleanComb (fun b => φ (fun i => !(b i))) C := by
  ext c
  simp only [booleanComb, negClass, xorShift, Set.mem_setOf_eq]
  constructor
  · rintro ⟨H, hH, rfl⟩
    choose g hg hgeq using hH
    refine ⟨g, hg, ?_⟩
    funext x
    refine congrArg φ (funext fun i => ?_)
    rw [← hgeq i]
    exact Bool.true_xor _
  · rintro ⟨g, hg, rfl⟩
    refine ⟨fun i => fun x => Bool.xor true (g i x), fun i => ⟨g i, hg i, rfl⟩, ?_⟩
    funext x
    refine congrArg φ (funext fun i => ?_)
    exact (Bool.true_xor _).symm
