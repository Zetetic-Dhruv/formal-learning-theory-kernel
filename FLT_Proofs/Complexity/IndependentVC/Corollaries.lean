/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.Pullback
import FLT_Proofs.Complexity.IndependentVC.BooleanComb

/-!
# Corollaries of the VC-dimension calculus

Two consequences of the pullback bound and the De Morgan lemma:

* restricting a concept class to a subset can only decrease its VC dimension, and
* negating the combiner of a Boolean combination leaves the VC dimension unchanged.

The second is the VC-dimension form of De Morgan duality: a bound proved for unions transfers to
intersections, since intersection is the negated combiner applied to negated classes.

## Main results

* `vcDim_restrict_le`: restriction to a subset decreases the VC dimension.
* `vcDim_booleanComb_not`: the VC dimension is invariant under negating the combiner.
-/

universe u

variable {X : Type u} {k : ℕ}

/-- Restricting a concept class to a subset can only decrease its VC dimension, as the case
`f = Subtype.val` of the pullback bound. -/
theorem vcDim_restrict_le (C : ConceptClass X Bool) (A : Set X) :
    VCDim A (pullback (Subtype.val : A → X) C) ≤ VCDim X C :=
  vcDim_pullback_le _ C

/-- Negating the combiner of a Boolean combination leaves the VC dimension unchanged, since the
negated combination is the complement of the original and complementation preserves VC dimension. -/
theorem vcDim_booleanComb_not (φ : (Fin k → Bool) → Bool) (C : Fin k → ConceptClass X Bool) :
    VCDim X (booleanComb (fun b => !(φ b)) C) = VCDim X (booleanComb φ C) := by
  rw [← negClass_booleanComb, vcDim_negClass]
