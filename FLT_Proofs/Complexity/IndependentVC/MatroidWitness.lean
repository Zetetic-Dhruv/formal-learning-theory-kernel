/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.VCDimension

/-!
# VC dimension is not a rank function on the concept-class lattice

The VC dimension is monotone, but it fails the subadditivity that a matroid or polymatroid rank
function must satisfy. The witness is small and explicit: on a one-point domain, two singleton
classes each have VC dimension zero, yet their collection union shatters the point, so its VC
dimension is one.

The substantive form of this failure, on the pointwise Boolean lattice, is asymptotically sharp:
the k-fold union of a class of VC dimension `d` has VC dimension `Θ(d · k · log k)`, exceeding the
`O(d · k)` any subadditive rank would force (Blumer, Ehrenfeucht, Haussler, Warmuth, J. ACM
36(4):929–965, 1989, Lemma 3.2.3; lower bound Eisenstat, Angluin, Inf. Process. Lett.
101(5):181–184, 2007). That bound is not formalized here. This file records the elementary
collection-lattice witness, which already refutes the rank-function property.

This does not contradict the oriented-matroid correspondence, under which the rank of an oriented
matroid equals the VC dimension of its tope graph (Goodman, Pollack, Discrete Comput. Geom., 1990).
That correspondence concerns arrangement-derived classes, not the collection lattice considered here.

## Main results

* `vcDim_singleton_eq_zero`: a one-concept class has VC dimension zero.
* `vcDim_not_subadditive_collectionUnion`: VC dimension is not subadditive under collection union.
-/

universe u

variable {X : Type u}

/-- A concept class consisting of a single concept has VC dimension zero: one concept realizes only
one labelling of any point, so no nonempty set is shattered. -/
theorem vcDim_singleton_eq_zero (c₀ : X → Bool) :
    VCDim X ({c₀} : ConceptClass X Bool) = 0 := by
  apply le_antisymm _ (zero_le _)
  unfold VCDim
  refine iSup₂_le fun S hS => ?_
  suffices h : S = ∅ by rw [h]; simp
  by_contra hS_ne
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hS_ne
  obtain ⟨c, hc, hcf⟩ := hS (fun y => !(c₀ (y : X)))
  obtain rfl : c = c₀ := hc
  have hcontra := hcf ⟨x, hx⟩
  simp at hcontra

/-- **VC dimension is not subadditive under collection union.** Two singleton classes on a one-point
domain each have VC dimension zero, but their collection union shatters the point, so its VC
dimension is positive. A subadditive (hence matroid or polymatroid) rank would force
`r (A ∪ B) ≤ r A + r B`. -/
theorem vcDim_not_subadditive_collectionUnion :
    ∃ (X : Type) (A B : ConceptClass X Bool), VCDim X A + VCDim X B < VCDim X (A ∪ B) := by
  refine ⟨Unit, {fun _ => false}, {fun _ => true}, ?_⟩
  rw [vcDim_singleton_eq_zero, vcDim_singleton_eq_zero, add_zero]
  refine lt_of_lt_of_le (b := 1) (by norm_num) ?_
  unfold VCDim
  refine le_iSup₂_of_le {()} ?_ (by simp)
  intro f
  cases hv : f ⟨(), Finset.mem_singleton_self ()⟩
  · refine ⟨fun _ => false, Or.inl rfl, fun x => ?_⟩
    have hx : x = ⟨(), Finset.mem_singleton_self ()⟩ := Subtype.ext (Subsingleton.elim _ _)
    rw [hx]; exact hv.symm
  · refine ⟨fun _ => true, Or.inr rfl, fun x => ?_⟩
    have hx : x = ⟨(), Finset.mem_singleton_self ()⟩ := Subtype.ext (Subsingleton.elim _ _)
    rw [hx]; exact hv.symm
