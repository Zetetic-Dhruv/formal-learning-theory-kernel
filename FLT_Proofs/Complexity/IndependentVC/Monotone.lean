/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.VCDimension

/-!
# Monotonicity of VC dimension in the concept class

Enlarging a concept class can only enlarge what it shatters, so the VC dimension is monotone in the
class. The intersection bound is an immediate consequence.

## Main results

* `shatters_mono`: shattering is monotone in the class.
* `vcDim_mono`: the VC dimension is monotone in the class.
* `vcDim_inter_le_min`: the VC dimension of an intersection is at most the minimum.
-/

universe u

variable {X : Type u}

/-- Shattering is monotone in the concept class: a labelling realized inside `C` is realized inside
any larger class `D`. -/
theorem shatters_mono {C D : ConceptClass X Bool} (h : C ⊆ D) {S : Finset X}
    (hS : Shatters X C S) : Shatters X D S := by
  intro f
  obtain ⟨c, hc, hcf⟩ := hS f
  exact ⟨c, h hc, hcf⟩

/-- The VC dimension is monotone in the concept class. -/
theorem vcDim_mono {C D : ConceptClass X Bool} (h : C ⊆ D) : VCDim X C ≤ VCDim X D := by
  unfold VCDim
  refine iSup_le fun S => iSup_le fun hS => ?_
  exact le_iSup_of_le S (le_iSup_of_le (shatters_mono h hS) le_rfl)

/-- The VC dimension of an intersection is at most the minimum of the two VC dimensions. -/
theorem vcDim_inter_le_min (C D : ConceptClass X Bool) :
    VCDim X (C ∩ D) ≤ min (VCDim X C) (VCDim X D) :=
  le_min (vcDim_mono Set.inter_subset_left) (vcDim_mono Set.inter_subset_right)
