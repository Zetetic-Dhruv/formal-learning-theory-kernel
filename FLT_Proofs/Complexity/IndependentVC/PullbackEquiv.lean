/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.Pullback

/-!
# Functoriality laws and bijection-invariance of VC dimension

Pullback composes contravariantly and is the identity on the identity map. Applying the pullback
bound in both directions of a bijection of the domain shows that a relabelling of the domain leaves
the VC dimension unchanged. Together with the codomain symmetries (complementation, exclusive-or
shift), this gives the full relabelling invariance of the VC dimension: it depends only on the
incidence between concepts and points, not on the names of either.

## Main results

* `pullback_pullback`, `pullback_id`: the functoriality laws.
* `vcDim_pullback_equiv`: a bijection of the domain preserves the VC dimension.
-/

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Pullback composes contravariantly: pulling back along `g` then `f` is pulling back along
`f ∘ g`. -/
theorem pullback_pullback (f : Y → X) (g : Z → Y) (C : ConceptClass X Bool) :
    pullback g (pullback f C) = pullback (f ∘ g) C := by
  ext c
  simp only [pullback, Set.mem_image]
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b ∘ f, ⟨b, hb, rfl⟩, rfl⟩

/-- Pulling back along the identity is the identity. -/
theorem pullback_id (C : ConceptClass X Bool) : pullback (id : X → X) C = C := by
  unfold pullback
  simp only [Function.comp_id]
  exact Set.image_id' C

/-- **Bijection-invariance of VC dimension.** A bijection `e` of the domain preserves the VC
dimension: `VCDim Y (pullback e C) = VCDim X C`. This is the domain-relabelling symmetry. -/
theorem vcDim_pullback_equiv (e : Y ≃ X) (C : ConceptClass X Bool) :
    VCDim Y (pullback (e : Y → X) C) = VCDim X C := by
  apply le_antisymm (vcDim_pullback_le _ C)
  have hC : pullback (e.symm : X → Y) (pullback (e : Y → X) C) = C := by
    rw [pullback_pullback, Equiv.self_comp_symm, pullback_id]
  calc VCDim X C
      = VCDim X (pullback (e.symm : X → Y) (pullback (e : Y → X) C)) := by rw [hC]
    _ ≤ VCDim Y (pullback (e : Y → X) C) := vcDim_pullback_le _ _
