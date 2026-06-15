/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.Pullback

/-!
# The dual concept class and the bidual lower bound

The dual of a concept class swaps the roles of points and concepts: each point `x : X` becomes the
evaluation concept `c ↦ c x` on the new domain `↥C`. Iterating gives the bidual, a class over
`↥(dualClass C)`.

The bidual recovers the primal up to a pullback: precomposing the bidual with the evaluation map
`x ↦ (c ↦ c x)` reproduces `C` exactly (`pullback_biDual_eq`). Contravariant functoriality of the VC
dimension (`vcDim_pullback_le`) then gives the **bidual lower bound** `VCDim X C ≤ VCDim (biDual C)`.
This is the direction complementary to Assouad's upper bound `VCDim(dual) ≤ 2^(VCDim+1) − 1`; together
they sandwich the dual dimension and, applied to the dual, give the dual lower bound
`VCDim(dual) ≥ ⌈log₂(VCDim + 1)⌉`.

Reference: P. Assouad, *Densité et dimension*, Annales de l'Institut Fourier 33 (1983), 233–282.

## Main results

* `dualClass`: the dual concept class (evaluation concepts on `↥C`).
* `pullback_biDual_eq`: the bidual pulled back along evaluation is the original class.
* `vcDim_le_biDual`: the VC dimension of a class is at most that of its bidual.
-/

universe u

variable {X : Type u}

/-- The **dual concept class**: each point `x : X` gives the evaluation concept `c ↦ c x` on the new
domain `↥C`. The dual class collects these over all points. -/
def dualClass (C : ConceptClass X Bool) : ConceptClass ↥C Bool :=
  { f | ∃ x : X, ∀ c : ↥C, f c = c.val x }

/-- The evaluation concept at a point `x`: the map `c ↦ c x` on `↥C`. -/
def evalConcept (C : ConceptClass X Bool) (x : X) : ↥C → Bool := fun c => c.val x

/-- Each evaluation concept belongs to the dual class. -/
theorem evalConcept_mem (C : ConceptClass X Bool) (x : X) : evalConcept C x ∈ dualClass C :=
  ⟨x, fun _ => rfl⟩

/-- **The bidual recovers the primal.** Pulling the bidual back along the evaluation embedding
`x ↦ (c ↦ c x)` reproduces `C` exactly: every bidual concept `φ ↦ φ z` precomposed with evaluation
is the concept `z`, and these range over all of `C`. -/
theorem pullback_biDual_eq (C : ConceptClass X Bool) :
    pullback (fun x => (⟨evalConcept C x, evalConcept_mem C x⟩ : ↥(dualClass C)))
      (dualClass (dualClass C)) = C := by
  ext h
  simp only [pullback, Set.mem_image]
  constructor
  · rintro ⟨g, ⟨z, hz⟩, rfl⟩
    have heq : (g ∘ fun x => (⟨evalConcept C x, evalConcept_mem C x⟩ : ↥(dualClass C)))
        = z.val := by
      funext x
      show g (⟨evalConcept C x, evalConcept_mem C x⟩ : ↥(dualClass C)) = z.val x
      simp only [hz, evalConcept]
    show (g ∘ fun x => (⟨evalConcept C x, evalConcept_mem C x⟩ : ↥(dualClass C))) ∈ C
    rw [heq]; exact z.2
  · intro hc
    exact ⟨fun φ => φ.val ⟨h, hc⟩, ⟨⟨h, hc⟩, fun _ => rfl⟩, by funext x; rfl⟩

/-- **Bidual lower bound.** The VC dimension of a class is at most that of its bidual. Immediate from
`pullback_biDual_eq` and the contravariance of the VC dimension under pullback. -/
theorem vcDim_le_biDual (C : ConceptClass X Bool) :
    VCDim X C ≤ VCDim ↥(dualClass C) (dualClass (dualClass C)) := by
  have h := vcDim_pullback_le
    (fun x => (⟨evalConcept C x, evalConcept_mem C x⟩ : ↥(dualClass C))) (dualClass (dualClass C))
  rwa [pullback_biDual_eq C] at h
