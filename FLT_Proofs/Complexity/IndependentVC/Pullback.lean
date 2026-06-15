/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.VCDimension

/-!
# Contravariant functoriality of VC dimension

Precomposing every concept of a class with a map `f : Y → X` can only decrease the VC dimension.
A set shattered by the pulled-back class forces `f` to be injective on it: otherwise two of its
points share every label, so a labelling separating them is unrealizable. The injective image then
has the same cardinality and is shattered by the original class.

Every later capacity bridge is a pullback along a feature map, so this is the composition tool.
Restriction to a subset is the case `f = Subtype.val`, and a bijection gives equality, which is the
domain-relabelling invariance of the VC dimension.

## Main results

* `pullback`: the pullback of a concept class along a map of domains.
* `vcDim_pullback_le`: the VC dimension is monotone-decreasing under pullback.
-/

universe u v

variable {X : Type u} {Y : Type v}

/-- The pullback of a concept class along `f : Y → X`, obtained by precomposing each concept. -/
def pullback (f : Y → X) (C : ConceptClass X Bool) : ConceptClass Y Bool :=
  (· ∘ f) '' C

/-- **Contravariant functoriality of VC dimension.** `VCDim Y (pullback f C) ≤ VCDim X C`. -/
theorem vcDim_pullback_le (f : Y → X) (C : ConceptClass X Bool) :
    VCDim Y (pullback f C) ≤ VCDim X C := by
  classical
  unfold VCDim
  refine iSup₂_le fun S hS => ?_
  have hinj : Set.InjOn f S := by
    intro a ha b hb hfab
    by_contra hne
    obtain ⟨c', ⟨c, _, rfl⟩, hc'eq⟩ := hS (fun y => decide ((y : Y) = a))
    have ea : c (f a) = true := by simpa using hc'eq ⟨a, ha⟩
    have eb : c (f b) = false := by
      have h := hc'eq ⟨b, hb⟩
      simp only [Function.comp_apply] at h
      rw [h]
      exact decide_eq_false (fun hba => hne hba.symm)
    rw [hfab, eb] at ea
    exact absurd ea (by decide)
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  refine le_iSup₂_of_le (S.image f) ?_ le_rfl
  intro g
  obtain ⟨c', ⟨c, hcC, rfl⟩, hc'eq⟩ :=
    hS (fun y => g ⟨f (y : Y), Finset.mem_image_of_mem f y.2⟩)
  refine ⟨c, hcC, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨y, hy, hfy⟩ := Finset.mem_image.mp hz
  have h := hc'eq ⟨y, hy⟩
  simp only [Function.comp_apply] at h
  subst hfy
  exact h
