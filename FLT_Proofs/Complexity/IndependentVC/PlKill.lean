/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.VCDimension

/-!
# Finite VC dimension is not preserved under unbounded Boolean closure

The class of all finite-support concepts on an infinite domain shatters every finite set, so it has
infinite VC dimension. This is the boundary that makes the arity bound in the quantitative
Boolean-combination estimates essential: closing a class under unbounded union takes finite VC
dimension to infinite.

The statement is existential, not universal. It is false that every class of positive VC dimension
has an infinite-VC unbounded closure; for instance the two-element constant class is its own union
closure and keeps VC dimension one. The blow-up needs unboundedly many independent concepts, which
the singletons inside the finite-support class supply.

## Main results

* `finiteSupportClass`: the class of concepts with finite support.
* `shatters_finiteSupportClass`: it shatters every finite set.
* `vcDim_finiteSupportClass_top`: it has infinite VC dimension on an infinite domain.
-/

universe u

variable {X : Type u}

/-- The class of concepts whose support is finite. -/
def finiteSupportClass (X : Type u) : ConceptClass X Bool := { c | Set.Finite {x | c x} }

/-- The finite-support class shatters every finite set: the indicator of the positive part of any
labelling has finite support and realizes that labelling. -/
theorem shatters_finiteSupportClass (S : Finset X) :
    Shatters X (finiteSupportClass X) S := by
  classical
  intro f
  refine ⟨fun x => if h : x ∈ S then f ⟨x, h⟩ else false, ?_, ?_⟩
  · refine Set.Finite.subset S.finite_toSet (fun x hx => ?_)
    by_contra hxS
    rw [Finset.mem_coe] at hxS
    simp only [Set.mem_setOf_eq, dif_neg hxS] at hx
    exact absurd hx (by decide)
  · intro x
    simp [x.2]

/-- **The finite-support class has infinite VC dimension on an infinite domain.** It shatters finite
sets of every size, so the supremum defining the VC dimension is `⊤`. -/
theorem vcDim_finiteSupportClass_top [Infinite X] :
    VCDim X (finiteSupportClass X) = ⊤ := by
  rw [WithTop.eq_top_iff_forall_ge]
  intro n
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq X n
  calc (n : WithTop ℕ) = (S.card : WithTop ℕ) := by rw [hS]
    _ ≤ VCDim X (finiteSupportClass X) := by
        unfold VCDim
        exact le_iSup₂_of_le S (shatters_finiteSupportClass S) le_rfl
