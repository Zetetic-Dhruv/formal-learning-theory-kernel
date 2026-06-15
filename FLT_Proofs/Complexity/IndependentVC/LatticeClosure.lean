/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.UnionFinite

/-!
# Finite VC dimension is closed under finite collection unions

The two-class union closure `vcDim_union_finite` lifts by induction to an arbitrary finite family:
the collection union `⋃ i ∈ s, C i` of finitely many finite-VC classes again has finite VC
dimension. The empty class has VC dimension `0` (it shatters nothing, not even the empty sample),
giving the base case.

This is the finite-union half of the permanence properties of VC classes (van der Vaart and Wellner,
*Weak Convergence and Empirical Processes*, Springer 1996, Lemma 2.6.17): the VC classes are stable
under finitely many set operations. The pointwise (lattice-B) analogue is `vcDim_booleanComb_finite`.

## Main results

* `vcDim_empty`: the empty concept class has finite VC dimension.
* `vcDim_biUnion_finite`: a union over a `Finset` of finite-VC classes has finite VC dimension.
* `vcDim_iUnion_finite`: the same for a union indexed by a `Fintype`.
-/

open Filter

universe u v

variable {X : Type u}

/-- The empty concept class has finite VC dimension. It shatters no sample — a labelling would have
to be realized by some concept, and there are none — so its VC dimension is `⊥ = 0`. -/
theorem vcDim_empty : VCDim X (∅ : ConceptClass X Bool) < ⊤ := by
  have h : VCDim X (∅ : ConceptClass X Bool) = ⊥ := by
    rw [VCDim]
    refine iSup₂_eq_bot.mpr (fun S hShat => ?_)
    obtain ⟨c, hc, -⟩ := hShat (fun _ => false)
    exact ((Set.mem_empty_iff_false c).mp hc).elim
  rw [h]; exact bot_lt_top

/-- **Finite VC dimension is closed under finite collection unions.** If every `C i` for `i` in a
finite set `s` has `VCDim < ⊤`, then so does the collection union `⋃ i ∈ s, C i`. -/
theorem vcDim_biUnion_finite {ι : Type v} (s : Finset ι) (C : ι → ConceptClass X Bool)
    (hC : ∀ i ∈ s, VCDim X (C i) < ⊤) : VCDim X (⋃ i ∈ s, C i) < ⊤ := by
  classical
  revert hC
  induction s using Finset.induction with
  | empty => intro _; simpa using vcDim_empty
  | @insert a s ha ih =>
      intro hC
      rw [Finset.set_biUnion_insert]
      exact vcDim_union_finite (hC a (Finset.mem_insert_self a s))
        (ih (fun i hi => hC i (Finset.mem_insert_of_mem hi)))

/-- **Finite VC dimension is closed under `Fintype`-indexed collection unions.** Corollary of
`vcDim_biUnion_finite` over the universal finite set. -/
theorem vcDim_iUnion_finite {ι : Type v} [Fintype ι] (C : ι → ConceptClass X Bool)
    (hC : ∀ i, VCDim X (C i) < ⊤) : VCDim X (⋃ i, C i) < ⊤ := by
  have hcover : (⋃ i, C i) = ⋃ i ∈ (Finset.univ : Finset ι), C i := by simp
  rw [hcover]
  exact vcDim_biUnion_finite Finset.univ C (fun i _ => hC i)
