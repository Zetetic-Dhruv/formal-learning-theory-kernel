/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.BooleanComb

/-!
# Sub-multiplicativity of restriction counts under Boolean combination

On a finite sample `S`, a concept class `C` realizes a finite set of labelling patterns, the
`restrictionSet C S`. For a `k`-ary Boolean combination, every pattern of the combined class is
obtained by applying the combiner pointwise to a tuple of patterns of the component classes. Hence
the number of combined patterns is at most the product of the component counts, uniformly over the
combiner.

This is the engine behind the quantitative Boolean-combination bounds. Read at the asymptotic
growth rate it yields the sub-additivity of VC density; read at the exact count it feeds the
Sauer-Shelah estimate for the VC dimension of unions and intersections.

## Main results

* `restrictionSet`: the patterns a class realizes on a sample.
* `ncard_univPi`: the cardinality of a universal dependent product of finite sets.
* `ncard_restrictionSet_booleanComb_le`: the sub-multiplicative bound.
-/

universe u

variable {X : Type u} {k : ℕ}

/-- The set of labelling patterns that `C` realizes on a finite sample `S`. -/
def restrictionSet (C : ConceptClass X Bool) (S : Finset X) : Set (S → Bool) :=
  { f | ∃ c ∈ C, ∀ x : S, c (x : X) = f x }

/-- The cardinality of a universal dependent product of sets over a finite index is the product of
the cardinalities. -/
theorem ncard_univPi {ι : Type*} [Fintype ι] {β : ι → Type*} (s : ∀ i, Set (β i)) :
    (Set.univ.pi s).ncard = ∏ i, (s i).ncard := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr (Equiv.Set.univPi s), Nat.card_pi]
  simp only [Nat.card_coe_set_eq]

/-- **Sub-multiplicativity of restriction counts under Boolean combination.** On any finite sample,
the number of restriction patterns of a `k`-ary Boolean combination is at most the product of the
per-class restriction counts, uniformly over the combiner `φ`. Each combined pattern is the image,
under pointwise `φ`, of a tuple of component patterns, so the combined patterns inject into the
product of the per-class pattern sets. -/
theorem ncard_restrictionSet_booleanComb_le (φ : (Fin k → Bool) → Bool)
    (C : Fin k → ConceptClass X Bool) (S : Finset X) :
    (restrictionSet (booleanComb φ C) S).ncard ≤ ∏ i, (restrictionSet (C i) S).ncard := by
  have hsub : restrictionSet (booleanComb φ C) S ⊆
      (fun t : Fin k → (S → Bool) => fun x => φ (fun i => t i x)) ''
        (Set.univ.pi (fun i => restrictionSet (C i) S)) := by
    rintro f ⟨c, hc, hcf⟩
    obtain ⟨g, hg, rfl⟩ := hc
    refine ⟨fun i => fun x => g i (x : X), ?_, ?_⟩
    · rw [Set.mem_univ_pi]
      intro i
      exact ⟨g i, hg i, fun x => rfl⟩
    · funext x
      exact hcf x
  calc (restrictionSet (booleanComb φ C) S).ncard
      ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.univ.pi (fun i => restrictionSet (C i) S)).ncard :=
          Set.ncard_image_le (Set.toFinite _)
    _ = ∏ i, (restrictionSet (C i) S).ncard := ncard_univPi _
