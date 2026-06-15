/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.Growth

/-!
# Sub-multiplicativity of the growth function under Boolean combination

The restriction-count engine lifts to the growth function: on every sample size, the growth
function of a `k`-ary Boolean combination is at most the product of the per-class growth functions.
This is the form consumed by the Sauer-Shelah machinery in `Rademacher`/`Generalization`.

## Main results

* `restrictionSet_ncard_le_growthFunction`: each restriction count is at most the growth function.
* `growthFunction_booleanComb_le_prod`: the growth function is sub-multiplicative under combination.
-/

universe u

variable {X : Type u} {k : ℕ}

private theorem growthFunction_eq (C : ConceptClass X Bool) (m : ℕ) :
    GrowthFunction X C m =
      sSup (Set.range fun S : { S : Finset X // S.card = m } => (restrictionSet C S.val).ncard) :=
  rfl

private theorem restrictionSet_ncard_le_two_pow (C : ConceptClass X Bool) (S : Finset X) :
    (restrictionSet C S).ncard ≤ 2 ^ S.card := by
  classical
  have h : (restrictionSet C S).ncard ≤ (Set.univ : Set (S → Bool)).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe] at h

/-- Each restriction count is at most the growth function at the matching sample size. -/
theorem restrictionSet_ncard_le_growthFunction (C : ConceptClass X Bool) {S : Finset X} {m : ℕ}
    (hS : S.card = m) : (restrictionSet C S).ncard ≤ GrowthFunction X C m := by
  rw [growthFunction_eq]
  refine le_csSup ⟨2 ^ m, ?_⟩ ⟨⟨S, hS⟩, rfl⟩
  rintro b ⟨S', rfl⟩
  calc (restrictionSet C S'.val).ncard ≤ 2 ^ S'.val.card := restrictionSet_ncard_le_two_pow C _
    _ = 2 ^ m := by rw [S'.property]

/-- **Sub-multiplicativity of the growth function under Boolean combination.** The growth function
of a `k`-ary Boolean combination is at most the product of the per-class growth functions,
uniformly over the combiner. -/
theorem growthFunction_booleanComb_le_prod (φ : (Fin k → Bool) → Bool)
    (C : Fin k → ConceptClass X Bool) (m : ℕ) :
    GrowthFunction X (booleanComb φ C) m ≤ ∏ i, GrowthFunction X (C i) m := by
  rw [growthFunction_eq]
  rcases Set.eq_empty_or_nonempty (Set.range fun S : { S : Finset X // S.card = m } =>
      (restrictionSet (booleanComb φ C) S.val).ncard) with he | hne
  · simp [he]
  · refine csSup_le hne ?_
    rintro b ⟨S, rfl⟩
    calc (restrictionSet (booleanComb φ C) S.val).ncard
        ≤ ∏ i, (restrictionSet (C i) S.val).ncard := ncard_restrictionSet_booleanComb_le φ C S.val
      _ ≤ ∏ i, GrowthFunction X (C i) m :=
          Finset.prod_le_prod' fun i _ => restrictionSet_ncard_le_growthFunction (C i) S.property
