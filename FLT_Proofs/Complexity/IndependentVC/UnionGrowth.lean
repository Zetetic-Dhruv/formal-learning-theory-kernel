/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.GrowthMul

/-!
# Sub-additivity of the growth function under collection union

For the collection union of two concept classes (a concept drawn from either class), every
restriction pattern is a pattern of one class or the other, so the growth function is sub-additive.
This is the combinatorial core of the additive two-class VC bound `VCDim (C ∪ D) ≤ d + d' + 1`; the
remaining step from sub-additivity to the bound is the Sauer-Shelah counting estimate.

NB this is the *collection* union `C ∪ D` (concept from either class), distinct from the pointwise
Boolean union handled in `GrowthMul`.

## Main results

* `growthFunction_union_le_add`: the growth function is sub-additive under collection union.
-/

universe u

variable {X : Type u}

private theorem gf_eq (C : ConceptClass X Bool) (m : ℕ) :
    GrowthFunction X C m =
      sSup (Set.range fun S : { S : Finset X // S.card = m } => (restrictionSet C S.val).ncard) :=
  rfl

/-- **Sub-additivity of the growth function under collection union.** Every restriction pattern of
`C ∪ D` on a sample is a pattern of `C` or of `D`, so the pattern count is at most the sum. -/
theorem growthFunction_union_le_add (C D : ConceptClass X Bool) (m : ℕ) :
    GrowthFunction X (C ∪ D) m ≤ GrowthFunction X C m + GrowthFunction X D m := by
  rw [gf_eq (C ∪ D)]
  rcases Set.eq_empty_or_nonempty (Set.range fun S : { S : Finset X // S.card = m } =>
      (restrictionSet (C ∪ D) S.val).ncard) with he | hne
  · rw [he, csSup_empty]
    exact bot_le
  · refine csSup_le hne ?_
    rintro b ⟨S, rfl⟩
    calc (restrictionSet (C ∪ D) S.val).ncard
        ≤ (restrictionSet C S.val ∪ restrictionSet D S.val).ncard := by
          refine Set.ncard_le_ncard ?_ (Set.toFinite _)
          rintro f ⟨c, hc, hcf⟩
          rcases hc with hc | hc
          · exact Or.inl ⟨c, hc, hcf⟩
          · exact Or.inr ⟨c, hc, hcf⟩
      _ ≤ (restrictionSet C S.val).ncard + (restrictionSet D S.val).ncard := Set.ncard_union_le _ _
      _ ≤ GrowthFunction X C m + GrowthFunction X D m :=
          Nat.add_le_add (restrictionSet_ncard_le_growthFunction C S.property)
            (restrictionSet_ncard_le_growthFunction D S.property)
