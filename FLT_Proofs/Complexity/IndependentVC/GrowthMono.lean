/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.GrowthMul

/-!
# Monotonicity of the growth function in the concept class

Enlarging a concept class can only enlarge the set of restriction patterns it realizes on any
sample, so the growth function is monotone in the class. This complements the class-monotonicity of
the VC dimension (`vcDim_mono`).

## Main results

* `growthFunction_mono`: the growth function is monotone in the concept class.
-/

universe u

variable {X : Type u}

private theorem gf_eq (C : ConceptClass X Bool) (m : ℕ) :
    GrowthFunction X C m =
      sSup (Set.range fun S : { S : Finset X // S.card = m } => (restrictionSet C S.val).ncard) :=
  rfl

/-- The growth function is monotone in the concept class: a larger class realizes at least as many
restriction patterns on every sample. -/
theorem growthFunction_mono {C D : ConceptClass X Bool} (h : C ⊆ D) (m : ℕ) :
    GrowthFunction X C m ≤ GrowthFunction X D m := by
  rw [gf_eq C]
  rcases Set.eq_empty_or_nonempty (Set.range fun S : { S : Finset X // S.card = m } =>
      (restrictionSet C S.val).ncard) with he | hne
  · rw [he, csSup_empty]
    exact bot_le
  · refine csSup_le hne ?_
    rintro b ⟨S, rfl⟩
    calc (restrictionSet C S.val).ncard
        ≤ (restrictionSet D S.val).ncard := by
          refine Set.ncard_le_ncard ?_ (Set.toFinite _)
          rintro f ⟨c, hc, hcf⟩
          exact ⟨c, h hc, hcf⟩
      _ ≤ GrowthFunction X D m := restrictionSet_ncard_le_growthFunction D S.property
