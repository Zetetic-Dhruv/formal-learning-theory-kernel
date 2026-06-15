/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.GrowthSauerShelah
import FLT_Proofs.Complexity.IndependentVC.UnionGrowth
import FLT_Proofs.Complexity.IndependentVC.VCFinite
import FLT_Proofs.Complexity.IndependentVC.PartialBinomial

/-!
# The tight two-class union bound

The collection union of classes of VC dimension `dC` and `dD` has VC dimension at most `dC + dD + 1`,
and this constant is sharp. A set of size `dC + dD + 2` cannot be shattered: by Sauer–Shelah the
union's growth function there is at most `∑_{k ≤ dC} C(n,k) + ∑_{k ≤ dD} C(n,k)`, which the
complementary-binomial identity `partial_binomial_sum_lt_two_pow` places strictly below `2^n` — yet
shattering would force growth `2^n`.

This refines the qualitative closure `vcDim_union_finite` to the exact additive constant. It is the
two-class case of the VC-class union permanence (van der Vaart and Wellner, *Weak Convergence and
Empirical Processes*, Springer 1996, Lemma 2.6.17); the sharp `+1` is the standard Sauer–Shelah
counting (e.g. Mohri, Rostamizadeh, Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press
2018, §3.3).

## Main results

* `vcDim_union_le`: `VCDim X C ≤ dC → VCDim X D ≤ dD → VCDim X (C ∪ D) ≤ dC + dD + 1`.
-/

open Filter

universe u

variable {X : Type u}

/-- **The tight two-class union bound.** If `VCDim X C ≤ dC` and `VCDim X D ≤ dD` then
`VCDim X (C ∪ D) ≤ dC + dD + 1`. -/
theorem vcDim_union_le {C D : ConceptClass X Bool} {dC dD : ℕ}
    (hC : VCDim X C ≤ (dC : WithTop ℕ)) (hD : VCDim X D ≤ (dD : WithTop ℕ)) :
    VCDim X (C ∪ D) ≤ ((dC + dD + 1 : ℕ) : WithTop ℕ) := by
  -- a finite VC bound forces every shattered set below it
  have shatter_bound : ∀ (E : ConceptClass X Bool) (e : ℕ), VCDim X E ≤ (e : WithTop ℕ) →
      ∀ s : Finset X, Shatters X E s → s.card ≤ e := by
    intro E e hE s hs
    have hle : (s.card : WithTop ℕ) ≤ VCDim X E :=
      le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X E S) => (S.card : WithTop ℕ)) s hs
    exact_mod_cast hle.trans hE
  have hsC := shatter_bound C dC hC
  have hsD := shatter_bound D dD hD
  rw [VCDim]
  refine iSup₂_le (fun S hS => ?_)
  have hbound : S.card ≤ dC + dD + 1 := by
    by_contra hlt
    push_neg at hlt
    have hn : dC + dD + 2 ≤ S.card := hlt
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hn
    have hTsh : Shatters X (C ∪ D) T := shatters_of_subset hS hTS
    have h2pow : 2 ^ (dC + dD + 2) ≤ GrowthFunction X (C ∪ D) (dC + dD + 2) := by
      have h := growthFunction_ge_two_pow_of_shatters hTsh
      rwa [hTcard] at h
    have hpoly : GrowthFunction X (C ∪ D) (dC + dD + 2)
        ≤ ∑ k ∈ Finset.range (dC + 1), (dC + dD + 2).choose k
          + ∑ k ∈ Finset.range (dD + 1), (dC + dD + 2).choose k :=
      (growthFunction_union_le_add C D (dC + dD + 2)).trans
        (add_le_add (growthFunction_le_sum_choose C dC hsC _)
          (growthFunction_le_sum_choose D dD hsD _))
    exact lt_irrefl _ (lt_of_le_of_lt (h2pow.trans hpoly) (partial_binomial_sum_lt_two_pow dC dD))
  exact_mod_cast hbound
