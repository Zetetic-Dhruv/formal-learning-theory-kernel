/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.VCFinite
import FLT_Proofs.Complexity.Generalization
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Finite VC dimension implies eventual polynomial growth

The converse of `vcDim_lt_top_of_growth_poly`: a class of finite VC dimension `v` has growth function
eventually bounded by `(v + 1) · m ^ v`. With Sauer-Shelah (`vcdim_finite_imp_growth_bounded`) the
growth function is at most `∑_{j ≤ v} (m choose j)`, and each binomial is at most `m ^ v`.

Together with the criterion this characterizes finiteness: `VCDim < ⊤` iff the growth function is
eventually polynomial. The bridge is what lets finiteness compose through the growth bounds for
Boolean combinations and unions.

## Main results

* `vcDim_finite_imp_growth_poly`: finite VC dimension implies eventual polynomial growth.
-/

open Filter

universe u

variable {X : Type u}

/-- **Finite VC dimension implies eventual polynomial growth.** If `VCDim X C < ⊤` then the growth
function is eventually bounded by a polynomial `K · m ^ d`. -/
theorem vcDim_finite_imp_growth_poly {C : ConceptClass X Bool} (hC : VCDim X C < ⊤) :
    ∃ (K : ℝ) (d : ℕ), ∀ᶠ m : ℕ in atTop, (GrowthFunction X C m : ℝ) ≤ K * (m : ℝ) ^ d := by
  obtain ⟨v, hv⟩ := vcdim_finite_imp_growth_bounded X C hC
  refine ⟨(v + 1 : ℝ), v, ?_⟩
  rw [eventually_atTop]
  refine ⟨max v 1, fun m hm => ?_⟩
  have hmv : v ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hgf : GrowthFunction X C m ≤ ∑ j ∈ Finset.range (v + 1), Nat.choose m j := hv m hmv
  have hsum : ∑ j ∈ Finset.range (v + 1), Nat.choose m j ≤ (v + 1) * m ^ v := by
    calc ∑ j ∈ Finset.range (v + 1), Nat.choose m j
        ≤ ∑ _j ∈ Finset.range (v + 1), m ^ v := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          exact le_trans (Nat.choose_le_pow m j)
            (Nat.pow_le_pow_right hm1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      _ = (v + 1) * m ^ v := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc (GrowthFunction X C m : ℝ) ≤ (((v + 1) * m ^ v : ℕ) : ℝ) := by
        exact_mod_cast le_trans hgf hsum
    _ = (v + 1 : ℝ) * (m : ℝ) ^ v := by push_cast; ring
