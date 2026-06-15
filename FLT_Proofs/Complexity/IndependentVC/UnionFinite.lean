/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.GrowthPoly
import FLT_Proofs.Complexity.IndependentVC.UnionGrowth

/-!
# Finite VC dimension is closed under collection union

The collection union of two finite-VC classes has finite VC dimension. Each class has eventually
polynomial growth (`vcDim_finite_imp_growth_poly`); the growth of the union is at most their sum
(`growthFunction_union_le_add`), which is again eventually polynomial; so the criterion
`vcDim_lt_top_of_growth_poly` applies.

## Main results

* `vcDim_union_finite`: the VC dimension of a collection union of finite-VC classes is finite.
-/

open Filter

universe u

variable {X : Type u}

/-- **Finite VC dimension is closed under collection union.** If `VCDim X C < ⊤` and
`VCDim X D < ⊤` then `VCDim X (C ∪ D) < ⊤`. -/
theorem vcDim_union_finite {C D : ConceptClass X Bool}
    (hC : VCDim X C < ⊤) (hD : VCDim X D < ⊤) : VCDim X (C ∪ D) < ⊤ := by
  obtain ⟨KC, dC, hC'⟩ := vcDim_finite_imp_growth_poly hC
  obtain ⟨KD, dD, hD'⟩ := vcDim_finite_imp_growth_poly hD
  refine vcDim_lt_top_of_growth_poly (|KC| + |KD|) (max dC dD) ?_
  filter_upwards [hC', hD', eventually_ge_atTop 1] with m hmC hmD hm1
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hpow : ∀ (K : ℝ) {e : ℕ}, e ≤ max dC dD →
      K * (m : ℝ) ^ e ≤ |K| * (m : ℝ) ^ max dC dD := fun K {e} he =>
    calc K * (m : ℝ) ^ e ≤ |K| * (m : ℝ) ^ e :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |K| * (m : ℝ) ^ max dC dD :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1' he) (abs_nonneg _)
  calc (GrowthFunction X (C ∪ D) m : ℝ)
      ≤ ((GrowthFunction X C m + GrowthFunction X D m : ℕ) : ℝ) := by
        exact_mod_cast growthFunction_union_le_add C D m
    _ = (GrowthFunction X C m : ℝ) + GrowthFunction X D m := by push_cast; ring
    _ ≤ KC * (m : ℝ) ^ dC + KD * (m : ℝ) ^ dD := add_le_add hmC hmD
    _ ≤ |KC| * (m : ℝ) ^ max dC dD + |KD| * (m : ℝ) ^ max dC dD :=
        add_le_add (hpow KC (le_max_left _ _)) (hpow KD (le_max_right _ _))
    _ = (|KC| + |KD|) * (m : ℝ) ^ max dC dD := by ring
