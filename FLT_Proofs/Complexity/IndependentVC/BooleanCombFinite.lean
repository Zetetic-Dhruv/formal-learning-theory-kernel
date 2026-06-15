/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.GrowthPoly
import FLT_Proofs.Complexity.IndependentVC.GrowthMul

/-!
# Finite VC dimension is closed under Boolean combination

A pointwise Boolean combination of finitely many finite-VC classes has finite VC dimension. Each
component has eventually polynomial growth (`vcDim_finite_imp_growth_poly`); the growth of the
combination is at most the product (`growthFunction_booleanComb_le_prod`), which is again eventually
polynomial; so the criterion `vcDim_lt_top_of_growth_poly` applies. The bound is uniform over the
combiner: no hypothesis constrains how the component labels are combined.

This is the closure of VC classes under finite Boolean operations, due to Blumer, Ehrenfeucht,
Haussler, and Warmuth, *Learnability and the Vapnik–Chervonenkis dimension*, J. ACM 36 (1989),
Lemma 3.2.3. With `vcDim_union_finite` it gives the qualitative half of the programme: finite VC
dimension is closed under the lattice operations.

## Main results

* `vcDim_booleanComb_finite`: a Boolean combination of finite-VC classes has finite VC dimension.
-/

open Filter

universe u

variable {X : Type u} {k : ℕ}

/-- **Finite VC dimension is closed under Boolean combination.** If every `C i` has `VCDim < ⊤` then
so does `booleanComb φ C`, uniformly over the combiner `φ`. -/
theorem vcDim_booleanComb_finite (φ : (Fin k → Bool) → Bool) (C : Fin k → ConceptClass X Bool)
    (hC : ∀ i, VCDim X (C i) < ⊤) : VCDim X (booleanComb φ C) < ⊤ := by
  choose K d hKd using fun i => vcDim_finite_imp_growth_poly (hC i)
  refine vcDim_lt_top_of_growth_poly (∏ i, |K i|) (∑ i, d i) ?_
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i, (GrowthFunction X (C i) m : ℝ) ≤ K i * (m : ℝ) ^ d i :=
    eventually_all.mpr hKd
  filter_upwards [hall, eventually_ge_atTop 1] with m hm hm1
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  calc (GrowthFunction X (booleanComb φ C) m : ℝ)
      ≤ ((∏ i, GrowthFunction X (C i) m : ℕ) : ℝ) := by
        exact_mod_cast growthFunction_booleanComb_le_prod φ C m
    _ = ∏ i, (GrowthFunction X (C i) m : ℝ) := by push_cast; ring
    _ ≤ ∏ i, |K i| * (m : ℝ) ^ d i := by
        refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
        calc (GrowthFunction X (C i) m : ℝ) ≤ K i * (m : ℝ) ^ d i := hm i
          _ ≤ |K i| * (m : ℝ) ^ d i := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ = (∏ i, |K i|) * (m : ℝ) ^ ∑ i, d i := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
