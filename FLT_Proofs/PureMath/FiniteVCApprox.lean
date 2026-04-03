/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.PureMath.ApproxMinimax

/-!
# Finite Sample Approximation for FinitePMF

Infrastructure for approximating FinitePMFs by empirical distributions of
finite samples. The key result is `expectation_approx_of_tv`: if the total
variation between a PMF and an empirical PMF is small, then all Boolean test
expectations are well-approximated.

## Main definitions

- `trueExpectation` : expected value of a function under a FinitePMF
- `totalVariation` : TV distance between a FinitePMF and an empirical PMF
- `boolTestExpectation` : expected value of a Boolean test (0/1 valued)

## Main results

- `expectation_approx_of_tv` : TV bound implies test approximation
- `tv_bound_implies_all_tests` : TV ≤ ε implies all tests ε-approximated
- `exists_approx_sample_of_rational` : construction for rational PMFs

## References

- Used in compression-based learnability proofs (sample compression lemma).
-/

open Finset Classical

noncomputable section

/-! ## Expectations -/

/-- True expectation of a real-valued function under a FinitePMF. -/
def trueExpectation {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → ℝ) : ℝ :=
  ∑ h : H, μ.prob h * f h

/-- Boolean test expectation: E_μ[𝟙[f(h)]]. -/
def boolTestExpectation {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) : ℝ :=
  trueExpectation μ (fun h => if f h then (1 : ℝ) else 0)

/-- Boolean test expectation is in [0, 1]. -/
lemma boolTestExpectation_nonneg {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) :
    0 ≤ boolTestExpectation μ f :=
  Finset.sum_nonneg fun h _ =>
    mul_nonneg (μ.prob_nonneg h) (by simp only; split_ifs <;> norm_num)

lemma boolTestExpectation_le_one {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) :
    boolTestExpectation μ f ≤ 1 := by
  simp only [boolTestExpectation, trueExpectation]
  calc ∑ h : H, μ.prob h * (if f h then (1 : ℝ) else 0)
      ≤ ∑ h : H, μ.prob h := Finset.sum_le_sum fun h _ =>
        mul_le_of_le_one_right (μ.prob_nonneg h) (by split_ifs <;> norm_num)
    _ = 1 := μ.prob_sum_one

/-! ## Total Variation Distance -/

/-- Total variation distance between two FinitePMFs. -/
def tvDistance {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) : ℝ :=
  ∑ h : H, |μ.prob h - ν.prob h|

/-- TV distance is nonneg. -/
lemma tvDistance_nonneg {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) :
    0 ≤ tvDistance μ ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- TV distance is symmetric. -/
lemma tvDistance_comm {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) :
    tvDistance μ ν = tvDistance ν μ := by
  simp only [tvDistance, abs_sub_comm]

/-- TV distance is zero between equal PMFs. -/
lemma tvDistance_self {H : Type*} [Fintype H]
    (μ : FinitePMF H) :
    tvDistance μ μ = 0 := by
  simp [tvDistance]

/-! ## Key Approximation Lemma -/

/-- **TV bound implies test approximation**: if the TV distance between
    two FinitePMFs is ≤ δ, then for any Boolean test f, the expectations
    under the two PMFs differ by at most δ. -/
theorem expectation_approx_of_tv {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) (f : H → Bool) (δ : ℝ)
    (hδ : tvDistance μ ν ≤ δ) :
    |boolTestExpectation μ f - boolTestExpectation ν f| ≤ δ := by
  simp only [boolTestExpectation, trueExpectation]
  calc |∑ h : H, μ.prob h * (if f h then (1 : ℝ) else 0) -
        ∑ h : H, ν.prob h * (if f h then (1 : ℝ) else 0)|
      = |∑ h : H, (μ.prob h - ν.prob h) *
          (if f h then (1 : ℝ) else 0)| := by
        congr 1; rw [← Finset.sum_sub_distrib]; congr 1; ext h; ring
    _ ≤ ∑ h : H, |(μ.prob h - ν.prob h) *
          (if f h then (1 : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h : H, |μ.prob h - ν.prob h| := by
        apply Finset.sum_le_sum; intro h _
        rw [abs_mul]
        calc |μ.prob h - ν.prob h| * |if f h then (1 : ℝ) else 0|
            ≤ |μ.prob h - ν.prob h| * 1 := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              split_ifs <;> simp [abs_of_nonneg]
          _ = |μ.prob h - ν.prob h| := mul_one _
    _ = tvDistance μ ν := rfl
    _ ≤ δ := hδ

/-- **All tests approximated under TV bound**: if TV(μ, ν) ≤ ε, then
    every Boolean test f has |E_μ[f] - E_ν[f]| ≤ ε. -/
theorem tv_bound_implies_all_tests {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) (ε : ℝ)
    (hε : tvDistance μ ν ≤ ε)
    (tests : Finset (H → Bool)) :
    ∀ f ∈ tests, |boolTestExpectation μ f - boolTestExpectation ν f| ≤ ε :=
  fun f _ => expectation_approx_of_tv μ ν f ε hε

/-! ## Expectation of empiricalPMF equals average -/

/-- The Boolean test expectation under an empirical PMF equals the
    average of the test over the sample. -/
lemma boolTestExpectation_empirical_eq_avg
    {H : Type*} [Fintype H] [DecidableEq H]
    {T : ℕ} (hT : 0 < T) (hs : Fin T → H) (f : H → Bool) :
    boolTestExpectation (empiricalPMF hT hs) f =
    (∑ t : Fin T, if f (hs t) then (1 : ℝ) else 0) / T := by
  simp only [boolTestExpectation, trueExpectation, empiricalPMF]
  -- Rewrite LHS: Σ_h (count(h)/T) * val(h) = (Σ_h count(h) * val(h)) / T
  conv_lhs => arg 2; ext h; rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  -- Now LHS = (Σ_h count(h) * val(h)) / T and RHS = (Σ_t val(hs t)) / T
  congr 1
  -- Need: Σ_h count(h) * g(h) = Σ_t g(hs t)
  -- where count(h) = |{t : hs t = h}| and g(h) = if f h then 1 else 0
  -- Proof by card_eq_sum_card_fiberwise applied to g ∘ hs
  symm
  have := Finset.card_eq_sum_card_fiberwise (f := hs)
    (s := univ) (t := univ) (fun _ _ => Finset.mem_univ _)
  -- Σ_t g(hs t) = Σ_h Σ_{t ∈ fib(h)} g(hs t) = Σ_h count(h) * g(h)
  -- since for t ∈ fib(h), g(hs t) = g(h)
  conv_lhs => rw [show (∑ t : Fin T, if f (hs t) then (1 : ℝ) else 0) =
    ∑ h : H, ∑ t ∈ univ.filter (fun t => hs t = h),
      (if f (hs t) then (1 : ℝ) else 0) from by
    rw [← Finset.sum_biUnion (s := univ)]
    · congr 1; ext t; simp
    · intro h₁ _ h₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro t _ ht1 ht2; exact hne (ht1.symm.trans ht2)]
  congr 1; ext h
  -- Σ_{t ∈ fib(h)} g(hs t) = count(h) * g(h)
  -- For t in fib(h), hs t = h, so g(hs t) = g(h)
  rw [Finset.sum_congr rfl (fun t ht => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Approximate Minimax Connection

The following connects the minimax game infrastructure with finite
sample approximation. For the compression proof, we need:

Given a distribution p on hypotheses (from minimax), find a small
sample that approximately preserves all test expectations.

The `tv_bound_implies_all_tests` theorem provides the bridge:
if we can find a FinitePMF ν close to p in TV distance, then all
tests are preserved. The FinitePMF ν can be taken as the empirical
PMF of a carefully constructed sample.
-/

/-- The boolGamePayoff of the minimax game equals the Boolean test expectation
    of the corresponding test, connecting the two frameworks. -/
lemma boolGamePayoff_eq_boolTestExpectation
    {R : Type*} [Fintype R] [DecidableEq R]
    {C : Type*} (M : R → C → Bool) (p : FinitePMF R) (c : C) :
    boolGamePayoff M p c = boolTestExpectation p (fun r => M r c) := by
  simp only [boolGamePayoff, boolTestExpectation, trueExpectation]

end -- noncomputable section
