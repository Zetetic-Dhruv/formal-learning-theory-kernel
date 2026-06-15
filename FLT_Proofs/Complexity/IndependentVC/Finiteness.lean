/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The exponential-beats-polynomial crux for VC-dimension finiteness

A class whose growth function is bounded by a polynomial cannot shatter sets of every size, because
`2 ^ m` eventually exceeds any polynomial `K · m ^ d`. This file isolates that real-analysis fact:
it has no dependence on concept classes, and is the analytic core consumed by the finiteness of
Boolean combinations and unions of finite-VC classes (a shattered set of size `m` forces the growth
function to be `2 ^ m`, contradicting a polynomial bound for large `m`).

## Main results

* `no_eventually_two_pow_le_poly`: `2 ^ m ≤ K · m ^ d` cannot hold for arbitrarily large `m`.
-/

open Asymptotics Filter

/-- **The exponential-beats-polynomial crux.** `2 ^ m ≤ K · m ^ d` cannot hold for arbitrarily
large `m`, since `m ^ d = o(2 ^ m)`. Stated with the eventually filter so it is applicable (the
`∀ m` form is unsatisfiable at `m = 0` for `d ≥ 1`). -/
theorem no_eventually_two_pow_le_poly (K : ℝ) (d : ℕ)
    (h : ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ m ≤ K * (m : ℝ) ^ d) : False := by
  have hlit : (fun m : ℕ => K * (m : ℝ) ^ d) =o[atTop] (fun m : ℕ => (2 : ℝ) ^ m) :=
    (isLittleO_pow_const_const_pow_of_one_lt d (by norm_num : (1 : ℝ) < 2)).const_mul_left K
  have hb : ∀ᶠ m : ℕ in atTop, ‖K * (m : ℝ) ^ d‖ ≤ (1 / 2) * ‖(2 : ℝ) ^ m‖ :=
    isLittleO_iff.mp hlit (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨m, hm, hmb⟩ := (h.and hb).exists
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hcontra : (2 : ℝ) ^ m ≤ (1 / 2) * 2 ^ m :=
    calc (2 : ℝ) ^ m ≤ K * (m : ℝ) ^ d := hm
      _ ≤ ‖K * (m : ℝ) ^ d‖ := le_abs_self _
      _ ≤ (1 / 2) * ‖(2 : ℝ) ^ m‖ := hmb
      _ = (1 / 2) * 2 ^ m := by rw [Real.norm_eq_abs, abs_of_pos h2]
  linarith
