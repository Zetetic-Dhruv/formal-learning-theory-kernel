/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Complementary partial binomial sums

The combinatorial core of the two-class VC union bound. At `n = a + b + 2` the low partial sum
`∑_{j ≤ a} C(n,j)` and (after the reflection `C(n,j) = C(n,n-j)`) the low partial sum
`∑_{j ≤ b} C(n,j)` cover exactly the bottom block `{0,…,a}` and the top block `{a+2,…,n}` of the row
of Pascal's triangle, leaving the single middle entry `C(n,a+1)`. Hence the two partial sums plus
that middle entry exhaust the row, whose total is `2^n` (`Nat.sum_range_choose`):

`∑_{j ≤ a} C(n,j) + ∑_{j ≤ b} C(n,j) + C(n,a+1) = 2^n`.

Since `C(n,a+1) ≥ 1`, the two partial sums fall strictly below `2^n`. This is precisely the counting
that forces `VCdim(C ∪ D) ≤ VCdim C + VCdim D + 1`: a sample of size `a + b + 2` cannot be shattered,
because Sauer–Shelah on each class would bound the union's growth function by the left-hand side,
which is `< 2^{a+b+2}`.

## Main results

* `partial_binomial_complement`: the two complementary partial sums plus the middle entry give `2^n`.
* `partial_binomial_sum_lt_two_pow`: the two complementary partial sums are strictly below `2^n`.
-/

open Finset

/-- **Complementary partial binomial sums.** At `n = a + b + 2`, the low partial sum to `a`, the low
partial sum to `b`, and the middle binomial `C(n, a+1)` partition the row of Pascal's triangle, so
they sum to `2^n`. The `b`-sum is reflected onto the top block via `C(n,j) = C(n,n-j)`. -/
theorem partial_binomial_complement (a b : ℕ) :
    (∑ j ∈ range (a + 1), (a + b + 2).choose j)
      + (∑ j ∈ range (b + 1), (a + b + 2).choose j)
      + (a + b + 2).choose (a + 1) = 2 ^ (a + b + 2) := by
  set n := a + b + 2 with hn
  have hb : (∑ j ∈ range (b + 1), n.choose j) = ∑ j ∈ Ico (a + 2) (n + 1), n.choose j := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : n + 1 - (a + 2) = b + 1 := by omega
    rw [hlen, ← Finset.sum_range_reflect (fun j => n.choose (a + 2 + j)) (b + 1)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hidx : a + 2 + (b + 1 - 1 - j) = n - j := by omega
    rw [hidx, Nat.choose_symm (by omega)]
  have hsplit : 2 ^ n = (∑ j ∈ range (a + 1), n.choose j)
      + (n.choose (a + 1) + ∑ j ∈ Ico (a + 2) (n + 1), n.choose j) := by
    rw [← Nat.sum_range_choose n, ← Finset.sum_range_add_sum_Ico _ (show a + 1 ≤ n + 1 by omega)]
    congr 1
    rw [Finset.sum_eq_sum_Ico_succ_bot (show a + 1 < n + 1 by omega)]
  rw [hb, hsplit]; ring

/-- **The two complementary partial binomial sums fall strictly below `2^n`.** The slack is exactly
the positive middle entry `C(n, a+1)`. This is the inequality consumed by the VC union bound. -/
theorem partial_binomial_sum_lt_two_pow (a b : ℕ) :
    (∑ j ∈ range (a + 1), (a + b + 2).choose j)
      + (∑ j ∈ range (b + 1), (a + b + 2).choose j) < 2 ^ (a + b + 2) := by
  have h := partial_binomial_complement a b
  have hpos : 0 < (a + b + 2).choose (a + 1) := Nat.choose_pos (by omega)
  omega
