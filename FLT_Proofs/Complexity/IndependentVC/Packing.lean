/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.GrowthSauerShelah
import FLT_Proofs.Complexity.IndependentVC.GrowthMul
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# T2.5 — A Haussler-style packing bound from the exponential Sauer–Shelah growth bound

A *δ-packing* of a concept class `C` on a finite sample `S` is a family `P ⊆ C` of concepts that
pairwise disagree on a strictly positive fraction `> δ` of the points of `S`. The basic combinatorial
fact behind every packing/covering estimate for VC classes is that the size of such a packing is
controlled by the *growth function* (shattering coefficient) of the class — and hence, through
Sauer–Shelah, grows only polynomially in the sample size. This file proves that bound in its two
natural layers.

## Layer A — the exponential Sauer–Shelah corollary

`growthFunction_le_exp` upgrades the polynomial Sauer–Shelah bound
`GrowthFunction X C m ≤ ∑_{k ≤ d} (m choose k)` (`growthFunction_le_sum_choose`) to the closed
exponential form

`GrowthFunction X C m ≤ (e · m / d) ^ d`

for a class whose shattered sets all have size `≤ d` (with `1 ≤ d ≤ m`). The analytic heart is the
binomial-tail inequality `∑_{i ≤ d} (m choose i) ≤ (e m / d) ^ d`
(`sum_choose_le_exp_pow`), proved here from `(1 + d/m) ^ m ≤ e ^ d` (via `Real.add_one_le_exp`) and
the factorisation `(m choose i) = (m choose i) · (d/m) ^ i · (m/d) ^ i` with `(m/d) ^ i ≤ (m/d) ^ d`.
This is the bound that Mathlib's `Data/Nat/Choose/Bounds.lean` explicitly flags as missing future
work. It is proved here self-containedly so that the independent VC module does not depend on the
heavy measure-theoretic `Rademacher`/`Generalization` stack (where the same inequality also lives, as
`sum_choose_le_exp_pow` / `sauer_shelah_exp_bound`, but stated for `VCDim X C = d` rather than for an
explicit shatter bound).

## Layer B — the combinatorial packing bound

`packing_card_le_growthFunction` proves `#P ≤ GrowthFunction X C (#S)` for any `δ`-packing `P` with
`0 ≤ δ`. The mechanism is the restriction map `c ↦ (fun x : ↥S => c x)`: on a packing it is
*injective*, because two concepts with the same restriction agree everywhere on `S`, so they disagree
on `0` points, contradicting `δ · #S < (number of disagreements)` once `δ · #S ≥ 0`. Injectivity
turns `#P` into the cardinality of the image, which sits inside the `restrictionSet` whose `ncard` is
bounded by the growth function (`restrictionSet_ncard_le_growthFunction`). Composing Layer B with
Layer A gives `packing_card_le_exp`: `#P ≤ (e · #S / d) ^ d`.

## Scope and honesty

This is the *δ-independent* packing bound: the deliverable is `#P ≤ Π_C(#S) ≤ (e m / d) ^ d`. It is
genuinely non-vacuous — `IsPacking` requires `P ⊆ C` and a strict pairwise-separation condition — but
it is **not** Haussler's *sharp* `δ`-dependent bound `M(δ) ≤ e (d+1) (2e/δ) ^ d`. The sharp constant
(exponent exactly `d`, no spurious `log(1/δ)`) requires the one-inclusion-graph / shifting argument of
Haussler 1995, which is not formalised here and is **deliberately not faked**; see the closing remark.

Reference: D. Haussler, *Sphere packing numbers for subsets of the Boolean n-cube with bounded
Vapnik–Chervonenkis dimension*, J. Combin. Theory Ser. A 69(2):217–232 (1995). The polynomial /
`(e m / d) ^ d` Sauer–Shelah corollary used here is classical: N. Sauer, *On the density of families
of sets*, J. Combin. Theory Ser. A 13 (1972); S. Shelah, *A combinatorial problem; stability and
order for models and theories in infinitary languages*, Pacific J. Math. 41 (1972).

## Main results

* `sum_choose_le_exp_pow`: the binomial-tail inequality `∑_{i ≤ d} (m choose i) ≤ (e m / d) ^ d`.
* `growthFunction_le_exp`: the exponential Sauer–Shelah bound `Π_C(m) ≤ (e m / d) ^ d`.
* `IsPacking`: a `δ`-packing of `C` on the sample `S`.
* `packing_card_le_growthFunction`: `#P ≤ Π_C(#S)` for any `δ`-packing with `0 ≤ δ`.
* `packing_card_le_exp`: the composed exponential packing bound `#P ≤ (e · #S / d) ^ d`.
-/

open Finset

universe u

variable {X : Type u}

/-! ## Layer A — the exponential Sauer–Shelah corollary -/

/-- **Binomial-tail inequality.** For `1 ≤ d ≤ m`, the partial sum of binomial coefficients obeys
`∑_{i ≤ d} (m choose i) ≤ (e · m / d) ^ d`. This is the analytic engine of the exponential
Sauer–Shelah bound; Mathlib's `Data/Nat/Choose/Bounds.lean` flags this estimate as missing.

The proof factors `(m choose i) = (m choose i) · t ^ i · (m/d) ^ i` with `t = d/m`, bounds
`(m/d) ^ i ≤ (m/d) ^ d`, sums the partial binomial against the full binomial theorem
`(1 + t) ^ m = ∑ (m choose i) t ^ i`, and lifts `(1 + t) ^ m ≤ e ^ d` via `Real.add_one_le_exp`. -/
theorem sum_choose_le_exp_pow (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    (∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hd hdm)
  have hdm_r : (d : ℝ) ≤ ↑m := Nat.cast_le.mpr hdm
  have hm_div_d_ge : (1 : ℝ) ≤ ↑m / ↑d := le_div_iff₀ hd_pos |>.mpr (by linarith)
  -- `t = d / m ∈ (0, 1]`.
  set t := (d : ℝ) / ↑m with ht_def
  have ht_pos : 0 < t := div_pos hd_pos hm_pos
  -- Full binomial theorem: `(1 + t) ^ m = ∑_{i ≤ m} (m choose i) t ^ i`.
  have h_binom' : (1 + t) ^ m = ∑ i ∈ Finset.range (m + 1),
      ↑(Nat.choose m i) * t ^ i := by
    rw [add_comm, add_pow t 1 m]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_pow, mul_one]; ring
  -- Partial binomial (to `d`) is below the full binomial (to `m`) since the terms are nonneg.
  have h_partial_le_binom : ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i ≤
      (1 + t) ^ m := by
    rw [h_binom']
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i _ _
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt ht_pos) _)
  -- `(1 + t) ^ m ≤ exp(t) ^ m = exp(t · m) = exp d = (exp 1) ^ d`.
  have h_exp_bound : (1 + t) ^ m ≤ Real.exp 1 ^ d := by
    have h1t_le : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have h_pow : (1 + t) ^ m ≤ (Real.exp t) ^ m :=
      pow_le_pow_left₀ (by linarith) h1t_le m
    have h_exp_eq : (Real.exp t) ^ m = Real.exp (t * ↑m) := by
      rw [mul_comm, Real.exp_nat_mul]
    have h_tm : t * ↑m = ↑d := by
      simp only [ht_def]; field_simp
    rw [h_exp_eq, h_tm] at h_pow
    calc (1 + t) ^ m ≤ Real.exp ↑d := h_pow
      _ = Real.exp 1 ^ d := by rw [← Real.exp_nat_mul]; simp
  -- Factor `(m/d) ^ d` out of the partial sum.
  have h_factor : (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ)) ≤
      (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := by
    have h_id : ∀ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ) =
        ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ i := by
      intro i _
      have htinv : t * (↑m / ↑d) = 1 := by
        simp only [ht_def]; field_simp
      rw [mul_assoc, ← mul_pow, htinv, one_pow, mul_one]
    rw [Finset.sum_congr rfl h_id]
    calc ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ i
        ≤ ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ d := by
          apply Finset.sum_le_sum
          intro i hi
          have hi_le : i ≤ d := by simp only [Finset.mem_range] at hi; omega
          apply mul_le_mul_of_nonneg_left
          · exact pow_right_mono₀ hm_div_d_ge hi_le
          · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt ht_pos) _)
      _ = (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := by
          rw [← Finset.sum_mul, mul_comm]
  -- Assemble: `∑ ≤ (m/d)^d · (1+t)^m ≤ (m/d)^d · e^d = (e m / d) ^ d`.
  calc (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ))
      ≤ (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := h_factor
    _ ≤ (↑m / ↑d) ^ d * ((1 + t) ^ m) := by
        apply mul_le_mul_of_nonneg_left h_partial_le_binom
        exact pow_nonneg (div_nonneg (le_of_lt hm_pos) (le_of_lt hd_pos)) d
    _ ≤ (↑m / ↑d) ^ d * Real.exp 1 ^ d := by
        apply mul_le_mul_of_nonneg_left h_exp_bound
        exact pow_nonneg (div_nonneg (le_of_lt hm_pos) (le_of_lt hd_pos)) d
    _ = (Real.exp 1 * ↑m / ↑d) ^ d := by
        rw [mul_div_assoc, ← mul_pow, mul_comm (Real.exp 1) _]

/-- **Exponential Sauer–Shelah bound.** If every set shattered by `C` has size at most `d`, and
`1 ≤ d ≤ m`, then the growth function obeys the closed exponential form
`GrowthFunction X C m ≤ (e · m / d) ^ d`. This chains the polynomial Sauer–Shelah bound
`growthFunction_le_sum_choose` with the binomial-tail inequality `sum_choose_le_exp_pow`. -/
theorem growthFunction_le_exp (C : ConceptClass X Bool) (d : ℕ)
    (hd : ∀ s : Finset X, _root_.Shatters X C s → s.card ≤ d) (hd1 : 1 ≤ d)
    {m : ℕ} (hm : d ≤ m) :
    (GrowthFunction X C m : ℝ) ≤ (Real.exp 1 * m / d) ^ d := by
  have h1 : GrowthFunction X C m ≤ ∑ k ∈ Finset.range (d + 1), m.choose k :=
    growthFunction_le_sum_choose C d hd m
  have h2 : (∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d :=
    sum_choose_le_exp_pow d m hd1 hm
  calc (↑(GrowthFunction X C m) : ℝ)
      ≤ ↑(∑ k ∈ Finset.range (d + 1), m.choose k) := by exact_mod_cast h1
    _ = (∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ)) := by push_cast; rfl
    _ ≤ (Real.exp 1 * m / d) ^ d := h2

/-! ## Layer B — the combinatorial packing bound -/

/-- **`δ`-packing of a concept class on a sample.** `P` is a `δ`-packing of `C` on the finite sample
`S` when every concept of `P` lies in `C` and any two distinct concepts of `P` disagree on strictly
more than a `δ`-fraction of `S` (measured in Hamming count: `δ · #S < #{x ∈ S | c₁ x ≠ c₂ x}`).

This is the genuine combinatorial packing predicate — it is *not* vacuous: it requires `P ⊆ C` and a
strict pairwise-separation lower bound on the per-sample disagreement count. -/
def IsPacking (C : ConceptClass X Bool) (S : Finset X) (P : Finset (X → Bool)) (δ : ℝ) : Prop :=
  ((↑P : Set (X → Bool)) ⊆ C) ∧ ∀ c₁ ∈ P, ∀ c₂ ∈ P, c₁ ≠ c₂ →
    δ * (S.card : ℝ) < ((S.filter (fun x => c₁ x ≠ c₂ x)).card : ℝ)

/-- **Packing ≤ growth function.** Any `δ`-packing with `0 ≤ δ` has cardinality at most the growth
function of `C` at the sample size: `#P ≤ GrowthFunction X C (#S)`.

The restriction map `c ↦ (fun x : ↥S => c x)` is injective on a packing: two concepts with equal
restriction agree on every point of `S`, so they disagree on none, contradicting the strict
separation `δ · #S < 0` once `δ · #S ≥ 0`. Injectivity identifies `#P` with the cardinality of the
image, which embeds into the `restrictionSet` whose `ncard` is bounded by the growth function. -/
theorem packing_card_le_growthFunction {C : ConceptClass X Bool} {S : Finset X}
    {P : Finset (X → Bool)} {δ : ℝ} (hδ : 0 ≤ δ) (hP : IsPacking C S P δ) :
    P.card ≤ GrowthFunction X C S.card := by
  classical
  obtain ⟨hsub, hsep⟩ := hP
  -- The restriction map onto the sample `S`.
  set r : (X → Bool) → (↥S → Bool) := fun c => fun x => c (x : X) with hr
  -- Step 1: injectivity of `r` on `↑P`.
  have hinj : Set.InjOn r (↑P : Set (X → Bool)) := by
    intro c₁ h1 c₂ h2 heq
    by_contra hne
    -- equal restrictions ⇒ agreement on every point of `S`
    have hagree : ∀ x ∈ S, c₁ x = c₂ x := by
      intro x hx
      have := congrFun heq ⟨x, hx⟩
      simpa [hr] using this
    -- ⇒ the disagreement set on `S` is empty
    have hfilter : (S.filter (fun x => c₁ x ≠ c₂ x)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx
      simp only [not_not]
      exact hagree x hx
    -- contradicts the strict separation, since `δ · #S ≥ 0`
    have hlt := hsep c₁ h1 c₂ h2 hne
    rw [hfilter] at hlt
    simp only [Finset.card_empty, Nat.cast_zero] at hlt
    have hnn : 0 ≤ δ * (S.card : ℝ) := mul_nonneg hδ (by positivity)
    linarith
  -- Step 2: `#P = #(image r)` by injectivity.
  have hcard_eq : (P.image r).card = P.card := Finset.card_image_of_injOn hinj
  -- Step 3: the image sits inside the restriction set.
  have hsubset : (↑(P.image r) : Set (↥S → Bool)) ⊆ restrictionSet C S := by
    intro f hf
    rw [Finset.coe_image, Set.mem_image] at hf
    obtain ⟨c, hcP, rfl⟩ := hf
    exact ⟨c, hsub hcP, fun x => rfl⟩
  -- Step 4: chain cardinalities up to the growth function.
  have hncard_le : ((↑(P.image r) : Set (↥S → Bool))).ncard ≤ (restrictionSet C S).ncard :=
    Set.ncard_le_ncard hsubset (Set.toFinite _)
  calc P.card = (P.image r).card := hcard_eq.symm
    _ = ((↑(P.image r) : Set (↥S → Bool))).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (restrictionSet C S).ncard := hncard_le
    _ ≤ GrowthFunction X C S.card := restrictionSet_ncard_le_growthFunction C rfl

/-- **Exponential packing bound (T2.5, `δ`-independent form).** Combining the combinatorial packing
bound with the exponential Sauer–Shelah corollary: any `δ`-packing of a class whose shattered sets
all have size `≤ d` (with `1 ≤ d ≤ #S`) satisfies `#P ≤ (e · #S / d) ^ d`.

This is the genuine deliverable. The *sharp* Haussler bound `#P ≤ e (d+1) (2e/δ) ^ d` (exponent
exactly `d`, no `log(1/δ)`) requires the one-inclusion-graph / shifting argument of Haussler 1995 and
is **not** proved here; it is left as a documented remark (see the module docstring). -/
theorem packing_card_le_exp {C : ConceptClass X Bool} {S : Finset X}
    {P : Finset (X → Bool)} {δ : ℝ} (hδ : 0 ≤ δ) (hP : IsPacking C S P δ) (d : ℕ)
    (hd : ∀ s : Finset X, _root_.Shatters X C s → s.card ≤ d) (hd1 : 1 ≤ d)
    (hm : d ≤ S.card) :
    (P.card : ℝ) ≤ (Real.exp 1 * S.card / d) ^ d := by
  calc (P.card : ℝ) ≤ (GrowthFunction X C S.card : ℝ) := by
        exact_mod_cast packing_card_le_growthFunction hδ hP
    _ ≤ (Real.exp 1 * S.card / d) ^ d := growthFunction_le_exp C d hd hd1 hm

/-!
## Remark — the sharp Haussler bound is not formalised here

The *sharp* packing bound of Haussler 1995,

`M(δ) ≤ e · (d + 1) · (2 e / δ) ^ d`,

has the optimal exponent `d` with **no spurious `log(1/δ)` factor** (naive Dudley chaining would give
`(1/δ) ^ d · log(1/δ)`). Removing that log requires the one-inclusion-graph degree / shifting
argument, which is a substantial combinatorial development not carried out in this module. The bound
delivered above — `#P ≤ Π_C(#S) ≤ (e · #S / d) ^ d` — is the honest, fully-formalised
`δ`-independent statement: it controls the packing by the growth function and is non-vacuous, but it
is weaker than the sharp constant. The sharp bound remains open here and is **not** faked.

Reference: D. Haussler, *Sphere packing numbers for subsets of the Boolean n-cube with bounded
Vapnik–Chervonenkis dimension*, J. Combin. Theory Ser. A 69(2):217–232 (1995).
-/
