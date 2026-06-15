/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.OpenRouteR2

/-!
# ε-approximation ⟹ ε-net (the combinatorial reduction)

This file supplies the missing combinatorial link in the R2 route. The kernel proves
T2.4 (uniform convergence / ε-approximation: `vcdim_finite_imp_uc'`) but states T2.3
(the ε-net **size** bound, `EpsilonNetSizeBound`) only as a target, because its proof is
probabilistic (Haussler–Welzl double sampling). Between those two sits a *purely
combinatorial* fact that needs no measure theory and no probability:

> **A `(ε/2)`-approximation of `P` is an `ε`-net of `P`.**

We define ε-approximation combinatorially — `N ⊆ P` reproduces every concept's
`P`-frequency up to an additive `ε`, measured by the empirical (uniform-on-`P`) measure —
and prove the reduction as a finite-set inequality. This is the standard textbook step
that turns a uniform-convergence guarantee into an ε-net (e.g. Vapnik–Chervonenkis;
Mohri–Rostamizadeh–Talwalkar, *Foundations of Machine Learning*, Ch. 3): once the
empirical frequency of every concept is within `ε/2` of its true frequency, every concept
of true frequency `≥ ε` has empirical frequency `≥ ε/2 > 0`, so the sample `N` meets it.

It advances R2 concretely: combined with the existence of small `(ε/2)`-approximations
(the content of T2.4 / `EpsilonNetSizeBound`'s probabilistic input), this reduction is the
deterministic half of the Haussler–Welzl chain
`bounded VC ⟹ small ε-approximation ⟹ small ε-net`.

## Main results

* `IsEpsilonApprox`: the combinatorial ε-approximation property on a finite ground set.
* `isEpsilonApprox_self`: `P` is a `0`-approximation of itself (the reduction is non-vacuous).
* `isEpsilonNet_of_isEpsilonApprox`: a nonempty `(ε/2)`-approximation is an `ε`-net.
-/

open Finset

universe u

variable {X : Type u}

/-- `IsEpsilonApprox C P N ε`: `N ⊆ P` and, for every concept `c ∈ C`, the empirical
frequency of `c` on `N` differs from its frequency on `P` by at most `ε`. Frequencies are
taken with respect to the uniform (counting) measure on each finite set, so this is the
purely combinatorial form of an ε-approximation — no measure theory. The ground set `P`
is a `0`-approximation of itself (`isEpsilonApprox_self`); the ε-approximation problem
asks for such an `N` of small cardinality. -/
def IsEpsilonApprox (C : ConceptClass X Bool) (P N : Finset X) (ε : ℝ) : Prop :=
  N ⊆ P ∧ ∀ c ∈ C,
    |((N.filter (fun x => c x = true)).card : ℝ) / (N.card : ℝ)
      - ((P.filter (fun x => c x = true)).card : ℝ) / (P.card : ℝ)| ≤ ε

/-- **The ground set is a `0`-approximation of itself.** This is the `ε = 0` baseline: it
shows `IsEpsilonApprox` is non-vacuously satisfiable, and pins the definition's orientation
(the difference of the two frequencies is literally `0`). -/
theorem isEpsilonApprox_self (C : ConceptClass X Bool) (P : Finset X) :
    IsEpsilonApprox C P P 0 := by
  refine ⟨subset_rfl, fun c _ => ?_⟩
  simp

/-- **An `(ε/2)`-approximation is an `ε`-net.** If `N ⊆ P` reproduces every concept's
`P`-frequency to within `ε/2`, then `N` meets every `ε`-heavy concept: a concept with
`P`-frequency `≥ ε` has `N`-frequency `≥ ε − ε/2 = ε/2 > 0`, so `N` contains a positive
point of it.

This is the deterministic combinatorial reduction at the heart of the R2 route. The only
extra hypothesis is `0 < N.card` (a sample must be nonempty to certify any positive
frequency); `0 < ε` is the usual ε-net nondegeneracy. The proof is a finite-set inequality
with no probability and no measure theory — it is the missing link between the kernel's
T2.4 (ε-approximation exists) and the ε-net statement. -/
theorem isEpsilonNet_of_isEpsilonApprox (C : ConceptClass X Bool) {P N : Finset X} {ε : ℝ}
    (hε : 0 < ε) (hN : 0 < N.card) (happrox : IsEpsilonApprox C P N (ε / 2)) :
    IsEpsilonNet C P N ε := by
  obtain ⟨hsub, hfreq⟩ := happrox
  refine ⟨hsub, fun c hc hheavy => ?_⟩
  -- Frequencies as reals, with positive denominators.
  set nN : ℝ := ((N.filter (fun x => c x = true)).card : ℝ) with hnN
  set nP : ℝ := ((P.filter (fun x => c x = true)).card : ℝ) with hnP
  have hNr : (0 : ℝ) < (N.card : ℝ) := by exact_mod_cast hN
  have hPpos : 0 < P.card := by
    -- `P` is nonempty because `N ⊆ P` is nonempty.
    have : 0 < N.card := hN
    have hle : N.card ≤ P.card := Finset.card_le_card hsub
    omega
  have hPr : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast hPpos
  -- ε-heaviness of `c` on `P`, rewritten as a frequency lower bound: ε ≤ nP / P.card.
  have hheavy' : ε ≤ nP / (P.card : ℝ) := by
    rw [le_div_iff₀ hPr]
    exact hheavy
  -- The approximation gives a two-sided bound; extract the lower side.
  have habs := hfreq c hc
  rw [abs_le] at habs
  have hlower : -(ε / 2) ≤ nN / (N.card : ℝ) - nP / (P.card : ℝ) := habs.1
  -- Chain: nN / N.card ≥ nP / P.card − ε/2 ≥ ε − ε/2 = ε/2 > 0.
  have hfreqN : ε / 2 ≤ nN / (N.card : ℝ) := by
    have h1 : nP / (P.card : ℝ) - ε / 2 ≤ nN / (N.card : ℝ) := by linarith
    linarith
  -- Positive frequency forces a positive count of positive points in `N`.
  have hpos : (0 : ℝ) < nN := by
    have hquot_pos : (0 : ℝ) < nN / (N.card : ℝ) := lt_of_lt_of_le (by linarith) hfreqN
    have := (div_pos_iff_of_pos_right hNr).mp hquot_pos
    exact this
  have hcard : 0 < (N.filter (fun x => c x = true)).card := by
    rw [hnN] at hpos; exact_mod_cast hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
