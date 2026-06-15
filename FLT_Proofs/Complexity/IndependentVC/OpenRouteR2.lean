/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.VCDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Open route R2: the ε-net size gap

An ε-net for a concept class `C` on a finite ground set `P` is a subset `N ⊆ P` meeting every concept
that is ε-heavy on `P` — a positive point of every range covering at least an ε-fraction of `P`. This
is the purely combinatorial form (a fractional threshold on a `Finset`, no measure theory).

The ε-net theorem (Haussler–Welzl) gives, for a class of VC dimension `d`, an ε-net of size
`O((d/ε) · log(1/ε))`; Komlós–Pach–Woeginger show this is tight in general. **R2 (open):** for which
classes can the logarithmic factor be removed — i.e. which bounded-VC classes admit ε-nets of size
`O(d/ε)`? Linear-size nets are known for some geometric ranges (half-planes) and ruled out for others;
a clean structural characterization is open.

This file gives the combinatorial definition, settles the trivial case (`P` itself is an ε-net), and
states the size bound `EpsilonNetSizeBound` as the formalization target. That bound is a known theorem
whose proof is probabilistic (the double-sampling argument), so it is stated, not proved here.

References: D. Haussler, E. Welzl, *ε-nets and simplex range queries*, Discrete Comput. Geom. 2 (1987);
J. Komlós, J. Pach, G. Woeginger, *Almost tight bounds for ε-nets*, Discrete Comput. Geom. 7 (1992).

## Main results

* `IsEpsilonNet`: the combinatorial ε-net property on a finite ground set.
* `isEpsilonNet_self`: the ground set is an ε-net (the trivial bound).
* `EpsilonNetSizeBound`: the `O((d/ε) log(1/ε))` size bound — the open formalization target.
-/

open Finset

universe u

variable {X : Type u}

/-- `IsEpsilonNet C P N ε`: `N ⊆ P` meets every concept of `C` that is ε-heavy on `P` (covers at
least an `ε`-fraction of `P`). The ε-net problem asks for such an `N` of small cardinality. -/
def IsEpsilonNet (C : ConceptClass X Bool) (P N : Finset X) (ε : ℝ) : Prop :=
  N ⊆ P ∧ ∀ c ∈ C, ε * (P.card : ℝ) ≤ ((P.filter (fun x => c x = true)).card : ℝ) →
    ∃ x ∈ N, c x = true

/-- **The ground set is an ε-net.** Trivially, `P` meets every ε-heavy concept: an ε-heavy concept on
a nonempty ground set has at least one positive point. This is the `|N| = |P|` baseline that the
ε-net theorem improves to `O((d/ε) log(1/ε))`. -/
theorem isEpsilonNet_self (C : ConceptClass X Bool) {P : Finset X} {ε : ℝ}
    (hε : 0 < ε) (hP : 0 < P.card) : IsEpsilonNet C P P ε := by
  refine ⟨subset_rfl, fun c _ hheavy => ?_⟩
  have hPr : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast hP
  have hpos : (0 : ℝ) < ((P.filter (fun x => c x = true)).card : ℝ) :=
    lt_of_lt_of_le (mul_pos hε hPr) hheavy
  have hcard : 0 < (P.filter (fun x => c x = true)).card := by exact_mod_cast hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

/-- **The ε-net size bound** (Haussler–Welzl) — R2's formalization target. A universal constant `κ`
bounds, for every VC-dimension-`d` class, the size of a smallest ε-net by `κ · (d/ε) · log(1/ε)`. This
is a known theorem; its proof is probabilistic (double sampling) and is not carried out in this
combinatorial module. R2 is whether the `log(1/ε)` factor is removable for specific classes. -/
def EpsilonNetSizeBound (X : Type u) : Prop :=
  ∃ κ : ℝ, ∀ (C : ConceptClass X Bool) (d : ℕ), VCDim X C ≤ (d : WithTop ℕ) →
    ∀ (P : Finset X) (ε : ℝ), 0 < ε → ε < 1 →
      ∃ N : Finset X, IsEpsilonNet C P N ε ∧ (N.card : ℝ) ≤ κ * (d / ε) * Real.log (1 / ε)
