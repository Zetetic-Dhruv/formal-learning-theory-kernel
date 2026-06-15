/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.VCDimension
import FLT_Proofs.Complexity.IndependentVC.VCFinite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Dudley's VC-dimension bound for linear sign classes

**Dudley (1978), Wenocur–Dudley (1981).** Let `V` be a finite-dimensional subspace of the real
functions `X → ℝ`. The class of sign patterns `x ↦ (0 < g x)` for `g ∈ V` has VC dimension at most
`dim V`.

## Main definitions

* `signClass V` : the concept class `{ x ↦ decide (0 < g x) | g ∈ V }`.

## Main results

* `vcDim_signClass_le` : `VCDim X (signClass V) ≤ finrank ℝ V`.

## Proof idea

Suppose a finite set `S` with `|S| > dim V` is shattered. The `|S|` evaluation functionals
`evalAt x : V →ₗ[ℝ] ℝ`, `g ↦ g x`, live in the dual space `Module.Dual ℝ V`, which has dimension
`dim V < |S|`. Hence they are linearly dependent: there is a nontrivial `α : ↥S → ℝ` with
`∑ i, α i • evalAt i = 0`, i.e. `∑ i, α i * g i = 0` for every `g ∈ V`. After possibly replacing
`α` by `-α` we may assume some `α i > 0`. Shatter `S` with the labelling `i ↦ (0 < α i)`: the
witnessing `g ∈ V` then has `0 < g i ↔ 0 < α i` for every `i ∈ S`. Each summand `α i * g i` is
`≥ 0` (both factors share sign), and at least one is `> 0`, so `0 < ∑ i, α i * g i = 0`, a
contradiction.
-/

open scoped BigOperators

universe u

variable {X : Type u}

/-- The sign-pattern concept class of a subspace `V ≤ (X → ℝ)`: all concepts of the form
`x ↦ decide (0 < g x)` for some `g ∈ V`. -/
def signClass (V : Submodule ℝ (X → ℝ)) : ConceptClass X Bool :=
  { c | ∃ g ∈ V, c = fun x => decide (0 < g x) }

/-- Evaluation at a point `x : X` as a linear functional on `V`: `g ↦ (g : X → ℝ) x`. -/
noncomputable def evalAt (V : Submodule ℝ (X → ℝ)) (x : X) : V →ₗ[ℝ] ℝ :=
  (LinearMap.proj x).comp V.subtype

@[simp]
theorem evalAt_apply (V : Submodule ℝ (X → ℝ)) (x : X) (g : V) :
    evalAt V x g = (g : X → ℝ) x := rfl

/-- **Dudley's bound.** The VC dimension of the linear sign class of a finite-dimensional subspace
`V ≤ (X → ℝ)` is at most `dim V`. -/
theorem vcDim_signClass_le (V : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ V] :
    VCDim X (signClass V) ≤ (Module.finrank ℝ V : WithTop ℕ) := by
  classical
  -- It suffices to bound the cardinality of every shattered set.
  refine iSup₂_le fun S hS => ?_
  rw [Nat.cast_le]
  by_contra hlt
  push_neg at hlt
  -- `hlt : finrank ℝ V < S.card`. The `|S|` evaluation functionals are linearly dependent.
  have hcard : Module.finrank ℝ (V →ₗ[ℝ] ℝ) < Fintype.card (↥S) := by
    rw [Subspace.dual_finrank_eq, Fintype.card_coe]
    exact hlt
  have hdep : ¬ LinearIndependent ℝ (fun i : ↥S => evalAt V (i : X)) := by
    intro hli
    exact absurd hli.fintype_card_le_finrank (not_le.mpr hcard)
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨α, hsum, hne⟩ := hdep
  -- Evaluating the functional relation at any `g ∈ V` gives `∑ i, α i * g i = 0`.
  have hkey : ∀ g : V, ∑ i : ↥S, α i * (g : X → ℝ) (i : X) = 0 := by
    intro g
    have := congrArg (fun (f : V →ₗ[ℝ] ℝ) => f g) hsum
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using this
  -- WLOG some `α i > 0`; otherwise replace `α` by `-α`.
  -- Package the contradiction-producing step so both cases reuse it.
  have main : ∀ β : ↥S → ℝ, (∀ g : V, ∑ i : ↥S, β i * (g : X → ℝ) (i : X) = 0) →
      (∃ i, 0 < β i) → False := by
    intro β hβ hpos
    -- Shatter `S` with the labelling `i ↦ decide (0 < β i)`.
    obtain ⟨c, hc, hcg⟩ := hS (fun i => decide (0 < β i))
    obtain ⟨g, hgV, rfl⟩ := hc
    -- From shattering: for each `i ∈ S`, `0 < g i ↔ 0 < β i`.
    have hsign : ∀ i : ↥S, (0 < g (i : X)) ↔ (0 < β i) := by
      intro i
      have h := hcg i
      simp only [decide_eq_decide] at h
      exact h
    -- Each summand is nonnegative; the positive index contributes a strictly positive one.
    have hnonneg : ∀ i ∈ (Finset.univ : Finset (↥S)), 0 ≤ β i * g (i : X) := by
      intro i _
      rcases lt_trichotomy (β i) 0 with hb | hb | hb
      · -- `β i < 0` ⟹ `¬ 0 < β i` ⟹ `¬ 0 < g i` ⟹ `g i ≤ 0`; product of nonpositives.
        have hgnp : g (i : X) ≤ 0 := by
          have : ¬ 0 < g (i : X) := by
            rw [hsign i]; exact not_lt.mpr (le_of_lt hb)
          exact not_lt.mp this
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt hb) hgnp
      · -- `β i = 0` ⟹ summand is `0`.
        rw [hb]; simp
      · -- `0 < β i` ⟹ `0 < g i`, product of positives.
        have hgpos : 0 < g (i : X) := (hsign i).mpr hb
        exact le_of_lt (mul_pos hb hgpos)
    obtain ⟨i₀, hi₀⟩ := hpos
    have hpos₀ : 0 < β i₀ * g (i₀ : X) := by
      have hgpos : 0 < g (i₀ : X) := (hsign i₀).mpr hi₀
      exact mul_pos hi₀ hgpos
    have hsumpos : 0 < ∑ i : ↥S, β i * g (i : X) :=
      Finset.sum_pos' hnonneg ⟨i₀, Finset.mem_univ i₀, hpos₀⟩
    have hsumzero : ∑ i : ↥S, β i * g (i : X) = 0 := hβ ⟨g, hgV⟩
    exact absurd hsumzero (ne_of_gt hsumpos)
  -- Resolve the WLOG: either `α` already has a positive entry, or `-α` does.
  rcases (em (∃ i, 0 < α i)) with hpos | hpos
  · exact main α hkey hpos
  · push_neg at hpos
    -- all `α i ≤ 0` and some `α i ≠ 0`, so some `α i < 0`, hence `-α` has a positive entry.
    obtain ⟨j, hj⟩ := hne
    have hjneg : α j < 0 := lt_of_le_of_ne (hpos j) hj
    refine main (fun i => - α i) ?_ ⟨j, by simpa using hjneg⟩
    intro g
    have := hkey g
    rw [← neg_eq_zero] at this
    rw [← this, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
