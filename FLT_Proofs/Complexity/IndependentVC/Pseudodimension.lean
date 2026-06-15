/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.Structures
import FLT_Proofs.Complexity.IndependentVC.Dudley
import FLT_Proofs.Complexity.IndependentVC.Monotone
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dudley's pseudodimension bound for finite-dimensional spaces of real functions

**Pollard (1984), Haussler (1992).** Let `V` be a finite-dimensional subspace of the real
functions `X → ℝ`. The *pseudodimension* of `V` (viewed as a class of real-valued concepts) is at
most `dim V + 1`.

The pseudodimension is the real-valued analogue of the VC dimension: a finite set `S` is
*pseudo-shattered* with thresholds `t : X → ℝ` when, for every Boolean labelling `b`, some `c ∈ C`
sits above `t` on the `true` points (`c x ≥ t x`) and strictly below `t` on the `false` points
(`c x < t x`).

## Main definitions

* `signClassLE W` : the *non-strict* sign-pattern class `{ x ↦ decide (0 ≤ g x) | g ∈ W }`.

## Main results

* `vcDim_signClassLE_le` : `VCDim X (signClassLE W) ≤ finrank ℝ W` — the non-strict counterpart of
  Dudley's `vcDim_signClass_le`.
* `pseudodim_le` : `Pseudodimension X (↑V) ≤ finrank ℝ V + 1`.

## Proof idea

The pseudodimension reduces to a *non-strict* sign-class VC bound. If `S` is pseudo-shattered by `V`
with threshold `t`, then for the enlarged space `W := V ⊔ ℝ∙t` the affine condition `c x ≥ t x`
becomes the homogeneous sign condition `0 ≤ (c - t) x` for `c - t ∈ W`. Concretely each labelling's
witness `f ∈ V` lifts to `f ∈ W` (since `V ≤ W`) and satisfies `0 ≤ f x ↔ … ` after a translation;
we package this so that `S` is genuinely VC-shattered by `signClassLE W`. Hence

  `|S| ≤ VCDim X (signClassLE W) ≤ finrank ℝ W ≤ finrank ℝ V + finrank ℝ (ℝ∙t) ≤ finrank ℝ V + 1`.

The non-strict Dudley bound `vcDim_signClassLE_le` is proved by the identical dual-space
linear-dependence argument as `vcDim_signClass_le`. The boundary `0 ≤ g x` is handled by extracting
the *strictly negative* coefficient: WLOG some `α i < 0` (otherwise replace `α` by `-α`); the
labelling `i ↦ decide (0 ≤ α i)` then forces `g i < 0` strictly at that index, so the summand
`α i * g i > 0` is strictly positive while every other summand is `≥ 0`, giving `0 < ∑ = 0`.
-/

open scoped BigOperators

universe u

variable {X : Type u}

/-- The *non-strict* sign-pattern concept class of a subspace `W ≤ (X → ℝ)`: all concepts of the
form `x ↦ decide (0 ≤ g x)` for some `g ∈ W`. This is the `≤`-counterpart of `signClass`, matching
the non-strict `c x ≥ t x` convention of `Pseudodimension`. -/
def signClassLE (W : Submodule ℝ (X → ℝ)) : ConceptClass X Bool :=
  { c | ∃ g ∈ W, c = fun x => decide (0 ≤ g x) }

/-- **Non-strict Dudley bound.** The VC dimension of the non-strict linear sign class of a
finite-dimensional subspace `W ≤ (X → ℝ)` is at most `dim W`. Same dual-space argument as
`vcDim_signClass_le`, but the contradiction is extracted from a strictly *negative* coefficient so
that the boundary `0 ≤ g x` cannot annihilate the strictly positive summand. -/
theorem vcDim_signClassLE_le (W : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ W] :
    VCDim X (signClassLE W) ≤ (Module.finrank ℝ W : WithTop ℕ) := by
  classical
  -- It suffices to bound the cardinality of every shattered set.
  refine iSup₂_le fun S hS => ?_
  rw [Nat.cast_le]
  by_contra hlt
  push_neg at hlt
  -- `hlt : finrank ℝ W < S.card`. The `|S|` evaluation functionals are linearly dependent.
  have hcard : Module.finrank ℝ (W →ₗ[ℝ] ℝ) < Fintype.card (↥S) := by
    rw [Subspace.dual_finrank_eq, Fintype.card_coe]
    exact hlt
  have hdep : ¬ LinearIndependent ℝ (fun i : ↥S => evalAt W (i : X)) := by
    intro hli
    exact absurd hli.fintype_card_le_finrank (not_le.mpr hcard)
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨α, hsum, hne⟩ := hdep
  -- Evaluating the functional relation at any `g ∈ W` gives `∑ i, α i * g i = 0`.
  have hkey : ∀ g : W, ∑ i : ↥S, α i * (g : X → ℝ) (i : X) = 0 := by
    intro g
    have := congrArg (fun (f : W →ₗ[ℝ] ℝ) => f g) hsum
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using this
  -- WLOG some `α i < 0`; otherwise replace `α` by `-α`.
  -- Package the contradiction-producing step so both cases reuse it.
  have main : ∀ β : ↥S → ℝ, (∀ g : W, ∑ i : ↥S, β i * (g : X → ℝ) (i : X) = 0) →
      (∃ i, β i < 0) → False := by
    intro β hβ hneg
    -- Shatter `S` with the labelling `i ↦ decide (0 ≤ β i)`.
    obtain ⟨c, hc, hcg⟩ := hS (fun i => decide (0 ≤ β i))
    obtain ⟨g, hgW, rfl⟩ := hc
    -- From shattering: for each `i ∈ S`, `0 ≤ g i ↔ 0 ≤ β i`.
    have hsign : ∀ i : ↥S, (0 ≤ g (i : X)) ↔ (0 ≤ β i) := by
      intro i
      have h := hcg i
      simp only [decide_eq_decide] at h
      exact h
    -- Each summand is nonnegative; the strictly-negative index contributes a strictly positive one.
    have hnonneg : ∀ i ∈ (Finset.univ : Finset (↥S)), 0 ≤ β i * g (i : X) := by
      intro i _
      rcases lt_trichotomy (β i) 0 with hb | hb | hb
      · -- `β i < 0` ⟹ `¬ 0 ≤ β i` ⟹ `¬ 0 ≤ g i` ⟹ `g i < 0`; product of negatives.
        have hgneg : g (i : X) < 0 := by
          have hnot : ¬ 0 ≤ g (i : X) := by
            rw [hsign i]; exact not_le.mpr hb
          exact not_le.mp hnot
        exact le_of_lt (mul_pos_of_neg_of_neg hb hgneg)
      · -- `β i = 0` ⟹ summand is `0`.
        rw [hb]; simp
      · -- `0 < β i` ⟹ `0 ≤ β i` ⟹ `0 ≤ g i`; product of nonnegatives.
        have hgnn : 0 ≤ g (i : X) := (hsign i).mpr (le_of_lt hb)
        exact mul_nonneg (le_of_lt hb) hgnn
    obtain ⟨i₀, hi₀⟩ := hneg
    have hpos₀ : 0 < β i₀ * g (i₀ : X) := by
      have hgneg : g (i₀ : X) < 0 := by
        have hnot : ¬ 0 ≤ g (i₀ : X) := by
          rw [hsign i₀]; exact not_le.mpr hi₀
        exact not_le.mp hnot
      exact mul_pos_of_neg_of_neg hi₀ hgneg
    have hsumpos : 0 < ∑ i : ↥S, β i * g (i : X) :=
      Finset.sum_pos' hnonneg ⟨i₀, Finset.mem_univ i₀, hpos₀⟩
    have hsumzero : ∑ i : ↥S, β i * g (i : X) = 0 := hβ ⟨g, hgW⟩
    exact absurd hsumzero (ne_of_gt hsumpos)
  -- Resolve the WLOG: either `α` already has a negative entry, or `-α` does.
  rcases (em (∃ i, α i < 0)) with hneg | hneg
  · exact main α hkey hneg
  · push_neg at hneg
    -- all `α i ≥ 0` and some `α i ≠ 0`, so some `α i > 0`, hence `-α` has a negative entry.
    obtain ⟨j, hj⟩ := hne
    have hjpos : 0 < α j := lt_of_le_of_ne (hneg j) (Ne.symm hj)
    refine main (fun i => - α i) ?_ ⟨j, by simpa using hjpos⟩
    intro g
    have := hkey g
    rw [← neg_eq_zero] at this
    rw [← this, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- `finrank ℝ (ℝ ∙ t) ≤ 1` for any `t : X → ℝ` (with equality when `t ≠ 0`). -/
theorem finrank_span_singleton_le_one (t : X → ℝ) :
    Module.finrank ℝ (Submodule.span ℝ ({t} : Set (X → ℝ))) ≤ 1 := by
  classical
  have h := finrank_span_le_card (R := ℝ) ({t} : Set (X → ℝ))
  simpa using h

/-- **Dudley's pseudodimension bound.** The pseudodimension of a finite-dimensional subspace
`V ≤ (X → ℝ)`, viewed as a class of real-valued concepts, is at most `dim V + 1`.

This is the real-valued analogue of `vcDim_signClass_le`. The proof reduces pseudo-shattering with a
threshold `t` to non-strict sign-shattering on the enlarged space `W := V ⊔ ℝ∙t`, then applies the
non-strict Dudley bound `vcDim_signClassLE_le` and `finrank_add_le_finrank_add_finrank`. -/
theorem pseudodim_le (V : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ V] :
    Pseudodimension X ((↑V : Set (X → ℝ)) : ConceptClass X ℝ) ≤
      (Module.finrank ℝ V + 1 : WithTop ℕ) := by
  classical
  -- Reduce to bounding the cardinality of every pseudo-shattered `(S, t)`.
  refine iSup₂_le fun S t => iSup_le fun hShat => ?_
  -- The enlarged space `W := V ⊔ ℝ∙t`.
  set W : Submodule ℝ (X → ℝ) := V ⊔ Submodule.span ℝ ({t} : Set (X → ℝ)) with hW
  -- `S` is VC-shattered by `signClassLE W`: each labelling's pseudo-witness `c ∈ V` lifts to
  -- `c - t ∈ W`, and `0 ≤ (c - t) x ↔ (the requested label)`.
  have hVCshat : Shatters X (signClassLE W) S := by
    intro f
    -- Extend `f : ↥S → Bool` to a total labelling `b : X → Bool`.
    obtain ⟨c, hcV, hc⟩ :=
      hShat (fun x => if h : x ∈ S then f ⟨x, h⟩ else false)
    -- View the witness as a plain function `g := (c : X → ℝ)` in `V`.
    set g : X → ℝ := c with hg
    have hgV : g ∈ V := hcV
    -- The translate `g - t` lies in `W = V ⊔ ℝ∙t`.
    have hsubW : g - t ∈ W := by
      rw [hW]
      exact Submodule.sub_mem_sup hgV (Submodule.subset_span (Set.mem_singleton t))
    refine ⟨fun x => decide (0 ≤ (g - t) x), ⟨g - t, hsubW, rfl⟩, ?_⟩
    intro x
    have hxS : (x : X) ∈ S := x.2
    have hxlab : (if h : (x : X) ∈ S then f ⟨(x : X), h⟩ else false) = f x := by
      rw [dif_pos hxS]
    have hpair := hc (x : X) hxS
    have hval : (g - t) (x : X) = g (x : X) - t (x : X) := rfl
    -- Discriminate on the requested Boolean label `f x`.
    rcases hfb : f x with _ | _
    · -- `f x = false`: pseudo-shattering gives `c x < t x`, so `¬ 0 ≤ g x - t x`.
      have hb : (if h : (x : X) ∈ S then f ⟨(x : X), h⟩ else false) = false := by
        rw [hxlab]; exact hfb
      have hlt : (c : X → ℝ) (x : X) < t (x : X) := hpair.2 hb
      have hneg : ¬ (0 ≤ (g - t) (x : X)) := by
        rw [hval, sub_nonneg]; exact not_le.mpr hlt
      simp only [decide_eq_false_iff_not]
      exact hneg
    · -- `f x = true`: pseudo-shattering gives `c x ≥ t x`, so `0 ≤ g x - t x`.
      have hb : (if h : (x : X) ∈ S then f ⟨(x : X), h⟩ else false) = true := by
        rw [hxlab]; exact hfb
      have hge : (c : X → ℝ) (x : X) ≥ t (x : X) := hpair.1 hb
      have hpos : (0 ≤ (g - t) (x : X)) := by
        rw [hval, sub_nonneg]; exact hge
      simp only [decide_eq_true_eq]
      exact hpos
  -- Now bound: `|S| ≤ VCDim (signClassLE W) ≤ finrank W ≤ finrank V + 1`.
  have h1 : (S.card : WithTop ℕ) ≤ VCDim X (signClassLE W) := by
    rw [VCDim]
    exact le_iSup₂_of_le S hVCshat le_rfl
  have h2 : VCDim X (signClassLE W) ≤ (Module.finrank ℝ W : WithTop ℕ) :=
    vcDim_signClassLE_le W
  have h3 : Module.finrank ℝ W ≤ Module.finrank ℝ V + 1 := by
    rw [hW]
    calc Module.finrank ℝ (V ⊔ Submodule.span ℝ ({t} : Set (X → ℝ)) : Submodule ℝ (X → ℝ))
        ≤ Module.finrank ℝ V + Module.finrank ℝ (Submodule.span ℝ ({t} : Set (X → ℝ))) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ Module.finrank ℝ V + 1 := by
          exact Nat.add_le_add_left (finrank_span_singleton_le_one t) _
  calc (S.card : WithTop ℕ)
      ≤ VCDim X (signClassLE W) := h1
    _ ≤ (Module.finrank ℝ W : WithTop ℕ) := h2
    _ ≤ (Module.finrank ℝ V + 1 : WithTop ℕ) := by exact_mod_cast h3

/-- **Fat shattering is no larger than pseudo-shattering.** A `γ`-fat-shattered configuration
(`c x ≥ t x + γ` / `c x ≤ t x - γ`) satisfies the pseudo-shattering conditions (`c x ≥ t x` /
`c x < t x`) with the same sample and thresholds, since `γ > 0`. Hence the fat-shattering dimension
is bounded by the pseudodimension at every scale. -/
theorem fatShatteringDim_le_pseudodim (C : ConceptClass X ℝ) {γ : ℝ} (hγ : 0 < γ) :
    FatShatteringDim X C γ hγ ≤ Pseudodimension X C := by
  rw [FatShatteringDim]
  refine iSup_le fun S => iSup_le fun t => iSup_le fun hfat => ?_
  have hpseudo : ∀ b : X → Bool, ∃ c ∈ C, ∀ x ∈ S,
      (b x = true → c x ≥ t x) ∧ (b x = false → c x < t x) := by
    intro b
    obtain ⟨c, hcC, hc⟩ := hfat b
    refine ⟨c, hcC, fun x hx => ?_⟩
    obtain ⟨htrue, hfalse⟩ := hc x hx
    exact ⟨fun hb => by have := htrue hb; linarith, fun hb => by have := hfalse hb; linarith⟩
  rw [Pseudodimension]
  exact le_iSup_of_le S (le_iSup_of_le t (le_iSup_of_le hpseudo le_rfl))

/-- **Dudley's fat-shattering bound.** At every scale `γ > 0`, the fat-shattering dimension of a
finite-dimensional space of real functions is at most `dim V + 1`. Immediate from
`fatShatteringDim_le_pseudodim` and `pseudodim_le`. -/
theorem fatShatteringDim_le (V : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ V] {γ : ℝ} (hγ : 0 < γ) :
    FatShatteringDim X ((↑V : Set (X → ℝ)) : ConceptClass X ℝ) γ hγ
      ≤ (Module.finrank ℝ V + 1 : WithTop ℕ) :=
  (fatShatteringDim_le_pseudodim _ hγ).trans (pseudodim_le V)
