/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.Finiteness
import FLT_Proofs.Complexity.IndependentVC.ShatterCount

/-!
# Polynomial growth implies finite VC dimension

If the growth function is bounded by a polynomial then the VC dimension is finite. The two
ingredients are now both available: a shattered set of size `m` forces growth `2 ^ m`
(`growthFunction_ge_two_pow_of_shatters`), and `2 ^ m` cannot stay below a polynomial for every `m`
(`no_unbounded_two_pow_le_poly`). The bridge is that an infinite VC dimension would produce
shattered sets of every size, by downward closure of shattering.

This is the criterion that delivers the finiteness of Boolean combinations and unions of finite-VC
classes: each has polynomially bounded growth (Sauer-Shelah on each component), so its VC dimension
is finite.

## Main results

* `shatters_of_subset`: shattering is closed under taking subsets of the sample.
* `two_pow_le_growthFunction_of_top`: an infinite VC dimension forces growth `≥ 2 ^ m` everywhere.
* `vcDim_lt_top_of_growth_poly`: eventual polynomial growth implies finite VC dimension.
-/

open Filter

universe u

variable {X : Type u}

/-- Shattering is closed under restriction of the sample: if `C` shatters `S` and `T ⊆ S`, then `C`
shatters `T`. Any labelling of `T` extends to a labelling of `S`, which is realized. -/
theorem shatters_of_subset {C : ConceptClass X Bool} {S T : Finset X}
    (hS : Shatters X C S) (hTS : T ⊆ S) : Shatters X C T := by
  classical
  intro f
  obtain ⟨c, hc, hcg⟩ := hS (fun y => if h : (y : X) ∈ T then f ⟨(y : X), h⟩ else false)
  refine ⟨c, hc, fun x => ?_⟩
  have hx := hcg ⟨(x : X), hTS x.2⟩
  simp only [dif_pos x.2] at hx
  rw [hx]

/-- An infinite VC dimension forces the growth function to be at least `2 ^ m` at every size: it
shatters sets of every size, by `iSup₂_eq_top` and downward closure. -/
theorem two_pow_le_growthFunction_of_top {C : ConceptClass X Bool} (hinf : VCDim X C = ⊤) (m : ℕ) :
    2 ^ m ≤ GrowthFunction X C m := by
  have hunb := (iSup₂_eq_top
    (fun (S : Finset X) (_ : Shatters X C S) => (S.card : WithTop ℕ))).mp
    (by rw [VCDim] at hinf; exact hinf)
  obtain ⟨S, hShat, hmS⟩ := hunb m (WithTop.coe_lt_top m)
  have hmS' : m < S.card := by exact_mod_cast hmS
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (le_of_lt hmS')
  have hTshat : Shatters X C T := shatters_of_subset hShat hTS
  have := growthFunction_ge_two_pow_of_shatters hTshat
  rwa [hTcard] at this

/-- **Polynomial growth implies finite VC dimension.** If `GrowthFunction X C m ≤ K · m ^ d` for all
large `m`, then `VCDim X C < ⊤`: an infinite VC dimension produces shattered sets of every size,
forcing `2 ^ m ≤ K · m ^ d` for arbitrarily large `m`, which is impossible. The hypothesis is the
eventually filter (the `∀ m` form is unsatisfiable at `m = 0`); Sauer-Shelah supplies it for `m ≥ d`. -/
theorem vcDim_lt_top_of_growth_poly {C : ConceptClass X Bool} (K : ℝ) (d : ℕ)
    (hpoly : ∀ᶠ m : ℕ in atTop, (GrowthFunction X C m : ℝ) ≤ K * (m : ℝ) ^ d) : VCDim X C < ⊤ := by
  by_contra htop
  push_neg at htop
  have hinf : VCDim X C = ⊤ := le_antisymm le_top htop
  apply no_eventually_two_pow_le_poly K d
  filter_upwards [hpoly] with m hm
  calc (2 : ℝ) ^ m = ((2 ^ m : ℕ) : ℝ) := by norm_cast
    _ ≤ (GrowthFunction X C m : ℝ) := by exact_mod_cast two_pow_le_growthFunction_of_top hinf m
    _ ≤ K * (m : ℝ) ^ d := hm
