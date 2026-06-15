/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.Dual

/-!
# Assouad's dual VC bound and dual finiteness

The companion of the bidual lower bound (`vcDim_le_biDual`): Assouad's upper bound
`VCDim(dualClass C) ≤ 2^(VCDim C + 1) − 1`, established here for the independent dual class.

The engine is a coding lemma: if the dual shatters a set `S` of at least `2^(d+1)` concepts, then `C`
shatters a set of `d + 1` points. Index `2^(d+1)` of the concepts by bitstrings `Fin (d+1) → Bool`;
for each coordinate `j`, dual shattering yields a point `x_j` reading off the `j`-th bit, and the
`x_j` are distinct and shattered by `C`. With `VCDim C ≤ d` this forces `S.card < 2^(d+1)`.

The payoff is `vcDim_dualClass_lt_top`: the dual of a finite-VC class is again finite-VC — VC
finiteness is a self-dual property. Together with `vcDim_le_biDual` the dual dimension is sandwiched.

Reference: P. Assouad, *Densité et dimension*, Annales de l'Institut Fourier 33 (1983), 233–282.

## Main results

* `dualClass_shatters_imp_shatters`: a large dual-shattered set yields a primal-shattered set.
* `vcDim_dualClass_le`: Assouad's bound `VCDim(dualClass C) ≤ 2^(VCDim C + 1) − 1`.
* `vcDim_dualClass_lt_top`: the dual of a finite-VC class has finite VC dimension.
-/

open Finset

universe u

variable {X : Type u} {C : ConceptClass X Bool}

/-- **Assouad's coding lemma.** If the dual class shatters a set `S` of concepts with
`2^(d+1) ≤ S.card`, then `C` shatters some set of `d + 1` points. Bitstrings index a `2^(d+1)`-subset
of the shattered concepts; coordinate `j` is read off by a point `x_j` supplied by dual shattering. -/
theorem dualClass_shatters_imp_shatters {d : ℕ}
    (S : Finset ↥C) (hS : Shatters ↥C (dualClass C) S) (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset X, T.card = d + 1 ∧ Shatters X C T := by
  classical
  -- index 2^(d+1) of the shattered concepts by bitstrings
  let eFun : (Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_bool, Fintype.card_fin])
  let eFin : Fin (2 ^ (d + 1)) ↪ Fin S.card := Fin.castLEEmb hcard
  let eFinS : Fin S.card ≃ ↥S := S.equivFin.symm
  let embed : (Fin (d + 1) → Bool) → ↥S := eFinS ∘ eFin ∘ eFun
  have hembed_inj : Function.Injective embed := by
    intro a b hab
    simp only [embed, Function.comp] at hab
    exact eFun.injective (eFin.injective (eFinS.injective hab))
  -- coordinate-`j` labelling: read the `j`-th bit of the indexing bitstring
  let label (j : Fin (d + 1)) : ↥S → Bool := fun s =>
    if h : ∃ b, embed b = s then (h.choose) j else false
  -- dual shattering supplies, for each coordinate, a point realizing that labelling
  have hpoints : ∀ j : Fin (d + 1), ∃ x : X, ∀ s : ↥S, (s : ↥C).val x = label j s := by
    intro j
    obtain ⟨f, hf_mem, hf_eq⟩ := hS (label j)
    obtain ⟨x, hx⟩ := hf_mem
    exact ⟨x, fun s => by rw [← hx s, ← hf_eq s]⟩
  choose x hx using hpoints
  let T : Finset X := Finset.univ.image x
  -- the points are distinct: the bitstring `i ↦ (i == j)` separates coordinates `j ≠ k`
  have hx_inj : Function.Injective x := by
    intro j k hjk
    by_contra hjk_ne
    have hlabel_eq : ∀ s : ↥S, label j s = label k s := by
      intro s
      have hj := hx j s
      have hk := hx k s
      rw [hjk] at hj
      rw [hj] at hk
      exact hk
    let b0 : Fin (d + 1) → Bool := fun i => i == j
    have hlabel_j_b0 : label j (embed b0) = true := by
      simp only [label]
      rw [dif_pos ⟨b0, rfl⟩]
      rw [hembed_inj (⟨b0, rfl⟩ : ∃ b, embed b = embed b0).choose_spec]
      simp [b0]
    have hlabel_k_b0 : label k (embed b0) = false := by
      simp only [label]
      rw [dif_pos ⟨b0, rfl⟩]
      rw [hembed_inj (⟨b0, rfl⟩ : ∃ b, embed b = embed b0).choose_spec]
      simp only [b0]
      cases hkj : (k == j)
      · rfl
      · exact absurd (beq_iff_eq.mp hkj).symm hjk_ne
    have hcontra := hlabel_eq (embed b0)
    rw [hlabel_j_b0, hlabel_k_b0] at hcontra
    exact Bool.noConfusion hcontra
  have hT_card : T.card = d + 1 := by
    simp only [T, card_image_of_injective _ hx_inj, card_univ, Fintype.card_fin]
  -- `C` shatters `T`: a labelling of `T` is realized by the concept indexed by the bitstring
  have hT_shatters : Shatters X C T := by
    intro f
    have hx_mem : ∀ j : Fin (d + 1), x j ∈ T := fun j => by
      simp only [T]; exact mem_image_of_mem _ (mem_univ _)
    let g : Fin (d + 1) → Bool := fun j => f ⟨x j, hx_mem j⟩
    let cg : ↥C := (embed g).val
    refine ⟨cg.val, cg.property, fun ⟨y, hy⟩ => ?_⟩
    simp only [T] at hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, _, rfl⟩ := hy
    show cg.val (x j) = f ⟨x j, hx_mem j⟩
    have step1 : (embed g).val.val (x j) = label j (embed g) := hx j (embed g)
    have step2 : label j (embed g) = g j := by
      simp only [label]
      rw [dif_pos ⟨g, rfl⟩]
      rw [hembed_inj (⟨g, rfl⟩ : ∃ b, embed b = embed g).choose_spec]
    have step3 : g j = f ⟨x j, hx_mem j⟩ := rfl
    rw [step1, step2, step3]
  exact ⟨T, hT_card, hT_shatters⟩

/-- **Assouad's dual VC bound.** If `VCDim X C ≤ d`, then `VCDim(dualClass C) ≤ 2^(d+1) − 1`. -/
theorem vcDim_dualClass_le {d : ℕ} (hd : VCDim X C ≤ (d : WithTop ℕ)) :
    VCDim ↥C (dualClass C) ≤ ((2 ^ (d + 1) - 1 : ℕ) : WithTop ℕ) := by
  apply iSup₂_le
  intro S hS
  by_contra hlt
  push_neg at hlt
  have hge : 2 ^ (d + 1) ≤ S.card := by
    by_contra hlt'
    push_neg at hlt'
    have hle : S.card ≤ 2 ^ (d + 1) - 1 := by omega
    exact absurd (WithTop.coe_le_coe.mpr hle) (not_le.mpr hlt)
  obtain ⟨T, hTcard, hTshat⟩ := dualClass_shatters_imp_shatters S hS hge
  have hvc : ((d + 1 : ℕ) : WithTop ℕ) ≤ VCDim X C :=
    le_iSup₂_of_le T hTshat (by exact_mod_cast hTcard.ge)
  have : d + 1 ≤ d := by exact_mod_cast le_trans hvc hd
  omega

/-- **VC finiteness is self-dual.** The dual of a finite-VC class has finite VC dimension. -/
theorem vcDim_dualClass_lt_top (h : VCDim X C < ⊤) : VCDim ↥C (dualClass C) < ⊤ := by
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt h)
  exact lt_of_le_of_lt (vcDim_dualClass_le hd.ge) (WithTop.coe_lt_top _)
