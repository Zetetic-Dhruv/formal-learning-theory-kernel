/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Nat.Choose.Sum

/-!
# Sauer–Shelah on a finite domain

The quantitative Sauer–Shelah lemma for a family of Boolean functions on a finite type. If no subset
of size exceeding `d` is shattered (every labelling realized), the family has at most
`∑_{k ≤ d} C(|α|, k)` members.

The proof is the true-set bridge to Mathlib's set-family Sauer–Shelah: a Boolean function `f : α → Bool`
is encoded by its support `{x | f x}`, an injection into `Finset α`, carrying the family `C` to a set
family `𝒜`. Membership-shattering of `𝒜` (Mathlib's `Finset.Shatters`) is exactly realizability of
every labelling by `C`, so the VC dimension of `𝒜` is at most `d`, and Pajor's bound
(`Finset.card_le_card_shatterer`) with `Finset.card_shatterer_le_sum_vcDim` finishes.

Reference: N. Sauer, *On the density of families of sets*, J. Combinatorial Theory Ser. A 13 (1972).

## Main results

* `finset_card_le_sum_choose`: the Sauer–Shelah cardinality bound for a finite Boolean function family.
-/

open Finset

/-- **Sauer–Shelah on a finite domain.** A family `C` of Boolean functions on a finite type `α` none
of whose shattered subsets exceed size `d` has at most `∑_{k ≤ d} C(|α|, k)` members. -/
theorem finset_card_le_sum_choose {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset (α → Bool)) (d : ℕ)
    (hd : ∀ s : Finset α, (∀ f : s → Bool, ∃ g ∈ C, ∀ x : s, g (x : α) = f x) → s.card ≤ d) :
    C.card ≤ ∑ k ∈ Finset.range (d + 1), (Fintype.card α).choose k := by
  classical
  set e : (α → Bool) → Finset α := fun f => Finset.univ.filter (fun x => f x = true) with he_def
  have hinj : Function.Injective e := by
    intro f g hfg
    funext x
    have hx : (f x = true) ↔ (g x = true) := by
      have h := Finset.ext_iff.mp hfg x
      simpa [he_def, Finset.mem_filter] using h
    cases hfx : f x <;> cases hgx : g x <;> simp_all
  set 𝒜 : Finset (Finset α) := C.image e with h𝒜
  -- Mathlib-shattering of `𝒜` ⇒ `C` realizes every labelling of `s`
  have hbridge : ∀ s : Finset α, 𝒜.Shatters s →
      (∀ f : s → Bool, ∃ g ∈ C, ∀ x : s, g (x : α) = f x) := by
    intro s hsh f
    set u : Finset α := (s.attach.filter (fun x => f x = true)).image Subtype.val with hu
    have hus : u ⊆ s := by
      intro y hy
      simp only [hu, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and] at hy
      obtain ⟨x, -, rfl⟩ := hy
      exact x.2
    have hmemu : ∀ y : α, y ∈ u ↔ ∃ hy : y ∈ s, f ⟨y, hy⟩ = true := by
      intro y
      simp only [hu, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
        Subtype.exists]
      constructor
      · rintro ⟨a, ha, hfa, rfl⟩; exact ⟨ha, hfa⟩
      · rintro ⟨hy, hfy⟩; exact ⟨y, hy, hfy, rfl⟩
    obtain ⟨w, hw, hsw⟩ := hsh hus
    rw [h𝒜, Finset.mem_image] at hw
    obtain ⟨g, hgC, rfl⟩ := hw
    refine ⟨g, hgC, fun x => ?_⟩
    have hxs : (x : α) ∈ s := x.2
    have hx : ((x : α) ∈ s ∧ g (x : α) = true) ↔ (x : α) ∈ u := by
      rw [← hsw]
      simp only [Finset.mem_inter, he_def, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hmemu] at hx
    have hiff : g (x : α) = true ↔ f x = true := by
      constructor
      · intro hg
        obtain ⟨hy, hfy⟩ := hx.mp ⟨hxs, hg⟩
        rwa [Subtype.coe_eta] at hfy
      · intro hf
        exact (hx.mpr ⟨hxs, by rw [Subtype.coe_eta]; exact hf⟩).2
    cases hgx : g (x : α) <;> cases hfx : f x <;> simp_all
  have hvc : 𝒜.vcDim ≤ d := by
    unfold Finset.vcDim
    refine Finset.sup_le (fun s hs => ?_)
    rw [Finset.mem_shatterer] at hs
    exact hd s (hbridge s hs)
  calc C.card = 𝒜.card := (Finset.card_image_of_injective C hinj).symm
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card α).choose k := Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card α).choose k :=
        Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hvc)
    _ = ∑ k ∈ Finset.range (d + 1), (Fintype.card α).choose k :=
        Finset.sum_congr (by ext k; simp [Finset.mem_Iic, Finset.mem_range]) (fun _ _ => rfl)
