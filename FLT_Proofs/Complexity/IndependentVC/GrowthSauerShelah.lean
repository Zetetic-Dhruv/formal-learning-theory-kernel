/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.VCDimension
import FLT_Proofs.Complexity.IndependentVC.FiniteSauerShelah

/-!
# Sauer–Shelah for the growth function

The growth function of a class of VC dimension at most `d` is bounded by the Sauer–Shelah
polynomial: `GrowthFunction X C m ≤ ∑_{k ≤ d} C(m, k)`. This is the general-domain form, obtained
from the finite-domain bound `finset_card_le_sum_choose` by restricting to each size-`m` sample.

The bridge is the projection lemma `shatters_val_image_of_realizes`: a labelling of a subset of the
sample realized by the trace of `C` extends to a shattering of the corresponding subset of `X`, so
the trace's shattered subsets are no larger than `d`. Applying the finite bound to each sample's
trace and taking the supremum gives the result.

Reference: N. Sauer, *On the density of families of sets*, J. Combinatorial Theory Ser. A 13 (1972);
S. Shelah, *A combinatorial problem; stability and order for models and theories in infinitary
languages*, Pacific J. Math. 41 (1972).

## Main results

* `shatters_val_image_of_realizes`: trace realizability lifts to shattering of the sample's image.
* `growthFunction_le_sum_choose`: the Sauer–Shelah polynomial bound on the growth function.
-/

open Finset

universe u

variable {X : Type u}

/-- **Projection lemma.** If, for a finite sample `SS` and a subset `s` of it, every labelling of `s`
is realized by some concept in `C`, then `C` shatters the image of `s` in `X` (the image taken with
the subtype embedding, so no decidable equality on `X` is needed). This transfers the shattering of
the trace on the sample back to the original domain. -/
theorem shatters_val_image_of_realizes (C : ConceptClass X Bool) (SS : Finset X)
    (s : Finset ↥SS)
    (hreal : ∀ f : s → Bool, ∃ c ∈ C, ∀ x : s, c ((x : ↥SS) : X) = f x) :
    _root_.Shatters X C (s.map (Function.Embedding.subtype (· ∈ SS))) := by
  classical
  intro φ
  have hmem : ∀ x : ↥SS, x ∈ s → (x : X) ∈ s.map (Function.Embedding.subtype (· ∈ SS)) :=
    fun x hx => Finset.mem_map_of_mem _ hx
  obtain ⟨c, hcC, hc⟩ := hreal (fun x => φ ⟨((x : ↥SS) : X), hmem (x : ↥SS) x.2⟩)
  refine ⟨c, hcC, fun y => ?_⟩
  obtain ⟨x, hxs, hxy⟩ := Finset.mem_map.mp y.2
  have hcx : c (y : X) = φ ⟨(x : X), hmem x hxs⟩ := by
    rw [← hxy]; exact hc ⟨x, hxs⟩
  rw [hcx]
  exact congrArg φ (Subtype.ext hxy)

/-- **Sauer–Shelah for the growth function.** If every set shattered by `C` has size at most `d`,
then the growth function obeys `GrowthFunction X C m ≤ ∑_{k ≤ d} C(m, k)`. -/
theorem growthFunction_le_sum_choose (C : ConceptClass X Bool) (d : ℕ)
    (hd : ∀ s : Finset X, _root_.Shatters X C s → s.card ≤ d) (m : ℕ) :
    GrowthFunction X C m ≤ ∑ k ∈ Finset.range (d + 1), m.choose k := by
  classical
  have hbd : ∀ (S : {S : Finset X // S.card = m}),
      ({ f : ↥S.val → Bool | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } : Set (↥S.val → Bool)).ncard
        ≤ ∑ k ∈ Finset.range (d + 1), m.choose k := by
    intro S
    haveI : Fintype ↥S.val := FinsetCoe.fintype S.val
    set Tr : Set (↥S.val → Bool) := { f | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } with hTr
    haveI : Fintype ↥Tr := (Set.toFinite Tr).fintype
    have hbound : ∀ s : Finset ↥S.val,
        (∀ f : s → Bool, ∃ g ∈ Tr.toFinset, ∀ x : s, g (x : ↥S.val) = f x) → s.card ≤ d := by
      intro s hs
      have hcard_eq : (s.map (Function.Embedding.subtype (· ∈ S.val))).card = s.card :=
        Finset.card_map _
      rw [← hcard_eq]
      refine hd _ (shatters_val_image_of_realizes C S.val s (fun f => ?_))
      obtain ⟨g, hg, hgf⟩ := hs f
      rw [Set.mem_toFinset, hTr] at hg
      obtain ⟨c, hcC, hcg⟩ := hg
      exact ⟨c, hcC, fun x => by rw [hcg (x : ↥S.val)]; exact hgf x⟩
    have key := finset_card_le_sum_choose Tr.toFinset d hbound
    have hcardSS : Fintype.card ↥S.val = m := by rw [Fintype.card_coe]; exact S.property
    rw [hcardSS] at key
    rwa [Set.ncard_eq_toFinset_card']
  unfold GrowthFunction
  rcases isEmpty_or_nonempty {S : Finset X // S.card = m} with hemp | hnem
  · haveI := hemp
    rw [Set.range_eq_empty, csSup_empty]
    exact bot_le
  · haveI := hnem
    refine csSup_le (Set.range_nonempty _) ?_
    rintro b ⟨S, rfl⟩
    exact hbd S
