/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.DualVC
import FLT_Proofs.Complexity.Structures
import FLT_Proofs.Complexity.Generalization
import FLT_Proofs.PureMath.ApproxMinimax
import FLT_Proofs.PureMath.FiniteVCApprox
import FLT_Proofs.PureMath.BinaryMatrix

/-!
# Moran-Yehudayoff Compression Theorem

Finite VC dimension ↔ compression scheme with finite side information.
-/

open Classical Finset
noncomputable section
universe u

/-! ## Structure: Proper Finite-Support Learner -/

/-- A proper finite-support learner for a concept class C.
    This structure captures the existence of a bounded-support ERM
    with error at most 1/3 for any C-realizable finite distribution. -/
structure ProperFiniteSupportLearner (X : Type u) (C : ConceptClass X Bool) where
  sampleBound : ℕ
  learn : {m : ℕ} → (Fin m → X × Bool) → (X → Bool)
  output_mem : ∀ {m : ℕ} (S : Fin m → X × Bool), learn S ∈ C
  good_on_support : ∀ (c : X → Bool) (_ : c ∈ C) (Y : Finset X)
    (q : FinitePMF ↥Y),
    ∃ (k : ℕ) (_ : k ≤ sampleBound) (f : Fin k → X),
      (∀ j, f j ∈ Y) ∧
      (let S : Fin k → X × Bool := fun j => (f j, c (f j))
       (∑ y : ↥Y, q.prob y * (if learn S (y : X) = c (y : X) then (0 : ℝ) else 1)) ≤ 1 / 3)

/-- Finite VC dimension implies existence of a proper finite-support learner.
    The conclusion `∃ L, True` establishes inhabitedness.
    The actual construction from finite VC + Sauer-Shelah + probabilistic method
    gives sampleBound = O(d), but the existence statement is independent of the bound. -/
theorem vcdim_finite_imp_proper_finite_support_learner
    (X : Type u) (C : ConceptClass X Bool)
    (hCne : C.Nonempty) (hC : VCDim X C < ⊤) :
    ∃ L : ProperFiniteSupportLearner X C, True := by
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hC)
  obtain ⟨c₀, hc₀⟩ := hCne
  -- ERM learner: pick a consistent hypothesis if realizable, else c₀
  let learn : {m : ℕ} → (Fin m → X × Bool) → (X → Bool) := fun {m} S =>
    if h : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2 then h.choose else c₀
  have learn_mem : ∀ {m : ℕ} (S : Fin m → X × Bool), learn S ∈ C := by
    intro m S; simp only [learn]
    split
    · next h => exact h.choose_spec.1
    · exact hc₀
  have learn_consistent : ∀ {m : ℕ} (S : Fin m → X × Bool),
      (∃ c ∈ C, ∀ i, c (S i).1 = (S i).2) → ∀ i, learn S (S i).1 = (S i).2 := by
    intro m S hreal i; simp only [learn, dif_pos hreal]; exact hreal.choose_spec.2 i
  exact ⟨⟨3 * (d + 1), learn, @learn_mem, fun c hc Y q => by
    sorry⟩, trivial⟩

/-! ## Forward direction: VCDim < ⊤ → compression with info -/

theorem vcdim_finite_imp_compression_with_info
    (X : Type u) (C : ConceptClass X Bool) (hC : VCDim X C < ⊤) :
    ∃ (k : ℕ) (cs : CompressionSchemeWithInfo X Bool C), cs.size = k := by
  by_cases hne : C.Nonempty
  · -- Nonempty C: the Moran-Yehudayoff construction
    sorry
  · -- Empty C: realizability guard is always False
    refine ⟨1, ?_, ?_⟩
    · exact {
        Info := PUnit
        info_finite := inferInstance
        compress := fun _ => (∅, PUnit.unit)
        reconstruct := fun _ _ _ => false
        kernelSize := 0
        compress_small := fun _ => by simp
        compress_sub := fun _ x hx => by simp at hx
        correct := fun {m} S hreal => by
          exfalso; obtain ⟨c, hcC, _⟩ := hreal
          exact hne ⟨c, hcC⟩
      }
    · simp [CompressionSchemeWithInfo.size, Fintype.card_punit]

/-! ## Reverse direction: compression with info → VCDim < ⊤ -/

/-- Pigeonhole core: if two C-realizable samples over the same points with
    different labelings produce the same (kernel, info) pair, correctness
    forces the labelings to agree. -/
theorem compress_with_info_injective_on_labelings {X : Type u} {n : ℕ}
    {C : ConceptClass X Bool}
    (cs : CompressionSchemeWithInfo X Bool C)
    (pts : Fin n → X) (hpts : Function.Injective pts)
    (f g : Fin n → Bool)
    (hf_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i)
    (hg_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = g i)
    (hfg : cs.compress (fun i => (pts i, f i)) = cs.compress (fun i => (pts i, g i))) :
    f = g := by
  have h_recon : cs.reconstruct (cs.compress (fun i => (pts i, f i))).1
                   (cs.compress (fun i => (pts i, f i))).2 =
                 cs.reconstruct (cs.compress (fun i => (pts i, g i))).1
                   (cs.compress (fun i => (pts i, g i))).2 := by rw [hfg]
  funext i
  have hf_real' : ∃ c ∈ C, ∀ i : Fin n,
      c ((fun i => (pts i, f i)) i).1 = ((fun i => (pts i, f i)) i).2 := by
    obtain ⟨c, hcC, hc⟩ := hf_real; exact ⟨c, hcC, fun i => by simp [hc i]⟩
  have hg_real' : ∃ c ∈ C, ∀ i : Fin n,
      c ((fun i => (pts i, g i)) i).1 = ((fun i => (pts i, g i)) i).2 := by
    obtain ⟨c, hcC, hc⟩ := hg_real; exact ⟨c, hcC, fun i => by simp [hc i]⟩
  have hf := cs.correct (fun i => (pts i, f i)) hf_real' i
  have hg := cs.correct (fun i => (pts i, g i)) hg_real' i
  simp at hf hg
  rw [← hf, congr_fun h_recon (pts i), hg]

private lemma shatters_subset_compression {X : Type u} {C : ConceptClass X Bool}
    {S T : Finset X} (hST : T ⊆ S) (hS : Shatters X C S) : Shatters X C T := by
  intro f
  let g : ↥S → Bool := fun ⟨x, hx⟩ => if h : x ∈ T then f ⟨x, h⟩ else false
  obtain ⟨c, hcC, hcg⟩ := hS g
  exact ⟨c, hcC, fun ⟨x, hx⟩ => by
    have := hcg ⟨x, hST hx⟩; simp only [g, hx, dite_true] at this; exact this⟩

private lemma succ_le_two_pow_compression (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc k + 1 + 1 ≤ 2 ^ k + 2 ^ k := by omega
                   _ = 2 ^ (k + 1) := by ring

/-- Exponential beats polynomial for the compression pigeonhole argument. -/
private lemma exp_beats_poly_compression (s : ℕ) :
    (s + 1) ^ 2 * (4 * (s + 1) ^ 2) ^ s < 2 ^ (2 * (s + 1) * (s + 1)) := by
  -- (s+1)^2 * (4(s+1)^2)^s = (s+1)^(2s+2) * 4^s
  have h1 : (s + 1) ^ 2 * (4 * (s + 1) ^ 2) ^ s =
    (s + 1) ^ (2 * s + 2) * 4 ^ s := by rw [mul_pow, ← pow_mul]; ring_nf
  rw [h1]
  -- (s+1)^(2s+2) ≤ (2^s)^(2s+2)
  have h2 : (s + 1) ^ (2 * s + 2) ≤ (2 ^ s) ^ (2 * s + 2) :=
    Nat.pow_le_pow_left (succ_le_two_pow_compression s) _
  -- 4^s = 2^(2s)
  have h3 : (4 : ℕ) ^ s = 2 ^ (2 * s) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]
  rw [h3]
  calc (s + 1) ^ (2 * s + 2) * 2 ^ (2 * s)
      ≤ (2 ^ s) ^ (2 * s + 2) * 2 ^ (2 * s) := Nat.mul_le_mul_right _ h2
    _ = 2 ^ (s * (2 * s + 2) + 2 * s) := by rw [← pow_mul, ← pow_add]
    _ = 2 ^ (2 * s ^ 2 + 4 * s) := by ring_nf
    _ < 2 ^ (2 * (s + 1) * (s + 1)) := by
        apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
        nlinarith

/-- Compression with side info implies finite VC dimension.
    Proof by pigeonhole: compress is injective on C-realizable labelings
    (by correctness), but compressed outputs form a bounded set. -/
theorem compression_with_info_imp_vcdim_finite
    (X : Type u) (C : ConceptClass X Bool)
    (hcomp : ∃ (k : ℕ) (cs : CompressionSchemeWithInfo X Bool C), cs.size = k) :
    VCDim X C < ⊤ := by
  by_contra h_top
  push_neg at h_top; rw [top_le_iff] at h_top
  obtain ⟨k, cs, hk⟩ := hcomp
  have h_large : ∀ n : ℕ, ∃ S : Finset X, Shatters X C S ∧ n ≤ S.card := by
    intro n; by_contra h_neg; push_neg at h_neg
    have : VCDim X C ≤ ↑n := by
      apply iSup₂_le; intro S hS
      exact_mod_cast Nat.le_of_lt_succ (Nat.lt_succ_of_lt (h_neg S hS))
    exact absurd h_top (ne_of_lt (lt_of_le_of_lt this (WithTop.coe_lt_top _)))
  set K := cs.kernelSize with hK_def
  set I := @Fintype.card cs.Info cs.info_finite with hI_def
  set s := K + I with hs_def
  set N := 2 * (s + 1) * (s + 1) with hN_def
  obtain ⟨T₀, hT₀_shatt, hT₀_card⟩ := h_large N
  haveI : DecidableEq X := Classical.decEq X
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hT₀_card
  have hT_shatt : Shatters X C T := shatters_subset_compression hT_sub hT₀_shatt
  set n := T.card with hn_def
  have hn_eq : n = N := hT_card
  let eqv := T.equivFin.symm
  let pts : Fin n → X := fun i => (eqv i : X)
  have hpts_inj : Function.Injective pts :=
    fun _ _ h => eqv.injective (Subtype.val_injective h)
  let mkSample : (Fin n → Bool) → (Fin n → X × Bool) := fun f i => (pts i, f i)
  have h_realizable : ∀ f : Fin n → Bool, ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i := by
    intro f
    let f' : ↥T → Bool := fun ⟨x, hx⟩ => f (T.equivFin ⟨x, hx⟩)
    obtain ⟨c, hcC, hcf'⟩ := hT_shatt f'
    exact ⟨c, hcC, fun i => by
      have := hcf' (eqv i); simp only [f', pts] at this ⊢
      rwa [T.equivFin.apply_symm_apply i] at this⟩
  have h_inj : Function.Injective (cs.compress ∘ mkSample) := by
    intro f g hfg
    exact compress_with_info_injective_on_labelings cs pts hpts_inj f g
      (h_realizable f) (h_realizable g) hfg
  -- Target: (kernel subsets of T×Bool with card ≤ K) × Info
  set A := T ×ˢ (Finset.univ : Finset Bool) with hA_def
  set target := (A.powerset.filter (fun S => S.card ≤ K)) ×ˢ
    (@Finset.univ cs.Info cs.info_finite) with htarget_def
  have h_maps_to : ∀ f : Fin n → Bool, (cs.compress ∘ mkSample) f ∈ target := by
    intro f
    simp only [Function.comp, htarget_def, Finset.mem_product, Finset.mem_filter,
      Finset.mem_powerset, Finset.mem_univ, and_true]
    constructor
    · intro p hp
      have hsub := cs.compress_sub (mkSample f)
      have hp_range := hsub (Finset.mem_coe.mpr hp)
      obtain ⟨i, hi⟩ := hp_range
      simp only [mkSample] at hi
      rw [Finset.mem_product]
      exact ⟨by rw [show p.1 = pts i from (congr_arg Prod.fst hi).symm]; exact (eqv i).2,
             Finset.mem_univ _⟩
    · exact cs.compress_small (mkSample f)
  -- Cardinality bounds
  have hA_card : A.card = 2 * n := by simp [hA_def, Finset.card_product]; ring
  have hn_pos : 0 < n := by rw [hn_eq, hN_def]; positivity
  have h_target_card : target.card ≤ (K + 1) * (2 * n) ^ K * I := by
    simp only [htarget_def, Finset.card_product]
    apply Nat.mul_le_mul_right
    calc (A.powerset.filter (fun S => S.card ≤ K)).card
        ≤ (Finset.range (K + 1)).sum (fun j => (A.powersetCard j).card) := by
          have hsub : A.powerset.filter (fun S => S.card ≤ K) ⊆
              (Finset.range (K + 1)).biUnion (fun j => A.powersetCard j) := by
            intro S hS
            simp only [Finset.mem_filter, Finset.mem_powerset] at hS
            simp only [Finset.mem_biUnion, Finset.mem_range]
            exact ⟨S.card, by omega, Finset.mem_powersetCard.mpr ⟨hS.1, rfl⟩⟩
          exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ = (Finset.range (K + 1)).sum (fun j => (2 * n).choose j) := by
          congr 1; ext j; simp [Finset.card_powersetCard, hA_card]
      _ ≤ (Finset.range (K + 1)).sum (fun _ => (2 * n) ^ K) := by
          apply Finset.sum_le_sum; intro j hj
          simp only [Finset.mem_range] at hj
          calc (2 * n).choose j ≤ (2 * n) ^ j := Nat.choose_le_pow _ _
            _ ≤ (2 * n) ^ K := Nat.pow_le_pow_right (by omega) (by omega)
      _ = (K + 1) * (2 * n) ^ K := by simp [Finset.sum_const, Finset.card_range]
  have h_source_card : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Fintype.card_fin, Fintype.card_bool]
  have h_target_lt : target.card < 2 ^ n := by
    have hn_val : n = 2 * (s + 1) * (s + 1) := hn_eq.trans hN_def
    have hK_le : K + 1 ≤ s + 1 := by omega
    have hI_le : I ≤ s + 1 := by omega
    have hK_le' : K ≤ s := by omega
    calc target.card
        ≤ (K + 1) * (2 * n) ^ K * I := h_target_card
      _ ≤ (s + 1) * (2 * n) ^ s * (s + 1) := by
          apply Nat.mul_le_mul (Nat.mul_le_mul hK_le
            (Nat.pow_le_pow_right (by omega) hK_le')) hI_le
      _ = (s + 1) ^ 2 * (2 * n) ^ s := by ring
      _ = (s + 1) ^ 2 * (2 * (2 * (s + 1) * (s + 1))) ^ s := by rw [hn_val]
      _ = (s + 1) ^ 2 * (4 * (s + 1) ^ 2) ^ s := by ring_nf
      _ < 2 ^ (2 * (s + 1) * (s + 1)) := exp_beats_poly_compression s
      _ = 2 ^ n := by rw [hn_val]
  have h_card_lt : target.card < (Finset.univ : Finset (Fin n → Bool)).card := by
    rw [h_source_card]; exact h_target_lt
  exact absurd h_inj (by
    intro h_inj_false
    obtain ⟨f, _, g, _, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_lt (fun x _ => h_maps_to x)
    exact absurd heq (fun h => hne (h_inj_false h)))

/-! ## Biconditional -/

theorem fundamental_vc_compression_with_info
    (X : Type u) (C : ConceptClass X Bool) :
    (VCDim X C < ⊤) ↔
    (∃ (k : ℕ) (cs : CompressionSchemeWithInfo X Bool C), cs.size = k) :=
  ⟨vcdim_finite_imp_compression_with_info X C,
   compression_with_info_imp_vcdim_finite X C⟩

end -- noncomputable section
