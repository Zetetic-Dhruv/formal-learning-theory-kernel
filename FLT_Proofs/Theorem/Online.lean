/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Criterion.Online
-- Replaced FLT_Proofs.Complexity.Littlestone with corrected definitions below:
-- depth-indexed complete trees + path-wise shattering.
import FLT_Proofs.Complexity.Generalization
-- Required for CompleteLattice instance and ConditionallyCompleteLinearOrderBot ℕ
import Mathlib.Data.Nat.Lattice

/-!
# Online Learning Theorems — Corrected Definitions

**Corrections from original LimitsOfLearning.Complexity.Littlestone:**
1. isShattered now restricts concept class at each branch (path-wise, not branch-wise)
2. MistakeTree is depth-indexed: `LTree X n` is a complete binary tree of depth n
   (the standard Littlestone tree definition). This ensures the adversary argument works.

**Leaf shattering and dimension type corrections:**
3. isShattered .leaf requires C.Nonempty (not True), so Ldim(∅) = ⊥ ≠ 0
4. LittlestoneDim returns WithBot (WithTop ℕ) = {⊥} ∪ ℕ ∪ {⊤}
   - ⊥ = empty class (Ldim = -1 in standard convention)
   - ↑(↑n) = finite dimension n
   - ↑⊤ = infinite dimension
   This resolves the SOA tie-breaking issue at d=0 without touching the SOA definition.

**Universe constraint:** `OnlineLearner.State : Type` forces `Type 0`.
The SOA needs `State = Set (X → Bool)`, requiring `X : Type`.
-/

-- ============================================================
-- CORRECTED DEFINITIONS: Depth-indexed complete Littlestone trees
-- ============================================================

/-- A complete binary Littlestone tree of depth n. -/
inductive LTree (X : Type) : ℕ → Type where
  | leaf : LTree X 0
  | branch : {n : ℕ} → X → LTree X n → LTree X n → LTree X (n + 1)

/-- Path-wise shattering for complete trees.
    Leaf case requires C.Nonempty so that Ldim(∅) = ⊥. -/
def LTree.isShattered {X : Type} {n : ℕ} (C : ConceptClass X Bool) : LTree X n → Prop
  | .leaf => C.Nonempty  -- was True, now C.Nonempty so Ldim(∅) = ⊥
  | .branch x l r =>
      (∃ c ∈ C, c x = true) ∧ (∃ c ∈ C, c x = false) ∧
      l.isShattered {c ∈ C | c x = true} ∧
      r.isShattered {c ∈ C | c x = false}

/-- Helper: shattering implies the concept class is nonempty. -/
theorem LTree.nonempty_of_isShattered {X : Type} {C : ConceptClass X Bool}
    {n : ℕ} (T : LTree X n) (hT : T.isShattered C) : C.Nonempty := by
  induction n with
  | zero => match T with | .leaf => exact hT
  | succ k _ =>
    match T with
    | .branch _ _ _ =>
      obtain ⟨⟨c, hc, _⟩, _⟩ := hT
      exact ⟨c, hc⟩

/-- Shattering is upward-monotone in the concept class. -/
theorem LTree.isShattered_mono {X : Type} {n : ℕ} (T : LTree X n)
    {C C' : ConceptClass X Bool} (h : C ⊆ C') :
    T.isShattered C → T.isShattered C' := by
  induction T generalizing C C' with
  | leaf => exact Set.Nonempty.mono h
  | branch x l r ihl ihr =>
    intro ⟨⟨ct, hct, hctx⟩, ⟨cf, hcf, hcfx⟩, hsl, hsr⟩
    refine ⟨⟨ct, h hct, hctx⟩, ⟨cf, h hcf, hcfx⟩, ?_, ?_⟩
    · exact ihl (fun _ hm => ⟨h hm.1, hm.2⟩) hsl
    · exact ihr (fun _ hm => ⟨h hm.1, hm.2⟩) hsr

/-- Littlestone dimension: the maximum depth of a complete shattered tree.
    Returns WithBot (WithTop ℕ) so Ldim(∅) = ⊥. -/
noncomputable def LittlestoneDim (X : Type) (C : ConceptClass X Bool) :
    WithBot (WithTop ℕ) :=
  ⨆ (n : ℕ) (_ : ∃ T : LTree X n, T.isShattered C),
    (↑(↑n : WithTop ℕ) : WithBot (WithTop ℕ))

-- ============================================================
-- COUNTING MISTAKES FROM ARBITRARY STATE
-- ============================================================

/-- Count mistakes starting from state s. -/
noncomputable def OnlineLearner.mistakesFrom {X : Type}
    (L : OnlineLearner X Bool) (s : L.State) (c : X → Bool) : List X → ℕ
  | [] => 0
  | x :: xs =>
    (if L.predict s x ≠ c x then 1 else 0) +
      L.mistakesFrom (L.update s x (c x)) c xs

-- ============================================================
-- FORWARD DIRECTION: OnlineLearnable → LittlestoneDim < ⊤
-- ============================================================

/-- Core adversary lemma. -/
private theorem adversary_core {X : Type}
    (L : OnlineLearner X Bool) (s : L.State)
    {C : ConceptClass X Bool} {n : ℕ}
    (T : LTree X n) (hT : T.isShattered C) (hne : C.Nonempty) :
    ∃ (seq : List X) (c : X → Bool), c ∈ C ∧
      L.mistakesFrom s c seq = n := by
  induction n generalizing C s with
  | zero =>
    obtain ⟨c₀, hc₀⟩ := hne
    exact ⟨[], c₀, hc₀, rfl⟩
  | succ k ih =>
    match T, hT with
    | .branch x l r, ⟨⟨ct, hct, hctx⟩, ⟨cf, hcf, hcfx⟩, hsl, hsr⟩ =>
      by_cases hpred : L.predict s x = true
      · have hne_f : ({c ∈ C | c x = false}).Nonempty := ⟨cf, hcf, hcfx⟩
        obtain ⟨seq', c', hc'mem, hcount⟩ :=
          ih (L.update s x false) r hsr hne_f
        refine ⟨x :: seq', c', hc'mem.1, ?_⟩
        simp only [OnlineLearner.mistakesFrom, hc'mem.2, hpred]
        simp [hcount]; omega
      · have hpf : L.predict s x = false := by
          cases h : L.predict s x <;> simp_all
        have hne_t : ({c ∈ C | c x = true}).Nonempty := ⟨ct, hct, hctx⟩
        obtain ⟨seq', c', hc'mem, hcount⟩ :=
          ih (L.update s x true) l hsl hne_t
        refine ⟨x :: seq', c', hc'mem.1, ?_⟩
        simp only [OnlineLearner.mistakesFrom, hc'mem.2, hpf]
        simp [hcount]; omega

/-- Relate mistakesFrom to the original mistakes function. -/
private theorem mistakesFrom_init_eq {X : Type}
    (L : OnlineLearner X Bool) (c : X → Bool) (seq : List X) :
    L.mistakesFrom L.init c seq = L.mistakes c seq := by
  suffices h : ∀ (s : L.State) (acc : ℕ),
      OnlineLearner.mistakes.go L c s seq acc = L.mistakesFrom s c seq + acc by
    simp [OnlineLearner.mistakes, h L.init 0]
  induction seq with
  | nil => intro s acc; simp [OnlineLearner.mistakes.go, OnlineLearner.mistakesFrom]
  | cons x xs ih =>
    intro s acc
    simp only [OnlineLearner.mistakes.go, OnlineLearner.mistakesFrom]
    rw [ih]
    by_cases h : L.predict s x = c x
    · simp_all
    · simp_all; omega

/-- Forward direction: OnlineLearnable → LittlestoneDim < ⊤ -/
theorem forward_direction (X : Type) (C : ConceptClass X Bool) :
    OnlineLearnable X Bool C → LittlestoneDim X C < ⊤ := by
  intro ⟨M, L, hL⟩
  by_contra hge
  push_neg at hge
  have htop : LittlestoneDim X C = ⊤ := le_antisymm le_top hge
  have hunbounded : ∃ n, n > M ∧ ∃ T : LTree X n, T.isShattered C := by
    by_contra hc
    push_neg at hc
    have hbound : LittlestoneDim X C ≤ ↑(↑M : WithTop ℕ) := by
      unfold LittlestoneDim
      apply iSup₂_le
      intro n ⟨T, hT⟩
      by_cases hmn : n ≤ M
      · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by exact_mod_cast hmn))
      · exact (hc n (by omega) T hT).elim
    rw [htop] at hbound; simp at hbound
  obtain ⟨n, hn, T, hTshat⟩ := hunbounded
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hne : C.Nonempty := T.nonempty_of_isShattered hTshat
  obtain ⟨seq, c, hcC, hcount⟩ := adversary_core L L.init T hTshat hne
  have hbound : L.mistakes c seq ≤ M := hL c hcC seq
  rw [← mistakesFrom_init_eq] at hbound; omega

-- ============================================================
-- BACKWARD DIRECTION: LittlestoneDim < ⊤ → OnlineLearnable
-- ============================================================

/-- Version space after observing a history. -/
def versionSpace {X : Type} (C : ConceptClass X Bool) (history : List (X × Bool)) :
    ConceptClass X Bool :=
  {c ∈ C | ∀ p ∈ history, c p.1 = p.2}

/-- The Standard Optimal Algorithm (SOA). -/
noncomputable def SOA (X : Type) (C : ConceptClass X Bool) : OnlineLearner X Bool where
  State := List (X × Bool)
  init := []
  predict := fun history x =>
    let V := versionSpace C history
    if LittlestoneDim X {c ∈ V | c x = true} ≥ LittlestoneDim X {c ∈ V | c x = false}
    then true else false
  update := fun history x y => history ++ [(x, y)]

-- ============================================================
-- SOA INTERFACE LEMMAS (abstraction barrier for proof stability)
-- ============================================================

/-- SOA prediction: picks the label whose version space side has higher Ldim.
    NOT @[simp]: proofs should explicitly opt-in to see SOA internals. -/
theorem SOA_predict_eq (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (x : X) :
    (SOA X C).predict history x =
      if LittlestoneDim X {c ∈ versionSpace C history | c x = true} ≥
         LittlestoneDim X {c ∈ versionSpace C history | c x = false}
      then true else false := rfl

/-- SOA state update: append observation to history.
    NOT @[simp]: explicit use preserves abstraction barrier. -/
theorem SOA_update_eq (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (x : X) (y : Bool) :
    (SOA X C).update history x y = history ++ [(x, y)] := rfl

/-- SOA init state is empty history. -/
theorem SOA_init_eq (X : Type) (C : ConceptClass X Bool) :
    (SOA X C).init = ([] : List (X × Bool)) := rfl

/-- SOA mistakesFrom cons: unfold one step using the interface. -/
theorem SOA_mistakesFrom_cons (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (c : X → Bool) (x : X) (xs : List X) :
    (SOA X C).mistakesFrom history c (x :: xs) =
      (if (SOA X C).predict history x ≠ c x then 1 else 0) +
        (SOA X C).mistakesFrom (history ++ [(x, c x)]) c xs := rfl

/-- In `WithBot (WithTop ℕ)`, `a < ↑↑(n+1) → a ≤ ↑↑n`. Reusable lattice fact. -/
private theorem WithBot_WithTop_lt_succ_le {a : WithBot (WithTop ℕ)} {n : ℕ}
    (h : a < ↑(↑(n + 1) : WithTop ℕ)) : a ≤ ↑(↑n : WithTop ℕ) := by
  cases a with
  | bot => exact bot_le
  | coe v =>
    cases v with
    | top => simp at h
    | coe m =>
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
        (Nat.le_of_lt_succ (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h))))

-- ============================================================
-- INFRASTRUCTURE LEMMAS (all compile)
-- ============================================================

/-- Restricting C can only decrease Ldim. -/
private theorem ldim_restriction_le {X : Type} {C : ConceptClass X Bool}
    {x : X} {y : Bool} :
    LittlestoneDim X {c ∈ C | c x = y} ≤ LittlestoneDim X C := by
  apply iSup₂_le; intro n ⟨T, hT⟩
  exact le_iSup₂_of_le n ⟨T, T.isShattered_mono (fun _ hm => hm.1) hT⟩ le_rfl

/-- Build a tree of depth k+1 from shattered subtrees on both sides.
    Parametrized over b : Bool so we don't need to case-split in the caller. -/
private theorem ldim_branch_lower_bound {X : Type} {V : ConceptClass X Bool}
    {x : X} {k : ℕ} {b : Bool}
    (hb : ∃ Tb : LTree X k, Tb.isShattered {c ∈ V | c x = b})
    (hnb : ∃ Tnb : LTree X k, Tnb.isShattered {c ∈ V | c x = !b})
    (hwb : ∃ c ∈ V, c x = b) (hwnb : ∃ c ∈ V, c x = !b) :
    LittlestoneDim X V ≥ ↑(↑(k + 1) : WithTop ℕ) := by
  obtain ⟨Tb, hTb⟩ := hb
  obtain ⟨Tnb, hTnb⟩ := hnb
  cases b
  · -- b = false: true-side = !b, false-side = b
    exact le_iSup₂_of_le (k + 1) ⟨.branch x Tnb Tb, hwnb, hwb, hTnb, hTb⟩ le_rfl
  · -- b = true: true-side = b, false-side = !b
    exact le_iSup₂_of_le (k + 1) ⟨.branch x Tb Tnb, hwb, hwnb, hTb, hTnb⟩ le_rfl

/-- Version space subset. -/
theorem versionSpace_subset {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} :
    versionSpace C history ⊆ C :=
  fun _ hm => hm.1

/-- Target stays in version space. -/
theorem target_in_versionSpace {X : Type} {C : ConceptClass X Bool}
    {c : X → Bool} (hcC : c ∈ C) {history : List (X × Bool)}
    (hcons : ∀ p ∈ history, c p.1 = p.2) :
    c ∈ versionSpace C history :=
  ⟨hcC, hcons⟩

/-- Extending history restricts the version space. -/
theorem versionSpace_append {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} {x : X} {y : Bool} :
    versionSpace C (history ++ [(x, y)]) ⊆ versionSpace C history := by
  intro c ⟨hcC, hcons⟩
  exact ⟨hcC, fun p hp => hcons p (List.mem_append.mpr (Or.inl hp))⟩

/-- Ldim of version space ≤ Ldim of C. -/
theorem ldim_versionSpace_le {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} :
    LittlestoneDim X (versionSpace C history) ≤ LittlestoneDim X C := by
  apply iSup₂_le; intro n ⟨T, hT⟩
  exact le_iSup₂_of_le n ⟨T, T.isShattered_mono versionSpace_subset hT⟩ le_rfl

/-- SOA predicts the label whose side has higher Ldim. -/
private theorem soa_predict_spec {X : Type} (C : ConceptClass X Bool)
    (history : List (X × Bool)) (x : X) :
    let V := versionSpace C history
    let b := (SOA X C).predict history x
    LittlestoneDim X {c ∈ V | c x = b} ≥
    LittlestoneDim X {c ∈ V | c x = !b} := by
  simp only [SOA]
  split
  · simp [Bool.not_true]; assumption
  · simp [Bool.not_false]; rename_i h; exact le_of_lt (not_le.mp h)

/-- Truncate a complete tree to a smaller depth. -/
def LTree.truncate {X : Type} {n m : ℕ} : (h : n ≤ m) → LTree X m → LTree X n := by
  intro h T; induction n generalizing m with
  | zero => exact .leaf
  | succ k ih =>
    match m, T, h with
    | _ + 1, .branch x l r, h =>
      exact .branch x (ih (Nat.le_of_succ_le_succ h) l) (ih (Nat.le_of_succ_le_succ h) r)

/-- A truncated tree is shattered if the original is. -/
theorem LTree.isShattered_truncate {X : Type} {C : ConceptClass X Bool}
    {m : ℕ} (T : LTree X m) (hT : T.isShattered C) {n : ℕ} (h : n ≤ m) :
    (T.truncate h).isShattered C := by
  induction n generalizing m C with
  | zero => exact T.nonempty_of_isShattered hT
  | succ k ih =>
    match m, T, h, hT with
    | _ + 1, .branch x l r, h, hT =>
      simp only [LTree.isShattered] at hT
      obtain ⟨hwt, hwf, hsl, hsr⟩ := hT
      simp only [LTree.truncate]
      exact ⟨hwt, hwf, ih l hsl (Nat.le_of_succ_le_succ h),
             ih r hsr (Nat.le_of_succ_le_succ h)⟩

/-- From Ldim ≥ d, extract a shattered tree of depth exactly d. -/
private theorem exists_shattered_of_ldim_ge {X : Type} {C : ConceptClass X Bool}
    {d : ℕ} (h : LittlestoneDim X C ≥ ↑(↑d : WithTop ℕ)) :
    ∃ T : LTree X d, T.isShattered C := by
  match d with
  | 0 =>
    -- Need C.Nonempty. From h: Ldim ≥ ↑↑0 > ⊥. If C empty, Ldim = ⊥. Contradiction.
    by_contra hall; push_neg at hall
    have hne : ¬ C.Nonempty := hall .leaf
    have hle : LittlestoneDim X C ≤ ⊥ := by
      apply iSup₂_le; intro n ⟨T, hT⟩
      exact absurd (T.nonempty_of_isShattered hT) hne
    have : LittlestoneDim X C = ⊥ := le_antisymm hle bot_le
    rw [this] at h
    exact absurd h (by simp)
  | d + 1 =>
    by_contra hall; push_neg at hall
    -- All trees of depth d+1 are not shattered. So Ldim ≤ d.
    have hle : LittlestoneDim X C ≤ ↑(↑d : WithTop ℕ) := by
      apply iSup₂_le; intro n ⟨T, hT⟩
      by_cases hnd : n ≤ d
      · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by exact_mod_cast hnd))
      · push_neg at hnd
        have hnd' : d + 1 ≤ n := hnd
        exact absurd (T.isShattered_truncate hT hnd') (hall _)
    -- But h says Ldim ≥ d + 1 > d. Contradiction.
    have hle' : (↑(↑(d + 1) : WithTop ℕ) : WithBot (WithTop ℕ)) ≤ ↑(↑d : WithTop ℕ) :=
      le_trans h hle
    exact absurd hle' (by norm_cast; omega)

-- ============================================================
-- KEY LEMMA: SOA mistake → Ldim strictly decreases
-- ============================================================

/-- When Ldim(V) = 0 (↑↑0), all concepts in V agree on every point.
    Key lemma: at dimension 0, all surviving concepts agree. -/
private theorem ldim_zero_all_agree {X : Type} {V : ConceptClass X Bool}
    (hd : LittlestoneDim X V = ↑(↑0 : WithTop ℕ)) (hne : V.Nonempty)
    (x : X) (c₁ c₂ : X → Bool) (hc₁ : c₁ ∈ V) (hc₂ : c₂ ∈ V) :
    c₁ x = c₂ x := by
  by_contra hdis
  -- c₁ x ≠ c₂ x, so one is true and the other false
  have hct : ∃ ct ∈ V, ct x = true := by
    cases h1 : c₁ x <;> cases h2 : c₂ x
    · exact absurd (h1.trans h2.symm) hdis  -- ff: contradiction
    · exact ⟨c₂, hc₂, h2⟩  -- ft
    · exact ⟨c₁, hc₁, h1⟩  -- tf
    · exact absurd (h1.trans h2.symm) hdis  -- tt: contradiction
  have hcf : ∃ cf ∈ V, cf x = false := by
    cases h1 : c₁ x <;> cases h2 : c₂ x
    · exact absurd (h1.trans h2.symm) hdis
    · exact ⟨c₁, hc₁, h1⟩
    · exact ⟨c₂, hc₂, h2⟩
    · exact absurd (h1.trans h2.symm) hdis
  -- Build a depth-1 shattered tree
  obtain ⟨ct, hctV, hctx⟩ := hct
  obtain ⟨cf, hcfV, hcfx⟩ := hcf
  have hge : LittlestoneDim X V ≥ ↑(↑1 : WithTop ℕ) :=
    le_iSup₂_of_le 1 ⟨.branch x .leaf .leaf,
      ⟨ct, hctV, hctx⟩, ⟨cf, hcfV, hcfx⟩,
      ⟨ct, ⟨hctV, hctx⟩⟩, ⟨cf, ⟨hcfV, hcfx⟩⟩⟩ le_rfl
  rw [hd] at hge
  exact absurd hge (by norm_cast)

/-- On an SOA mistake, the Ldim of the version space strictly decreases. -/
private theorem ldim_strict_decrease_on_mistake {X : Type}
    {C : ConceptClass X Bool} {history : List (X × Bool)} {x : X} {c : X → Bool}
    (hc_vs : c ∈ versionSpace C history)
    (hpred : (SOA X C).predict history x ≠ c x)
    (hfin : LittlestoneDim X (versionSpace C history) < ⊤) :
    LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) <
    LittlestoneDim X (versionSpace C history) := by
  -- Setup
  let V := versionSpace C history
  let b := (SOA X C).predict history x
  have hcx_ne_b : c x ≠ b := fun h => hpred (h ▸ rfl)
  -- New version space ⊆ {c' ∈ V | c' x = c x}
  have hvs_sub : versionSpace C (history ++ [(x, c x)]) ⊆ {c' ∈ V | c' x = c x} := by
    intro c' ⟨hc'C, hcons⟩
    exact ⟨⟨hc'C, fun p hp => hcons p (List.mem_append_left _ hp)⟩,
           hcons (x, c x) (List.mem_append_right _ (List.mem_singleton.mpr rfl))⟩
  have hle_side : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) ≤
      LittlestoneDim X {c' ∈ V | c' x = c x} := by
    apply iSup₂_le; intro n ⟨T, hT⟩
    exact le_iSup₂_of_le n ⟨T, T.isShattered_mono hvs_sub hT⟩ le_rfl
  -- Get finite Ldim
  obtain ⟨d, hd⟩ : ∃ d : ℕ, LittlestoneDim X V = ↑(↑d : WithTop ℕ) := by
    cases hc : LittlestoneDim X V with
    | bot => -- Ldim = ⊥ means empty. But c ∈ V, contradiction.
      have : V.Nonempty := ⟨c, hc_vs⟩
      have hge : LittlestoneDim X V ≥ ↑(↑0 : WithTop ℕ) :=
        le_iSup₂_of_le 0 ⟨.leaf, this⟩ le_rfl
      rw [hc] at hge; exact absurd hge (by simp)
    | coe v =>
      cases v with
      | top => -- ⊤ case: contradicts hfin
        have : LittlestoneDim X V = ⊤ := hc
        rw [this] at hfin; exact absurd hfin (lt_irrefl _)
      | coe n => exact ⟨n, rfl⟩
  -- c x = !b (since c x ≠ b and Bool has exactly two values)
  have hcx_eq_notb : c x = !b := by
    show c x = !(SOA X C).predict history x
    cases hcx : c x <;> cases hbv : (SOA X C).predict history x <;> simp_all
  -- Handle d = 0: when Ldim(V)=0, all concepts agree → SOA predicts correctly → no mistake possible
  cases hd0 : d with
  | zero =>
    rw [hd0] at hd
    have hne : V.Nonempty := ⟨c, hc_vs⟩
    -- All concepts in V agree on x with c
    have hagree : ∀ c' ∈ V, c' x = c x :=
      fun c' hc' => ldim_zero_all_agree hd hne x c' c hc' hc_vs
    -- SOA sides: {c' ∈ V | c' x = c x} = V, {c' ∈ V | c' x = !(c x)} = ∅
    -- So Ldim of c x side ≥ 0, Ldim of !(c x) side = ⊥
    -- SOA picks the c x side → predicts c x → no mistake
    have h_cx_side_eq_V : {c' ∈ V | c' x = c x} = V := by
      ext c'; simp only [Set.mem_sep_iff]; exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, hagree c' h⟩⟩
    have h_notcx_empty : ¬ ({c' ∈ V | c' x = !(c x)}).Nonempty := by
      intro ⟨c', hc'V, hc'x⟩
      have := hagree c' hc'V
      cases hcx : c x <;> simp_all
    have h_notcx_ldim : LittlestoneDim X {c' ∈ V | c' x = !(c x)} = ⊥ := by
      apply le_antisymm _ bot_le
      apply iSup₂_le; intro n ⟨T, hT⟩
      exact absurd (T.nonempty_of_isShattered hT) h_notcx_empty
    -- Now show SOA predicts c x:
    -- If c x = true: Ldim(true side) = Ldim(V) ≥ 0 > ⊥ = Ldim(false side) → SOA picks true = c x
    -- If c x = false: Ldim(true side) = ⊥ < Ldim(false side) = Ldim(V) → SOA picks false = c x
    exfalso; apply hpred
    show (SOA X C).predict history x = c x
    simp only [SOA]
    cases hcx : c x
    · -- c x = false
      simp only [hcx, Bool.not_false] at h_notcx_ldim h_cx_side_eq_V
      -- true side is empty (Ldim = ⊥), false side = V
      simp only [ite_eq_right_iff]
      intro hge_contra
      -- hge_contra : Ldim(true side) ≥ Ldim(false side)
      -- But Ldim(true side) = ⊥ and Ldim(false side) ≥ 0
      rw [h_notcx_ldim] at hge_contra
      have : LittlestoneDim X {c' ∈ V | c' x = false} ≥ ↑(↑0 : WithTop ℕ) := by
        rw [h_cx_side_eq_V]
        exact le_iSup₂_of_le 0 ⟨.leaf, hne⟩ le_rfl
      exact absurd (le_trans this hge_contra) (by simp)
    · -- c x = true
      simp only [hcx, Bool.not_true] at h_notcx_ldim h_cx_side_eq_V
      -- false side is empty, true side = V
      simp only [ite_eq_left_iff]
      intro hlt_contra
      -- hlt_contra says ¬(Ldim(true) ≥ Ldim(false)), i.e., Ldim(true) < Ldim(false)
      -- But Ldim(false) = ⊥ < Ldim(true) ≥ 0. Contradiction.
      push_neg at hlt_contra
      rw [h_notcx_ldim] at hlt_contra
      have : LittlestoneDim X {c' ∈ V | c' x = true} ≥ ↑(↑0 : WithTop ℕ) := by
        rw [h_cx_side_eq_V]
        exact le_iSup₂_of_le 0 ⟨.leaf, hne⟩ le_rfl
      exact absurd hlt_contra not_lt_bot
  | succ d' =>
  -- d ≥ 1. Use suffices + by_contra + both-side extraction.
  rw [hd0] at hd -- hd : LittlestoneDim X V = ↑(↑(d' + 1) : WithTop ℕ)
  suffices hsuff : LittlestoneDim X {c' ∈ V | c' x = c x} < ↑(↑(d' + 1) : WithTop ℕ) by
    calc LittlestoneDim X (versionSpace C (history ++ [(x, c x)]))
        ≤ LittlestoneDim X {c' ∈ V | c' x = c x} := hle_side
      _ < ↑(↑(d' + 1) : WithTop ℕ) := hsuff
      _ = LittlestoneDim X V := hd.symm
  by_contra hge; push_neg at hge
  have hsoa := soa_predict_spec C history x
  have hnb_ge : LittlestoneDim X {c' ∈ V | c' x = !b} ≥ ↑(↑(d' + 1) : WithTop ℕ) := by
    rwa [show (c x) = !b from hcx_eq_notb] at hge
  have hb_ge : LittlestoneDim X {c' ∈ V | c' x = b} ≥ ↑(↑(d' + 1) : WithTop ℕ) :=
    le_trans hnb_ge hsoa
  obtain ⟨Tb, hTb⟩ := exists_shattered_of_ldim_ge hb_ge
  obtain ⟨Tnb, hTnb⟩ := exists_shattered_of_ldim_ge hnb_ge
  have hwnb : ∃ c' ∈ V, c' x = !b := ⟨c, hc_vs, hcx_eq_notb⟩
  -- d' + 1 ≥ 1: extract b-side witness from the depth-(d'+1) shattered tree
  have hwb : ∃ c' ∈ V, c' x = b := by
    match Tb, hTb with
    | .branch y l r, hTb =>
      simp only [LTree.isShattered] at hTb
      obtain ⟨⟨c', hc'mem, _⟩, _⟩ := hTb
      exact ⟨c', hc'mem.1, hc'mem.2⟩
  have hge_dp : LittlestoneDim X V ≥ ↑(↑(d' + 1 + 1) : WithTop ℕ) :=
    ldim_branch_lower_bound ⟨Tb, hTb⟩ ⟨Tnb, hTnb⟩ hwb hwnb
  rw [hd] at hge_dp
  exact absurd hge_dp (by norm_cast; omega)

-- ============================================================
-- BACKWARD DIRECTION (potential function argument)
-- ============================================================

/-- SOA mistakes from a given state are bounded by the Ldim of the version space.
    This is the core potential function argument: Ldim serves as the potential. -/
private theorem soa_mistakes_bounded {X : Type} {C : ConceptClass X Bool}
    (c : X → Bool) (hcC : c ∈ C)
    (history : List (X × Bool))
    (hcons : ∀ p ∈ history, c p.1 = p.2)
    (d : ℕ) (hd : LittlestoneDim X (versionSpace C history) ≤ ↑(↑d : WithTop ℕ))
    (hfin : LittlestoneDim X (versionSpace C history) < ⊤)
    (seq : List X) :
    (SOA X C).mistakesFrom history c seq ≤ d := by
  induction seq generalizing history d with
  | nil => simp [OnlineLearner.mistakesFrom]
  | cons x xs ih =>
    -- Use interface lemma to unfold one step (doesn't expose SOA internals)
    rw [SOA_mistakesFrom_cons]
    by_cases hmistake : (SOA X C).predict history x ≠ c x
    · -- SOA makes a mistake: Ldim strictly decreases (potential decreases)
      rw [if_pos hmistake]
      have hc_vs : c ∈ versionSpace C history := target_in_versionSpace hcC hcons
      have hdecrease := ldim_strict_decrease_on_mistake hc_vs hmistake hfin
      have hcons' : ∀ p ∈ history ++ [(x, c x)], c p.1 = p.2 := by
        intro p hp
        cases List.mem_append.mp hp with
        | inl h => exact hcons p h
        | inr h => simp at h; rw [h]
      -- d must be ≥ 1 (Ldim decreases, so d > 0)
      cases d with
      | zero =>
        -- Ldim(V) ≤ 0 but Ldim decreases → Ldim(V') < Ldim(V) ≤ 0.
        -- But c ∈ V', so V' nonempty, so Ldim(V') ≥ 0. Contradiction.
        have hc_vs' : c ∈ versionSpace C (history ++ [(x, c x)]) :=
          target_in_versionSpace hcC hcons'
        have hge0 : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) ≥
            ↑(↑0 : WithTop ℕ) :=
          le_iSup₂_of_le 0 ⟨.leaf, ⟨c, hc_vs'⟩⟩ le_rfl
        have hlt := lt_of_lt_of_le hdecrease hd
        exact absurd hlt (not_lt.mpr hge0)
      | succ d' =>
        -- Ldim of new VS ≤ d' (reusable lattice fact: a < ↑↑(d'+1) → a ≤ ↑↑d')
        have hd_new : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) ≤
            ↑(↑d' : WithTop ℕ) :=
          WithBot_WithTop_lt_succ_le (lt_of_lt_of_le hdecrease hd)
        have hfin_new : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) < ⊤ :=
          lt_of_lt_of_le hdecrease (le_of_lt hfin)
        have ih_result := ih (history ++ [(x, c x)]) hcons' d' hd_new hfin_new
        omega
    · -- SOA predicts correctly: no mistake, φ doesn't decrease but bound holds
      rw [if_neg hmistake]; simp only [Nat.zero_add]
      have hcons' : ∀ p ∈ history ++ [(x, c x)], c p.1 = p.2 := by
        intro p hp
        cases List.mem_append.mp hp with
        | inl h => exact hcons p h
        | inr h => simp at h; rw [h]
      have hle_new : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) ≤
          ↑(↑d : WithTop ℕ) := by
        calc LittlestoneDim X (versionSpace C (history ++ [(x, c x)]))
            ≤ LittlestoneDim X (versionSpace C history) := by
              apply iSup₂_le; intro n ⟨T, hT⟩
              exact le_iSup₂_of_le n ⟨T, T.isShattered_mono versionSpace_append hT⟩ le_rfl
          _ ≤ ↑(↑d : WithTop ℕ) := hd
      have hfin_new : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) < ⊤ := by
        calc LittlestoneDim X (versionSpace C (history ++ [(x, c x)]))
            ≤ LittlestoneDim X (versionSpace C history) := by
              apply iSup₂_le; intro n ⟨T, hT⟩
              exact le_iSup₂_of_le n ⟨T, T.isShattered_mono versionSpace_append hT⟩ le_rfl
          _ < ⊤ := hfin
      exact ih (history ++ [(x, c x)]) hcons' d hle_new hfin_new

/-- Backward direction: LittlestoneDim < ⊤ → OnlineLearnable. -/
theorem backward_direction (X : Type) (C : ConceptClass X Bool) :
    LittlestoneDim X C < ⊤ → OnlineLearnable X Bool C := by
  intro h
  -- Extract finite Ldim bound
  obtain ⟨d, hd⟩ : ∃ d : ℕ, LittlestoneDim X C ≤ ↑(↑d : WithTop ℕ) := by
    cases hc : LittlestoneDim X C with
    | bot => exact ⟨0, bot_le⟩
    | coe v =>
      cases v with
      | top => simp [hc] at h
      | coe n => exact ⟨n, le_rfl⟩
  refine ⟨d, SOA X C, fun c hcC seq => ?_⟩
  -- SOA makes at most d mistakes (potential function argument)
  have hle : LittlestoneDim X (versionSpace C []) ≤ ↑(↑d : WithTop ℕ) := by
    have : versionSpace C [] = C := by
      ext c'; simp [versionSpace]
    rw [this]; exact hd
  have hfin : LittlestoneDim X (versionSpace C []) < ⊤ := by
    have : versionSpace C [] = C := by ext c'; simp [versionSpace]
    rw [this]; exact lt_of_le_of_lt hd (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (a := d)))
  have hmf := soa_mistakes_bounded c hcC [] (by simp) d hle hfin seq
  rwa [show (SOA X C).mistakesFrom [] c seq = (SOA X C).mistakesFrom (SOA X C).init c seq
    from by rw [SOA_init_eq],
    mistakesFrom_init_eq] at hmf

-- ============================================================
-- MAIN THEOREMS
-- ============================================================

/-- Littlestone characterization: C is online-learnable iff LittlestoneDim(C) < ∞. -/
theorem littlestone_characterization (X : Type)
    (C : ConceptClass X Bool) :
    OnlineLearnable X Bool C ↔ LittlestoneDim X C < ⊤ :=
  ⟨forward_direction X C, backward_direction X C⟩

/-- Adversary lower bound: if a tree of depth n is shattered by C, then any
    mistake-bounded learner must allow at least n mistakes (the inf-sup half of minimax). -/
private theorem adversary_lower_bound {X : Type} {C : ConceptClass X Bool}
    {n : ℕ} (T : LTree X n) (hT : T.isShattered C)
    {M : ℕ} (hM : MistakeBounded X Bool C M) : n ≤ M := by
  obtain ⟨L, hL⟩ := hM
  have hne : C.Nonempty := T.nonempty_of_isShattered hT
  obtain ⟨seq, c, hcC, hcount⟩ := adversary_core L L.init T hT hne
  have hbound := hL c hcC seq
  rw [← mistakesFrom_init_eq] at hbound
  omega

/-- The optimal mistake bound equals the Littlestone dimension (for nonempty C).
    OptimalMistakeBound : WithTop ℕ, LittlestoneDim : WithBot (WithTop ℕ).
    For nonempty C, LittlestoneDim ≥ 0, so the coercion ↑(OptimalMistakeBound) works. -/
theorem optimal_mistake_bound_eq_ldim (X : Type)
    (C : ConceptClass X Bool) (hne : C.Nonempty) :
    (↑(OptimalMistakeBound X C) : WithBot (WithTop ℕ)) = LittlestoneDim X C := by
  apply le_antisymm
  · -- ≤ direction: OptimalMistakeBound ≤ Ldim
    -- If Ldim = ⊤, then OptimalMistakeBound ≤ ⊤ trivially (anything ≤ ↑⊤)
    -- If Ldim = ↑↑d, then SOA achieves d mistakes → MistakeBounded d → OptimalMistakeBound ≤ d
    cases hc : LittlestoneDim X C with
    | bot =>
      -- Ldim = ⊥ for nonempty C → impossible (C.Nonempty gives shattered leaf)
      have hge : LittlestoneDim X C ≥ ↑(↑0 : WithTop ℕ) :=
        le_iSup₂_of_le 0 ⟨.leaf, hne⟩ le_rfl
      rw [hc] at hge; exact absurd hge (by simp)
    | coe v =>
      cases v with
      | top => -- Ldim = ⊤ → ↑OptimalMistakeBound ≤ ↑⊤ = ⊤
        exact le_top
      | coe d => -- Ldim = ↑↑d
        -- backward_direction gives: OnlineLearnable, i.e., ∃ M, MistakeBounded M
        have hfin : LittlestoneDim X C < ⊤ := by
          rw [hc]; exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (a := d))
        obtain ⟨M, hMB⟩ := backward_direction X C hfin
        -- OptimalMistakeBound ≤ M (since MistakeBounded M)
        have : OptimalMistakeBound X C ≤ ↑M := iInf₂_le M hMB
        -- M ≤ d (from the proof structure: backward_direction uses Ldim ≤ d)
        -- Actually we just need OptimalMistakeBound ≤ ↑d, and hc says Ldim = ↑↑d
        -- backward_direction gives MistakeBounded for some M. Need M ≤ d to close.
        -- Actually, backward_direction refines M = d from the proof. Let's check:
        -- backward_direction uses SOA with bound d, so M = d and hMB = MistakeBounded d
        -- But backward_direction doesn't guarantee M ≤ d from the statement alone.
        -- We need: OptimalMistakeBound ≤ Ldim. Ldim = ↑↑d. So need OptimalMistakeBound ≤ ↑d.
        -- From backward_direction: MistakeBounded M holds. So OptimalMistakeBound ≤ ↑M.
        -- We need M ≤ d. But backward_direction's M comes from the ∃ inside OnlineLearnable.
        -- The construction in backward_direction sets M = d, so this works.
        -- Let me check: backward_direction says refine ⟨d, SOA X C, ...⟩ so M = d.
        -- But from the TYPE, we only know ∃ M, MistakeBounded M. We need MistakeBounded d specifically.
        -- Solution: invoke soa_mistakes_bounded directly instead of going through backward_direction.
        have hMB_d : MistakeBounded X Bool C d := by
          refine ⟨SOA X C, fun c' hc'C seq => ?_⟩
          have hle : LittlestoneDim X (versionSpace C []) ≤ ↑(↑d : WithTop ℕ) := by
            have : versionSpace C [] = C := by ext c''; simp [versionSpace]
            rw [this]; exact le_of_eq hc
          have hfin' : LittlestoneDim X (versionSpace C []) < ⊤ := by
            have : versionSpace C [] = C := by ext c''; simp [versionSpace]
            rw [this]; exact hfin
          have hmf := soa_mistakes_bounded c' hc'C [] (by simp) d hle hfin' seq
          rwa [show (SOA X C).mistakesFrom [] c' seq = (SOA X C).mistakesFrom (SOA X C).init c' seq
            from by rw [SOA_init_eq], mistakesFrom_init_eq] at hmf
        exact WithBot.coe_le_coe.mpr (iInf₂_le d hMB_d)
  · -- ≥ direction: Ldim ≤ OptimalMistakeBound
    -- For each shattered tree of depth n, adversary forces n mistakes → OptimalMistakeBound ≥ n
    apply iSup₂_le; intro n ⟨T, hT⟩
    -- Any learner makes ≥ n mistakes against the adversary from T
    -- So MistakeBounded M → M ≥ n → OptimalMistakeBound ≥ n
    suffices h : (↑(↑n : WithTop ℕ) : WithBot (WithTop ℕ)) ≤ ↑(OptimalMistakeBound X C) by
      exact h
    apply WithBot.coe_le_coe.mpr
    -- Need: ↑n ≤ OptimalMistakeBound X C, i.e., ↑n ≤ ⨅ M (_ : MistakeBounded), ↑M
    -- Equivalently: ∀ M, MistakeBounded M → n ≤ M
    apply le_iInf₂; intro M hM
    -- Use the adversary lower bound
    exact WithTop.coe_le_coe.mpr (adversary_lower_bound T hT hM)

