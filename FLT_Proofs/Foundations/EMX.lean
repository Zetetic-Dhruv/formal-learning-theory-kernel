/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Image

/-!
# EMX undecidability: compression of the finite-subset family (Kuratowski form)

Formalization of the combinatorial core of

  Ben-David, Hrubeš, Moran, Shpilka, Yehudayoff,
  *Learnability can be undecidable*, Nature Machine Intelligence **1** (2019) 44–48.

EMX-learnability of the family `Fᶠⁱⁿ_[0,1]` of all finite subsets of `[0,1]` is independent
of ZFC; the reduction runs through compression schemes (Definition 2, Theorem 1). This file
isolates Theorem 1:

> `Fᶠⁱⁿ_X` admits a `(k+2) → (k+1)` compression scheme  ↔  `#X ≤ ℵ_k`.

This is a repackaging of **Kuratowski's free set theorem** (1951): the reconstruction is a
set-mapping `η : [X]^{≤d} → [X]^{<ω}`, and "no `(k+2)`-element free set" is exactly the
covering condition below. We model the scheme set-theoretically (`η : Finset X → Finset X`),
which is faithful to the Kuratowski object and avoids the spurious order-structure of a
tuple encoding. The paper's *monotone* strengthening (`η` monotone under `⊆`) is a refinement
not needed for the reverse direction; we omit it so the reverse theorem is the stronger
statement (any scheme, monotone or not, bounds `#X`).

The two directions are stated separately to locate the axiom of choice:

* **Reverse (A)** `scheme ⟹ #X ≤ ℵ_k`: a downward induction (Lemma 2 collapse) terminated by
  the impossibility of a `1 → 0` scheme on an infinite set. The choice-light direction, and the
  one proved here in full.
* **Forward (B)** `#X ≤ ℵ_k ⟹ scheme`: Kuratowski's well-ordering construction (a well-order
  of `X` of order type `≤ ω_k`). This is where the axiom of choice enters; it is the hard
  direction of Kuratowski's theorem and is left as a documented obligation.
-/

universe u

namespace FLT.Foundations.EMX

open Cardinal

/-- A **compression scheme** of size `m → d` for the family `Fᶠⁱⁿ_X` of all finite subsets of
`X` (Ben-David–Hrubeš–Moran–Shpilka–Yehudayoff 2019, Definition 2, in its Kuratowski
set-mapping form): a reconstruction `η` sending a finite set of retained points to a finite
subset of `X`, such that every `m`-element set is covered by the reconstruction of some `d` of
its own points. The content lives in `d < m`. Equivalently (Kuratowski), `η` witnesses that no
`m`-element set is *free*. -/
structure MonoComp (X : Type u) (m d : ℕ) where
  /-- Reconstruction: a finite set of retained points determines a finite subset of `X`. -/
  η : Finset X → Finset X
  /-- Compression: every `m`-element set `A` is covered by the reconstruction `η B` of some
  `B ⊆ A` with at most `d` points. -/
  covers : ∀ A : Finset X, A.card = m → ∃ B ⊆ A, B.card ≤ d ∧ A ⊆ η B

/-- **Base case (CLOSED).** A `1 → 0` compression scheme forces `X` to be finite.

A `1 → 0` scheme reconstructs from sets of size `≤ 0`, i.e. from `∅`, so `η ∅` is a fixed finite
set `F`; the covering condition on the singleton `{x}` says `x ∈ F` for every `x : X`. Hence `X`
embeds into the finite set `F`. This is the floor of the Lemma 2 induction: a `1 → 0` scheme on
an infinite set is impossible. Choice-free in spirit (the only `Classical.choice` is Mathlib's
`Finite`). -/
theorem monoComp_one_zero_finite (X : Type u) (hc : Nonempty (MonoComp X 1 0)) :
    Finite X := by
  obtain ⟨cs⟩ := hc
  have hmem : ∀ x : X, x ∈ cs.η ∅ := by
    intro x
    obtain ⟨B, _, hBcard, hBcov⟩ := cs.covers {x} (Finset.card_singleton x)
    have hBempty : B = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hBcard)
    rw [hBempty] at hBcov
    exact hBcov (Finset.mem_singleton_self x)
  exact Finite.of_injective (fun x : X => (⟨x, hmem x⟩ : {y // y ∈ cs.η ∅}))
    (fun a b h => by simpa using h)

/-- **O2a (cardinality core of the reduction, CLOSED).** For infinite `Y`, the union of all
reconstructions `η B` over finite sets `B` has cardinality at most `#Y`: there are exactly `#Y`
finite subsets of `Y` (`mk_finset_of_infinite`) and each `η B` is finite. This is Lemma 2's
`Z`. The codomain is an arbitrary `α` so the reduction can union reconstructions living in the
ambient type `X`, not just in `Y`. -/
theorem mk_iUnion_reconstr_le {Y : Type u} [Infinite Y] {α : Type u}
    (η : Finset Y → Finset α) :
    #(⋃ B : Finset Y, (↑(η B) : Set α)) ≤ #Y := by
  calc #(⋃ B : Finset Y, (↑(η B) : Set α))
      ≤ sum (fun B => #(↑(η B) : Set α)) := mk_iUnion_le_sum_mk
    _ ≤ sum (fun _ : Finset Y => #Y) := by
        apply sum_le_sum; intro B
        exact le_of_lt (lt_of_lt_of_le
          (Set.Finite.lt_aleph0 (Finset.finite_toSet (η B))) (aleph0_le_mk Y))
    _ = #(Finset Y) * #Y := by rw [Cardinal.sum_const']
    _ = #Y * #Y := by rw [Cardinal.mk_finset_of_infinite]
    _ = #Y := Cardinal.mul_eq_self (aleph0_le_mk Y)

/-- **Reduction (Lemma 2, CLOSED).** A `(j+2) → (j+1)` compression scheme on `X` restricts to a
`(j+1) → j` scheme on any subset `Y` of strictly smaller (infinite) cardinality.

Construction (the set-based form makes this clean, with no tuple bookkeeping): let
`Z = ⋃_{B ⊆ Y} η B ⊆ X`; by `mk_iUnion_reconstr_le`, `#Z ≤ #Y`, so `#(Z ∪ Y) ≤ #Y < #X` and we
may pick `x ∉ Z ∪ Y`. Define the restricted reconstruction `η_Y C = (η (insert x C)).subtype Y`.
For an `(j+1)`-set `A ⊆ Y`, apply the scheme to `A ∪ {x}` (size `j+2`): the retained `B ⊆ A ∪ {x}`
must contain `x`, for otherwise `B ⊆ Y` gives `η B ⊆ Z` while `x ∈ η B`, contradicting `x ∉ Z`.
Then `B \ {x} ⊆ A` has `≤ j` points and `η_Y (B \ {x})` covers `A`. -/
theorem monoComp_reduction (X : Type u) (j : ℕ) (Y : Set X) [Infinite (↥Y)]
    (hYX : Cardinal.mk (↥Y) < Cardinal.mk X) (hc : Nonempty (MonoComp X (j + 2) (j + 1))) :
    Nonempty (MonoComp (↥Y) (j + 1) j) := by
  classical
  obtain ⟨cs⟩ := hc
  -- `g B` reconstructs from the image of a finite subset of `Y`; `Z` collects all of them.
  set g : Finset (↥Y) → Finset X :=
    fun B => cs.η (B.map (Function.Embedding.subtype (· ∈ Y))) with hg
  set Z : Set X := ⋃ B : Finset (↥Y), (↑(g B) : Set X) with hZ
  have hZle : Cardinal.mk (Z : Set X) ≤ Cardinal.mk (↥Y) := mk_iUnion_reconstr_le g
  -- `Z ∪ Y` is still strictly smaller than `X`, so it omits some point `x`.
  have hWle : Cardinal.mk ((Z ∪ Y : Set X)) ≤ Cardinal.mk (↥Y) :=
    calc Cardinal.mk ((Z ∪ Y : Set X))
        ≤ Cardinal.mk (Z : Set X) + Cardinal.mk (↥Y) := Cardinal.mk_union_le Z Y
      _ ≤ Cardinal.mk (↥Y) + Cardinal.mk (↥Y) := by gcongr
      _ = Cardinal.mk (↥Y) := Cardinal.add_eq_self (Cardinal.aleph0_le_mk (↥Y))
  have hWlt : Cardinal.mk ((Z ∪ Y : Set X)) < Cardinal.mk X := lt_of_le_of_lt hWle hYX
  obtain ⟨x, hxW⟩ : ∃ x : X, x ∉ (Z ∪ Y : Set X) := by
    by_contra hcon
    push_neg at hcon
    rw [Set.eq_univ_of_forall hcon, Cardinal.mk_univ] at hWlt
    exact lt_irrefl _ hWlt
  have hxZ : x ∉ Z := fun h => hxW (Or.inl h)
  have hxY : x ∉ Y := fun h => hxW (Or.inr h)
  -- The restricted scheme on `Y`.
  refine ⟨⟨fun C => (cs.η (insert x (C.map (Function.Embedding.subtype (· ∈ Y))))).subtype (· ∈ Y),
    ?_⟩⟩
  intro A hA
  set A' : Finset X := A.map (Function.Embedding.subtype (· ∈ Y)) with hA'
  have hA'card : A'.card = j + 1 := by rw [hA', Finset.card_map]; exact hA
  have hA'subY : (↑A' : Set X) ⊆ Y := Finset.map_subtype_subset A
  have hxA' : x ∉ A' := fun h => hxY (hA'subY (Finset.mem_coe.mpr h))
  have hins : (insert x A').card = j + 2 := by
    rw [Finset.card_insert_of_notMem hxA', hA'card]
  obtain ⟨B, hBsub, hBcard, hBcov⟩ := cs.covers (insert x A') hins
  -- `x` must be retained, else `B ⊆ Y` forces `x ∈ η B ⊆ Z`.
  have hxB : x ∈ B := by
    by_contra hxB
    have hBA' : B ⊆ A' := by
      intro z hz
      rcases Finset.mem_insert.1 (hBsub hz) with rfl | h
      · exact absurd hz hxB
      · exact h
    have hBY : ∀ z ∈ B, z ∈ Y := fun z hz => hA'subY (Finset.mem_coe.mpr (hBA' hz))
    have hmap : (B.subtype (· ∈ Y)).map (Function.Embedding.subtype (· ∈ Y)) = B :=
      Finset.subtype_map_of_mem hBY
    have hxηB : x ∈ cs.η B := hBcov (Finset.mem_insert_self x A')
    apply hxZ
    rw [hZ, Set.mem_iUnion]
    refine ⟨B.subtype (· ∈ Y), ?_⟩
    simp only [Finset.mem_coe, hg]
    rw [hmap]
    exact hxηB
  -- Drop `x`: `C = (B \ {x})` lives in `Y`, has `≤ j` points, and `η_Y C ⊇ A`.
  have hBerA' : B.erase x ⊆ A' := by
    intro z hz
    have hzB := Finset.mem_of_mem_erase hz
    rcases Finset.mem_insert.1 (hBsub hzB) with rfl | h
    · exact absurd rfl (Finset.ne_of_mem_erase hz)
    · exact h
  have hBerY : ∀ z ∈ B.erase x, z ∈ Y := fun z hz => hA'subY (Finset.mem_coe.mpr (hBerA' hz))
  have hCmap : ((B.erase x).subtype (· ∈ Y)).map (Function.Embedding.subtype (· ∈ Y))
      = B.erase x := Finset.subtype_map_of_mem hBerY
  refine ⟨(B.erase x).subtype (· ∈ Y), ?_, ?_, ?_⟩
  · -- `C ⊆ A`
    intro a haC
    have h1 : (a : X) ∈ B.erase x := Finset.mem_subtype.1 haC
    have h2 : (a : X) ∈ A' := hBerA' h1
    rw [hA'] at h2
    exact (Finset.mem_map' _).mp h2
  · -- `C.card ≤ j`
    have h1 : ((B.erase x).subtype (· ∈ Y)).card = ((B.erase x).filter (· ∈ Y)).card :=
      Finset.card_subtype _ _
    have h2 : ((B.erase x).filter (· ∈ Y)).card ≤ (B.erase x).card := Finset.card_filter_le _ _
    have h3 : (B.erase x).card = B.card - 1 := Finset.card_erase_of_mem hxB
    omega
  · -- `A ⊆ η_Y C`
    intro a haA
    simp only [Finset.mem_subtype]
    rw [hCmap, Finset.insert_erase hxB]
    have : (a : X) ∈ A' := by rw [hA', Finset.mem_map]; exact ⟨a, haA, rfl⟩
    exact hBcov (Finset.mem_insert_of_mem this)

/-- **Theorem 1, reverse direction (A, CLOSED).** A `(k+2) → (k+1)` compression scheme forces
`#X ≤ ℵ_k`. Downward induction on `k`: at each step pick a subset `Y` of cardinality `ℵ_k`
(strictly below an assumed `#X > ℵ_k`), restrict the scheme via `monoComp_reduction`, and apply
the inductive hypothesis to contradict `#Y = ℵ_k`. The base case `k = 0` bottoms out in
`monoComp_one_zero_finite`: a `1 → 0` scheme on the infinite `Y` is impossible. -/
theorem card_le_aleph_of_monoComp (X : Type u) (k : ℕ)
    (h : Nonempty (MonoComp X (k + 2) (k + 1))) :
    Cardinal.mk X ≤ Cardinal.aleph (k : Ordinal) := by
  induction k generalizing X with
  | zero =>
    by_contra hlt
    push_neg at hlt
    obtain ⟨Y, hY⟩ := Cardinal.le_mk_iff_exists_set.1 (le_of_lt hlt)
    haveI : Infinite (↥Y) :=
      Cardinal.infinite_iff.2 (by rw [hY]; exact Cardinal.aleph0_le_aleph _)
    have hYX : Cardinal.mk (↥Y) < Cardinal.mk X := by rw [hY]; exact hlt
    exact (monoComp_one_zero_finite _ (monoComp_reduction X 0 Y hYX h)).false
  | succ k ih =>
    by_contra hlt
    push_neg at hlt
    obtain ⟨Y, hY⟩ := Cardinal.le_mk_iff_exists_set.1 (le_of_lt hlt)
    haveI : Infinite (↥Y) :=
      Cardinal.infinite_iff.2 (by rw [hY]; exact Cardinal.aleph0_le_aleph _)
    have hYX : Cardinal.mk (↥Y) < Cardinal.mk X := by rw [hY]; exact hlt
    have hYle : Cardinal.mk (↥Y) ≤ Cardinal.aleph (k : Ordinal) :=
      ih _ (monoComp_reduction X (k + 1) Y hYX h)
    rw [hY] at hYle
    have hkk : k + 1 ≤ k := by exact_mod_cast Cardinal.aleph_le_aleph.1 hYle
    omega

/-- **Theorem 1, forward direction (B, OPEN, the axiom-of-choice seam).** If `#X ≤ ℵ_k` then
`Fᶠⁱⁿ_X` admits a `(k+2) → (k+1)` compression scheme. This is the hard direction of Kuratowski's
free set theorem: fix a well-ordering of `X` of order type `≤ ω_k = (ℵ_k).ord`
(`Cardinal.ord_aleph`) and let `η B` reconstruct from the `≺`-predecessors, descending the aleph
hierarchy via `Ordinal.typein` and the fact that an initial segment below a point of `ω_k` has
cardinality `≤ ℵ_{k-1}`. The well-ordering of an arbitrary `X` of cardinality `ℵ_k` is the choice
artifact; removing it collapses this direction (the content of the EMX/CH undecidability). Left as
a documented obligation per the project's scope decision. -/
theorem monoComp_of_card_le_aleph (X : Type u) (k : ℕ)
    (h : Cardinal.mk X ≤ Cardinal.aleph (k : Ordinal)) :
    Nonempty (MonoComp X (k + 2) (k + 1)) := by
  sorry

/-- **Theorem 1** (Ben-David, Hrubeš, Moran, Shpilka, Yehudayoff, *Nature Machine Intelligence*
2019), the Kuratowski equivalence: `Fᶠⁱⁿ_X` admits a `(k+2) → (k+1)` compression scheme **iff**
`#X ≤ ℵ_k`. Composed with `#[0,1] ≤ ℵ_k` being a continuum-hypothesis variant, this is the source
of the ZFC-independence of EMX learnability. The reverse implication is proved
(`card_le_aleph_of_monoComp`); the forward implication is the choice-using
`monoComp_of_card_le_aleph`. -/
theorem monoComp_iff_card_le_aleph (X : Type u) (k : ℕ) :
    Cardinal.mk X ≤ Cardinal.aleph (k : Ordinal) ↔ Nonempty (MonoComp X (k + 2) (k + 1)) :=
  ⟨monoComp_of_card_le_aleph X k, card_le_aleph_of_monoComp X k⟩

end FLT.Foundations.EMX
