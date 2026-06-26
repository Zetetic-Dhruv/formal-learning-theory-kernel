/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Image

/-!
# EMX undecidability: monotone compression of the finite-subset family

Formalization of the combinatorial core of

  Ben-David, Hrubeš, Moran, Shpilka, Yehudayoff,
  *Learnability can be undecidable*, Nature Machine Intelligence **1** (2019) 44–48.

EMX-learnability of the family `Fᶠⁱⁿ_[0,1]` of all finite subsets of `[0,1]` is independent
of ZFC; the reduction runs through **monotone compression schemes** (Definition 2, Theorem 1).
This file isolates Theorem 1:

> `Fᶠⁱⁿ_X` admits a `(k+2) → (k+1)` monotone compression scheme  ↔  `#X ≤ ℵ_k`.

(The schemes that matter compress one point, `(m+1) → m`; the CH-true case `#[0,1] = ℵ₁`,
`k = 1`, gives the `3 → 2` scheme the paper exhibits.) The forward direction uses a
well-ordering of `X` of order type `≤ ω_k`, which is where the axiom of choice enters; the
reverse is a finite induction (Lemma 2 collapse) and is the candidate for a choice-free
proof. The directions are stated separately to locate the choice-dependence.
-/

universe u

namespace FLT.Foundations.EMX

open Cardinal

/-- A **monotone compression scheme** of size `m → d` for the family `Fᶠⁱⁿ_X` of all
finite subsets of `X` (Ben-David–Hrubeš–Moran–Shpilka–Yehudayoff 2019, Definition 2,
specialized to the finite-subset family): a reconstruction `η` from `d` retained points,
such that any `m` points are covered by the reconstruction of some `d` of their own
coordinates. The content lives in `d < m`. -/
structure MonoComp (X : Type u) (m d : ℕ) where
  /-- Reconstruction: `d` retained points determine a finite subset of `X`. -/
  η : (Fin d → X) → Finset X
  /-- Compression: every `m`-tuple is covered by the reconstruction of some `d` of its
  own coordinates. -/
  covers : ∀ x : Fin m → X, ∃ s : Fin d → Fin m, ∀ i : Fin m, x i ∈ η (fun j => x (s j))

/-- **Base case (CLOSED).** A `1 → 0` monotone compression scheme forces `X` to be finite.

A `1 → 0` scheme reconstructs from *zero* points, so `η` of the (unique) empty tuple is a
fixed finite set `F`; the covering condition applied to the constant `1`-tuple at `x` says
`x ∈ F` for every `x : X`. Hence `X` embeds into the finite set `F`. This is the floor of
the Lemma 2 induction: a `1 → 0` scheme on an infinite set is impossible. Choice-free. -/
theorem monoComp_one_zero_finite (X : Type u) (hc : Nonempty (MonoComp X 1 0)) :
    Finite X := by
  obtain ⟨cs⟩ := hc
  -- `F` is the reconstruction of the empty tuple; every element of `X` lands in it.
  set F : Finset X := cs.η Fin.elim0 with hF
  have hmem : ∀ x : X, x ∈ F := by
    intro x
    obtain ⟨s, hs⟩ := cs.covers (fun _ => x)
    have h0 := hs 0
    -- the reconstructed tuple is a map `Fin 0 → X`, hence equal to `Fin.elim0`
    have hfun : (fun j : Fin 0 => (fun _ : Fin 1 => x) (s j)) = Fin.elim0 :=
      funext (fun j => j.elim0)
    rw [hfun] at h0
    simpa [hF] using h0
  -- `X ↪ {y // y ∈ F}`, a finite type
  exact Finite.of_injective (fun x : X => (⟨x, hmem x⟩ : {y // y ∈ F}))
    (fun a b h => by simpa using h)

open Cardinal in
/-- **O2a (cardinality core of the reduction).** For infinite `Y`, the union of all
reconstructions `η t` over `d`-tuples `t` has cardinality at most `#Y`: there are at most
`#Y` distinct tuples (`#Y ^ d = #Y` for infinite `Y`, `d ≥ 1`; `= 1 ≤ #Y` for `d = 0`) and
each `η t` is finite. This is Lemma 2's `Z`. -/
theorem mk_iUnion_reconstr_le {Y : Type u} [Infinite Y] {α : Type u} {d : ℕ}
    (η : (Fin d → Y) → Finset α) :
    #(⋃ t : Fin d → Y, (↑(η t) : Set α)) ≤ #Y := by
  have hidx : #(Fin d → Y) ≤ #Y := by
    have h : #(Fin d → Y) = #Y ^ d := by
      simp [Cardinal.mk_arrow, Cardinal.mk_fin, Cardinal.power_natCast]
    rw [h]
    exact Cardinal.power_nat_le (aleph0_le_mk Y)
  calc #(⋃ t : Fin d → Y, (↑(η t) : Set α))
      ≤ sum (fun t => #(↑(η t) : Set α)) := mk_iUnion_le_sum_mk
    _ ≤ sum (fun _ : Fin d → Y => #Y) := by
        apply sum_le_sum; intro t
        exact le_of_lt (lt_of_lt_of_le
          (Set.Finite.lt_aleph0 (Finset.finite_toSet (η t))) (aleph0_le_mk Y))
    _ = #(Fin d → Y) * #Y := by rw [Cardinal.sum_const']
    _ ≤ #Y * #Y := mul_le_mul_right' hidx _
    _ = #Y := Cardinal.mul_eq_self (aleph0_le_mk Y)

/-- **Reduction (Lemma 2, OPEN).** A `(j+2) → (j+1)` monotone compression scheme on an
infinite `X` yields a `(j+1) → j` scheme on a subset whose cardinality is one aleph lower.

PROOF ROUTE (scheduled structure for this `sorry`, A5): for a subset `Y ⊆ X`, the union
`Z = ⋃_{T ⊆ Y, |T| ≤ j+1} η(T)` of reconstructions has `#Z = #Y` for infinite `Y`
(`Cardinal.mk_iUnion_le`, `mul_eq_self`). Taking `Y` of cardinality `< #X` lets one pick
`x ∈ X \ Z`; the compression of `T ∪ {x}` must drop `x`, exposing a `(j+1) → j` scheme on
`Y`. This direction is the candidate choice-free collapse; the cardinality bookkeeping is
the remaining work. -/
theorem monoComp_reduction (X : Type u) (j : ℕ) (Y : Set X) [Infinite (↥Y)]
    (hYX : Cardinal.mk (↥Y) < Cardinal.mk X) (hc : MonoComp X (j + 2) (j + 1)) :
    Nonempty (MonoComp (↥Y) (j + 1) j) := by
  -- CONSTRUCTION (route): let Z = ⋃_{t : Fin (j+1) → ↥Y} ↑(η (val ∘ t)) ⊆ X; by
  -- `mk_iUnion_reconstr_le` (codomain X), #Z ≤ #↥Y < #X, so pick x ∈ X \ Z. The (j+2)→(j+1)
  -- scheme on the tuple (j+1 pts of Y, then x) must drop x (else the kept j+1 lie in Y and
  -- η of them ⊆ Z ∋ x, contradiction). Define η_Y(R : Fin j → ↥Y) =
  -- (η (Fin.snoc (val ∘ R) x)).preimage Subtype.val, a Finset ↥Y; covers follows.
  sorry

/-- **Theorem 1, reverse direction (OPEN).** A `(k+2) → (k+1)` monotone compression scheme
forces `#X ≤ ℵ_k`. Assembled by downward induction from `monoComp_reduction`
(`(k+2)→(k+1) ⟹ (k+1)→k ⟹ ⋯ ⟹ 1→0`) terminated by `monoComp_one_zero_finite`
(a `1 → 0` scheme on an infinite set is impossible). -/
theorem card_le_aleph_of_monoComp (X : Type u) (k : ℕ)
    (h : Nonempty (MonoComp X (k + 2) (k + 1))) :
    Cardinal.mk X ≤ Cardinal.aleph (k : Ordinal) := by
  sorry

/-- **Theorem 1, forward direction (OPEN).** If `#X ≤ ℵ_k` then `Fᶠⁱⁿ_X` admits a
`(k+2) → (k+1)` monotone compression scheme. This is the choice-using construction: fix a
well-ordering of `X` of order type `≤ ω_k = (ℵ_k).ord` (`Cardinal.ord_aleph`) and compress
by recursively retaining the `≺`-maximal element and descending the aleph hierarchy, using
that the initial segment below a point of `ω_k` has cardinality `≤ ℵ_{k-1}` (`Ordinal.typein`,
`IsInitial`). The well-ordering of an arbitrary `X` of cardinality `ℵ_k` is the choice
artifact. -/
theorem monoComp_of_card_le_aleph (X : Type u) (k : ℕ)
    (h : Cardinal.mk X ≤ Cardinal.aleph (k : Ordinal)) :
    Nonempty (MonoComp X (k + 2) (k + 1)) := by
  sorry

/-- **Theorem 1** (Ben-David, Hrubeš, Moran, Shpilka, Yehudayoff, *Nature Machine
Intelligence* 2019): `Fᶠⁱⁿ_X` admits a `(k+2) → (k+1)` monotone compression scheme **iff**
`#X ≤ ℵ_k`. Composed with `#[0,1] ≤ ℵ_k` being a continuum-hypothesis variant, this is the
source of the ZFC-independence of EMX learnability. -/
theorem monoComp_iff_card_le_aleph (X : Type u) (k : ℕ) :
    Cardinal.mk X ≤ Cardinal.aleph (k : Ordinal) ↔ Nonempty (MonoComp X (k + 2) (k + 1)) :=
  ⟨monoComp_of_card_le_aleph X k, card_le_aleph_of_monoComp X k⟩

end FLT.Foundations.EMX
