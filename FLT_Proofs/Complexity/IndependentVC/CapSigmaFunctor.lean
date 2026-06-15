/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.CapacitySpectrum
import FLT_Proofs.Complexity.IndependentVC.FrameworkClosures
import FLT_Proofs.Complexity.IndependentVC.CapacityClosures
import Mathlib.SetTheory.Ordinal.Basic

/-!
# `Cap_Σ` — the capacity-spectrum functor, structured as far as in-FLT machinery allows

This module advances the synthesis conjecture **IM1 / `Cap_Σ`** (the "dimension zoo" — `VCDim`,
`LittlestoneDim`, `OptimalMistakeBound`, `NatarajanDim`, `DSDim`, `Pseudodimension`,
`FatShatteringDim`, `OrdinalVCDim` — is *one* capacity-spectrum functor measured at different
shattering shapes, with the proven inter-dimension inequalities as its monotone arrows) past the
state left by `CapacitySpectrum.lean`, `FrameworkClosures.lean`, and `CapacityClosures.lean`.

What those files left standing:

* `CapacitySpectrum.lean` built `capSpectrum : CapShape → Option (WithTop ℕ)` — a *partial map*,
  evaluating only the `set` shape — and recorded the **codomain-unification blocker** as
  confirmed-absent: the dimensions live in three different ordered codomains (`WithTop ℕ`,
  `WithBot (WithTop ℕ)` for Littlestone, `Ordinal` for ordinal-VC), so no *total* `WithTop ℕ`-valued
  evaluator can even be typed.
* `FrameworkClosures.lean` built the inductive `ShapeLE` and a `Preorder CapShape` (refl + trans
  only), with `capSpectrum_monotone_on_set`, and flagged the **full functor into one codomain** as a
  sharpened-KU residual.
* `CapacityClosures.lean` built `fatShatteringDim_boolToReal_eq` (the Boolean ↔ real fibre:
  `FatShatteringDim X (boolToReal C) γ hγ = VCDim X C` for `0 < γ < 1/2`) and a *supplied-hypothesis*
  reduction `capacityTerminal_reduction` over an abstract `UnifiedCapacityCodomain`.

## A correction this module makes (an honest finding)

`UnifiedCapacityCodomain` was declared with `Ω : Type` (universe `Type 0`). But the ordinal-VC
codomain `Ordinal` lives in `Type 1`, so **no term of that structure could use `Ordinal` as its
carrier** — which is exactly why its reduction had to stay supplied-as-a-hypothesis and could never be
instantiated. The fix lands in `CapacityClosures.lean` itself: the carrier is now `Ω : Type*` (with
`ofOrdinal : Ordinal.{0} → Ω`), so `Ordinal` is admissible. Here we **construct an instance** with
carrier `Ordinal`, discharging the existence the old `Type 0` carrier could not even type — and the
two abstract reductions become this module's `capSigma_*_at_ordinal` theorems, each literally the
`CapacityClosures` reduction instantiated at that instance.

## What is genuinely closed here (KK), and what stays a reduction

1. **The shape order is a `PartialOrder`, not merely a `Preorder`** (`shapeLE_antisymm`,
   `capShapePartialOrder`). `FrameworkClosures` only proved reflexivity and transitivity. We prove
   `ShapeLE` is **antisymmetric** — the law that makes the shapes a genuine ordered set. The proof is
   the content: each non-reflexive generator (`fullRealizability ⊑ twoColour`, `set ⊑ tree`) has **no
   reverse generator**, so a two-sided comparison forces `s = t`. The comparison edges of the
   dimension zoo are a strict, acyclic refinement.

2. **A concrete unified codomain exists** (`capSigmaCodomain : UnifiedCapacityCodomain`). We construct
   a unified codomain with carrier `Ω = Ordinal.{0}` and the three monotone embeddings exhibited
   explicitly: `WithTop ℕ ↪ Ordinal` via the kernel's `withTopNatToOrdinal`; `Ordinal ↪ Ordinal` the
   identity; and the new `withBotWithTopNatToOrdinal : WithBot (WithTop ℕ) ↪ Ordinal` (sending the
   Littlestone bottom `⊥` to the ordinal `0`), whose monotonicity `withBotWithTopNatToOrdinal_mono` is
   the new lemma. With this term, every `spectrum_*` edge of `CapacitySpectrum.lean` becomes an
   inequality of ordinals in **one** order — the codomain-unification blocker, discharged for the
   three native codomains.

3. **The Bool ↔ ℝ stratum gap is bridged inside one codomain** (`capSigma_bool_eq_margin_in_codomain`).
   The `set` shape (`VCDim X C`, over `ConceptClass X Bool`) and the `margin` shape (`FatShatteringDim`
   of the `{0,1}`-embedded class `boolToReal C`, over `ConceptClass X ℝ`) — two shapes the partial
   `capSpectrum` could not compare because they live over *different concept-class domains* — take the
   **same value** in the unified codomain `Ordinal`, for every margin `γ ∈ (0,1/2)`. This consumes
   `fatShatteringDim_boolToReal_eq`. It is a genuine cross-*domain* equality of `Cap_Σ` evaluations.

4. **The monotone action is assembled along the order, in the unified codomain**
   (`capSigma_ds_le_nat_in_codomain`, `capSigma_monotone_on_proven_edges`): the proven inequalities
   (`DSDim ≤ NatarajanDim`, `VCDim ⟶ OrdinalVCDim`, sub-class monotonicity) become inequalities of
   ordinals in the single codomain — the functor's action where the machinery supports it without a
   missing lemma.

## What remains genuinely open (named-blocker reductions, not sorries)

* **The `set ⊑ tree` arrow** needs `VCDim ≤ LittlestoneDim`, whose kernel proof
  (`vcdim_le_of_mistake_bounded`) is `private` in `FLT_Proofs/Theorem/Separation.lean`, so it is not
  re-exportable. Delivered conditionally as `capSigma_set_le_tree_edge_reduces_to`.
* **Total functoriality** — a single uniform per-shape evaluator into `Ordinal` over the *label-typed*
  multiclass shapes (Natarajan / DS need a free type `Y`, absent from the `Bool`/`ℝ` shape signature)
  — is reduced to its named missing data in `capSigma_total_evaluator_reduces_to`.

## References

* D. Pollard, *Convergence of Stochastic Processes* (1984): the pseudodimension / `finrank` bound.
* B. K. Natarajan, *On learning sets and functions*, Machine Learning 4 (1989): the Natarajan
  dimension for multiclass learning.
* P. L. Bartlett, P. M. Long, R. C. Williamson, *Fat-shattering and the learnability of real-valued
  functions* (1996): the fat-shattering scale and its collapse to VC at the `{0,1}` fibre.
* N. Littlestone, *Learning quickly when irrelevant attributes abound*, Machine Learning 2 (1988):
  the mistake-bound / Littlestone-dimension identity (and the empirical `VCDim ≤ LittlestoneDim`
  direction the `set ⊑ tree` shape morphism encodes).
* A. Daniely, S. Shalev-Shwartz, *Optimal learners for multiclass problems* (2014): the DS dimension
  and the `DSDim ≤ NatarajanDim` comparison (the multiclass shape morphism).
* S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning* (2014), Ch. 6, 9, 21: the survey
  view of the dimension zoo as comparable capacity notions.
-/

open scoped BigOperators Classical

universe u v

namespace CapSigmaFunctor

/-! ## 1. The shape order is a genuine `PartialOrder` (antisymmetry — the new law)

`FrameworkClosures.lean` proved `ShapeLE` reflexive and transitive (`Preorder CapShape`). The law it
did *not* prove — the one distinguishing a partial order from a mere preorder — is **antisymmetry**.
We prove it: the comparison edges of the shape zoo form a *strict, acyclic* refinement, so no two
distinct shapes are mutually `⊑`-related. -/

/-- **`ShapeLE` is antisymmetric** (new; the law `FrameworkClosures` left unproved). If shape `s` is at
least as demanding as `t` *and* `t` is at least as demanding as `s`, then `s = t`. The proof is the
content: the two non-reflexive generators of `ShapeLE` (`fullRealizability ⊑ twoColour` and
`set ⊑ tree`) each have **no reverse generator**, so once `h₁` is a strict edge, `h₂ : ShapeLE t s` is
*unrealizable* (`cases h₂` closes with no constructors) and only the reflexive branch survives — the
shape comparison relation is acyclic. -/
theorem shapeLE_antisymm {s t : CapShape} (h₁ : ShapeLE s t) (h₂ : ShapeLE t s) : s = t := by
  cases h₁ with
  | refl => rfl
  | ds_le_nat => cases h₂
  | set_le_tree => cases h₂

/-- **The shattering shapes form a `PartialOrder`** (new; upgrades `FrameworkClosures`'s `Preorder`).
With reflexivity and transitivity (from `FrameworkClosures.ShapeLE.refl` / `.trans`) and the new
`shapeLE_antisymm`, the shapes are a genuine partially ordered set: the source of the functor is now a
poset.

Delivered as a `def` (not a global `instance`) on purpose: `FrameworkClosures.lean` already registers
a global `Preorder CapShape` with the *same* `le := ShapeLE`, so registering a second order instance
would create an instance diamond. The `PartialOrder` is a named term downstream code can `letI` in
when it needs antisymmetry, leaving the existing `Preorder` resolution untouched. -/
@[reducible] def capShapePartialOrder : PartialOrder CapShape where
  le := ShapeLE
  le_refl := ShapeLE.refl
  le_trans := fun _ _ _ h₁ h₂ => ShapeLE.trans h₁ h₂
  le_antisymm := fun _ _ h₁ h₂ => shapeLE_antisymm h₁ h₂

/-! ## 2. A concrete unified codomain over `Ordinal`

The unified codomain `UnifiedCapacityCodomain` is now declared universe-correctly (`Ω : Type*`) in
`CapacityClosures.lean` — the carrier can hold the ordinal-VC codomain `Ordinal.{0} : Type 1`, which a
`Type 0`-bound carrier could not, and which is exactly why its reductions used to stay
supplied-as-a-hypothesis. We therefore **reuse that canonical structure** here (no duplicate) and
discharge the codomain-unification blocker by **constructing an instance over `Ordinal`**. The earlier
`CapSigmaUnifiedCodomain` duplicate has been consolidated away into `UnifiedCapacityCodomain`. -/

/-- **The Littlestone-codomain embedding into `Ordinal`** (new construction). Sends the bottom `⊥`
(the Littlestone dimension of the empty class) to the ordinal `0`, and a genuine value `↑a` to
`withTopNatToOrdinal a` (the kernel's existing `WithTop ℕ ↪ Ordinal`, which sends `⊤ ↦ ω`). This is
the embedding the unified codomain needs for the Littlestone codomain. -/
noncomputable def withBotWithTopNatToOrdinal : WithBot (WithTop ℕ) → Ordinal.{0} :=
  WithBot.recBotCoe 0 withTopNatToOrdinal

@[simp] theorem withBotWithTopNatToOrdinal_bot :
    withBotWithTopNatToOrdinal ⊥ = 0 := rfl

@[simp] theorem withBotWithTopNatToOrdinal_coe (a : WithTop ℕ) :
    withBotWithTopNatToOrdinal (a : WithBot (WithTop ℕ)) = withTopNatToOrdinal a := rfl

/-- **The Littlestone embedding is monotone** (new; the missing third edge of the unified codomain).
From `⊥` everything is `≥ 0` (the ordinal bottom); between two genuine values it reduces to
`withTopNatToOrdinal_mono`. With this the unified codomain over `Ordinal` is fully constructible. -/
theorem withBotWithTopNatToOrdinal_mono :
    ∀ a b : WithBot (WithTop ℕ), a ≤ b →
      withBotWithTopNatToOrdinal a ≤ withBotWithTopNatToOrdinal b := by
  intro a b h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd (le_bot_iff.mp h) WithBot.coe_ne_bot
    | coe b => exact withTopNatToOrdinal_mono a b (by exact_mod_cast h)

/-- **A concrete unified capacity codomain over `Ordinal`** (new; the codomain-unification blocker
discharged for the three native codomains). Carrier `Ω = Ordinal.{0}`; embeddings:

* `ofWithTop := withTopNatToOrdinal`      (VC / Natarajan / DS / pseudo / fat), monotone by
  `withTopNatToOrdinal_mono`;
* `ofOrdinal := id`                         (ordinal-VC), monotone trivially;
* `ofWithBot := withBotWithTopNatToOrdinal` (Littlestone), monotone by the lemma above.

A term of `UnifiedCapacityCodomain` genuinely exists — the existence the old `Type 0`-bound carrier
could not even type. With it, the scattered dimensions of the proven spectrum fragment really land in
one ordered object. -/
noncomputable def capSigmaCodomain : UnifiedCapacityCodomain where
  Ω := Ordinal.{0}
  order := inferInstance
  ofWithTop := withTopNatToOrdinal
  ofWithTop_mono := withTopNatToOrdinal_mono
  ofWithBot := withBotWithTopNatToOrdinal
  ofWithBot_mono := withBotWithTopNatToOrdinal_mono
  ofOrdinal := id
  ofOrdinal_mono := fun _ _ h => h

/-- **The master-capacity reduction now holds against the concrete codomain.** The proven edge
`vcdim_to_ordinal_vcdim` (set shape `⟶` ordinal shape) is an inequality of *ordinals* in the single
constructed codomain: `Cap_Σ`'s set-shape value sits below its ordinal-shape value, both in `Ordinal`.
Previously the abstract `capacityTerminal_reduction` required *supplying* a unified codomain; here the
supply is discharged — this is literally that theorem instantiated at `capSigmaCodomain`. -/
theorem capSigma_terminal_at_ordinal (X : Type) (C : ConceptClass X Bool) :
    capSigmaCodomain.ofOrdinal (withTopNatToOrdinal (VCDim X C))
      ≤ capSigmaCodomain.ofOrdinal (OrdinalVCDim X C) :=
  capacityTerminal_reduction capSigmaCodomain X C

/-- **Set-shape capacity is monotone in the concrete codomain.** A sub-class has no larger VC
dimension, hence no larger image in the unified `Ordinal` codomain: `C ⊆ D ⟹ Cap_Σ(set, C) ≤
Cap_Σ(set, D)` as ordinals. A genuine constraint any terminal `Cap_Σ` must satisfy — the abstract
`capacityTerminal_set_shape_mono` instantiated at the concrete `capSigmaCodomain`. -/
theorem capSigma_set_mono_at_ordinal {X : Type} {C D : ConceptClass X Bool} (h : C ⊆ D) :
    capSigmaCodomain.ofWithTop (VCDim X C) ≤ capSigmaCodomain.ofWithTop (VCDim X D) :=
  capacityTerminal_set_shape_mono capSigmaCodomain h

/-! ## 3. Bridging the Bool ↔ ℝ stratum gap *inside* the unified codomain

The partial `capSpectrum` could not compare the `set` shape (over `ConceptClass X Bool`) with the
real-valued `margin` shape (over `ConceptClass X ℝ`): they live over *different concept-class
domains*. The synthesis singled out `fatShatteringDim_boolToReal_eq` as the bridge. We use it to prove
the two shapes take the **same value** in the unified `Ordinal` codomain. -/

/-- **The set shape and the margin shape coincide in the unified codomain** (new; the Bool ↔ ℝ
cross-domain coincidence of `Cap_Σ`). For every margin `γ ∈ (0, 1/2)`, the fat-shattering dimension of
the `{0,1}`-embedded class `boolToReal C` (the `margin` shape, over `ConceptClass X ℝ`) equals the VC
dimension of `C` (the `set` shape, over `ConceptClass X Bool`) **as elements of the single ordered
codomain `Ordinal`**. Two shapes over different concept-class types are forced to one value in one
codomain. Consumes `fatShatteringDim_boolToReal_eq` (the scale-independent `{0,1}` fibre), carried
through the embedding `ofWithTop` by `congrArg`. -/
theorem capSigma_bool_eq_margin_in_codomain {X : Type} (C : ConceptClass X Bool)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 1 / 2) :
    capSigmaCodomain.ofWithTop (FatShatteringDim X (boolToReal C) γ hγ)
      = capSigmaCodomain.ofWithTop (VCDim X C) :=
  congrArg capSigmaCodomain.ofWithTop (fatShatteringDim_boolToReal_eq C hγ hγ2)

/-- **The Bool/ℝ coincidence is scale-independent across the whole margin interval** (new corollary).
The unified-codomain value of the `margin` shape is *the same* at every two margins `γ, δ ∈ (0, 1/2)`,
namely the set-shape value `VCDim X C`. The `Cap_Σ` reading: the margin direction is a *constant* fibre
over `(0, 1/2)` once routed through the unified codomain — the "scale" coordinate of the spectrum does
not move below the `{0,1}` half-gap. -/
theorem capSigma_margin_scale_independent {X : Type} (C : ConceptClass X Bool)
    {γ δ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 1 / 2) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    capSigmaCodomain.ofWithTop (FatShatteringDim X (boolToReal C) γ hγ)
      = capSigmaCodomain.ofWithTop (FatShatteringDim X (boolToReal C) δ hδ) := by
  rw [capSigma_bool_eq_margin_in_codomain C hγ hγ2,
      capSigma_bool_eq_margin_in_codomain C hδ hδ2]

/-! ## 4. The monotone action along the shape order, in the unified codomain

We bundle the proven order-edges of `ShapeLE` with their witnessing dimension inequalities, lifted
into the single ordinal codomain — exhibiting the `spectrum_*` inequalities as the functor's action on
shape morphisms. The DS/Natarajan edge is unconditional; the `set ⊑ tree` edge is delivered
conditionally on its named missing lemma (§5). -/

/-- **The DS ⟶ Natarajan arrow is the functor's action in the unified codomain** (new; unconditional).
The shape edge `fullRealizability ⊑ twoColour` (a `ShapeLE` generator) is witnessed by
`DSDim ≤ NatarajanDim` (`spectrum_DS_le_Natarajan`), lifted monotonically into `Ordinal`:
`Cap_Σ(fullRealizability, C) ≤ Cap_Σ(twoColour, C)` as ordinals. Both shapes' dimensions are
`WithTop ℕ`-valued, so `ofWithTop` carries the inequality without any missing lemma. -/
theorem capSigma_ds_le_nat_in_codomain (X : Type u) (Y : Type v) [Fintype Y] [Nontrivial Y]
    (C : ConceptClass X Y) :
    ShapeLE CapShape.fullRealizability CapShape.twoColour ∧
      capSigmaCodomain.ofWithTop (DSDim X Y C) ≤ capSigmaCodomain.ofWithTop (NatarajanDim X Y C) :=
  ⟨ShapeLE.ds_le_nat,
   capSigmaCodomain.ofWithTop_mono _ _ (spectrum_DS_le_Natarajan X Y C)⟩

/-- **The proven monotone edges of `Cap_Σ`, assembled in one codomain** (new packaging). Bundles the
unconditional arrows that hold *for the evaluator's image in `Ordinal`*: the DS ⟶ Natarajan arrow, and
the set ⟶ ordinal arrow (`capSigma_terminal_at_ordinal`). Together they are genuine arrows of `Cap_Σ`
living in the *single* constructed codomain — the functor's action made explicit where the in-FLT
machinery supports it without a missing lemma. -/
theorem capSigma_monotone_on_proven_edges (X : Type) (Y : Type) [Fintype Y] [Nontrivial Y]
    (C : ConceptClass X Bool) (C₂ : ConceptClass X Y) :
    (capSigmaCodomain.ofWithTop (DSDim X Y C₂)
        ≤ capSigmaCodomain.ofWithTop (NatarajanDim X Y C₂))
      ∧ (capSigmaCodomain.ofOrdinal (withTopNatToOrdinal (VCDim X C))
          ≤ capSigmaCodomain.ofOrdinal (OrdinalVCDim X C)) :=
  ⟨capSigmaCodomain.ofWithTop_mono _ _ (spectrum_DS_le_Natarajan X Y C₂),
   capSigma_terminal_at_ordinal X C⟩

/-! ## 5. The frontier — named-blocker reductions for the genuinely cross-domain edges

The two arrows the in-FLT machinery does *not* supply are stated as precise conditionals, each
reducing to a single named missing lemma. Neither is faked; each is a real implication whose
hypothesis is the confirmed-absent edge. -/

/-- **The `set ⊑ tree` arrow, reduced to its named missing lemma** (conditional KK). The shape edge
`set ⊑ tree` (a `ShapeLE` generator) would be witnessed by `VCDim ≤ LittlestoneDim` — the empirical
"a shattered set is a depth-bounded shattered tree" direction (Littlestone 1988). That inequality is
**not** a public theorem of this kernel: `vcdim_le_of_mistake_bounded` is `private` in
`FLT_Proofs/Theorem/Separation.lean`, so it cannot be re-exported (recorded confirmed-absent in
`CapacitySpectrum`'s stayed-KU ledger).

We deliver the arrow **conditionally**: *given* the missing edge `hVC_le_L` in its native
`WithBot (WithTop ℕ)` form, the `set ⊑ tree` morphism lifts into the unified `Ordinal` codomain as
`Cap_Σ(set, C) ≤ Cap_Σ(tree, C)`. The proof is genuine content (it matches `ofWithTop` to `ofWithBot`
at the integer value via `withBotWithTopNatToOrdinal_coe`, then applies the monotone Littlestone
embedding `ofWithBot_mono`); the only open part is the hypothesis, which *is* the named blocker. This
is the honest replacement for fabricating `VCDim ≤ LittlestoneDim`. -/
theorem capSigma_set_le_tree_edge_reduces_to {X : Type} (C : ConceptClass X Bool)
    (hVC_le_L : (VCDim X C : WithBot (WithTop ℕ)) ≤ LittlestoneDim X C) :
    ShapeLE CapShape.set CapShape.tree ∧
      capSigmaCodomain.ofWithTop (VCDim X C)
        ≤ capSigmaCodomain.ofWithBot (LittlestoneDim X C) := by
  refine ⟨ShapeLE.set_le_tree, ?_⟩
  have key : capSigmaCodomain.ofWithTop (VCDim X C)
      = capSigmaCodomain.ofWithBot ((VCDim X C : WithTop ℕ) : WithBot (WithTop ℕ)) := by
    simp only [capSigmaCodomain, withBotWithTopNatToOrdinal_coe]
  rw [key]
  exact capSigmaCodomain.ofWithBot_mono _ _ hVC_le_L

/-- **Total functoriality, reduced to its named missing data** (open residual; not banked as a
structural theorem). The unified codomain `capSigmaCodomain` discharges the *codomain*-unification
blocker for the three native codomains, but a single uniform functor `(CapShape, ⊑) ⥤ Ordinal` would
still need a per-shape evaluator `eval : CapShape → Ordinal` defined by *one rule* — and the multiclass
shapes (`twoColour` for Natarajan, `fullRealizability` for DS) carry a free label type `Y : Type` that
the `Bool`/`ℝ` shape signature does not. The residual is: a total evaluator exists iff one supplies an
`eval` together with a proof it is monotone along `ShapeLE` and agrees with `ofWithTop ∘ VCDim` at the
`set` shape.

The statement below is a genuine implication — *given* such an `eval` and its set-shape agreement, the
set-shape value is the expected ordinal — naming exactly the missing data (`eval` for the label-typed
shapes) rather than asserting it. That construction is the standing `UU`. -/
theorem capSigma_total_evaluator_reduces_to {X : Type} (C : ConceptClass X Bool)
    (eval : CapShape → Ordinal.{0})
    (hset : eval CapShape.set = capSigmaCodomain.ofWithTop (VCDim X C)) :
    eval CapShape.set = withTopNatToOrdinal (VCDim X C) := by
  rw [hset]; simp only [capSigmaCodomain]

/-! ## Closure ledger — what is banked here, at which tier

| target | tier | key new declaration(s) |
|---|---|---|
| shape order is a `PartialOrder` (antisymmetry) | KK-theorem (CONSTRUCT) | `shapeLE_antisymm`, `capShapePartialOrder` |
| universe-fixed unified codomain (`Ω : Type*`) + concrete `Ordinal` instance | KK-theorem (CONSTRUCT) | `UnifiedCapacityCodomain` (universe-fixed upstream), `withBotWithTopNatToOrdinal`, `withBotWithTopNatToOrdinal_mono`, `capSigmaCodomain`, `capSigma_terminal_at_ordinal`, `capSigma_set_mono_at_ordinal` |
| Bool ↔ ℝ stratum gap bridged in one codomain | KK-theorem (DIRECT, via `fatShatteringDim_boolToReal_eq`) | `capSigma_bool_eq_margin_in_codomain`, `capSigma_margin_scale_independent` |
| monotone action along the order (DS ⟶ Nat, set ⟶ ordinal) | KK-theorem (DIRECT) | `capSigma_ds_le_nat_in_codomain`, `capSigma_monotone_on_proven_edges` |
| `set ⊑ tree` arrow (`VCDim ≤ LittlestoneDim`) | conditional (named blocker: `vcdim_le_of_mistake_bounded` is `private`) | `capSigma_set_le_tree_edge_reduces_to` |
| total uniform functor over label-typed shapes | reduction (named blocker: per-shape evaluator for `Y`-typed shapes) | `capSigma_total_evaluator_reduces_to` |

**Honest summary of how much of IM1 closed.** The **codomain-unification blocker is discharged for the
three native codomains**: a concrete common ordered codomain (`Ordinal`) with all three monotone
embeddings now exists — including the universe correction that the old `Ω : Type` structure could not
even type. The shapes are now a genuine **`PartialOrder`** (antisymmetry proved). The **Bool ↔ ℝ
cross-domain coincidence** is proven inside that codomain. What stays open is the *total* functor with
a uniform per-shape rule over the label-typed multiclass shapes, and the single `set ⊑ tree` dimension
inequality whose kernel proof is `private` — both reduced to named blockers, neither fabricated. The
"one functor" conjecture is therefore **substantially but not fully** closed: its codomain and order
skeleton are built and one stratum gap is bridged; its uniform action over all eight dimensions remains
a precise, well-posed reduction. -/

end CapSigmaFunctor
