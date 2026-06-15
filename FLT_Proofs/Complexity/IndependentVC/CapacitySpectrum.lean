/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.Pseudodimension
import FLT_Proofs.Complexity.Structures
import FLT_Proofs.Theorem.Online
import FLT_Proofs.Bridge

/-!
# `Cap_Σ` — the capacity spectrum, a proven fragment

This module collects, under one roof and one ordering, the *kernel-verified* relations between the
many capacity dimensions of a concept class (VC, Littlestone, Natarajan, DS/strong-shattering,
pseudodimension, fat-shattering, ordinal-VC, optimal-mistake-bound). The noological synthesis
(`design-lab/learning-theory/flt_discovery_urs/noological_synthesis.md`, GR2 / IM1) conjectures that
these dimensions are not eleven unrelated functionals but **one functor `Cap_Σ` measured at different
"shattering shapes"**: sets (VC), trees (Littlestone), two-colour witnesses (Natarajan),
full-realizability witnesses (DS), thresholds (pseudodimension), margins (fat-shattering), ordinals
(ordinal-VC). On this reading the scattered comparison lemmas are not ad-hoc inequalities — they are
the *functorial action of `Cap_Σ` along morphisms of shapes* (a finer shape forces a smaller
dimension; a coarser scale forces a larger one).

## What this module is, honestly

The functor `Cap_Σ` itself — an honest index category of shapes with a functor into a single ordered
codomain — is **not** built here and is **not** banked as a theorem. It is the synthesis's CONJECTURE
(IM1), and it is recorded as such in the "stayed KU" ledger of this module's docstring. What *is*
banked here is a small **ordered fragment** of that hoped-for spectrum: the inter-dimension relations
that already have `sorry`-free proofs in the kernel, re-stated under `spectrum_*` names with a
docstring pointing back to the anchor and to the shape morphism it would witness. Re-stating a proved
theorem under a new name is `describe`, not new mathematics, and every `spectrum_*` edge below says
so. The only construction is the minimal `Shape` enum and the partial evaluator `capSpectrum`
(item 2 below), which recovers `VCDim` at the `set` shape *definitionally* — a naming convenience,
not a theorem.

The honest obstruction to a *total* functor is recorded in the code: the eight dimensions do not even
share a codomain (`LittlestoneDim : WithBot (WithTop ℕ)`, `OrdinalVCDim : Ordinal`, the rest
`WithTop ℕ`, the real-valued ones live over `ConceptClass X ℝ` not `ConceptClass X Bool`). A single
total `Cap_Σ` would first have to *unify the codomain*, which is itself open. So `capSpectrum` is
deliberately partial: it ranges only over the `WithTop ℕ`-valued, `Bool`-domain shapes, and the
cross-codomain edges (VC↪OrdinalVC, OMB=Littlestone) are kept as standalone `spectrum_*` re-exports
with their native coercions rather than forced through one evaluator.

## The proven edges (the fragment that builds)

| edge (`spectrum_*`)            | anchor theorem                | shape morphism it witnesses          |
| ------------------------------ | ----------------------------- | ------------------------------------ |
| `spectrum_DS_le_Natarajan`     | `DSDim_le_NatarajanDim`       | full-realizability ⟶ two-colour      |
| `spectrum_fat_le_pseudo`       | `fatShatteringDim_le_pseudodim` | margin-`γ` ⟶ threshold              |
| `spectrum_fat_le_pseudo_dimle` | `fatShatteringDim_le` + `pseudodim_le` | both ⟶ linear `finrank+1`   |
| `spectrum_vc_le_finrank`       | `vcDim_signClass_le`          | set-shape on a linear sign class     |
| `spectrum_vc_to_ordinal`       | `vcdim_to_ordinal_vcdim`      | set ⟶ ordinal (codomain lift)        |
| `spectrum_omb_eq_littlestone`  | `optimal_mistake_bound_eq_ldim` | mistake-game = tree-shape          |
| `spectrum_online_iff_littlestone_finite` | `littlestone_characterization` | tree-shape `Inv` boundary  |

## References

* D. Pollard, *Convergence of Stochastic Processes* (1984): the linear-algebra (`finrank`)
  pseudodimension / sign-class bound.
* B. K. Natarajan, *On learning sets and functions*, Machine Learning 4 (1989): the Natarajan
  dimension and its role for multiclass learning.
* P. L. Bartlett, P. M. Long, R. C. Williamson, *Fat-shattering and the learnability of real-valued
  functions* (1996): the fat-shattering ↔ pseudodimension scale.
* N. Littlestone, *Learning quickly when irrelevant attributes abound*, Machine Learning 2 (1988):
  the mistake-bound / Littlestone-dimension identity for online learning.
-/

open scoped BigOperators

universe u v

/-! ## 1. The proven edges of `Cap_Σ` (a small ordered fragment; all re-exports)

Each declaration below is **definitionally** an existing kernel theorem, surfaced under a
`spectrum_*` name. None is a new theorem. The docstrings record which shape morphism the edge would
be the action of, *if* the full `Cap_Σ` functor (IM1, conjectural) were built. -/

/-- **`Cap_Σ` edge — full-realizability `⟶` two-colour (multiclass shapes)** (re-export of
`DSDim_le_NatarajanDim`). DS-shattering asks that *every* labelling of the sample be realizable;
Natarajan-shattering asks only for a two-colour witness. The DS condition is strictly stronger, so
fewer sets satisfy it, and the dimension it produces is no larger:

  `DSDim X Y C ≤ NatarajanDim X Y C`  (for `|Y| ≥ 2`).

This is the action of `Cap_Σ` along the shape morphism "drop from full realizability to a two-colour
witness" — a coarser shattering shape can only raise the dimension. Re-export, not a new theorem. -/
theorem spectrum_DS_le_Natarajan (X : Type u) (Y : Type v) [Fintype Y] [Nontrivial Y]
    (C : ConceptClass X Y) : DSDim X Y C ≤ NatarajanDim X Y C :=
  DSDim_le_NatarajanDim X Y C

/-- **`Cap_Σ` edge — margin-`γ` `⟶` threshold (real-valued scale)** (re-export of
`fatShatteringDim_le_pseudodim`). A `γ`-fat-shattered configuration satisfies the pseudo-shattering
conditions with the same sample and thresholds (a strict `γ`-margin implies the non-strict threshold
crossing), so at every scale `γ > 0`:

  `FatShatteringDim X C γ hγ ≤ Pseudodimension X C`.

This is the action of `Cap_Σ` along the scale morphism "forget the margin `γ`" — a coarser scale can
only raise the dimension. Re-export, not a new theorem. -/
theorem spectrum_fat_le_pseudo {X : Type u} (C : ConceptClass X ℝ) {γ : ℝ} (hγ : 0 < γ) :
    FatShatteringDim X C γ hγ ≤ Pseudodimension X C :=
  fatShatteringDim_le_pseudodim C hγ

/-- **`Cap_Σ` edge — set-shape on a linear sign class** (re-export of `vcDim_signClass_le`,
Pollard 1984). For a finite-dimensional space of real functions `V`, the VC dimension of its linear
sign class is bounded by the linear dimension:

  `VCDim X (signClass V) ≤ finrank ℝ V`.

The "set" shape (VC) of a linearly-parametrised class is pinned by the parameter count. Re-export,
not a new theorem. -/
theorem spectrum_vc_le_finrank {X : Type u} (V : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ V] :
    VCDim X (signClass V) ≤ (Module.finrank ℝ V : WithTop ℕ) :=
  vcDim_signClass_le V

/-- **`Cap_Σ` edge — both real-valued shapes meet at the linear dimension** (re-export of
`fatShatteringDim_le` and `pseudodim_le`, Pollard 1984 / Haussler 1992). For a finite-dimensional
space `V`, both the pseudodimension and the fat-shattering dimension at every scale are bounded by
`finrank ℝ V + 1`:

  `Pseudodimension X ↑V ≤ finrank ℝ V + 1`  and  `FatShatteringDim X ↑V γ hγ ≤ finrank ℝ V + 1`.

This packages the two anchors as one statement: the threshold and margin shapes both collapse to the
same linear ceiling on a linear class — a common value of `Cap_Σ` at a linear object. The conjunction
restates two proved theorems; it is not new mathematics. -/
theorem spectrum_real_dims_le_finrank {X : Type u} (V : Submodule ℝ (X → ℝ))
    [FiniteDimensional ℝ V] {γ : ℝ} (hγ : 0 < γ) :
    Pseudodimension X ((↑V : Set (X → ℝ)) : ConceptClass X ℝ) ≤ (Module.finrank ℝ V + 1 : WithTop ℕ)
      ∧ FatShatteringDim X ((↑V : Set (X → ℝ)) : ConceptClass X ℝ) γ hγ
          ≤ (Module.finrank ℝ V + 1 : WithTop ℕ) :=
  ⟨pseudodim_le V, fatShatteringDim_le V hγ⟩

/-- **`Cap_Σ` edge — set-shape `⟶` ordinal-shape (codomain lift)** (re-export of
`vcdim_to_ordinal_vcdim`). The (finite or `⊤`) VC dimension embeds into the ordinal-valued VC
dimension via `withTopNatToOrdinal` (sending `⊤ ↦ ω`):

  `withTopNatToOrdinal (VCDim X C) ≤ OrdinalVCDim X C`.

This is `Cap_Σ` changing *codomain* — measuring the same set-shape over `Ordinal` rather than over
`WithTop ℕ`. It is kept as a standalone edge (rather than routed through the partial `capSpectrum`
evaluator below) precisely because it crosses codomains. Re-export, not a new theorem. -/
theorem spectrum_vc_to_ordinal (X : Type u) (C : ConceptClass X Bool) :
    withTopNatToOrdinal (VCDim X C) ≤ OrdinalVCDim X C :=
  vcdim_to_ordinal_vcdim X C

/-- **`Cap_Σ` edge — mistake-game equals the tree-shape** (re-export of
`optimal_mistake_bound_eq_ldim`, Littlestone 1988). For a nonempty class the optimal worst-case
mistake bound of online learning equals the Littlestone (tree-shattering) dimension:

  `↑(OptimalMistakeBound X C) = LittlestoneDim X C`.

This is the one *equality* in the fragment: the operational "mistake-game" shape and the
combinatorial "shattered tree" shape are the *same* value of `Cap_Σ`, not merely comparable. The
coercion lifts `OptimalMistakeBound : WithTop ℕ` into `LittlestoneDim`'s codomain
`WithBot (WithTop ℕ)`. Re-export, not a new theorem. -/
theorem spectrum_omb_eq_littlestone (X : Type) (C : ConceptClass X Bool) (hne : C.Nonempty) :
    (↑(OptimalMistakeBound X C) : WithBot (WithTop ℕ)) = LittlestoneDim X C :=
  optimal_mistake_bound_eq_ldim X C hne

/-- **`Cap_Σ` edge — the tree-shape `Inv` boundary is online learnability** (re-export of
`littlestone_characterization`, Littlestone 1988). The finite-vs-`⊤` dividing line of the
tree-shattering shape *is* online learnability:

  `OnlineLearnable X Bool C ↔ LittlestoneDim X C < ⊤`.

This is the tree-shape analogue of the VC fundamental theorem (`VCDim < ⊤ ↔ PAC-learnable`): the
`Inv` coordinate read at the Littlestone shape recovers the online-learnability dichotomy. Re-export,
not a new theorem. -/
theorem spectrum_online_iff_littlestone_finite (X : Type) (C : ConceptClass X Bool) :
    OnlineLearnable X Bool C ↔ LittlestoneDim X C < ⊤ :=
  littlestone_characterization X C

/-! ## 2. A minimal spectrum interface — shapes and a partial evaluator

A small enumeration of the `WithTop ℕ`-valued, `Bool`-domain shattering shapes, and a partial
evaluator `capSpectrum` from shapes to capacities. This is the *honest* sliver of the conjectural
`Cap_Σ` functor: it is a plain function (no functoriality claimed), and it covers only the shapes
that genuinely share the codomain `WithTop ℕ` over a fixed `ConceptClass X Bool`.

* The Littlestone tree-shape is **excluded** from this evaluator: `LittlestoneDim` lives in
  `WithBot (WithTop ℕ)` and requires `X : Type` (not `Type u`). Its relation to the rest is recorded
  separately by `spectrum_omb_eq_littlestone` (an exact identity with `OptimalMistakeBound`) and
  `spectrum_online_iff_littlestone_finite`.
* The ordinal shape is **excluded**: `OrdinalVCDim : Ordinal`. Its relation is
  `spectrum_vc_to_ordinal`.
* The real-valued shapes (pseudo, fat) live over `ConceptClass X ℝ`, a different object, and are
  related by `spectrum_fat_le_pseudo` / `spectrum_real_dims_le_finrank`.

So the evaluator below recovers exactly the **set shape** as `VCDim`. The point of the interface is
the *typed acknowledgement* that "VC is `Cap_Σ` at the set shape" — the one evaluation the synthesis
(GR2) says must hold — together with a precise, honest statement of which shapes do *not* yet fit one
evaluator (the open codomain-unification problem, recorded as stayed-KU). -/

/-- The shattering **shapes** that share the codomain `WithTop ℕ` over a Boolean concept class.
Only `set` is wired into the partial evaluator `capSpectrum`; the other constructors are recorded as
*named placeholders* for shapes whose dimension is measured in a different codomain or over a
different domain (see the `capSpectrum` docstring), so that the interface states the open
codomain-unification problem rather than hiding it. -/
inductive CapShape where
  /-- The **set** shape: ordinary VC shattering of a finite subset of the domain. -/
  | set : CapShape
  /-- The **two-colour** shape (Natarajan). Placeholder: needs a finite label type `Y`, so it is not
  evaluated by the `Bool`-only `capSpectrum`. -/
  | twoColour : CapShape
  /-- The **full-realizability** shape (DS / strong shattering). Placeholder: also needs `Y`. -/
  | fullRealizability : CapShape
  /-- The **tree** shape (Littlestone). Placeholder: codomain is `WithBot (WithTop ℕ)`. -/
  | tree : CapShape
  /-- The **ordinal** shape (ordinal-VC). Placeholder: codomain is `Ordinal`. -/
  | ordinal : CapShape
  deriving DecidableEq, Repr

/-- The **partial capacity spectrum**: the evaluation of (the proven sliver of) `Cap_Σ` at the shapes
that share the `WithTop ℕ` codomain over a fixed `Bool`-valued class. Only the `set` shape is wired
to its capacity (`VCDim`); the other shapes return `none`, marking that they do *not* yet fit a single
`WithTop ℕ`-valued evaluator — the codomain-unification problem the full functor would have to solve
(this is the synthesis's open IM1, recorded as stayed-KU, not faked here).

`Option` is used deliberately: `none` is the typed statement "this shape's dimension is measured
elsewhere (different codomain or domain)", not a defaulted-to-zero placeholder. -/
noncomputable def capSpectrum {X : Type u} (C : ConceptClass X Bool) : CapShape → Option (WithTop ℕ)
  | .set => some (VCDim X C)
  | _ => none

/-- **The one evaluation that must hold** (`describe`, definitional). `Cap_Σ` at the set shape *is*
the VC dimension: `capSpectrum C set = some (VCDim X C)`. This is the typed form of the synthesis's
requirement (GR2) that the spectrum recover VC at the set shape; it holds by definition of
`capSpectrum`, so it is a naming convenience, not a theorem. -/
@[simp] theorem capSpectrum_set {X : Type u} (C : ConceptClass X Bool) :
    capSpectrum C CapShape.set = some (VCDim X C) :=
  rfl

/-- The placeholder shapes are not wired to the `WithTop ℕ` evaluator (`describe`, definitional):
their dimension is measured in a different codomain or over a different domain, recorded by the
standalone `spectrum_*` edges above. This lemma makes the partiality explicit rather than implicit. -/
@[simp] theorem capSpectrum_eq_none_of_ne_set {X : Type u} (C : ConceptClass X Bool)
    {s : CapShape} (hs : s ≠ CapShape.set) : capSpectrum C s = none := by
  cases s with
  | set => exact absurd rfl hs
  | twoColour => rfl
  | fullRealizability => rfl
  | tree => rfl
  | ordinal => rfl

/-! ## 3. `stayedKU` — what is NOT banked (the open functor, recorded honestly)

The following remain **conjectures (KU)**, deliberately *not* proved here, because the proof material
does not exist in the kernel and manufacturing it would violate the honesty discipline. They are the
synthesis's GR2 / IM1, sharpened by what this module's fragment makes visible:

1. **The functor `Cap_Σ` itself.** A genuine functor from an index category of *shattering shapes*
   to one ordered codomain, with the `spectrum_*` edges above as its action on shape morphisms, is
   **not built**. Blocking sub-problem (now precise, thanks to the partiality of `capSpectrum`):
   *the codomain is not unified* — `LittlestoneDim : WithBot (WithTop ℕ)`, `OrdinalVCDim : Ordinal`,
   the real shapes live over `ConceptClass X ℝ`, the rest over `WithTop ℕ` and `ConceptClass X Bool`.
   A total `Cap_Σ` must first construct a common codomain and the coercions between them as a single
   ordered object; that object is absent.

2. **The missing edges of the partial order.** Several inter-dimension relations that *would* be
   `Cap_Σ`-edges are **not** in the kernel as public theorems and are NOT asserted here:
   * `VCDim ≤ LittlestoneDim` (set-shape `⟶` tree-shape, "a shattered set is a depth-`d` shattered
     stump"). The kernel has `vcdim_le_of_mistake_bounded` but it is `private` in
     `FLT_Proofs/Theorem/Separation.lean`, so it cannot be re-exported; the clean
     `VCDim ≤ LittlestoneDim` edge is open here.
   * `NatarajanDim ≤ VCDim`-type collapses at `|Y| = 2` (the multiclass shapes degenerating to the
     binary set shape): not stated.
   * Pseudodimension `⟶` VC for `Bool`-thresholded classes (the real shape restricting to the set
     shape): not stated.

3. **Functoriality vs. mere comparability.** Even granting the codomain, the claim that the proven
   edges *compose* coherently (that the shape morphisms form a category and `Cap_Σ` respects
   composition) is unproven. The one composite the fragment supports — `spectrum_fat_le_pseudo`
   followed by `pseudodim_le` to get `FatShatteringDim ≤ finrank+1`, packaged in
   `spectrum_real_dims_le_finrank` — is suggestive but is a single triangle, not functoriality.

These are recorded so the next agent knows exactly which construction targets are open (the common
codomain, the `VCDim ≤ LittlestoneDim` edge, the category of shapes) and which are already KK (the
seven `spectrum_*` re-exports above). -/
