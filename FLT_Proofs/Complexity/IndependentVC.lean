/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.Relabel
import FLT_Proofs.Complexity.IndependentVC.BooleanComb
import FLT_Proofs.Complexity.IndependentVC.DeMorgan
import FLT_Proofs.Complexity.IndependentVC.Growth
import FLT_Proofs.Complexity.IndependentVC.GrowthMul
import FLT_Proofs.Complexity.IndependentVC.GrowthMono
import FLT_Proofs.Complexity.IndependentVC.UnionGrowth
import FLT_Proofs.Complexity.IndependentVC.Monotone
import FLT_Proofs.Complexity.IndependentVC.MatroidWitness
import FLT_Proofs.Complexity.IndependentVC.PlKill
import FLT_Proofs.Complexity.IndependentVC.Pullback
import FLT_Proofs.Complexity.IndependentVC.PullbackEquiv
import FLT_Proofs.Complexity.IndependentVC.Corollaries
import FLT_Proofs.Complexity.IndependentVC.Finiteness
import FLT_Proofs.Complexity.IndependentVC.ShatterCount
import FLT_Proofs.Complexity.IndependentVC.VCFinite
import FLT_Proofs.Complexity.IndependentVC.GrowthPoly
import FLT_Proofs.Complexity.IndependentVC.FiniteSauerShelah
import FLT_Proofs.Complexity.IndependentVC.GrowthSauerShelah
import FLT_Proofs.Complexity.IndependentVC.PartialBinomial
import FLT_Proofs.Complexity.IndependentVC.UnionFinite
import FLT_Proofs.Complexity.IndependentVC.UnionTight
import FLT_Proofs.Complexity.IndependentVC.BooleanCombFinite
import FLT_Proofs.Complexity.IndependentVC.LatticeClosure
import FLT_Proofs.Complexity.IndependentVC.Dual
import FLT_Proofs.Complexity.IndependentVC.DualBound
import FLT_Proofs.Complexity.IndependentVC.VCDensity
import FLT_Proofs.Complexity.IndependentVC.OpenRouteR1
import FLT_Proofs.Complexity.IndependentVC.OpenRouteR2
import FLT_Proofs.Complexity.IndependentVC.MatroidStructure
import FLT_Proofs.Complexity.IndependentVC.Dudley
import FLT_Proofs.Complexity.IndependentVC.Pseudodimension
import FLT_Proofs.Complexity.IndependentVC.Packing
import FLT_Proofs.Complexity.IndependentVC.EpsilonNetBridge
import FLT_Proofs.Complexity.IndependentVC.Learnability
import FLT_Proofs.Complexity.IndependentVC.FundamentalTheorem
import FLT_Proofs.Complexity.IndependentVC.CapacityFinite
import FLT_Proofs.Complexity.IndependentVC.Halfspace
import FLT_Proofs.Complexity.IndependentVC.FrameworkRoot
import FLT_Proofs.Complexity.IndependentVC.CapacitySpectrum
import FLT_Proofs.Complexity.IndependentVC.Finitization
import FLT_Proofs.Complexity.IndependentVC.FrameworkClosures
import FLT_Proofs.Complexity.IndependentVC.ScaleFinitization
import FLT_Proofs.Complexity.IndependentVC.CapacityClosures
import FLT_Proofs.Complexity.IndependentVC.ExpressivityClosures
import FLT_Proofs.Complexity.IndependentVC.StructureClosures
import FLT_Proofs.Complexity.IndependentVC.LObjGalois
import FLT_Proofs.Complexity.IndependentVC.CapSigmaFunctor

/-!
# Independent VC-dimension theory — module index

A self-contained Vapnik–Chervonenkis theory built directly on the bare definitions in
`FLT_Proofs.Complexity.VCDimension` (`Shatters`, `VCDim`, `GrowthFunction`), depending only on
Mathlib, then bridged to the kernel's measure-theoretic learning infrastructure. Importing this file
pulls in the whole development. Every module is `sorry`-free with axioms
`{propext, Classical.choice, Quot.sound}`.

## Map of the development

**Boolean calculus & relabelling.** `Relabel` (complement/XOR invariance), `BooleanComb`,
`DeMorgan` — the pointwise Boolean algebra of concept classes.

**Growth function.** `Growth`, `GrowthMul` (sub-multiplicativity for Boolean combinations),
`GrowthMono`, `UnionGrowth` (sub-additivity), `ShatterCount` (`shatters ⇒ growth ≥ 2^|S|`).

**Finiteness characterization.** `Finiteness` (`2^m` beats every polynomial), `VCFinite`
(`vcDim_lt_top_of_growth_poly`), `GrowthPoly` (converse, Sauer–Shelah), giving
`VCDim < ⊤ ⟺ eventually polynomial growth`.

**Quantitative Sauer–Shelah.** `FiniteSauerShelah` (true-set encoding → Mathlib Pajor bound),
`GrowthSauerShelah` (`GrowthFunction ≤ ∑_{k≤d} C(m,k)`, general domain), `PartialBinomial`
(complementary-binomial counting), `Packing` (exponential form `(em/d)^d` + packing bound).

**Lattice closure.** `Monotone`, `UnionFinite`, `UnionTight` (sharp `d+d'+1`), `BooleanCombFinite`,
`LatticeClosure` (k-fold) — finite VC is closed under the lattice operations.

**Duality & density.** `Pullback`/`PullbackEquiv` (contravariant functoriality), `Dual`/`DualBound`
(Assouad sandwich + self-dual finiteness), `VCDensity` (subadditive density — the matroid-arc closer
opposite `MatroidWitness`/`PlKill`).

**Dudley / real-valued capacity.** `Dudley` (`VCDim(signClass V) ≤ finrank ℝ V`), `Pseudodimension`
(`Pseudodimension ≤ finrank + 1`, `fatShatteringDim_le`), `Halfspace` (the sharp
`VCDim(halfspaces ℝⁿ) = n` corollary).

**Learning bridge.** `Learnability` (finite VC ⇒ PAC via the kernel), `FundamentalTheorem`
(`VCDim < ⊤ ⟺ PACLearnable ⟺ eventual poly growth`), `CapacityFinite` (the `Inv`-coordinate
predicate `CapacityFinite C := VCDim X C < ⊤` with the fundamental theorem as its iff-cluster).

**Open routes.** `OpenRouteR1` (matroid-rank submodularity — chain-modular, full lattice open),
`OpenRouteR2` (ε-net size gap — the ε-approximation ⇒ ε-net reduction proved).

**Framework synthesis (Γ-axis).** `FrameworkRoot` (the consumable measurement-quartet hub +
`vcDim_finite_ideal_closed`), `CapacitySpectrum` (the partial `capSpectrum` map on shattering shapes),
`Finitization` (the `Fin↓` `FinitizationScheme` + sample instance), and `FrameworkClosures` — the
closure of the four still-open framework conjectures at their honest tier: the further `Fin↓`
instances (sign / complement / intersection) with the unification edge `finitization_capacityInvariant`;
the shape partial-order `ShapeLE` with `capSpectrum_monotone_on_set`; the additivity-defect partial
`additivityDefect_pos` / `additivityDefect_le_one`; the Galois shadow
`galois_duality_exact_carrier_lax_invariant`; the genuine cross-library scale reduction
`scaleFinitization_reduces_to`; and three **sharpened-KU residuals** (full `Cap_Σ` functoriality, the
`k`-fold defect lower bound, the full `LObj` Galois adjunction) recorded in-place as open conjectures,
each naming its single confirmed-absent blocker rather than banked as a theorem.
`ScaleFinitization` — the **third** `Fin↓` resolution (IM2 / GM7), upgrading the scale leg from the
abstract reduction to a *genuine, concrete* instance: the sample-empirical Hamming pseudometric
`sampleHammingDist`, the in-FLT covering–growth bridge `coveringNumber_le_growthFunction` (the forward,
capacity-controls-trace half, fully discharged), the genuine `scaleFinitizationScheme` (size = the real
`CoveringNumber`, refinement `𝓝[>] 0`, forward half proved, reverse half = named TLT blocker), the
unification edge `scaleFinitization_capacityInvariant` (sample/sign/scale recover one invariant), and
the metric-Dudley residual `scaleFinitization_dudley_reduction` naming `TLT.Capacity.Chaining`.

**`Cap_Σ` functor (Γ-axis, IM1).** `CapSigmaFunctor` — advancing the "dimension zoo is one functor"
conjecture past the partial `capSpectrum` map: the shape order upgraded from a `Preorder` to a genuine
`PartialOrder` (`shapeLE_antisymm`, `capShapePartialOrder`); the unified codomain
`UnifiedCapacityCodomain` made *universe-correct* (`Ω : Type*`, fixed in `CapacityClosures.lean`) with a
**concrete instance** over `Ordinal` (`capSigmaCodomain`, built from the new Littlestone embedding
`withBotWithTopNatToOrdinal_mono`), discharging the codomain-unification blocker for the three native
codomains where the old `Ω : Type` structure could not even hold `Ordinal`; the Bool ↔ ℝ stratum gap bridged inside that codomain via `fatShatteringDim_boolToReal_eq`
(`capSigma_bool_eq_margin_in_codomain`, `capSigma_margin_scale_independent`); the proven inequalities
exhibited as the functor's monotone action in one ordinal codomain (`capSigma_ds_le_nat_in_codomain`,
`capSigma_monotone_on_proven_edges`); and the two genuinely cross-domain arrows delivered as precise
named-blocker reductions (`capSigma_set_le_tree_edge_reduces_to` — the `private`
`vcdim_le_of_mistake_bounded`; `capSigma_total_evaluator_reduces_to` — the per-shape evaluator for the
label-typed multiclass shapes), not fabricated.

**Expressivity closures (γ-axis).** `ExpressivityClosures` — the still-open arguments of the
*Expressivity* discovery URS, closed at their honest tier: the shatter↔adversary game reading
(`shatters_forces_all_mistakes` forward, `shatters_iff_realizerOracle` converse-reduction); the
super-additivity defect characterization `superadditivity_defect_iff_not_submodular` (defect positive
iff not submodular, consuming `FrameworkClosures`'s defect bracketing); the VC / Littlestone
**separation Pl-kill** `vc_littlestone_separation` (threshold class: `VCDim < ⊤` yet
`LittlestoneDim = ⊤`, with `littlestoneDim_ge_vcDim` for the one-directionality); the consolidated
realizability certificate `shatters_realizability_certificate`; and the parity / computational-axis
gate `parity_shattering_invariant` + `vcDim_is_parity_blind`, with the parity-sensitive separator
recorded as a **sharpened-KU residual** (open, not banked).

**Structure closures (γ-axis, `Pl + Coh`).** `StructureClosures` — the still-open arguments of the
*Structure* discovery URS, closed at their honest tier: the two dual developments are one canonical
object (`dualClass_eq_DualClass`, definitional) with coinciding Assouad bounds; the bidual is settled
as a **boundary** — dualization is provably lossy (`dualClass_not_vcDim_preserving`, a sharp Pl-kill),
equality holds only conditionally (`vcDim_biDual_eq_of_eval_equiv`); the **category of learning
objects** `LObj` is built as a genuine `CategoryTheory.Category` (`instLObjCategory`) with the **lax**
Galois statement `lobj_biDual_unit_lax`; the **automorphism group** `autClass` is built as a `Subgroup`
of `Equiv.Perm` (`instAutGroup`) with `vcDim_aut_invariant`, the universality claim genuinely killed —
a *proven* relabel-invariant functional that *provably* does not factor through VCDim, by concept count
(`vcDim_not_universal_relabel_invariant`) and the sharper Assouad dual capacity
(`vcDim_not_universal_relabel_invariant_dual`); the obstruction-module generators
`vcDim_not_subadditive_under_union` /
`vcDim_not_modular_off_chain` against `vcDim_permitted_identities`; the proven Hasse edges
(`hasse_proven_edges`) with the named open-edge reduction (`hasse_open_reduction`); and decomposition
theory — the union budget (`finite_vc_union_decomposition_budget`), the sharp no-cheap-decomposition
obstruction (`no_cheap_union_decomposition`), and the primary-decomposition reduction
(`primary_decomposition_reduction`).

**The genuine point↔concept Galois connection (γ-axis, IM3).** `LObjGalois` — the honest closure of
the IM3 conjecture (a genuine point↔concept Galois connection / contravariant adjunction). A *strict*
capacity-preserving adjunction is impossible (the dual drops VC dimension,
`dualClass_not_vcDim_preserving`), so the genuine Galois structure lives one level down, as the
classical **Birkhoff polarity** of the incidence relation `r x c := (c x = true)`: the two antitone
derivation operators `intent : Set X → Set (X → Bool)` and `extent : Set (X → Bool) → Set X` of formal
concept analysis form a **genuine `GaloisConnection`** `pointConcept_galoisConnection`
(via Mathlib's relation-polarity `SetRel.gc_leftDual_rightDual`), with the closure-operator facts
(`subset_extent_intent`, `subset_intent_extent`, `intent_extent_intent`, the concept-closure operator
`conceptClosure`). This polarity *is* the LObj duality data: the incidence relation is `evalConcept`
(`incidence_iff_evalConcept`) and the dual class is the range of incidence rows
(`dualClass_eq_evalConcept_range`). The exact boundary is `galois_holds_capacity_fails` /
`im3_closure_verdict`: genuine on the **set lattices**, but no capacity-preserving lift (the VC
functional is not polarity-invariant). Birkhoff 1940 (polarities); Ganter–Wille 1999 (FCA).
-/
