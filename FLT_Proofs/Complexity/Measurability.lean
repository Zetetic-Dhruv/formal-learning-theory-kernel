/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Basic
import FLT_Proofs.Data
import FLT_Proofs.Complexity.Symmetrization

/-!
# Measurability Infrastructure for Learning Theory

This file defines the `MeasurableConceptClass` typeclass, which bundles
the measure-theoretic regularity conditions needed for PAC learning theory.

## Background

The Fundamental Theorem of Statistical Learning (PAC ↔ finite VC dimension)
requires measurability assumptions that are often left implicit in pen-and-paper
proofs. Krapp & Wirth (2024, arXiv:2410.10243) systematically extract these
conditions. This file formalizes them as Lean4 typeclass infrastructure.

The three bundled conditions are:
1. `mem_measurable`: every concept in C is a measurable function
2. `all_measurable`: all concepts X → Bool are measurable (for disagreement sets)
3. `wellBehaved`: the uniform convergence bad event is NullMeasurableSet
   (the `WellBehavedVC` condition from Symmetrization.lean)

Condition 3 is the non-trivial one. For countable concept classes, it holds
automatically. For uncountable classes, the existential quantifier in the UC event
{∃ h ∈ C, |TrueErr - EmpErr| ≥ ε} does not preserve MeasurableSet, and the
NullMeasurableSet weakening is needed. This was discovered during the Lean4
formalization and is a genuine measure-theoretic subtlety absent
from standard textbook presentations.

## Relationship to ad hoc predicates

This typeclass replaces explicit hypothesis threading in theorem signatures:
- `(hmeas_C : ∀ h ∈ C, Measurable h)` → `MeasurableConceptClass.mem_measurable`
- `(hc_meas : ∀ c : Concept X Bool, Measurable c)` → `MeasurableConceptClass.all_measurable`
- `(hWB : WellBehavedVC X C)` → `MeasurableConceptClass.wellBehaved`

Combined with `MeasurableBatchLearner` (Learner/Core.lean), these two typeclasses
provide the complete regularity infrastructure for PAC learning proofs.
-/

universe u

/-- A concept class with the measure-theoretic regularity needed for PAC theory.

    Bundles three conditions:
    1. Every concept in C is measurable
    2. All concepts are measurable (needed for disagreement set measurability)
    3. The UC bad event satisfies NullMeasurableSet (WellBehavedVC)

    Condition 3 is the deep one: for uncountable C, the existential
    {∃ h ∈ C, |TrueErr - EmpErr| ≥ ε} is NOT MeasurableSet in general.
    WellBehavedVC asserts it is NullMeasurableSet, which suffices for
    integration (lintegral_indicator_one₀). -/
class MeasurableConceptClass (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop where
  /-- Every concept in C is measurable -/
  mem_measurable : ∀ h ∈ C, Measurable h
  /-- All concepts X → Bool are measurable (for disagreement sets) -/
  all_measurable : ∀ c : Concept X Bool, Measurable c
  /-- Uniform convergence bad event is NullMeasurableSet -/
  wellBehaved : WellBehavedVC X C

/-! ## Bridge API: typeclass → explicit hypotheses

These bridge lemmas allow incremental migration of existing theorems.
Each theorem currently takes explicit `hmeas_C`, `hc_meas`, `hWB` arguments.
With these bridges, callers can write:
  `MeasurableConceptClass.hmeas_C C`
instead of threading the hypothesis manually. -/

/-- Accessor: every concept in a `MeasurableConceptClass` is measurable. Lifts the
`mem_measurable` field to the call site. -/
theorem MeasurableConceptClass.hmeas_C
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : MeasurableConceptClass X C] :
    ∀ c ∈ C, Measurable c :=
  h.mem_measurable

/-- Accessor: in a `MeasurableConceptClass`, every `Bool`-valued function on the domain is
measurable, not only those in `C`. Required wherever a disagreement set must be shown
measurable. -/
theorem MeasurableConceptClass.hc_meas
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : MeasurableConceptClass X C] :
    ∀ c : Concept X Bool, Measurable c :=
  h.all_measurable

/-- Accessor: extracts the `WellBehavedVC` regularity hypothesis from a
`MeasurableConceptClass`. The substantive field of the bundle. -/
theorem MeasurableConceptClass.hWB
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : MeasurableConceptClass X C] :
    WellBehavedVC X C :=
  h.wellBehaved

/-! ## Instances

TODO: Add automatic instances for common cases:
- Finite concept classes (WellBehavedVC holds automatically)
- Concept classes over MeasurableSingletonClass spaces
- Countable concept classes (existential preserves measurability)
-/

/-! ## UniversallyMeasurableSpace: domain-level measurability

When the domain X is "nice enough" (e.g., MeasurableSingletonClass, countable,
or standard Borel), EVERY concept class over X automatically satisfies
MeasurableConceptClass. This is a property of the space, not the class.

This typeclass captures: "X is regular enough that measurability of learning
events is never an issue." It resolves theorems like `uc_does_not_imply_online`
which quantify over ALL concept classes, not a specific one. -/

/-- A measurable space where all Bool-valued functions are measurable and
    all concept classes are well-behaved (WellBehavedVC).

    This is a domain-level property: it says the σ-algebra on X is rich enough
    that learning-theoretic measurability is automatic.

    Examples:
    - Any MeasurableSingletonClass space (discrete σ-algebra)
    - Any countable space
    - Standard Borel spaces (ℝⁿ with Borel σ-algebra)

    The key consequence: for any C over X, the UC bad event
    {∃ h ∈ C, |TrueErr - EmpErr| ≥ ε} is NullMeasurableSet automatically. -/
class UniversallyMeasurableSpace (X : Type u) [MeasurableSpace X] : Prop where
  /-- All Bool-valued functions on X are measurable -/
  all_concepts_measurable : ∀ c : Concept X Bool, Measurable c
  /-- All concept classes over X have well-behaved uniform convergence events -/
  all_classes_wellBehaved : ∀ C : ConceptClass X Bool, WellBehavedVC X C

/-- UniversallyMeasurableSpace implies MeasurableConceptClass for every C. -/
instance (priority := 50) MeasurableConceptClass.ofUniversallyMeasurable
    {X : Type u} [MeasurableSpace X] [h : UniversallyMeasurableSpace X]
    (C : ConceptClass X Bool) : MeasurableConceptClass X C where
  mem_measurable := fun c _ => h.all_concepts_measurable c
  all_measurable := h.all_concepts_measurable
  wellBehaved := h.all_classes_wellBehaved C

/-! ## UniversallyMeasurableSpace bridge API -/

/-- On a `UniversallyMeasurableSpace`, every `Bool`-valued concept is automatically
measurable. The easy half of the regularity hierarchy: when the σ-algebra is rich enough
(discrete, countable, or standard Borel with `MeasurableSingletonClass`), no per-concept
measurability hypothesis is needed. -/
theorem UniversallyMeasurableSpace.concept_measurable
    {X : Type u} [MeasurableSpace X] [h : UniversallyMeasurableSpace X]
    (c : Concept X Bool) : Measurable c :=
  h.all_concepts_measurable c

/-- On a `UniversallyMeasurableSpace`, every concept class is `WellBehavedVC`. The bad
event reduces to a measurable countable union, with no need for the grid reduction or the
Choquet bridge. The complementary case to the genuinely uncountable, genuinely analytic
setting handled in `BorelAnalyticBridge.lean`. -/
theorem UniversallyMeasurableSpace.class_wellBehaved
    {X : Type u} [MeasurableSpace X] [h : UniversallyMeasurableSpace X]
    (C : ConceptClass X Bool) : WellBehavedVC X C :=
  h.all_classes_wellBehaved C

/-! ## Bridge Instances (L1 ↔ L5) -/

instance (priority := 60) MeasurableHypotheses.ofMeasurableConceptClass
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C] :
    MeasurableHypotheses X C where
  mem_measurable := MeasurableConceptClass.hmeas_C C

instance (priority := 50) MeasurableBoolSpace.ofUniversallyMeasurable
    {X : Type u} [MeasurableSpace X] [h : UniversallyMeasurableSpace X] :
    MeasurableBoolSpace X where
  all_bool_measurable := h.all_concepts_measurable

/-! ## Krapp-Wirth Ghost Gap Infrastructure

Formalization of the ghost-gap machinery from Krapp & Wirth (2024, arXiv:2410.10243).
Uses sSup over value sets (not ⨆) to avoid class-inference ambiguity.
V-measurability is ONE-SIDED (not absolute) to match WellBehavedVC's event shape. -/

/-- The one-sided ghost gap `E_{S'}(h) - E_S(h)`: empirical error of `h` on the ghost
sample minus empirical error on the train sample. The supremum of this quantity over
`h ∈ C` is the random variable that the symmetrization inequality compares to `ε`. The
two-sided variant `absGhostGap` is paper-faithful but not what the VC to PAC route needs;
the one-sided form matches the one-sided shape of `WellBehavedVC`. -/
noncomputable def oneSidedGhostGap
    {X : Type u} [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : ℝ :=
  EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
  EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool)

/-- Two-sided ghost gap `|E_{S'}(h) - E_S(h)|`. Used only by the absolute Krapp-Wirth
formulation `KrappWirthVAbs`; the kernel's main route uses `oneSidedGhostGap`. -/
noncomputable def absGhostGap
    {X : Type u} [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : ℝ :=
  |oneSidedGhostGap h c m p|

/-- The set of one-sided ghost-gap values realised by the class on a fixed sample pair.
Defined as a `Set ℝ` rather than a `Finset ℝ` so that the existential over `h ∈ C` is
expressed natively; finiteness is recovered as a separate lemma (`ghostGapVals_finite`),
which is exactly what licenses the supremum to be attained. -/
noncomputable def ghostGapVals
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : Set ℝ :=
  {r | ∃ h ∈ C, r = oneSidedGhostGap h c m p}

/-- Two-sided counterpart of `ghostGapVals`. Used only in the absolute Krapp-Wirth
variant. -/
noncomputable def absGhostGapVals
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : Set ℝ :=
  {r | ∃ h ∈ C, r = absGhostGap h c m p}

/-- The supremum `sSup (ghostGapVals C c m p)`. Although stated as a supremum over
`h ∈ C` (an uncountable index in general), the underlying value set is finite, so the
supremum is attained. This is the random variable whose preimage characterises the
symmetrization bad event. -/
noncomputable def ghostGapSup
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : ℝ :=
  sSup (ghostGapVals C c m p)

/-- Two-sided counterpart of `ghostGapSup`. Used only in the absolute Krapp-Wirth
variant. -/
noncomputable def absGhostGapSup
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : ℝ :=
  sSup (absGhostGapVals C c m p)

/-! ## Krapp-Wirth Measurability Conditions (Definition 3.2)

V-measurability uses the ONE-SIDED ghost gap sup (not absolute value).
This is needed for the implication KrappWirthWellBehaved → WellBehavedVC,
because WellBehavedVC's event is one-sided.

The paper-faithful ABSOLUTE version is KrappWirthVAbs, kept separately. -/

/-- V-measurability (one-sided): the ghost gap sup map is measurable. -/
def KrappWirthV (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∀ (c : Concept X Bool) (m : ℕ),
    Measurable (ghostGapSup C c m)

/-- V-measurability (absolute, paper-faithful): the abs ghost gap sup is measurable. -/
def KrappWirthVAbs (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∀ (c : Concept X Bool) (m : ℕ),
    Measurable (absGhostGapSup C c m)

/-- U-measurability: the UC gap map is measurable. -/
def KrappWirthU (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∀ (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (m : ℕ),
    Measurable (fun xs : Fin m → X =>
      sSup {r | ∃ h ∈ C, r =
        |TrueErrorReal X h c D -
         EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)|})

/-- Krapp-Wirth well-behavedness: measurable hypotheses + V + U.
    Extends MeasurableHypotheses (L1).
    Strictly stronger than MeasurableConceptClass (our condition). -/
class KrappWirthWellBehaved (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) extends MeasurableHypotheses X C : Prop where
  V_measurable : KrappWirthV X C
  U_measurable : KrappWirthU X C

/-! ## Finite-Grid Attainment

EmpiricalError on m samples takes values in {0/m, 1/m, ..., m/m}.
So the one-sided ghost gap takes values in a finite set (differences of grid values).
Therefore sSup is attained, and {sSup ≥ ε} = {∃ h ∈ C, gap(h) ≥ ε}. -/

/-- The finite grid `{0/m, 1/m, …, m/m}` of possible empirical-error values on a sample
of size `m`. Defined as a `Finset ℝ` of cardinality `m + 1` (with the boundary case
`m = 0` returning `{0}`). The combinatorial fact that drives the entire grid reduction:
no matter how complex the hypothesis, its empirical error lives here. -/
noncomputable def empErrGrid (m : ℕ) : Finset ℝ :=
  if m = 0 then {0}
  else (Finset.range (m + 1)).image (fun (k : ℕ) => (k : ℝ) / (m : ℝ))

/-- The grid of one-sided ghost-gap values: pairwise differences of `empErrGrid m`, of
cardinality at most `(m + 1)^2`. Every value of `oneSidedGhostGap` lies in this grid
(`oneSidedGhostGap_mem_grid`), so the value set `ghostGapVals C c m p` is finite for
every class and every sample pair. -/
noncomputable def ghostGapGrid (m : ℕ) : Finset ℝ :=
  ((empErrGrid m).product (empErrGrid m)).image (fun ab => ab.1 - ab.2)

/-- Every empirical error lies in the grid `empErrGrid m`. The proof is direct counting:
the error is `(# misclassifications) / m` and the numerator ranges over `{0, …, m}`. -/
lemma empiricalError_mem_empErrGrid
    {X : Type u} [MeasurableSpace X]
    (h : Concept X Bool) {m : ℕ}
    (S : Fin m → X × Bool) :
    EmpiricalError X Bool h S (zeroOneLoss Bool) ∈ empErrGrid m := by
  by_cases hm : m = 0
  · simp [EmpiricalError, empErrGrid, hm]
  · simp only [EmpiricalError, hm, ↓reduceIte, empErrGrid]
    set k := (Finset.univ.filter (fun i : Fin m => h (S i).1 ≠ (S i).2)).card
    have hsum : Finset.univ.sum (fun i => zeroOneLoss Bool (h (S i).1) (S i).2) = (k : ℝ) := by
      simp only [zeroOneLoss, k]
      have : ∀ i : Fin m, (if h (S i).1 = (S i).2 then (0 : ℝ) else 1) =
          if h (S i).1 ≠ (S i).2 then 1 else 0 := by
        intro i; split_ifs <;> simp_all
      simp_rw [this, Finset.sum_boole]
    rw [hsum]
    have hk : k < m + 1 := by
      calc k ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = m := Finset.card_fin m
        _ < m + 1 := Nat.lt_succ_iff.mpr le_rfl
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩

/-- Every one-sided ghost-gap value lies in `ghostGapGrid m`, by applying
`empiricalError_mem_empErrGrid` to the train and ghost samples and taking the
difference. -/
lemma oneSidedGhostGap_mem_grid
    {X : Type u} [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) :
    oneSidedGhostGap h c m p ∈ ghostGapGrid m := by
  simp only [ghostGapGrid, oneSidedGhostGap]
  exact Finset.mem_image.mpr
    ⟨(EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool),
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool)),
     Finset.mem_product.mpr
       ⟨empiricalError_mem_empErrGrid h (fun i => (p.2 i, c (p.2 i))),
        empiricalError_mem_empErrGrid h (fun i => (p.1 i, c (p.1 i)))⟩,
     rfl⟩

/-- The set of ghost-gap values realised on a fixed sample pair is finite, regardless of
the cardinality of `C`. Embeds into `ghostGapGrid m` via `oneSidedGhostGap_mem_grid`. The
finiteness statement that allows `csSup_mem` to apply in
`wellBehaved_event_eq_preimage_gapSup`. -/
lemma ghostGapVals_finite
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) :
    (ghostGapVals C c m p).Finite :=
  (Finset.finite_toSet (ghostGapGrid m)).subset (fun r ⟨h, _, hr⟩ =>
    hr ▸ oneSidedGhostGap_mem_grid h c m p)

/-! ## Implication Chain: KrappWirth → WellBehavedVC -/

/-- The grid-reduction identity. For nonempty `C`, the one-sided ghost-gap event
  `{p | ∃ h ∈ C, oneSidedGhostGap h c m p ≥ ε / 2}`
equals the preimage
  `ghostGapSup C c m ⁻¹' Set.Ici (ε / 2)`.

The proof has two halves. Forward, a witness `h ∈ C` realising `gap(h) ≥ ε / 2`
contributes to the value set, so the supremum is at least `ε / 2`. Backward, the value
set is finite (`ghostGapVals_finite`), so its supremum is *attained* by some `h ∈ C`,
and that `h` is the witness.

The consequence is that the bad event reduces to a preimage under a single function
into ℝ, even though `C` is uncountable. Measurability follows from
`measurableSet_le` once `ghostGapSup` itself is shown measurable, and the latter is
exactly the content of `KrappWirthV`. The kernel uses this to conclude `NullMeasurableSet`
of the bad event, which is strictly weaker than `MeasurableSet` and is the correct
regularity level for the symmetrization argument: it is what Krapp and Wirth (2024)
should have asked for. -/
lemma wellBehaved_event_eq_preimage_gapSup
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ)
    (hC : C.Nonempty) :
    {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      oneSidedGhostGap h c m p ≥ ε / 2}
    = ghostGapSup C c m ⁻¹' Set.Ici (ε / 2) := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici, ghostGapSup]
  constructor
  · rintro ⟨h_wit, hh_wit, hge⟩
    calc ε / 2 ≤ oneSidedGhostGap h_wit c m p := hge
      _ ≤ sSup (ghostGapVals C c m p) :=
          le_csSup (ghostGapVals_finite C c m p).bddAbove
            (show oneSidedGhostGap h_wit c m p ∈ ghostGapVals C c m p from
              ⟨h_wit, hh_wit, rfl⟩)
  · intro hp
    have hne : (ghostGapVals C c m p).Nonempty := by
      obtain ⟨h0, hh0⟩ := hC
      exact ⟨oneSidedGhostGap h0 c m p, h0, hh0, rfl⟩
    have h_attained : sSup (ghostGapVals C c m p) ∈ ghostGapVals C c m p :=
      hne.csSup_mem (ghostGapVals_finite C c m p)
    obtain ⟨h_star, hh_star, h_eq⟩ := h_attained
    exact ⟨h_star, hh_star, by rw [← h_eq]; exact hp⟩

/-- KrappWirthWellBehaved → WellBehavedVC.
    Map measurability → event NullMeasurability. -/
theorem KrappWirthWellBehaved.toWellBehavedVC
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : KrappWirthWellBehaved X C] :
    WellBehavedVC X C := by
  intro D _ c m ε
  by_cases hC : C.Nonempty
  · have hV := h.V_measurable c m
    have hEq : {p : (Fin m → X) × (Fin m → X) | ∃ h_1 ∈ C,
        EmpiricalError X Bool h_1 (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h_1 (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      = ghostGapSup C c m ⁻¹' Set.Ici (ε / 2) := by
      have := wellBehaved_event_eq_preimage_gapSup C c m ε hC
      simp only [oneSidedGhostGap] at this
      exact this
    rw [hEq]
    exact (hV measurableSet_Ici).nullMeasurableSet
  · -- C empty → event is empty → NullMeasurableSet
    have : {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} = ∅ := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      push_neg; intro h hh; exact absurd ⟨h, hh⟩ hC
    rw [this]; exact MeasureTheory.nullMeasurableSet_empty

/-- KrappWirthWellBehaved → MeasurableConceptClass. -/
instance (priority := 75) MeasurableConceptClass.ofKrappWirth
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : KrappWirthWellBehaved X C]
    [hbool : MeasurableBoolSpace X] : MeasurableConceptClass X C where
  mem_measurable := h.mem_measurable
  all_measurable := hbool.all_bool_measurable
  wellBehaved := KrappWirthWellBehaved.toWellBehavedVC C

/-! ## Separation Interface (Open Questions) -/

/-- OPEN: Does finite VC + measurable hypotheses imply WellBehavedVC? -/
def WellBehavedVC_automatic : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (C : ConceptClass X Bool),
    MeasurableHypotheses X C → VCDim X C < ⊤ → WellBehavedVC X C

/-- OPEN: Does WellBehavedVC (NullMeasurable events) separate from
    KrappWirthWellBehaved (measurable maps)? -/
def KrappWirth_separation : Prop :=
  ∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
    MeasurableHypotheses X C ∧ WellBehavedVC X C ∧ ¬ KrappWirthWellBehaved X C

/-! ## Measurable-Target Variants

The Borel-analytic bridge theorem proves NullMeasurableSet for bad events
only when the target concept c is measurable. These variants restrict
the quantification to measurable targets. -/

/-- WellBehavedVC restricted to measurable targets.
    This is the correct target for the Borel-analytic positive bridge:
    Borel parameterization ⇒ analytic bad event ⇒ NullMeasurableSet,
    but only when c is measurable (so the ghost-gap map is measurable). -/
def WellBehavedVCMeasTarget
    (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∀ (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool), Measurable c →
    ∀ (m : ℕ) (ε : ℝ),
      MeasureTheory.NullMeasurableSet
        {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
        ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
         (MeasureTheory.Measure.pi (fun _ : Fin m => D)))

/-- OPEN QUESTION (measurable-target version):
    Does WellBehavedVCMeasTarget separate from KrappWirthWellBehaved?
    The Borel-analytic bridge (BorelAnalyticBridge.lean) closes this. -/
def KrappWirthSeparationMeasTarget : Prop :=
  ∃ (C : ConceptClass ℝ Bool),
    MeasurableHypotheses ℝ C ∧
    WellBehavedVCMeasTarget ℝ C ∧
    ¬ KrappWirthWellBehaved ℝ C
