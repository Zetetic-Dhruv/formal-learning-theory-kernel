/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Theorem.PAC
import FLT_Proofs.Complexity.IndependentVC.Dudley
import FLT_Proofs.Complexity.IndependentVC.BooleanCombFinite
import FLT_Proofs.Complexity.IndependentVC.UnionFinite
import FLT_Proofs.Complexity.IndependentVC.LatticeClosure

/-!
# Learnability of the independent VC classes

This file is the bridge between the *independent VC-dimension module*
(`FLT_Proofs.Complexity.IndependentVC.*`) and the *statistical-learning kernel*
(`FLT_Proofs.Theorem.PAC`). The independent module proves, from scratch, a family of
**finiteness theorems** — each says some concept class has `VCDim < ⊤`. The kernel proves the
Fundamental Theorem of Statistical Learning, whose easy half is

`vcdim_finite_imp_pac : VCDim X C < ⊤ → PACLearnable X C`

(under the standard measurability regularity packaged by `MeasurableConceptClass`). Composing the
two gives a self-contained chain

```
            Dudley / lattice closure              vcdim_finite_imp_pac
  geometry  ───────────────────────▶  VCDim < ⊤  ─────────────────────▶  PAC-learnable
```

from a *combinatorial / linear-algebraic* input to a *statistical* output, with no shared
dependency between the two halves beyond the common notion of VC dimension.

## The showcase: linear sign classes (Dudley → PAC)

`signClass V`, the half-space-style class `{ x ↦ decide (0 < g x) | g ∈ V }` of a
finite-dimensional subspace `V ≤ (X → ℝ)`, is PAC-learnable
(`signClass_pacLearnable`). The whole argument is

* **linear algebra** — `vcDim_signClass_le V : VCDim X (signClass V) ≤ finrank ℝ V`, proved by a
  dual-space dimension count (Dudley 1978);
* **`finrank ℝ V : ℕ`** is finite, so the coercion is `< ⊤`
  (`lt_of_le_of_lt _ (WithTop.coe_lt_top _)`);
* **the kernel** — `vcdim_finite_imp_pac` then delivers PAC-learnability.

This is the canonical "VC dimension of linear classifiers is the parameter count, hence they
generalize" result, here as a single composition of two independently-proved theorems.

## The lattice of learnable classes

Finite VC dimension — and therefore PAC-learnability — is preserved by the Boolean/lattice
operations on concept classes. Each bridge below is the corresponding finiteness theorem fed to the
kernel:

| operation                | finiteness theorem            | learnability theorem        |
| ------------------------ | ----------------------------- | --------------------------- |
| pointwise Boolean combo  | `vcDim_booleanComb_finite`    | `booleanComb_pacLearnable`  |
| binary collection union  | `vcDim_union_finite`          | `union_pacLearnable`        |
| finite indexed union     | `vcDim_iUnion_finite`         | `iUnion_pacLearnable`       |

So the PAC-learnable classes over a fixed (measurably regular) domain form a family closed under
finite intersections, unions, complements, and any finite pointwise Boolean combination: a *lattice
of learnable hypotheses*, generated combinatorially and certified statistically.

## Honest hypotheses

The kernel theorem genuinely needs measurability, and we do not hide it: every theorem here takes
`[MeasurableSpace X] [MeasurableSingletonClass X]` and the relevant `[MeasurableConceptClass X _]`
as instance/hypothesis arguments. These discharge the regularity conditions of
`vcdim_finite_imp_pac` (every concept measurable, all `X → Bool` measurable, the uniform-convergence
bad event `NullMeasurableSet`). No measurability is faked; where it cannot be discharged for free it
is assumed. See the closing remark on finite domains for the one case where it *is* free.

## Discharging measurability for free on discrete domains

On a *countable* domain `X` carrying the discrete σ-algebra — equivalently `[Countable X]` with
`[MeasurableSingletonClass X]`, since on a countable space those imply `DiscreteMeasurableSpace X`
— *every* `X → Bool` is measurable and *every* uniform-convergence bad event is a measurable (hence
null-measurable) set. So the whole regularity package `MeasurableConceptClass X C` holds for *any*
`C`, with no extra hypothesis. We record this as a `UniversallyMeasurableSpace X` instance, which
then supplies `[MeasurableConceptClass X (signClass V)]` automatically. The upshot
(`signClass_pacLearnable_of_countable`, `signClass_pacLearnable_of_finite`) is the showcase with
*no measurability hypothesis at all*: on a finite domain, Dudley's bound alone certifies
PAC-learnability of every linear sign class.

## Main results

* `signClass_pacLearnable`   — Dudley ⟹ `signClass V` is PAC-learnable. **(showcase)**
* `booleanComb_pacLearnable` — finite Boolean combination of finite-VC classes is PAC-learnable.
* `union_pacLearnable`       — binary union of finite-VC classes is PAC-learnable.
* `iUnion_pacLearnable`      — finite indexed union of finite-VC classes is PAC-learnable.
* `signClass_pacLearnable_of_finite` — on a finite discrete domain, `signClass V` is PAC-learnable
  with no measurability hypothesis (BONUS).
-/

universe u v

variable {X : Type u}

/-! ## Showcase: linear sign classes are PAC-learnable (Dudley → finite VC → PAC) -/

/-- **Dudley ⟹ PAC.** The linear sign class `signClass V` of a finite-dimensional subspace
`V ≤ (X → ℝ)` is PAC-learnable.

The VC dimension is bounded by the parameter count `finrank ℝ V` (Dudley's theorem,
`vcDim_signClass_le`); a coerced natural number is `< ⊤`; and the kernel's
`vcdim_finite_imp_pac` converts finite VC dimension into PAC-learnability. This is the headline
"linear classifiers generalize, with sample complexity governed by their dimension" result,
assembled from the independent VC module and the learning kernel. -/
theorem signClass_pacLearnable [MeasurableSpace X] [MeasurableSingletonClass X]
    (V : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ V]
    [MeasurableConceptClass X (signClass V)] :
    PACLearnable X (signClass V) :=
  vcdim_finite_imp_pac X (signClass V)
    (lt_of_le_of_lt (vcDim_signClass_le V) (WithTop.coe_lt_top _))

/-! ## The lattice of learnable classes -/

/-- **Boolean combinations preserve PAC-learnability.** A pointwise Boolean combination
`booleanComb φ C` of finitely many finite-VC classes `C : Fin k → ConceptClass X Bool` is
PAC-learnable, uniformly over the combiner `φ`.

Finiteness of the VC dimension is `vcDim_booleanComb_finite`; the kernel closes the gap. -/
theorem booleanComb_pacLearnable [MeasurableSpace X] [MeasurableSingletonClass X]
    {k : ℕ} (φ : (Fin k → Bool) → Bool) (C : Fin k → ConceptClass X Bool)
    (hC : ∀ i, VCDim X (C i) < ⊤)
    [MeasurableConceptClass X (booleanComb φ C)] :
    PACLearnable X (booleanComb φ C) :=
  vcdim_finite_imp_pac X (booleanComb φ C) (vcDim_booleanComb_finite φ C hC)

/-- **Binary unions preserve PAC-learnability.** The collection union `C ∪ D` of two finite-VC
classes is PAC-learnable.

Finiteness of the VC dimension is `vcDim_union_finite`; the kernel closes the gap. -/
theorem union_pacLearnable [MeasurableSpace X] [MeasurableSingletonClass X]
    {C D : ConceptClass X Bool} (hC : VCDim X C < ⊤) (hD : VCDim X D < ⊤)
    [MeasurableConceptClass X (C ∪ D)] :
    PACLearnable X (C ∪ D) :=
  vcdim_finite_imp_pac X (C ∪ D) (vcDim_union_finite hC hD)

/-- **Finite indexed unions preserve PAC-learnability.** The union `⋃ i, C i` of a `Fintype`-indexed
family of finite-VC classes is PAC-learnable.

Finiteness of the VC dimension is `vcDim_iUnion_finite`; the kernel closes the gap. -/
theorem iUnion_pacLearnable [MeasurableSpace X] [MeasurableSingletonClass X]
    {ι : Type v} [Fintype ι] (C : ι → ConceptClass X Bool)
    (hC : ∀ i, VCDim X (C i) < ⊤)
    [MeasurableConceptClass X (⋃ i, C i)] :
    PACLearnable X (⋃ i, C i) :=
  vcdim_finite_imp_pac X (⋃ i, C i) (vcDim_iUnion_finite C hC)

/-! ## BONUS: discharging measurability on discrete domains

On a countable domain with the discrete σ-algebra, measurability is automatic. We package this once
as a `UniversallyMeasurableSpace` instance, then read off the showcase with no measurability
hypothesis. -/

open MeasureTheory in
/-- A countable space with the discrete σ-algebra is universally measurable: every `X → Bool` is
measurable and every uniform-convergence bad event is a measurable set. On such a domain
`MeasurableConceptClass X C` holds for *every* concept class `C`
(via `MeasurableConceptClass.ofUniversallyMeasurable`).

`[Countable X] [MeasurableSingletonClass X]` is the same hypothesis, since together they synthesize
`DiscreteMeasurableSpace X` (`MeasurableSingletonClass.toDiscreteMeasurableSpace`). The
discrete-measurability of the product sample space `(Fin m → X) × (Fin m → X)` — needed for the
`WellBehavedVC` bad event — is then synthesized automatically from countability of `X`. -/
instance (priority := 100) UniversallyMeasurableSpace.ofCountableDiscrete
    [MeasurableSpace X] [Countable X] [DiscreteMeasurableSpace X] :
    UniversallyMeasurableSpace X where
  all_concepts_measurable := fun _ => Measurable.of_discrete
  all_classes_wellBehaved := fun _ => by
    intro _ _ _ _ _
    exact MeasurableSet.nullMeasurableSet (DiscreteMeasurableSpace.forall_measurableSet _)

/-- **Showcase on a countable discrete domain — no measurability hypothesis.** When `X` is countable
with the discrete σ-algebra, `signClass V` is PAC-learnable for any finite-dimensional `V`. The
`MeasurableConceptClass` instance is discharged automatically through
`UniversallyMeasurableSpace.ofCountableDiscrete`. -/
theorem signClass_pacLearnable_of_countable [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X]
    (V : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ V] :
    PACLearnable X (signClass V) :=
  signClass_pacLearnable V

/-- **Showcase on a finite discrete domain — no measurability hypothesis.** When `X` is finite with
the discrete σ-algebra, `signClass V` is PAC-learnable for any finite-dimensional `V`. This is
Dudley's bound, alone, certifying PAC-learnability of every linear sign class. -/
theorem signClass_pacLearnable_of_finite [MeasurableSpace X] [Finite X]
    [MeasurableSingletonClass X]
    (V : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ V] :
    PACLearnable X (signClass V) :=
  signClass_pacLearnable V
