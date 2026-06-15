/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.GrowthPoly
import FLT_Proofs.Complexity.IndependentVC.VCFinite
import FLT_Proofs.Theorem.PAC

/-!
# The fundamental theorem of statistical learning

The capstone tying the independent VC-dimension development together. For a concept class `C`, three
properties coincide:

* **finite VC dimension** (`VCDim X C < ⊤`),
* **eventually polynomial growth** (`GrowthFunction X C m ≤ K · m^d` for large `m`),
* **PAC learnability** (`PACLearnable X C`, the measure-theoretic learning guarantee).

The growth equivalence is purely combinatorial: `vcDim_finite_imp_growth_poly` (Sauer–Shelah) and its
converse `vcDim_lt_top_of_growth_poly` (a shattered set of size `m` forces growth `2^m`, which beats
every polynomial). The PAC equivalence is the kernel's `vc_characterization`, routed through uniform
convergence and Sauer–Shelah; it needs the measurability structure on the domain.

Reference: V. Vapnik, A. Chervonenkis (1971); the synthesis is the "fundamental theorem of statistical
learning" (Blumer–Ehrenfeucht–Haussler–Warmuth, J. ACM 36 (1989); Shalev-Shwartz–Ben-David, *Under-
standing Machine Learning*, CUP 2014, Thm 6.7).

## Main results

* `vcDim_lt_top_iff_growth_poly`: finite VC dimension iff eventually polynomial growth.
* `vcDim_lt_top_iff_pacLearnable`: finite VC dimension iff PAC learnable.
* `vcDim_fundamental_theorem`: the three-way equivalence.
-/

open Filter

universe u

variable {X : Type u}

/-- **Finite VC dimension ⟺ eventually polynomial growth.** The purely combinatorial half of the
fundamental theorem: `VCDim X C < ⊤` exactly when the growth function is eventually bounded by a
polynomial. -/
theorem vcDim_lt_top_iff_growth_poly {C : ConceptClass X Bool} :
    VCDim X C < ⊤ ↔
      ∃ (K : ℝ) (d : ℕ), ∀ᶠ m : ℕ in atTop, (GrowthFunction X C m : ℝ) ≤ K * (m : ℝ) ^ d :=
  ⟨vcDim_finite_imp_growth_poly, fun ⟨K, d, h⟩ => vcDim_lt_top_of_growth_poly K d h⟩

/-- **Finite VC dimension ⟺ PAC learnability.** The measure-theoretic half: `VCDim X C < ⊤` exactly
when `C` is PAC learnable. This is the kernel's `vc_characterization`, surfaced for the independent
module; it requires the domain's measurability structure. -/
theorem vcDim_lt_top_iff_pacLearnable [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C] :
    VCDim X C < ⊤ ↔ PACLearnable X C :=
  (vc_characterization X C).symm

/-- **The fundamental theorem of statistical learning.** For a measurable concept class, finite VC
dimension, eventually polynomial growth, and PAC learnability are mutually equivalent. -/
theorem vcDim_fundamental_theorem [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C] :
    (VCDim X C < ⊤ ↔ PACLearnable X C) ∧
      (VCDim X C < ⊤ ↔
        ∃ (K : ℝ) (d : ℕ), ∀ᶠ m : ℕ in atTop, (GrowthFunction X C m : ℝ) ≤ K * (m : ℝ) ^ d) :=
  ⟨vcDim_lt_top_iff_pacLearnable C, vcDim_lt_top_iff_growth_poly⟩
