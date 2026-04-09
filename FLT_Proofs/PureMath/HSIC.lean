/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.PureMath.MMD
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Hilbert-Schmidt Independence Criterion

Pure mathematical infrastructure for the Hilbert-Schmidt Independence Criterion
(HSIC) in reproducing kernel Hilbert spaces (RKHS). HSIC measures the dependence
between two random variables by computing the MMD squared between the joint
distribution and the product of its marginals. Under a characteristic kernel on
the product space, HSIC equals zero if and only if the random variables are
independent (i.e., the joint distribution equals the product of its marginals).

This file eliminates the `hsic_zero_iff_independent` axiom from the ICM
Unbundling project by proving it as a theorem.

## Main definitions

- `hsicDef` : the Hilbert-Schmidt Independence Criterion, defined as
  MMD²(P_{XY}, P_X ⊗ P_Y) where P_X and P_Y are the marginals of the
  joint distribution P_{XY}

## Main results

- `hsicDef_nonneg` : HSIC is nonneg
- `hsicDef_eq_zero_of_independent` : if P = P_X ⊗ P_Y then HSIC = 0
- `hsicDef_zero_iff_independent` : under a characteristic kernel on X × Y,
  HSIC(P) = 0 ↔ P = (P.map fst).prod (P.map snd)

## References

- Gretton, Bousquet, Smola, Scholkopf, "Measuring Statistical Dependence with
  Hilbert-Schmidt Norms", ALT 2005
- Gretton, Borgwardt, Rasch, Scholkopf, Smola, "A Kernel Two-Sample Test",
  Journal of Machine Learning Research, 2012
-/

noncomputable section

open MeasureTheory RKHS

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H (X × Y) ℝ]
variable [BoundedKernel H (X := X × Y)]

/-- The Hilbert-Schmidt Independence Criterion (HSIC) of a joint distribution P
    on X × Y is the squared MMD between P and the product of its marginals:
    HSIC(P) = MMD²(P_{XY}, P_X ⊗ P_Y).
    Here P_X = P.map Prod.fst and P_Y = P.map Prod.snd are the marginal
    distributions, and P_X.prod P_Y is their product measure.
    HSIC equals zero if and only if X and Y are independent under P
    (when the kernel is characteristic). -/
def hsicDef (P : Measure (X × Y)) : ℝ :=
  mmdSq (H := H) P ((P.map Prod.fst).prod (P.map Prod.snd))

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [OpensMeasurableSpace Y]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- HSIC is nonnegative, since it is the squared MMD between two measures. -/
theorem hsicDef_nonneg (P : Measure (X × Y)) : 0 ≤ hsicDef (H := H) P :=
  mmdSq_nonneg _ _

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [OpensMeasurableSpace Y]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- If the joint distribution equals the product of its marginals (i.e., X and Y
    are independent), then HSIC equals zero. This follows from MMD²(P, P) = 0. -/
theorem hsicDef_eq_zero_of_independent
    (P : Measure (X × Y))
    (hind : P = (P.map Prod.fst).prod (P.map Prod.snd)) :
    hsicDef (H := H) P = 0 := by
  unfold hsicDef
  -- hind : P = (P.map fst).prod (P.map snd) =: Q
  -- Goal: mmdSq P Q = 0
  -- Strategy: rewrite the first argument P to Q using hind,
  -- then apply mmdSq_self. We use congruence to avoid rewriting
  -- P inside Q (which would cause infinite regress).
  have : mmdSq (H := H) P ((P.map Prod.fst).prod (P.map Prod.snd)) =
      mmdSq (H := H) ((P.map Prod.fst).prod (P.map Prod.snd))
        ((P.map Prod.fst).prod (P.map Prod.snd)) :=
    congr_arg (mmdSq (H := H) · _) hind
  rw [this]
  exact mmdSq_self (H := H) _

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [OpensMeasurableSpace Y]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- **Hilbert-Schmidt Independence Criterion characterization.**
    Under a characteristic kernel on the product space X × Y,
    HSIC(P) = 0 if and only if the joint distribution P equals the product of
    its marginals P_X ⊗ P_Y. This is the key theorem: under a characteristic
    kernel, HSIC = 0 characterizes statistical independence.

    The proof routes through `mmdSq_zero_iff`: HSIC is defined as
    MMD²(P, P_X ⊗ P_Y), so HSIC = 0 ↔ MMD²(P, Q) = 0 with Q = P_X ⊗ P_Y,
    which under characteristic kernels is equivalent to P = Q. -/
theorem hsicDef_zero_iff_independent
    (hchar : IsCharacteristic (H := H) (X := X × Y))
    (P : Measure (X × Y)) :
    hsicDef (H := H) P = 0 ↔ P = (P.map Prod.fst).prod (P.map Prod.snd) := by
  unfold hsicDef
  exact mmdSq_zero_iff hchar P _

end -- noncomputable section
