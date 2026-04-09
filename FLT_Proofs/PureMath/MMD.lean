/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.PureMath.KernelMeanEmbedding

/-!
# Maximum Mean Discrepancy

Pure mathematical infrastructure for the Maximum Mean Discrepancy (MMD) in
reproducing kernel Hilbert spaces (RKHS). The MMD squared between two measures
P and Q is defined as the squared RKHS norm of the difference of their kernel
mean embeddings: MMD^2(P,Q) = ||mu_P - mu_Q||^2. Combined with the
IsCharacteristic predicate (injectivity of the kernel mean embedding), this
gives a metric on probability measures: MMD^2(P,Q) = 0 iff P = Q.

## Main definitions

- `mmdSq` : the squared maximum mean discrepancy, ||mu_P - mu_Q||^2
- `IsCharacteristic` : predicate asserting that the kernel mean embedding
  is injective (i.e., the kernel is characteristic)

## Main results

- `mmdSq_nonneg` : MMD^2 is nonneg
- `mmdSq_self` : MMD^2(P, P) = 0
- `mmdSq_comm` : MMD^2(P, Q) = MMD^2(Q, P)
- `mmdSq_zero_iff` : under a characteristic kernel, MMD^2(P,Q) = 0 iff P = Q
- `mmdSq_eq_zero` : under a characteristic kernel, MMD^2(P,Q) = 0 implies P = Q

## References

- Gretton, Borgwardt, Rasch, Scholkopf, Smola, "A Kernel Two-Sample Test",
  Journal of Machine Learning Research, 2012
- Muandet, Fukumizu, Sriperumbudur, Scholkopf, "Kernel Mean Embedding of
  Distributions: A Review and Beyond", Foundations and Trends in Machine
  Learning, 2017
-/

noncomputable section

open MeasureTheory RKHS

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H X ℝ]
variable [BoundedKernel H (X := X)]

/-- The squared Maximum Mean Discrepancy between two measures P and Q is the
    squared RKHS norm of the difference of their kernel mean embeddings:
    MMD^2(P,Q) = ||mu_P - mu_Q||^2.
    This is the fundamental quantity for kernel two-sample testing. -/
def mmdSq (P Q : Measure X) : ℝ :=
  ‖kernelMeanEmbedding (H := H) P - kernelMeanEmbedding (H := H) Q‖ ^ 2

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- MMD^2 is nonnegative, since it is the square of a norm. -/
theorem mmdSq_nonneg (P Q : Measure X) : 0 ≤ mmdSq (H := H) P Q :=
  sq_nonneg _

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- MMD^2(P, P) = 0, since mu_P - mu_P = 0 and ||0||^2 = 0. -/
theorem mmdSq_self (P : Measure X) : mmdSq (H := H) P P = 0 := by
  unfold mmdSq
  rw [sub_self, norm_zero, sq, mul_zero]

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- MMD^2 is symmetric: MMD^2(P,Q) = MMD^2(Q,P).
    This follows from ||a - b|| = ||b - a|| (norm_sub_rev). -/
theorem mmdSq_comm (P Q : Measure X) : mmdSq (H := H) P Q = mmdSq (H := H) Q P := by
  unfold mmdSq
  rw [norm_sub_rev]

/-- A kernel is characteristic if its kernel mean embedding is injective:
    distinct measures have distinct embeddings. This is the condition under
    which MMD^2 = 0 implies equality of measures. -/
def IsCharacteristic : Prop :=
  Function.Injective (kernelMeanEmbedding (H := H) (X := X))

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- Under a characteristic kernel, MMD^2(P,Q) = 0 if and only if P = Q.
    Forward direction: the chain is
      ||mu_P - mu_Q||^2 = 0 -> ||mu_P - mu_Q|| = 0 -> mu_P - mu_Q = 0
      -> mu_P = mu_Q -> P = Q (by injectivity).
    Backward direction: P = Q -> mmdSq_self. -/
theorem mmdSq_zero_iff
    (hchar : IsCharacteristic (H := H) (X := X))
    (P Q : Measure X) :
    mmdSq (H := H) P Q = 0 ↔ P = Q := by
  constructor
  · -- Forward: MMD^2 = 0 -> P = Q
    intro h
    -- Step 1: ||mu_P - mu_Q||^2 = 0 -> ||mu_P - mu_Q|| = 0
    have h1 : ‖kernelMeanEmbedding (H := H) P - kernelMeanEmbedding (H := H) Q‖ = 0 := by
      unfold mmdSq at h
      rwa [sq_eq_zero_iff] at h
    -- Step 2: ||mu_P - mu_Q|| = 0 -> mu_P - mu_Q = 0
    have h2 : kernelMeanEmbedding (H := H) P - kernelMeanEmbedding (H := H) Q = 0 :=
      norm_eq_zero.mp h1
    -- Step 3: mu_P - mu_Q = 0 -> mu_P = mu_Q
    have h3 : kernelMeanEmbedding (H := H) P = kernelMeanEmbedding (H := H) Q :=
      sub_eq_zero.mp h2
    -- Step 4: mu_P = mu_Q -> P = Q (by injectivity)
    exact hchar h3
  · -- Backward: P = Q -> MMD^2 = 0
    intro h
    rw [h]
    exact mmdSq_self Q

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- Under a characteristic kernel, MMD^2(P,Q) = 0 implies P = Q.
    This is the forward direction of mmdSq_zero_iff extracted for convenience. -/
theorem mmdSq_eq_zero
    (hchar : IsCharacteristic (H := H) (X := X))
    {P Q : Measure X}
    (h : mmdSq (H := H) P Q = 0) :
    P = Q :=
  (mmdSq_zero_iff hchar P Q).mp h

end -- noncomputable section
