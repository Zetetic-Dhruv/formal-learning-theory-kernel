/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Kernel Mean Embeddings

Pure mathematical infrastructure for kernel mean embeddings in reproducing kernel
Hilbert spaces (RKHS). The kernel mean embedding maps a probability measure to an
element of the RKHS via the Bochner integral of kernel sections, and satisfies
the reproducing property relating inner products in the RKHS to expectations
under the measure.

## Main definitions

- `BoundedKernel` : typeclass certifying a uniform bound on RKHS kernel sections
- `kernelMeanEmbedding` : the Bochner integral ∫ kerFun H x 1 ∂P, an element of H

## Main results

- `kernelMeanEmbedding_integrable` : bounded kernel sections are integrable under
  finite measures
- `kernelMeanEmbedding_reproducing` : the reproducing property ⟪μ_P, f⟫ = ∫ f dP
- `kernelMeanEmbedding_norm_le` : norm bound ‖μ_P‖ ≤ C for probability measures

## References

- Muandet, Fukumizu, Sriperumbudur, Scholkopf, "Kernel Mean Embedding of Distributions:
  A Review and Beyond", Foundations and Trends in Machine Learning, 2017
-/

noncomputable section

open MeasureTheory RKHS

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H X ℝ]

/-- A bounded kernel is an RKHS whose kernel sections have uniformly bounded norms.
    This is the integrability certificate: bounded kernel sections are integrable
    under any finite measure. -/
class BoundedKernel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {X : Type*} [RKHS ℝ H X ℝ] where
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_kerFun_le : ∀ x : X, ‖kerFun H x (1 : ℝ)‖ ≤ bound

variable [BoundedKernel H (X := X)]

/-- The kernel mean embedding of a measure P is the Bochner integral of the kernel
    sections x ↦ kerFun H x 1 under P. This is an element of H. -/
def kernelMeanEmbedding (P : Measure X) : H :=
  ∫ x, kerFun H x (1 : ℝ) ∂P

/-- Bounded kernel sections are integrable under any finite measure, given that
    the kernel section map x ↦ kerFun H x 1 is continuous. Continuity provides
    AEStronglyMeasurable, and the uniform norm bound with finite measure gives
    integrability. -/
lemma kernelMeanEmbedding_integrable
    (P : Measure X) [IsFiniteMeasure P]
    (hcont : Continuous (fun x => kerFun H x (1 : ℝ))) :
    Integrable (fun x => kerFun H x (1 : ℝ)) P := by
  apply MemLp.integrable le_top
  exact memLp_top_of_bound
    hcont.aestronglyMeasurable
    (BoundedKernel.bound (H := H) (X := X))
    (Filter.Eventually.of_forall (BoundedKernel.norm_kerFun_le (H := H) (X := X)))

/-- Helper: ⟪a, 1⟫_ℝ = a in the real inner product space ℝ. -/
private lemma inner_real_one_right (a : ℝ) : @inner ℝ ℝ _ a 1 = a := by
  change 1 * starRingEnd ℝ a = a
  simp

/-- Helper: ⟪1, a⟫_ℝ = a in the real inner product space ℝ. -/
private lemma inner_real_one_left (a : ℝ) : @inner ℝ ℝ _ 1 a = a := by
  rw [real_inner_comm]
  exact inner_real_one_right a

/-- The reproducing property of the kernel mean embedding:
    ⟪μ_P, f⟫ = ∫ x, f x ∂P for all f ∈ H.

    This is the key theorem that makes the kernel mean embedding useful:
    it converts inner products in the RKHS to expectations under the measure.

    The proof routes through three Mathlib lemmas:
    1. `real_inner_comm` to orient the inner product for integral_inner
    2. `integral_inner` to swap the inner product and Bochner integral
    3. `inner_kerFun` (the RKHS reproducing property) to evaluate the integrand -/
theorem kernelMeanEmbedding_reproducing
    (P : Measure X) [IsFiniteMeasure P]
    (hcont : Continuous (fun x => kerFun H x (1 : ℝ)))
    (f : H) :
    @inner ℝ H _ (kernelMeanEmbedding (H := H) P) f = ∫ x, f x ∂P := by
  unfold kernelMeanEmbedding
  rw [real_inner_comm]
  rw [← integral_inner (kernelMeanEmbedding_integrable P hcont)]
  congr 1
  ext x
  rw [inner_kerFun, inner_real_one_right]

omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- Bridge lemma: f x equals the inner product of the kernel section with f.
    This connects the function evaluation to the RKHS inner product,
    enabling the Cauchy-Schwarz argument for boundedness. -/
lemma rkhs_eval_eq_inner (f : H) (x : X) :
    (f x : ℝ) = @inner ℝ H _ (kerFun H x (1 : ℝ)) f := by
  -- kerFun_inner gives ⟪kerFun H x 1, f⟫_ℝ = ⟪1, f x⟫_ℝ
  -- inner_real_one_left gives ⟪1, f x⟫_ℝ = f x
  -- Chain: f x = ⟪1, f x⟫_ℝ = ⟪kerFun H x 1, f⟫_ℝ
  rw [← inner_real_one_left (f x)]
  exact (kerFun_inner (𝕜 := ℝ) (H := H) (V := ℝ) x 1 f).symm

omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] in
/-- Pointwise bound on RKHS function evaluations via Cauchy-Schwarz and the
    kernel bound. For any f ∈ H and x ∈ X, ‖f x‖ ≤ C * ‖f‖ where C is the
    kernel bound. The proof routes through the reproducing property
    (f x = ⟪kerFun H x 1, f⟫) and Cauchy-Schwarz in H. -/
lemma norm_apply_le_bound_mul_norm (f : H) (x : X) :
    ‖f x‖ ≤ BoundedKernel.bound (H := H) (X := X) * ‖f‖ := by
  rw [Real.norm_eq_abs, rkhs_eval_eq_inner f x]
  calc |@inner ℝ H _ (kerFun H x (1 : ℝ)) f|
      ≤ ‖kerFun H x (1 : ℝ)‖ * ‖f‖ := abs_real_inner_le_norm _ _
    _ ≤ BoundedKernel.bound (H := H) (X := X) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (BoundedKernel.norm_kerFun_le x) (norm_nonneg _)

omit [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology H]
  [BoundedKernel H] in
/-- The map x ↦ f x for f ∈ H is continuous when the kernel section map is continuous.
    This follows from f x = ⟪kerFun H x 1, f⟫ (reproducing property) and continuity
    of the inner product with a fixed element composed with the continuous kernel map. -/
lemma continuous_rkhs_apply
    (hcont : Continuous (fun x => kerFun H x (1 : ℝ)))
    (f : H) :
    Continuous (fun x => f x) := by
  have heq : (fun x => f x) = (fun x => @inner ℝ H _ (kerFun H x (1 : ℝ)) f) := by
    ext x; exact rkhs_eval_eq_inner f x
  rw [heq]
  exact hcont.inner continuous_const

omit [SecondCountableTopology H] in
/-- RKHS functions are integrable under any finite measure when the kernel is bounded.
    This follows from the pointwise bound ‖f x‖ ≤ C * ‖f‖ and the finite measure
    condition. Measurability comes from continuity of x ↦ f x (via the reproducing
    property and continuity of the kernel section map). -/
lemma rkhs_fun_integrable
    (P : Measure X) [IsFiniteMeasure P]
    (hcont : Continuous (fun x => kerFun H x (1 : ℝ)))
    (f : H) :
    Integrable (fun x => f x) P := by
  apply MemLp.integrable le_top
  exact memLp_top_of_bound
    (continuous_rkhs_apply hcont f).aestronglyMeasurable
    (BoundedKernel.bound (H := H) (X := X) * ‖f‖)
    (Filter.Eventually.of_forall (norm_apply_le_bound_mul_norm f))

omit [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopology H] in
/-- The norm of the kernel mean embedding is bounded by the kernel bound C
    for probability measures. The proof chains norm_integral_le_integral_norm
    with the pointwise kernel bound and the probability measure normalization.
    Note: this holds unconditionally (no continuity hypothesis needed) because
    norm_integral_le_integral_norm and integral_mono_of_nonneg hold for all
    functions, and the Bochner integral of a non-integrable function is 0. -/
theorem kernelMeanEmbedding_norm_le
    (P : Measure X) [IsProbabilityMeasure P] :
    ‖kernelMeanEmbedding (H := H) P‖ ≤ BoundedKernel.bound (H := H) (X := X) := by
  unfold kernelMeanEmbedding
  calc ‖∫ x, kerFun H x (1 : ℝ) ∂P‖
      ≤ ∫ x, ‖kerFun H x (1 : ℝ)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ _, BoundedKernel.bound (H := H) (X := X) ∂P := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
        · exact integrable_const _
        · exact Filter.Eventually.of_forall (BoundedKernel.norm_kerFun_le (H := H) (X := X))
    _ = BoundedKernel.bound (H := H) (X := X) := by
        rw [integral_const, probReal_univ, one_smul]

end -- noncomputable section
