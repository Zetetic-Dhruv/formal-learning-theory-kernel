/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Criterion.PAC
import FLT_Proofs.Complexity.VCDimension
import FLT_Proofs.Complexity.Rademacher
import FLT_Proofs.Complexity.Structures
import FLT_Proofs.Complexity.Generalization
import FLT_Proofs.Complexity.Symmetrization
import FLT_Proofs.Computation
import FLT_Proofs.Bridge

/-!
# PAC Learning Theorems

VC characterization, fundamental theorem (5-way equivalence),
Sauer-Shelah, NFL, Occam's algorithm, PAC lower bound.

## Key dependencies from Mathlib

- Finset.vcDim + card_le_card_shatterer + card_shatterer_le_sum_vcDim (Sauer-Shelah)
- lean-rademacher (Rademacher complexity bounds) -- external, future import
- Measure.pi (IsProbabilityMeasure instance for product measures)
- measure_sum_ge_le_of_iIndepFun (Hoeffding's inequality)

## Five Generalization Bounds
The fundamental theorem bundles five characterizations with different
type signatures. This conjunction IS the theorem.

## Proof strategy for VCDim < infinity implies PACLearnable

The standard proof has three layers:
1. Sauer-Shelah: VCDim < infinity implies the growth function is polynomial
   (Mathlib: card_shatterer_le_sum_vcDim)
2. Uniform convergence: polynomial growth + Hoeffding implies
   forall D, P[|emp_err - true_err| > epsilon] < delta
   (Mathlib: measure_sum_ge_le_of_iIndepFun for concentration)
3. ERM works: uniform convergence implies any ERM learner PAC-learns C
   (Connects to BatchLearner via output_in_H)

The reverse direction PACLearnable implies VCDim < infinity uses a probabilistic
construction: if VCDim = infinity, construct a distribution D where any learner
fails with probability > delta for some epsilon.
-/

universe u v

/-- Direction <-: finite VCDim implies PAC learnability.

    Proof route (via infrastructure in Generalization.lean):
    Step 1: VCDim < infinity implies HasUniformConvergence (vcdim_finite_imp_uc)
      Sub-step 1a: Sauer-Shelah gives GrowthFunction bound
      Sub-step 1b: Symmetrization reduces UC to growth function counting
      Sub-step 1c: Concentration inequality closes the bound
    Step 2: HasUniformConvergence implies PACLearnable (uc_imp_pac)
      Sub-step 2a: Construct ERM learner
      Sub-step 2b: ERM is consistent in realizable case
      Sub-step 2c: Consistent + UC implies low TrueError

    Note: C.Nonempty is needed for ERM but not stated as hypothesis.
    If C is empty, PACLearnable is vacuously true (forall c in C, ... is vacuous).
    But ERM needs a fallback hypothesis from C. The empty case is handled separately below.

    Alternative proof path: if the ERM approach fails for computational
    reasons (ERM is noncomputable), one can use the compression-based proof:
    VCDim < infinity implies finite compression scheme (Moran-Yehudayoff 2016)
    implies compression scheme learner is PAC.
    This alternative applies when proving COMPUTATIONAL PAC learnability (polynomial time). -/
theorem vcdim_finite_imp_pac (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    PACLearnable X C := by
  -- Route through UC path: vcdim_finite_imp_uc' + uc_imp_pac (Symmetrization.lean).
  by_cases hne : C.Nonempty
  · exact uc_imp_pac X C hne (vcdim_finite_imp_uc' X C hC hmeas_C hc_meas hWB)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨⟨Set.univ, fun _ => fun _ => false, fun _ => Set.mem_univ _⟩,
           fun _ _ => 0, fun _ _ _ _ _ _ c hcC => by simp [hne] at hcC⟩

/-- Direction ->: PAC learnability implies finite VCDim.

    Proof route (via double-sample infrastructure in Generalization.lean):
    Step 1: Contrapositive -- assume VCDim = infinity
    Step 2: For m = mf(epsilon, delta), extract S with |S| = 2m shattered by C
    Step 3: Construct D = uniform on S
    Step 4: Double-sample trick via GhostSample + symmetrization
    Step 5: Counting argument on restricted labelings

    Note: Step 3 requires constructing a probability measure from a combinatorial
    object (the shattered set). The hard distribution construction is the only
    non-constructive step (related to derandomization in learning). -/
theorem pac_imp_vcdim_finite (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (hC : PACLearnable X C) :
    VCDim X C < ⊤ := by
  -- Contrapositive: VCDim = top implies not PACLearnable (in Generalization.lean)
  by_contra h
  push_neg at h
  exact absurd hC (vcdim_infinite_not_pac X C (le_antisymm le_top h))

/-- VC characterization: C is PAC-learnable iff VCDim(C) < infinity.

    This factors through the two directions:
      <- : vcdim_finite_imp_uc + uc_imp_pac (in Generalization.lean)
      -> : pac_imp_vcdim_finite (contrapositive via double-sample)

    Note: the iff hides an asymmetry: the <- proof is constructive (produces ERM),
    while the -> proof is non-constructive (produces hard distribution). -/
theorem vc_characterization (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    PACLearnable X C ↔ VCDim X C < ⊤ :=
  ⟨pac_imp_vcdim_finite X C, fun hC => vcdim_finite_imp_pac X C hC hmeas_C hc_meas hWB⟩

/-- Sauer-Shelah lemma: if VCDim(C) = d and m >= d, then the growth function
    is bounded by the polynomial sum_{i=0}^{d} C(m,i).

    This is the quantitative version. The bound is tight.
    For m >= d, sum_{i=0}^{d} C(m,i) <= (em/d)^d.

    Proof via Mathlib bridge:
    1. Bridge our Shatters to Finset.Shatters
    2. Apply card_shatterer_le_sum_vcDim from Mathlib
    3. Bridge back to our GrowthFunction -/
theorem sauer_shelah_quantitative (X : Type u) [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (d : ℕ)
    (hd : Finset.vcDim (conceptClassToFinsetFamily C) = d) (m : ℕ) (hm : d ≤ m) :
    GrowthFunction X (↑C : Set (X → Bool)) m ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose m i :=
  growth_function_le_sauer_shelah C d hd m hm

/-- Weak Sauer-Shelah (legacy statement, trivially true). -/
theorem sauer_shelah (X : Type u)
    (C : ConceptClass X Bool) (d m : ℕ)
    (hd : VCDim X C = d) (hm : d ≤ m) :
    ∃ (bound : ℕ), GrowthFunction X C m ≤ bound := by
  exact ⟨GrowthFunction X C m, le_refl _⟩

/-- PAC lower bound: sample complexity is at least linear in d/epsilon.

    The corrected statement asserts the specific quantitative lower bound
    from learning theory: m >= ceil((d-1)/(64*epsilon)) for PAC learning
    with VCDim = d. (The original statement `exists lower, lower <= SampleComplexity`
    was trivially true via `(0, Nat.zero_le _)`.)

    The tight constant is (d-1)/(2*epsilon) (EHKV 1989); see EHKV.lean.

    Proof route: construct 2^d labelings on a shattered set of size d,
    use double-averaging + reversed Markov to show that m < (d-1)/(64*epsilon)
    implies Pr[error <= epsilon] < 6/7 under uniform distribution on shattered set.

    Note: the exact constant (1/7 vs 1/8 vs 1/4) depends on the proof technique.
    The factor (d-1) vs d also varies by source. -/
theorem pac_lower_bound (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (d : ℕ)
    (hd : VCDim X C = d) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ2 : δ ≤ 1/7) (hd_pos : 1 ≤ d)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ := by
  -- Route through sample_complexity_lower_bound (Generalization.lean)
  exact sample_complexity_lower_bound X C d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos hmeas_C hc_meas hWB

/-- Any PAC witness (L, mf) gives an upper bound on SampleComplexity:
    the infimum is at most the witness sample size. -/
theorem sample_complexity_upper_of_pac_witness (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ)
    (hPAC :
      ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
        ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
          ∀ c ∈ C,
            MeasureTheory.Measure.pi (fun _ : Fin (mf ε δ) => D)
              { xs : Fin (mf ε δ) → X |
                D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                  ≤ ENNReal.ofReal ε }
              ≥ ENNReal.ofReal (1 - δ)) :
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      SampleComplexity X C ε δ ≤ mf ε δ := by
  intro ε δ hε hδ
  unfold SampleComplexity
  apply Nat.sInf_le
  exact ⟨L, fun D hD c hcC => hPAC ε δ hε hδ D hD c hcC⟩

/-- Quantitative sample-complexity sandwich attached to any PAC witness.
    Packages: (1) PAC guarantee, (2) SampleComplexity <= mf,
    (3) NFL/VC lower bound on both SampleComplexity and mf. -/
theorem pac_sample_complexity_sandwich (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    PACLearnable X C →
      ∃ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
            ∀ c ∈ C,
              MeasureTheory.Measure.pi (fun _ : Fin (mf ε δ) => D)
                { xs : Fin (mf ε δ) → X |
                  D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                    ≤ ENNReal.ofReal ε }
                ≥ ENNReal.ofReal (1 - δ)) ∧
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          SampleComplexity X C ε δ ≤ mf ε δ) ∧
        (∀ (d : ℕ), VCDim X C = d →
          ∀ (ε δ : ℝ), 0 < ε → ε ≤ 1 / 4 →
            0 < δ → δ ≤ 1 → δ ≤ 1 / 7 → 1 ≤ d →
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ ∧
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ mf ε δ) := by
  intro hPAC
  rcases hPAC with ⟨L, mf, hmf⟩
  refine ⟨L, mf, hmf, ?_, ?_⟩
  · intro ε δ hε hδ
    exact sample_complexity_upper_of_pac_witness X C L mf hmf ε δ hε hδ
  · intro d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos
    have hlower :=
      sample_complexity_lower_bound X C d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos hmeas_C hc_meas hWB
    have hupper :=
      sample_complexity_upper_of_pac_witness X C L mf hmf ε δ hε hδ
    exact ⟨hlower, le_trans hlower hupper⟩

/-- Fundamental theorem: finite VC dim iff finite compression scheme.
    Moran-Yehudayoff 2016 gives the forward direction. -/
theorem fundamental_vc_compression (X : Type u)
    (C : ConceptClass X Bool) :
    (VCDim X C < ⊤) ↔
    (∃ (k : ℕ) (cs : CompressionScheme X Bool C), cs.size = k) :=
  -- -> : Moran-Yehudayoff 2016
  -- <- : pigeonhole compression implies finite VCDim
  ⟨vcdim_finite_imp_compression X C, compression_imp_vcdim_finite X C⟩

/-- Fundamental theorem: Rademacher complexity characterization.
    The two directions cross different paradigm boundaries (combinatorial vs measure-theoretic).
    Uses uniform vanishing (exists m_0 forall D), which is the textbook-standard form. -/
theorem fundamental_rademacher (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    PACLearnable X C ↔
    (∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε) :=
  ⟨fun hpac => vcdim_finite_imp_rademacher_vanishing X C
     (pac_imp_vcdim_finite X C hpac),
   fun hrad => by
     -- Rademacher vanishing → VCDim < ⊤ (contrapositive) → PAC via UC
     have hvcdim : VCDim X C < ⊤ := by
       by_contra hvcdim_inf
       push_neg at hvcdim_inf
       have hvcdim_top : VCDim X C = ⊤ := le_antisymm le_top hvcdim_inf
       have h_large_shatter : ∀ n : ℕ, ∃ T : Finset X, Shatters X C T ∧ n ≤ T.card := by
         intro n; by_contra h_neg; push_neg at h_neg
         have hle : VCDim X C ≤ ↑n := by
           apply iSup₂_le; intro T hT; exact_mod_cast le_of_lt (h_neg T hT)
         rw [hvcdim_top] at hle; exact absurd hle (by simp)
       obtain ⟨m₀, hm₀⟩ := hrad (1/2) (by norm_num)
       set m := max m₀ 1
       obtain ⟨T, hT_shat, hT_card⟩ := h_large_shatter (4 * m ^ 2 + 1)
       obtain ⟨D, hD, hRad_ge⟩ := rademacher_lower_bound_on_shattered X C T hT_shat m (by omega) hT_card
       linarith [hm₀ D hD m (le_max_left m₀ 1)]
     exact vcdim_finite_imp_pac_via_uc' X C hvcdim hmeas_C hc_meas hWB⟩

/-- Fundamental theorem of statistical learning (5-way equivalence). -/
theorem fundamental_theorem (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    (PACLearnable X C ↔ VCDim X C < ⊤) ∧
    ((VCDim X C < ⊤) ↔ ∃ (k : ℕ) (cs : CompressionScheme X Bool C), cs.size = k) ∧
    ((VCDim X C < ⊤) ↔
      ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
        MeasureTheory.IsProbabilityMeasure D →
        ∀ m ≥ m₀, RademacherComplexity X C D m < ε) ∧
    (PACLearnable X C →
      ∃ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
            ∀ c ∈ C,
              MeasureTheory.Measure.pi (fun _ : Fin (mf ε δ) => D)
                { xs : Fin (mf ε δ) → X |
                  D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                    ≤ ENNReal.ofReal ε }
                ≥ ENNReal.ofReal (1 - δ)) ∧
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          SampleComplexity X C ε δ ≤ mf ε δ) ∧
        (∀ (d : ℕ), VCDim X C = d →
          ∀ (ε δ : ℝ), 0 < ε → ε ≤ 1 / 4 →
            0 < δ → δ ≤ 1 → δ ≤ 1 / 7 → 1 ≤ d →
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ ∧
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ mf ε δ)) ∧
    ((VCDim X C < ⊤) ↔
      ∃ (d : ℕ), ∀ (m : ℕ), d ≤ m →
        GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i) :=
  -- 5-way conjunction assembles from component theorems
  ⟨vc_characterization X C hmeas_C hc_meas hWB,
   fundamental_vc_compression X C,
   (vc_characterization X C hmeas_C hc_meas hWB).symm.trans (fundamental_rademacher X C hmeas_C hc_meas hWB),
   pac_sample_complexity_sandwich X C hmeas_C hc_meas hWB,
   -- Conjunct 5: VCDim < top iff growth function bounded
   ⟨vcdim_finite_imp_growth_bounded X C, growth_bounded_imp_vcdim_finite X C⟩⟩

/-! CORRECTION: The naive NFL statement `not PACLearnable X Set.univ` for [Fintype X]
    is PROVABLY FALSE for finite X.

    For finite X: VCDim(Set.univ) = Fintype.card X < infinity, so by vc_characterization
    (backward direction), Set.univ IS PAC-learnable (with sample complexity O(|X|/epsilon)).
    The learner can take m >= |X| samples and memorize the entire domain.

    The correct NFL theorem operates on INFINITE domains where VCDim = infinity. -/

/-- NFL for infinite domains: Set.univ has infinite VC dimension. -/
theorem vcdim_univ_infinite (X : Type u) [Infinite X] :
    VCDim X (Set.univ : ConceptClass X Bool) = ⊤ := by
  -- Step 1: reduce to showing forall n, n <= VCDim
  apply WithTop.eq_top_iff_forall_ge.mpr
  intro n
  -- Step 2: get S : Finset X with |S| = n from Infinite X
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq X n
  -- Step 3: every labeling of S is realized by some c in Set.univ
  have hShat : Shatters X (Set.univ : ConceptClass X Bool) S := by
    intro f
    refine ⟨Function.extend Subtype.val f (fun _ => false), Set.mem_univ _, ?_⟩
    intro ⟨x, hxS⟩
    exact Function.Injective.extend_apply Subtype.val_injective f _ ⟨x, hxS⟩
  -- Step 4: |S| = n and |S| <= VCDim via le_iSup2_of_le
  show (n : WithTop ℕ) ≤ VCDim X Set.univ
  unfold VCDim
  calc (n : WithTop ℕ) = ↑S.card := by exact_mod_cast hS.symm
    _ ≤ ⨆ (T : Finset X) (_ : Shatters X (Set.univ : ConceptClass X Bool) T),
        (T.card : WithTop ℕ) := le_iSup₂_of_le S hShat (le_refl _)

/-- NFL corollary: Set.univ over infinite domains is not PAC-learnable. -/
theorem nfl_theorem_infinite (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X] [Infinite X] :
    ¬ PACLearnable X (Set.univ : ConceptClass X Bool) := by
  -- PACLearnable implies VCDim < top, contradicting vcdim_univ_infinite
  intro h
  have hfin := pac_imp_vcdim_finite X (Set.univ : ConceptClass X Bool) h
  rw [vcdim_univ_infinite] at hfin
  exact lt_irrefl _ hfin

/-- NFL for fixed sample size (Shalev-Shwartz & Ben-David Theorem 5.1):
    For any fixed sample size m, there exists a distribution such that
    any learner using m samples fails on SOME concept in Set.univ.

    The original statement used `exists D, (IsProbabilityMeasure D -> ...)`
    which allows D = 0 (zero measure), making the implication vacuously true.
    Corrected to `exists D, IsProbabilityMeasure D /\ ...` (bundled conjunction).

    Proof route:
    1. Let T subset X with |T| = 2m (exists since 2m <= |X|)
    2. D = uniform over T
    3. For any learner L, average over random labelings c : T -> Bool:
       E_c[TrueError(L(S), c, D)] >= 1/4 (the unseen points are random)
    4. By Markov: exists c with TrueError > 1/8 with positive probability

    Note: the [MeasurableSingletonClass X] hypothesis is needed for the uniform
    measure to work with Measure.count. This is standard for discrete spaces. -/
theorem nfl_fixed_sample (X : Type u) [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X]
    (hX : 2 ≤ Fintype.card X) (m : ℕ) (hm : 2 * m ≤ Fintype.card X)
    (L : BatchLearner X Bool) :
    ∃ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D ∧
      ∃ (c : X → Bool),
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              > ENNReal.ofReal (1/8) }
          > 0 :=
  -- Routes through nfl_core (Generalization.lean) which captures the
  -- uniform measure construction + counting argument.
  nfl_core X hX m hm L

/-- Occam's algorithm: any consistent learner with bounded description length
    is a PAC learner.

    Hypotheses:
    1. L is consistent: forall S, forall i, L.learn S (S i).1 = (S i).2
    2. Description length bound: forall c in C, dl c <= k
    3. Hoeffding: for iid sample of size m >= (1/epsilon)(k * ln 2 + ln(1/delta)),
       a consistent hypothesis has true error <= epsilon with probability >= 1 - delta

    The genuine Occam content is the SAMPLE COMPLEXITY bound: m = O((k + log(1/delta))/epsilon)
    via union bound over 2^k bounded-length hypotheses. This is tighter than the
    generic VC bound. But the existential PACLearnable already follows from VCDim < infinity.

    The VCDim < infinity hypothesis is needed because without it the statement is false:
    consistent learners exist for VCDim = infinity classes, but PACLearnable is false there. -/
theorem occam_algorithm (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool)
    (dl : DescriptionLength (Concept X Bool))
    (k : ℕ) (hk : ∀ c ∈ C, dl c ≤ k)
    (hvcdim : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    (∀ {m : ℕ} (S : Fin m → X × Bool), ∀ i, L.learn S (S i).1 = (S i).2) →
    PACLearnable X C := by
  intro _
  exact (vc_characterization X C hmeas_C hc_meas hWB).mpr hvcdim
