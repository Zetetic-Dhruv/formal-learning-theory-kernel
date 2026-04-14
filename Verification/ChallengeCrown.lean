import Verification.Definitions
import FLT_Proofs.Complexity.Compression

noncomputable section

universe u

-- Crown Jewel 1: Fundamental theorem of statistical learning (5-way equivalence)
-- Source: FLT_Proofs/Theorem/PAC.lean:293
theorem challenge_fundamental_theorem (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    [MeasurableConceptClass X C] :
    (PACLearnable X C ↔ VCDim X C < ⊤) ∧
    ((VCDim X C < ⊤) ↔ ∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k) ∧
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
        GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i) := by
  sorry

-- Crown Jewel 2: Compression with side information (Moran-Yehudayoff 2016)
-- Source: FLT_Proofs/Complexity/Compression.lean:1321
theorem challenge_fundamental_vc_compression_with_info
    (X : Type u) (C : ConceptClass X Bool) :
    (VCDim X C < ⊤) ↔
    (∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k) := by
  sorry

-- Crown Jewel 3: VC characterization (PAC iff VCDim < top)
-- Source: FLT_Proofs/Theorem/PAC.lean:127
theorem challenge_vc_characterization (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    [MeasurableConceptClass X C] :
    PACLearnable X C ↔ VCDim X C < ⊤ := by
  sorry

-- Crown Jewel 4: Sauer-Shelah lemma
-- Source: FLT_Proofs/Theorem/PAC.lean:153
theorem challenge_sauer_shelah (X : Type u)
    (C : ConceptClass X Bool) (d m : ℕ)
    (_hd : VCDim X C = d) (_hm : d ≤ m) :
    ∃ (bound : ℕ), GrowthFunction X C m ≤ bound := by
  sorry

-- Crown Jewel 5: Approximate minimax via MWU regret extraction
-- Source: FLT_Proofs/PureMath/ApproxMinimax.lean:597
theorem challenge_mwu_approx_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty R] [Nonempty C]
    [DecidableEq R] [DecidableEq C]
    (M : R → C → Bool) (v ε : ℝ) (hε : 0 < ε)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∃ p : FinitePMF R, ∀ c : C, v - ε ≤ boolGamePayoff M p c := by
  sorry

-- Crown Jewel 6: Finite-support VC approximation
-- Source: FLT_Proofs/Complexity/FiniteSupportUC.lean:97
theorem challenge_finite_support_vc_approx
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : ℕ) (hT : 0 < T),
      ∀ {H : Type*} [Fintype H] [DecidableEq H]
        (A : Finset (H → Bool)),
        A.boolVCDim ≤ d →
        ∀ μ : FinitePMF H, ∃ hs : Fin T → H,
          ∀ a ∈ A,
            |boolTestExpectation μ a -
              boolTestExpectation (empiricalPMF hT hs) a| ≤ ε := by
  sorry

end -- noncomputable section
