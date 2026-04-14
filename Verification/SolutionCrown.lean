import Verification.Definitions
import FLT_Proofs.Theorem.PAC
import FLT_Proofs.Complexity.Compression
import FLT_Proofs.PureMath.ApproxMinimax
import FLT_Proofs.Complexity.FiniteSupportUC

noncomputable section

universe u

-- Crown Jewel 1: delegates to fundamental_theorem
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
        GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i) :=
  fundamental_theorem X C

-- Crown Jewel 2: delegates to fundamental_vc_compression_with_info
theorem challenge_fundamental_vc_compression_with_info
    (X : Type u) (C : ConceptClass X Bool) :
    (VCDim X C < ⊤) ↔
    (∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k) :=
  fundamental_vc_compression_with_info X C

-- Crown Jewel 3: delegates to vc_characterization
theorem challenge_vc_characterization (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    [MeasurableConceptClass X C] :
    PACLearnable X C ↔ VCDim X C < ⊤ :=
  vc_characterization X C

-- Crown Jewel 4: delegates to sauer_shelah
theorem challenge_sauer_shelah (X : Type u)
    (C : ConceptClass X Bool) (d m : ℕ)
    (_hd : VCDim X C = d) (_hm : d ≤ m) :
    ∃ (bound : ℕ), GrowthFunction X C m ≤ bound :=
  sauer_shelah X C d m _hd _hm

-- Crown Jewel 5: delegates to mwu_approx_minimax
theorem challenge_mwu_approx_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty R] [Nonempty C]
    [DecidableEq R] [DecidableEq C]
    (M : R → C → Bool) (v ε : ℝ) (hε : 0 < ε)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∃ p : FinitePMF R, ∀ c : C, v - ε ≤ boolGamePayoff M p c :=
  mwu_approx_minimax M v ε hε hrow

-- Crown Jewel 6: delegates to finite_support_vc_approx
theorem challenge_finite_support_vc_approx
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : ℕ) (hT : 0 < T),
      ∀ {H : Type*} [Fintype H] [DecidableEq H]
        (A : Finset (H → Bool)),
        A.boolVCDim ≤ d →
        ∀ μ : FinitePMF H, ∃ hs : Fin T → H,
          ∀ a ∈ A,
            |boolTestExpectation μ a -
              boolTestExpectation (empiricalPMF hT hs) a| ≤ ε :=
  finite_support_vc_approx d ε hε

end -- noncomputable section
