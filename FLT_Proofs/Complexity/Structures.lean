/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Basic
import FLT_Proofs.Learner.Core
import FLT_Proofs.Complexity.VCDimension
import FLT_Proofs.Criterion.Online
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Structured Complexity Measures

Compression schemes, algorithmic stability, multiclass dimensions,
real-valued dimensions, teaching/eluder dimensions, SQ dimension,
KL complexity, margin theory, covering numbers.
-/

universe u v

/-!
## Compression Schemes
-/

/-- A compression scheme of size k for concept class C (Littlestone-Warmuth 1986).
    - `compress` returns `Finset (X × Y)` (actual compressed data points),
      not indices, so that `reconstruct` depends only on the compressed subset
      (enabling the pigeonhole argument for VCDim bounds).
    - `correct` is guarded by C-realizability: the reconstructed hypothesis agrees
      with every sample point when the sample is consistent with some concept in C.
      This matches the standard definition (Littlestone-Warmuth, Moran-Yehudayoff). -/
structure CompressionScheme (X : Type u) (Y : Type v) (C : ConceptClass X Y) where
  /-- Compression: extract ≤ size labeled examples from the sample -/
  compress : {m : ℕ} → (Fin m → X × Y) → Finset (X × Y)
  /-- Reconstruction: produce hypothesis from compressed subset alone -/
  reconstruct : Finset (X × Y) → (X → Y)
  /-- Size of the compressed representation -/
  size : ℕ
  /-- Compressed set is small -/
  compress_small : ∀ {m : ℕ} (S : Fin m → X × Y), (compress S).card ≤ size
  /-- Compressed set is a subset of the sample -/
  compress_sub : ∀ {m : ℕ} (S : Fin m → X × Y),
    ↑(compress S) ⊆ Set.range S
  /-- Correctness: reconstructed hypothesis agrees with every sample point,
      when the sample is C-realizable (∃ c ∈ C agreeing with all labels) -/
  correct : ∀ {m : ℕ} (S : Fin m → X × Y),
    (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) →
    ∀ i : Fin m, reconstruct (compress S) (S i).1 = (S i).2

/-- Unlabeled compression: reconstruction uses only input points, not labels. -/
structure UnlabeledCompression (X : Type u) (Y : Type v) where
  size : ℕ
  compress : {m : ℕ} → (Fin m → X × Y) → Finset (Fin m)
  reconstruct : {m : ℕ} → (Fin m → X) → Finset (Fin m) → Concept X Y
  small : ∀ {m : ℕ} (S : Fin m → X × Y), (compress S).card ≤ size

/-!
## Algorithmic Stability
-/

/-- Algorithmic stability: removing one example changes the loss by at most β. -/
structure AlgorithmicStability (X : Type u) (Y : Type v) where
  /-- The learner whose stability we measure -/
  learner : BatchLearner X Y
  /-- Stability parameter -/
  beta : ℝ
  beta_nonneg : 0 ≤ beta
  loss : LossFunction Y
  /-- Stability: for any sample S and any index i, the loss of L(S) vs L(S\i)
      on any fresh point z differs by at most β.
      S\i denotes the sample with the i-th element removed. -/
  stable : ∀ {m : ℕ} (S : Fin (m + 1) → X × Y) (i : Fin (m + 1)) (z : X × Y),
    |loss (learner.learn S z.1) z.2 -
     loss (learner.learn (fun j => S (Fin.succAbove i j)) z.1) z.2| ≤ beta

/-!
## Multiclass and Real-Valued Extensions
-/

/-- Natarajan dimension: multiclass generalization of VC dimension.
    Largest d such that ∃ S with |S| = d and two witness functions f₀ f₁ : S → Y
    disagreeing everywhere on S, such that for every binary selection h,
    some concept in C picks f₀ or f₁ at each point according to h. -/
noncomputable def NatarajanDim (X : Type u) (Y : Type v) [Fintype Y]
    (C : ConceptClass X Y) : WithTop ℕ :=
  ⨆ (S : Finset X)
    (_ : ∃ (f₀ f₁ : X → Y), (∀ x ∈ S, f₀ x ≠ f₁ x) ∧
      ∀ (h : X → Bool), ∃ c ∈ C, ∀ x ∈ S,
        c x = if h x then f₀ x else f₁ x),
    (S.card : WithTop ℕ)

/-- DS dimension: multiclass shattering where EVERY labeling is realizable.
    Strictly stronger than Natarajan dimension. -/
noncomputable def DSDim (X : Type u) (Y : Type v) [Fintype Y]
    (C : ConceptClass X Y) : WithTop ℕ :=
  ⨆ (S : Finset X)
    (_ : ∀ (f : X → Y), ∃ c ∈ C, ∀ x ∈ S, c x = f x),
    (S.card : WithTop ℕ)

/-- DS dimension ≤ Natarajan dimension: DS-shattering (every labeling realizable)
    is strictly STRONGER than Natarajan-shattering (2-coloring witness), so fewer
    sets satisfy the DS condition, hence DSDim ≤ NatarajanDim.
    Requires |Y| ≥ 2 (Nontrivial Y): when |Y| = 1, Natarajan witnesses f₀ ≠ f₁ cannot exist. -/
theorem DSDim_le_NatarajanDim (X : Type u) (Y : Type v) [Fintype Y] [Nontrivial Y]
    (C : ConceptClass X Y) : DSDim X Y C ≤ NatarajanDim X Y C := by
  obtain ⟨y₀, y₁, hne⟩ := exists_pair_ne Y
  apply iSup₂_le
  intro S hDS
  have hNat : ∃ (f₀ f₁ : X → Y), (∀ x ∈ S, f₀ x ≠ f₁ x) ∧
      ∀ (h : X → Bool), ∃ c ∈ C, ∀ x ∈ S,
        c x = if h x then f₀ x else f₁ x := by
    refine ⟨fun _ => y₀, fun _ => y₁, fun _ _ => hne, fun h => ?_⟩
    obtain ⟨c, hcC, hcS⟩ := hDS (fun x => if h x then y₀ else y₁)
    exact ⟨c, hcC, fun x hxS => hcS x hxS⟩
  exact le_iSup₂_of_le S hNat (le_refl _)

/-- Pseudodimension: real-valued generalization of VC dimension.
    Largest d such that ∃ S with |S| = d and thresholds t, such that
    for every binary labeling, some concept crosses the thresholds accordingly. -/
noncomputable def Pseudodimension (X : Type u) (C : ConceptClass X ℝ) : WithTop ℕ :=
  ⨆ (S : Finset X) (t : X → ℝ)
    (_ : ∀ (b : X → Bool), ∃ c ∈ C, ∀ x ∈ S,
      (b x = true → c x ≥ t x) ∧ (b x = false → c x < t x)),
    (S.card : WithTop ℕ)

/-- Fat-shattering dimension at margin γ > 0.
    Like pseudodimension but with γ-margin on both sides of the threshold. -/
noncomputable def FatShatteringDim (X : Type u) (C : ConceptClass X ℝ)
    (γ : ℝ) (hγ : 0 < γ) : WithTop ℕ :=
  ⨆ (S : Finset X) (t : X → ℝ)
    (_ : ∀ (b : X → Bool), ∃ c ∈ C, ∀ x ∈ S,
      (b x = true → c x ≥ t x + γ) ∧ (b x = false → c x ≤ t x - γ)),
    (S.card : WithTop ℕ)

/-!
## Other Complexity Measures
-/

/-- SQ dimension: largest d such that there exist d concepts in C with
    pairwise small correlations under D. Captures the hardness of learning C
    using only statistical queries (expected values of functions of the sample).
-/
noncomputable def SQDimension (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure D] (τ : ℝ) : WithTop ℕ :=
  ⨆ (S : Finset (Concept X Bool))
    (_ : ↑S ⊆ C ∧ ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ c₂ →
      |∫ x, (if c₁ x = c₂ x then (1 : ℝ) else -1) ∂D| ≤ τ),
    (S.card : WithTop ℕ)

/-- Covering number: minimum number of balls of radius ε (under metric d) to cover C. -/
noncomputable def CoveringNumber (X : Type u) (C : ConceptClass X Bool)
    (d : Concept X Bool → Concept X Bool → ℝ) (ε : ℝ) : ℕ :=
  sInf { k : ℕ | ∃ (S : Finset (Concept X Bool)), S.card ≤ k ∧
    ∀ c, c ∈ C → ∃ s ∈ S, d c s ≤ ε }

/-- Teaching dimension: max over concepts of min teaching set size.
    A teaching set for c ∈ C is a set of labeled examples consistent with c
    that distinguishes c from all other concepts in C. -/
noncomputable def TeachingDim (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (c : Concept X Bool) (_ : c ∈ C),
    ⨅ (T : Finset (X × Bool))
      (_ : (∀ p ∈ T, c p.1 = p.2) ∧
           ∀ c' ∈ C, c' ≠ c → ∃ p ∈ T, c' p.1 ≠ p.2),
      (T.card : WithTop ℕ)

/-- Eluder dimension: length of the longest eluder-independent sequence.
    Each element xᵢ has two concepts in C agreeing on x₁,...,x_{i-1} but
    disagreeing on xᵢ. -/
noncomputable def EluderDim (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (seq : List X)
    (_ : ∀ (i : Fin seq.length),
      ∃ (c₁ c₂ : Concept X Bool), c₁ ∈ C ∧ c₂ ∈ C ∧
        (∀ (j : Fin seq.length), j.val < i.val →
          c₁ (seq[j]) = c₂ (seq[j])) ∧
        c₁ (seq[i]) ≠ c₂ (seq[i])),
    (seq.length : WithTop ℕ)

/-- KL complexity: KL divergence D_KL(posterior ‖ prior).
    Uses the convention 0 · log(0/·) = 0 and · · log(·/0) = +∞
    (the tsum returns 0 for non-summable families). -/
noncomputable def KLComplexity (α : Type*) (prior posterior : α → ℝ) : ℝ :=
  ∑' x, if prior x > 0 ∧ posterior x > 0
    then posterior x * Real.log (posterior x / prior x)
    else 0

/-- Margin theory: framework connecting margins to generalization. -/
structure MarginTheory (X : Type u) where
  margin : ℝ
  margin_pos : 0 < margin
  conceptClass : ConceptClass X ℝ
  bound : ℕ → ℝ

