/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.PureMath.ChoquetCapacity
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Real

/-!
# Analytic Sets are NullMeasurableSet

Bridge from analytic sets to null-measurability via Choquet capacity theory.
This file is independent of learning theory and is a candidate for contribution to Mathlib.

## Main results

- `AnalyticSet.exists_isCompact_measureReal_gt`: inner approximation for analytic sets
- `analyticSet_nullMeasurableSet`: analytic sets are null-measurable for finite Borel measures
-/

open MeasureTheory Set

theorem MeasureTheory.AnalyticSet.exists_isCompact_measureReal_gt
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ μ.real s < μ.real K + ε := by
  intro ε hε
  have hcap := hs.compactCap_eq (μ := μ)
  have hfin : μ s ≠ ⊤ := measure_ne_top μ s
  have hε_ennreal : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hε_ne_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Get K with μ s < μ K + ε in ENNReal
  -- By contradiction: if all r ∈ S satisfy r + ε ≤ μ s, then sSup S + ε ≤ μ s,
  -- but sSup S = μ s, contradiction.
  have hmem : ∃ r ∈ {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K},
      μ s < r + ENNReal.ofReal ε := by
    by_contra h
    push_neg at h
    -- Every r in S satisfies r + ε ≤ μ s, hence r ≤ μ s - ε
    have hbound : sSup {r | ∃ K, IsCompact K ∧ K ⊆ s ∧ r = μ K} ≤ μ s - ENNReal.ofReal ε := by
      apply sSup_le
      intro r hr
      exact ENNReal.le_sub_of_add_le_right hε_ne_top (h r hr)
    -- But sSup S = compactCap μ s = μ s, so μ s ≤ μ s - ε
    have : MeasureTheory.compactCap μ s = sSup {r | ∃ K, IsCompact K ∧ K ⊆ s ∧ r = μ K} := rfl
    rw [← this, hcap] at hbound
    -- μ s - ε < μ s when μ s ≠ 0 and ε ≠ 0 and μ s ≠ ⊤
    by_cases hμs : μ s = 0
    · -- When μ s = 0, use K = ∅: μ ∅ = 0 = μ s, so μ s < μ ∅ + ε iff 0 < ε, which is true.
      -- So the by_contra path is impossible when μ s = 0: h says ∀ r ∈ S, r + ε ≤ 0 = μ s,
      -- but 0 ∈ S (via K = ∅) and 0 + ε = ε > 0 = μ s, contradiction.
      have hmem : (0 : ENNReal) ∈ {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K} :=
        ⟨∅, isCompact_empty, Set.empty_subset _, by simp⟩
      have hle := h 0 hmem
      rw [hμs, zero_add] at hle
      exact absurd hle (not_le.mpr hε_ennreal)
    · exact absurd hbound (not_le.mpr (ENNReal.sub_lt_self hfin hμs hε_ennreal.ne'))
  obtain ⟨r, ⟨K, hKc, hKs, rfl⟩, hlt⟩ := hmem
  refine ⟨K, hKc, hKs, ?_⟩
  have hKfin : μ K ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hKs)
  -- Convert: μ s < μ K + ofReal ε  →  (μ s).toReal < (μ K).toReal + ε
  have hadd_ne_top : μ K + ENNReal.ofReal ε ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨hKfin, hε_ne_top⟩
  rw [Measure.real, Measure.real]
  calc (μ s).toReal < (μ K + ENNReal.ofReal ε).toReal :=
        (ENNReal.toReal_lt_toReal hfin hadd_ne_top).mpr hlt
    _ = (μ K).toReal + ε := by
        rw [ENNReal.toReal_add hKfin hε_ne_top, ENNReal.toReal_ofReal hε.le]

/-! ## Main theorem: analytic → NullMeasurableSet -/

theorem analyticSet_nullMeasurableSet
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    MeasureTheory.NullMeasurableSet s μ := by
  classical
  obtain ⟨t, hst, ht_meas, ht_eq⟩ := MeasureTheory.exists_measurable_superset μ s
  have hzero : μ (t \ s) = 0 := by
    by_contra hne
    have hfin_diff : μ (t \ s) ≠ ⊤ := measure_ne_top μ _
    have hpos : 0 < μ.real (t \ s) := ENNReal.toReal_pos hne hfin_diff
    obtain ⟨K, hKc, hKs, hKapprox⟩ :=
      hs.exists_isCompact_measureReal_gt (μ := μ) (μ.real (t \ s) / 2) (by positivity)
    have hKt : K ⊆ t := fun x hx => hst (hKs hx)
    have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
    -- μ.real(t \ K) = μ.real t - μ.real K (since K ⊆ t, K measurable)
    have hdiff_eq : μ.real (t \ K) = μ.real t - μ.real K :=
      measureReal_diff hKt hKmeas
    -- μ.real t = μ.real s (from ht_eq)
    have ht_real : μ.real t = μ.real s := by
      simp only [Measure.real]; rw [ht_eq]
    -- t \ s ⊆ t \ K when K ⊆ s
    have hsub : t \ s ⊆ t \ K := Set.diff_subset_diff_right hKs
    have hle : μ.real (t \ s) ≤ μ.real (t \ K) :=
      measureReal_mono hsub
    -- Combine: μ.real(t \ s) ≤ μ.real t - μ.real K = μ.real s - μ.real K
    -- But hKapprox: μ.real s < μ.real K + μ.real(t \ s)/2
    -- So μ.real s - μ.real K < μ.real(t \ s)/2
    -- And μ.real(t \ s) ≤ μ.real s - μ.real K < μ.real(t \ s)/2
    -- Contradiction: μ.real(t \ s) < μ.real(t \ s)/2
    linarith
  have h_ae : s =ᵐ[μ] t := by
    rw [Filter.eventuallyEq_comm, ae_eq_set]
    exact ⟨hzero, by simp [Set.diff_eq_empty.mpr hst]⟩
  exact ht_meas.nullMeasurableSet.congr h_ae.symm
