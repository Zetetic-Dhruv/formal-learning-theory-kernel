/-
  FLT_Proofs/Meta/BridgeTests.lean

  10 smoke tests for the proof operad world model + bridge_search tactic.
  Tests cover: typing judgments, failure diagnostics, paradigm classification,
  tactic behavior on real FLT goals, and the four-gate quality model.
-/

import WorldModel.BridgeTactic
import WorldModel.ProofOperadTheorems

-- ============================================================
-- Test 1: PAC pipeline types end-to-end
-- The PAC characterization decomposes as GrowthConstruction >> MeasureBridge >> UCToPAC
-- ============================================================

#check @pac_pipeline_types  -- should print: HasType fltTheory stratBuildThenBridge iFiniteVCDim [iPACLearnable]

/-- PAC pipeline output is exactly [iPACLearnable]. -/
example : ∃ p, HasType fltTheory p iFiniteVCDim [iPACLearnable] :=
  ⟨stratBuildThenBridge, pac_pipeline_types⟩

-- ============================================================
-- Test 2: DST pipeline types end-to-end
-- AnalyticProjection >> CompactApproximation
-- ============================================================

example : ∃ p, HasType fltTheory p iBorelParam [iNullMeasBadEvent] :=
  ⟨stratProjectThenApprox, dst_pipeline_types⟩

-- ============================================================
-- Test 3: Online pipeline — single generator suffices
-- ============================================================

example : ∃ p, HasType fltTheory p iFiniteLDim [iOnlineLearnable] :=
  ⟨stratPotentialThenBound, online_pipeline_types⟩

-- ============================================================
-- Test 4: Gold pipeline types
-- ============================================================

example : ∃ p, HasType fltTheory p iEXLearnable [iContradiction] :=
  ⟨stratLocking, gold_pipeline_types⟩

-- ============================================================
-- Test 5: Separation pipeline types — two outputs
-- ============================================================

example : ∃ p, HasType fltTheory p iMeasurableHyps [iWBVCMeasTarget, iNotKrappWirth] :=
  ⟨stratWitnessSeparation, separation_pipeline_types⟩

-- ============================================================
-- Test 6: Bayesian pipeline types
-- ============================================================

example : ∃ p, HasType fltTheory p iPerHypBound [iPACBayes] :=
  ⟨stratJensenChain, bayes_pipeline_types⟩

-- ============================================================
-- Test 7: FD3 negative typing — MeasureBridge rejected without MeasurableConceptClass
-- ============================================================

/-- Without MeasurableConceptClass, MeasureBridge is inadmissible. -/
example : ∃ r, fltTheory.admissible
    ⟨"GrowthBound_noMCC", [.pac], ["C", "hC_vcdim"], "GrowthFunction_le_poly"⟩
    genMeasureBridge = .error r :=
  fd3_blocks_measure_bridge

-- ============================================================
-- Test 8: Paradigm lock — no universal generator
-- ============================================================

/-- No generator in fltTheory spans PAC ∧ Online ∧ Gold. -/
example : ¬ ∃ g ∈ fltTheory.generators,
    Paradigm.pac ∈ g.paradigm ∧ Paradigm.online ∈ g.paradigm ∧ Paradigm.gold ∈ g.paradigm :=
  no_universal_generator

-- ============================================================
-- Test 9: Corpus-relative completeness — all 6 major pipelines type
-- ============================================================

/-- Every entry in majorPipelines has a well-typed plan. -/
example : ∀ entry ∈ majorPipelines,
    HasType fltTheory entry.1 entry.2.1 entry.2.2 :=
  corpus_relative_completeness

-- ============================================================
-- Test 10: bridge_search tactic on a trivial goal (graceful degradation)
-- The tactic should report "no bridge found" and leave the goal open
-- ============================================================

example : True := by
  bridge_search  -- logs warning: no bridge found
  trivial        -- closes the remaining goal

-- ============================================================
-- Quality model tests (bonus)
-- ============================================================

/-- A step with all four gates passing is funnel-valid. -/
example : (StepQuality.mk true true true true).funnelValid = true := by rfl

/-- A step with robustness but no completion violates the funnel. -/
example : (StepQuality.mk true true false true).funnelValid = false := by rfl

/-- The benchmark's typical partial: compliance + validity OK, completion + robustness fail. -/
example : (StepQuality.mk true true false false).funnelValid = true := by rfl

/-- Interface widening: dropping a premise widens. -/
example : Interface.widens
    ⟨"A", [.pac], ["C", "hC_vcdim", "MeasurableConceptClass"], "X"⟩
    ⟨"A", [.pac], ["C", "hC_vcdim"], "X"⟩ = true := by rfl

/-- Generator robustness: UCToPAC on iHasUC is NOT robust —
    removing MeasurableConceptClass from premises triggers FD3 upstream.
    This is correct: the PAC pipeline depends on measurability. -/
example : Generator.isRobust fltTheory genUCToPAC iHasUC = false := by native_decide

/-- Generator robustness: Adversary on iFiniteLDim is also NOT robust —
    removing "C" from premises causes input mismatch.
    This is correct: every domain generator references C. -/
example : Generator.isRobust fltTheory genAdversary iFiniteLDim = false := by native_decide

/-- Structural generators ARE robust: Contrapose on iGoal (empty premises). -/
example : Generator.isRobust fltTheory genContrapose iGoal = true := by native_decide
