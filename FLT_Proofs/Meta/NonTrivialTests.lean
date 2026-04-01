/-
  FLT_Proofs/Meta/NonTrivialTests.lean

  Non-trivial tests for TPG_FLT: the proof operad world model.
  Each test exercises a distinct property of the operad that goes beyond
  smoke-testing type signatures.

  Test categories:
  - Negative typing: compositions that SHOULD fail
  - Cross-paradigm: attempts to cross paradigm boundaries
  - Extension mechanism: adding generators to solve gaps
  - Cost model: difficulty ordering on concrete plans
  - Robustness: transport under interface widening
  - Completeness: structural properties of the theory
-/

import FLT_Proofs.Meta.BridgeTactic
import FLT_Proofs.Meta.ProofOperadTheorems

-- ============================================================
-- NT1: Cross-paradigm composition FAILS
-- Trying to feed Online output into PAC generator is ill-typed
-- ============================================================

/-- Cross-paradigm composition is blocked at the admissibility level:
    UCToPAC is inadmissible on iOnlineLearnable (paradigm mismatch). -/
example : ∃ r, fltTheory.admissible iOnlineLearnable genUCToPAC = .error r := by
  exact ⟨_, rfl⟩

-- ============================================================
-- NT2: FD1 fires — Fintype blocks MeasureBridge
-- ============================================================

/-- An interface with Fintype_X in premises triggers FD1 on MeasureBridge. -/
example : ∃ r, fltTheory.admissible
    ⟨"FiniteVCDim_Fintype", [.pac], ["C", "hC_vcdim", "MeasurableConceptClass", "Fintype_X"],
     "VCDim_lt_top"⟩
    genMeasureBridge = .error r := by
  exact ⟨_, rfl⟩

-- ============================================================
-- NT3: FD5 fires — branchwise shattering blocks Adversary
-- ============================================================

/-- Branchwise shattering target triggers FD5 on Adversary. -/
example : ∃ r, fltTheory.admissible
    ⟨"BranchwiseLDim", [.online], ["C"], "isShattered_branchwise"⟩
    genAdversary = .error r := by
  exact ⟨_, rfl⟩

-- ============================================================
-- NT4: Extension mechanism — adding a generator solves a gap
-- ============================================================

/-- Define a gap: no generator takes iCompression to iPACLearnable.
    Then show: adding such a generator extends the theory. -/
def iCompression : Interface := ⟨"Compression", [.pac], ["C"], "HasCompression"⟩

def genCompressionToPAC : Generator :=
  ⟨"CompressionToPAC", .domain, iCompression, [iPACLearnable],
   "compression -> sample_complexity -> PAC", [.pac]⟩

/-- The extension theorem: adding genCompressionToPAC gives a well-typed plan. -/
example : HasType ⟨genCompressionToPAC :: fltTheory.generators, fltTheory.failures, fltTheory.gaps⟩
    (.atom "CompressionToPAC") iCompression [iPACLearnable] := by
  exact HasType.atom genCompressionToPAC (List.Mem.head _) rfl rfl

-- ============================================================
-- NT5: Cost model ordering — PAC pipeline is harder than Online
-- ============================================================

def nfPAC : NFPlan := .seq "GrowthConstruction" (.seq "MeasureBridge" (.atom "UCToPAC"))
def nfOnline : NFPlan := .atom "TreePotential"

/-- PAC pipeline has higher bridge depth than Online. -/
example : (nfPAC.cost fltTheory).bridgeDepth > (nfOnline.cost fltTheory).bridgeDepth := by
  native_decide

/-- PAC pipeline has higher total cost than Online. -/
example : (nfPAC.cost fltTheory).total > (nfOnline.cost fltTheory).total := by
  native_decide

-- ============================================================
-- NT6: Cost model — DST pipeline has highest elaboration penalty
-- ============================================================

def nfDST : NFPlan := .seq "AnalyticProjection" (.atom "CompactApproximation")

/-- DST has higher elaboration penalty than Online (cross-paradigm generators). -/
example : (nfDST.cost fltTheory).elaborationPenalty ≥
    (nfOnline.cost fltTheory).elaborationPenalty := by
  native_decide

-- ============================================================
-- NT7: Interface widening is reflexive
-- ============================================================

/-- Every interface widens to itself. -/
example : Interface.widens iFiniteVCDim iFiniteVCDim = true := by rfl
example : Interface.widens iBorelParam iBorelParam = true := by rfl
example : Interface.widens iGoal iGoal = true := by rfl

-- ============================================================
-- NT8: Structural generators are paradigm-unlocked
-- ============================================================

/-- All 5 structural generators have paradigm = [.structural]. -/
example : [genContrapose, genExtensionalize, genCaseSplit, genCalcChain, genWitnessRefine].all
    (fun g => g.paradigm == [Paradigm.structural]) = true := by native_decide

-- ============================================================
-- NT9: Domain generators are paradigm-locked
-- ============================================================

/-- No domain generator has paradigm = [.structural]. -/
example : [genGrowthConstruction, genMeasureBridge, genUCToPAC,
           genTreePotential, genAdversary, genLocking,
           genAnalyticProjection, genCompactApproximation,
           genWitnessSeparation, genJensenChain].all
    (fun g => g.paradigm != [Paradigm.structural]) = true := by native_decide

-- ============================================================
-- NT10: Guard filters by paradigm
-- ============================================================

/-- A PAC-guarded plan types on PAC interfaces. -/
example : HasType fltTheory (.guard .pac (.atom "UCToPAC")) iHasUC [iPACLearnable] := by
  apply HasType.guard
  · simp [iHasUC]
  · exact HasType.atom genUCToPAC
      (by unfold fltTheory; simp [List.mem_cons])
      (by rfl)
      (by rfl)

/-- An Online-guarded plan does NOT type on PAC interfaces
    (Online ∉ iHasUC.locks). -/
example : ¬ HasType fltTheory (.guard .online (.atom "UCToPAC")) iHasUC [iPACLearnable] := by
  intro h
  cases h with
  | guard hmatch _ =>
    simp [iHasUC] at hmatch

-- ============================================================
-- NT11: Choose picks the first valid alternative
-- ============================================================

/-- Choose between TreePotential and UCToPAC on iFiniteLDim: TreePotential wins. -/
example : HasType fltTheory
    (.choose [.atom "TreePotential", .atom "UCToPAC"])
    iFiniteLDim [iOnlineLearnable] := by
  apply HasType.chooseHead
  exact HasType.atom genTreePotential
    (by unfold fltTheory; simp [List.mem_cons])
    (by rfl)
    (by rfl)

-- ============================================================
-- NT12: Quality funnel rejects violations
-- ============================================================

/-- Robustness without validity violates the funnel. -/
example : (StepQuality.mk true false false true).funnelValid = false := by rfl

/-- Validity without compliance violates the funnel. -/
example : (StepQuality.mk false true false false).funnelValid = false := by rfl

/-- Completion without validity violates the funnel. -/
example : (StepQuality.mk true false true false).funnelValid = false := by rfl

-- ============================================================
-- NT13: bridge_search on True (graceful degradation, revisited)
-- ============================================================

/-- bridge_search on a non-FLT goal degrades gracefully. -/
example : 1 + 1 = 2 := by
  bridge_search  -- should report no bridge found
  rfl
