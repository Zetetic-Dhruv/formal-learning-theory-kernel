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

-- BridgeTactic import removed: bridge_search is future work (world_model/future_work/)
import WorldModel.ProofOperadTheorems

-- ============================================================
-- NT1: Cross-paradigm composition FAILS
-- Trying to feed Online output into PAC generator is ill-typed
-- ============================================================

/-- Cross-paradigm composition is blocked at the admissibility level:
    UCToPAC is inadmissible on iOnlineLearnable (paradigm mismatch). -/
example : ∃ r, fltTheory.admissible iOnlineLearnable genUCToPAC = .error r := by
  exact ⟨_, rfl⟩

set_option maxHeartbeats 400000 in
/-- Cross-paradigm composition is ill-typed at the composition level:
    seq TreePotential UCToPAC does NOT type iFiniteLDim to [iPACLearnable].
    Proof uses inversion lemmas to extract generator identity, then
    derives contradiction from interface mismatch. -/
theorem nt1_cross_paradigm_composition_fails :
    ¬ HasType fltTheory
      (.seq (.atom "TreePotential") (.atom "UCToPAC"))
      iFiniteLDim [iPACLearnable] := by
  intro h
  -- Step 1: Invert the seq to get intermediate interfaces Js
  obtain ⟨Js, hTP, hUC⟩ := h.seq_inv
  -- Step 2: Invert the atom for TreePotential
  obtain ⟨gen₁, hg₁, hname₁, hinput₁, houtput₁⟩ := hTP.atom_inv
  -- Step 3: Enumerate generators to identify gen₁ = genTreePotential
  simp only [fltTheory, List.mem_cons, List.mem_nil_iff] at hg₁
  rcases hg₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  -- Cases 1-5: structural generators (name ≠ "TreePotential")
  · exact absurd hname₁ (by decide)   -- Contrapose
  · exact absurd hname₁ (by decide)   -- Extensionalize
  · exact absurd hname₁ (by decide)   -- CaseSplit
  · exact absurd hname₁ (by decide)   -- CalcChain
  · exact absurd hname₁ (by decide)   -- WitnessRefine
  -- Cases 6-8: PAC generators
  · exact absurd hname₁ (by decide)   -- GrowthConstruction
  · exact absurd hname₁ (by decide)   -- MeasureBridge
  · exact absurd hname₁ (by decide)   -- UCToPAC
  -- Case 9: gen₁ = genTreePotential — the surviving case
  · -- Js = genTreePotential.outputs = [iOnlineLearnable]
    -- Now apply hUC to iOnlineLearnable
    have hUC' := hUC iOnlineLearnable (by simp [genTreePotential] at houtput₁; rw [← houtput₁]; exact List.Mem.head _)
    -- Invert atom for UCToPAC
    obtain ⟨gen₂, hg₂, hname₂, hinput₂, _⟩ := hUC'.atom_inv
    -- Enumerate generators for gen₂
    simp only [fltTheory, List.mem_cons, List.mem_nil_iff] at hg₂
    rcases hg₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h₂
    · exact absurd hname₂ (by decide)   -- Contrapose
    · exact absurd hname₂ (by decide)   -- Extensionalize
    · exact absurd hname₂ (by decide)   -- CaseSplit
    · exact absurd hname₂ (by decide)   -- CalcChain
    · exact absurd hname₂ (by decide)   -- WitnessRefine
    · exact absurd hname₂ (by decide)   -- GrowthConstruction
    · exact absurd hname₂ (by decide)   -- MeasureBridge
    -- gen₂ = genUCToPAC: hinput₂ says genUCToPAC.input = iOnlineLearnable
    -- but genUCToPAC.input = iHasUC ≠ iOnlineLearnable
    · exact absurd hinput₂ (by decide)  -- UCToPAC: input mismatch
    · exact absurd hname₂ (by decide)   -- TreePotential
    · exact absurd hname₂ (by decide)   -- Adversary
    · exact absurd hname₂ (by decide)   -- Locking
    · exact absurd hname₂ (by decide)   -- AnalyticProjection
    · exact absurd hname₂ (by decide)   -- CompactApproximation
    · exact absurd hname₂ (by decide)   -- WitnessSeparation
    · exact absurd hname₂ (by decide)   -- ComponentMeasurability
    · exact absurd hname₂ (by decide)   -- RectangleDecomposition
    · exact absurd hname₂ (by decide)   -- JensenChain
    · exact absurd h₂ (by simp)         -- empty list case
  -- Cases 10-17: remaining generators
  · exact absurd hname₁ (by decide)   -- Adversary
  · exact absurd hname₁ (by decide)   -- Locking
  · exact absurd hname₁ (by decide)   -- AnalyticProjection
  · exact absurd hname₁ (by decide)   -- CompactApproximation
  · exact absurd hname₁ (by decide)   -- WitnessSeparation
  · exact absurd hname₁ (by decide)   -- ComponentMeasurability
  · exact absurd hname₁ (by decide)   -- RectangleDecomposition
  · exact absurd hname₁ (by decide)   -- JensenChain
  · exact absurd h (by simp)           -- empty list case

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
  decide

/-- PAC pipeline has higher total cost than Online. -/
example : (nfPAC.cost fltTheory).total > (nfOnline.cost fltTheory).total := by
  decide

-- ============================================================
-- NT6: Cost model — DST pipeline has highest elaboration penalty
-- ============================================================

def nfDST : NFPlan := .seq "AnalyticProjection" (.atom "CompactApproximation")

/-- DST has higher elaboration penalty than Online (cross-paradigm generators). -/
example : (nfDST.cost fltTheory).elaborationPenalty ≥
    (nfOnline.cost fltTheory).elaborationPenalty := by
  decide

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
    (fun g => g.paradigm == [Paradigm.structural]) = true := by decide

-- ============================================================
-- NT9: Domain generators are paradigm-locked
-- ============================================================

/-- No domain generator has paradigm = [.structural]. -/
example : [genGrowthConstruction, genMeasureBridge, genUCToPAC,
           genTreePotential, genAdversary, genLocking,
           genAnalyticProjection, genCompactApproximation,
           genWitnessSeparation, genJensenChain].all
    (fun g => g.paradigm != [Paradigm.structural]) = true := by decide

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

-- NT12-NT13: Moved to world_model/future_work/ (bridge_search planning layer)
