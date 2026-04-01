/-
  FLT_Proofs/Meta/ProofOperadInstances.lean

  Concrete instances populating the proof operad with interfaces,
  generators, failure rules, and binding theorems for the FLT proof stack.
-/

import FLT_Proofs.Meta.ProofOperad

-- ============================================================
-- Part 1: Concrete Interfaces
-- ============================================================

-- PAC pipeline
def iFiniteVCDim : Interface :=
  ⟨"FiniteVCDim", [.pac], ["C", "hC_vcdim", "MeasurableConceptClass"], "VCDim_lt_top"⟩
def iGrowthBound : Interface :=
  ⟨"GrowthBound", [.pac], ["C", "hC_vcdim", "MeasurableConceptClass"], "GrowthFunction_le_poly"⟩
def iHasUC : Interface :=
  ⟨"HasUC", [.pac], ["C", "MeasurableConceptClass"], "HasUniformConvergence"⟩
def iPACLearnable : Interface := ⟨"PACLearnable", [.pac], ["C"], "PACLearnable"⟩

-- Online pipeline
def iFiniteLDim : Interface := ⟨"FiniteLDim", [.online], ["C"], "LittlestoneDim_lt_top"⟩
def iOnlineLearnable : Interface := ⟨"OnlineLearnable", [.online], ["C"], "OnlineLearnable"⟩

-- Gold pipeline
def iEXLearnable : Interface := ⟨"EXLearnable", [.gold], ["C"], "EXLearnable"⟩

-- DST pipeline
def iBorelParam : Interface := ⟨"BorelParam", [.dst, .pac], ["C", "e", "he"], "Measurable_eval"⟩
def iAnalyticBadEvent : Interface := ⟨"AnalyticBadEvent", [.dst], ["C"], "AnalyticSet_badEvent"⟩
def iNullMeasBadEvent : Interface := ⟨"NullMeasBadEvent", [.dst, .pac], ["C"], "NullMeasurableSet_badEvent"⟩

-- Bayesian pipeline
def iPerHypBound : Interface := ⟨"PerHypBound", [.bayes], ["P", "hs"], "per_hyp_tail_bound"⟩
def iPACBayes : Interface := ⟨"PACBayes", [.bayes], ["P", "Q"], "pac_bayes_bound"⟩

-- Separation
def iMeasurableHyps : Interface := ⟨"MeasurableHyps", [.separation], ["C"], "MeasurableHypotheses"⟩
def iWBVCMeasTarget : Interface := ⟨"WBVCMeasTarget", [.separation, .pac], ["C"], "WellBehavedVCMeasTarget"⟩
def iNotKrappWirth : Interface := ⟨"NotKrappWirth", [.separation], ["C"], "not_KrappWirthWellBehaved"⟩

-- Structural
def iGoal : Interface := ⟨"Goal", [.structural], [], "any"⟩
def iContradiction : Interface := ⟨"Contradiction", [.structural], [], "False"⟩

-- ============================================================
-- Part 2: Generators
-- ============================================================

-- Structural Combinators
def genContrapose : Generator :=
  ⟨"Contrapose", .structural, iGoal, [iContradiction],
   "by_contra -> push_neg -> witness -> absurd", [.structural]⟩

def genExtensionalize : Generator :=
  ⟨"Extensionalize", .structural, iGoal, [iGoal, iGoal],
   "ext -> simp only -> constructor -> case analysis", [.structural]⟩

def genCaseSplit : Generator :=
  ⟨"CaseSplit", .structural, iGoal, [iGoal, iGoal],
   "by_cases -> (branch 1) -> (branch 2)", [.structural]⟩

def genCalcChain : Generator :=
  ⟨"CalcChain", .structural, iGoal, [iGoal],
   "calc a ≤ b := ... _ ≤ c := ...", [.structural]⟩

def genWitnessRefine : Generator :=
  ⟨"WitnessRefine", .structural, iGoal, [iGoal, iGoal],
   "refine ⟨witness, ?_, ?_⟩ -> prove A -> prove B", [.structural]⟩

-- Domain Generators
def genGrowthConstruction : Generator :=
  ⟨"GrowthConstruction", .domain, iFiniteVCDim, [iGrowthBound],
   "let/set GrowthFunction -> have Sauer-Shelah -> exact bound", [.pac]⟩

def genMeasureBridge : Generator :=
  ⟨"MeasureBridge", .domain, iGrowthBound, [iHasUC],
   "DoubleSampleMeasure -> symmetrization_step -> Hoeffding", [.pac]⟩

def genUCToPAC : Generator :=
  ⟨"UCToPAC", .domain, iHasUC, [iPACLearnable],
   "exact uc_imp_pac", [.pac]⟩

def genTreePotential : Generator :=
  ⟨"TreePotential", .domain, iFiniteLDim, [iOnlineLearnable],
   "induction seq -> by_cases mistake -> ldim_strict_decrease -> omega", [.online]⟩

def genAdversary : Generator :=
  ⟨"Adversary", .domain, iFiniteLDim, [⟨"AdversaryBound", [.online], ["C", "T"], "mistakes_ge_ldim"⟩],
   "induction n -> match branch -> by_cases predict -> omega", [.online]⟩

def genLocking : Generator :=
  ⟨"Locking", .domain, iEXLearnable, [iContradiction],
   "Nat.rec chain -> mod arith -> List.ext_getElem -> omega", [.gold]⟩

def genAnalyticProjection : Generator :=
  ⟨"AnalyticProjection", .domain, iBorelParam, [iAnalyticBadEvent],
   "AnalyticSet.preimage -> .analyticSet -> paramBadEvent_analytic", [.dst]⟩

def genCompactApproximation : Generator :=
  ⟨"CompactApproximation", .domain, iAnalyticBadEvent, [iNullMeasBadEvent],
   "le_antisymm -> Nat.rec compact seq -> iInter_closure -> capacitability", [.dst]⟩

def genWitnessSeparation : Generator :=
  ⟨"WitnessSeparation", .domain, iMeasurableHyps, [iWBVCMeasTarget, iNotKrappWirth],
   "refine ⟨C, ?_, ?_⟩ -> prove WellBehavedVCMeasTarget -> prove ¬KrappWirth", [.separation]⟩

def genComponentMeasurability : Generator :=
  ⟨"ComponentMeasurability", .domain, iGoal, [iGoal],
   "simp [def] -> Measurable.piecewise + measurableSet_singleton", [.pac, .separation]⟩

def genRectangleDecomposition : Generator :=
  ⟨"RectangleDecomposition", .domain, iGoal, [iGoal],
   "ext -> preimage = ⋃ n (Aₙ ×ˢ Bₙ) -> MeasurableSet.iUnion -> .prod", [.pac, .structural]⟩

def genJensenChain : Generator :=
  ⟨"JensenChain", .domain, iPerHypBound, [iPACBayes],
   "per-h Hoeffding -> union bound sum -> Jensen sqrt -> calc", [.bayes]⟩

-- ============================================================
-- Part 3: Failure Rules
-- ============================================================

def fd1_fintype_blocks_symmetrization : FailureRule :=
  ⟨"FD1", fun I => I.premises.contains "Fintype_X",
   fun g => g == "MeasureBridge", .forbiddenInstance "Fintype_X"⟩

def fd2_uncountable_blocks_union : FailureRule :=
  ⟨"FD2", fun I => !I.premises.contains "Fintype_C" && !I.premises.contains "Countable_C",
   fun g => g == "UnionBound", .forbiddenInstance "uncountable_C"⟩

def fd3_missing_measurability : FailureRule :=
  ⟨"FD3", fun I => !I.premises.contains "MeasurableConceptClass",
   fun g => g == "MeasureBridge", .missingPremise "MeasurableConceptClass"⟩

def fd4_quantifier_order : FailureRule :=
  ⟨"FD4", fun I => I.targetTag == "forall_D_exists_m0",
   fun g => g == "UCToPAC", .elaborationDeadEnd "quantifier order: need ∃m₀ ∀D"⟩

def fd5_branchwise_littlestone : FailureRule :=
  ⟨"FD5", fun I => I.targetTag == "isShattered_branchwise",
   fun g => g == "Adversary", .forbiddenInstance "branchwise_shattering"⟩

def fd6_existential_dm : FailureRule :=
  ⟨"FD6", fun I => I.targetTag == "PACLearnable_exists_Dm",
   fun g => g == "UCToPAC", .nonconstructiveSelection⟩

def fd7_nonconstructive_selection : FailureRule :=
  ⟨"FD7", fun _ => true,
   fun g => g == "ClassicalChooseUncountable", .nonconstructiveSelection⟩

-- ============================================================
-- Part 4: The Theory Instance
-- ============================================================

def fltTheory : Theory where
  generators := [
    genContrapose, genExtensionalize, genCaseSplit, genCalcChain, genWitnessRefine,
    genGrowthConstruction, genMeasureBridge, genUCToPAC,
    genTreePotential, genAdversary, genLocking,
    genAnalyticProjection, genCompactApproximation,
    genWitnessSeparation, genComponentMeasurability,
    genRectangleDecomposition, genJensenChain
  ]
  failures := [
    fd1_fintype_blocks_symmetrization, fd2_uncountable_blocks_union,
    fd3_missing_measurability, fd4_quantifier_order,
    fd5_branchwise_littlestone, fd6_existential_dm,
    fd7_nonconstructive_selection
  ]
  gaps := []

-- ============================================================
-- Part 5: Strategic Plans
-- ============================================================

def stratBuildThenBridge : Plan :=
  .seq (.atom "GrowthConstruction") (.seq (.atom "MeasureBridge") (.atom "UCToPAC"))

def stratProjectThenApprox : Plan :=
  .seq (.atom "AnalyticProjection") (.atom "CompactApproximation")

def stratPotentialThenBound : Plan :=
  .atom "TreePotential"

-- ============================================================
-- Part 6: Binding Theorems
-- ============================================================

/-- Theorem 3: Online pipeline types — genTreePotential transforms iFiniteLDim to [iOnlineLearnable]. -/
theorem online_pipeline_types :
    HasType fltTheory stratPotentialThenBound iFiniteLDim [iOnlineLearnable] := by
  unfold stratPotentialThenBound
  exact HasType.atom genTreePotential
    (by unfold fltTheory; simp [List.mem_cons])
    (by rfl)
    (by rfl)

/-- Theorem 2: DST pipeline types — AnalyticProjection then CompactApproximation. -/
theorem dst_pipeline_types :
    HasType fltTheory stratProjectThenApprox iBorelParam [iNullMeasBadEvent] := by
  unfold stratProjectThenApprox
  apply HasType.seq
  · -- first atom: AnalyticProjection
    exact HasType.atom genAnalyticProjection
      (by unfold fltTheory; simp [List.mem_cons])
      (by rfl)
      (by rfl)
  · -- second atom: CompactApproximation on each output of first
    intro J hJ
    simp [genAnalyticProjection] at hJ
    subst hJ
    exact HasType.atom genCompactApproximation
      (by unfold fltTheory; simp [List.mem_cons])
      (by rfl)
      (by rfl)

/-- Theorem 1: PAC pipeline types — GrowthConstruction >> MeasureBridge >> UCToPAC. -/
theorem pac_pipeline_types :
    HasType fltTheory stratBuildThenBridge iFiniteVCDim [iPACLearnable] := by
  unfold stratBuildThenBridge
  apply HasType.seq
  · -- first atom: GrowthConstruction
    exact HasType.atom genGrowthConstruction
      (by unfold fltTheory; simp [List.mem_cons])
      (by rfl)
      (by rfl)
  · -- inner seq: MeasureBridge >> UCToPAC on each output of GrowthConstruction
    intro J hJ
    simp [genGrowthConstruction] at hJ
    subst hJ
    apply HasType.seq
    · exact HasType.atom genMeasureBridge
        (by unfold fltTheory; simp [List.mem_cons])
        (by rfl)
        (by rfl)
    · intro K hK
      simp [genMeasureBridge] at hK
      subst hK
      exact HasType.atom genUCToPAC
        (by unfold fltTheory; simp [List.mem_cons])
        (by rfl)
        (by rfl)

/-- Theorem 4: FD3 blocks MeasureBridge when MeasurableConceptClass is absent. -/
theorem fd3_blocks_measure_bridge :
    ∃ r, fltTheory.admissible
      ⟨"GrowthBound_noMCC", [.pac], ["C", "hC_vcdim"], "GrowthFunction_le_poly"⟩
      genMeasureBridge = .error r := by
  exact ⟨_, rfl⟩
