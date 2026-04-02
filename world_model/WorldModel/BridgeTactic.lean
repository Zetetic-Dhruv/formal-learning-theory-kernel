/-
  FLT_Proofs/Meta/BridgeTactic.lean

  Bridge lemma search tactic for the proof operad.
  Classifies goals by paradigm, searches the environment for matching
  bridge lemmas, and reports structured gap information on failure.
-/

import WorldModel.ProofOperadInstances
import Lean

-- ============================================================
-- Part 1: Four-Gate Step Quality
-- ============================================================

structure StepQuality where
  assumptionCompliance : Bool
  inferenceValidity : Bool
  goalCompletion : Bool
  generalizationRobustness : Bool
  deriving Repr, DecidableEq, BEq

def StepQuality.funnelValid (q : StepQuality) : Bool :=
  (!q.inferenceValidity || q.assumptionCompliance) &&
  (!q.goalCompletion || q.inferenceValidity) &&
  (!q.generalizationRobustness || q.goalCompletion)

-- ============================================================
-- Part 2: Gap Classification
-- ============================================================

inductive GapType where
  | bridge (source target : String) (missingLemma : String)
  | openEnded (reason : String)
  deriving Repr

structure BridgeReport where
  paradigm : Paradigm
  gapType : GapType
  quality : StepQuality
  triedAndFailed : List String
  goalDescription : String
  deriving Repr

-- ============================================================
-- Part 3: Interface Widening + Robustness
-- ============================================================

def Interface.widens (I I' : Interface) : Bool :=
  I'.premises.all (fun p => I.premises.contains p) &&
  I'.locks.all (fun l => I.locks.contains l)

def Generator.isRobust (Sigma : Theory) (g : Generator) (I : Interface) : Bool :=
  I.premises.all fun p =>
    let I' := { I with premises := I.premises.filter (· != p) }
    match Sigma.admissible I' g with
    | .ok () => true
    | .error _ => false

instance : ToString Paradigm where
  toString
    | .structural => "structural"
    | .pac => "pac"
    | .online => "online"
    | .gold => "gold"
    | .dst => "dst"
    | .bayes => "bayes"
    | .separation => "separation"

-- ============================================================
-- Part 4: Paradigm Classifier (MetaM)
-- ============================================================

/-- Check if `s` contains `sub` as a substring. -/
private def String.hasSubstring (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

private def matchParadigm (name : String) : Option Paradigm :=
  if name.hasSubstring "Measure" || name.hasSubstring "ENNReal"
     || name.hasSubstring "PACLearnable" || name.hasSubstring "WellBehavedVC"
     || name.hasSubstring "HasUniformConvergence"
     || name.hasSubstring "EmpiricalError" then some .pac
  else if name.hasSubstring "OnlineLearner" || name.hasSubstring "LittlestoneDim"
     || name.hasSubstring "LTree" || name.hasSubstring "versionSpace"
     || name.hasSubstring "OnlineLearnable" then some .online
  else if name.hasSubstring "DataStream" || name.hasSubstring "MindChange"
     || name.hasSubstring "EXLearnable" then some .gold
  else if name.hasSubstring "AnalyticSet" || name.hasSubstring "NullMeasurable"
     || name.hasSubstring "PolishSpace" then some .dst
  else if name.hasSubstring "FinitePMF" || name.hasSubstring "klDiv" then some .bayes
  else if name.hasSubstring "KrappWirth" || name.hasSubstring "WellBehavedVCMeasTarget"
     then some .separation
  else none

open Lean Meta Elab Tactic in
def classifyExpr (e : Expr) : MetaM Paradigm := do
  -- Check raw head BEFORE whnf
  let rawHead := e.getAppFn
  if rawHead.isConst then
    let name := Name.toString rawHead.constName!
    if let some p := matchParadigm name then return p
  -- Fallback: whnf then check
  let e' ← whnf e
  let head := e'.getAppFn
  if head.isConst then
    let name := Name.toString head.constName!
    if let some p := matchParadigm name then return p
  return .structural

-- ============================================================
-- Part 5: Bridge Lemma Search (MetaM)
-- ============================================================

open Lean Meta Elab Tactic in
def searchBridgeLemmaRestricted (goal : MVarId) : MetaM (Option Name) := do
  let env ← getEnv
  let entries := env.constants.fold (init := (#[] : Array (Name × ConstantInfo)))
    fun (acc : Array (Name × ConstantInfo)) (name : Name) info =>
      if name.isInternal then acc
      else
        let ns := Name.toString name
        -- Skip known library namespaces
        if ns.hasSubstring "Mathlib." || ns.hasSubstring "Lean." || ns.hasSubstring "Init."
           || ns.hasSubstring "Std." || ns.hasSubstring "Batteries." || ns.hasSubstring "Aesop."
           || ns.hasSubstring "Qq." || ns.hasSubstring "ProofWidgets." || ns.hasSubstring "ImportGraph."
           || ns.hasSubstring "LeanSearchClient." || ns.hasSubstring "Plausible."
           || ns.hasSubstring "Option." || ns.hasSubstring "List." || ns.hasSubstring "Array."
           || ns.hasSubstring "String." || ns.hasSubstring "Nat." || ns.hasSubstring "Int."
           || ns.hasSubstring "Bool." || ns.hasSubstring "Fin." || ns.hasSubstring "UInt"
           || ns.hasSubstring "Float." || ns.hasSubstring "IO." || ns.hasSubstring "System."
           || ns.hasSubstring "Decidable." || ns.hasSubstring "Eq." || ns.hasSubstring "HEq."
           || ns.hasSubstring "And." || ns.hasSubstring "Or." || ns.hasSubstring "Not."
           || ns.hasSubstring "Iff." || ns.hasSubstring "True." || ns.hasSubstring "False."
           || ns.hasSubstring "Exists." || ns.hasSubstring "Sigma." || ns.hasSubstring "PSigma."
           || ns.hasSubstring "Subtype." || ns.hasSubstring "Prod." || ns.hasSubstring "Sum."
           || ns.hasSubstring "Function." || ns.hasSubstring "Quot." || ns.hasSubstring "Quotient."
           || ns.hasSubstring "WellFounded." || ns.hasSubstring "Acc." then acc
        else match info with
        | .thmInfo _ => acc.push (name, info)
        | _ => acc
  -- Two-pass search: prioritize FLT-specific theorems, then generic ones
  let isFLTName (ns : String) : Bool :=
    ns.hasSubstring "pac" || ns.hasSubstring "PAC" || ns.hasSubstring "uc_imp"
    || ns.hasSubstring "vcdim" || ns.hasSubstring "VCDim" || ns.hasSubstring "vc_dim"
    || ns.hasSubstring "versionSpace" || ns.hasSubstring "ldim" || ns.hasSubstring "Littlestone"
    || ns.hasSubstring "learnable" || ns.hasSubstring "Learnable"
    || ns.hasSubstring "online" || ns.hasSubstring "Online"
    || ns.hasSubstring "bridge" || ns.hasSubstring "Bridge"
    || ns.hasSubstring "erm" || ns.hasSubstring "ERM"
    || ns.hasSubstring "analytic" || ns.hasSubstring "Analytic"
    || ns.hasSubstring "separation" || ns.hasSubstring "Separation"
    || ns.hasSubstring "mind_change" || ns.hasSubstring "MindChange"
    || ns.hasSubstring "klDiv" || ns.hasSubstring "bayes" || ns.hasSubstring "Bayes"
    || ns.hasSubstring "uniform_convergence" || ns.hasSubstring "UniformConvergence"
    || ns.hasSubstring "empirical" || ns.hasSubstring "Empirical"
    || ns.hasSubstring "measurable_concept" || ns.hasSubstring "MeasurableConcept"
    || ns.hasSubstring "concept_class" || ns.hasSubstring "ConceptClass"
  -- Pass 1: FLT-specific theorems
  for (name, _info) in entries do
    let ns := Name.toString name
    if isFLTName ns then
      let found ← withoutModifyingState do
        try
          let lemmaExpr ← mkConstWithFreshMVarLevels name
          let _newGoals ← goal.apply lemmaExpr
          return some name
        catch _ =>
          return none
      if let some n := found then
        return some n
  -- Pass 2: all remaining theorems
  for (name, _info) in entries do
    let ns := Name.toString name
    if !isFLTName ns then
      let found ← withoutModifyingState do
        try
          let lemmaExpr ← mkConstWithFreshMVarLevels name
          let _newGoals ← goal.apply lemmaExpr
          return some name
        catch _ =>
          return none
      if let some n := found then
        return some n
  return none

-- ============================================================
-- Part 6: The bridge_search Tactic
-- ============================================================

open Lean Meta Elab Tactic in
elab "bridge_search" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let paradigm ← classifyExpr target
    let result ← searchBridgeLemmaRestricted goal
    match result with
    | some name =>
      let lemmaExpr ← mkConstWithFreshMVarLevels name
      let newGoals ← goal.apply lemmaExpr
      replaceMainGoal newGoals
      logInfo m!"bridge_search: applied {name}"
    | none =>
      let goalStr := toString (← ppExpr target)
      let report : BridgeReport := {
        paradigm := paradigm
        gapType := .bridge (toString paradigm) goalStr "unknown"
        quality := ⟨true, true, false, false⟩
        triedAndFailed := []
        goalDescription := goalStr
      }
      logWarning m!"bridge_search: no bridge found.\n{repr report}"

-- ============================================================
-- Part 7: Soundness Lemmas
-- ============================================================

/-- Construct a gap specification from a bridge report.
    The gap records the paradigm and goal description from the report,
    making the structured ignorance concrete. -/
def BridgeReport.toGapSpec (report : BridgeReport) (I : Interface) : GapSpec :=
  ⟨I, ⟨report.goalDescription, I.locks, I.premises, report.goalDescription⟩,
    .missingBridge I.name report.goalDescription⟩

theorem BridgeReport.toGapSpec_source (report : BridgeReport) (I : Interface) :
    (report.toGapSpec I).source = I := rfl

theorem quality_funnel_monotone (q : StepQuality) (h : q.funnelValid = true) :
    (q.generalizationRobustness = true → q.goalCompletion = true) ∧
    (q.goalCompletion = true → q.inferenceValidity = true) ∧
    (q.inferenceValidity = true → q.assumptionCompliance = true) := by
  simp only [StepQuality.funnelValid, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_true] at h
  constructor
  · intro hr
    cases hac : q.assumptionCompliance <;> cases hiv : q.inferenceValidity <;>
      cases hgc : q.goalCompletion <;> cases hgr : q.generalizationRobustness <;>
      simp_all
  constructor
  · intro hg
    cases hac : q.assumptionCompliance <;> cases hiv : q.inferenceValidity <;>
      cases hgc : q.goalCompletion <;> cases hgr : q.generalizationRobustness <;>
      simp_all
  · intro hv
    cases hac : q.assumptionCompliance <;> cases hiv : q.inferenceValidity <;>
      cases hgc : q.goalCompletion <;> cases hgr : q.generalizationRobustness <;>
      simp_all

-- ============================================================
-- Part 8: Smoke Test
-- ============================================================

example : True := by
  bridge_search
  all_goals rfl
