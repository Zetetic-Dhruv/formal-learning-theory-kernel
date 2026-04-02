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

open Lean Meta Elab Tactic in
def classifyExpr (e : Expr) : MetaM Paradigm := do
  let e ← whnf e
  let head := e.getAppFn
  if head.isConst then
    let name := head.constName!.toString
    -- PAC
    if name.hasSubstring "Measure" || name.hasSubstring "ENNReal"
       || name.hasSubstring "PACLearnable" || name.hasSubstring "WellBehavedVC" then
      return .pac
    -- Online
    if name.hasSubstring "OnlineLearner" || name.hasSubstring "LittlestoneDim"
       || name.hasSubstring "LTree" then
      return .online
    -- Gold
    if name.hasSubstring "DataStream" || name.hasSubstring "MindChange"
       || name.hasSubstring "EXLearnable" then
      return .gold
    -- DST
    if name.hasSubstring "AnalyticSet" || name.hasSubstring "NullMeasurable"
       || name.hasSubstring "PolishSpace" then
      return .dst
    -- Bayes
    if name.hasSubstring "FinitePMF" || name.hasSubstring "klDiv" then
      return .bayes
    -- Separation
    if name.hasSubstring "KrappWirth" || name.hasSubstring "WellBehavedVCMeasTarget" then
      return .separation
  return .structural

-- ============================================================
-- Part 5: Bridge Lemma Search (MetaM)
-- ============================================================

open Lean Meta Elab Tactic in
def searchBridgeLemmaRestricted (goal : MVarId) : MetaM (Option Name) := do
  let target ← goal.getType
  let env ← getEnv
  let entries := env.constants.fold (init := #[]) fun acc name info =>
    if name.isInternal then acc
    else if !(name.toString.hasSubstring "FLT_Proofs") then acc
    else match info with
    | .thmInfo _ => acc.push (name, info)
    | _ => acc
  for (name, info) in entries do
    let found ← observing? do
      forallTelescopeReducing info.type fun _ conclusion => do
        if ← isDefEq conclusion target then return name
        else throwError "no match"
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
      let lemmaExpr := mkConst name
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

theorem bridge_failure_implies_gap
    (_Sigma : Theory) (I : Interface)
    (report : BridgeReport) (_hfail : report.quality.goalCompletion = false) :
    ∃ gap : GapSpec, gap.source = I :=
  ⟨⟨I, ⟨"bridge_target", I.locks, I.premises, "bridge_target"⟩,
    .missingBridge I.name "bridge_target"⟩, rfl⟩

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
  trivial
