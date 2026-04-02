/-
  Diagnostic: what does bridge_search actually see?
-/
import WorldModel.BridgeTactic
import FLT_Proofs.Theorem.PAC
import FLT_Proofs.Complexity.GameInfra

set_option maxHeartbeats 800000

private def String.hasSub (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

-- Diagnostic tactic: log the goal target and search candidates
open Lean Meta Elab Tactic in
elab "bridge_diag" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let targetStr := toString (← ppExpr target)
    let paradigm ← classifyExpr target
    logInfo m!"Target: {targetStr}"
    logInfo m!"Paradigm: {repr paradigm}"
    -- Count FLT_Proofs theorems
    let env ← getEnv
    let entries := env.constants.fold (init := #[]) fun acc name info =>
      if name.isInternal then acc
      else if !(name.toString.hasSub "FLT_Proofs") then acc
      else match info with
      | .thmInfo _ => acc.push (name, info)
      | _ => acc
    logInfo m!"FLT_Proofs theorems in scope: {entries.size}"
    -- Count ALL non-internal theorems and collect samples
    let (count, samples) := env.constants.fold (init := (0, #[] : Array String)) fun (c, s) name info =>
      if name.isInternal then (c, s)
      else match info with
      | .thmInfo _ => (c + 1, if s.size < 10 then s.push name.toString else s)
      | _ => (c, s)
    logInfo m!"Total non-internal theorems: {count}"
    logInfo m!"Sample names: {samples}"
    -- Check head of target BEFORE and AFTER whnf
    let rawHead := target.getAppFn
    if rawHead.isConst then
      logInfo m!"Raw head (before whnf): {rawHead.constName!}"
    else
      logInfo m!"Raw head is NOT a const"
    let whnfTarget ← whnf target
    let whnfHead := whnfTarget.getAppFn
    if whnfHead.isConst then
      logInfo m!"WHNF head: {whnfHead.constName!}"
    else
      logInfo m!"WHNF head is NOT a const"
    -- Try first 5 matches
    let mut tried := 0
    for (name, info) in entries do
      if tried >= 20 then break
      let found ← observing? do
        forallTelescopeReducing info.type fun _ conclusion => do
          let concStr := toString (← ppExpr conclusion)
          if ← isDefEq conclusion target then
            logInfo m!"MATCH: {name} (conclusion: {concStr})"
            return name
          else
            return name  -- log anyway to see what we're comparing
      if found.isSome then
        tried := tried + 1

section Test
variable {X : Type} [MeasurableSpace X]
  (C : ConceptClass X Bool) [MeasurableConceptClass X C]
  (hC : C.Nonempty)
  (hUC : HasUniformConvergence X C)

example : PACLearnable X C := by
  bridge_diag
  sorry

end Test

section Test2
variable {X : Type} (C : ConceptClass X Bool)
  (history : List (X × Bool))

example : versionSpace C history ⊆ C := by
  bridge_diag
  sorry

end Test2
