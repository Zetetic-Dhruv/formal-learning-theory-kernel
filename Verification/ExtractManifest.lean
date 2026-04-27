import Lean
import FLT_Proofs.Theorem.PAC
import FLT_Proofs.Theorem.Online
import FLT_Proofs.Theorem.Gold
import FLT_Proofs.Theorem.Separation
import FLT_Proofs.Theorem.Extended
import FLT_Proofs.Theorem.PACBayes
import FLT_Proofs.Theorem.BorelAnalyticSeparation
import FLT_Proofs.Complexity.Compression
import FLT_Proofs.Complexity.FiniteSupportUC
import FLT_Proofs.PureMath.ApproxMinimax
import FLT_Proofs.Bridge
import FLT_Proofs.Process

open Lean Meta

/-- Check if a name belongs to the FLT_Proofs namespace by module. -/
def isFLTModule (n : Name) : Bool :=
  match n with
  | .str p _ => p == `FLT_Proofs || isFLTModule p
  | .num p _ => isFLTModule p
  | .anonymous => false

/-- Check if a constant is a public theorem from FLT_Proofs. -/
def isPublicTheorem (env : Environment) (n : Name) : Bool :=
  if n.isInternal then false
  else
    match env.getModuleFor? n with
    | some modName =>
      if !isFLTModule modName then false
      else
        match env.find? n with
        | some (.thmInfo _) => true
        | _ => false
    | none => false

/-- Escape a string for JSON output. -/
def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

/-- Extract the source module for a constant. -/
def getSourceModule (env : Environment) (n : Name) : Name :=
  match env.getModuleFor? n with
  | some m => m
  | none => .anonymous

/-- Pretty-print a type expression. -/
def ppType (env : Environment) (type : Expr) : IO String := do
  let opts := Options.empty
    |>.setBool `pp.universes false
    |>.setBool `pp.fullNames false
    |>.setBool `pp.unicode false
  let ctxCore : Core.Context := {
    fileName := "<manifest>"
    fileMap := .ofString ""
    options := opts
  }
  let stCore : Core.State := { env }
  let (result, _) ← (do
    let fmt ← Meta.MetaM.run' (Meta.ppExpr type)
    return fmt.pretty (width := 120)
  : CoreM String).toIO ctxCore stCore
  return result

unsafe def main : IO Unit := do
  -- Initialize search path so importModules can find .olean files
  initSearchPath (← Lean.findSysroot)
  -- Import the full environment
  let mods := #[
    { module := `FLT_Proofs.Theorem.PAC : Import },
    { module := `FLT_Proofs.Theorem.Online },
    { module := `FLT_Proofs.Theorem.Gold },
    { module := `FLT_Proofs.Theorem.Separation },
    { module := `FLT_Proofs.Theorem.Extended },
    { module := `FLT_Proofs.Theorem.PACBayes },
    { module := `FLT_Proofs.Theorem.BorelAnalyticSeparation },
    { module := `FLT_Proofs.Complexity.Compression },
    { module := `FLT_Proofs.Complexity.FiniteSupportUC },
    { module := `FLT_Proofs.PureMath.ApproxMinimax },
    { module := `FLT_Proofs.Bridge },
    { module := `FLT_Proofs.Process }
  ]
  let env ← importModules mods {}
  -- Debug: count total constants, FLT constants, theorems
  let (totalCount, fltCount, thmCount, internalCount) :=
    env.constants.fold (init := (0, 0, 0, 0)) fun (t, f, th, i) name info =>
      let t' := t + 1
      let isFLT := match env.getModuleFor? name with
        | some m => isFLTModule m
        | none => false
      let f' := if isFLT then f + 1 else f
      let i' := if name.isInternal then i + 1 else i
      let th' := match info with | .thmInfo _ => if isFLT then th + 1 else th | _ => th
      (t', f', th', i')
  IO.eprintln s!"DEBUG: total constants = {totalCount}"
  IO.eprintln s!"DEBUG: FLT_Proofs constants = {fltCount}"
  IO.eprintln s!"DEBUG: FLT_Proofs theorems = {thmCount}"
  IO.eprintln s!"DEBUG: internal names = {internalCount}"
  -- Debug: sample names containing "FLT" substring
  let fltSamples := env.constants.fold (init := (#[] : Array String)) fun acc name _ =>
    if acc.size < 20 && (name.toString.splitOn "FLT").length > 1 then acc.push name.toString
    else acc
  IO.eprintln s!"DEBUG: sample names containing FLT = {fltSamples}"
  -- Debug: check getModuleFor on a known theorem
  let knownName := `FLT_Proofs.Theorem.PAC.fundamental_theorem
  IO.eprintln s!"DEBUG: env.find? fundamental_theorem = {(env.find? `fundamental_theorem).isSome}"
  IO.eprintln s!"DEBUG: env.find? {knownName} = {(env.find? knownName).isSome}"
  IO.eprintln s!"DEBUG: getModuleFor fundamental_theorem = {env.getModuleFor? `fundamental_theorem}"
  IO.eprintln s!"DEBUG: getModuleFor {knownName} = {env.getModuleFor? knownName}"
  -- Debug: test isFLTProofs on a known name
  let testName := `FLT_Proofs.Theorem.PAC.fundamental_theorem
  IO.eprintln s!"DEBUG: isFLTProofs {testName} = {isFLTProofs testName}"
  IO.eprintln s!"DEBUG: isFLTProofs `FLT_Proofs = {isFLTProofs `FLT_Proofs}"
  -- Debug: check Name structure of a sample
  let nameSample := env.constants.fold (init := (#[] : Array String)) fun acc name _ =>
    if acc.size < 3 then
      let s := match name with
        | .str p s => s!".str ({p}) \"{s}\""
        | .num p n => s!".num ({p}) {n}"
        | .anonymous => ".anonymous"
      acc.push s!"{name} -> {s}"
    else acc
  IO.eprintln s!"DEBUG: name structure = {nameSample}"
  -- Collect all public theorems using env.constants.fold (canonical pattern)
  let collected := env.constants.fold (init := (#[] : Array (Name × ConstantInfo)))
    fun acc name info =>
      if isPublicTheorem env name then acc.push (name, info)
      else acc
  let mut entries : Array (Name × Name × String) := #[]
  for (n, ci) in collected do
    match ci with
    | .thmInfo ti => do
      let typeStr ← ppType env ti.type
      let modName := getSourceModule env n
      entries := entries.push (n, modName, typeStr)
    | _ => pure ()
  -- Sort by name for deterministic output
  let sorted := entries.qsort (fun a b => a.1.toString < b.1.toString)
  -- Emit JSON (no timestamp: deterministic output, caller adds timestamp)
  IO.println "{"
  IO.println s!"  \"total_public_theorems\": {sorted.size},"
  IO.println "  \"theorems\": ["
  for i in [:sorted.size] do
    let (name, modName, typeStr) := sorted[i]!
    let comma := if i + 1 < sorted.size then "," else ""
    IO.println "    {"
    IO.println s!"      \"name\": \"{name}\","
    IO.println s!"      \"module\": \"{modName}\","
    IO.println s!"      \"type\": \"{jsonEscape typeStr}\""
    IO.println s!"    }}{comma}"
  IO.println "  ]"
  IO.println "}"
