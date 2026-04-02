/-
  FLT_Proofs/Meta/ProofOperadTheorems.lean

  Phase 3 of the proof operad: normal forms, corpus audit,
  difficulty model, and paradigm-lock theorem.
-/

import WorldModel.ProofOperadInstances

-- ============================================================
-- Part 1: Normal Form Plans
-- ============================================================

/-- A plan in normal form: atoms composed by seq only, no nesting. -/
inductive NFPlan where
  | atom (g : String)
  | seq (g : String) (rest : NFPlan)
  deriving Repr, DecidableEq

/-- Convert a normal-form plan back to Plan. -/
def NFPlan.toPlan : NFPlan → Plan
  | .atom g => .atom g
  | .seq g rest => .seq (.atom g) rest.toPlan

/-- A plan is normalizable if an equivalent NFPlan exists. -/
def IsNormalizable (Sigma : Theory) (p : Plan) (I : Interface) (Os : List Interface) : Prop :=
  HasType Sigma p I Os → ∃ nf : NFPlan, HasType Sigma nf.toPlan I Os

-- ============================================================
-- Part 2: Plan Cost / Difficulty Model
-- ============================================================

structure PlanCost where
  bridgeDepth : Nat
  novelInterfaces : Nat
  elaborationPenalty : Nat
  branchFactor : Nat
  deriving Repr, DecidableEq

def NFPlan.cost (Sigma : Theory) : NFPlan → PlanCost
  | .atom g =>
    let gen := Sigma.generators.find? (fun gen => gen.name == g)
    match gen with
    | some gen => ⟨1, 0, if gen.paradigm == [Paradigm.structural] then 0 else 1, gen.outputs.length⟩
    | none => ⟨0, 1, 0, 0⟩
  | .seq g rest =>
    let headCost :=
      let gen := Sigma.generators.find? (fun gen => gen.name == g)
      match gen with
      | some gen => PlanCost.mk 1 0 (if gen.paradigm == [Paradigm.structural] then 0 else 1) gen.outputs.length
      | none => PlanCost.mk 0 1 0 0
    let tailCost := rest.cost Sigma
    ⟨headCost.bridgeDepth + tailCost.bridgeDepth,
     headCost.novelInterfaces + tailCost.novelInterfaces,
     headCost.elaborationPenalty + tailCost.elaborationPenalty,
     max headCost.branchFactor tailCost.branchFactor⟩

def PlanCost.total (c : PlanCost) : Nat :=
  3 * c.bridgeDepth + 5 * c.novelInterfaces + 2 * c.elaborationPenalty + c.branchFactor

-- ============================================================
-- Part 3: New Plans + Binding Theorems
-- ============================================================

def stratLocking : Plan := .atom "Locking"
def stratWitnessSeparation : Plan := .atom "WitnessSeparation"
def stratJensenChain : Plan := .atom "JensenChain"

/-- Gold pipeline: Locking transforms EXLearnable to Contradiction. -/
theorem gold_pipeline_types :
    HasType fltTheory stratLocking iEXLearnable [iContradiction] := by
  unfold stratLocking
  exact HasType.atom genLocking
    (by unfold fltTheory; simp [List.mem_cons])
    (by rfl)
    (by rfl)

/-- Separation pipeline: WitnessSeparation transforms MeasurableHyps. -/
theorem separation_pipeline_types :
    HasType fltTheory stratWitnessSeparation iMeasurableHyps [iWBVCMeasTarget, iNotKrappWirth] := by
  unfold stratWitnessSeparation
  exact HasType.atom genWitnessSeparation
    (by unfold fltTheory; simp [List.mem_cons])
    (by rfl)
    (by rfl)

/-- Bayesian pipeline: JensenChain transforms PerHypBound to PACBayes. -/
theorem bayes_pipeline_types :
    HasType fltTheory stratJensenChain iPerHypBound [iPACBayes] := by
  unfold stratJensenChain
  exact HasType.atom genJensenChain
    (by unfold fltTheory; simp [List.mem_cons])
    (by rfl)
    (by rfl)

-- ============================================================
-- Part 4: Corpus-Relative Completeness
-- ============================================================

def majorPipelines : List (Plan × Interface × List Interface) :=
  [ (stratBuildThenBridge, iFiniteVCDim, [iPACLearnable])
  , (stratProjectThenApprox, iBorelParam, [iNullMeasBadEvent])
  , (stratPotentialThenBound, iFiniteLDim, [iOnlineLearnable])
  , (stratLocking, iEXLearnable, [iContradiction])
  , (stratWitnessSeparation, iMeasurableHyps, [iWBVCMeasTarget, iNotKrappWirth])
  , (stratJensenChain, iPerHypBound, [iPACBayes])
  ]

/-- Every major pipeline in the corpus is well-typed under fltTheory. -/
theorem corpus_relative_completeness :
    ∀ entry ∈ majorPipelines,
      HasType fltTheory entry.1 entry.2.1 entry.2.2 := by
  intro entry hentry
  simp only [majorPipelines, List.mem_cons, List.mem_nil_iff] at hentry
  rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl | h
  · exact pac_pipeline_types
  · exact dst_pipeline_types
  · exact online_pipeline_types
  · exact gold_pipeline_types
  · exact separation_pipeline_types
  · exact bayes_pipeline_types
  · exact absurd h (by simp)

-- ============================================================
-- Part 5: Normalization Theorems
-- ============================================================

theorem atom_normalizable (Sigma : Theory) (g : String) (I : Interface) (Os : List Interface) :
    IsNormalizable Sigma (.atom g) I Os := by
  intro h; exact ⟨.atom g, h⟩

theorem seq_atoms_normalizable (Sigma : Theory) (g1 g2 : String)
    (I : Interface) (Os : List Interface) :
    IsNormalizable Sigma (.seq (.atom g1) (.atom g2)) I Os := by
  intro h; exact ⟨.seq g1 (.atom g2), h⟩

/-- Append two normal-form plans. -/
def NFPlan.append (nf1 nf2 : NFPlan) : NFPlan :=
  match nf1 with
  | .atom g => .seq g nf2
  | .seq g rest => .seq g (rest.append nf2)

/-- The length of a normal-form plan (number of atoms). -/
def NFPlan.length : NFPlan → Nat
  | .atom _ => 1
  | .seq _ rest => 1 + rest.length

/-- Appending increases length additively. -/
theorem NFPlan.length_append (nf1 nf2 : NFPlan) :
    (nf1.append nf2).length = nf1.length + nf2.length := by
  induction nf1 with
  | atom g => simp [NFPlan.append, NFPlan.length]
  | seq g rest ih => simp [NFPlan.append, NFPlan.length, ih, Nat.add_assoc]

/-- Guard elimination: a guard over a normalizable plan is normalizable,
    given that the underlying plan is normalizable. -/
theorem guard_normalizable (Sigma : Theory) (lock : Paradigm) (p : Plan)
    (I : Interface) (Os : List Interface)
    (hn : IsNormalizable Sigma p I Os) :
    IsNormalizable Sigma (.guard lock p) I Os := by
  intro h
  cases h with
  | guard _hmatch hp => exact hn hp

/-- NFPlan.toPlan of an atom is Plan.atom. -/
theorem NFPlan.toPlan_atom (g : String) : (NFPlan.atom g).toPlan = Plan.atom g := rfl

/-- NFPlan.toPlan of a seq is Plan.seq of the atom head and the recursive toPlan. -/
theorem NFPlan.toPlan_seq (g : String) (rest : NFPlan) :
    (NFPlan.seq g rest).toPlan = Plan.seq (Plan.atom g) rest.toPlan := rfl

/-- Every NFPlan has positive length. -/
theorem NFPlan.length_pos (nf : NFPlan) : 0 < nf.length := by
  cases nf with
  | atom _ => simp [NFPlan.length]
  | seq _ rest => simp [NFPlan.length]; omega

-- ============================================================
-- Part 6: Paradigm Lock Theorem
-- ============================================================

/-- No generator in fltTheory spans all three paradigms (pac, online, gold).
    This reflects the fundamental separation of learning paradigms. -/
theorem no_universal_generator :
    ¬ ∃ g ∈ fltTheory.generators,
      Paradigm.pac ∈ g.paradigm ∧ Paradigm.online ∈ g.paradigm ∧ Paradigm.gold ∈ g.paradigm := by
  rintro ⟨g, hg, hpac, honline, hgold⟩
  simp only [fltTheory, List.mem_cons, List.mem_nil_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  · simp [genContrapose] at hpac
  · simp [genExtensionalize] at hpac
  · simp [genCaseSplit] at hpac
  · simp [genCalcChain] at hpac
  · simp [genWitnessRefine] at hpac
  · simp [genGrowthConstruction] at honline
  · simp [genMeasureBridge] at honline
  · simp [genUCToPAC] at honline
  · simp [genTreePotential] at hpac
  · simp [genAdversary] at hpac
  · simp [genLocking] at hpac
  · simp [genAnalyticProjection] at honline
  · simp [genCompactApproximation] at honline
  · simp [genWitnessSeparation] at hpac
  · simp [genComponentMeasurability] at honline
  · simp [genRectangleDecomposition] at honline
  · simp [genJensenChain] at hpac
  · exact absurd h (by simp)
