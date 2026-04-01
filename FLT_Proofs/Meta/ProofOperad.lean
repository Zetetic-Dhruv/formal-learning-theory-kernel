/-
  FLT_Proofs/Meta/ProofOperad.lean

  A typed calculus for proof generation in formal learning theory.
  TPG_FLT = (Interfaces, Generators, Plans, FailureRules, Extensions)

  Typing judgment:  Sigma |- p : I => O_vec
  Under theory Sigma, plan p transforms obligation I into sub-obligations O_vec.

  Imports: Lean core only. No Mathlib, no FLT_Proofs.
-/

-- ============================================================
-- 1. Paradigm
-- ============================================================

/-- Mathematical universes that lock proof methods to type families. -/
inductive Paradigm where
  | structural
  | pac
  | online
  | gold
  | dst
  | bayes
  | separation
  deriving DecidableEq, Repr, BEq, Hashable

-- ============================================================
-- 2. Interface
-- ============================================================

/-- An abstract proof interface: the type of obligation flowing between generators. -/
structure Interface where
  name : String
  locks : List Paradigm
  premises : List String
  targetTag : String
  deriving DecidableEq, Repr, BEq

-- ============================================================
-- 3. GenLevel
-- ============================================================

/-- The three levels of the stratified operad. -/
inductive GenLevel where
  | structural
  | domain
  | strategic
  deriving DecidableEq, Repr

-- ============================================================
-- 4. Generator
-- ============================================================

/-- A primitive proof generator in the operad. -/
structure Generator where
  name : String
  level : GenLevel
  input : Interface
  outputs : List Interface
  tacticPattern : String
  paradigm : List Paradigm
  deriving Repr, DecidableEq

-- ============================================================
-- 5. Plan
-- ============================================================

/-- A proof plan: the syntax of proof generation. -/
inductive Plan where
  | atom (g : String)
  | seq (p q : Plan)
  | par (ps : List Plan)
  | guard (lock : Paradigm) (p : Plan)
  | choose (alts : List Plan)
  | extend (gapName : String)
  deriving Repr

-- ============================================================
-- 6. RejectReason
-- ============================================================

/-- Reasons a generator application is rejected (negative typing). -/
inductive RejectReason where
  | paradigmMismatch (needed : List Paradigm) (found : List Paradigm)
  | missingPremise (name : String)
  | forbiddenInstance (tag : String)
  | nonconstructiveSelection
  | missingBridge (source target : String)
  | elaborationDeadEnd (msg : String)
  deriving Repr

-- ============================================================
-- 7. FailureRule
-- ============================================================

/-- A failure rule: a negative typing judgment.
    Uses function fields for flexible matching; no Repr derivation. -/
structure FailureRule where
  name : String
  onInput : Interface → Bool
  blocks : String → Bool
  reason : RejectReason

-- ============================================================
-- 8. GapSpec
-- ============================================================

/-- A typed gap: what the theory needs but doesn't have. -/
structure GapSpec where
  source : Interface
  needed : Interface
  because : RejectReason
  deriving Repr

-- ============================================================
-- 9. Theory
-- ============================================================

/-- The proof operad: generators, failure rules, and known gaps. -/
structure Theory where
  generators : List Generator
  failures : List FailureRule
  gaps : List GapSpec

-- ============================================================
-- Admissibility
-- ============================================================

/-- Check that a generator is admissible for an interface under a theory. -/
def Theory.admissible (Sigma : Theory) (I : Interface) (g : Generator) :
    Except RejectReason Unit :=
  -- Check paradigm lock: every paradigm in g.paradigm must appear in I.locks
  if g.paradigm.any (fun p => !I.locks.contains p) && !g.paradigm.isEmpty then
    .error (.paradigmMismatch g.paradigm I.locks)
  -- Check premises: every premise required by g.input must appear in I
  else
    match g.input.premises.filter (fun p => !I.premises.contains p) with
    | m :: _ => .error (.missingPremise m)
    | [] =>
      -- Check failure rules
      match Sigma.failures.find? (fun fd => fd.onInput I && fd.blocks g.name) with
      | some fd => .error fd.reason
      | none => .ok ()

-- ============================================================
-- HasType: the typing judgment
-- ============================================================

/-- Typing judgment: under theory Sigma, plan p transforms interface I
    into sub-obligations Os. -/
inductive HasType (Sigma : Theory) : Plan → Interface → List Interface → Prop where
  | atom {I : Interface} (g : Generator)
      (hg : g ∈ Sigma.generators)
      (hinput : g.input = I)
      (hadm : Sigma.admissible I g = .ok ()) :
      HasType Sigma (.atom g.name) I g.outputs
  | seq {p q : Plan} {I : Interface} {Js Ks : List Interface}
      (hp : HasType Sigma p I Js)
      (hq : ∀ J, J ∈ Js → HasType Sigma q J Ks) :
      HasType Sigma (.seq p q) I Ks
  | guard {lock : Paradigm} {p : Plan} {I : Interface} {Os : List Interface}
      (hmatch : lock ∈ I.locks)
      (hp : HasType Sigma p I Os) :
      HasType Sigma (.guard lock p) I Os
  | chooseHead {p : Plan} {rest : List Plan} {I : Interface} {Os : List Interface}
      (hp : HasType Sigma p I Os) :
      HasType Sigma (.choose (p :: rest)) I Os
  | chooseTail {p : Plan} {rest : List Plan} {I : Interface} {Os : List Interface}
      (hp : HasType Sigma (.choose rest) I Os) :
      HasType Sigma (.choose (p :: rest)) I Os
  | extend {gapName : String} {I : Interface} :
      HasType Sigma (.extend gapName) I
        [⟨gapName, I.locks, I.premises, gapName⟩]

-- ============================================================
-- Inversion lemmas
-- ============================================================

/-- Inversion for atom: if `.atom g` is well-typed, a matching generator exists. -/
theorem HasType.atom_inv {Sigma : Theory} {g : String} {I : Interface} {Os : List Interface}
    (h : HasType Sigma (.atom g) I Os) :
    ∃ gen ∈ Sigma.generators, gen.name = g ∧ gen.input = I ∧ gen.outputs = Os := by
  cases h with
  | atom gen hg hinput hadm => exact ⟨gen, hg, rfl, hinput, rfl⟩

/-- Inversion for seq: if `.seq p q` is well-typed, p types to intermediate Js. -/
theorem HasType.seq_inv {Sigma : Theory} {p q : Plan} {I : Interface} {Os : List Interface}
    (h : HasType Sigma (.seq p q) I Os) :
    ∃ Js, HasType Sigma p I Js ∧ ∀ J, J ∈ Js → HasType Sigma q J Os := by
  cases h with
  | seq hp hq => exact ⟨_, hp, hq⟩

-- ============================================================
-- Theorem 1: failure_as_negative_typing
-- ============================================================

/-- If a failure rule matches an interface and blocks a generator,
    then admissibility returns an error. -/
theorem failure_as_negative_typing
    (Sigma : Theory) (fd : FailureRule) (I : Interface) (g : Generator)
    (_hfd : fd ∈ Sigma.failures)
    (honInput : fd.onInput I = true)
    (hblocks : fd.blocks g.name = true) :
    ∃ r : RejectReason, Sigma.admissible I g = .error r := by
  simp only [Theory.admissible]
  split
  · -- paradigm mismatch
    exact ⟨_, rfl⟩
  · -- paradigm OK, check premises
    split
    · -- missing premise found
      exact ⟨_, rfl⟩
    · -- no missing premises, check failure rules
      split
      · -- find? returned some failure rule
        rename_i fd' _
        exact ⟨fd'.reason, rfl⟩
      · -- find? returned none — contradicts our hypotheses
        rename_i heq
        exfalso
        have hne := List.find?_eq_none.mp heq fd _hfd
        simp at hne
        simp [honInput, hblocks] at hne

-- ============================================================
-- Theorem 2: typed_openness
-- ============================================================

/-- If no plan can type an interface, a gap witness exists. -/
theorem typed_openness
    (Sigma : Theory) (I : Interface)
    (_hno : ¬ ∃ p Os, HasType Sigma p I Os) :
    ∃ gap : GapSpec, gap.source = I :=
  ⟨⟨I, ⟨"unknown", I.locks, I.premises, "unknown"⟩, .missingBridge I.name "unknown"⟩, rfl⟩

-- ============================================================
-- Theorem 3: extension_sound
-- ============================================================

/-- Extending a theory with a generator that solves a gap yields a well-typed plan. -/
theorem extension_sound
    (Sigma : Theory) (gap : GapSpec)
    (g : Generator) (hsolve : g.input = gap.source ∧ g.outputs = [gap.needed])
    (hadm : (Theory.mk (g :: Sigma.generators) Sigma.failures Sigma.gaps).admissible
              gap.source g = .ok ()) :
    HasType ⟨g :: Sigma.generators, Sigma.failures, Sigma.gaps⟩
      (.atom g.name) gap.source [gap.needed] := by
  rw [← hsolve.2]
  exact HasType.atom g (List.Mem.head _) hsolve.1 hadm
