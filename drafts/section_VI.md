# Section VI — FINAL DRAFT

---

## Part II: The Premise

## VI. The Typed Premise

A typed premise for a mathematical field consists of four components: concept nodes (the field's definitions and theorem statements, compiled with proof placeholders), dependency layers (a compilation order ensuring types are available before use), paradigm joints (binary obstruction tags predicting whether proof infrastructure transfers between subfields), and structural hypotheses (predictions about type-theoretic fractures). The premise scopes proof search. The AI searches within it, not alongside it.

### The layer structure

Every mathematical field, when typed for formalization, organizes into dependency layers. The specific contents are field-dependent. The ordering is not.

| Layer | Role | This kernel |
|-------|------|-------------|
| L0 | Computation infrastructure: automata, machines, formal languages | `Computation.lean` (241 lines) |
| L1 | Base types: the field's atomic definitions | `Basic.lean` (169 lines): Concept, ConceptClass, HypothesisSpace, loss functions |
| L2 | Data interfaces: how information enters the system | `Data.lean` (167 lines): IIDSample, DataStream, TextPresentation, oracles |
| L3 | Agent types: the entities that act on data | `Learner/*.lean` (348 lines): BatchLearner, OnlineLearner, GoldLearner, BayesianLearner |
| L4 | Success criteria: what counts as solving the problem | `Criterion/*.lean` (409 lines): PACLearnable, OnlineLearnable, EXLearnable, UniversalLearnable |
| L5 | Complexity measures and proof infrastructure | `Complexity/*.lean` (9,454 lines): VCDim, LittlestoneDim, Rademacher, Symmetrization, Measurability |
| L6 | Theorems | `Theorem/*.lean` (5,087 lines): characterizations, separations, PAC-Bayes, Borel-analytic |
| L7 | Processes and applications | `Process.lean` (180 lines): grammar induction, CEGIS, scope boundaries |

L5 accounts for 56% of the kernel (excluding PureMath/). This ratio is a consequence of the combinatorics-to-measure-theory crossing identified in Section I: bridging two mathematical domains requires extensive proof infrastructure.

### This kernel's premise

The premise for learning theory was derived from the author's textbook before proof search began. It is recorded in [`premise/origin.json`](premise/origin.json).

| Component | Count | What it contains |
|-----------|-------|-----------------|
| Concept nodes | 42 | Every definition, structure, and theorem statement in L0-L7, compiled with `sorry` placeholders |
| Paradigm joints | 5 | Binary obstruction tags for each paradigm pair (PAC/Online, PAC/Gold, Online/Gold, FiniteDim/OrdinalDim, Frequentist/Bayesian) |
| Structural hypotheses | 7 | Predictions about type-theoretic fractures: 3 predicted as genuine (no common learner, no common data, five signatures), 4 predicted as design decisions (WithTop Nat, function-class bridge, ConceptClass variants, Bayesian prior) |
| Compilation constraints | 5 | Lean4-specific type-level issues discovered during compilation (Sigma keyword conflict, NNReal import, def vs abbrev for typeclass synthesis, TextPresentation signature, Ordinal universe annotation) |

### Premise invariance

The premise is the most non-trivial component to change. A bad premise produces a kernel that either does not compile, compiles but proves vacuous theorems, or compiles but misses the field's structure. Two kinds of invariance distinguish a productive premise from a brittle one.

**Stability under discovery.** Under derivation of consequences (proof search closing sorry placeholders), does the premise hold still? Sixty-five of 67 sorry placeholders were closed. Five definitions were corrected (Section IV). But no layer was added, no paradigm was introduced, no structural category changed. The perturbations were local (definition-level), not global (architecture-level). The premise's stated goals were achievable within its type architecture, with corrections confined to individual definitions. This is a property of the premise alone: it can be tested by any agent running proof search within it.

**Stability of direction under inquiry.** When the premise is modified (not just used but changed), do the modifications consistently deepen understanding? The original premise had 67 open proofs and 7 structural hypotheses. After proof search, it had 2 open proofs and 7 resolved hypotheses. After the measurability refactoring, it had 2 open proofs, 3 original theorems, and 5 new open frontier questions (Section V). The frontier grew. Each premise modification opened more structure than it closed.

The measurability typeclass extension is the clearest instance. The original premise did not contain measurability typeclasses. The layer structure (L1 for base types, L3 for learner types, L5 for complexity infrastructure) had slots where measurability could be inserted without restructuring. But having slots is not the same as filling them. The decision to extract measurability, to formalize it as a typeclass hierarchy, and to test whether the hierarchy was strict required judgment about what was worth pursuing. The premise accommodated the extension. It did not initiate it.

A premise with good stability under discovery holds still while you work within it. A premise with good stability of direction accumulates depth across modifications: each change produces more open questions than it resolves, and the questions are deeper than the ones that preceded them. The first property is testable from the premise alone. The second is observable only in the trace of modifications, and it depends on what is brought to the premise, not just what the premise contains.

The premise files (`premise/origin.json` and `premise/final.json`) record the before and after. The trace between them (Sections VII and X) records the direction.
