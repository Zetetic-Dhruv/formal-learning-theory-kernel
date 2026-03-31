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

The premise is the most non-trivial component to change. A bad premise produces a kernel that either does not compile, compiles but proves vacuous theorems, or compiles but misses the field's structure. Two properties distinguish a productive premise from a brittle one.

**Stability under task execution.** Under derivation of consequences (proof search closing sorry placeholders), does the premise hold still? Sixty-five of 67 sorry placeholders were closed. Five definitions were corrected (Section IV). But no layer was added, no paradigm was introduced, no structural category changed. The perturbations were local (definition-level), not global (architecture-level). This is a property of the premise alone: it can be tested by any agent running proof search within it.

**Structured growth of the open frontier.** When the premise is modified, does the modification produce more precisely stated open questions than existed before?

| Stage | Open proofs | Resolved hypotheses | Open frontier questions | Character of ignorance |
|-------|------------|--------------------|-----------------------|----------------------|
| Original premise | 67 | 0 of 7 | "Are the structural hypotheses correct? Will the proofs close?" | Broad, unstructured |
| After proof search | 2 | 7 of 7 | "Can Moran-Yehudayoff and BHMZ be formalized?" | Narrow, specific (two published results) |
| After measurability refactoring | 2 | 7 of 7 | 5 precisely stated questions (Section V) + 3 original theorems | Broad again, but articulate |

The frontier grew from 67 vague placeholders to 2 specific blockers to 5 precise research questions. The volume of ignorance increased from the second stage to the third. But its structure sharpened at every step: each of the five frontier questions has specific evidence motivating it and a known mathematical approach or obstruction.

The premise modification did not just produce theorems. It produced better ignorance. Before the measurability refactoring, the relationship between NullMeasurableSet and MeasurableSet was an unstructured gap. After: the gap is inhabited by a concrete witness, the witness is connected to composition operations, the composition connection is connected to RL policy validity, and each connection opens a specific further question.

> A premise that produces theorems but leaves the open frontier vague has been consumed. A premise whose modifications articulate what is not yet known, and make that articulation more precise with each iteration, is productive beyond its original scope.

The measurability typeclass hierarchy is the primary evidence. It was not in the original premise. It was introduced to solve an engineering problem (hypothesis threading). It generated both new theorems and new questions that the original premise could not have stated. The premise accommodated the extension. It did not initiate it.

The premise files (`premise/origin.json` and `premise/final.json`) record the before and after. The trace between them (Sections VII and X) records what changed and what it produced.
