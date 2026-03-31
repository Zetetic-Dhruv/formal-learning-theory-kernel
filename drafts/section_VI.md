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

The premise is the most non-trivial component to change. A bad premise (wrong type choices, missing paradigm joints, too many or too few concept nodes) produces a kernel that either does not compile, compiles but proves vacuous theorems, or compiles but misses the field's structure.

Two properties of a well-designed premise:

**Discovery-enabling invariance.** Does the premise scaffold expansion to deeper premises without restructuring? The original premise did not contain measurability typeclasses. But the layer structure (L1 for base types, L3 for learner types, L5 for complexity infrastructure) had the right slots for measurability to be inserted at L1, L3, and L5 without adding layers or changing the compilation order. The premise did not predict the measurability hierarchy. It accommodated it. The measurability extension produced three original theorems (Section V) without perturbing the premise architecture. A premise that required restructuring to accept a new cross-cutting concern would have been brittle. This one was not.

**Goal-completing invariance.** Under derivation of consequences (proof search closing sorry placeholders), does the premise allow completing its own stated goals with minimum perturbation? Sixty-five of 67 sorry placeholders were closed. Five definitions were corrected (Section IV). But no layer was added, no paradigm was introduced, no structural category changed. The perturbations were local (definition-level), not global (architecture-level). The premise's stated goals (67 theorems across three paradigms) were achievable within the premise's type architecture, with corrections confined to individual definitions.

Both properties are testable. Discovery-enabling invariance is tested by each extension: if a future extension requires a new dependency layer or a new paradigm joint not predicted by the premise, the premise was too rigid. Goal-completing invariance is tested by the closure rate: if proof search requires restructuring the layer order or adding structural categories, the premise was too brittle.

The premise files (`premise/origin.json` and `premise/final.json`) are the data against which both tests are applied.
