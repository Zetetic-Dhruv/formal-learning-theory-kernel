# TPG_FLT: Proof Operad World Model

A stratified, open, typed proof operad with negative typing and extension objects.

This is a **reference copy** of the proof operad from the [companion discovery repository](https://github.com/Zetetic-Dhruv/formal-learning-theory-discovery). To build and use the world model, use the discovery repo's lakefile.

## Architecture

```
world_model/
├── proof_world_model.json          Machine-extracted 21 MP taxonomy (empirical)
├── WorldModel/                     Lean4 formalization (reference copy)
│   ├── ProofOperad.lean            Core calculus: Interface, Generator, Plan, HasType, Theory
│   ├── ProofOperadInstances.lean   17 generators, 7 failure rules, fltTheory, binding theorems
│   ├── ProofOperadTheorems.lean    Corpus-relative completeness, paradigm lock, normalization
│   └── NonTrivialTests.lean        Non-trivial tests (cross-paradigm, extension, cost)
├── dag/                            Machine-generated premise DAG
│   ├── generator_dag.json          17 generators, 18 interfaces, 66 edges, 6 pipelines
│   └── generate_dag.py             Generation script
├── future_work/                    Planning layer (not part of the kernel)
│   ├── BridgeTactic.lean           bridge_search tactic (future direction)
│   ├── BridgeTests.lean            Smoke tests for bridge_search
│   ├── BridgeRealTests.lean        5 real FLT goals (search does not yet match)
│   └── BridgeDiagnostic.lean       Diagnostic tactic for debugging
└── README.md
```

## Layers

1. **proof_world_model.json** -- Empirical layer: 21 metaprograms extracted from
   tactic sequences across 292 kernel theorems. Each MP is a reusable DAG of TacticM
   transformations with typed inputs, outputs, paradigm locks, and failure diagnostics.

2. **WorldModel/** -- Formalized theory: The 21 empirical MPs reclassified into a three-level
   stratified operad:
   - **Structural combinators** (5): Contrapose, Extensionalize, CaseSplit, CalcChain, WitnessRefine
   - **Domain generators** (12): GrowthConstruction, MeasureBridge, UCToPAC, TreePotential,
     Adversary, Locking, AnalyticProjection, CompactApproximation, WitnessSeparation,
     ComponentMeasurability, RectangleDecomposition, JensenChain
   - **Failure rules** (7): FD1-FD7 as negative typing judgments
   - **Extension objects**: GapSpec for typed theory growth

3. **future_work/** -- Planning layer: `bridge_search` tactic that would classify live
   Lean4 goals by paradigm, search the environment for bridge lemmas, and produce
   structured BridgeReports on failure. This is a future direction, not part of the
   current kernel. See the planning layer diagram in Section VIII of the README.

## Key Results

- **Corpus-relative completeness**: All 6 major pipelines (PAC, DST, Online, Gold,
  Separation, Bayes) type-check under fltTheory.
- **Paradigm lock theorem**: No generator spans PAC + Online + Gold simultaneously.
- **NT1 cross-paradigm impossibility**: `seq TreePotential UCToPAC` is provably ill-typed
  at the composition level (65-line proof via HasType inversion + generator enumeration).

## Metrics

| Component | LOC | Sorrys | Status |
|-----------|-----|--------|--------|
| ProofOperad.lean | 253 | 0 | Complete |
| ProofOperadInstances.lean | 252 | 0 | Complete |
| ProofOperadTheorems.lean | 207 | 0 | Complete |
| NonTrivialTests.lean | 228 | 0 | All pass |
| **Total (core)** | **940** | **0** | |
| BridgeTactic.lean | 197 | 0 | Future work |

## Building

This is a reference copy. To build, use the discovery repo:

```bash
# Clone the discovery repo which has the lakefile for WorldModel
git clone https://github.com/Zetetic-Dhruv/formal-learning-theory-discovery
cd formal-learning-theory-discovery
lake build WorldModel
```
