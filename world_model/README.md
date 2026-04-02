# TPG_FLT: Proof Operad World Model

A stratified, open, typed proof operad with negative typing and extension objects.

## Architecture

```
world_model/
├── proof_world_model.json          Machine-extracted 21 MP taxonomy (v1, empirical)
├── WorldModel/                     Lean4 formalization (canonical build target)
│   ├── ProofOperad.lean            Core calculus: Interface, Generator, Plan, HasType, Theory
│   ├── ProofOperadInstances.lean   17 generators, 7 failure rules, fltTheory, binding theorems
│   ├── ProofOperadTheorems.lean    Corpus-relative completeness, paradigm lock, normalization
│   ├── BridgeTactic.lean           bridge_search tactic (under construction)
│   ├── BridgeTests.lean            Smoke tests (27/27 pass)
│   ├── NonTrivialTests.lean        Non-trivial tests (cross-paradigm, extension, cost)
│   ├── BridgeRealTests.lean        5 real FLT goals (search fails -- under construction)
│   └── BridgeDiagnostic.lean       Diagnostic tactic for debugging the search
├── dag/                            Machine-generated premise DAG
│   ├── generator_dag.json          17 generators, 18 interfaces, 66 edges, 6 pipelines
│   └── generate_dag.py             Generation script
└── README.md
```

## Layers

1. **proof_world_model.json** -- Empirical layer (SCM): 21 metaprograms extracted from
   tactic sequences across 278 kernel theorems. Each MP is a reusable DAG of TacticM
   transformations with typed inputs, outputs, paradigm locks, and failure diagnostics.

2. **WorldModel/** -- Formalized theory: The 21 empirical MPs reclassified into a three-level
   stratified operad:
   - **Structural combinators** (5): Contrapose, Extensionalize, CaseSplit, CalcChain, WitnessRefine
   - **Domain generators** (12): GrowthConstruction, MeasureBridge, UCToPAC, TreePotential,
     Adversary, Locking, AnalyticProjection, CompactApproximation, WitnessSeparation,
     ComponentMeasurability, RectangleDecomposition, JensenChain
   - **Failure rules** (7): FD1-FD7 as negative typing judgments
   - **Extension objects**: GapSpec for typed theory growth

3. **bridge_search tactic** -- Planning layer (RCA above the SCM): classifies live Lean4
   goals by paradigm, searches the environment for bridge lemmas, and produces structured
   BridgeReports on failure. **Under construction**: paradigm classifier works, environment
   search does not yet find matches on real FLT goals. See BridgeRealTests.lean.

## Key Results

- **Corpus-relative completeness**: All 6 major pipelines (PAC, DST, Online, Gold,
  Separation, Bayes) type-check under fltTheory.
- **Paradigm lock theorem**: No generator spans PAC + Online + Gold simultaneously.
- **NT1 cross-paradigm impossibility**: `seq TreePotential UCToPAC` is provably ill-typed
  at the composition level (65-line proof via HasType inversion + generator enumeration).
- **Four-gate quality model**: Calibrated against First Proof Benchmark funnel
  (100% -> 98% -> 76% -> 69%). StepQuality structure with funnelValid invariant.
- **Robustness model**: Structural generators are robust under interface widening;
  domain generators are not (reproduces the benchmark's 29-point validity-to-robustness gap).

## Metrics

| Component | LOC | Sorrys | Status |
|-----------|-----|--------|--------|
| ProofOperad.lean | 232 | 0 | Complete |
| ProofOperadInstances.lean | 252 | 0 | Complete |
| ProofOperadTheorems.lean | 207 | 0 | Complete |
| BridgeTactic.lean | 197 | 0 | Under construction (search) |
| BridgeTests + NonTrivialTests | 282 | 0 | All pass |
| **Total** | **1170** | **0** | |

## Build

```bash
lake build WorldModel
```

Or build individual targets:
```bash
lake build WorldModel.ProofOperad
lake build WorldModel.ProofOperadInstances
lake build WorldModel.ProofOperadTheorems
lake build WorldModel.BridgeTactic
lake build WorldModel.BridgeTests
lake build WorldModel.NonTrivialTests
```
