# TPG_FLT: Proof Operad World Model

A stratified, open, typed proof operad with negative typing and extension objects.

## Architecture

```
world_model/
├── proof_world_model.json       Machine-extracted 21 MP taxonomy (v1, empirical)
├── lean/                        Lean4 formalization of the proof operad
│   ├── ProofOperad.lean         Core calculus: Interface, Generator, Plan, HasType, Theory
│   ├── ProofOperadInstances.lean 17 generators, 7 failure rules, fltTheory, binding theorems
│   ├── ProofOperadTheorems.lean  Corpus-relative completeness, paradigm lock, normalization
│   └── BridgeTactic.lean        bridge_search tactic (planning layer above the world model)
├── dag/                         Machine-generated premise DAG
│   ├── generator_dag.json       17 generators, 18 interfaces, 66 edges, 6 pipelines
│   └── generate_dag.py          Generation script
└── tests/                       Test suite
    ├── BridgeTests.lean         10 smoke tests + 7 bonus (typing, failure, tactic)
    ├── NonTrivialTests.lean     17 non-trivial tests (cross-paradigm, extension, cost, guard)
    ├── results.md               Full results: 27/27 pass, 0 sorrys
    └── run_tests.sh             Test runner script
```

## Layers

1. **proof_world_model.json** — Empirical layer: 21 metaprograms extracted from tactic
   sequences across 278 kernel theorems. This is the SCM (structural causal model).

2. **lean/** — Formalized theory: 17 generators reclassified into 3 levels (structural,
   domain, strategic), typed composition algebra, failure diagnostics as negative typing,
   extension objects for theory growth.

3. **BridgeTactic.lean** — Planning layer: `bridge_search` tactic that classifies goals
   by paradigm, searches the environment for bridge lemmas, and reports structured
   BridgeReports on failure. This is the RCA engine above the SCM.

## Key Results

- **Corpus-relative completeness**: All 6 major pipelines (PAC, DST, Online, Gold,
  Separation, Bayes) type-check under fltTheory.
- **Paradigm lock theorem**: No generator spans PAC + Online + Gold simultaneously.
- **NT1 cross-paradigm impossibility**: seq TreePotential UCToPAC is provably ill-typed.
- **Four-gate quality model**: Calibrated against First Proof Benchmark funnel
  (100% → 98% → 76% → 69%).

## Metrics

| Component | LOC | Sorrys |
|-----------|-----|--------|
| ProofOperad.lean | 232 | 0 |
| ProofOperadInstances.lean | 252 | 0 |
| ProofOperadTheorems.lean | 207 | 0 |
| BridgeTactic.lean | 197 | 0 |
| Tests | 282 | 0 |
| **Total** | **1170** | **0** |

Note: The Lean files in `lean/` are COPIES of the files in `FLT_Proofs/Meta/` which
are the build targets. The `world_model/` folder is the reference/documentation view.
The `FLT_Proofs/Meta/` files are what `lake build` compiles.
