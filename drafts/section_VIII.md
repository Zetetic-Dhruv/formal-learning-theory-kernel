# Section VIII -- FINAL DRAFT

---

## Part III: The Proof Structure

## VIII. The Proof World Model

A Lean4 proof is a sequence of tactic applications transforming goals. An `MVarId` holds the current goal; a `TacticM Unit` transformation replaces it with zero or more subgoals. Individual tactics (`simp`, `omega`, `exact`, `apply`) are the atoms. But proof *methods* -- the strategies that close theorems across hundreds of lines -- operate above individual tactics. They are compositions: sequential chains, parallel decompositions, guarded paradigm-specific branches, backtracking over alternatives.

This kernel's 278 theorems use 21 recurring proof methods. The methods are not annotations added after the fact. They were extracted from actual `by`-blocks by analyzing tactic sequences, identifying shared prefixes and suffixes, and abstracting over the varying middle. Each method is a metaprogram: a reusable DAG of `TacticM` transformations with typed inputs, typed outputs, paradigm locks, and failure diagnostics.

The methods are encoded in three layers.

<!-- FIGURE: world_model_layers.svg
     Style: black/white, Times New Roman, old school academic
     Three horizontal bands stacked vertically, connected by vertical arrows:

     Top band (dashed border): "Layer 3: Planning (under construction)"
       Contents: "bridge_search tactic"
       Subtitle: "Classifies live MVarId goals by paradigm, searches environment"
       Arrow down labeled "queries"

     Middle band (solid border, thick): "Layer 2: Typed Proof Operad (1,170 LOC, 0 sorry)"
       Contents: "Interface | Generator | Plan | HasType | FailureRule | GapSpec"
       Left annotation: "17 generators (5 structural + 12 domain)"
       Right annotation: "7 failure rules (negative typing)"
       Arrow down labeled "formalizes"

     Bottom band (solid border, thin): "Layer 1: Empirical Taxonomy (proof_world_model.json)"
       Contents: "21 metaprograms extracted from 278 theorems"
       Left annotation: "Tactic patterns, instances, compositions"
       Right annotation: "Goal profiles, failure diagnostics"

     Caption: "Three layers of proof method encoding. Layer 2 is the centerpiece."
-->

### Layer 1: Empirical taxonomy

The 21 metaprograms, extracted from tactic sequences across 43 source files and stored in `proof_world_model.json`. Each has a typed signature: an input goal profile and output subgoals. Composition is sequential (`;`), parallel (`all_goals`), focused (`focus`), or backtracking (`try <|>`).

<details>
<summary><strong>Full metaprogram table (21 entries)</strong></summary>

| ID | Name | Pattern | Paradigm | Instances |
|----|------|---------|----------|-----------|
| MP1 | M-Pipeline | `have` (extract instances) -> `exact` (delegate) | PAC | 4 |
| MP2 | M-Contrapositive | `by_contra` -> `push_neg` -> witness -> `absurd` | PAC | 4 |
| MP3 | M-Construction | `let`/`set` (build object) -> `have` (verify) -> `refine` | PAC, Online | 5 |
| MP4 | M-Bridge | `have` (bridge lemma) -> `exact` (connect) | Cross-cutting | 3 |
| MP5 | M-UnionBound | `calc` chain: per-element bound -> `Finset.sum` -> `div_le` | PAC | 3 |
| MP6 | M-Complement | `have` := 1 - P(bad) -> `linarith` | PAC | 2 |
| MP7 | M-IntegralBound | `lintegral_indicator` -> `mul_comm` -> `ENNReal.toReal` | PAC | 2 |
| MP8 | M-Pigeonhole | `Finset.exists_lt_card_fiber_of_nsmul_lt_card` | PAC | 1 |
| MP9 | M-Adversary | `induction` on tree -> `by_cases` predict -> `omega` | Online | 2 |
| MP10 | M-Potential | `induction` on sequence -> version space shrinkage | Online | 2 |
| MP11 | M-LatticeMinMax | `iSup`/`iInf` lattice operations -> `le_antisymm` | Online | 2 |
| MP12 | M-Locking | `Nat.rec` chain -> `mod_arith` -> `List.ext_getElem` | Gold | 2 |
| MP13 | M-DefinitionUnfolding | `simp [def1, def2]` -> `ext` -> case analysis | Structural | 6 |
| MP14 | M-WitnessConstruction | `refine <..., ?_, ?_>` -> prove each conjunct | Structural | 5 |
| MP15 | M-ComponentMeasurability | `Measurable.piecewise` + `measurableSet_singleton` | PAC, Separation | 3 |
| MP16 | M-SetExtensionBridge | `Set.ext` or `Finset.ext` -> pointwise argument | Structural | 4 |
| MP17 | M-AnalyticChain | `AnalyticSet.preimage` -> `.analyticSet` -> projection | DST | 2 |
| MP18 | M-SurjectiveTransfer | `Function.Surjective` -> `map_eq` -> transfer property | Structural | 2 |
| MP19 | M-RectangleDecomposition | preimage = `iUnion` (An xˢ Bn) -> `.iUnion` -> `.prod` | PAC, Separation | 1 |
| MP20 | M-ChoquetCapacitability | `le_antisymm` -> `Nat.rec` compact seq -> capacity = measure | DST | 1 |
| MP21 | M-JensenChain | per-hypothesis Hoeffding -> union bound -> Jensen `sqrt` -> `calc` | Bayesian | 1 |

</details>

The distribution is not uniform. PAC methods dominate (MP1-MP8, 24 instances) because the PAC characterization has the deepest infrastructure chain. Online and Gold methods (MP9-MP12, 8 instances) are self-contained. The structural combinators (MP13-MP14, MP16, MP18) appear across paradigms. The cross-cutting methods (MP15, MP17, MP19-MP21) serve the measurability and separation infrastructure.

<details>
<summary><strong>Lean4 metaprogramming model</strong></summary>

A Lean4 proof state is an `MVarId` -- a metavariable whose type is the current goal. A tactic is a `TacticM Unit` function that assigns the metavariable (closing the goal) or replaces it with new metavariables (subgoals). At the `MetaM` level, `MVarId.assign` closes a goal, `MVarId.getType` inspects the target, and `Lean.Meta.isDefEq` checks definitional equality.

A metaprogram operates above this level. It is a *composition* of tactics that transforms a goal profile (not a single goal) into subgoal profiles. The composition types are:

| Composition | Lean4 construct | Effect |
|-------------|----------------|--------|
| Sequential | `p ; q` | Apply `p`, then `q` to each resulting subgoal |
| Parallel | `all_goals p` | Apply `p` to every open subgoal simultaneously |
| Focused | `focus p` | Apply `p` to the first subgoal only |
| Backtracking | `try p <\|> q` | Attempt `p`, revert state and try `q` on failure |

The metaprogram is the unit of proof method reuse. A human identifies the pattern; an agent can match goal profiles to metaprograms and execute the corresponding tactic sequence.

</details>

### Layer 2: Typed proof operad

The 21 empirical metaprograms are reclassified into a typed calculus: `TPG_FLT`. 1,170 lines of Lean4. 0 sorry. 27/27 tests pass.

The calculus has five components.

> **Interface.** An abstract proof obligation carrying a name, paradigm locks, required premises, and target tag. 18 concrete interfaces defined across 7 paradigms.

> **Generator.** A primitive proof step. 5 structural combinators (paradigm-unlocked) and 12 domain generators (paradigm-locked). Each has a typed input interface and typed output interfaces.

> **Plan.** The syntax of proof generation: `atom(g) | seq(p,q) | par(ps) | guard(lock,p) | choose(alts) | extend(gapName)`.

> **HasType.** The typing judgment: under theory Sigma, plan `p` transforms interface `I` into sub-obligations `Os`. Inductively defined with rules for atom, sequential composition, guarded execution, choice, and extension.

> **FailureRule.** Negative typing. Failure is not the absence of a derivation. It is a derivation of rejection.

<!-- FIGURE: operad_pipelines.svg
     Style: black/white, Times New Roman, old school academic
     Six horizontal pipeline diagrams, one per row, aligned left:

     Row 1 (PAC): iFiniteVCDim -[GrowthConstruction]-> iGrowthBound -[MeasureBridge]-> iHasUC -[UCToPAC]-> iPACLearnable
     Row 2 (DST): iBorelParam -[AnalyticProjection]-> iAnalyticBadEvent -[CompactApproximation]-> iNullMeasBadEvent
     Row 3 (Online): iFiniteLDim -[TreePotential]-> iOnlineLearnable
     Row 4 (Gold): iEXLearnable -[Locking]-> iContradiction
     Row 5 (Separation): iMeasurableHyps -[WitnessSeparation]-> iWBVCMeasTarget + iNotKrappWirth
     Row 6 (Bayesian): iPerHypBound -[JensenChain]-> iPACBayes

     Interfaces as rounded rectangles. Generators as arrows with labels.
     Each row labeled with paradigm name on left margin.
     A red X between Row 3 output and Row 1 middle (iHasUC) labeled "NT1: ill-typed"

     Caption: "Six pipelines, all well-typed. Cross-paradigm composition (red X) is provably ill-typed."
-->

#### Failure as negative typing

Seven failure rules encode proof search pitfalls as first-class typing judgments:

| Rule | Detects | Blocks | Prevents |
|------|---------|--------|----------|
| FD1 | `Fintype_X` in premises | MeasureBridge | Symmetrization on finite domains |
| FD2 | C not finite/countable | UnionBound | Union bound on uncountable classes |
| FD3 | `MeasurableConceptClass` absent | MeasureBridge | Measure-theoretic proof without measurability |
| FD4 | Quantifier order `forall_D_exists_m0` | UCToPAC | Wrong quantifier ordering |
| FD5 | Branchwise shattering target | Adversary | Wrong Littlestone definition |
| FD6 | `PACLearnable_exists_Dm` target | UCToPAC | Existential Dm leak |
| FD7 | Any context | ClassicalChooseUncountable | Non-constructive selection |

These are the failure modes of Section IV, formalized. The theorem `failure_as_negative_typing` proves: if a failure rule matches an interface and blocks a generator, admissibility returns a typed error. The error carries a `RejectReason` -- paradigm mismatch, missing premise, forbidden instance, elaboration dead end, or missing bridge -- that an agent can use to diagnose and reroute.

### Machine-checked structural results

> [!IMPORTANT]
> **Corpus-relative completeness.** All six major proof pipelines type-check under `fltTheory`. Each row in the pipeline diagram above is a proved theorem.

**Paradigm lock.** No generator in `fltTheory` spans PAC, Online, and Gold simultaneously. Proved by exhaustive enumeration over 17 generators. This is Section I's paradigm-locking hypothesis, machine-checked.

**Cross-paradigm impossibility (NT1).** `seq TreePotential UCToPAC` is provably ill-typed at the composition level. Not just inadmissible at the generator level: ill-typed at the *composition* level. The 65-line proof uses `HasType` inversion lemmas and double 17-way generator enumeration. The obstruction: `TreePotential` outputs `iOnlineLearnable`, but `UCToPAC` requires `iHasUC`. No generator bridges them.

**Typed openness.** When the operad cannot type an interface, a `GapSpec` exists: a typed specification of what the theory needs but does not have. This is the formal version of Section VI's structured ignorance. The gap tells you what you don't know. Precisely.

<details>
<summary><strong>Extension mechanism</strong></summary>

The `extension_sound` theorem proves that adding a generator solving a gap yields a well-typed plan. The operad grows by filling typed holes. Each `GapSpec` records the source interface, the needed interface, and the `RejectReason` that created the gap. Future kernel extensions (game theory typeclasses, topology infrastructure for Gold learning) would appear first as `GapSpec` entries before being resolved by new generators.

</details>

### Layer 3: Planning tactic (under construction)

The `bridge_search` tactic is the operational layer above the operad. Given a live Lean4 goal, it classifies by paradigm (inspects `Expr` head before `whnf`), searches the environment for bridge lemmas, and applies or reports a structured `BridgeReport`.

Current status: paradigm classifier works. Environment search does not yet find matches on real FLT goals. Root cause diagnosed: the kernel's theorems are at the top level (not namespaced), and `goal.apply` with `mkConstWithFreshMVarLevels` fails when typeclass arguments cannot be synthesized in the search context. Fix path: `Lean.Meta.DiscrTree` for O(1) lookup by head symbol.

<details>
<summary><strong>Quality funnel model</strong></summary>

The operad includes a four-gate quality model calibrated against the First Proof Benchmark:

| Gate | Measures | Benchmark rate |
|------|----------|---------------|
| Assumption compliance | Hypotheses match the interface | 100% |
| Inference validity | Tactic applications are sound | 98% |
| Goal completion | All subgoals closed | 76% |
| Generalization robustness | Proof survives interface widening | 69% |

The `StepQuality` structure enforces a monotonicity invariant: robustness implies completion implies validity implies compliance. The 29-point drop from validity to robustness reproduces the benchmark's fragility observation: structural generators are robust under interface widening; domain generators are not.

</details>

### Coverage and boundaries

The 21 metaprograms account for approximately 50 of the kernel's 278 theorems directly. The remaining 228:

<details>
<summary><strong>Classification of uncovered theorems</strong></summary>

- **Term-mode compositions** (~90): proved by `exact` or `rfl` delegating to a single lemma. Trivial MP1 instances with no metaprogram structure above the delegation.
- **Private infrastructure lemmas** (~100): helper lemmas (`private lemma`, `have` blocks) serving as substeps *within* metaprograms. Already covered inside metaprogram instances.
- **Unique proof structures** (~38): proof methods appearing exactly once. Candidates for new metaprograms if they recur in future kernel extensions.

</details>

The operad's 17 generators reclassify the 21 empirical metaprograms: structural combinators (MP13, MP14, MP16, MP18) collapse into 5 structural generators; domain methods are preserved as 12 domain generators. The reclassification loses finer tactic-level detail but gains compositionality. Plans built from generators have typed signatures that can be checked, composed, and extended.
