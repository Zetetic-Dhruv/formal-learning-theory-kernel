# Section VIII — FINAL DRAFT

---

## Part III: The Proof Structure

## VIII. Proof Technique Taxonomy

The kernel's proof architecture is encoded as a metaprogram world model in [`assets/proof_world_model.json`](assets/proof_world_model.json). The primary unit is the metaprogram: a structured proof prediction with typed inputs, outputs, strategy steps, preconditions, failure diagnostics, and known instances. An agent consuming the world model can route proof search from a goal's type signature to the appropriate methods and infrastructure without reading the kernel's source files.

### How the world model works

Given a new proof goal, an agent:

1. **Matches the goal profile.** The goal's type signature (shape, quantifier depth, mentions of specific types) is matched against 10 goal profile patterns. Each pattern routes to one or more metaprograms and lists which metaprograms to avoid.

2. **Selects a metaprogram.** Each metaprogram specifies a strategy: a sequence of steps with typed inputs and outputs, the infrastructure files required, and the preconditions that must hold. For example, `MP_pac_chain` (PAC characterization via uniform convergence) is a 3-step pipeline: Sauer-Shelah → Symmetrization → Concentration, requiring `[MeasurableConceptClass X C]` and 7,925 lines of infrastructure.

3. **Checks failure diagnostics.** Before executing, the agent consults 7 failure diagnostics. Each diagnostic has an early detection rule that can be checked against the local context. For example: if `[Fintype X]` is in context, do not attempt symmetrization (it produces 2^{2m} instead of GrowthFunction).

4. **Composes methods via typed interfaces.** Methods compose when one's output type matches another's input type. The world model encodes 8 composition types with bridge lemma references. For example: Sauer-Shelah outputs a GrowthFunction bound, which is the input type for Symmetrization, bridged by `sauer_shelah_exp_bound`.

### The metaprograms

| Metaprogram | Type | Paradigm | Strategy summary | Infrastructure |
|-------------|------|----------|-----------------|----------------|
| PAC chain | Pipeline (3 steps) | PAC | Sauer-Shelah → Symmetrization → Concentration | 7,925 lines |
| PAC contrapositive | Single step | PAC | Contrapositive + hard distribution witness | 200 lines |
| SOA construction | Pipeline | Online | Version space potential → mistake bound = Ldim | 400 lines |
| Adversary tree | Single step | Online | Adversary on shattered tree forces n mistakes | 100 lines |
| Gold locking | Single step | Gold | Locking sequence on monotone enumeration | 0 lines (self-contained) |
| Witness construction | Construction | Any | Build concept class satisfying A, violating B | varies |
| Symmetrization | Pipeline (3 steps) | PAC (infinite X) | Ghost sample → exchangeability → Hoeffding | 3,027 lines |
| Finite enumeration | Single step | PAC (finite X) | Enumerate, Hoeffding, union bound | ~100 lines |
| Borel-analytic bridge | Pipeline (3 steps) | Cross-cutting | Borel parameterization → Suslin → Choquet | 783 lines |
| PAC-Bayes chain | Pipeline (3 steps) | Bayesian | Per-hypothesis Hoeffding → union → Jensen | 584 lines |
| Rectangle decomposition | Single step | Cross-cutting | Nat.find preimage → countable union of rectangles | 203 lines |
| Interpolation descent | Reduction | Cross-cutting | Reduce to patchEval range → apply bridge | Interpolation.lean |

### Paradigm locking

Methods are locked to paradigms because their preconditions reference paradigm-specific types. The lock is detectable from the goal's type signature.

| Method | Locked to | Detection: goal mentions |
|--------|-----------|------------------------|
| Symmetrization, Concentration | PAC | `MeasureTheory.Measure`, `ENNReal` |
| Version space potential, Tree induction | Online | `OnlineLearner.State`, `versionSpace`, `LTree` |
| Locking sequence, Topological convergence | Gold | `DataStream`, `TextPresentation`, `MindChangeOrdinal` |
| Suslin + Choquet | Cross-cutting | `AnalyticSet`, `NullMeasurableSet`, `PolishSpace` |
| KL-divergence / Jensen | Bayesian | `FinitePMF`, `klDiv` |
| Rectangle decomposition | Cross-cutting | `MeasurableBatchLearner`, `Nat.find` |

No method crosses all three classical paradigm boundaries. The paradigm-locking hypothesis (Section I) predicts that formalizing a theorem crossing new domains will require methods not in this table.

### Failure diagnostics

The world model encodes 7 failure diagnostics, each with early detection rules:

| Failure | Early detection | Fix |
|---------|----------------|-----|
| Symmetrization on finite domain | `[Fintype X]` in context | Route to finite enumeration |
| Union bound on uncountable C | C not provably finite/countable | Insert symmetrization |
| Measurability blocked | `[MeasurableConceptClass X C]` absent | Add typeclass or route to Borel-analytic bridge |
| Quantifier order wrong | UC uses `∀ D, ∃ m₀` instead of `∃ m₀, ∀ D` | Use uniform ordering |
| Branch-wise Littlestone | `isShattered` does not restrict C at recursive calls | Use path-wise definition (GameInfra.lean) |
| Existential Dm leak | PACLearnable uses `∃ Dm` instead of `Measure.pi` | Use Measure.pi definition |
| Non-measurable selection | Goal has `∃ h ∈ C` with `Classical.choose` over uncountable set | Measurable inner event pattern |

### Infrastructure by domain

| Module | Lines | Domain | Field-independent? |
|--------|-------|--------|--------------------|
| PureMath/ChoquetCapacity | 416 | Descriptive set theory | Yes |
| PureMath/AnalyticMeasurability | 110 | Descriptive set theory | Yes |
| PureMath/Concentration | 195 | Probability theory | Yes |
| PureMath/Exchangeability | 128 | Measure theory | Yes |
| PureMath/KLDivergence | 59 | Information theory | Yes |
| Complexity/GameInfra | 219 | Game theory | No |

908 lines in PureMath/ are field-independent and reusable in any Lean4 project.

### Quantitative profile

All counts generated by `scripts/metrics.sh`.

| Metric | Count |
|--------|-------|
| Theorem/lemma statements | 278 (190 public, 88 private) |
| Definitions | 200 |
| Structures | 54 |
| Total lines | 17,956 |
| Files | 43 |
