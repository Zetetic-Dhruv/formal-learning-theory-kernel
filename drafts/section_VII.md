# Section VII — FINAL DRAFT

---

## VII. Premise Evolution

Two unfoldings of the premise test the invariance properties defined in Section VI.

### Unfolding 1: Stability under task execution

The origin premise: a typed DAG with 8 dependency layers, 42 concept nodes, and 67 proof placeholders, compiled against Mathlib. Seven structural hypotheses were embedded as testable predictions.

| Structural hypothesis | Prediction | Outcome |
|----------------------|-----------|---------|
| No common learner parent | BatchLearner, OnlineLearner, GoldLearner cannot share a parent type | **Confirmed** (fracture): each characterization quantifies over a signature-specific property |
| No common data interface | IIDSample, DataStream, TextPresentation involve incompatible quantifiers | **Confirmed** (fracture): PAC over distributions, Online over adversaries, Gold over enumerations |
| Five characterization signatures | The 5-way fundamental theorem requires five differently-typed objects | **Confirmed** (fracture): PAC, VC, compression, Rademacher, growth function span five domains |
| WithTop Nat vs Ordinal | Two viable types for VC dimension | **Resolved** (design decision): WithTop Nat chosen, VCDim_embed_ordinal bridges |
| Function-class vs set-family | ConceptClass X Bool vs Set (Set X) | **Resolved** (design decision): bridge proved lossless for Bool |
| ConceptClass variants | Bare Set vs typeclass hierarchy | **Resolved** (design decision): typeclass hierarchy adopted in unfolding 2 |
| Bayesian prior type | R-valued density vs ProbabilityMeasure | **Resolved** (design decision): R-valued chosen for proof ergonomics |

Five definitions were corrected during proof search (Section IV). No layer was added. No paradigm was introduced. The premise held still: perturbations were definitional, not architectural.

<div style="overflow-x: auto; overflow-y: auto; max-height: 1000px; border: 1px solid #d1d5db; border-radius: 6px; padding: 8px;">
  <img src="premise/evolution_dag.svg" alt="Premise Evolution: origin types, interventions, and final types" />
</div>

### Unfolding 2: Structured growth of the open frontier

The proof-discovery kernel exposed ad-hoc measurability hypothesis threading across 8 files. The premise was extended.

| Premise addition | What it produced | What question it opened |
|-----------------|-----------------|------------------------|
| `MeasurableConceptClass` (L3) | Borel-analytic separation theorem | Does the gap contain natural concept classes? |
| `KrappWirthWellBehaved` (L5) | Strict hierarchy: KrappWirthWellBehaved implies MeasurableConceptClass but not conversely | Is there a measurability dimension? |
| `MeasurableBatchLearner` (L3) | Version space measurability theorem (non-neural RL policy class) | Is the measurable learner class closed under composition? |
| `BorelRouterCode` (L5) | Interpolation descent theorem | Does amalgamation also weaken measurability? |
| Measurability refactoring (L1, L3, L5) | Typeclass hierarchy replacing 8-file hypothesis threading | Does network depth increase measurability complexity? |
| PureMath/ extraction | 908 lines of field-independent pure math | — |
| GameInfra.lean extraction | 219 lines of explicit game infrastructure | Does the adversary-learner pattern connect to bandits or chosen-plaintext attacks? |

Every premise addition produced theorems, extracted infrastructure, or opened precisely stated questions. The frontier grew from 2 specific blockers to 7 research questions, each with known mathematical approaches or specific obstructions.

<details>
<summary><strong>Engineering and proof steps behind the extensions</strong></summary>

**Measurability typeclasses.** The original kernel threaded `hmeas_C`, `hc_meas`, `hWB` as explicit parameters through 8 files. Bundling these into `MeasurableConceptClass` at L3 was a refactoring step. Once bundled, `WellBehavedVC` became a named condition rather than an inline hypothesis, which made it possible to ask whether Krapp-Wirth's stronger condition (MeasurableSet) was equivalent. The singleton class construction showed it was not.

**Version space measurability.** The boosting proof required integrating over the learner's output. Lean4 refused without a measurability witness for the joint map `(training_data, x) → L(training_data)(x)`. Formalizing this as `MeasurableBatchLearner` created a checkable gate. The version space proof decomposes the evaluation preimage into countable unions of measurable rectangles via `Nat.find` and `IsFirstConsistent`.

**Interpolation descent.** The Borel-analytic separation established that the NullMeasurableSet level is inhabited. The interpolation theorem asked: what operation produces concept classes at that level? The `patchEval` construction combines two Borel-parameterized families via a measurable router. The Suslin projection over the combined parameter space produces analytic bad events.

**Pure math extraction.** Concentration inequalities, exchangeability infrastructure, KL divergence, and Choquet capacitability were inlined in proof files. Extracting them to PureMath/ required verifying each module compiles independently of the learning theory theorems it serves.

**Game infrastructure.** Version space, adversary strategy, SOA, and mistake counting were defined inside `Theorem/Online.lean`. Extracting them to `GameInfra.lean` required separating the game-theoretic definitions from the characterization proofs that use them.

</details>

### The pattern

Unfolding 1 consumed the premise: proof search closed 65 of 67 placeholders within the fixed type architecture. Unfolding 2 extended it: each extension produced both results and questions more precise than those that preceded them. A premise that passes only the first test is adequate. A premise that passes both is generative.
