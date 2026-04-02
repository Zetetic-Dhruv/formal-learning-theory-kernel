# Session Context: FLT Kernel README as ArXiv Preprint

Last updated: 2026-04-02. Source: JSONL transcript `833865f9-3ff2-4d26-9468-394f2f761608.jsonl` + live session.

---

## 1. The Project

Lean4 formal learning theory kernel. Three learning paradigms (PAC, Online, Gold) formalized with Mathlib4.

| Metric | Value |
|--------|-------|
| Lines of code | 17,956 (kernel) + 1,170 (world model) |
| Theorems | 278 |
| Sorry count | 2 (both blocked by missing Mathlib: BHMZ STOC 2021, Moran-Yehudayoff 2016) |
| Core sorry | 0 |
| Timeline | ~7 days (March 18-25, 2026) |
| AI used | Claude Opus 4.6 in bypass mode |
| AI alone | 8/67 proofs closed correctly (12 more vacuously) |
| With URT | 65/67 |

**Author:** Dhruv Gupta. Human-guided, AI-driven proof search using URT (Universal Reasoning Theory) framework.

---

## 2. The Document

ArXiv-quality preprint captured as README. NOT a project description.

### Thesis (METHOD level)
"Premise-first, human-guided, AI-driven proof search works, and the infrastructure forced by the types can generate mathematics the premise did not predict."

The subject matter of the kernel is a level BELOW the thesis so new versions don't break it.

### Structure: 4 Parts, 15 Sections

**Part I -- Kernel (Sections I-V):**
- I: Structure of Learning Theory (combinatorics-measure theory axis, hub structure, why these paradigms)
- II: Characterization Theorems (equivalence tables with pseudocode, asymmetry hypothesis, PAC-Bayes bridge)
- III: Separations (IF/THEN/Witness/Exploits table, Borel-analytic separation, figure specs)
- IV: Definition Sensitivity (false/vacuous/displaced taxonomy, finite-infinite tactic hypothesis, premise design blueprint YAML)
- V: Measurability Question (typeclass hierarchy, MeasurableBatchLearner, frontier questions)

**Part II -- Premise (Sections VI-VII):**
- VI: Typed Premise (L0-L7 layers, two invariances: stability under task + structured growth of ignorance)
- VII: Premise Evolution (7 structural hypotheses table, extension/question table, collapsible engineering steps)

**Part III -- Proof Structure (Sections VIII-X):**
- VIII: Proof Technique Taxonomy (metaprogram world model, 21 metaprograms) -- USER IS REVISING
- IX: Pure Mathematics Contributions (PureMath/ modules) -- TO BE WRITTEN
- X: Discovery DAG (Mermaid diagram + dead branch table)

**Part IV -- Apparatus (Sections XI-XV):**
- Not yet started. Methods, Attribution, Citation, Artifact Checklist, Appendices.

### Section Status

| Section | File | Status |
|---------|------|--------|
| Front Matter | drafts/front_matter.md | Finalized |
| I | drafts/section_I.md | Finalized |
| II | drafts/section_II.md | Finalized |
| III | drafts/section_III.md | Finalized |
| IV | drafts/section_IV.md | Finalized |
| V | drafts/section_V.md | Finalized |
| VI | drafts/section_VI.md | Finalized |
| VII | drafts/section_VII.md | Finalized |
| VIII | drafts/section_VIII.md | User revising (proof_world_model.json) |
| IX | drafts/section_IX.md | Placeholder -- next task |
| X | drafts/section_X.md | Draft exists |
| XI-XV | -- | Not started |

---

## 3. Key Technical Content

### Three Learning Paradigms
- **PAC**: Combinatorics x Measure Theory. Symmetrization, Rademacher, VC dimension.
- **Online**: Combinatorics x Game Theory. Littlestone dimension, potential functions, adversary.
- **Gold**: Computability x Topology. Locking sequences, enumeration, mind change ordinals.

### New Mathematics Produced
1. **NullMeasurableSet correction**: Corrects Krapp-Wirth's unnecessarily strong MeasurableSet condition. The implication is strict (proved via Borel-analytic separation).
2. **Borel-analytic separation**: Singleton class over analytic non-Borel set. Suslin projection -> Analytic -> Choquet capacitability -> NullMeasurable. Proof that WellBehavedVC holds but KrappWirth fails.
3. **Interpolation descent**: Composition of Borel classes weakens measurability.
4. **Version space measurability**: Version space learners satisfy MeasurableBatchLearner via rectangle decomposition.
5. **MeasurableBatchLearner as RL policy gate**: RL is possible over all MeasurableBatchLearners even if non-neural.

### PureMath/ Modules (Section IX content)
| Module | Lines | Main Results | Used By |
|--------|-------|-------------|---------|
| ChoquetCapacity | 416 | IsChoquetCapacity, capacitability theorem | AnalyticMeasurability |
| AnalyticMeasurability | 110 | analyticSet_nullMeasurableSet | BorelAnalyticBridge |
| Concentration | 195 | BoundedRandomVariable, chebyshev_majority_bound | Separation |
| Exchangeability | 128 | DoubleSampleMeasure, ValidSplit, SplitMeasure | Symmetrization |
| KLDivergence | 59 | FinitePMF, klDivFinitePMF, crossEntropyFinitePMF | PACBayes |

### World Model (Added post-compaction)
Typed proof operad: TPG_FLT. 1,170 LOC, 0 sorry. Three layers:
- **Empirical** (proof_world_model.json): 21 metaprograms extracted from tactic sequences
- **Formalized** (WorldModel/*.lean): Stratified operad with HasType judgment, negative typing, extension objects
- **Planning** (bridge_search tactic): Under construction. Paradigm classifier works, search doesn't yet.

Key results: corpus-relative completeness (6 pipelines type-check), paradigm lock theorem (no universal generator), NT1 cross-paradigm impossibility (seq TreePotential UCToPAC provably ill-typed).

### Measurability Hierarchy
```
MeasurableHypotheses (L1)
  -> MeasurableConceptClass (L3)
    -> KrappWirthWellBehaved (L5, strict)
```
MeasurableBatchLearner is the RL policy gate. Version space learners satisfy it.

### 21 Metaprograms
M-Pipeline, M-Contrapositive, M-Construction, M-Bridge, M-UnionBound, M-Complement, M-IntegralBound, M-Pigeonhole, M-Adversary, M-Potential, M-LatticeMinMax, M-Locking, M-DefinitionUnfolding, M-WitnessConstruction, M-ComponentMeasurability, M-SetExtensionBridge, M-AnalyticChain, M-SurjectiveTransfer, M-RectangleDecomposition, M-ChoquetCapacitability, M-JensenChain

### Premise Design Blueprint
`assets/premise_blueprint.yaml` -- General methodology (not kernel-specific). Phase 1 (formalization, 8 steps) + Phase 2 (discovery via refactoring, 5 steps). Standalone publishable NeurIPS-quality artifact.

---

## 4. Standing Rules (User Corrections That Are Policy)

These are PERMANENT rules from Dhruv. Violating any of them will require re-doing work.

1. **No URT vocabulary** in published content. URT is unpublished. Internal vocabulary must NOT leak.
2. **No em dashes** anywhere.
3. **No "first instance"** -- always say "an instance." Never reference local construction.
4. **No sorry counting** unless directly relevant to the discussion at hand.
5. **No local/internal references** (I/J/K/L labels, BP1-7, "Level 2/Level 3" -- use real names).
6. **Hypothesis-driven, not descriptive.** Every sentence states a hypothesis, sets one up, or disproves one. Everything else goes to observations/discussions section.
7. **Writing is NEVER planned, ALWAYS discovered.** Use URS manuscript skill for content discovery.
8. **ArXiv quality preprint.** Not a project description.
9. **Old school academic style.** Black and white, sharp, Times New Roman for visuals.
10. **No Claude co-authorship.** Do not add Claude as co-author.
11. **Colors:** Blues, greys, black, red only.
12. **Correlation =/= causation.** Trace actual causal chains. Don't dress up before/after as causation.
13. **Don't soften contributions.** Frame Borel-analytic separation as producing new mathematics.
14. **Implicit sophistication.** URT insights present but never stated directly. Should change how a smart reader perceives the section.
15. **No boasting** about timeline except in Methods section.
16. **Print to screen for feedback before committing.** Never commit without showing Dhruv first.
17. **"HUMAN guided, AI DRIVEN proof search"** -- don't soften this framing.
18. **Don't include Mathlib folder lines in kernel count.** PureMath is separate.
19. **No uniform distribution of text.** Not everything needs to be mentioned. Not everything must be written in the same style. Asymmetric treatment by content weight.
20. **"So what?" test.** Every observation must prove something, raise questions, or predict. Observations that don't matter to an intelligent reader should be cut.

---

## 5. Two Invariance Properties (Section VI, Critical Concept)

1. **Stability under task execution (discovery):** Property of the premise alone. The premise holds still while proofs are derived within it. 65/67 close within the fixed premise.

2. **Structured growth of open frontier (inquiry):** Property of premise + agent. The premise DOES move (measurability typeclasses added, GameInfra extracted), but changes are committed to a DIRECTION. A better premise lets you know exactly what you don't know and the structure of that ignorance, shaping future discovery. This is URT showing itself -- must be stated as design hypothesis with observational evidence, never using URT vocabulary directly.

Key implicit sentence: "The premise accommodated the extension. It did not initiate it."

---

## 6. Key User Quotes (Exact, For Tone Calibration)

- "The writing is NEVER planned and ALWAYS discovered."
- "In scientific writing you are either stating a hypothesis, setting one up or disproving one. Anything else can go under a discussions and observations section."
- "This section is a masterclass in bad writing and uniform distribution of text by LLMs."
- "Every proof in this library answers one question: How does finite combinatorial structure control infinite measure-theoretic objects?"
- "The idea is that the subject matter of the kernel should be a level BELOW the thesis so that new versions don't break the thesis itself!"
- "I have a deep drive for originality and that's my lens/my taste in everything I do."
- "A better premise allows you to know exactly what you don't know and the structure of that ignorance."
- "The idea is not to decorate theorems but to make proof METHODS -- to discover the METAPROGRAM layer."
- "Don't look for correlated elements. You literally know the causation from our conversation."
- "Dude chill. This is your uniform representation of whatever mentioned acting up again."

---

## 7. Deferred Mathematical Problems

1. Compression characterization forward direction (Moran-Yehudayoff -- kernel sorry)
2. Universal trichotomy middle branch (BHMZ -- kernel sorry)
3. Amalgamation weakening measurability (open question, deferred until after README)
4. MeasurableBatchLearner closed under composition (open question, deferred)
5. Gold learner as MeasurableBatchLearner (saved as remark in Section V)
6. Game theory/cryptography + online learning connection (open question)
7. Topology typeclasses for Gold learning (deferred)
8. EX-learning -> RL policy engineering (saved as remark)

---

## 8. File Map

```
formal-learning-theory-kernel/
├── FLT_Proofs/                    The kernel (17,956 LOC, 278 theorems, 2 sorry)
│   ├── Basic.lean, Computation.lean, Data.lean, Process.lean, Bridge.lean
│   ├── Learner/                   Core, Properties, Active, Bayesian, VersionSpace
│   ├── Criterion/                 Gold, PAC, Online, Extended
│   ├── Complexity/                VCDimension, Littlestone, Ordinal, MindChange,
│   │                              Generalization, Rademacher, Symmetrization,
│   │                              GeneralizationResults, Structures, Measurability,
│   │                              BorelAnalyticBridge, GameInfra, Interpolation
│   ├── Theorem/                   Gold, PAC, Online, Separation, Extended,
│   │                              BorelAnalyticSeparation, PACBayes
│   └── PureMath/                  ChoquetCapacity, AnalyticMeasurability,
│                                  Concentration, Exchangeability, KLDivergence
├── world_model/                   Typed proof operad (1,170 LOC, 0 sorry)
│   ├── WorldModel/                Canonical Lean4 source (lake build WorldModel)
│   ├── proof_world_model.json     Empirical 21 MP taxonomy
│   └── dag/                       Machine-generated premise DAG
├── drafts/                        Section drafts for README
├── assets/                        proof_world_model.json, premise_blueprint.yaml
├── premise/                       origin.json, final.json
├── scripts/                       metrics.sh
├── lakefile.lean                  FLT_Proofs (default) + WorldModel
└── README.md                      Integrated preprint (older version; drafts not merged)
```

---

## 9. Immediate Next Steps

1. **Write Section IX** (Pure Mathematics Contributions) using URS manuscript skill
2. Revisit Section VIII together after user finishes proof_world_model.json revisions
3. Draft Sections XI-XV (Part IV: Apparatus)
4. Integrate all section drafts into README.md
5. Create figures/SVGs for Section III
6. Final consistency pass, metrics update, push, tag v2.0.0
