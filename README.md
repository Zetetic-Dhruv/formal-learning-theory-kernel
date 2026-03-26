# Formal Learning Theory Kernel

<p align="center">
  <img src="premise/hero.svg" alt="The Fundamental Theorem of Statistical Learning: five equivalent characterizations of learnability" width="820" />
</p>

A Lean4 formalization of the **Fundamental Theorem of Statistical Learning** (5-way equivalence, 4/5 conjuncts proved), the **Littlestone characterization** of online learnability, **Gold's theorem** on identification in the limit, all **paradigm separations** with constructive witnesses, and the **universal learning trichotomy** (2/3 branches proved). Built on Mathlib4.

The two remaining sorry tactics are blocked by Moran-Yehudayoff 2016 (compression conjecture) and Bousquet-Hanneke-Moran-Zhivotovskiy STOC 2021 (one-inclusion graph (a combinatorial construction on labeled samples)). Both require combinatorial infrastructure absent from Mathlib. They are the frontier, not engineering gaps.

This document presents the **structure of learning theory as revealed by formalization**: the type-theoretic fractures, the proof asymmetries textbooks suppress, and the world model of theorem dependencies that emerges when one forces an entire field through a proof assistant.

---

## I. The Structure of Learning Theory

### The Paradigm Joints

Six decades of learning theory produced three paradigms that textbooks treat as chapters of one story. Formalization reveals they are three theories sharing vocabulary but not structure.

```mermaid
flowchart TB
    classDef shared fill:#1a3a5c,stroke:#4a8abf,color:#fff
    classDef pac fill:#2563eb,stroke:#1d4ed8,color:#fff
    classDef online fill:#374151,stroke:#6b7280,color:#fff
    classDef gold fill:#111827,stroke:#374151,color:#d1d5db

    CC["ConceptClass\n(shared grammar)"]:::shared

    PAC["PAC paradigm"]:::pac
    ONL["Online paradigm"]:::online
    GLD["Gold paradigm"]:::gold

    CC --> PAC
    CC --> ONL
    CC --> GLD

    BL["BatchLearner"]:::pac
    IID["IIDSample"]:::pac
    STP["State + predict"]:::online
    DS["DataStream"]:::gold
    LST["List → conjecture"]:::gold

    PAC --> BL
    PAC --> IID
    ONL --> STP
    GLD --> DS
    GLD --> LST
```

Each paradigm pair carries a binary **obstruction tag**: *obstructed* (the paradigms share vocabulary but no proof infrastructure transfers between them; cross-paradigm theorems require explicit bridges) or *independent* (the paradigms share vocabulary but never interact in any theorem).

| Pair | Tag | Evidence |
|------|-----|----------|
| PAC / Online | obstructed | `online_imp_pac` exists, but `pac_not_implies_online` proves the reverse fails |
| PAC / Gold | obstructed | `ex_not_implies_pac` proves Gold learnability does not entail PAC learnability |
| Online / Gold | independent | No theorem in this library connects them. No shared proof technique. |

No common learner parent type exists. A `BatchLearner` takes `{m : Nat} -> (Fin m -> X x Y) -> Concept X Y`. An `OnlineLearner` carries mutable `State` and processes instances one at a time. A `GoldLearner` takes `List (X x Y) -> Concept X Y`. No common parent captures all three without erasing the structural properties their theorems depend on.

The type system does not permit conflation. This is not a limitation. It is the mathematics.

### Three structural fractures

Formalization revealed three points where the type system of learning theory *cannot* be unified. These are not design choices. Any formalization that proves theorems from all three paradigms will encounter them.

**No common learner.** `BatchLearner`, `OnlineLearner`, and `GoldLearner` have incompatible signatures. A batch learner receives a sample and returns a hypothesis. An online learner commits to a prediction before seeing the label, round by round. A Gold learner conjectures from a growing prefix of an enumeration. The Littlestone characterization requires the sequential commitment; the fundamental theorem requires the batch structure; Gold's theorem requires the enumeration interface. No parent type captures all three without destroying the property each theorem quantifies over.

**No common data interface.** PAC learning quantifies over probability distributions (measure-theoretic). Online learning quantifies over adversary strategies (game-theoretic). Gold-style learning quantifies over enumerations of the target concept (topological/computability). These are three different universal quantifiers with three different mathematical frameworks. A sum type would push the case split into every theorem statement without resolving the incompatibility.

**Five characterizations, five signatures.** The fundamental theorem asserts the equivalence of five differently-typed mathematical statements: PAC learnability (algorithmic), finite VC dimension (combinatorial), finite compression (information-theoretic), vanishing Rademacher complexity (measure-theoretic), and bounded growth function (enumerative). The theorem's significance is precisely that these five objects from five branches of mathematics are equivalent. The type diversity is the content, not an obstacle.

### Four design decisions

The type architecture also encountered four points where alternative designs were possible. These were resolved during premise construction (the first two predicted before compilation, the latter two discovered during it). Each records a tradeoff, not an impossibility.

| Decision | Chosen type | Alternative | Why this choice |
|----------|------------|-------------|-----------------|
| VC dimension type | `WithTop Nat` | `Ordinal` (uniform) | `WithTop Nat` gives `CompleteLattice` for free; `Ordinal` requires explicit `BddAbove` witnesses at every `iSup`. The embedding `VCDim_embed_ordinal` bridges the two when needed. |
| Concept representation | `Set (X -> Bool)` (functions) | `Set (Set X)` (Mathlib set families) | Function application `c x` is natural for learner definitions and error computation. The bridge to Mathlib's `Finset.vcDim` is proved lossless for `Bool` via `conceptToFinset_injective`. |
| ConceptClass variants | Bare `Set` + explicit hypotheses | Typeclass hierarchy (`DecidableConceptClass`, `MeasurableConceptClass`, ...) | Different theorems need decidable, RE, measurable, or multiclass variants. The bare `Set` with explicit hypothesis parameters (e.g., `hmeas_C`) keeps the primary definition simple. Four commented alternatives in `Basic.lean` document the spectrum. |
| Bayesian prior type | `R`-valued (unnormalized density) | `ProbabilityMeasure (Concept X Y)` | The measure-theoretic type is mathematically canonical but requires `MeasurableSpace` on the function space. `R`-valued avoids this. No Bayesian theorem is on the critical path; the alternative is preserved as a commented structure in `Learner/Bayesian.lean`. |

### The Dependency DAG

```mermaid
flowchart TB
    classDef types fill:#d1d5db,stroke:#6b7280,color:#111827
    classDef infra fill:#1a3a5c,stroke:#4a8abf,color:#fff
    classDef thm fill:#2563eb,stroke:#1d4ed8,color:#fff
    classDef vocab fill:#9ca3af,stroke:#6b7280,color:#111827

    L0["L0: Computation\n241 lines"]:::vocab
    L1["L1: Basic\n163 lines"]:::types
    L2["L2: Data\n155 lines"]:::types
    L3["L3: Learner/\n303 lines"]:::types
    L4["L4: Criterion/\n409 lines"]:::types

    subgraph L5["L5: Complexity/ (8,740 lines)"]
        VCD["VCDimension"]:::infra
        LIT["Littlestone"]:::infra
        MC["MindChange"]:::infra
        ORD["Ordinal"]:::infra
        STR["Structures"]:::infra
        GEN["Generalization\n2,997 lines"]:::infra
        SYM["Symmetrization\n3,027 lines"]:::infra
        RAD2["Rademacher\n1,901 lines"]:::infra
        GR["GeneralizationResults"]:::infra
    end

    BR["Bridge\n769 lines"]:::infra

    subgraph L6["L6: Theorem/ (3,985 lines)"]
        GOLD["Gold ✓"]:::thm
        TPAC["PAC ✓"]:::thm
        TONL["Online ✓"]:::thm
        SEP["Separation ✓"]:::thm
        EXT["Extended ⊘"]:::thm
    end

    L7["L7: Process\n180 lines"]:::vocab

    L0 --> L1
    L1 --> L2
    L2 --> L3
    L3 --> L4
    L4 --> L5
    L5 --> BR
    BR --> L6
    L0 --> L7

    VCD --> GEN
    LIT --> GEN
    MC --> GEN
    ORD --> GEN
    STR --> GEN
    GEN --> SYM
    SYM --> RAD2
    GEN --> GR
```

The infrastructure layers (L5) account for **58%** of the codebase. The theorems (L6) account for 27%. Definitions (L1-L4) account for 7%. This ratio is itself a datum about learning theory: the conceptual vocabulary is small, but the proof infrastructure connecting combinatorics to measure theory is vast.

### The shared axis

Every proof in this library answers one question: *How does finite combinatorial structure control infinite measure-theoretic objects?*

The VC dimension is a finite combinatorial quantity (largest shattered set). PAC learnability is a measure-theoretic property (probability over i.i.d. samples). The fundamental theorem says they are equivalent. The entire proof infrastructure exists to cross this bridge: Sauer-Shelah translates VCDim into growth function bounds (combinatorics to combinatorics), symmetrization translates growth bounds into uniform convergence (combinatorics to measure theory), and concentration inequalities translate uniform convergence into PAC guarantees (measure theory to measure theory).

The two sorry theorems sit on this same axis. Moran-Yehudayoff's compression theorem shows that finite VCDim implies a finite compression scheme (combinatorics to combinatorics, but the construction requires approximate minimax on binary matrices). BHMZ's (Bousquet-Hanneke-Moran-Zhivotovskiy) universal learning theorem shows that finite VCDim with infinite Littlestone dimension still permits learning (combinatorics to measure theory, but the construction requires one-inclusion graph aggregation).

There is no proof in this library that does not participate in this axis.

---

## II. The Fundamental Theorem

The central result, stated as `fundamental_theorem` in `Theorem/PAC.lean`:

> **Theorem** (5-way equivalence). *For a concept class* C *over a measurable space* X, *the following are equivalent:*
>
> 1. C *is PAC-learnable*
> 2. C *admits a finite compression scheme*
> 3. *The Rademacher complexity of* C *vanishes uniformly*
> 4. *The sample complexity of* C *is finitely bounded (with quantitative sandwich)*
> 5. *The growth function of* C *is bounded by Sauer-Shelah*
>
> *and all five are equivalent to* VCDim(C) < infinity.

```mermaid
flowchart TB
    classDef center fill:#2563eb,stroke:#1d4ed8,color:#fff
    classDef equiv fill:#1a3a5c,stroke:#4a8abf,color:#fff
    classDef sorry fill:#dc2626,stroke:#991b1b,color:#fff

    VC2["VCDim(C) &lt; ∞"]:::center
    C1["(1) PACLearnable"]:::equiv
    C2["(2) Compression\nscheme"]:::sorry
    C3["(3) Rademacher → 0"]:::equiv
    C4["(4) Sample bounds"]:::equiv
    C5["(5) Growth ≤ S-S"]:::equiv

    VC2 <--> C1
    VC2 <--> C2
    VC2 <--> C3
    VC2 --> C4
    VC2 <--> C5
```

**Status**: 4 of 5 conjuncts fully proved. The forward direction of conjunct 2 (VCDim finite implies compression scheme exists) requires Moran-Yehudayoff's 2016 construction, an approximate minimax argument on bounded-VC binary matrices that has no Mathlib infrastructure.

### The constructive / non-constructive asymmetry

The biconditional `PACLearnable ↔ VCDim < infinity` conceals a deep asymmetry:

- **Forward** (finite VCDim → PAC): **Constructive.** Produces an explicit ERM (Empirical Risk Minimization) learner. Routes through 3,000 lines of symmetrization infrastructure to establish uniform convergence.
- **Backward** (PAC → finite VCDim): **Non-constructive.** Constructs an adversarial hard distribution via contrapositive. The witness is a probability measure that cannot be computed from the learner.

This asymmetry is *unavoidable*. It is not an artifact of the proof strategy but a genuine structural feature of the characterization. The forward direction builds a learner; the backward direction proves one cannot exist.

---

## III. What Formalization Reveals That Textbooks Suppress

### 1. The No-Free-Lunch theorem is false for finite domains

Every standard textbook states a version of: "No learner can learn `Set.univ`." Formalization exposes that this claim, as typically stated, is **provably false** when the domain X is finite.

For finite X: `VCDim(Set.univ) = |X| < infinity`. By the fundamental theorem (forward direction), `Set.univ` *is* PAC-learnable. The learner is trivial: take m >= |X| samples and memorize.

The correct NFL (No-Free-Lunch) theorem requires **infinite X**, where `VCDim(Set.univ) = infinity`. The proof in `Theorem/PAC.lean` constructs this via `Function.extend` on `Subtype.val_injective`. For every finite S, every labeling of S is realized by some function in `Set.univ`, giving VCDim = infinity by `WithTop.eq_top_iff_forall_ge`.

This is not a pedantic point. It reflects a genuine structural divide: the boundary between learnable and unlearnable is not "all functions" vs "some functions" but "finite VC dimension" vs "infinite VC dimension." Cardinality of the hypothesis space is irrelevant.

### 2. Infinite domains double proof complexity

For **finite X**, the PAC learnability proof is direct:
- Hoeffding concentration on i.i.d. samples
- Union bound over finitely many hypotheses
- ~100 lines of Lean4

For **infinite X**, the same mathematical statement requires:
- **Ghost sample (independent copy of the training set) construction** (the double-sample trick)
- **Symmetrization** (exchanging order of expectation and supremum over uncountable C)
- **Exchangeability bounds** via `NullMeasurableSet` + Tonelli interchange
- **Growth function restriction** to reduce uncountable union to polynomial bound
- ~3,000 lines of Lean4

The textbook treatment occupies the same two paragraphs in both cases. The formalization reveals that the infinite-domain case is **30x harder** in proof infrastructure, because the symmetrization argument, invisible in informal mathematics, requires explicit construction of swap functions, product measure isomorphisms, and measurability witnesses for every intermediate step.

The fundamental theorem holds for ALL measurable spaces X. The proof splits via `rcases finite_or_infinite X`: the finite branch is trivial (enumerate all concepts, union bound), roughly 100 lines. The infinite branch requires the full symmetrization apparatus: 3,000 lines. The entire VC dimension theory, as a proof infrastructure, exists to handle the infinite case.

The direct union bound over uncountable concept classes gives 2^{2m}, which is vacuous. The Rademacher route succeeds because it takes suprema over finite sample restrictions, reducing the uncountable class to a polynomial-sized set of labelings. This is why Rademacher complexity appears in the formalization at all: not as a theoretical nicety, but as the only viable route through uncountable C.

The three irreducible layers of the symmetrization route:

```
Layer 3: Growth function restriction              ~400 lines
  GrowthFunction(C, 2m) bounds distinct labelings on 2m points.
  Reduces uncountable sup over C to finite union bound.
  Uses: sauer_shelah_exp_bound, growth_exp_le_delta
         │
         ▼
Layer 2: Ghost-sample symmetrization               ~1,200 lines
  Introduces independent copy S' of sample S.
  Exchanges sup and expectation via exchangeability.
  Pr[sup |gen - emp| ≥ ε] ≤ 2 · Pr[sup |emp' - emp| ≥ ε/2]
  Uses: symmetrization_step, double_sample_pattern_bound,
        finite_exchangeability_bound (NullMeasurableSet + Tonelli)
         │
         ▼
Layer 1: Concentration (Hoeffding)                  ~300 lines
  Per-hypothesis tail bound via sub-Gaussian MGF (moment generating function).
  Pr[emp_err - true_err ≥ t] ≤ exp(-2mt^2)
  Uses: hoeffding_one_sided, cosh_le_exp_sq_half,
        rademacher_mgf_bound
```

No layer can be removed. Layer 3 is needed because C may be uncountable. Layer 2 is needed because the sup over C does not commute with expectation. Layer 1 is needed because individual hypothesis errors are random variables requiring concentration.

### 3. Measure-theoretic regularity is non-negotiable

For uncountable concept classes, the "bad event"

{xs : Fin m -> X | exists h in C, |true_err(h) - emp_err(h)| >= eps}

is not `MeasurableSet`. This is stronger than "not automatically measurable": the sigma-algebra generated by the product measure genuinely does not contain the uncountable union. The standard Lean4/Mathlib integration API (`lintegral`, `integral`) requires measurability witnesses.

The resolution: `NullMeasurableSet` suffices. Integration via `lintegral_indicator_one₀` and `AEMeasurable.indicator₀` requires only almost-everywhere measurability, not pointwise. The formalization introduces `WellBehavedVC` as a regularity assumption: the bad event is null-measurable with respect to the product measure. This is not a formalization artifact. It is a mathematical condition that pen-and-paper proofs suppress by working with parametric or countable hypothesis classes implicitly. For uncountable C, the condition is non-trivial and must be stated.

### 4. The Littlestone tree definition has a subtle bug

The standard branch-wise definition of tree shattering:

```
isShattered C (.branch x l r) =
  (∃ c ∈ C, c x = true ∧ isShattered C l) ∧
  (∃ c ∈ C, c x = false ∧ isShattered C r)
```

does **not** restrict the concept class at recursive calls. Different witness concepts may appear at each tree level without path consistency. Under this definition, `C = {const_true, const_false}` gives `LittlestoneDim = infinity`, but C is trivially online-learnable with 1 mistake.

The corrected definition restricts C at each branch:

```
isShattered C (.branch x l r) =
  (∃ c ∈ C, c x = true) ∧ (∃ c ∈ C, c x = false) ∧
  isShattered {c ∈ C | c x = true} l ∧
  isShattered {c ∈ C | c x = false} r
```

The characterization theorem (`Theorem/Online.lean`) uses the corrected version. The original buggy definition is preserved in `Complexity/Littlestone.lean` with documentation.

### 5. Quantifier ordering in uniform convergence is load-bearing

The definition of uniform convergence uses:

```
∀ ε > 0, ∃ m₀, ∀ D (probability measure), ∀ m ≥ m₀, [UC bound ≤ ε]
```

This is **not** the same as:

```
∀ ε > 0, ∀ D, ∃ m₀, ∀ m ≥ m₀, [UC bound ≤ ε]
```

The first (used in this formalization) makes m₀ independent of D and c, which is essential, because `PACLearnable`'s sample size function `mf(ε, δ)` must be distribution-free. The second allows m₀ to depend on D, which makes `uc_imp_pac` unprovable.

Textbooks state both orders interchangeably. They are not interchangeable.

### 6. Bool is fundamentally special

The bridge between `ConceptClass X Bool` (our type: sets of functions) and `Set (Set X)` (Mathlib's type: set families) is a **bijection**: the map `c ↦ {x | c x = true}` is lossless for `Y = Bool`.

For `|Y| > 2`, this bridge is **lossy**. Multiple functions map to the same family of level sets. The entire formalization (every theorem, every bridge, every complexity measure) operates over `Bool`. This is not a simplification. It reflects the mathematical fact that binary classification is the unique setting where function-based and set-based approaches coincide.

### 7. Definition as proof technique

The standard mind change count records how many times a learner changes its hypothesis. It says nothing about whether the final hypothesis is correct. The backward direction of any characterization theorem ("few mind changes implies learning") must separately establish convergence to the right concept.

`MindChangeOrdinal` in `Complexity/MindChange.lean` takes a different approach. It returns a finite ordinal when the learner converges correctly with finitely many changes. It returns omega otherwise, for both non-convergent and wrong-limit learners. This single design choice collapses the backward direction to: "MindChangeOrdinal < omega implies, by definition, that the learner converges to the correct concept with finitely many changes." The definition IS the proof.

This pattern, encoding a theorem's conclusion into a definition's return type, has no standard name. It appears once in the kernel (for Gold-style learning) and nowhere in the textbook literature. Formalization forced it: Lean4's type system rewards definitions that make theorems structurally obvious.

### 8. The measurable inner event principle

When the target event is non-measurable, find a measurable event inside it with the same probability bound. Conclude by monotonicity.

This pattern appears twice in the kernel, in unrelated proof chains:

1. **Symmetrization** (`Complexity/Symmetrization.lean`): The union over uncountable C of "hypothesis h has generalization gap >= epsilon" is not measurable. Resolution: construct a `NullMeasurableSet` inner event via `MeasureTheory.measurable_measure_prod_mk_left`, then bound by measure monotonicity.

2. **Advice elimination** (`Theorem/Extended.lean`): The product-space success event `SuccessProd` (defined via `Classical.choose`) is not measurable. Resolution: construct `GoodPair`, a measurable inner event satisfying the same probability bound, then transport via monotonicity.

The principle has no pen-and-paper analogue. Measurability is invisible in informal mathematics. Formalization makes it load-bearing: without a measurability witness, `lintegral` and `integral` refuse to compute. The two instances were discovered independently (in different proof chains, weeks apart) and only recognized as the same pattern afterward.

---

## IV. Paradigm Separations: The Witness Constructions

Separation theorems prove that paradigm implications are strict. The constructions are explicit.

```mermaid
flowchart TB
    classDef proved fill:#1a3a5c,stroke:#4a8abf,color:#fff
    classDef sep fill:#dc2626,stroke:#991b1b,color:#fff
    classDef sorry fill:#374151,stroke:#6b7280,color:#d1d5db,stroke-dasharray:5 5

    GLD["Gold (EX)"]:::proved
    PAC2["PAC"]:::proved
    ONL2["Online"]:::proved
    UNI["Universal"]:::proved

    GLD -->|"✗ EX ↛ PAC\nfinite-subset indicators"| PAC2
    ONL2 -->|"✓ online_imp_pac\n(always)"| PAC2
    PAC2 -->|"✗ PAC ↛ Online\nthresholds on ℕ"| ONL2
    UNI -->|"✗ ¬Univ if VCDim = ∞"| PAC2
    UNI -.->|"Branch 2: BHMZ sorry"| ONL2
```

**PAC does not imply Online** (`pac_not_implies_online`): The witness is the threshold class on natural numbers, `C = {(· ≤ n) | n : Nat}`. VC dimension is 1, since only singletons are shattered (thresholds are monotone). Littlestone dimension is infinite: an adversary binary-searches the threshold by querying midpoints, forcing one mistake per query at every depth. The proof constructs the adversary strategy explicitly via induction on tree depth.

**EX (identification in the limit) does not imply PAC** (`ex_not_implies_pac`): The witness is finite-subset indicators on natural numbers. The Gold learner outputs "true on everything seen so far" and converges because every finite concept eventually stabilizes. But every finite subset of natural numbers is shattered, giving VCDim = infinity.

**Online implies PAC** (`online_imp_pac`): The only non-strict separation. Any online learner with mistake bound M gives a PAC learner with sample complexity polynomial in M, 1/epsilon, and 1/delta. The proof routes through the generalization bound from finite Littlestone dimension.

---

## V. The Proof World Model

### Load-bearing vs routine

| Component | LOC | Load-bearing? | Why |
|-----------|-----|---------------|-----|
| Symmetrization infrastructure | 3,027 | **Yes** | Irreducible for infinite-X uniform convergence. Three layers: Hoeffding, ghost-sample symmetrization, growth function restriction. |
| Rademacher infrastructure | 1,901 | **Yes** | Massart's lemma, MGF bounds, VCDim-Rademacher connection. Self-contained chain (does not need symmetrization). |
| NFL core counting | ~200 | **Yes** | Per-sample adversarial construction + product measure positivity. Cannot be simplified. |
| Littlestone characterization | 690 | **Yes** | Corrected tree definition + version space potential argument. Non-constructive at each decision step. |
| Sauer-Shelah bridge | ~100 | Routine | Connects to Mathlib's `Finset.vcDim`. |
| Hoeffding bounds | ~300 | Routine | Concentration inequality infrastructure from Mathlib. |
| Occam's algorithm | ~50 | Routine | Follows immediately from the VCDim gate. |

### Critical path to the fundamental theorem

```
fundamental_theorem
├── vc_characterization ←──── vcdim_finite_imp_pac
│                                  └── vcdim_finite_imp_uc'  [3027 lines, sorry-free]
│                                        ├── symmetrization_uc_bound
│                                        │     ├── hoeffding_one_sided
│                                        │     ├── symmetrization_step
│                                        │     └── finite_exchangeability_bound
│                                        └── growth_exp_le_delta
│                                              └── sauer_shelah_exp_bound
├── pac_imp_vcdim_finite ←──── vcdim_infinite_not_pac
│                                  └── nfl_core [counting argument]
├── fundamental_vc_compression
│   ├── compression_imp_vcdim_finite ← [pigeonhole, proved]
│   └── vcdim_finite_imp_compression ← [SORRY: Moran-Yehudayoff 2016]
├── fundamental_rademacher ←── vcdim_finite_imp_rademacher_vanishing
│                                  └── [self-contained chain, 1901 lines]
└── growth_bounded_imp_vcdim_finite / vcdim_finite_imp_growth_bounded
```

### Quantitative profile

| Metric | Count |
|--------|-------|
| Theorem/lemma statements | 210 |
| Definitions | 157 |
| Structures | 46 |
| Total lines | 14,945 |
| Sorry tactics | 2 |
| Files | 31 |
| Mathlib bridges | 5 (ConceptClass ↔ Set, Shatters ↔ Finset.Shatters, VCDim ↔ Finset.vcDim, IIDSample ↔ Measure.pi, WithTop Nat ↔ Ordinal) |
| Paradigms formalized | 5 with proved theorems (PAC, Online, Gold, Universal, Bayesian); 1 with definitions only (Query) |
| Break points | 7 |
| Maximum dependency chain depth | 7 (Concept → VCDim → fundamental_theorem) |
| Maximum fan-in node | ConceptClass (22 incoming edges) |

### Proof techniques

The library uses 8 distinct proof methods. Their distribution across the codebase is not uniform.

| Method | Paradigm | Where used | Frequency |
|--------|----------|-----------|-----------|
| **Contrapositive** | PAC | `pac_imp_vcdim_finite`, `nfl_theorem_infinite`, `rademacher_vanishing_imp_pac` | 12 theorems |
| **Symmetrization** (ghost sample) | PAC | `symmetrization_step`, `symmetrization_uc_bound`, `vcdim_finite_imp_uc'` | 5 theorems, ~3000 LOC |
| **Adversary construction** | PAC, Online | `pac_not_implies_online`, `adversary_threshold`, `nfl_core` | 6 theorems |
| **Potential function** | Online | `backward_direction` (SOA, Standard Optimal Algorithm), `ldim_versionSpace_le` | 3 theorems |
| **Pigeonhole** | PAC | `compression_imp_vcdim_finite`, `compress_injective_on_labelings` | 4 theorems |
| **Concentration inequality** | PAC | `hoeffding_one_sided`, `chebyshev_seven_twelfths_bound`, `rademacher_mgf_bound` | 8 theorems |
| **Induction on tree depth** | Online | `forward_direction`, `backward_direction`, `adversary_threshold` | 5 theorems |
| **Locking sequence (an enumeration strategy that forces convergence)** | Gold | `gold_theorem` | 1 theorem |

No proof method is shared across all three paradigms. PAC theorems use concentration inequalities and symmetrization. Online theorems use potential functions and tree induction. Gold's theorem uses a locking sequence that appears nowhere else in the library. The shared mathematical axis (Section I) is answered by completely disjoint proof technologies. This is not an artifact of the formalization: the data presentations are incompatible (i.i.d. samples vs. adversarial sequences vs. enumerating streams), and incompatible data presentations force incompatible proof methods.

### Formalization techniques

| Technique | Where used | What it solves |
|-----------|-----------|---------------|
| 7/12-fraction Chebyshev | `boost_two_thirds_to_pac` | Integer threshold in majority-vote boosting |
| Doubled-count trick | Markov bounds in ℕ | Half-integer threshold avoidance |
| Three-step pullback | Product-space transport | One map at a time, not full event |
| Set-equality bridge | Binder-type gaps | Non-reducing functions in lambda terms |
| Nat.pair encoding | Sample splitting | Avoids dependent types in learner signature |
| finite_exchangeability_bound | Symmetrization | NullMeasurableSet Tonelli lemma |

### Key Mathlib dependencies

| Mathlib component | Role in this library |
|------------------|---------------------|
| `MeasureTheory.Measure.pi` | i.i.d. product measure for PAC sample spaces |
| `Finset.vcDim` + `card_le_card_shatterer` | Sauer-Shelah lemma (bridged via `Bridge.lean`) |
| `SetTheory.Ordinal.Arithmetic` | Ordinal VC dimension and mind change ordinals |
| `MeasureTheory.Integral.Bochner` | Expected values in Rademacher and generalization bounds |
| `Computability.TuringMachine` | Computation infrastructure (L0 layer) |

---

## VI. The Two Remaining Sorrys

| File | Theorem | Blocked by | Citation | Role |
|------|---------|-----------|----------|------|
| `Complexity/Generalization.lean` | `vcdim_finite_imp_compression` | Approximate minimax on bounded-VC binary matrices | Moran-Yehudayoff 2016 (arXiv:1503.06960) | Forward direction of conjunct 2 |
| `Theorem/Extended.lean` | `bhmz_middle_branch` | One-inclusion graph learners + doubling aggregation | Bousquet-Hanneke-Moran-Zhivotovskiy, STOC 2021 | Branch 2 of universal trichotomy |

Both are blocked by deep combinatorial constructions with no Mathlib infrastructure. The Moran-Yehudayoff compression theorem has been open in some form since Littlestone and Warmuth's 1986 conjecture; the best known bound is 2^{O(d)}. The BHMZ universal learning construction requires ordinal analysis and tree-based aggregation schemes.

These are not engineering gaps. They are the frontier.

---

## VII. The Discovery DAG: Proof Structure with Counterfactual Branches

The following diagram renders the full theorem dependency structure of this library. Solid arrows are proved dependencies. Dashed arrows with **X** marks are **counterfactual branches**: dead-end proof routes that were explored and killed by specific discoveries during formalization. Each counterfactual branch records the intervention that killed it and what was discovered.

The counterfactual branches are the most informative part of this diagram. They show where the proof *could not* go, and why. Proving that a route is dead is a discovery of the same order as proving a theorem.

```mermaid
flowchart TB
    classDef typ fill:#1e293b,stroke:#475569,color:#e2e8f0
    classDef meas fill:#1e3a5f,stroke:#3b82f6,color:#e2e8f0
    classDef infra fill:#1e3a5f,stroke:#3b82f6,color:#e2e8f0
    classDef bridge fill:#2563eb,stroke:#60a5fa,color:#fff
    classDef thm fill:#1e3a5f,stroke:#3b82f6,color:#e2e8f0
    classDef summit fill:#2563eb,stroke:#60a5fa,color:#fff
    classDef sorry fill:#7f1d1d,stroke:#dc2626,color:#fca5a5
    classDef dead fill:#374151,stroke:#6b7280,color:#9ca3af,stroke-dasharray:5 5

    %% L0: TYPES
    CC["ConceptClass · 22 edges"]:::typ
    BL[BatchLearner]:::typ
    OL[OnlineLearner]:::typ
    GL[GoldLearner]:::typ
    Mpi[Measure.pi]:::bridge
    BR[Bridge: Bool bij.]:::bridge

    %% L1: MEASURES
    VCD["VCDim < ∞"]:::meas
    LD["LittlestoneDim < ∞"]:::meas
    MCO[MindChangeOrd.]:::meas
    GF[GrowthFunction]:::meas
    RAD["Rademacher → 0"]:::meas

    %% L2: INFRASTRUCTURE
    SS[Sauer-Shelah]:::bridge
    UC["Uniform Conv."]:::infra
    WB[WellBehavedVC]:::bridge
    SYM["Symmetrization · 3027 LOC"]:::infra
    HOE[Hoeffding]:::infra
    NFL[NFL core]:::infra
    CS[CompressionScheme]:::infra
    BST[boost_2/3]:::infra

    %% L3: CHARACTERIZATIONS
    VCC["vc_characterization"]:::thm
    LC["littlestone_charact."]:::thm
    GT[gold_theorem]:::thm

    %% L4: SEPARATIONS + APPLICATIONS
    OIP[online_imp_pac]:::thm
    PNO["pac ⇏ online"]:::thm
    ENP["ex ⇏ pac"]:::thm
    NFLI[nfl_theorem_inf.]:::thm

    %% L5: SUMMIT
    FT["FUNDAMENTAL THM · 5-way equiv."]:::summit
    UT["universal_trichotomy · 2/3"]:::sorry

    %% L6: SORRY / FRONTIER
    COMP["SORRY: compression · Moran-Yehudayoff 2016"]:::sorry
    BHMZ["SORRY: bhmz_middle · BHMZ STOC 2021"]:::sorry

    %% DEAD BRANCHES
    CF1["✗ NFL finite X"]:::dead
    CF2["✗ BranchWise LDim"]:::dead
    CF3["✗ Direct union bound"]:::dead
    CF4["✗ UC w/o regularity"]:::dead
    CF5["✗ PAC ∃ Dm"]:::dead
    CF6["✗ D-dep. m₀"]:::dead
    CF7["✗ Bridge |Y|>2"]:::dead

    %% ── L0 → L1 ──
    CC --> VCD
    CC --> LD
    CC --> MCO
    CC --> GF

    %% ── L0/L1 → L2 ──
    VCD --> SS
    VCD --> UC
    VCD --> RAD
    VCD --> CS
    BR --> SS
    SS --> GF
    Mpi --> NFL
    Mpi --> UC
    WB --> SYM
    UC --> SYM
    SYM --> HOE
    SYM --> GF

    %% ── L0/L1 → L3 ──
    BL --> VCC
    VCD --> VCC
    OL --> LC
    LD --> LC
    GL --> GT
    MCO --> GT

    %% ── L3 → L4 ──
    LC --> OIP
    VCD --> PNO
    LD --> PNO
    NFL --> NFLI
    VCC --> NFLI

    %% ── L2-L4 → L5 ──
    VCC --> FT
    CS --> FT
    RAD --> FT
    GF --> FT
    VCC --> UT
    LC --> UT
    BST --> UT
    BHMZ --> UT

    %% ── L6: SORRY deps ──
    COMP --> CS
    BHMZ --> UT

    %% ── DEAD → targets ──
    CF1 -.-> NFLI
    CF2 -.-> LC
    CF3 -.-> UC
    CF4 -.-> SYM
    CF5 -.-> VCC
    CF6 -.-> UC
    CF7 -.-> BR
```

### Reading the counterfactual branches

Each dashed node represents a proof route that was explored and killed. The annotation describes what was discovered:

| # | Intervention | What was discovered | Effect on DAG |
|---|-------------|---------------------|---------------|
| 1 | **NFL for finite X** | Statement is provably false for finite domains | Killed: memorizer learns Set.univ when X is finite. Correct NFL requires infinite X. |
| 2 | **BranchWise Littlestone** | Definition does not restrict C at recursive calls | Killed: characterization theorem is false under the branch-wise definition. Corrected to path-wise. |
| 3 | **Direct union bound** | Bound gives 2^{2m}, not GrowthFunction(C,2m) | Killed: three separate proof attempts confirmed the route is dead. Symmetrization is necessary. |
| 4 | **UC without regularity** | Bad event not measurable for uncountable C | Repaired: introduced WellBehavedVC as regularity gate. NullMeasurableSet suffices for integration. |
| 5 | **PAC with existential Dm** | Existential Dm makes PACLearnable trivially true | Killed: Dm depends on target concept c via memorizer + point mass. Fixed to Measure.pi (distribution-free). |
| 6 | **UC with D-dependent m0** | Sample complexity function cannot depend on D | Repaired: m0 must be distribution-free for PACLearnable's quantifier structure. Fixed quantifier ordering. |
| 7 | **Bridge for general Y** | Bijection is Bool-specific | Boundary: for |Y| > 2, multiple functions map to the same level-set family. All results require Y = Bool. |

Interventions 1, 3, and 5 killed provably false statements. Interventions 2, 4, and 6 repaired definitions or added hypotheses to rescue viable routes. Intervention 7 established a setting-specific boundary: the library's results hold for binary classification, and the restriction is mathematically necessary.

The counterfactual branches collectively explain why the library has the shape it does. The NFL correction (1) explains why all NFL theorems require `[Infinite X]`. The Littlestone fix (2) explains why `Theorem/Online.lean` defines its own `LTree.isShattered` rather than using `Complexity/Littlestone.lean`. The symmetrization necessity (3) explains why 58% of the codebase is infrastructure. The WellBehavedVC introduction (4) explains the regularity hypothesis that appears in every measure-theoretic theorem. The PAC repair (5) explains why `Measure.pi` appears in the definition rather than an existential. The quantifier fix (6) explains the specific quantifier ordering in `HasUniformConvergence`. The Bool boundary (7) explains why the entire library operates over `Bool`.

---

## VIII. Premise Evolution: From Textbook to Kernel

The type architecture began as a derivation from informal learning theory (the author's textbook). Formalization forced modifications. Some were mathematical discoveries (the textbook was wrong). Others were forced by Mathlib's current state. The premise-evolution DAG shows which.

<div style="overflow-x: auto; overflow-y: auto; max-height: 1000px; border: 1px solid #d1d5db; border-radius: 6px; padding: 8px;">
  <img src="premise/evolution_dag.svg" alt="Premise Evolution DAG: origin types, interventions, and final types" />
</div>

Seven of ten core types required attention during formalization. Five were mathematical discoveries: the original definitions were provably inadequate (PACLearnable, NFL, LittlestoneDim, HasUniformConvergence, MindChangeOrdinal). One was forced by Mathlib's ordinal/VC dimension API (VCDim: Nat to WithTop Nat). One remains at the frontier: CompressionScheme is blocked by Moran-Yehudayoff 2016, a mathematical result absent from Mathlib, not an API constraint. The remaining three types (ConceptClass, Bridge, BayesianLearner) survived formalization unchanged, though ConceptClass required 4 alternative definitions to be evaluated and rejected during premise creation. One type was added that was not in the original premise: `WellBehavedVC`, a regularity assumption for uncountable concept classes that textbooks suppress.

---

## IX. Methodology

Built in **7 days** (March 18-25, 2026) using **Claude Code (Opus 4.6)** guided by an epistemological framework for AI-assisted formalization.

### The premise

Before proof discovery began, a **type architecture premise** was derived: 42 concept nodes across 8 layers (L0-L7), with explicit paradigm joints, obstruction tags, structural hypotheses, and compilation constraints. This premise, recorded in `premise/origin.json`, defined the typed hypothesis space within which proof search operated.

The premise served as a **grammar** for the AI: instead of jointly discovering types and proofs (which produces trivially-true theorems, sorry-in-Prop, and type homogeneity), the AI searched for proofs within a well-scoped, pre-validated type structure.

### The delta

| | Before (origin) | After (final) |
|-|-----------------|---------------|
| Lines | 2,912 | 14,945 |
| Files | 10 monolithic | 31 modular |
| Sorry count | 69 | 2 |
| Structural hypotheses tested | 0 of 7 | 7 of 7 (3 confirmed as fractures, 4 resolved as design decisions) |

**Without the framework**, Claude closed 8 of 67 open proofs correctly (and 12 more trivially/vacuously). The dominant failure mode was **adding new sorrys faster than closing existing ones** and **attacking only the easiest proofs** (trivial computation lemmas).

**With the framework**, 65 of 67 were closed. The remaining 2 are blocked by results absent from Mathlib, not by AI capability.

### Type architecture stability

The type distribution across the kernel remained constant through 12,033 lines of proof addition:

<p align="center">
  <img src="premise/type_distribution.svg" width="600" alt="Type distribution: origin vs final"/>
</p>

Abbreviations, propositions, and structures held at 32.9%, 31.4%, and 27.9% respectively in both the origin premise (2,912 LOC) and the final kernel (14,945 LOC). The proof infrastructure redistributed across layers (L5 Complexity grew from a stub to 8,740 lines), but the balance of type categories did not change. The pre-designed grammar absorbed the proofs without architectural modification.

Both the origin and final type architectures are recorded in `premise/origin.json` and `premise/final.json`.

### Discovery process

The full discovery process (10,000+ recorded tactics, 74 reasoning traces, error mode analysis) is documented in the [companion discovery repository](https://github.com/Zetetic-Dhruv/formal-learning-theory-discovery).

---

## X. Building

```bash
lake build   # Requires elan. First build fetches Mathlib (~20 min).
```

Lean `v4.29.0-rc6` | Mathlib4 from `master`

---

## XI. Companion Repositories

This kernel is one component of a larger programme. The four public companion repositories:

| Repository | Role | Relationship to this repo |
|-----------|------|--------------------------|
| [formal-learning-theory-discovery](https://github.com/Zetetic-Dhruv/formal-learning-theory-discovery) | Discovery process: 74 reasoning traces, metakernel, 10,000+ exploration paths | Documents *how* this kernel was built |
| [formal-learning-theory-dataset](https://github.com/Zetetic-Dhruv/formal-learning-theory-dataset) | Structured concept graph (142 nodes, 260 edges) + fine-tuned SLM | The concept graph that informed the type architecture in `premise/origin.json` |
| [formal-learning-theory-book](https://github.com/Zetetic-Dhruv/formal-learning-theory-book) | *A Textbook of Formal Learning Theory* (202 pages, 18 chapters) | Informal exposition of the same mathematical content |
| [First-Proof-Benchmark-Results](https://github.com/Zetetic-Dhruv/First-Proof-Benchmark-Results) | Empirical analysis of AI-driven proof discovery across frontier models | Broader context: proof discovery benchmarks beyond this library |

---

## XII. Citation

```bibtex
@software{gupta2026flt_kernel,
  author       = {Gupta, Dhruv},
  title        = {Formal Learning Theory Kernel: {Lean4} Formalization
                  of the Fundamental Theorem of Statistical Learning},
  year         = {2026},
  url          = {https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel},
  note         = {31 files, 14{,}945 LOC, 2 sorry.
                  Proof discovery via Claude Opus 4.6.}
}

@software{gupta2026flt_discovery,
  author       = {Gupta, Dhruv},
  title        = {Formal Learning Theory Discovery: Empirical Analysis
                  of {AI}-Guided Proof Search},
  year         = {2026},
  url          = {https://github.com/Zetetic-Dhruv/formal-learning-theory-discovery},
  note         = {74 reasoning traces, 10{,}000+ exploration paths.}
}

@software{gupta2026flt_book,
  author       = {Gupta, Dhruv},
  title        = {A Textbook of Formal Learning Theory},
  year         = {2026},
  url          = {https://github.com/Zetetic-Dhruv/formal-learning-theory-book},
  note         = {202 pages, 18 chapters.}
}
```

---

## XIII. Attribution

Copyright (c) 2026 Dhruv Gupta. Apache 2.0.

Proof discovery was conducted using Claude Opus 4.6 (Anthropic) via Claude Code, guided by an epistemological framework for structured AI-assisted formalization. The type architecture, proof scoping, error correction, and all editorial decisions are the author's.
