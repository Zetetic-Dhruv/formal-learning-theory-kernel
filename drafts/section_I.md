# Section I — FINAL DRAFT

---

## Part I: The Kernel

## I. The Combinatorics-Measure Theory Axis

Each learning paradigm's proof methods are determined by the mathematical domains its definitions cross. In this kernel, PAC learning sits at the intersection of finite combinatorics and infinite measure theory. Online learning sits at the intersection of combinatorics and game theory. Gold-style learning sits within computability and topology. The paradigms connect to each other only through PAC.

This hypothesis predicts: given a new paradigm's type signature, the proof methods it requires are determined before a single theorem is proved. A paradigm whose definitions cross into measure theory will need concentration inequalities and symmetrization. A paradigm whose definitions involve sequential commitment will need game-theoretic potential arguments. A paradigm whose definitions involve convergence on enumerations will need topological arguments. The premise's type choices are a routing table for proof search. The hypothesis would be falsified by a PAC proof requiring no measure theory, an Online proof requiring concentration inequalities, or a direct Online-Gold theorem bypassing PAC.

### The PAC crossing

Every PAC theorem in this kernel crosses from combinatorics to measure theory. The fundamental theorem asserts that PAC learnability (a measure-theoretic property: probability over i.i.d. samples) is equivalent to finite VC dimension (a combinatorial property: the largest shattered set). The proof infrastructure exists to bridge the crossing:

| Step | From | To | Mechanism |
|------|------|----|-----------|
| Sauer-Shelah | VCDim (combinatorial) | Growth function bound (combinatorial) | Counting restricted labelings |
| Symmetrization | Growth function bound | Uniform convergence (measure-theoretic) | Ghost sample + exchangeability |
| Concentration | Uniform convergence | PAC guarantee (measure-theoretic) | Hoeffding via sub-Gaussian MGF |

A paradigm staying within one mathematical domain would not need this infrastructure, which accounts for 56% of this kernel precisely because PAC crosses two domains.

### Online learning: combinatorics and game theory

The Littlestone characterization asserts that online learnability is equivalent to finite Littlestone dimension. Both sides are combinatorial, but the proof method is game-theoretic. The adversary inspects the learner's prediction and plays the opposite label. The Standard Optimal Algorithm (SOA) is a minimax strategy: at each step, predict the label whose version-space branch has higher Littlestone dimension. The version space is the game state. The Littlestone dimension is the game value.

The game-theoretic infrastructure (version space, adversary strategy, SOA, mistake counting) is extracted to `Complexity/GameInfra.lean` (219 lines). No product measures. No concentration inequalities. No sigma-algebras. The proof infrastructure is 690 lines, not 5,000, because no combinatorics-to-measure-theory crossing is needed.

The adversary-learner interaction pattern (sequential commitment, state update, payoff counting) is shared with bandits and chosen-plaintext attacks, suggesting a common game-theoretic abstraction across these settings.

### Gold-style learning: computability and topology

Gold's theorem constructs a locking sequence: an enumeration strategy that forces the learner to commit to a finite concept, then extends the adversarial text to be consistent with the infinite target. This is a computability argument operating on enumerations. The mind change characterization uses topological convergence: the sequence of conjectures must stabilize on a growing prefix of the enumeration, which is convergence in the pointwise topology on function spaces.

Gold-style learning shares neither the combinatorial shattering structure of PAC and Online nor the measure-theoretic machinery of PAC. It is the only paradigm in this kernel that does not share any proof infrastructure with either of the other two, which is why no theorem connects it to Online directly. On countable domains (which Gold's theorem requires via `[Countable X]`), every function is measurable under the discrete sigma-algebra. Measurability is trivially satisfied. The proof difficulty is elsewhere: in the enumeration structure and the convergence argument.

### The hub structure

PAC is the hub. Online connects to PAC through the VC dimension: `online_imp_pac` proves that any online learner with mistake bound M gives a PAC learner. Gold connects to PAC only negatively: `ex_not_implies_pac` proves that Gold-style learnability does not imply PAC learnability. No theorem in the learning theory literature known to us directly connects online learnability and Gold-style identification without routing through PAC. We state this as a hypothesis, not a fact: if a direct Online-Gold theorem exists, the hub structure would change.

| Pair | Relationship | Evidence | Through PAC? |
|------|-------------|----------|-------------|
| PAC / Online | Obstructed: one direction holds, reverse fails | `online_imp_pac`, `pac_not_implies_online` | N/A (direct) |
| PAC / Gold | Obstructed: Gold does not imply PAC | `ex_not_implies_pac` | N/A (direct) |
| Online / Gold | Independent (hypothesis) | No known direct theorem | All paths route through PAC |

### Why the learner types cannot unify

The learner types are incompatible because each characterization theorem quantifies over a structural feature that exists only in its paradigm's signature.

The fundamental theorem requires that sample complexity `mf(ε, δ)` is distribution-free: it must work for all probability measures simultaneously. This measure-theoretic universal quantifier forces the `BatchLearner` signature, where the sample size `m` is a parameter that depends only on `ε` and `δ`, not on the distribution.

The Littlestone characterization requires that the learner commits to a prediction before seeing the label. This temporal commitment is a property of the `OnlineLearner` signature's `predict : State → X → Y`: the output depends on state accumulated from past rounds, not on the current round's label.

Gold's theorem requires that the learner stabilizes on a growing enumeration prefix. This convergence property is a property of the `GoldLearner` signature's `List (X × Y) → Concept X Y`: the output depends on the full history, and the theorem's conclusion is that the output eventually stops changing.

A parent type that erases the sample size parameter, the temporal commitment, or the growing prefix would erase the mathematical property that the corresponding theorem quantifies over. The type incompatibility is entailed by the theorems.

### What this predicts

If a new learning paradigm is formalized, its proof methods will be determined by which mathematical domains its definitions cross.

A paradigm crossing combinatorics and information theory (e.g., compression-based learning) will need information-theoretic proof infrastructure but may share the combinatorial side with PAC. A paradigm crossing measure theory and game theory (e.g., stochastic online learning) will need tools from both PAC and Online. A paradigm staying within a single domain will require proportionally less proof infrastructure.

For AI-driven proof search: an agent that reads the goal's type signature before choosing tactics can restrict its search space to the paradigm-appropriate methods. Goals mentioning `MeasureTheory.Measure` route to the PAC tactic library. Goals mentioning sequential state route to the Online tactic library. Goals mentioning enumerations and convergence route to the Gold tactic library. The premise is a routing table.
