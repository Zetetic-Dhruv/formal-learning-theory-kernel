# Section II — FINAL DRAFT

---

## II. Characterization Theorems

A characterization theorem asserts that two objects from different mathematical domains are equivalent. The theorem's difficulty is proportional to the distance between the domains it bridges.

### The equivalence landscape

| Theorem | Object A (structural) | Object B (algorithmic) | Domains bridged |
|---------|----------------------|----------------------|-----------------|
| Fundamental theorem | VCDim(C) < ∞ | PACLearnable(C): `select hypothesis minimizing empirical error over C` | Combinatorics ↔ Measure theory |
| Littlestone char. | LittlestoneDim(C) < ∞ | OnlineLearnable(C): `predict majority label in version space V` | Combinatorics ↔ Game theory |
| Mind change char. | MindChangeOrdinal < ω | EXLearnable(C): `conjecture first h in C consistent with prefix` | Ordinal arithmetic ↔ Computability |
| PAC-Bayes | KL(Q ‖ P) penalty | Gibbs error bound: `classify via h sampled from posterior Q` | Information theory ↔ Combinatorics × Measure theory |

Each row connects a structural object (a dimension, a divergence) to an algorithmic object (a learner, a bound). The type signatures of A and B live in different mathematical domains. The proof infrastructure required to bridge them is determined by the distance between those domains.

### The asymmetry hypothesis

**In biconditional characterization theorems where both directions are proved, the constructive direction (structural → algorithmic: "build a learner from a bound") requires more proof infrastructure than the non-constructive direction (algorithmic → structural: "if a learner exists, derive the bound").**

| Theorem | Forward (structural → algorithmic) | Backward (algorithmic → structural) | Ratio |
|---------|-----------------------------------|-------------------------------------|-------|
| Fundamental theorem | ERM via symmetrization, 3,027 lines | Contrapositive + counting, ~200 lines | 15:1 |
| Littlestone char. | SOA via version space potential, ~400 lines | Adversary construction, ~100 lines | 4:1 |

The pattern: building the algorithm from the structural bound is harder than proving the structural bound from the algorithm's existence. The 15:1 ratio in the fundamental theorem reflects the combinatorics-to-measure-theory crossing from Section I: the symmetrization infrastructure exists because the constructive direction must bridge from a combinatorial bound to a measure-theoretic guarantee. The 4:1 ratio in Littlestone is smaller because both directions stay within combinatorics and game theory.

This predicts that for any new characterization theorem in this kernel, the constructive direction will dominate the proof burden.

PAC-Bayes is a one-directional bound (prior + posterior + data → generalization guarantee), not a biconditional. The asymmetry hypothesis does not apply. PAC-Bayes exhibits a different asymmetry: pointwise-to-uniform (per-hypothesis Hoeffding is straightforward; uniformizing over all hypotheses via Jensen requires the KL machinery).

### The fundamental theorem

The central result, stated as `fundamental_theorem` in `Theorem/PAC.lean` (under `[MeasurableConceptClass X C]`):

> **Theorem** (5-way equivalence). *For a concept class C over a measurable space X, the following are equivalent:*
>
> 1. *C is PAC-learnable*
> 2. *C admits a finite compression scheme*
> 3. *The Rademacher complexity of C vanishes uniformly*
> 4. *The sample complexity of C is finitely bounded (with quantitative sandwich)*
> 5. *The growth function of C is bounded by Sauer-Shelah*
>
> *and all five are equivalent to* VCDim(C) < infinity.

Four of five equivalences are proved. The forward direction of the compression characterization (finite VCDim implies compression scheme exists) is blocked by Moran-Yehudayoff 2016.

The constructive direction (VCDim → PAC) produces an explicit ERM learner and routes through 3,027 lines of symmetrization infrastructure to establish uniform convergence. The non-constructive direction (PAC → VCDim) proves the contrapositive: infinite VCDim implies a hard distribution exists. The proof is ~200 lines. The 15:1 ratio is the largest in the kernel and reflects the combinatorics-to-measure-theory crossing from Section I: the symmetrization infrastructure exists because the constructive direction must bridge from a combinatorial bound to a measure-theoretic guarantee.

### The Littlestone characterization

Online learnability is equivalent to finite Littlestone dimension. The forward direction constructs the SOA (Standard Optimal Algorithm), a minimax strategy over version spaces: ~400 lines. The backward direction constructs an adversary that forces mistakes along a shattered tree: ~100 lines. The 4:1 ratio is smaller than the fundamental theorem's 15:1 because both directions stay within combinatorics and game theory. No domain crossing is needed.

### Gold's theorem and definition as proof technique

The mind change characterization asserts: a concept class is EX-learnable if and only if every text presentation has finite mind change ordinal.

The definition of `MindChangeOrdinal` encodes the forward direction:

```
MindChangeOrdinal X L c T :=
  if change_set.Finite then
    if ∃ t₀, ∀ t ≥ t₀, L.conjecture (T.prefix t) = c then
      change_set.toFinset.card    -- finite ordinal: converged correctly
    else
      omega                       -- omega: converged to wrong concept or did not converge
  else
    omega                         -- omega: infinitely many changes
```

The return type carries the convergence proof: a finite ordinal means the learner both converged AND converged correctly. The backward direction of the characterization (EX → finite ordinal) requires showing the change set is finite and the limit is correct: ~30 lines. The forward direction (finite ordinal → EX) is a definitional consequence: if the ordinal is finite, the definition's branching structure already guarantees correct convergence.

The mind change characterization does not participate in the asymmetry hypothesis because the forward direction is not proved but defined. It is an instance of a different phenomenon: definition choice determines where proof work lives. The constructive content (encoding correctness in the return type) is a design decision, not a proof obligation.

Gold's theorem itself (`gold_theorem` in `Theorem/Gold.lean`) proves that no learner can identify in the limit a concept class containing all finite subsets plus an infinite set. The proof constructs a locking sequence: an enumeration strategy that forces the learner to commit to a finite concept, then extends the adversarial text to be consistent with the infinite target. The locking sequence is a paradigm-specific proof technique: it exploits the enumeration structure of text presentations, which exists only in the Gold paradigm. It cannot be applied to PAC (no enumeration) or Online (no convergence requirement).

### PAC-Bayes: the frequentist-Bayesian bridge

McAllester's PAC-Bayes bound connects three mathematical domains. PAC learning is itself the intersection of combinatorics and measure theory (Section I). PAC-Bayes adds information theory to this intersection:

| Domain | Object | Role in the bound |
|--------|--------|-------------------|
| Information theory | KL divergence KL(Q ‖ P) | Complexity penalty for the posterior |
| Measure theory | Gibbs posterior Q over hypotheses | The distribution whose expected error is bounded |
| Combinatorics | Finite hypothesis class H | The space over which prior and posterior are defined |

The proof chains through three steps: per-hypothesis Hoeffding with prior-weighted tail (`pac_bayes_per_hypothesis`), simultaneous bound via union bound (`pac_bayes_all_hypotheses`), and Jensen's inequality over the posterior (`pac_bayes_finite`). The pure mathematical infrastructure (KL divergence, finite PMFs, expected values) is extracted to `PureMath/KLDivergence.lean`.

In the hub structure established in Section I, PAC is the hub through which all paradigms connect. PAC-Bayes provides evidence: it connects the Bayesian paradigm to PAC not through shared vocabulary (both use `ConceptClass` and `HypothesisSpace`) but through a shared bound. The KL divergence penalty mediates between the Bayesian prior-posterior structure and the PAC generalization guarantee. Without this bound, Bayesian and PAC learning share types but not theorems. PAC-Bayes is the theorem that makes the connection substantive.
