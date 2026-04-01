# Section IX — FINAL DRAFT

---

## IX. Pure Mathematics Contributions

Formalization projects consume mathematics. They import Mathlib, instantiate definitions, close goals. This kernel also produced mathematics. Five modules totaling 908 lines, all absent from Mathlib, all independent of learning theory, all forced into existence by type errors during proof construction.

| Module | Lines | What the type system demanded | What it enables |
|--------|-------|------------------------------|-----------------|
| `ChoquetCapacity.lean` | 416 | Abstract capacity axioms; capacitability theorem for analytic sets in Polish spaces | Analytic measurability bridge |
| `AnalyticMeasurability.lean` | 110 | Analytic sets are NullMeasurableSet for finite Borel measures | Borel-analytic separation (Section III) |
| `Concentration.lean` | 195 | `BoundedRandomVariable` typeclass; Chebyshev majority bound for independent events | PAC boost: probability 2/3 to probability 1-delta |
| `Exchangeability.lean` | 128 | Double-sample measure, merge/split isomorphism, `ValidSplit`, `SplitMeasure` | Symmetrization argument (PAC characterization) |
| `KLDivergence.lean` | 59 | `FinitePMF`, KL divergence, cross-entropy over finite types | PAC-Bayes bound |

None of these modules import from `FLT_Proofs`. Each compiles against Mathlib alone. Each is a candidate for upstream contribution.

### The dependency chain that produced new mathematics

The two largest modules form a pipeline:

```
ChoquetCapacity.lean (416 lines)
  └── AnalyticMeasurability.lean (110 lines)
        └── BorelAnalyticBridge.lean (kernel)
              └── BorelAnalyticSeparation (Section III: new mathematics)
```

`ChoquetCapacity.lean` exists because `AnalyticMeasurability.lean` needs it. `AnalyticMeasurability.lean` exists because the symmetrization bad event for uncountable concept classes is not Borel-measurable, and the kernel requires a path from `AnalyticSet` to `NullMeasurableSet`. Mathlib has Polish spaces, Borel spaces, and analytic sets. It does not have the theorem connecting them: that analytic sets are universally measurable.

The path runs through Choquet's capacitability theorem (1954). A finite Borel measure on a Polish space satisfies the capacity axioms. An analytic set is capacitable: its measure equals the supremum of measures of compact subsets. A capacitable set with compact inner approximation is NullMeasurableSet. This is Kechris, Theorem 30.13 -- standard descriptive set theory, but absent from Mathlib and absent from every learning theory textbook that silently assumes the bad event is measurable.

The 526 lines of this pipeline were not planned. They were forced by a type error: `lintegral_indicator_one₀` requires `NullMeasurableSet`, and no existing Lean4 proof connects `AnalyticSet` to `NullMeasurableSet`. The resolution required building the Choquet capacity infrastructure from the axioms. That infrastructure, once built, made the Borel-analytic separation in Section III provable.

### What each paradigm demanded

The remaining three modules serve the three learning paradigms independently:

**Concentration** (195 lines). The PAC characterization requires boosting: if k independent weak learners each succeed with probability at least 2/3, then majority vote succeeds with probability at least 1-delta when k >= 9/delta. The proof uses indicator random variables, Popoviciu's variance bound, independence for variance of sums, and Chebyshev's inequality. `BoundedRandomVariable` is formalized as a typeclass -- a random variable bounded in [a,b] almost everywhere with a measurability certificate. The typeclass pattern eliminates explicit bound-threading in downstream proofs.

**Exchangeability** (128 lines). The symmetrization argument requires reasoning about double samples: `D^m x D^m` (training and ghost), their merge into `Fin (2*m) -> X`, and the uniform distribution over all `C(2m,m)` valid splits of 2m points into two groups of m. The `ValidSplit` structure, `SplitMeasure`, and the merge/split isomorphism formalize the combinatorial substrate that every symmetrization proof uses but no Mathlib file provides. The key type: `ValidSplit m` is a decidable subtype of `Fin (2*m) -> Bool` with a cardinality constraint, equipped with a discrete measurable space.

**KL divergence** (59 lines). The PAC-Bayes bound requires KL divergence between finite probability mass functions. `FinitePMF` bundles a probability assignment `H -> R` with non-negativity and summation-to-one proofs. `klDivFinitePMF`, `crossEntropyFinitePMF`, and `expectFinitePMF` are the three operations. `HasPositivePrior` is a typeclass asserting strictly positive weights. This is the smallest module and the most straightforward: vocabulary that Mathlib lacks because Mathlib's `PMF` works over `ENNReal`, not `R`, and the PAC-Bayes bound needs real-valued arithmetic.

### Why formalization produces pure mathematics

The pattern across all five modules is the same. A learning theory proof requires a mathematical fact. The fact is "obvious" on paper: textbooks either state it without proof or silently assume it. Mathlib does not contain it. The type system rejects the proof until the fact is formalized. The formalization turns out to be non-trivial.

The Choquet capacitability theorem is the strongest case. No learning theory paper cites it. No textbook mentions it in the context of PAC learning. The connection between analytic sets and the symmetrization bad event is invisible until the type system forces the question: given a set defined by an existential projection over an uncountable family, what is its measurability status? The answer requires 416 lines of capacity theory.

This is the mechanism by which premise-driven formalization generates mathematics the premise did not predict. The type system acts as a completeness checker: it rejects proofs that skip steps. When the skipped step is a genuine mathematical theorem, the formalization must produce it. The resulting infrastructure is not a formalization artifact. It is mathematics, independent of the application that forced it, reusable in any context that needs Choquet capacities or analytic measurability.
