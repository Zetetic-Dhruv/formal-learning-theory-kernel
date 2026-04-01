# Section IX — FINAL DRAFT

---

## IX. Pure Mathematics Contributions

The kernel required results that Mathlib does not contain. These are formalized in `PureMath/` and are independent of learning theory.

| Result | File | Lines | What it proves | Reference |
|--------|------|-------|---------------|-----------|
| Choquet capacitability | ChoquetCapacity.lean | 416 | Finite Borel measures on Polish spaces are Choquet capacities. Analytic sets are capacitable: compact capacity equals measure. | Kechris, *Classical Descriptive Set Theory*, Theorem 30.13 |
| Analytic measurability | AnalyticMeasurability.lean | 110 | Analytic sets are universally measurable (NullMeasurableSet under any probability measure). | Lusin (1925); Kechris Ch. 29 |
| Concentration inequalities | Concentration.lean | 195 | `BoundedRandomVariable` typeclass. Chebyshev majority bound for independent events. | Boucheron-Lugosi-Massart Ch. 2 |
| Exchangeability | Exchangeability.lean | 128 | Double-sample construction, merge/split isomorphism, valid splits, split measure. | Shalev-Shwartz & Ben-David Ch. 4/6 |
| KL divergence | KLDivergence.lean | 59 | `FinitePMF` structure, KL divergence, cross-entropy, expected value over finite types. | Cover & Thomas Ch. 2 |

908 lines total. Each module compiles independently of the learning theory theorems it serves. The Choquet capacitability theorem is the most substantial and the strongest candidate for upstream contribution to Mathlib.
