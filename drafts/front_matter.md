# Front Matter — FINAL DRAFT

---

# Formal(ized) Learning Theory

[![CI](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/actions/workflows/ci.yml/badge.svg)](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/actions/workflows/ci.yml)

| Lean | Mathlib | LOC | Theorems | Sorry (core) | Sorry (extended) |
|------|---------|-----|----------|-------------|-----------------|
| `v4.29.0-rc6` | [`fde0cc5`](https://github.com/leanprover-community/mathlib4/commit/fde0cc508f5375f278f515cb2f50a34a545a4c5c) | 17,956 | 278 | **0** (core) | **2** (extended) |

<p align="center">
  <img src="premise/hero.svg" alt="The Fundamental Theorem of Statistical Learning" width="820" />
</p>

A 42-node typed premise scoped human-guided, AI-driven proof search across three learning paradigms. The search formalized 278 machine-checked theorems in 17,956 lines of Lean 4. The infrastructure it required produced three results that had never been proved.

The type structure of a field's definitions determines the proof methods available to formalize it. A typed premise, derived before proof search, constrains the search space enough for AI-driven proof discovery to succeed where unconstrained search fails, and the infrastructure forced by the types can generate mathematics the premise did not predict.

| | Contributions |
|---|---|
| **New proof methodology** | 1. Piecewise composition of Borel-parameterized families produces analytic suprema; transportable to optimization, game theory, and control theory beyond learning. 2. Bridge between descriptive set theory and statistical learning: Suslin projections and Choquet capacitability applied to uniform convergence bad events. 3. Rectangle decomposition for `Nat.find`-based measurable selection, bypassing Kuratowski-Ryll-Nardzewski for countable families. |
| **New learning theory** | 1. Borel-analytic separation: `NullMeasurableSet` is strictly weaker than `MeasurableSet` for uniform convergence bad events (corrects Krapp-Wirth 2024). 2. Interpolation descent: composition of Borel concept classes weakens measurability to NullMeasurable. 3. `MeasurableBatchLearner`: new precondition isolating joint learner measurability; gates RL policy validity for non-neural architectures. 4. Version space measurability: first proof that non-neural learners satisfy `MeasurableBatchLearner`. 5. NullMeasurableSet correction: weakens the hypothesis for the entire fundamental theorem. |
| **First formalizations** | 1. Fundamental theorem of statistical learning (5-way equivalence, 4/5 conjuncts). 2. Choquet capacitability theorem (Kechris 30.13; Mathlib-contributable). 3. PAC-Bayes bound (McAllester; first frequentist-Bayesian bridge in Lean 4). 4. Littlestone characterization with corrected path-wise tree definition. 5. Gold's theorem and mind change characterization. 6. Baxter multi-task base case. 7. All paradigm separations with constructive witnesses. 8. Confidence boosting via 7/12-fraction Chebyshev concentration. 9. Measurability typeclass hierarchy with strict separation. |
| **Proof engineering** | 1. Definition sensitivity taxonomy: wrong definition produces false theorems (Littlestone), vacuous theorems (PACLearnable), or wrong proof architecture (MindChangeOrdinal). 2. Measurable inner event metaprogram for non-measurable target events defined by uncountable selection. 3. `BorelRouterCode` abstraction for conditional interpolation (attention, routing, transfer). 4. Countable enumeration bypass of Kuratowski-Ryll-Nardzewski measurable selection. 5. Premise ablation: 67 to 187 sorrys without structured inquiry framework, 65/67 closed with it. 87.5% vs 0% first-attempt success on articulated unknowns. |

### Core and extended modules

The kernel separates into a **fully checked core** (0 sorry) and an **extended frontier** (2 sorry):

- **Core**: Every theorem whose proof tree contains no sorry. This includes `vc_characterization`, `littlestone_characterization`, `gold_theorem`, all paradigm separations, all NFL theorems, the full symmetrization chain (3,027 LOC), the Rademacher bounds, the PAC-Bayes bound, the Borel-analytic separation, and the interpolation descent theorem.
- **Extended frontier**: Theorems whose proof trees pass through one of two sorry tactics. The individually proved conjuncts and branches are in the core; only the bundles that include all conjuncts/branches are tainted.

| Sorry | File | Blocks | Citation |
|-------|------|--------|----------|
| `vcdim_finite_imp_compression` | Generalization.lean:1903 | `fundamental_theorem` conjunct 2 (forward) | Moran-Yehudayoff 2016 |
| `bhmz_middle_branch` | Extended.lean:40 | `universal_trichotomy` branch 2 | BHMZ STOC 2021 |
