# Original Lean4 FLT Tactics

Proof discoveries, engineering wins, and non-obvious insights from building the formal learning theory kernel. Extracted from inline comments before library-release cleanup.

## 1. Hard Proof Discoveries

### XOR trick in Assouad's coding argument
`Complexity/Compression.lean`

The coding argument for "VCDim finite implies compression" requires showing that a set shattered in the dual (hypothesis space) implies shattering in the primal (input space). The key move: define `b(j) = decide(g(x_j) = c(x_j))`, which absorbs the agree/disagree flip via XOR. This converts agreement-test shattering into standard shattering on the original concept class. The same XOR bijection recurs in the restriction pattern counting step of symmetrization (`Complexity/Symmetrization.lean`).

### Pigeonhole on compression schemes requires realizability guard
`Complexity/Generalization.lean`

The pigeonhole argument for "compression implies finite VC dimension" is: a compression scheme of size d maps 2^n labelings of n points to at most C(n,d) * 2^d compressed pairs. If n is large enough, injectivity fails. But this only works when the compression scheme's correctness is GUARDED by C-realizability. The original definition quantified over ALL samples (including inconsistent ones), making CompressionScheme uninhabited for nonempty X. Guarding by realizability (only requiring correctness on C-consistent samples) fixed the definition and made the pigeonhole argument non-vacuous.

### NFL double-counting via Boolean complement pairing
`Complexity/Generalization.lean`

For every labeling f and its Boolean complement flip(f), at most one can have low error on unseen points. Reason: on each unseen point t, exactly one of f(t) and flip(f)(t) agrees with any fixed output. So disagreement counts are complementary: disagree(f) + disagree(flip(f)) >= |unseen|. When |unseen| > d/2, at least one has high error. This pairing argument is the core of the no-free-lunch proof.

### Exponential beats polynomial at exact witness
`Bridge.lean`, `Complexity/Generalization.lean`

The inequality (k+1)*(2n)^k < 2^n, needed for the pigeonhole step, is witnessed at n = 2(k+1)^2. This concrete witness avoids asymptotic reasoning entirely and closes the arithmetic in Lean4 via `Nat.lt_two_pow_of_lt_pow_sq`.

### Sample-dependent vs sample-independent covers
`Complexity/Generalization.lean`

A sample-independent covering lemma (representatives fixed before seeing the sample) is unprovable for infinite concept classes. The standard PAC proof requires sample-dependent covers where representatives are chosen after observing the sample. This distinction is invisible in informal presentations but blocks formalization completely.

## 2. Lean4 Engineering Wins

### `dsimp only [localLet]` works on goals but NOT hypotheses
`Complexity/Compression.lean`

When `localLet` definitions (local abbreviations via `let`) are used, `dsimp` must be applied to the goal BEFORE introducing hypotheses. Reversing this order causes definitional unfolding to fail silently. Pattern: `dsimp only [localLet]; intro h` not `intro h; dsimp only [localLet]`.

### `Nat.find` for measurable selection (bypassing KRN)
`Learner/VersionSpace.lean`

Kuratowski-Ryll-Nardzewski measurable selection is not in Mathlib. For countable concept classes with a measurable enumeration `enum : N -> Concept X Bool`, `Nat.find` provides a constructive measurable selector. The evaluation preimage decomposes as a countable union of measurable rectangles: `Union_n ({S | IsFirstConsistent enum S n} x {x | enum n x = true})`. Measurability follows from `measurable_to_countable'` (Mathlib).

### `convert` + `Fin.heq_fun_iff` for Nat.pair bridges
`Theorem/Extended.lean`

When `Nat.pair`/`Nat.unpair` creates heterogeneous equality goals between `Fin m1 -> X` and `Fin (Nat.unpair (Nat.pair m1 m2)).1 -> X`, the combination `convert ... using 10` + `Fin.heq_fun_iff` resolves the HEq goals cleanly. The high `using` parameter is needed because the type mismatch is deep in the term structure.

### `if_congr` handles Decidable instance mismatch
`Complexity/Compression.lean`

When two `if` expressions have the same Boolean condition but different `Decidable` instances (from different unfolding paths), `if_congr` rewrites through the mismatch where `simp` and `rw` fail. Pattern: `Finset.sum_congr rfl (fun t _ => if_congr (...) rfl rfl)` for rewriting inside conditional sums.

### `MeasurableSingletonClass` required for uniform measures
`Theorem/PAC.lean`

Lean4's `Measure.count` requires `MeasurableSingletonClass` for singletons to be measurable. This enriches theorem hypotheses (more structure on X) but does not simplify them. Required for any discrete probability argument using uniform or counting measures.

### `Classical.decEq X` for Finset operations
`Complexity/Generalization.lean`

Many Finset operations (`Finset.exists_subset_card_eq`, `Finset.filter`, etc.) require `DecidableEq`, which must be explicitly synthesized via `haveI : DecidableEq X := Classical.decEq X` in noncomputable contexts.

### PMF.toMeasure = toOuterMeasure under top sigma-algebra
`Complexity/FiniteSupportUC.lean`

Under the discrete sigma-algebra (MeasurableSpace = top), `PMF.toMeasure` equals `PMF.toOuterMeasure`, which simplifies measure computations on finite types. Key for bridging combinatorial and measure-theoretic formulations.

### `Real.pow_div_factorial_le_exp` from Mathlib
`Complexity/Generalization.lean`

The Mathlib API `Real.pow_div_factorial_le_exp` provides the Taylor series lower bound `t^(d+1) / (d+1)! <= exp(t)` for t >= 0. Enables the key arithmetic lemma `t^d * exp(-t) <= (d+1)!/t` needed for sample complexity bounds.

## 3. Mathematical Insights (Non-Obvious)

### NullMeasurableSet is the correct level for the FTSL
`Complexity/Measurability.lean`, `Complexity/BorelAnalyticBridge.lean`

For uncountable concept classes, the uniform convergence bad event `{exists h in C, |TrueErr - EmpErr| >= eps}` is NOT MeasurableSet in general (the existential quantifier over an uncountable set does not preserve Borel measurability). NullMeasurableSet suffices for integration via `lintegral_indicator_one_0`. This is absent from standard textbooks (SSBD, etc.) which silently assume measurability.

### TrueError is a measure (ENNReal), not an integral (Real)
`Complexity/Generalization.lean`

PACLearnable uses `D {x | h x != c x}` (ENNReal measure of disagreement set), not `integral loss dD` (Real-valued expected loss). The bridge between them requires four conditions: D is probability, loss is 0-1, disagreement set is measurable, and integral equals measure of disagreement set. This type mismatch is invisible on paper.

### Quantifier structure: UC vs PAC
`Complexity/Generalization.lean`

The universal quantifier over hypotheses appearing INSIDE the probability event (not outside) makes uniform convergence strictly stronger than PAC learnability. UC: `forall D, P_S(sup_{h in H} |gap(h)| >= eps) <= f(m)`. PAC: `forall D, forall c, P_S(err(L(S)) >= eps) <= delta`. The sup inside the measure is the difference.

### Asymmetry in the VC characterization
`Theorem/PAC.lean`

The two directions of "PAC iff finite VCDim" cross between combinatorics and measure theory in opposite directions. Forward (PAC -> finite VCDim): constructive, produces a hard distribution via double-counting. Backward (finite VCDim -> PAC): non-constructive, routes through symmetrization + concentration. The 15:1 LOC ratio reflects genuine mathematical asymmetry.

### Borel-analytic separation settles the exact measurability level
`Complexity/BorelAnalyticBridge.lean`, `Theorem/BorelAnalyticSeparation.lean`

The UC bad event for Borel-parameterized concept classes is analytic (Suslin projection of Borel witness graph). Analytic implies NullMeasurableSet (Choquet capacitability, Kechris 30.13). But analytic does NOT imply Borel. The singleton class over an analytic non-Borel set witnesses the strict separation: WellBehavedVCMeasTarget holds, KrappWirthWellBehaved fails.

## 4. Dead Branches (Proof Routes Tried and Abandoned)

### Direct PAC via consistent covering (Gamma_92 path)
`Complexity/Generalization.lean`

A direct route from finite VCDim to PAC (bypassing uniform convergence) was attempted via a consistent covering lemma + union bound. Abandoned because the covering lemma required sample-independent covers, which are unprovable for infinite concept classes. The surviving architecture routes through UC as an intermediary.

### Tonelli interchange blocked by uncountable C
`Complexity/Symmetrization.lean`

The original plan to close the symmetrization chain via direct Tonelli interchange failed because uncountable concept classes break the MeasurableSet requirement for Tonelli's theorem. Resolution: finite exchangeability bound + NullMeasurableSet weakening, which avoids the Tonelli interchange entirely.

### Hoeffding obstruction was false alarm
`Complexity/Generalization.lean`

The feared obstruction "Hoeffding's inequality not in Mathlib" was false. Mathlib has `Real.one_sub_le_exp_neg` and `Real.one_sub_div_pow_le_exp_neg`. The real obstruction was missing type-level definitions (TrueError as measure vs integral, EmpiricalMeasureError bridge).

## 5. Definition Repairs (Formalization-Forced Corrections)

| Definition | Bug | Fix |
|-----------|-----|-----|
| CompressionScheme | Correctness quantified over ALL samples (uninhabited for nonempty X) | Guard by C-realizability |
| UniformConvergence | m0 depended on D and c (made uc_imp_pac unprovable) | Quantifier order: exists m0, forall D, forall c |
| LittlestoneDim (branchwise) | Independent witnesses per level; const_true gives LDim = infinity for 1-mistake class | Path-wise restriction: restrict C at each recursive call |
| PACLearnable (existential Dm) | Dm depends on target c via memorizer + point mass | Use Measure.pi (product of independent copies) |
| MindChangeCount | Returns count only; forward direction requires separate convergence proof | MindChangeOrdinal branches on finiteness AND correctness |
| DSDim vs NatarajanDim | Inequality stated in wrong direction | Corrected direction |
| SQDimension | Missing distribution parameter D | Added D parameter |
| ERM | Missing nonemptiness witness for H | Added (hne : H.Nonempty) |

## 6. Recurring Proof Patterns

| Pattern | Where | Description |
|---------|-------|-------------|
| XOR bijection | Compression, Symmetrization | Convert disagreement patterns to agreement patterns via pointwise XOR |
| Pigeonhole on bounded image | Compression, Generalization | Injectivity + bounded target set gives cardinality contradiction |
| `convert ... using N` + `heq_fun_iff` | Extended | Bridge heterogeneous equality across Fin type changes |
| `dsimp only` on goal first | Compression | Unfold let-definitions in goal before introducing hypotheses |
| `if_congr` inside `sum_congr` | Compression | Rewrite conditional sums through Decidable instance mismatches |
| Growth function bound (4 phases) | Symmetrization | XOR bijection, witness Finset, ncard comparison, GF bound |
| `by_contra; push_neg` for existence | Generalization | Standard double-counting setup for NFL-type arguments |
| `measurable_to_countable'` for Bool | VersionSpace, BorelAnalyticBridge | Bool-valued functions: measurability reduces to singleton preimages |
