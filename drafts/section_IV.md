# Section IV — FINAL DRAFT

---

## IV. Definition Sensitivity

A definition is not a stylistic choice. In this kernel, three definitions that appeared correct on paper produced, respectively, a false theorem, a vacuous theorem, and a proof whose difficulty was located in the wrong place. Each was detected during formalization. Each was repaired by modifying the definition.

### The taxonomy

| Failure mode | What goes wrong | Example | How to anticipate |
|-------------|----------------|---------|-------------------|
| **False theorem** | The definition admits a counterexample to the intended characterization | Littlestone tree shattering | Check: does the definition's quantifier structure admit more witnesses than the theorem requires? |
| **Vacuous theorem** | The definition makes the theorem trivially true | PACLearnable with existential Dm | Check: can the existentially quantified auxiliary be constructed from the target concept? |
| **Displaced proof** | The definition forces proof work into the wrong location | MindChangeOrdinal without correctness encoding | Check: does the return type encode the properties the theorem's conclusion requires? |

### False theorem: Littlestone tree shattering

The branch-wise definition allows independent witnesses at each branch:

```
isShattered C (.branch x l r) =
  (exists c in C, c x = true and isShattered C l) and
  (exists c in C, c x = false and isShattered C r)
```

Let C = {const_true, const_false}. const_true witnesses every left branch. const_false witnesses every right branch. LittlestoneDim = infinity. But C is online-learnable with 1 mistake: after one observation, the learner knows which constant it faces. The characterization theorem is false under this definition.

The corrected definition restricts C at each recursive call:

```
isShattered C (.branch x l r) =
  (exists c in C, c x = true) and (exists c in C, c x = false) and
  isShattered {c in C | c x = true} l and
  isShattered {c in C | c x = false} r
```

Under the corrected definition, C = {const_true, const_false} gives LittlestoneDim = 1. The characterization theorem holds. The two definitions are different logical formulas: the first quantifies independent witnesses per level, the second restricts to a consistent class along each path.

### Vacuous theorem: PACLearnable with existential Dm

The original definition:

```
exists Dm : Measure (Fin m -> X x Y), [probability conditions] and [PAC guarantee]
```

The existential allows Dm to depend on the target concept c. A memorizer constructs Dm as the point mass encoding c. Every finite concept class is trivially PAC-learnable. The theorem is vacuous.

The corrected definition uses Measure.pi:

```
Measure.pi (fun _ : Fin m => D) { xs | ... }
```

The sample measure is the product of m independent copies of D. The learner cannot see c through the sample distribution. PAC learnability becomes non-trivial.

### Displaced proof: MindChangeOrdinal

The original MindChangeCount returned a natural number: the count of mind changes. The forward direction of the characterization (finite count implies EX-learnable) required a separate proof that the learner converges correctly, not just that it stops changing. The proof was unexpectedly difficult because the definition did not carry the information the theorem needed.

The corrected MindChangeOrdinal branches on finiteness AND correctness:

```
MindChangeOrdinal X L c T :=
  if change_set.Finite then
    if exists t0, forall t >= t0, L.conjecture (T.prefix t) = c then
      change_set.toFinset.card    -- finite ordinal: converged correctly
    else
      omega                       -- omega: wrong concept or no convergence
  else
    omega                         -- omega: infinitely many changes
```

A finite return value guarantees correct convergence. The forward direction becomes definitional. The proof work moved from the theorem into the definition.

### Additional corrections

**NFL and domain cardinality.** The No-Free-Lunch theorem is provably false for finite domains: VCDim(Set.univ) = |X| when X is finite, so Set.univ is PAC-learnable by memorization. The correct statement requires `[Infinite X]`. This is a known correction in the learning theory community, formalized here.

**Quantifier ordering.** The orderings `forall eps, exists m0, forall D` (uniform convergence) and `forall eps, forall D, exists m0` (pointwise convergence) are not interchangeable. The first makes m0 independent of D. The second allows m0 to depend on D. PACLearnable requires distribution-free sample complexity, which forces the uniform ordering. The distinction is the Dini/Arzela gap from real analysis: uniform convergence implies pointwise, but not conversely.

### The finite-infinite tactic hypothesis

The corrections above cluster around a structural boundary: the distinction between finite and infinite domains changes the proof methods available.

For finite X, the PAC proof is direct: enumerate all hypotheses, apply Hoeffding, union bound. ~100 lines. For infinite X, the same mathematical statement requires symmetrization, ghost samples, exchangeability bounds, NullMeasurableSet. ~3,000 lines.

This suggests three hypotheses about proof search:

1. **Tactic space signature.** The finite branch uses `Finset.sum`, `Finset.card`, direct counting. The infinite branch uses `lintegral`, `NullMeasurableSet`, product measure isomorphisms. The two tactic spaces are disjoint. An agent that detects `[Infinite X]` or uncountable C in the goal can restrict its tactic library before searching.

2. **Predictable agent failure.** AI proof search agents attempting the infinite-domain case with finite-domain tactics (direct union bound) fail predictably: they produce 2^{2m} where the proof needs GrowthFunction(C, 2m). This failure mode was observed in three independent agent attempts during proof discovery.

3. **Non-inductive atoms.** Each infinite-domain proof technique (symmetrization, Rademacher restriction, Choquet capacity, NullMeasurableSet) is a new local construction that cannot be obtained by inductive extension of the finite case. The finite case does not contain the seed of symmetrization. These techniques are atoms: they must be introduced, not derived.

### The measurable inner event metaprogram

When the target event is defined by an existential quantifier over an uncountable set (`exists h in C, ...`) and the selection involves `Classical.choose` or a non-constructive principle, the target event may not be measurable. The proof design for this class of problems: find a measurable subset of the target event that carries the same probability bound, then conclude by monotonicity.

Two instances appear in the kernel: the symmetrization bad event (uncountable union over C, resolved via NullMeasurableSet) and the advice elimination success event (`Classical.choose` in bestAdvice, resolved via GoodPair subset of SuccessProd). Both involve events defined by non-constructive selection over uncountable indexing sets. The proof pattern is the same: replace the non-measurable selection with a measurable approximation, then use measure monotonicity.

The class of proofs requiring this pattern: any proof where the goal involves integrating over an event defined by `exists theta in Theta, P(theta, x)` where Theta is uncountable and the selector `theta*(x) = Classical.choose` is not measurable. Joint measurability of P in (theta, x) is the sufficient condition for the pattern to apply.
