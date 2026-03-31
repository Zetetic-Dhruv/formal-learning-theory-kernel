# Premise Design Blueprint

A guide for constructing typed premises for AI-driven proof search in formalization projects. Derived from the empirical record of the formal-learning-theory-kernel (42 concept nodes, 5 paradigm joints, 7 structural hypotheses, 67 proofs attempted, 65 closed).

## What a premise is

A typed premise for a mathematical field consists of:
- **Concept nodes**: the definitions, structures, and theorem statements of the field, organized into typed Lean4 declarations with `sorry` placeholders for proofs
- **Dependency layers**: a compilation order (L0-L7) ensuring types are available before they are used
- **Paradigm joints**: binary obstruction tags between paradigm pairs, predicting whether proof infrastructure transfers
- **Structural hypotheses**: predictions about type-theoretic fractures and design tradeoffs

The premise scopes the proof search. The AI searches within the premise, not alongside it. Without a premise, proof search produces vacuous theorems, sorry-in-Prop, and type homogeneity.

## Step 1: Identify the field's paradigms

List the major subfields or approaches that share vocabulary but may not share proof methods. In learning theory: PAC, Online, Gold. Each paradigm has its own data presentation, success criterion, and complexity measure.

For each pair of paradigms, assign an obstruction tag:
- **obstructed**: the paradigms share vocabulary but cross-paradigm theorems require explicit bridges
- **independent**: the paradigms share vocabulary but no theorem connects them

This determines which definitions can be shared (ConceptClass, HypothesisSpace) and which must be paradigm-specific (BatchLearner, OnlineLearner, GoldLearner).

## Step 2: Assign dependency layers

Organize concept nodes into layers such that each layer depends only on layers above it:

| Layer | Contents | Example |
|-------|----------|---------|
| L0 | Computation infrastructure (automata, Turing machines) | `Computation.lean` |
| L1 | Base types (domain, concept, concept class, loss) | `Basic.lean` |
| L2 | Data interfaces (samples, streams, oracles) | `Data.lean` |
| L3 | Learner types (batch, online, gold, bayesian) | `Learner/*.lean` |
| L4 | Success criteria (PAC, online, EX, universal) | `Criterion/*.lean` |
| L5 | Complexity measures + proof infrastructure | `Complexity/*.lean` |
| L6 | Theorems (characterizations, separations, NFL) | `Theorem/*.lean` |
| L7 | Processes and applications | `Process.lean` |

The layer structure ensures `lake build` succeeds with all proofs as `sorry`.

## Step 3: Write definitions with sorry placeholders

For each theorem, write the STATEMENT with the correct type signature. Leave the proof as `sorry`. The type signature is the premise. The proof is what the AI will search for.

## Step 4: Check definitions against the failure taxonomy

Before launching proof search, check each definition against three failure modes:

### Failure mode 1: False theorem (quantifier mismatch)

**Symptom**: The definition admits a counterexample to the intended characterization.

**Diagnostic**: Does the definition's quantifier structure admit more witnesses than the theorem requires?

**Example**: Branch-wise Littlestone tree shattering allows independent witnesses per level. The characterization theorem requires path-consistent witnesses. The definition's `exists c1 ... exists c2 ...` (independent) does not match the theorem's requirement of a single consistent concept along each path.

**Check procedure**:
1. Write down the theorem's intended proof sketch
2. Identify which objects the proof treats as "the same" across different parts of the argument
3. Verify the definition forces these objects to BE the same, not merely to exist independently

### Failure mode 2: Vacuous theorem (information leak)

**Symptom**: The theorem has a trivial proof that should not exist.

**Diagnostic**: Can an existentially quantified auxiliary be constructed from the target concept (or other information the theorem should deny access to)?

**Example**: PACLearnable with existential Dm allows Dm to depend on the target concept c. A memorizer constructs Dm = point mass encoding c.

**Check procedure**:
1. For each existential in the definition, ask: what information can the witness access?
2. If the witness can access the target concept, the labels, or any object the theorem's "for all" quantifier ranges over, the definition is too permissive
3. Replace the existential with a fixed construction (Measure.pi, a specific distribution) that blocks the information leak

### Failure mode 3: Displaced proof (return type underspecified)

**Symptom**: One direction of a characterization is unexpectedly difficult.

**Diagnostic**: Does the definition's return type encode all properties the theorem's conclusion requires?

**Example**: MindChangeCount returns Nat (count of changes). The theorem's conclusion requires correct convergence. The return type does not encode correctness, so the proof must establish it separately.

**Check procedure**:
1. Write down the theorem's conclusion
2. List every property the conclusion asserts
3. For each property, check: is it encoded in the definition's return type, or must it be proved separately?
4. If it must be proved separately, consider encoding it in the definition

## Step 5: Check domain boundary

If the field involves both finite and infinite objects:

1. **Identify which definitions require `[Infinite X]` or `[Countable X]`**: these constraints determine the tactic space
2. **Check whether theorems stated for "all X" are actually false for finite X**: the NFL correction (VCDim(Set.univ) = |X| for finite X) is an instance of this
3. **Anticipate the tactic split**: finite-domain proofs use `Finset` operations and direct counting; infinite-domain proofs require measure theory, symmetrization, and NullMeasurableSet infrastructure

## Step 6: Check measurability requirements

If the field involves measure theory:

1. **Identify which definitions require measurability hypotheses**: every definition involving integration, probability, or expectation needs measurability
2. **Choose the measurability level**: `MeasurableSet` (Borel) is stronger than `NullMeasurableSet`. For uncountable hypothesis classes, `NullMeasurableSet` may be necessary and sufficient.
3. **Check whether measurability is trivial or non-trivial**: on countable domains, everything is measurable under the discrete sigma-algebra. On uncountable domains, measurability requires explicit infrastructure.
4. **Introduce measurability typeclasses early** (at L1-L3, not L5): measurability cross-cuts the dependency hierarchy

## Step 7: Estimate the infrastructure ratio

The fraction of the kernel that will be proof infrastructure (L5) vs theorems (L6) vs definitions (L1-L4) is predicted by the number of domain crossings:

- **Single-domain paradigm** (e.g., Online: combinatorics + game theory): infrastructure < 30%
- **Two-domain crossing** (e.g., PAC: combinatorics x measure theory): infrastructure 40-60%
- **Three-domain crossing** (e.g., PAC-Bayes: information theory x combinatorics x measure theory): infrastructure > 60%

Budget proof search time proportionally.

## Failure mode diagnostic table

| Symptom | Likely cause | Diagnostic question | Fix |
|---------|-------------|--------------------|----|
| Counterexample found to a characterization theorem | Quantifier mismatch (failure mode 1) | Does the definition allow independent witnesses where the theorem needs consistent ones? | Restrict quantifier scope |
| Trivial proof exists for a non-trivial theorem | Information leak (failure mode 2) | Can the existential witness access the target concept? | Replace existential with fixed construction |
| One proof direction is 10x harder than expected | Return type underspecified (failure mode 3) | Does the return type encode all properties the conclusion requires? | Encode properties in the definition |
| Proof blocked at measurability step | Missing measurability infrastructure | Is the concept class uncountable? Is the bad event defined by an uncountable existential? | Add NullMeasurableSet + typeclass hierarchy |
| Agent produces 2^{2m} where GrowthFunction is needed | Finite tactics applied to infinite domain | Does the goal contain `[Infinite X]` or uncountable C? | Route to symmetrization + Rademacher tactics |
| Theorem is false for finite domains | Domain cardinality not constrained | Does the theorem require `[Infinite X]`? | Add cardinality constraint |
| Quantifier ordering makes theorem unprovable | Uniform vs pointwise convergence | Does the sample complexity function need to be distribution-free? | Use `forall eps, exists m0, forall D` (uniform) |
