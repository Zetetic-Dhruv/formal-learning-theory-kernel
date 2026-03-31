# Section III — FINAL DRAFT

---

## III. Separations

A separation theorem proves that an implication is strict by constructing a witness: a specific mathematical object that satisfies one condition and provably fails the other. The witness is the mathematics. The theorem statement is the label on the witness.

### PAC does not imply Online

<!-- FIGURE: threshold_separation.svg
     Style: black/white, Times New Roman, old school academic
     Left panel: Number line (N). Step function showing threshold (· ≤ n).
     Mark a singleton {k} as shattered: threshold at k vs k-1 separates it.
     Mark a pair {a,b} with a < b: labeling (false, true) impossible with monotone function.
     Right panel: Binary search tree. Root queries midpoint m.
     Left child: learner predicted true, adversary reveals false, threshold moves left.
     Right child: learner predicted false, adversary reveals true, threshold moves right.
     Tree grows to arbitrary depth. Each edge labeled with one mistake.
     Caption: "VCDim = 1, LittlestoneDim = infinity. Monotonicity helps sampling, not adversaries."
-->

Consider the threshold class on the natural numbers: `C = {(· ≤ n) | n : Nat}`. Every threshold function is monotone. VC dimension is 1: any singleton {k} is shattered (the threshold at k vs the threshold at k-1 separates it), but no pair {a, b} with a < b is shattered (the labeling "a false, b true" requires a non-monotone function).

Littlestone dimension is infinite. An adversary plays the following game: query the midpoint of the current interval. Whatever the learner predicts, the adversary reveals the opposite. The threshold moves to whichever half the learner got wrong. This binary search forces one mistake per round at every depth. The adversary strategy constructs a shattered tree of arbitrary depth by induction.

VCDim = 1, LittlestoneDim = ∞. The class is PAC-learnable but not online-learnable. The separation exploits the gap between statistical sampling (where monotonicity helps) and adversarial sequencing (where monotonicity is irrelevant because the adversary adapts).

### Gold does not imply PAC

<!-- FIGURE: gold_separation.svg
     Style: black/white, Times New Roman, old school academic
     Left panel: Timeline showing Gold learner's conjectures.
     t=1: sees 2, conjectures {2}
     t=2: sees 5, conjectures {2,5}
     t=3: sees 7, conjectures {2,5,7} = target. Stabilizes.
     Arrow labeled "converges" at the stabilization point.
     Right panel: Shattering diagram.
     Set S = {a, b} on number line.
     Four labelings shown as four indicator functions:
     {a,b}, {a}, {b}, {} — all realized by Finset indicators.
     Label: "Every finite set shattered. VCDim = infinity."
     Caption: "EX-learnable (convergence on enumeration) but not PAC-learnable (VCDim = infinity)."
-->

Consider finite-subset indicators on the natural numbers: `C = {fun x => decide (x ∈ S) | S : Finset Nat}`. The Gold learner outputs "true on everything seen so far." After finitely many observations, every element of the target finite set has appeared, and the learner's conjecture stabilizes. The class is EX-learnable.

Every finite subset of N is shattered: given any S = {a₁, ..., aₖ}, each labeling f : S → Bool is realized by the indicator of {aᵢ | f(aᵢ) = true}. VCDim = ∞. The class is not PAC-learnable.

The separation exploits the gap between convergence on a fixed enumeration (which requires only eventual correctness) and generalization from a random sample (which requires uniform error control over the entire domain). Gold-style learning does not need to generalize. PAC learning does.

### Online implies PAC

The reverse implication holds unconditionally: any online learner with mistake bound M gives a PAC learner with sample complexity polynomial in M, 1/ε, and 1/δ. The proof routes through the generalization bound from finite Littlestone dimension. This is the only non-strict paradigm separation in the kernel.

### The Borel-analytic separation

<!-- FIGURE: borel_analytic_separation.svg
     Style: black/white, Times New Roman, old school academic
     Three panels stacked vertically:

     Top panel: "The witness class"
     Real line R with a shaded region A labeled "A ⊆ R (analytic, non-Borel)".
     Below the line: zeroConcept shown as flat line at y=false.
     Above the line: three spikes at points a₁, a₂, a₃ ∈ A, each labeled singletonConcept(aᵢ).
     Caption: "singletonClassOn(A): every hypothesis is Borel-measurable."

     Middle panel: "The proof chain"
     Flow diagram, left to right:
     Box "Bad event defined by ∃ a ∈ A"
       → arrow labeled "Suslin projection" →
     Box "Analytic (Σ₁¹)"
       → arrow labeled "Choquet capacity" →
     Box "NullMeasurable"
     Below, a separate path:
     Box "Assume Borel"
       → arrow labeled "preimage under x ↦ (a₀, x)" →
     Box "A is Borel"
       → arrow labeled "contradiction" →
     Box "NOT Borel" (crossed out)

     Bottom panel: "The separation"
     Two boxes side by side:
     Left box (solid border): "WellBehavedVC: HOLDS" with "NullMeasurable ✓" below
     Right box (dashed border): "KrappWirth: FAILS" with "not Borel ✗" below
     Gap between them labeled "strict"

     Caption: "The gap between NullMeasurableSet and MeasurableSet is inhabited."
-->

The kernel's measurability condition for uniform convergence (`WellBehavedVC`, requiring `NullMeasurableSet`) is strictly weaker than the condition proposed by Krapp and Wirth (2024), which requires `MeasurableSet` (Borel). The separation is proved by constructing a concept class whose bad event is NullMeasurable but not Borel.

The witness: let A be an analytic non-Borel subset of the reals. Define the singleton class `singletonClassOn(A) = {zeroConcept} ∪ {singletonConcept(a) | a ∈ A}`, where `singletonConcept(a)` returns true only at x = a.

Every hypothesis in this class is Borel-measurable: the zero concept is constant, and each singleton concept is piecewise constant on a measurable singleton. The uniform convergence bad event (the set of ghost sample pairs where some hypothesis in the class has empirical gap ≥ ε/2) reduces to a planar witness event via a preimage calculation.

The planar witness is analytic. It is defined by an existential projection: "there exists a ∈ A such that the training point misses a and the ghost point hits a." The projection of a Borel set through an existential quantifier is analytic by Suslin's theorem (1917). Analytic sets are universally measurable by Choquet's capacitability theorem (1954), which this kernel formalizes from Kechris 30.13.

The planar witness is not Borel. If it were, then the preimage under the constant section x ↦ (a₀, x) would be Borel. But this preimage is A itself, which is not Borel by hypothesis. Contradiction.

Therefore: `WellBehavedVCMeasTarget` holds (the bad event is NullMeasurable via the analytic-to-universally-measurable chain) but `KrappWirthWellBehaved` fails (the bad event is not Borel). The gap between NullMeasurableSet and MeasurableSet is inhabited by a concrete concept class.

The separation is conditional on the existence of an analytic non-Borel subset of the reals, which is provable under standard set-theoretic assumptions. The theorem `exists_measTarget_separation` takes this as a hypothesis.

This separation connects three fields that had not been connected in this way: descriptive set theory (Suslin projections, Choquet capacity), measure theory (NullMeasurableSet vs MeasurableSet), and statistical learning (uniform convergence bad events for concept classes). The proof method is transportable beyond learning theory to any setting where supremum events over Borel-parameterized families arise.
