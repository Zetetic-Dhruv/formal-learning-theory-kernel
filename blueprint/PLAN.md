# Blueprint v1: Task URS State

This file is the running URS (Universal Reasoning State) for the blueprint, derived
from the task-URS-manuscript Cuzzolin-mass-function procedure. It drives content
discovery for `blueprint/src/content.tex` in subsequent implementation sessions. The
reader of this file is the author and any collaborator implementing the blueprint;
the reader of the blueprint itself never sees this machinery.

## Scope of v1

Core story: the five-way equivalence for PAC, the Littlestone characterization for
Online, the Gold and mind-change characterization for Gold-style learning, the
three-paradigm separation, and the measurability refinement (NullMeasurableSet
weakening plus the Borel-analytic separation theorem that corrects Krapp-Wirth 2024).

Deferred to v2: compression via approximate minimax, the MBL monad and version-space
measurability, PAC-Bayes, the Baxter multi-task base case, extended criteria (robust
PAC, RKHS statistical layer).

Deferred to v3 or dropped: Assouad dual VC bound (technically novel but sits better
as a standalone paper appendix than inside the blueprint's narrative).

## Methodology

For each concept X the blueprint workflow computes

    M(X) = (g_Pl, g_Coh, Inv_score, Comp_score, Tone_trajectory)

plus auxiliary quantities (σ_Pl, Coh_fail, Coh_surprise, Open_count), per
task-URS-manuscript Step 1. Profile classification follows the R1 to R8 decision
rules from Step 2. Structural prescriptions come from Step 3. The "asymmetric
content weight" principle is the core anti-template mechanism: small ignorance gap
produces short treatment, large ignorance gap earns space.

## Concept inventory and measurements

Compact table; detailed entries for asymmetric concepts follow below.

| #  | Concept                                        | Profile | σ_Pl | Coh_surprise | Coh_fail | Inv  | Comp | Length     |
|----|------------------------------------------------|---------|------|--------------|----------|------|------|------------|
| 1  | Concept class                                  | A       | 1.0  | 0.00         | 0.00     | 1.00 | 1.00 | 3 lines    |
| 2  | Batch learner (realizable / agnostic)          | A       | 0.9  | 0.10         | 0.00     | 0.90 | 1.00 | 6 lines    |
| 3  | i.i.d. sample                                  | A       | 1.0  | 0.00         | 0.00     | 1.00 | 1.00 | 3 lines    |
| 4  | Zero-one loss                                  | A       | 1.0  | 0.00         | 0.00     | 1.00 | 1.00 | 2 lines    |
| 5  | Empirical vs. true error                       | A       | 1.0  | 0.00         | 0.00     | 1.00 | 1.00 | 4 lines    |
| 6  | VC dimension and shattering                    | A       | 1.0  | 0.10         | 0.00     | 0.95 | 1.00 | 10 lines   |
| 7  | Growth function / Sauer-Shelah lemma           | B       | 1.0  | 0.35         | 0.00     | 0.95 | 1.00 | 0.5 page   |
| 8  | Uniform convergence and symmetrization         | B       | 0.8  | 0.20         | 0.00     | 0.90 | 1.00 | 1.0 page   |
| 9  | **Five-way equivalence (crown jewel)**         | B + C   | 0.7  | 0.50         | 0.00     | 0.75 | 1.00 | 2.0 pages  |
| 10 | **NullMeasurableSet refinement**               | C       | 1.0  | 0.50         | 0.30     | 0.90 | 1.00 | 1.0 page   |
| 11 | Littlestone dimension and mistake tree         | A + B   | 1.0  | 0.15         | 0.00     | 0.95 | 1.00 | 1.0 page   |
| 12 | Standard Optimal Algorithm (SOA)               | B       | 1.0  | 0.20         | 0.00     | 0.90 | 1.00 | 0.5 page   |
| 13 | Littlestone characterization theorem           | B       | 1.0  | 0.10         | 0.00     | 0.90 | 1.00 | 0.5 page   |
| 14 | EX-identification in the limit                 | A       | 1.0  | 0.10         | 0.00     | 0.90 | 1.00 | 5 lines    |
| 15 | **Gold's theorem**                             | B + D   | 1.0  | 0.25         | 0.50     | 0.90 | 1.00 | 1.0 page   |
| 16 | Mind change dimension and ordinal bounds       | A + B   | 1.0  | 0.30         | 0.00     | 0.85 | 1.00 | 0.8 page   |
| 17 | **PAC ⇏ Online (threshold class witness)**     | D       | 1.0  | 0.40         | 1.00     | 0.90 | 1.00 | 0.6 page   |
| 18 | **Gold ⇏ PAC (finite-subset witness)**         | D       | 1.0  | 0.40         | 1.00     | 0.90 | 1.00 | 0.6 page   |
| 19 | Online ⇒ PAC (unconditional)                   | B       | 1.0  | 0.20         | 0.00     | 0.95 | 1.00 | 0.3 page   |
| 20 | Borel parameterization                         | A + E   | 0.85 | 0.15         | 0.25     | 0.70 | 1.00 | 0.6 page   |
| 21 | Analytic measurability bridge                  | B + C   | 1.0  | 0.40         | 0.00     | 0.90 | 1.00 | 1.0 page   |
| 22 | **Borel-analytic separation (Krapp-Wirth fix)**| C       | 1.0  | 0.50         | 0.30     | 0.80 | 1.00 | 1.0 page   |

**Profile distribution for the η check.** A: 10. B: 10. C: 3. D: 2. E: 1. F: 0. G: 0.
B sits at 38%, under the 40% homogeneity threshold. A dominates the cheap vocabulary
end (short inline definitions that carry no risk of manufactured content). No profile
crosses the warning line. No profile F because the kernel has zero sorry and all v1
conjuncts are closed; open frontiers return in v2 with compression and MBL monad.

Total body estimate: approximately 13 to 14 pages for v1 proper.

## Detailed entries for the asymmetric concepts

### 9. Five-way equivalence (crown jewel)

g_Pl is elevated to around 0.3 because the literature ranges across several framings:
the 4-way classical (VC finite ↔ uniform convergence ↔ PAC learnable ↔ ERM consistent),
the 5-way refinement with explicit rate bounds, and this kernel's version which makes
the NullMeasurableSet hypothesis explicit rather than folding it silently into a Borel
assumption on the hypothesis class. Coh_surprise sits at 0.5: five a priori distinct
conditions collapse to one equivalence class, and the collapse is the content. Inv is
bounded because the theorem statement requires a measurability certificate on the
hypothesis class; drop the certificate and the statement falls back to a 3-way
equivalence only.

**Profile: B + C (mixed).** Primary is load-bearing theorem with a proof journey; the
architecture of the chain is the content. Secondary is revelation: the opening should
mark the surprise of the collapse before settling into methodical derivation.

**Centerpiece.** The proof chain. Lemma chain:

    Sauer-Shelah (growth polynomial) → Hoeffding on the growth function →
    uniform convergence over the class → realizability gives PAC via ERM.

The backward direction (PAC → VC finite) goes via an infinite-shattered-set
contradiction. The fifth equivalence (WellBehavedVCMeasTarget) connects to §6.

**Length allocation.** 2.0 pages. The single largest concept in v1.

**Structure prescription.** Theorem statement first, as a bundled 5-way conjunction in
one block. Then §2.3.1 Sauer-Shelah. §2.3.2 Uniform convergence via symmetrization.
§2.3.3 The NullMeasurableSet hypothesis and why it is weaker than the standard Borel
assumption. §2.3.4 Proof of the forward implication. §2.3.5 Backward implication
sketch. §2.3.6 Connection to §6.

**Tone.** Anticipatory and methodical at the opening. Compression at the Sauer-Shelah
lemma (the double-counting combinatorial crux). Release after the uniform convergence
lemma lands. An explicit marker paragraph for the NullMeasurableSet hypothesis pulling
back from the proof journey to say: here is the point where this kernel differs from
the standard treatment.

**Dependency skeleton.** `\uses{sauer_shelah, symmetrization, uniform_convergence,
erm_soundness, nullMeasurable_defn}`.

### 10. NullMeasurableSet refinement

g_Pl low (the refinement is a precise substitution of one measurability class for
another). Coh_surprise 0.5 and Coh_fail 0.3: the refinement shows that the literature's
Borel assumption is stronger than needed, which is a compositional failure of the
stronger claim. The failure is of the literature's hypothesis, not of the theorem.

**Profile: C (Revelation).** Structure is narrative: start with the problem (the
5-way equivalence as traditionally stated requires Borel), show why the Borel assumption
looked natural (it was imported wholesale from the measurability hypothesis on the bad
event), then reveal the resolution (completion-measurability is enough and
completion-measurability is what the symmetrization step uses).

**Centerpiece.** The moment of substitution. A single bold sentence in the blueprint:
"Replace MeasurableSet with NullMeasurableSet throughout the bad-event analysis. The
proof goes through, and the theorem becomes strictly more general."

**Length allocation.** 1.0 page.

**Structure prescription.** Paragraph 1 states the traditional 5-way with Borel.
Paragraph 2 reframes the hypothesis as a choice rather than as forced structure.
Paragraph 3 exhibits the weakening. Paragraph 4 points forward to §6.3 which carries
the witness class where the weakening is strict.

**Tone.** Anticipatory, slow build. "One might expect that..." Then a short punchy
sentence at the reveal. Expansive on the consequences afterwards.

**Dependency skeleton.** `\uses{five_way_equivalence, symmetrization, analytic_measurability_bridge}`.

### 15. Gold's theorem

g_Pl crisp. Coh_fail 0.5 because the result is a negative result about an entire class
of learners (those based on text enumeration). The witness construction (finite subsets
plus an infinite target) is where the content lives. Inv 0.9.

**Profile: B + D (mixed).** Primary is load-bearing theorem via witness construction.
Secondary is negative result: the diagonalization-style construction IS the mathematical
content.

**Centerpiece.** The enumeration of texts. Given the infinite target `c_inf` and any
proposed learner L, the construction takes a countable surjection onto the positive
support of `c_inf`, interleaves it with the enumeration of `c_inf` itself, builds finite
sets S_n, and shows that on the text generated by any S_n the learner must converge to
the characteristic function of S_n (which disagrees with c_inf on at least one point
the learner has not yet seen). The construction is visible at
`FLT_Proofs/Theorem/Gold.lean`.

**Length allocation.** 1.0 page.

**Structure prescription.** Theorem statement. The construction with explicit naming
of the surjection, the embedding, and the S_n family. The diagonalization step. The
conclusion. The construction IS the content; do not fold it into a "by contradiction,
suppose L learns this class" gloss.

**Tone.** Diagnostic and adversarial in the Profile D sense. The witness is built with
the energy of a chess problem. Short precise sentences. No rhetorical softening.

### 17 and 18. Paradigm separations PAC ⇏ Online and Gold ⇏ PAC

Shared measurements: Coh_fail 1.0 for both (explicit non-implications). σ_Pl 1.0 (the
witnesses are specific and crisp). Both are Profile D with the witness as centerpiece.

**PAC ⇏ Online.** Threshold class on ℕ. The class {h_n : ℕ → Bool | h_n(k) = [k ≥ n],
n ∈ ℕ}. PAC learnable by ERM (VCDim = 1). Not Online learnable because the Littlestone
dimension is infinite: the mistake tree of depth k exists for every k, obtained by
binary-searching the threshold.

**Gold ⇏ PAC.** The class of indicators of finite subsets of ℕ plus the indicator of
ℕ itself. Gold-learnable via a straightforward enumeration-based algorithm that outputs
the current observed support. Not PAC learnable because every finite set is shattered
by the finite-subset indicators, so VCDim is infinite.

**Length allocation.** 0.6 page each.

**Tone.** Adversarial and precise. Each witness is named as a specific object; the text
walks the reader through the shattering argument and the corresponding learner failure.

### 22. Borel-analytic separation theorem

g_Pl low. Coh_surprise 0.5 and Coh_fail 0.3 against the Krapp-Wirth 2024 claim. Inv
0.8. This is the theorem that makes the §10 refinement content rather than cosmetic.

**Profile: C (Revelation).**

**Centerpiece.** The singleton-class witness. Given an analytic non-Borel set A ⊆ ℝ,
the concept class C_A = {0} ∪ {1_{a} : a ∈ A} satisfies WellBehavedVCMeasTarget but
fails KrappWirthWellBehaved. The bad event is rewritten as the preimage of a planar
witness {(x,y) : y ∈ A, x ≠ y} ⊆ ℝ × ℝ, which is analytic but not Borel. Therefore the
bad event is NullMeasurable but not MeasurableSet.

**Length allocation.** 1.0 page.

**Structure prescription.** Context on Krapp-Wirth 2024 and the standard Borel
assumption. The counterexample chain, made explicit at each step. The proof is the
chain. Close with a sentence on what the existence of this witness means for the v1
theorem (T1): the five-way equivalence as stated by Krapp-Wirth is a strict
specialization of (T1), not an equivalent statement.

**Tone.** Clinical diagnostic with Profile E flavor, because the obstruction to the
Borel hypothesis is structural rather than computational. Voice: "The analogy between
Borel and NullMeasurable holds up to the following point. Beyond that point, the
singleton witness shows the gap is strict."

## Derived global structure

Sections for `content.tex`, with length and profile budgets.

### §0 Introduction (1.0 page, flat orientational)

States the scope (core story), names the novelty (measurability refinement), and
orients the reader toward the three paradigm characterizations as the structural
anchors of the blueprint. Flat declarative throughout. No rhetorical softening.

### §1 Primitives (1.0 page, Profile A throughout)

Concept class, batch learner, realizable and agnostic framings, sample, loss,
empirical and true error. Dictionary-like. Short. Carries no proofs.

### §2 PAC characterization (3.5 pages, centered on the five-way equivalence)

- §2.1 VC dimension and shattering (0.5 page)
- §2.2 Sauer-Shelah lemma (0.5 page, proof via double counting)
- §2.3 The five-way equivalence (2.0 pages, including the NullMeasurableSet refinement
  subsection)
- §2.4 Pointer forward to the measurability layer (0.5 page)

### §3 Online characterization (1.5 pages)

- §3.1 Littlestone dimension and mistake trees (0.5 page)
- §3.2 Standard Optimal Algorithm (0.5 page)
- §3.3 Littlestone characterization theorem (0.5 page)

### §4 Gold characterization (1.8 pages)

- §4.1 EX-identification from text (0.3 page)
- §4.2 Gold's theorem (1.0 page, centered on the enumeration witness)
- §4.3 Mind change dimension and ordinal bounds (0.5 page)

### §5 Three-paradigm separations (1.5 pages)

- §5.1 PAC ⇏ Online (0.6 page, threshold class witness)
- §5.2 Gold ⇏ PAC (0.6 page, finite-subset witness)
- §5.3 Online ⇒ PAC (0.3 page, unconditional)

### §6 Measurability layer (2.6 pages)

- §6.1 Borel parameterization and the symmetrization route (0.6 page)
- §6.2 Analytic measurability bridge via Choquet capacitability (1.0 page)
- §6.3 Borel-analytic separation (1.0 page, singleton-class witness)

### §7 Closing notes (0.5 page)

Brief pointer to v2 (compression, MBL monad) and an acknowledgment of what is outside
the blueprint (PAC-Bayes, extended criteria, Baxter multi-task). Flat.

Total body: 13.4 pages. With front matter, references, and the dependency graph, a
printed v1 runs to 15 to 18 pages.

## Tonal trajectory across sections

§0 flat, orientational. §1 flat A-tone, near dictionary. §2 has the richest trajectory:
tightening across §2.1 and §2.2, peak compression at Sauer-Shelah, release into §2.3,
sharp reveal at the NullMeasurableSet refinement mid-§2.3, aftermath into §2.4. §3
methodical, compressed at SOA's optimality proof. §4 diagnostic and sharp at the Gold
enumeration construction. §5 is parallactic (Profile G flavor at section level even
though individual subsections are D): each subsection sits in the voice of the relevant
paradigm, with explicit transition markers between paradigms. §6 anticipatory in §6.1,
proof journey in §6.2, sharp clinical turn in §6.3 at the Krapp-Wirth correction. §7
flat.

No section repeats the previous section's tonal arc. No sustained passage longer than
one page without a sentence under nine words.

## Dependency skeleton for `\uses{}` wiring

High-level edges for v1:

- `five_way_equivalence` uses `{sauer_shelah, symmetrization, uniform_convergence, erm_soundness, nullMeasurable_defn}`
- `sauer_shelah` uses `{}` (base lemma inside the blueprint)
- `symmetrization` uses `{iid_setup, nullMeasurable_bad_event}`
- `nullMeasurable_refinement` uses `{five_way_equivalence, symmetrization, analytic_measurability_bridge}`
- `littlestone_characterization` uses `{mistake_tree, soa}`
- `soa` uses `{mistake_tree}`
- `gold_theorem` uses `{enumeration_infrastructure}`
- `mind_change_characterization` uses `{gold_theorem}`
- `pac_not_online` uses `{threshold_class, vc_dim_threshold, littlestone_dim_threshold}`
- `gold_not_pac` uses `{finite_subset_class, vc_dim_finite_subsets}`
- `online_implies_pac` uses `{littlestone_characterization, uniform_convergence}`
- `analytic_measurability_bridge` uses `{choquet_capacitability}`
- `borel_analytic_separation` uses `{singleton_class, planar_witness, analytic_non_borel_set}`

Choquet capacitability itself is a pure-math prerequisite left as a black box in v1
with a Mathlib pointer; the full proof lives in `FLT_Proofs/PureMath/ChoquetCapacity.lean`
and will ship as a separate Mathlib PR.

## Draft informal statements for v1 main theorems

Preliminary, draft-quality, in content-discovery register. The LaTeX pass will polish
wording and fix exact Lean identifiers. Each statement notes the target file for the
`\lean{}` macro.

**(T1) Five-way equivalence for PAC learning.** Let C be a concept class over an
infinite domain X such that C satisfies WellBehavedVCMeasTarget. The following are
equivalent: (i) C has finite VC dimension; (ii) C satisfies uniform convergence of
empirical to true error over all distributions; (iii) empirical risk minimization over
C is a PAC learner; (iv) C is PAC learnable; (v) every realizable distribution admits
a sample complexity bound polynomial in 1/ε and 1/δ. The equivalence holds with the
NullMeasurableSet hypothesis on the bad event, which is strictly weaker than the Borel
hypothesis used in the standard treatment. `\lean{FLT_Proofs.Theorem.PAC.fundamentalTheorem}`
(exact identifier to be confirmed in the implementation session).

**(T2) NullMeasurableSet refinement.** (T1) holds with the bad event required only to
be NullMeasurable rather than MeasurableSet in the Borel sense. The weakening is strict:
see (T9).

**(T3) Littlestone characterization.** Let C be a concept class. C is online learnable
if and only if LittlestoneDim(C) < ∞. Forward direction by a mistake-tree shattering
argument; backward direction by the Standard Optimal Algorithm. For nonempty C the
optimal mistake bound equals LittlestoneDim(C).
`\lean{FLT_Proofs.Theorem.Online.littlestone_characterization}`.

**(T4) Gold's theorem (1967).** Let C be a concept class over a countable X containing
all finite subsets and at least one infinite set. Then C is not EX-identifiable in the
limit from text. The obstruction is witnessed by an enumeration construction that forces
any proposed learner to converge on a finite approximation that disagrees with the
infinite target on an unobserved point. `\lean{FLT_Proofs.Theorem.Gold.gold_theorem}`.

**(T5) Mind change characterization.** (v1 placeholder; see D1 below on the scope
decision.) For a precise subclass of text-based learning criteria, the mind change
dimension with ordinal bounds characterizes the class of learnable families.
`\lean{FLT_Proofs.Theorem.Extended...}` (scope TBD).

**(T6) PAC ⇏ Online.** The threshold class T = {h_n : ℕ → Bool | h_n(k) = [k ≥ n],
n ∈ ℕ} is PAC learnable (VCDim(T) = 1) but not online learnable (LittlestoneDim(T) = ∞).
`\lean{FLT_Proofs.Theorem.Separation.pac_not_online}` (exact identifier TBC).

**(T7) Gold ⇏ PAC.** The class F = {1_S | S ⊆ ℕ finite} ∪ {1_ℕ} is EX-identifiable
(Gold-learnable) but not PAC learnable (VCDim(F) = ∞).
`\lean{FLT_Proofs.Theorem.Separation.gold_not_pac}` (exact identifier TBC).

**(T8) Online ⇒ PAC (unconditional).** Every online learnable class is PAC learnable.
Proof via the Littlestone characterization and the fact that finite Littlestone
dimension implies finite VC dimension, followed by (T1).
`\lean{FLT_Proofs.Theorem.Separation.online_implies_pac}` (exact identifier TBC).

**(T9) Borel-analytic separation (Krapp-Wirth correction).** There exists a concept
class on ℝ whose ghost-gap bad event is NullMeasurable but not Borel. Concretely, let
A ⊆ ℝ be any analytic non-Borel set and let C_A = {0} ∪ {1_{a} : a ∈ A}. Then C_A
satisfies WellBehavedVCMeasTarget but fails KrappWirthWellBehaved. The witness in the
proof is the planar set {(x,y) : y ∈ A, x ≠ y} ⊆ ℝ × ℝ, which is analytic but not
Borel. `\lean{FLT_Proofs.Theorem.BorelAnalyticSeparation.singleton_badEvent_not_measurable}`.

**(T10) Analytic measurability bridge.** Every analytic set in a standard Borel space
is NullMeasurable with respect to every completion of a Borel probability measure. Proof
via Choquet capacitability (Kechris 30.13). `\lean{FLT_Proofs.PureMath.AnalyticMeasurability...}`
(exact identifier TBC).

## Open decisions

**D1. Framing of the mind-change theorem (T5).** The precise scope of the mind-change
characterization is a design question. Option (a): state only for EX-learnability,
matching Gold's original setting. Option (b): state for a broader family of text-based
criteria with ordinal bounds. Recommendation: (a) for v1 with a remark pointing at the
kernel's extended criteria infrastructure.

**D2. Choquet capacitability in the blueprint.** The proof is 416 lines in the kernel
and Mathlib-contributable. Option (a): black-box reference in v1 and ship the proof as
a standalone Mathlib PR. Option (b): include a proof sketch in §6.2 for readers who
want the analytic machinery. Recommendation: (a), with a footnote pointer to the kernel
file.

**D3. Treatment of the hypothesis `WellBehavedVCMeasTarget`.** This name is kernel-
specific. Options: introduce the name carefully with a paragraph of motivation, or use
a more traditional label like "null-measurable bad event" for the informal statements.
Recommendation: introduce the kernel name in §6.1, then use it throughout §2.3 and §6
without re-explaining.

**D4. Inclusion of Sauer-Shelah proof vs. black-box.** Sauer-Shelah is standard in
learning theory textbooks. Option (a): full double-counting proof (0.5 page).
Option (b): statement only with a citation. Recommendation: (a), because the
double-counting proof is short and the blueprint's educational role benefits from
at least one combinatorial proof that a reader can check by hand.

**D5. Figures.** The dep-graph tool produces the dependency diagram automatically.
Additional hand-drawn figures worth considering: (i) a two-dimensional map of the
three paradigms with ⇒ edges and crossed-out edges for ⇏; (ii) a schematic of the
singleton-class witness in (T9). Recommendation: add (i) in §5 as a summary; defer (ii).

**D6. Self-reference language.** The kernel's README refers to the project as "the
kernel". Blueprint prose should use "this kernel" or "the formalization", not "this
paper" or "this blueprint", to match the existing self-description.

## Next actions

Once the live docs deploy is green and the docstring pass has landed:

1. `leanblueprint new` in the repo root to scaffold `blueprint/src/content.tex`,
   `blueprint/src/web.tex`, and the `blueprint/` infrastructure.
2. Port the scope and section structure from this PLAN into `content.tex`.
3. Draft §0, §1, §2.1, §2.2, §2.3 (crown jewel section with the refinement), §2.4 in
   one implementation session.
4. Draft §3, §4, §5 in a second session.
5. Draft §6 in a third session (measurability layer; most care needed).
6. Wire the `\uses{}` dependencies per the skeleton above. Verify the dep-graph
   renders without orphaned nodes.
7. Verify every `\lean{}` macro resolves against a live identifier in the doc-gen4
   output. Use `lake exe checkdecls blueprint/lean_decls` as part of the docs workflow
   to enforce this.
8. Flip `blueprint: false → true` behavior in `.github/workflows/docs.yml` (see the
   workflow update section below).

## Workflow update needed before blueprint ships

The current `.github/workflows/docs.yml` hand-rolls doc-gen4 build and does not handle
blueprint. Before step 8 above, port the blueprint branch of
`docgen-action/scripts/build_docs.sh` into the hand-rolled workflow:

- Add a step that installs `leanblueprint` and `pygraphviz` inside a texlive-action
  docker environment (`ghcr.io/xu-cheng/texlive-full:2025xxxx` or later).
- Build the blueprint PDF with `leanblueprint pdf`.
- Build the blueprint web version with `leanblueprint web`.
- Copy `blueprint/print/print.pdf` to `docs/blueprint.pdf`.
- Copy `blueprint/web/` to `docs/blueprint/`.
- Run `lake exe checkdecls blueprint/lean_decls` as a verification step. This
  requires adding the `checkdecls` package as a docbuild require in the generated
  `docbuild/lakefile.toml`.

Estimated addition: 40 to 60 YAML lines plus one Python dependency step and one
Lake require in the docbuild-creation step of the workflow.

## Revision history

- v1 draft: task-URS-manuscript discovery pass. Scope v1 = core story.
  Profile distribution checked under the 40% homogeneity threshold. Dependency skeleton
  and draft informal statements captured. Next action: `leanblueprint new` in a fresh
  implementation session.

- v1 book-grade rewrite (session 4): imported chapters 0-5 verbatim from the
  companion textbook with `\lean{}` annotations, copied `flt_bibliography.bib`
  as `blueprint/src/references.bib`, updated preamble to match book conventions,
  added Chapter 6 as net-new content, wired initial CI workflow port.

- v1 publication-grade rewrite (session 5): the full task-URS-manuscript pass
  was rerun on Chapter 6 (the kernel's novel contribution) per the skill's
  three-step procedure. Two references missing from the book bibliography were
  added (KrappWirth2024 arXiv:2410.10243, Kechris1995 GTM 156). An A4 violation
  in `ch02_pac.tex` was corrected (`\lean{sauer_shelah}` was incorrectly attached
  to `def:growth-function`, which is a definition; the annotation now lives
  only on `lem:sauer-shelah`). A refinement remark was added after the VC
  characterization theorem pointing forward to Chapter 6 so the reader
  encounters the null-measurability vs Borel gap before reading the four-stage
  proof that depends on it. The CI workflow was tightened: `checkdecls` is now
  added as a Lake dependency in the generated `docbuild/lakefile.toml`, the web
  build switched from direct plastex to the canonical `leanblueprint web` CLI
  (which auto-generates `blueprint/lean_decls`), and `lake exe checkdecls
  ../blueprint/lean_decls` is invoked as a hard-failing gate. Silent `|| true`
  pass-throughs were removed.

### Chapter 6 URS measurements (session 5)

Computed per task-URS-manuscript Step 1 (Cuzzolin mass functions per
measurement class). These drove the section-level structural decisions:
content length, environment selection, diagram requirement, tonal arc.

```
§6.1 Borel parameterization and the symmetrization route
  g_Pl       = 0.00 (single crisp definition of Borel parameterization)
  sigma_Pl   = 1.00
  Coh_fail   = 0.25 (edge: symmetrization step fails to preserve Borelness)
  Coh_surpr  = 0.00
  Inv        = 0.50 (boundary at multiclass / regression / unsupervised)
  Comp       = 1.00
  Profile    = E (Obstruction) primary, hint of C secondary
  Centerpiece= the precise point where "Borel on the product" is stronger
               than "null-measurable wrt completion"
  Tone arc   = diagnostic / clinical, with explicit Krapp-Wirth diagnosis
               remark box
  Length     = 1.5 pages
```

```
§6.2 The analytic measurability bridge via Choquet capacitability
  g_Pl       = 0.50 (three defensible framings of Choquet: capacity,
                     Souslin, compact approximation)
  sigma_Pl   = 0.50
  Coh_fail   = 0.00
  Coh_surpr  = 0.50 (Choquet-learning bridge is the revelation edge)
  Inv        = 1.00 (every Borel probability measure on every Polish space)
  Comp       = 0.85 (Mathlib contribution status partial)
  Profile    = B + C (load-bearing with revelation at the bridge)
  Centerpiece= the bridge sentence tying Choquet's 1955 capacitability
               theorem to the ghost-gap bad event of statistical learning
  Tone arc   = anticipatory then sharp turn at the bridge, expansive
               after
  Length     = 1.3 pages
```

```
§6.3 The Borel-analytic separation theorem
  g_Pl       = 0.00 (kernel is sole authority for the separation)
  sigma_Pl   = 1.00
  Coh_fail   = 0.20 (one fails edge: WBVCMeasTarget vs KrappWirthWB)
  Coh_surpr  = 0.40 (two surprises: individual measurability does not
                     lift, and the Souslin-not-Borel planar witness)
  Inv        = 0.33 (robust on R, boundary for other Polish spaces
                     and higher sample sizes)
  Comp       = 1.00 (all five theorems in the chain proved sorry-free)
  Profile    = C (Revelation) primary, D (Negative Result) secondary
  Centerpiece= singleton class over an analytic non-Borel set plus the
               planar-witness reduction
  Environments used: \begin{historical} for Krapp-Wirth 2024 context,
                     \begin{separation} for the main theorem block,
                     TikZ figure for the planar witness W_A
  Tone arc   = build tension through the singleton class definition and
               individual-measurability lemma, sharp turn at the planar
               reduction, slow burn through the analytic/not-Borel steps,
               witness-centered close
  Length     = 3.2 pages
```

Homogeneity check: Chapter 6 has three sections with distinct primary
profiles (E, B+C, C+D). Centerpieces are distinct (obstruction point,
bridge sentence, witness construction). Tonal arcs are distinct
(diagnostic, anticipatory-sharp, tension-release-witness). No
homogeneity warning. No banned vocabulary. Zero em-dashes. 14 unique
`\lean{}` identifiers in the chapter, all cross-checked against source.

- Next action after session 5: wait for CI workflow run. If the first
  run goes green, the blueprint v1 first-pass content is complete. If
  checkdecls reports unresolved identifiers, reconcile per the error
  listing and push a fix.
