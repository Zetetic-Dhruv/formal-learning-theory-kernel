# Methodology v1: Task URS State

This file is the running URS for the methodology artifact, derived from the
task-URS-manuscript Cuzzolin-mass-function procedure. It drives content
discovery for `methodology/src/content.tex` in subsequent implementation
sessions. Sibling of `blueprint/PLAN.md`. Audience: formalization specialists
and proof automation researchers, not learning theorists. Both artifacts
render into the same Pages site with explicit cross-links.

## Scope of v1

Core content: the Proof World Model's Layer 1 (the 21-metaprogram empirical
taxonomy extracted from 43 Lean 4 source files, stored in
`world_model/proof_world_model.json`) and Layer 2 (TPG_FLT, the typed proof
operad in `world_model/WorldModel/`, around 940 lines of Lean 4, 0 sorry, 27
of 27 non-trivial tests passing). Plus two case studies: the measurable inner
event metaprogram (README §IV, instantiated twice in the kernel) and the
premise design blueprint (README §IV plus `assets/premise_blueprint.yaml`,
a Phase 1 plus Phase 2 methodology for constructing typed premises).

Deferred to v2: Layer 3 planning tactic (`bridge_search`), currently in
`world_model/future_work/`. Will be documented alongside any new generators
or failure rules added as part of kernel extensions.

Important property: the entire TPG_FLT source is Lean-core only. No Mathlib
dependency, no `FLT_Proofs` dependency. Reads and builds independently.

## Methodology

Same Cuzzolin procedure as `blueprint/PLAN.md`. For each concept X:

    M(X) = (g_Pl, g_Coh, Inv_score, Comp_score, Tone_trajectory)

plus auxiliary quantities (σ_Pl, Coh_fail, Coh_surprise, Open_count) per
task-URS-manuscript Step 1. Profile classification per Step 2. Structural
prescriptions per Step 3. Asymmetric content weight principle.

## Concept inventory and measurements

Twenty concepts, filtered from the full Layer 1 plus Layer 2 content.

| #  | Concept                                                            | Profile | σ_Pl | Coh_surprise | Coh_fail | Inv  | Comp | Length    |
|----|--------------------------------------------------------------------|---------|------|--------------|----------|------|------|-----------|
| 1  | Lean 4 metaprogramming primer (MVarId, TacticM, composition)       | A       | 1.0  | 0.00         | 0.00     | 1.00 | 1.00 | 0.5 page  |
| 2  | Metaprogram as unit of proof method                                | A       | 0.9  | 0.20         | 0.00     | 0.90 | 1.00 | 0.3 page  |
| 3  | Layer 1: the 21 metaprograms taxonomy                              | A + C   | 0.8  | 0.30         | 0.00     | 0.70 | 1.00 | 1.0 page  |
| 4  | Paradigm as a type-family lock (7-way enum)                        | A       | 1.0  | 0.15         | 0.00     | 0.90 | 1.00 | 0.3 page  |
| 5  | Interface, Generator, Plan (the three type atoms)                  | A + B   | 1.0  | 0.15         | 0.00     | 0.90 | 1.00 | 1.0 page  |
| 6  | HasType judgment (six-rule inductive)                              | B       | 1.0  | 0.20         | 0.00     | 0.90 | 1.00 | 0.8 page  |
| 7  | Admissibility and the six-way RejectReason taxonomy                | A + B   | 1.0  | 0.10         | 0.00     | 0.90 | 1.00 | 0.5 page  |
| 8  | **Failure as negative typing (`failure_as_negative_typing`)**      | C       | 0.9  | 0.40         | 0.00     | 0.90 | 1.00 | 0.8 page  |
| 9  | **GapSpec and `extension_sound` (typed openness)**                 | C       | 0.9  | 0.45         | 0.00     | 0.90 | 1.00 | 0.6 page  |
| 10 | The 17 concrete interfaces in `fltTheory` (catalogue)              | A       | 1.0  | 0.00         | 0.00     | 0.80 | 1.00 | 0.5 page  |
| 11 | The 17 concrete generators (5 structural + 12 domain)              | A + B   | 1.0  | 0.10         | 0.00     | 0.80 | 1.00 | 0.8 page  |
| 12 | The 7 failure rules FD1-FD7                                        | A + B   | 1.0  | 0.10         | 0.10     | 0.85 | 1.00 | 0.5 page  |
| 13 | Six pipeline binding theorems (PAC, DST, Online, Gold, Sep, Bayes) | B       | 1.0  | 0.15         | 0.00     | 0.85 | 1.00 | 0.5 page  |
| 14 | `corpus_relative_completeness`                                     | B       | 1.0  | 0.10         | 0.00     | 0.85 | 1.00 | 0.3 page  |
| 15 | **`no_universal_generator` (paradigm lock theorem)**               | B + D   | 1.0  | 0.20         | 0.30     | 0.85 | 1.00 | 0.6 page  |
| 16 | **NT1: cross-paradigm composition fails (65-line proof)**          | D       | 1.0  | 0.30         | 1.00     | 0.90 | 1.00 | 0.7 page  |
| 17 | Cost model (PlanCost, NFPlan, ordering tests)                      | A + B   | 1.0  | 0.10         | 0.00     | 0.85 | 1.00 | 0.6 page  |
| 18 | **Case study: measurable inner event metaprogram**                 | A + C   | 0.9  | 0.30         | 0.00     | 0.90 | 1.00 | 0.8 page  |
| 19 | Premise design blueprint (Phase 1 + Phase 2)                       | C + F   | 0.9  | 0.25         | 0.00     | 0.70 | 0.70 | 1.0 page  |
| 20 | Layer 3: planning tactic (future work)                             | F       | 0.5  | 0.10         | 0.00     | 0.50 | 0.00 | 0.3 page  |

**Profile distribution for the η check.** Primary-profile counts: A 8, B 4,
C 4, D 2, E 0, F 2, G 0. None of A, B, C exceeds the 40% homogeneity
threshold. Profile A dominates the cheap catalogue end (short definitional
entries), Profile B carries the load-bearing definitions and pipeline
theorems, Profile C carries the two Revelation moments (failure as negative
typing, typed openness via GapSpec), Profile D carries the paradigm lock and
NT1 negative results, and Profile F carries the planning-layer frontier.
Distribution is varied and asymmetric by design.

Total body estimate: approximately 13 to 14 pages for methodology v1.

## Detailed entries for the asymmetric concepts

### 8. Failure as negative typing

g_Pl is nonzero (around 0.2) because the "failure as first-class typing"
framing is a shift from the standard "absence of derivation" pattern used in
Mtac, Isar, and abstract-tactic proposals. Coh_surprise 0.4: treating a
failure rule as a derivation OF a rejection (rather than the non-existence of
a derivation) is a reframing that changes what the typing judgment IS.

**Profile: C (Revelation).** Structure is narrative. Start with the standard
framing (failure = absence). Show why that framing leaves the failure modes
of README §IV invisible to the type system. Reveal the negative-typing
reframing. Walk through the `FailureRule` structure and the
`failure_as_negative_typing` theorem, which proves that a matching rule
produces a `RejectReason` as an error inside the `Except` monad.

**Centerpiece.** The theorem itself, stated in English and then in Lean. The
proof in the kernel is a case split on the structure of `admissible`: if
paradigm mismatch fires first, the error is `paradigmMismatch`; if a missing
premise fires, the error is `missingPremise`; otherwise the failure rule
produces the error directly.

**Length allocation.** 0.8 page.

**Tone.** Anticipatory in setup. Short compressed sentence at the reframing:
"Failure is not the absence of a derivation. It is a derivation of
rejection." Expansive on the consequences.

**Dependency skeleton.** Uses Interface, Generator, Theory, RejectReason, the
`admissible` function.

### 9. GapSpec and `extension_sound`

Coh_surprise 0.45: treating the absence of a theorem not as a sorry but as a
typed object `⟨source, needed, because⟩` with a proved extension-soundness
theorem is a structural reframing of proof-theory openness. This is the
formal version of "structured ignorance" in the noological URT vocabulary.

**Profile: C (Revelation).** Structure: narrative from the standard
"incomplete theory has sorries" view to the typed-openness view.

**Centerpiece.** The `extension_sound` theorem. Given a theory Σ, a gap spec
`⟨I, J, r⟩`, and a generator g with `g.input = I`, `g.outputs = [J]`, and g
admissible in `Σ ∪ {g}`, the plan `.atom g.name` types from I to [J] under
the extended theory.

**Length allocation.** 0.6 page.

**Tone.** Diagnostic. The voice observes: here is a theory-level notion of
openness that is neither "we have a sorry" nor "we have a proof". It is
"we have a typed specification of what a future generator must provide."

### 15. `no_universal_generator` (paradigm lock theorem)

g_Pl 0.1 (crisp statement once the operad formalism is in place). Coh 0.8
(the theorem is the meta-level confirmation of the README §I paradigm-locking
hypothesis). Comp 1.0. The proof is exhaustive enumeration over the 17
generators in `fltTheory`, each case discharged by `simp` on the generator's
`paradigm` field.

**Profile: B + D (mixed).** Primary: load-bearing theorem with a proof-by-
enumeration architecture. Secondary: negative result (the theorem asserts
the absence of a universal generator).

**Centerpiece.** The statement plus the 17-way case split, rendered in the
blueprint as a compact table mapping each generator to the paradigm it fails
to contain. Demonstrates exhaustively that no generator carries all three of
{pac, online, gold}.

**Length allocation.** 0.6 page.

**Tone.** Clinical and precise. Each case stated exactly. Not "we prove this
by exhaustion" (casual) but "the lock is witnessed at each of the 17
generators, as follows" (precise).

### 16. NT1: cross-paradigm composition fails

Coh_fail 1.0. Comp 1.0 (the 65-line proof is complete and sorry-free in
`NonTrivialTests.lean`).

**Profile: D (Negative Result).** The proof architecture IS the content.

**Centerpiece.** The proof structure. `seq_inv` extracts intermediate
interfaces `Js`. `atom_inv` on the first atom extracts generator identity
`gen₁`. A 17-way case split on `hg₁` isolates `gen₁ = genTreePotential`,
with the other 16 cases dispatched by `exact absurd hname₁ (by decide)`.
In the surviving case, `Js = [iOnlineLearnable]`, and `hUC` is applied to
that intermediate interface to obtain a `HasType` judgment on the second
atom. A second `atom_inv` and 17-way case split isolates
`gen₂ = genUCToPAC`, whose `input` field is `iHasUC` rather than
`iOnlineLearnable`, yielding the contradiction.

The result: the composition is ill-typed not just at the admissibility level
(which would just reject a single generator on a mismatched interface) but
at the HasType composition level. No sequential arrangement of this pair
types the transition from `iFiniteLDim` to `[iPACLearnable]`.

**Length allocation.** 0.7 page.

**Tone.** Adversarial, chess-problem precise. Each inversion step is named.
The 17-way enumeration is compressed in the blueprint rendering into a
compact table with one row per generator and a one-word disposition.

### 18. Case study: measurable inner event metaprogram

Pl low. Coh 0.7 (bridges the methodology layer with the measurability content
of blueprint v1 §6.3). Comp 1.0 (two instances in the kernel, both proved
sorry-free).

**Profile: A + C (mixed).** Primary: pattern definition (what the
metaprogram is). Secondary: the framing of an ad hoc proof technique as a
reusable typed pattern is novel in this kernel.

**Centerpiece.** The pattern. When a target event is defined by an
existential quantifier over an uncountable indexing set `C`, with the
selector `Classical.choose` not measurable, the proof pattern is: find a
measurable subset of the target event that carries the same probability
bound, then conclude by measure monotonicity. Joint measurability of the
underlying predicate in (theta, x) is the sufficient condition for the
pattern to apply.

Two instances in the kernel: the symmetrization bad event (blueprint v1
§6.3, the NullMeasurableSet refinement) and the advice elimination success
event in the compression pipeline (deferred to blueprint v2).

**Length allocation.** 0.8 page.

**Tone.** Bridging. The voice explicitly marks the parallax between proof
engineering (what the metaprogram does) and mathematical content (what the
metaprogram enables). "The pattern appears in two places. One is documented
mathematically in blueprint v1 §6.3; the other will be documented in
blueprint v2 once the compression pipeline is written up."

## Derived global structure

Sections for `methodology/src/content.tex`.

**§0 Introduction (0.8 page).** Orientational. Scope, audience, the
relationship to the mathematical blueprint, the Layer 1/2/3 architecture.
Flat declarative.

**§1 Lean 4 metaprogramming primer (0.5 page).** MVarId, TacticM, goal
profile, composition operators (sequential, parallel, focused, backtracking).
Brief dictionary register for readers who already know Lean 4 basics.

**§2 Layer 1: Empirical taxonomy (1.0 page).**
- §2.1 The 21 metaprograms (compact distillation table plus extraction
  methodology paragraph; full data in `proof_world_model.json`)
- §2.2 Distribution across paradigms (PAC dominance, Online/Gold
  self-contained, structural/cross-cutting)

**§3 Layer 2: The typed proof operad (4.0 pages).**
- §3.1 Paradigm as a type-family lock (0.3 page)
- §3.2 Interface, Generator, Plan (1.0 page)
- §3.3 The HasType judgment (0.8 page)
- §3.4 Admissibility and the RejectReason taxonomy (0.5 page)
- §3.5 **Failure as negative typing** (0.8 page, first Revelation moment)
- §3.6 **GapSpec and extension_sound** (0.6 page, second Revelation moment)

**§4 The concrete theory `fltTheory` (2.0 pages, catalogue and reference).**
- §4.1 17 interfaces across 7 paradigms (0.5 page)
- §4.2 17 generators: 5 structural and 12 domain (0.8 page)
- §4.3 7 failure rules FD1-FD7 as codifications of the README §IV failure
  taxonomy (0.5 page)
- §4.4 Strategic plans and the six pipeline binding theorems (0.2 page)

**§5 Machine-checked structural results (2.0 pages, centerpiece).**
- §5.1 `corpus_relative_completeness` (0.5 page)
- §5.2 **Paradigm lock: `no_universal_generator`** (0.8 page, 17-way
  enumeration rendered as a table)
- §5.3 **NT1: cross-paradigm composition fails** (0.7 page, the 65-line
  proof architecture as the centerpiece)

**§6 Case study: measurable inner event metaprogram (1.0 page).** Parallactic
bridge to blueprint v1 §6.3.

**§7 Cost model and plan normalization (0.6 page).** PlanCost, NFPlan, the
NT5 PAC-above-Online ordering and NT6 DST elaboration penalty observations.
Short supporting infrastructure.

**§8 Premise design blueprint: Phase 1 and Phase 2 (1.0 page).** Walkthrough
of the 8-step Phase 1 and 5-step Phase 2 process. Pointer to
`assets/premise_blueprint.yaml` for the machine-readable form.

**§9 Layer 3: Planning tactic (0.5 page, open frontier).** What
`bridge_search` is intended to do. Pointer to `world_model/future_work/`.

**§10 Closing (0.3 page).** Cross-references to blueprint v1 for the
mathematical content, and a brief pointer to the case study in §6 as the
one cross-artifact edge.

Total body: 13.7 pages. Comparable to blueprint v1's 13.4.

## Tonal trajectory

§0 flat orientational. §1 near-dictionary, terse. §2 catalogue with a brief
paragraph on extraction methodology. §3 has the richest arc: methodical
through §3.1 to §3.4, then a Revelation moment at §3.5 (failure as negative
typing) and another at §3.6 (typed openness via GapSpec); both Revelation
moments want compression at the reframing sentence and expansion on
consequences. §4 is catalogue tone, dense tables and lists. §5 is diagnostic
and clinical; §5.3 is the NT1 "chess-problem" moment of the methodology
blueprint. §6 explicitly marks the parallax between engineering and
mathematics. §7 is brief supporting infrastructure. §8 is methodological
walkthrough. §9 is honest uncertainty. §10 is flat.

The two Revelation moments in §3.5 and §3.6 plus the NT1 clinical peak in
§5.3 are the three tonal anchors. No section repeats the previous section's
arc, and no sustained passage longer than one page runs without a sentence
under nine words.

## Dependency skeleton for `\uses{}` wiring

Core chain:

- `interface_type` uses `{}`
- `paradigm_enum` uses `{}`
- `gen_level_enum` uses `{}`
- `generator_type` uses `{interface_type, gen_level_enum, paradigm_enum}`
- `plan_syntax` uses `{}`
- `reject_reason_enum` uses `{}`
- `failure_rule_type` uses `{interface_type, reject_reason_enum}`
- `gap_spec_type` uses `{interface_type, reject_reason_enum}`
- `theory_type` uses `{generator_type, failure_rule_type, gap_spec_type}`
- `admissibility_def` uses `{theory_type, interface_type, generator_type, failure_rule_type}`
- `has_type_judgment` uses `{plan_syntax, interface_type, theory_type, admissibility_def}`
- `atom_inv_lemma` uses `{has_type_judgment}`
- `seq_inv_lemma` uses `{has_type_judgment}`
- `failure_as_negative_typing_theorem` uses `{admissibility_def, failure_rule_type, reject_reason_enum}`
- `mkGap_construction` uses `{interface_type, gap_spec_type, reject_reason_enum}`
- `extension_sound_theorem` uses `{theory_type, gap_spec_type, has_type_judgment}`
- `flt_theory_instance` uses `{17_interfaces, 17_generators, 7_failure_rules}`
- `six_pipeline_binding_theorems` uses `{flt_theory_instance, has_type_judgment}`
- `corpus_relative_completeness` uses `{six_pipeline_binding_theorems}`
- `no_universal_generator` uses `{flt_theory_instance}`
- `nt1_cross_paradigm_composition_fails` uses `{flt_theory_instance, has_type_judgment, seq_inv_lemma, atom_inv_lemma}`
- `nf_plan_type` uses `{plan_syntax}`
- `plan_cost_model` uses `{generator_type, plan_syntax, nf_plan_type}`

Case-study and process content (no Lean `\uses{}`):

- `measurable_inner_event_metaprogram` references-by-href
  `blueprint_v1.null_measurable_refinement`
- `premise_design_phase1_phase2` references
  `assets/premise_blueprint.yaml`

## Draft statements for methodology v1 main definitions and theorems

Preliminary, draft-quality, in content-discovery register. The LaTeX pass
polishes wording.

**(M1) The Plan syntax.** A proof plan is an inductive data type with six
constructors: `atom(g)` invokes a generator by name, `seq(p, q)` is
sequential composition, `par(ps)` is parallel composition on all subgoals,
`guard(ℓ, p)` restricts application to interfaces carrying paradigm lock ℓ,
`choose(alts)` selects the first valid alternative, and `extend(gapName)`
emits a typed placeholder for a future generator.
`\lean{WorldModel.ProofOperad.Plan}`.

**(M2) The HasType judgment.** Under theory Σ, plan p transforms interface
I into a list of sub-obligations Os. Inductively defined with six rules:
`atom`, `seq`, `guard`, `chooseHead`, `chooseTail`, `extend`. The `extend`
rule emits a synthetic gap interface. The `par` Plan constructor has no
corresponding typing rule in the current operad; see MD7 below.
`\lean{WorldModel.ProofOperad.HasType}`.

**(M3) Failure as negative typing theorem.** If a failure rule `fd` matches
an interface I (`fd.onInput I = true`) and blocks a generator g
(`fd.blocks g.name = true`), then `Σ.admissible I g` returns an error with
a specific `RejectReason`. Failure is not the absence of a derivation; it is
a derivation of rejection.
`\lean{WorldModel.ProofOperad.failure_as_negative_typing}`.

**(M4) Extension soundness theorem.** Given a theory Σ, a gap specification
`⟨I, J, r⟩`, and a generator g with `g.input = I`, `g.outputs = [J]`, and g
admissible in `Σ ∪ {g}`, the plan `.atom g.name` types from I to [J] under
the extended theory. Adding a generator that solves a gap yields a
well-typed plan.
`\lean{WorldModel.ProofOperad.extension_sound}`.

**(M5) Paradigm lock theorem.** No generator in `fltTheory` carries all
three of the PAC, Online, and Gold paradigm labels simultaneously. Proved
by exhaustive enumeration over the 17 generators of `fltTheory`. This is
the machine-checked version of the README §I claim that the learning
paradigms are structurally separated.
`\lean{WorldModel.ProofOperadTheorems.no_universal_generator}`.

**(M6) Corpus-relative completeness.** Every major pipeline in the kernel
(`stratBuildThenBridge` for PAC, `stratProjectThenApprox` for DST,
`stratPotentialThenBound` for Online, `stratLocking` for Gold,
`stratWitnessSeparation` for Separation, `stratJensenChain` for Bayesian)
types under `fltTheory`. Proved by case split on the six pipelines, each
case discharged by its individual binding theorem.
`\lean{WorldModel.ProofOperadTheorems.corpus_relative_completeness}`.

**(M7) NT1: cross-paradigm composition fails.** The plan
`seq (atom "TreePotential") (atom "UCToPAC")` does not type from
`iFiniteLDim` to `[iPACLearnable]`. Proof uses `seq_inv` to extract the
intermediate interfaces, `atom_inv` to extract generator identity, and a
double 17-way enumeration to isolate the surviving candidates. The
contradiction is derived in the surviving case from
`genUCToPAC.input = iHasUC ≠ iOnlineLearnable`.
`\lean{WorldModel.NonTrivialTests.nt1_cross_paradigm_composition_fails}`.

**(M8) Measurable inner event metaprogram (case study).** When a target
event is defined by an existential quantifier over an uncountable set C
with a non-measurable selector, the proof pattern replaces the selector
with a measurable inner approximation that carries the same probability
bound, then concludes by measure monotonicity. Instances: symmetrization
bad event (blueprint v1 §6.3) and advice elimination (deferred to
blueprint v2). No single Lean identifier for the pattern itself; the
instances are named in the README §IV.

## Open decisions

**MD1. Scope of the Layer 1 exposition.** Option (a): full 21-metaprogram
table in §2 with a compact entry per method. Option (b): 5 to 6
representative metaprograms described fully, the other 15 to 16 listed only
by name with a pointer to `proof_world_model.json`. Recommendation: (b).
The empirical taxonomy serves as a bridge to Layer 2, not as the centerpiece.

**MD2. `\lean{}` resolution for world model identifiers.** The world model
source lives at `world_model/WorldModel/` and is not part of the
`FLT_Proofs` lean_lib built by the main lakefile. Option (a): add
`WorldModel` as a second lean_lib in the main `lakefile.lean` so doc-gen4
covers it. Option (b): create a separate lakefile inside `world_model/` and
a second doc-gen4 build pass in the docs workflow. Option (c): use inline
GitHub source links instead of `\lean{}` macros for world model identifiers
in the methodology blueprint, leaving the working build file untouched.
Recommendation: (c) for v1. Revisit after the blueprint-enabled workflow
lands and adding a second doc-gen4 coverage pass is cheap.

**MD3. Position of the premise design blueprint (§8).** The premise design
blueprint is methodology-about-methodology: a process for constructing
typed premises rather than a property of the operad itself. Option (a):
include as a standalone §8 in the methodology blueprint. Option (b): carve
out a third parallel artifact (`premise-methodology/`). Recommendation: (a).
One page of content is too small to justify a third artifact, and the
process narratively follows from the operad's extension mechanism (§3.6).

**MD4. Lean 4 metaprogramming primer scope (§1).** The primer can be a
dense half-page (MVarId, TacticM, composition types, `by`-block semantics)
or a fuller two-page tutorial. Recommendation: half-page dense primer for
readers who already know Lean 4 basics. Fuller tutorials exist elsewhere.

**MD5. Figures.** Three worth considering: (i) the generator DAG from
`world_model/dag/generator_dag.json`, showing interface flow between
generators; (ii) the six pipeline diagrams from the README §VIII figure
(the six rows including the red X for NT1); (iii) a layered architecture
diagram (Layer 1 empirical / Layer 2 typed / Layer 3 planning).
Recommendation: (i) and (ii) both essential. (iii) reuse the existing
`assets/world_model_layers.png` if legible, otherwise commission a
re-render.

**MD6. Cross-artifact references with blueprint v1.** One known cross-edge:
measurable inner event metaprogram (§6 of methodology) to NullMeasurableSet
refinement (§6.3 of mathematical blueprint). Recommendation: implement as
explicit `\href` out-of-graph hyperlinks in both artifacts with a matching
footnote in each. Do not attempt to merge the two `\uses{}` dep-graphs.

**MD7. The `par` Plan constructor has no `HasType` rule.** The `Plan`
inductive declares `par (ps : List Plan)` but the `HasType` inductive has
no `par` constructor. Any plan using `par` is currently untyped. Option (a):
document as intentional reservation for a future parallel-typing extension.
Option (b): add a `par` rule with an aggregation law over subgoal lists.
Option (c): remove `par` from the Plan enum pending a designed typing rule.
Recommendation: document as an observed gap in §3.3 and flag it as a
concrete instance of the `GapSpec` machinery the operad provides for its
own extension.

## Next actions

Prerequisites: docs CI lands, blueprint v1 implementation lands, the
blueprint-enabled workflow port is complete.

1. `mkdir -p methodology/src` and scaffold `content.tex`, `web.tex`, and
   a dep-graph configuration file.
2. Port the scope and section structure from this PLAN into `content.tex`.
3. Draft §0, §1, §2 (orientation, primer, Layer 1 taxonomy) in one session.
4. Draft §3 (typed operad) in a dedicated session. Content-heaviest section
   and wants voice extraction against `world_model/WorldModel/ProofOperad.lean`
   for docstring conventions.
5. Draft §4 (concrete theory catalogue) in a session that leans on
   `ProofOperadInstances.lean` as reference.
6. Draft §5 (machine-checked structural results) in a session centered on
   the NT1 proof architecture as the §5.3 centerpiece.
7. Draft §6 (measurable inner event case study) paired with or after
   blueprint v1 §6.3 is drafted, so the cross-reference is stable.
8. Draft §7, §8, §9, §10 in a wrap-up session.
9. Resolve MD2 (world model `\lean{}` identifiers) before flipping to CI
   build.
10. Wire the `\uses{}` dependencies per the skeleton above. Verify the
    dep-graph renders without orphaned nodes or cycles.

## Workflow implications

The methodology blueprint is outside `FLT_Proofs`, which means the docs
workflow needs:

1. A decision on how to index the world model for doc-gen4 (MD2 above).
2. The blueprint-enabled workflow port (flagged in `blueprint/PLAN.md`,
   40 to 60 YAML lines) handles a single blueprint source tree. Extending
   it to handle TWO blueprint source trees (`blueprint/src/` and
   `methodology/src/`) requires another 15 to 25 lines: a second
   `leanblueprint pdf` invocation, a second `leanblueprint web` run, a
   second `checkdecls` verification pass, and two copy steps into `docs/`.
3. The `docs/index.html` landing page (currently a redirect to `./docs/`)
   should be updated to a small landing page linking both: `docs/blueprint/`
   and `docs/methodology/`. This is a ten-line HTML change.
4. Cross-artifact references (the single known case: measurable inner
   event metaprogram) are handled as inline hyperlinks, outside the
   `\uses{}` dep-graph machinery which is single-artifact by design.

## Revision history

- v1 draft: task-URS-manuscript discovery pass, grounded in direct reads of
  `world_model/WorldModel/ProofOperad.lean`, `ProofOperadInstances.lean`,
  `ProofOperadTheorems.lean`, `NonTrivialTests.lean`, and the README §VIII
  and §IV content. Scope v1 = Layers 1 and 2 plus two case studies. Profile
  distribution verified under the 40% homogeneity threshold. Next action:
  wait for blueprint v1 implementation to land, then scaffold
  `methodology/src/`.
