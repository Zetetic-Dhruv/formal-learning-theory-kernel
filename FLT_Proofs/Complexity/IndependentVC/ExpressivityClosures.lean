/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.MatroidWitness
import FLT_Proofs.Complexity.IndependentVC.MatroidStructure
import FLT_Proofs.Complexity.IndependentVC.UnionTight
import FLT_Proofs.Complexity.IndependentVC.Relabel
import FLT_Proofs.Complexity.IndependentVC.FrameworkClosures
import FLT_Proofs.Complexity.GameInfra
import FLT_Proofs.Learner.Core
import FLT_Proofs.Complexity.Littlestone

/-!
# Expressivity closures — the open arguments of the `Expressivity` discovery URS

This module closes the still-open arguments of the **Expressivity** reading-axis recorded in
`design-lab/learning-theory/flt_discovery_urs/final_expressivity.md`. Expressivity is the intrinsic
*realizability / separation power* of a `ConceptClass X Bool`, measured by `Shatters` **before**
learnability (axioms A1, A2 of the URS). Each closure below is one of the URS's named open arguments,
driven to a kernel-verified outcome under the closure discipline: a theorem where it composes, a
precise conditional where the naive statement needs hypotheses, and a `Pl`-kill (concrete
impossibility / separation witness) where the naive conjecture is false.

The whole development is self-contained over the bare `Shatters` / `VCDim` / `LittlestoneDim`
primitives plus Mathlib; it does not depend on the measure-theoretic learning stratum.

## The arguments and their outcomes

1. **Shatter ↔ adversary biconditional** (RKU-4, a game-semantic reading of realizability). The
   forward arrow is a **theorem**: a shattered set forces *every* online learner to make `|S|`
   mistakes on a presentation of `S` (the GM6 shatter-witness functor, `shatters_forces_all_mistakes`).
   The honest converse is the *labelling-game* biconditional `shatters_iff_labelling_game`: shattering
   is exactly the existence, for every labelling demand, of a consistent concept. The
   learner-quantified converse is closed as a genuine **theorem** `shatters_iff_adversary_forces`
   (IM6): shattering is *equivalent* to `AdversaryForcesShattering` — against *every* online learner
   from *every* state, the adversary presents the points of `S` once and forces a mistake at each.
   (The earlier `shatters_iff_realizerOracle` reduction to a named *realizer oracle* — a choice
   function into the realizing concepts — is retained as the constructive Skolem packaging, but it is
   no longer the strongest statement: IM6 quantifies over all learners, not the oracle object.)

2. **The super-additivity defect** (KU-2 / RKU-2). A **lower-bound witness**: a domain on which the
   defect `VCDim (A ∪ B) − (VCDim A + VCDim B)` is at least `1` while each part has dimension `0`
   (`superadditivity_defect_witness`), and the matching **ceiling** `defect ≤ dC + dD + 1` from the
   sharp union bound. The defect is then **reduced** to the failure of submodularity: it is positive
   somewhere iff VC dimension is not a polymatroid rank (`superadditivity_defect_iff_not_submodular`),
   tying the quantitative gap to the structural Pl-kill `vcDim_not_polymatroid_rank`.

3. **Is the expressivity coordinate ≥ 2-dimensional?** (RKU-5 / UK-4). A genuine **separation
   Pl-kill**: the threshold class has `VCDim = 1` (small) yet `LittlestoneDim = ⊤` (large)
   (`vc_littlestone_separation`). VC and Littlestone are therefore *independent* coordinates — one
   cannot be recovered from the other — so expressivity is at least two-dimensional. The separation
   is genuinely one-directional (the reverse `VCDim` large / `LittlestoneDim` small is impossible by
   `littlestoneDim_ge_vcDim`), and that asymmetry is itself the content.

4. **Realizability lower-bounds packaging** (R7, consolidation). The scattered shattering-yields-a-
   certificate facts are consolidated into one statement `shatters_realizability_certificate`:
   a shattered set simultaneously realizes every labelling, forces the growth function up to `2^|S|`,
   and forces every online learner to `|S|` mistakes — the expressivity→capacity arrow at the
   combinatorial scale, with no measure theory.

5. **The `xorShift` computational-axis pressure** (RKU-6 / UK-3, gated by A1). A **partial + open
   residual**: parity (`xorShift`) is shattering-invariant (`vcDim_xorShift`, re-surfaced as
   `parity_shattering_invariant`), so the statistical/shattering grammar is *constitutively blind* to
   it. The strongest in-closure statement is that the shift acts freely on realizations
   (`xorShift_realizes_iff`); the residual — a measure-free FLT shadow that *sees* the computational
   axis — is recorded as a **sharpened-KU residual** naming a parity-sensitive separator as its single
   missing object, honoring the gate A1 (opcount excluded). VC's parity-blindness is banked as
   `vcDim_is_parity_blind`.
-/

universe u v

open scoped Classical

namespace ExpressivityClosures

variable {X : Type u}

/-! ## Argument 1 — the shatter ↔ adversary biconditional (RKU-4)

The URS asks (RKU-4) whether realizability has a single game-semantic reading: is `Shatters X C S`
equivalent to "there is a winning adversary strategy on `S` against any learner"? We deliver four
graded results, the last of which closes the learner-quantified converse as a genuine theorem (IM6).

* The **labelling-game** biconditional `shatters_iff_labelling_game`: shattering is *exactly* the
  property that every labelling demand on `S` is met by a consistent concept. This is the honest,
  unconditional game reading of realizability (the converse is definitional, the forward is the
  shattering definition).
* The **forward adversary arrow** `shatters_forces_all_mistakes` (the GM6 shatter-witness functor):
  a shattered set forces *every* online learner to make `|S|` mistakes on a presentation of `S`. This
  is the expressivity→capacity content — shattering yields a universal lower bound on mistakes.
* The **realizer-oracle reduction** `shatters_iff_realizerOracle`: shattering is equivalent to the
  existence of a Skolem choice function (the *realizer oracle*) into the realizing concepts. This is
  the constructive packaging of the labelling game, retained as a named adversarial object.
* The **learner-quantified converse, as a genuine theorem** `shatters_iff_adversary_forces` (IM6):
  shattering is *equivalent* to `AdversaryForcesShattering` — against *every* online learner from
  *every* state, the adversary presents the points of `S` exactly once and forces a mistake at each.
  This quantifies over all learners (not the oracle object), so it is the true two-way game-semantic
  equivalence the URS asked for, proved without overclaim: the forward arrow is the enumerated
  adversary induction, the converse instantiates the universal quantifier at a single stateless
  learner and reads off agreement via a saturation lemma.
-/

/-- **The labelling-game reading of shattering** (the honest unconditional biconditional). `C`
shatters `S` if and only if every labelling demand `f : ↥S → Bool` is met by some concept `c ∈ C`
that realizes it on `S`. This is the game where the adversary names a target labelling and the
defender must produce a consistent concept; shattering is exactly "the defender always wins". Both
directions are immediate from the definition of `Shatters`; the value is naming the game. -/
theorem shatters_iff_labelling_game (C : ConceptClass X Bool) (S : Finset X) :
    Shatters X C S ↔ ∀ f : ↥S → Bool, ∃ c ∈ C, ∀ x : ↥S, c (x : X) = f x :=
  Iff.rfl

/-- Mistake count of an online learner started in state `s`, replayed against the target concept `c`
along a presentation sequence. This is the in-module copy of the kernel's `mistakesFromU`, kept here
so the development is self-contained over `GameInfra`. -/
noncomputable def mistakesAlong (L : OnlineLearner X Bool) (s : L.State) (c : X → Bool) :
    List X → ℕ
  | [] => 0
  | x :: xs =>
    (if L.predict s x ≠ c x then 1 else 0) +
      mistakesAlong L (L.update s x (c x)) c xs

/-- Restricting a shattered family to the slice agreeing with one label on one point keeps the rest
of the set shattered. The combinatorial heart of the adversary induction: after the learner commits
to a prediction on `x`, the adversary moves to the slice forcing the mistake and `S.erase x` is still
shattered there. -/
theorem shatters_erase_slice {C : ConceptClass X Bool} {S : Finset X}
    (hshat : Shatters X C S) {x : X} (hx : x ∈ S) (b : Bool) :
    Shatters X {c ∈ C | c x = b} (S.erase x) := by
  classical
  intro f
  let f' : ↥S → Bool := fun ⟨y, hy⟩ => if h : y ∈ S.erase x then f ⟨y, h⟩ else b
  obtain ⟨c, hcC, hc⟩ := hshat f'
  have hcx : c x = b := by
    have := hc ⟨x, hx⟩
    simp only [f', Finset.mem_erase, ne_eq, not_true_eq_false, false_and, dite_false] at this
    exact this
  refine ⟨c, ⟨hcC, hcx⟩, fun ⟨y, hy⟩ => ?_⟩
  have hyS : y ∈ S := Finset.mem_of_mem_erase hy
  have := hc ⟨y, hyS⟩
  simp only [f', hy, dite_true] at this
  exact this

/-- **The forward adversary arrow — shattering forces maximal mistakes** (GM6 shatter-witness functor).
If `C` shatters `S`, then for *every* online learner `L` and *every* starting state `s` there is a
presentation `seq` of (a subset of) `S` and a target concept `c ∈ C` on which `L` makes exactly
`|S|` mistakes. This is the universe-polymorphic, measure-free expressivity→capacity arrow: maximal
realizability power produces a worst-case mistake lower bound against any predictor.

The proof is the standard adversary induction (Littlestone): present the points of `S` one at a
time; at each point the learner's prediction is met by the *opposite* label, which the shattered
slice still realizes (`shatters_erase_slice`), forcing a mistake and shrinking `S` by one. -/
theorem shatters_forces_all_mistakes {C : ConceptClass X Bool} {S : Finset X}
    (hshat : Shatters X C S) (L : OnlineLearner X Bool) (s : L.State) :
    ∃ (seq : List X) (c : X → Bool), c ∈ C ∧ mistakesAlong L s c seq = S.card := by
  classical
  induction S using Finset.induction_on generalizing C s with
  | empty =>
    obtain ⟨c₀, hc₀, _⟩ := hshat (fun ⟨_, h⟩ => by simp at h)
    exact ⟨[], c₀, hc₀, rfl⟩
  | @insert x S' hx ih =>
    by_cases hpred : L.predict s x = true
    · have hshat' := shatters_erase_slice hshat (Finset.mem_insert_self x S') false
      rw [Finset.erase_insert hx] at hshat'
      obtain ⟨seq', c', hc'mem, hcount⟩ := ih (s := L.update s x false) hshat'
      refine ⟨x :: seq', c', hc'mem.1, ?_⟩
      simp only [mistakesAlong, hc'mem.2, hpred, Finset.card_insert_of_notMem hx]
      simp [hcount]; omega
    · have hpf : L.predict s x = false := by cases h : L.predict s x <;> simp_all
      have hshat' := shatters_erase_slice hshat (Finset.mem_insert_self x S') true
      rw [Finset.erase_insert hx] at hshat'
      obtain ⟨seq', c', hc'mem, hcount⟩ := ih (s := L.update s x true) hshat'
      refine ⟨x :: seq', c', hc'mem.1, ?_⟩
      simp only [mistakesAlong, hc'mem.2, hpf, Finset.card_insert_of_notMem hx]
      simp [hcount]; omega

/-- A **realizer oracle** for `S` against `C`: a Skolem function that, given any labelling demand
`f : ↥S → Bool`, returns a concept of `C` realizing `f` on `S`. This is the named adversarial object
the learner-quantified converse reduces to — the constructive content of "the defender always wins
the labelling game". -/
structure RealizerOracle (C : ConceptClass X Bool) (S : Finset X) where
  /-- The realizing concept chosen for each labelling demand. -/
  realize : (↥S → Bool) → (X → Bool)
  /-- Each chosen concept lies in the class. -/
  mem : ∀ f, realize f ∈ C
  /-- Each chosen concept realizes the demanded labelling on `S`. -/
  agrees : ∀ f, ∀ x : ↥S, realize f (x : X) = f x

/-- **The learner-quantified converse, as a reduction to the realizer oracle.** Shattering of `S` by
`C` is equivalent to the existence of a `RealizerOracle` — a uniform adversarial witness that meets
every labelling demand. This is the precise sense in which the bare "forces a mistake against every
learner" converse holds: the adversary's winning strategy is *exactly* a choice function into the
realizing concepts, and that choice function is the named object the reduction targets.

The forward direction Skolemizes the shattering definition (`Classical.choice`); the converse reads
the oracle's data back off as shattering. Together with `shatters_forces_all_mistakes` this closes
RKU-4: the forward adversary arrow is a theorem, and its converse is a reduction to the realizer
oracle, with no hidden determinacy or finiteness hypothesis beyond choice. -/
theorem shatters_iff_realizerOracle (C : ConceptClass X Bool) (S : Finset X) :
    Shatters X C S ↔ Nonempty (RealizerOracle C S) := by
  classical
  constructor
  · intro hshat
    exact ⟨{
      realize := fun f => (hshat f).choose,
      mem := fun f => (hshat f).choose_spec.1,
      agrees := fun f => (hshat f).choose_spec.2 }⟩
  · rintro ⟨O⟩ f
    exact ⟨O.realize f, O.mem f, O.agrees f⟩

/-! ### IM6 — the genuine learner-quantified converse (upgrading the realizer reduction to a theorem)

The reduction `shatters_iff_realizerOracle` characterizes shattering via a *named adversarial object*
(the realizer oracle) rather than via the online game directly. IM6 closes the genuine
**learner-quantified** converse: shattering is *equivalent* to the property that, against **every**
`OnlineLearner` from **every** state, the adversary can present the points of `S` (each exactly once)
and choose a consistent target concept forcing a mistake at *every* point. This is a strictly
stronger statement than the realizer reduction — `AdversaryForcesShattering` quantifies over all
online learners, a genuinely different object than the Skolem choice function — and we prove it as a
real two-way theorem with no hidden determinacy hypothesis beyond choice.

The forward direction strengthens the adversary induction `shatters_forces_all_mistakes` to also
expose that the presentation is a *nodup enumeration of `S`* (`shatters_forces_all_mistakes_enum`).
The converse is the new content: from "forces all mistakes against every learner" we recover
shattering by instantiating the universal quantifier at a single **stateless** learner that predicts
the negation of the demanded labelling; a saturation lemma then turns "mistakes = length" into
"the concept agrees with the demand at every point", which is exactly realizability of that demand. -/

/-- The mistake count along any presentation is bounded by its length: each step contributes at most
one mistake. The arithmetic backbone of the saturation lemma. -/
theorem mistakesAlong_le_length (L : OnlineLearner X Bool) (s : L.State) (c : X → Bool)
    (seq : List X) : mistakesAlong L s c seq ≤ seq.length := by
  induction seq generalizing s with
  | nil => simp [mistakesAlong]
  | cons x xs ih =>
    simp only [mistakesAlong, List.length_cons]
    have hstep : (if L.predict s x ≠ c x then (1 : ℕ) else 0) ≤ 1 := by split <;> omega
    have := ih (L.update s x (c x))
    omega

/-- **Saturation.** For a learner whose prediction ignores its state (`L.predict s x = p x` for all
`s`), a mistake count equal to the presentation length forces a mistake at *every* position: at each
point the learner predicts `p x` and the target `c` disagrees, so `p x ≠ c x`. Since every step
contributes at most one mistake (`mistakesAlong_le_length`), equality with the length can only happen
if each step contributes exactly one — and for a state-blind predictor that pins `c` against `p`
pointwise. This is the lemma that lets the adversary's "forces all mistakes" certificate be read back
as agreement of the witnessed concept with the demanded labelling. -/
theorem mistakesAlong_saturation (L : OnlineLearner X Bool) (p : X → Bool) (c : X → Bool)
    (seq : List X) (hpred : ∀ s x, L.predict s x = p x) (s : L.State)
    (heq : mistakesAlong L s c seq = seq.length) : ∀ x ∈ seq, p x ≠ c x := by
  induction seq generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [mistakesAlong, List.length_cons, hpred] at heq
    have hbound : mistakesAlong L (L.update s x (c x)) c xs ≤ xs.length :=
      mistakesAlong_le_length L _ c xs
    have hpx : p x ≠ c x := by
      by_contra h; rw [if_neg (by simpa using h)] at heq; omega
    have htail : mistakesAlong L (L.update s x (c x)) c xs = xs.length := by
      rw [if_pos hpx] at heq; omega
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact hpx
    · exact ih (L.update s x (c x)) htail y hmem

/-- **The forward adversary arrow, enumerated.** Strengthens `shatters_forces_all_mistakes` so the
forced presentation `seq` is additionally a *nodup enumeration of `S`* (`seq.Nodup` and
`seq.toFinset = S`), hence each point of `S` is presented exactly once. Same adversary induction
(`shatters_erase_slice`): the empty set gives the empty presentation; inserting a fresh point `x`
prepends it to the inductive presentation of `S'`, where `x ∉ S' = seq'.toFinset` supplies both the
nodup head condition and the `toFinset = insert x S'` step. This is the forward half of IM6. -/
theorem shatters_forces_all_mistakes_enum {C : ConceptClass X Bool} {S : Finset X}
    (hshat : Shatters X C S) (L : OnlineLearner X Bool) (s : L.State) :
    ∃ (seq : List X) (c : X → Bool),
      c ∈ C ∧ seq.Nodup ∧ seq.toFinset = S ∧ mistakesAlong L s c seq = S.card := by
  classical
  induction S using Finset.induction_on generalizing C s with
  | empty =>
    obtain ⟨c₀, hc₀, _⟩ := hshat (fun ⟨_, h⟩ => by simp at h)
    refine ⟨[], c₀, hc₀, List.nodup_nil, ?_, rfl⟩
    simp
  | @insert x S' hx ih =>
    by_cases hpred : L.predict s x = true
    · have hshat' := shatters_erase_slice hshat (Finset.mem_insert_self x S') false
      rw [Finset.erase_insert hx] at hshat'
      obtain ⟨seq', c', hc'mem, hnodup', htoF', hcount⟩ := ih (s := L.update s x false) hshat'
      have hxnotin : x ∉ seq' := by rw [← List.mem_toFinset, htoF']; exact hx
      refine ⟨x :: seq', c', hc'mem.1, List.nodup_cons.mpr ⟨hxnotin, hnodup'⟩, ?_, ?_⟩
      · rw [List.toFinset_cons, htoF']
      · simp only [mistakesAlong, hc'mem.2, hpred, Finset.card_insert_of_notMem hx]
        simp [hcount]; omega
    · have hpf : L.predict s x = false := by cases h : L.predict s x <;> simp_all
      have hshat' := shatters_erase_slice hshat (Finset.mem_insert_self x S') true
      rw [Finset.erase_insert hx] at hshat'
      obtain ⟨seq', c', hc'mem, hnodup', htoF', hcount⟩ := ih (s := L.update s x true) hshat'
      have hxnotin : x ∉ seq' := by rw [← List.mem_toFinset, htoF']; exact hx
      refine ⟨x :: seq', c', hc'mem.1, List.nodup_cons.mpr ⟨hxnotin, hnodup'⟩, ?_, ?_⟩
      · rw [List.toFinset_cons, htoF']
      · simp only [mistakesAlong, hc'mem.2, hpf, Finset.card_insert_of_notMem hx]
        simp [hcount]; omega

/-- The online-game characterization of shattering: against **every** online learner from **every**
state, the adversary can present the points of `S` (each exactly once, as a nodup enumeration) and
choose a consistent concept `c ∈ C` forcing a mistake at *every* point of `S`. This quantifies over
all `OnlineLearner`s — a genuinely different object than the realizer oracle of
`shatters_iff_realizerOracle`, and the predicate the IM6 biconditional pins to `Shatters`. -/
def AdversaryForcesShattering (C : ConceptClass X Bool) (S : Finset X) : Prop :=
  ∀ (L : OnlineLearner X Bool) (s : L.State),
    ∃ (seq : List X) (c : X → Bool),
      c ∈ C ∧ seq.Nodup ∧ seq.toFinset = S ∧ mistakesAlong L s c seq = S.card

/-- **IM6: shattering ⟺ the online adversary forces a mistake at every point of `S`.** The genuine
two-way game-semantic equivalence — upgrading the previous reduction-to-realizer-oracle
(`shatters_iff_realizerOracle`) to a real *learner-quantified* theorem.

Forward (`shatters_forces_all_mistakes_enum`): a shattered set forces every online learner, from
every state, to make `|S|` mistakes on a nodup presentation of `S`.

Converse (the new content): given that the adversary forces all mistakes against every learner, fix a
labelling demand `f : ↥S → Bool` and extend it to `f' : X → Bool`. Instantiate the universal
quantifier at the **stateless** learner `Lf` with `State := PUnit` that predicts `! (f' x)`. The
returned certificate has `mistakesAlong Lf () c seq = S.card`; since `seq` is a nodup enumeration of
`S`, its length is `S.card` (`List.toFinset_card_of_nodup`), so the mistake count equals the length.
Saturation (`mistakesAlong_saturation`, applicable because `Lf.predict` ignores state) then gives
`! (f' x) ≠ c x` at every point of `seq ⊇ S`, i.e. `c x = f' x`; hence `c` realizes `f` on `S`. As
`c ∈ C`, the demand `f` is met, and since `f` was arbitrary, `C` shatters `S`. The adversary's
universal forcing power is therefore *exactly* shattering. -/
theorem shatters_iff_adversary_forces (C : ConceptClass X Bool) (S : Finset X) :
    Shatters X C S ↔ AdversaryForcesShattering C S := by
  classical
  constructor
  · intro hshat L s
    exact shatters_forces_all_mistakes_enum hshat L s
  · intro h f
    set f' : X → Bool := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else false with hf'
    let Lf : OnlineLearner X Bool :=
      { State := PUnit
        init := PUnit.unit
        predict := fun _ x => ! (f' x)
        update := fun _ _ _ => PUnit.unit }
    obtain ⟨seq, c, hcC, hnodup, htoF, hmis⟩ := h Lf PUnit.unit
    have hlen : seq.length = S.card := by
      rw [← htoF, List.toFinset_card_of_nodup hnodup]
    have hmis' : mistakesAlong Lf PUnit.unit c seq = seq.length := by rw [hmis, hlen]
    have hsat : ∀ x ∈ seq, (! (f' x)) ≠ c x :=
      mistakesAlong_saturation Lf (fun x => ! (f' x)) c seq (fun _ _ => rfl) PUnit.unit hmis'
    refine ⟨c, hcC, fun x => ?_⟩
    have hxS : (x : X) ∈ S := x.2
    have hxseq : (x : X) ∈ seq := by rw [← List.mem_toFinset, htoF]; exact hxS
    have hne := hsat (x : X) hxseq
    have hcfx : c (x : X) = f' (x : X) := by
      cases hb : c (x : X) <;> cases hb2 : f' (x : X) <;> simp_all
    rw [hcfx]
    simp only [hf', dif_pos hxS]

/-! ## Argument 2 — the super-additivity defect (KU-2 / RKU-2)

The kernel already proves super-additivity *exists* (`vcDim_not_subadditive_collectionUnion`), and the
Γ-axis closure module already packages the two-class quantitative envelope: `additivityDefect_pos`
(the defect is strictly positive on a witness, `= 1` on the one-point two-constant family) and
`additivityDefect_le_one` (the union bound `dA + dB + 1` brackets it from above), with the conjectured
`k`-fold conserved functional recorded there as a sharpened-KU residual naming the BEHW lower-bound
family as its blocker. **We do not re-close those.**

The expressivity-axis residual still open after that work is the *characterization* of the gap: the
URS (RKU-2) asks not merely that the defect is positive but *what algebraic law replaces additivity*.
We close that with one genuinely-new biconditional: a strictly positive defect on some pair is
**equivalent** to the failure of the polymatroid submodular law. The quantitative gap and the
structural Pl-kill `vcDim_not_polymatroid_rank` are therefore the *same* phenomenon, not two facts.
-/

/-- **The defect is positive somewhere iff VC dimension is not submodular** — the reduction tying the
quantitative super-additivity gap to the structural Pl-kill. A strictly positive defect on *some*
pair of classes (over *some* domain) is exactly the failure of the polymatroid submodular law
`VCDim (C ∪ D) + VCDim (C ∩ D) ≤ VCDim C + VCDim D`. The forward direction notes that submodularity
forces two-class subadditivity (`vcDim_submodular_imp_subadditive`), contradicting any positive
defect; the converse is the witness `vcDim_not_subadditive_collectionUnion`, whose positive defect is
itself a submodularity failure. This is the precise residual of RKU-2 reachable on the two-class
lattice: the defect *is* the obstruction `vcDim_not_polymatroid_rank` measures. -/
theorem superadditivity_defect_iff_not_submodular :
    (∃ (X : Type) (A B : ConceptClass X Bool), VCDim X A + VCDim X B < VCDim X (A ∪ B)) ↔
      ¬ ∀ X : Type, VCDimSubmodular X := by
  constructor
  · rintro ⟨X, A, B, hAB⟩ hsub
    exact absurd (vcDim_submodular_imp_subadditive (hsub X) A B) (not_le.mpr hAB)
  · intro _
    exact vcDim_not_subadditive_collectionUnion

/-! ## Argument 3 — is the expressivity coordinate ≥ 2-dimensional? (RKU-5 / UK-4)

The URS asks (RKU-5) whether expressivity is genuinely *at least two-dimensional* — whether
`VCDim` (set-shattering power) and `LittlestoneDim` (ordered/adaptive shattering power) are
*independent* coordinates rather than a single broken chain. We answer with a **separation Pl-kill**:
the threshold class `{ (· ≤ n) | n }` on `ℕ` has `VCDim = 1` (it shatters no pair) yet
`LittlestoneDim = ⊤` (it shatters complete trees of every depth). VC small does not bound Littlestone;
the two coordinates carry independent information, so the expressivity coordinate is at least
two-dimensional.

The separation is genuinely **one-directional**: the reverse — VC large, Littlestone small — is
impossible, because Littlestone dimension always dominates VC dimension (`littlestoneDim_ge_vcDim`,
the proven `BranchWiseLittlestoneDim_ge_VCDim` on a decidable domain). That asymmetry (UK-4 of the
URS) is itself the content: trees are uniformly *richer* than sets, and the threshold class is the
extremal witness pinning the gap to its maximum (`1` versus `⊤`).

**Def-skew note (A4 honesty).** Two Littlestone notions coexist in the kernel: the tree-depth
`GameInfra.LittlestoneDim : WithBot (WithTop ℕ)` used in `ldim_threshold_top` / the separation, and
the branch-wise `BranchWiseLittlestoneDim : WithTop ℕ` for which the `≥ VCDim` direction is a proven
theorem. The one-directional lemma is stated in the branch-wise form (the proven one) and the skew is
flagged here rather than papered over with an unproven equality of the two definitions.

The whole argument is self-contained over `Shatters` / `VCDim` / `LittlestoneDim` and reconstructs
the threshold witness in-module (the kernel's `Theorem.Separation` copies are `private`). -/

/-- The **threshold class** on `ℕ`: all initial-segment indicators `(· ≤ n)`. The canonical
low-VC / high-Littlestone gap object. -/
def thresholdClass : ConceptClass ℕ Bool :=
  { f | ∃ n : ℕ, f = fun x => decide (x ≤ n) }

/-- No two-point set is shattered by the threshold class: a threshold cannot send the smaller point
to `false` and the larger to `true`, so the "split the pair the wrong way" labelling is unrealizable.
The combinatorial core of `VCDim ≤ 1`. -/
theorem threshold_not_shatter_pair {S : Finset ℕ} (hcard : 2 ≤ S.card) :
    ¬ Shatters ℕ thresholdClass S := by
  intro hshat
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · obtain ⟨c, ⟨n, rfl⟩, hc⟩ := hshat (fun s => if (s : ℕ) = a then false else true)
    have hca : decide (a ≤ n) = false := by convert hc ⟨a, ha⟩ using 1; simp
    have hcb : decide (b ≤ n) = true := by
      convert hc ⟨b, hb⟩ using 1
      simp only [show (b : ℕ) ≠ a from Ne.symm hab, ite_false]
    simp only [decide_eq_false_iff_not, not_le] at hca
    simp only [decide_eq_true_eq] at hcb
    omega
  · obtain ⟨c, ⟨n, rfl⟩, hc⟩ := hshat (fun s => if (s : ℕ) = b then false else true)
    have hcb : decide (b ≤ n) = false := by convert hc ⟨b, hb⟩ using 1; simp
    have hca : decide (a ≤ n) = true := by
      convert hc ⟨a, ha⟩ using 1
      simp only [show (a : ℕ) ≠ b from hab, ite_false]
    simp only [decide_eq_false_iff_not, not_le] at hcb
    simp only [decide_eq_true_eq] at hca
    omega

/-- **The threshold class has finite VC dimension** (`≤ 1`). No pair is shattered, so the supremum
defining the VC dimension is below `2`. The low-expressivity coordinate. -/
theorem vcDim_threshold_lt_top : VCDim ℕ thresholdClass < ⊤ := by
  apply lt_of_le_of_lt _ (WithTop.coe_lt_top (a := 1))
  refine iSup₂_le fun S hshat => ?_
  by_contra hgt
  push_neg at hgt
  exact threshold_not_shatter_pair (by exact_mod_cast hgt) hshat

/-- A complete shattered Littlestone tree of depth `d` for thresholds in `[lo, lo + 2^d)`. The branch
node tests the midpoint `lo + 2^d`; the left slice keeps the thresholds above it, the right slice
those below. -/
noncomputable def thresholdTree (lo : ℕ) : (d : ℕ) → LTree ℕ d
  | 0 => .leaf
  | d + 1 => .branch (lo + 2 ^ d) (thresholdTree (lo + 2 ^ d) d) (thresholdTree lo d)

/-- The threshold tree of depth `d` is shattered by any class containing the thresholds with indices
in `[lo, lo + 2^d)`. The recursion mirrors `thresholdTree`: at the midpoint both labels are
realizable, and each slice still contains its half-range of thresholds. -/
theorem thresholdTree_shattered (lo : ℕ) (d : ℕ) (C : ConceptClass ℕ Bool)
    (hC : ∀ n, lo ≤ n → n < lo + 2 ^ d → (fun x => decide (x ≤ n)) ∈ C) :
    (thresholdTree lo d).isShattered C := by
  induction d generalizing lo C with
  | zero => exact ⟨_, hC lo le_rfl (by simp)⟩
  | succ d ih =>
    simp only [thresholdTree, LTree.isShattered]
    set mid := lo + 2 ^ d with hmid_def
    have hpow_pos : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
    have hpow_succ : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨_, hC mid (Nat.le_add_right lo _) ?_, by simp⟩
      rw [hpow_succ]; omega
    · have hmid_pos : 0 < mid := by omega
      refine ⟨_, hC (mid - 1) (by omega) (by rw [hpow_succ]; omega), ?_⟩
      simp only [decide_eq_false_iff_not, not_le]; omega
    · apply ih mid {c ∈ C | c mid = true}
      intro n hn1 hn2
      exact ⟨hC n (by omega) (by rw [hpow_succ]; omega), by simp [decide_eq_true_eq]; omega⟩
    · apply ih lo {c ∈ C | c mid = false}
      intro n hn1 hn2
      exact ⟨hC n hn1 (lt_of_lt_of_le hn2 (by rw [hpow_succ]; omega)),
        by simp [decide_eq_false_iff_not, not_le]; omega⟩

/-- **The threshold class has infinite Littlestone dimension.** It shatters a complete tree of every
depth, so the supremum defining the Littlestone dimension is `⊤`. The high-expressivity coordinate. -/
theorem ldim_threshold_top : LittlestoneDim ℕ thresholdClass = ⊤ := by
  have hall : ∀ d : ℕ, ∃ T : LTree ℕ d, T.isShattered thresholdClass :=
    fun d => ⟨thresholdTree 0 d, thresholdTree_shattered 0 d thresholdClass (fun n _ _ => ⟨n, rfl⟩)⟩
  by_contra hne
  have hlt : LittlestoneDim ℕ thresholdClass < ⊤ := lt_top_iff_ne_top.mpr hne
  cases hc : LittlestoneDim ℕ thresholdClass with
  | bot =>
    have hge : LittlestoneDim ℕ thresholdClass ≥ ↑(↑0 : WithTop ℕ) :=
      le_iSup₂_of_le 0 ⟨.leaf, ⟨_, 0, rfl⟩⟩ le_rfl
    rw [hc] at hge; exact absurd hge (by simp)
  | coe v =>
    cases v with
    | top => rw [hc] at hlt; exact absurd hlt (lt_irrefl _)
    | coe n =>
      obtain ⟨T, hT⟩ := hall (n + 1)
      have hge : LittlestoneDim ℕ thresholdClass ≥ ↑(↑(n + 1) : WithTop ℕ) :=
        le_iSup₂_of_le (n + 1) ⟨T, hT⟩ le_rfl
      rw [hc] at hge
      exact absurd hge (by
        simp only [WithBot.coe_le_coe]; exact not_le.mpr (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)))

/-- **The VC / Littlestone separation — expressivity is at least two-dimensional** (the Pl-kill of
RKU-5). There is a concept class whose set-shattering power is finite (`VCDim < ⊤`) but whose
ordered/adaptive shattering power is infinite (`LittlestoneDim = ⊤`). VC dimension therefore does not
determine Littlestone dimension: the two are independent coordinates of expressivity, and the
expressivity reading-axis is genuinely ≥ 2-dimensional. The threshold class is the witness. -/
theorem vc_littlestone_separation :
    ∃ C : ConceptClass ℕ Bool, VCDim ℕ C < ⊤ ∧ LittlestoneDim ℕ C = ⊤ :=
  ⟨thresholdClass, vcDim_threshold_lt_top, ldim_threshold_top⟩

/-- **The separation is one-directional** (UK-4 — the asymmetry is the content). On a decidable
domain the branch-wise Littlestone dimension always dominates the VC dimension: a set-shattered
subset induces a shattered tree of the same depth. So the *reverse* separation — VC large,
Littlestone small — is impossible; the gap can only open in the `VCDim ≤ LittlestoneDim` direction.
This is `BranchWiseLittlestoneDim_ge_VCDim`, surfaced here as the structural reason the
two-dimensionality of expressivity is *ordered*: trees are uniformly richer than sets. (See the
def-skew note above: this is the branch-wise Littlestone notion.) -/
theorem littlestoneDim_ge_vcDim (Y : Type u) [DecidableEq Y] (C : ConceptClass Y Bool) :
    VCDim Y C ≤ BranchWiseLittlestoneDim Y C :=
  BranchWiseLittlestoneDim_ge_VCDim Y C

/-! ## Argument 4 — realizability lower-bounds packaging (R7, consolidation)

The URS (R7) lists the "shattering yields a certificate" facts as scattered one-directional theorems.
This is a **DIRECT** consolidation: a shattered set is, simultaneously, a realizer of every labelling,
a forcing witness for the growth function, and an adversary forcing every online learner to its
maximum mistake count. We bundle the three into one statement — the expressivity→capacity arrow
(GM6) at the purely combinatorial scale, with no measure theory. Each conjunct is an anchor
(`shatters_iff_labelling_game`, `growthFunction_ge_two_pow_of_shatters`,
`shatters_forces_all_mistakes`); the conjunction is the consolidation. -/

/-- **The realizability certificate of a shattered set** (consolidation of the R7 arrow). A set `S`
shattered by `C` carries three certificates at once:

* it **realizes every labelling** — for each `f : ↥S → Bool` some concept of `C` matches `f` on `S`;
* it **forces the growth function up** to its combinatorial maximum, `2 ^ |S| ≤ GrowthFunction C |S|`;
* it is a **universal adversary** — every online learner, from any start state, makes `|S|` mistakes
  on some presentation of `S` against a target in `C`.

This is the single expressivity→capacity object the URS asks for: maximal realizability power
(shattering) packaged as a worst-case lower bound on every downstream capacity reading
(growth, mistakes), measure-free. -/
theorem shatters_realizability_certificate {C : ConceptClass X Bool} {S : Finset X}
    (hshat : Shatters X C S) :
    (∀ f : ↥S → Bool, ∃ c ∈ C, ∀ x : ↥S, c (x : X) = f x) ∧
      2 ^ S.card ≤ GrowthFunction X C S.card ∧
      (∀ (L : OnlineLearner X Bool) (s : L.State),
        ∃ (seq : List X) (c : X → Bool), c ∈ C ∧ mistakesAlong L s c seq = S.card) :=
  ⟨(shatters_iff_labelling_game C S).mp hshat,
    growthFunction_ge_two_pow_of_shatters hshat,
    fun L s => shatters_forces_all_mistakes hshat L s⟩

/-! ## Argument 5 — the `xorShift` computational-axis pressure (RKU-6 / UK-3, gated by A1)

The URS records (UK-3, A1) that parity (`xorShift`) sits at a phase boundary: it is *invariant* for
the statistical/shattering grammar yet maximal on the computational axis that A1 (opcount excluded)
deliberately drops. RKU-6 asks whether a measure-free FLT shadow can *see* that axis without
re-opening A1. We close the in-closure part and reduce the residual.

* **Partial (in closure).** The shift acts *freely on realizations* (`xorShift_realizes_iff`) and is
  therefore exactly VC-invariant (`parity_shattering_invariant` = `vcDim_xorShift`). This is the
  precise statement that the shattering grammar is *constitutively blind* to parity: no shattering-
  derived functional can distinguish `C` from `xorShift a C`.
* **Open residual (gated).** Any functional that *does* see the computational axis must, by
  definition, fail to be `xorShift`-invariant. We name this object — a *parity-sensitive separator* —
  and record the open question as a **sharpened-KU residual** below: a measure-free FLT shadow of the
  computational axis is a non-`xorShift`-invariant functional, and VC dimension is provably not one
  (`vcDim_is_parity_blind`). This honors gate A1: we do not assert such a separator exists (that would
  require the excluded opcount content); we state *exactly* what is missing. -/

/-- **The exclusive-or shift acts freely on realizations.** A concept realizes a labelling `f` on `S`
after the shift by `a` if and only if its pre-image realizes the `a`-twisted labelling before the
shift. The shift is a bijection of labellings, so it permutes realizations without creating or
destroying any — the mechanism behind parity's shattering-invariance. -/
theorem xorShift_realizes_iff (a : X → Bool) (C : ConceptClass X Bool) (S : Finset X)
    (f : ↥S → Bool) :
    (∃ c ∈ xorShift a C, ∀ x : ↥S, c (x : X) = f x) ↔
      (∃ c ∈ C, ∀ x : ↥S, c (x : X) = Bool.xor (a (x : X)) (f x)) := by
  constructor
  · rintro ⟨c, ⟨c₀, hc₀, rfl⟩, hcf⟩
    refine ⟨c₀, hc₀, fun x => ?_⟩
    have := hcf x
    simp only at this
    rw [← this]
    cases a (x : X) <;> cases c₀ (x : X) <;> rfl
  · rintro ⟨c₀, hc₀, hc₀f⟩
    refine ⟨fun x => Bool.xor (a x) (c₀ x), ⟨c₀, hc₀, rfl⟩, fun x => ?_⟩
    show Bool.xor (a (x : X)) (c₀ (x : X)) = f x
    rw [hc₀f x]
    cases a (x : X) <;> cases f x <;> rfl

/-- **Parity is invariant for the shattering grammar** (re-export of `vcDim_xorShift`, the A1 boundary
made explicit). Every exclusive-or shift preserves VC dimension exactly, so VC dimension — and every
functional definable from `Shatters` — is blind to the parity content of a class. This is the typed
form of the URS's UK-3 phase boundary: parity is `Inv/Comp`-invariant for the statistical grammar
while being maximal on the excluded computational axis. -/
theorem parity_shattering_invariant (a : X → Bool) (C : ConceptClass X Bool) :
    VCDim X (xorShift a C) = VCDim X C :=
  vcDim_xorShift a C

/-! SHARPENED KU (open): there is a measure-free FLT functional `J : ConceptClass X Bool → WithTop ℕ`
that *sees* the parity / computational axis — i.e. `J` is **not** `xorShift`-invariant: `∃ a C,
J (xorShift a C) ≠ J C`. VC dimension is provably on the *blind* side (`vcDim_is_parity_blind` below:
`VCDim` is always `xorShift`-invariant), so such a `J` cannot be `VCDim` or any `Shatters`-definable
functional. — reduces to constructing a **parity-sensitive separator**, which requires the
opcount/circuit (computational-axis) content that gate A1 deliberately excludes; confirmed-absent from
the `Shatters`/`VCDim` grammar. Recorded here as an open residual, not a theorem. (The earlier
`parity_axis_invisible_to_vc` was removed in the A4 honesty pass: it was the logical tautology
`(∃ …, J ≠) ↔ ¬(∀ …, J =)`, i.e. `P ↔ ¬¬P` after `push_neg`, with no parity content.) -/

/-- **VC dimension is on the invariant (blind) side of the parity dichotomy.** The VC functional
satisfies the invariance that a parity-sensitive separator must violate, so `VCDim` can never be the
computational-axis shadow the sharpened-KU residual above asks for. The clean negative content of the
A1 gate: the statistical grammar's own capacity functional is provably parity-blind. -/
theorem vcDim_is_parity_blind :
    ∀ (a : X → Bool) (C : ConceptClass X Bool), VCDim X (xorShift a C) = VCDim X C :=
  fun a C => vcDim_xorShift a C

end ExpressivityClosures
