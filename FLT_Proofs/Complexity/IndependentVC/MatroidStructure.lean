/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.OpenRouteR1
import FLT_Proofs.Complexity.IndependentVC.LatticeClosure
import FLT_Proofs.Complexity.IndependentVC.MatroidWitness

/-!
# Is VC dimension a matroid rank? — the verdict

A (poly)matroid rank function `r` on a lattice must be **monotone**, **normalized** (`r ⊥ = 0`),
and **submodular** (`r(C ∪ D) + r(C ∩ D) ≤ r C + r D`). On the lattice of concept classes ordered
by inclusion, with join `∪` and meet `∩`, the VC dimension satisfies the first two axioms outright,
and is even *modular* on chains. This file settles the third: submodularity **fails**, so VC
dimension is **not** a polymatroid rank.

The argument is short and forced. Submodularity, together with normalization (`VCDim ⊥ = 0`, and
more locally `VCDim(C ∩ D) ≥ ⊥`), would imply collection-subadditivity
`VCDim(C ∪ D) ≤ VCDim C + VCDim D` — drop the nonnegative meet term from the left. By Finset
induction this lifts to `VCDim(⋃ i ∈ s, C i) ≤ ∑ i ∈ s, VCDim(C i)`. But the explicit witness
`vcDim_not_subadditive_collectionUnion` already breaks the two-class case: two VC-dimension-zero
singleton classes on a one-point domain union to a class that shatters the point, so `0 + 0 < 1`.
Subadditivity is false, hence submodularity is false. This is a structural **boundary** result, not
a positive one: it tells us what VC dimension is *not*.

What VC dimension *is*, structurally: a monotone, normalized, modular-on-chains invariant whose
union behaviour is governed not by submodularity but by the sharp `VCDim C + VCDim D + 1` two-class
bound (`vcDim_union_le`) and the super-additive `k`-fold growth `Θ(d · k · log k)` (Blumer,
Ehrenfeucht, Haussler, Warmuth, *J. ACM* 36(4):929–965, 1989, Lemma 3.2.3; lower bound Eisenstat,
Angluin, *Inf. Process. Lett.* 101(5):181–184, 2007; tight super-additivity Csíkós, Kupavskii,
Mustafa, *J. Mach. Learn. Res.* 20(81):1–17, 2019). That `k log k` correction is precisely what no
submodular function can carry, since a submodular (hence subadditive) rank forces an `O(d · k)`
ceiling on the `k`-fold union. The rank-compatible surrogate lives one scale down, at VC *density*
(`VCDensity.lean`), which *is* subadditive under Boolean combination. The companion lattice fact —
that the oriented-matroid rank equals the VC dimension of its tope graph (Goodman, Pollack,
*Discrete Comput. Geom.* 5:259–263, 1990) — concerns arrangement-derived classes and is not in
tension with this: that correspondence is about a single oriented matroid, not the collection
lattice of arbitrary concept classes considered here.

## Main results

* `vcDim_rank_monotone`, `vcDim_rank_normalized`, `vcDim_rank_modular_on_chain`: the rank axioms VC
  dimension *does* satisfy (re-surfaced from `vcDim_mono`, `vcDim_empty`, `vcDim_modular_on_chain`).
* `vcDim_submodular_imp_subadditive`: submodularity would force two-class subadditivity.
* `vcDim_submodular_imp_subadditive_biUnion`: …and, by induction, `k`-fold subadditivity.
* `not_vcDimSubmodular`: VC dimension is **not** submodular — it cannot hold on every domain,
  refuted by composing the bridge with the one-point witness `vcDim_not_subadditive_collectionUnion`.
* `vcDim_not_polymatroid_rank`: the verdict — monotone and normalized, but not a polymatroid rank.
-/

open Set

universe u v

variable {X : Type u}

/-! ## The rank axioms VC dimension satisfies

Two of the three (poly)matroid-rank axioms hold for VC dimension on the concept-class lattice, plus
the strengthening to modularity on chains. We restate them here under rank-oriented names so the
positive side of the verdict sits beside the negative side; the proofs are the existing lemmas. -/

/-- **Rank axiom 1 (monotonicity), satisfied.** Enlarging the concept class can only enlarge the VC
dimension. This is `vcDim_mono`, restated as the monotonicity axiom of a rank function. -/
theorem vcDim_rank_monotone {C D : ConceptClass X Bool} (h : C ⊆ D) :
    VCDim X C ≤ VCDim X D :=
  vcDim_mono h

/-- **Rank axiom 2 (normalization), satisfied.** The bottom of the lattice — the empty concept class
— has VC dimension `⊥ = 0`: it shatters nothing, not even the empty sample. -/
theorem vcDim_rank_normalized : VCDim X (∅ : ConceptClass X Bool) = ⊥ := by
  refine iSup₂_eq_bot.mpr (fun S hShat => ?_)
  obtain ⟨c, hc, -⟩ := hShat (fun _ => false)
  exact ((Set.mem_empty_iff_false c).mp hc).elim

/-- **Rank axiom 3 (submodularity) holds *only* on chains — with equality.** If `C ⊆ D` the meet and
join collapse (`C ∩ D = C`, `C ∪ D = D`), so the submodular inequality is an equality: on a chain VC
dimension is genuinely *modular*. This is `vcDim_modular_on_chain`, restated. Off chains the equality
breaks and, as `not_vcDimSubmodular` shows, even the inequality fails. -/
theorem vcDim_rank_modular_on_chain {C D : ConceptClass X Bool} (h : C ⊆ D) :
    VCDim X (C ∪ D) + VCDim X (C ∩ D) = VCDim X C + VCDim X D :=
  vcDim_modular_on_chain h

/-! ## The bridge: submodularity forces subadditivity

A submodular rank, once normalized, is subadditive — the meet term on the left of the submodular
inequality is nonnegative and can only be dropped. We make this implication explicit, first for two
classes and then, by Finset induction, for an arbitrary finite family. This is the lever that turns
the explicit subadditivity counterexample into a refutation of submodularity. -/

/-- **Submodularity implies two-class subadditivity.** From `VCDimSubmodular X` we get
`VCDim(C ∪ D) ≤ VCDim C + VCDim D` for all `C, D`. The meet term `VCDim(C ∩ D)` is nonnegative
(everything in `WithTop ℕ` dominates `⊥`), so dropping it from the left of the submodular inequality
only weakens it. -/
theorem vcDim_submodular_imp_subadditive (h : VCDimSubmodular X) (C D : ConceptClass X Bool) :
    VCDim X (C ∪ D) ≤ VCDim X C + VCDim X D :=
  -- `VCDim(C∪D) ≤ VCDim(C∪D) + VCDim(C∩D) ≤ VCDim C + VCDim D`
  le_trans (self_le_add_right _ _) (h C D)

/-- **Submodularity implies `k`-fold subadditivity.** Lifting `vcDim_submodular_imp_subadditive` by
induction over a `Finset`: a submodular VC dimension would satisfy
`VCDim(⋃ i ∈ s, C i) ≤ ∑ i ∈ s, VCDim(C i)`. The empty case is normalization
(`VCDim ∅ = ⊥ ≤ 0`); the insertion step peels off one class with the two-class bound and adds the
inductive bound on the rest. This is the form a polymatroid rank must obey, and the form the witness
`vcDim_not_subadditive_collectionUnion` violates already at `s` of size two. -/
theorem vcDim_submodular_imp_subadditive_biUnion (h : VCDimSubmodular X) {ι : Type v}
    (s : Finset ι) (C : ι → ConceptClass X Bool) :
    VCDim X (⋃ i ∈ s, C i) ≤ ∑ i ∈ s, VCDim X (C i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [vcDim_rank_normalized]
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      exact le_trans (vcDim_submodular_imp_subadditive h _ _) (add_le_add le_rfl ih)

/-! ## The verdict: VC dimension is not submodular

Composing the bridge with the explicit witness. Submodularity on the witness domain would force
two-class subadditivity everywhere on that domain, but the witness exhibits two classes whose union
strictly exceeds the sum of their dimensions. Contradiction. -/

/-- **VC dimension is not submodular** — the core negative content (a Pl-kill). Submodularity on a
domain forces two-class subadditivity there (`vcDim_submodular_imp_subadditive`); yet
`vcDim_not_subadditive_collectionUnion` exhibits a domain — a single point carrying the two constant
concepts `{fun _ => false}`, `{fun _ => true}`, each of VC dimension `0`, whose union shatters the
point — on which `0 + 0 < 1`. Composing the bridge with that witness refutes submodularity holding on
every domain, so no rank surrogate built from `(∪, ∩)` and `+` is submodular on the concept-class
lattice.

The failure is elementary (one point, two constants), not an asymptotic artifact; the
`Θ(d · k · log k)` super-additivity (BEHW 1989; Eisenstat–Angluin 2007; Csíkós–Kupavskii–Mustafa
2019) measures *how far* submodularity fails, not *that* it fails. -/
theorem not_vcDimSubmodular : ¬ ∀ X : Type, VCDimSubmodular X := by
  intro h
  obtain ⟨X, A, B, hAB⟩ := vcDim_not_subadditive_collectionUnion
  exact absurd (vcDim_submodular_imp_subadditive (h X) A B) (not_le.mpr hAB)

/-- **VC dimension is not a polymatroid rank function.** The verdict for open route R1, packaged as a
single statement: VC dimension is monotone and normalized (the first two rank axioms), yet there is a
domain on which it is **not** submodular. A polymatroid rank must be all three at once, so VC
dimension is not a polymatroid rank on the `(∪, ∩)`-lattice of concept classes.

This is a sharp structural boundary. The clean part of the picture is real — monotone, normalized,
modular on chains (`vcDim_rank_modular_on_chain`) — but the rank structure stops at the chain: the
submodular gluing that would make VC dimension a matroid rank is exactly what the union counting
forbids. The invariant that *does* glue submodularly is VC density, one scale below dimension. -/
theorem vcDim_not_polymatroid_rank :
    (∀ {X : Type u} {C D : ConceptClass X Bool}, C ⊆ D → VCDim X C ≤ VCDim X D)
      ∧ (∀ {X : Type u}, VCDim X (∅ : ConceptClass X Bool) = ⊥)
      ∧ ¬ ∀ X : Type, VCDimSubmodular X :=
  ⟨fun h => vcDim_rank_monotone h, vcDim_rank_normalized, not_vcDimSubmodular⟩
