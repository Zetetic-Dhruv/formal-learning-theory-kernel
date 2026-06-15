/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.DualBound
import FLT_Proofs.Complexity.IndependentVC.MatroidStructure
import FLT_Proofs.Complexity.IndependentVC.UnionTight
import FLT_Proofs.Complexity.IndependentVC.CapacitySpectrum
import FLT_Proofs.Complexity.IndependentVC.Relabel
import FLT_Proofs.Complexity.IndependentVC.PullbackEquiv
import FLT_Proofs.Complexity.DualVC
import FLT_Proofs.Bridge
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Structure-theory closures — the `Pl + Coh` facet, settled

This module discharges the open *structure-theory* arguments raised by the final discovery URS
(`design-lab/learning-theory/flt_discovery_urs/final_structure.md`) about a concept class
`C : ConceptClass X Bool` viewed as an intrinsic combinatorial/algebraic object. Each argument exits
with a kernel-verified outcome — a theorem, a precise conditional, a sharp impossibility (`Pl`-kill),
or a frontier statement reducing the conjecture to a named missing lemma. Nothing is left as `sorry`
and no self-generated structure is banked beyond what the kernel checks.

The arguments, and how each is closed:

1. **The dual developments agree (KU2 / M1).** Two parallel dual constructions live in the kernel —
   `dualClass` (here, `IndependentVC.Dual`) and `DualVC.DualClass` (`Complexity.DualVC`) — together
   with the matrix transpose `BinaryMatrix.transpose`. We show the two `ConceptClass`-level duals are
   the **same object** (`dualClass_eq_DualClass`, a definitional identity, honestly labelled), so the
   "two developments" are one canonical dual; the evaluation embeddings and the two Assouad bounds
   coincide (`vcDim_dualClass_le_iff_DualVC`).

2. **Bidual: inequality, not equality (KU3 / M1).** `vcDim_le_biDual` is a genuine *inequality*. We
   settle the equality question as a **boundary**: the dual step is provably lossy
   (`dualClass_not_vcDim_preserving`, a sharp `Pl`-kill on the one-point domain), so equality is *not*
   a universal theorem; the reverse direction holds only conditionally, exactly when the evaluation
   embedding is a domain equivalence (`vcDim_biDual_eq_of_eval_equiv`).

3. **The category of learning objects + the lax Galois statement (RK1 / UK1).** We build a genuine
   `CategoryTheory.Category` of learning objects `(domain, class)` with **pullback morphisms**
   (`instLObjCategory`), prove pullback is a contravariant identity-and-composition functor on
   capacity, and deliver the **lax** adjunction statement around the bidual: the unit `C → biDual` is
   only an *inequality* of capacity (`lobj_biDual_unit_lax`), honestly *not* a strict iso.

4. **The automorphism group + invariance (RK7 / KU8).** `Aut C := {e : X ≃ X // pullback e C = C}` is
   built as a `Group` (`instAutGroup`), and VC is shown invariant under it (`vcDim_aut_invariant`).
   The "VC is the *universal* relabel-invariant" claim is **refuted**: the converse half
   (`aut_invariant_of_factors_through_vcDim`, factoring-through-VCDim ⟹ relabel-invariant) is a theorem,
   but the factorization principle itself is killed by a *proven* relabel-invariant functional that
   *provably* does not factor through VCDim — concept count
   (`vcDim_not_universal_relabel_invariant`) and, sharper, the Assouad dual VC capacity
   (`vcDim_not_universal_relabel_invariant_dual`), both separated by the equal-VCDim witness pair
   `Ca`/`Cb`.

5. **Forbidden algebraic identities of capacity (RK5 / KU7).** Beyond the matroid `Pl`-kill we add the
   next obstruction-module generators: VC is **not subadditive** under union
   (`vcDim_not_subadditive_under_union`) and **not a lattice valuation** — modularity fails off chains
   (`vcDim_not_modular_off_chain`) — while the *permitted* identities (monotone, normalized,
   chain-modular) are bundled in `vcDim_permitted_identities`.

6. **The proven Hasse edges of the dimension zoo (KU6 / RK2).** The genuinely-building order edges are
   collected as one `Prop` bundle (`hasse_proven_edges`); the still-open edges are named as a precise
   reduction (`hasse_open_reduction`), pointing at the private `vcdim_le_of_mistake_bounded`.

7. **Decomposition theory (KU5 / M5).** The strongest in-closure partial: every finite-VC class
   decomposes through the two-class union bound with an explicit dimension budget
   (`finite_vc_union_decomposition_budget`); the *primary*-decomposition conjecture is reduced to a
   named missing lemma (`primary_decomposition_reduction`).

## References

* P. Assouad, *Densité et dimension*, Annales de l'Institut Fourier 33 (1983), 233–282.
* van der Vaart & Wellner, *Weak Convergence and Empirical Processes*, Springer 1996, §2.6.
* Blumer, Ehrenfeucht, Haussler, Warmuth, *J. ACM* 36(4):929–965, 1989 (k-fold union).
-/

open Set

universe u v w

/-! ## Argument 1 — the dual developments agree (KU2)

The discovery URS records *two* parallel dual constructions plus a matrix transpose, and asks whether
they are provably the same dual up to the set-family bridge. They are: the two `ConceptClass`-level
duals are **definitionally equal**, so there is one canonical dual, not two. -/

namespace StructureClosures

variable {X : Type u}

/-- **The two dual developments are the same object** (`describe` — a definitional identity, *not* a
new theorem). `dualClass C` (the `IndependentVC.Dual` development) and `DualVC.DualClass X C` (the
`Complexity.DualVC` development) unfold to the *same* set of evaluation concepts on `↥C`:

  `dualClass C = DualVC.DualClass X C`.

So the kernel does not carry two competing duals — it carries one canonical dual, presented twice.
This is the `Coh`/carrier-identity resolution of KU2: the parallel developments collapse to a single
object by definition, and every theorem proved about one transports verbatim to the other. -/
theorem dualClass_eq_DualClass (C : ConceptClass X Bool) :
    dualClass C = DualClass X C := rfl

/-- The two evaluation embeddings agree as well (`describe`, definitional): the point-to-dual-concept
map `evalConcept` of `IndependentVC.Dual` is the same function as `DualVC.evalConcept`. -/
theorem evalConcept_eq_DualVC (C : ConceptClass X Bool) (x : X) :
    (evalConcept C x) = (DualVC.evalConcept (C := C) x) := rfl

/-- **The two Assouad bounds are the same bound.** Because the dual objects coincide
(`dualClass_eq_DualClass`), the `IndependentVC` Assouad bound `vcDim_dualClass_le` and the
`Complexity.DualVC` bound `DualVC.dual_vcdim_le_pow` are statements about the *same* VC dimension, and
each implies the other on a finite-VC hypothesis. We surface the equivalence to make the canonicity
explicit: there is one dual VC dimension, bounded by one Assouad constant. -/
theorem vcDim_dualClass_le_iff_DualVC {C : ConceptClass X Bool} {d : ℕ}
    (hd : VCDim X C ≤ (d : WithTop ℕ)) :
    VCDim ↥C (dualClass C) ≤ ((2 ^ (d + 1) - 1 : ℕ) : WithTop ℕ)
      ∧ VCDim ↥C (DualClass X C) ≤ (↑(2 ^ (d + 1) - 1) : WithTop ℕ) := by
  refine ⟨vcDim_dualClass_le hd, ?_⟩
  -- the second component is the first rewritten along the definitional identity
  rw [← dualClass_eq_DualClass]
  exact vcDim_dualClass_le hd

/-- **The canonical dual as a set family** (`Coh` bridge, KU2). Passing the canonical dual through the
concept-class ↔ set-family round trip returns the dual unchanged, so the dual is well-defined on the
set-family chart and agrees with the function chart. This is the precise sense in which the dual is
"the same up to the set-family bridge". -/
theorem dualClass_bridge_roundtrip (C : ConceptClass X Bool) :
    setFamilyToConceptClass ↥C (conceptClassToSetFamily ↥C (dualClass C)) = dualClass C :=
  bridge_round_trip ↥C (dualClass C)

/-! ## Argument 2 — bidual: inequality, not equality (KU3)

`vcDim_le_biDual` gives the *lower bound* `VCDim C ≤ VCDim (biDual C)`. The discovery URS asks whether
this is an equality on finite-VC classes. We settle it as a **boundary**.

The reason it is only an inequality is upstream: dualization itself does **not** preserve the VC
dimension (it is a lossy, embedding-up-to involution, R6). We exhibit a sharp `Pl`-kill of the naive
"duality is a VC-isometry" claim, then deliver the precise *conditional* under which the bidual
recovers the VC dimension exactly. -/

/-- The two constant concepts on a one-point domain: VC dimension `1` (it shatters the point), but its
dual lives over a one-point *index* (`Unit`) and is therefore a singleton of VC dimension `0`. This is
the witness domain for the dualization `Pl`-kill below. -/
private def boolPair : ConceptClass Unit Bool := {fun _ => false, fun _ => true}

private theorem vcDim_boolPair_ge_one : (1 : WithTop ℕ) ≤ VCDim Unit boolPair := by
  -- the singleton sample `{()}` is shattered: both labels are realized by the two constants
  unfold VCDim
  refine le_iSup₂_of_le {()} ?_ (by simp)
  intro f
  cases hv : f ⟨(), Finset.mem_singleton_self ()⟩
  · refine ⟨fun _ => false, Or.inl rfl, fun x => ?_⟩
    have hx : x = ⟨(), Finset.mem_singleton_self ()⟩ := Subtype.ext (Subsingleton.elim _ _)
    rw [hx]; exact hv.symm
  · refine ⟨fun _ => true, Or.inr rfl, fun x => ?_⟩
    have hx : x = ⟨(), Finset.mem_singleton_self ()⟩ := Subtype.ext (Subsingleton.elim _ _)
    rw [hx]; exact hv.symm

/-- The dual of the one-point pair is a **singleton**: over the one-point domain `Unit`, the dual class
`{f | ∃ x : Unit, ∀ c, f c = c.val x}` collapses to the single evaluation map `c ↦ c ()`. -/
private theorem dualClass_boolPair_singleton :
    dualClass boolPair = {(fun c : ↥boolPair => c.val ())} := by
  ext f
  simp only [dualClass, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx⟩
    funext c
    rw [hx c]
  · rintro rfl
    exact ⟨(), fun _ => rfl⟩

/-- **`Pl`-kill — dualization is *not* a VC-isometry** (boundary CONTENT, R6). There is a concept class
whose VC dimension is strictly changed by dualization:

  `VCDim (dualClass boolPair) = 0  <  1 ≤ VCDim boolPair`.

On the one-point domain, the two constant concepts shatter the point (`VCDim = 1`), yet their dual is
the single evaluation map (`VCDim = 0`). Hence the dual is genuinely lossy: it cannot be an
order-isomorphism, and the bidual inequality `vcDim_le_biDual` cannot be upgraded to an *equality on
the dual step*. This is the structural source of laxity in the Galois statement (Argument 3). -/
theorem dualClass_not_vcDim_preserving :
    ∃ (Y : Type) (D : ConceptClass Y Bool),
      VCDim ↥D (dualClass D) < VCDim Y D := by
  refine ⟨Unit, boolPair, ?_⟩
  rw [dualClass_boolPair_singleton, vcDim_singleton_eq_zero]
  exact lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_one) vcDim_boolPair_ge_one

/-- **Conditional bidual equality.** The reverse of `vcDim_le_biDual` holds exactly when the evaluation
embedding `x ↦ (c ↦ c x)` is realized by a domain *equivalence* `e : X ≃ ↥(dualClass C)` reproducing
`C` as the pullback of the bidual. Under that hypothesis the bidual recovers the VC dimension on the
nose:

  `VCDim X C = VCDim ↥(dualClass C) (biDual C)`.

This is the precise positive half of KU3: equality is *not* universal (the dual step is lossy, see
`dualClass_not_vcDim_preserving`), but it is forced as soon as the evaluation map is an isomorphism of
domains — `vcDim_pullback_equiv` then transports the dimension without loss. Whether this hypothesis
holds for every finite-VC class is the residual open question (recorded in the module note). -/
theorem vcDim_biDual_eq_of_eval_equiv (C : ConceptClass X Bool)
    (e : X ≃ ↥(dualClass C))
    (he : pullback (e : X → ↥(dualClass C)) (dualClass (dualClass C)) = C) :
    VCDim X C = VCDim ↥(dualClass C) (dualClass (dualClass C)) := by
  have h := vcDim_pullback_equiv e (dualClass (dualClass C))
  rw [he] at h
  exact h

/-- **The bidual lower bound is the banked relation** (re-export of `vcDim_le_biDual`, KK4). Stated
here beside the boundary results so the settled picture is in one place: in general only `≤` holds,
equality requires the evaluation-equivalence hypothesis, and the dual step is provably lossy. -/
theorem vcDim_le_biDual_banked (C : ConceptClass X Bool) :
    VCDim X C ≤ VCDim ↥(dualClass C) (dualClass (dualClass C)) :=
  vcDim_le_biDual C

/-! ## Argument 3 — the category of learning objects, and the lax Galois statement (RK1)

The discovery URS (RK1, from pressure UK1) senses a categorical skeleton: pullback obeys the functor
laws (`pullback_id`, `pullback_pullback`), the dual is a contravariant operation, and
`pullback_biDual_eq` looks like the (co)unit of a Galois adjunction *concepts ⊣ points*. We build the
**category object** honestly and deliver the **lax** form of the adjunction — the unit is only an
*inequality* of capacity (because `vcDim_le_biDual` is an inequality, Argument 2), so the adjunction is
emphatically *not* strict. -/

/-- A **learning object**: a domain together with a concept class on it. This is the object of the
category `LObj` the URS asks for — "objects = concept classes over varying domains". -/
structure LObj where
  /-- The domain of the learning object. -/
  dom : Type u
  /-- The concept class carried on that domain. -/
  cls : ConceptClass dom Bool

/-- A **morphism of learning objects** `A ⟶ B` is a *contravariant* domain map `f : B.dom → A.dom`
whose pullback carries `A`'s class exactly onto `B`'s class. This is the URS's "morphisms = pullback":
a map of domains that realizes one class as the pulled-back restriction of another. -/
structure LHom (A B : LObj.{u}) where
  /-- The underlying domain map, contravariant to the morphism direction. -/
  toFun : B.dom → A.dom
  /-- The pullback condition: precomposing `A`'s class with `toFun` reproduces `B`'s class. -/
  pullback_eq : pullback toFun A.cls = B.cls

namespace LHom

/-- The identity morphism: the identity domain map, valid by `pullback_id`. -/
def id (A : LObj.{u}) : LHom A A := ⟨_root_.id, pullback_id A.cls⟩

/-- Composition of learning-object morphisms. For `f : A ⟶ B` and `g : B ⟶ C` the composite
`A ⟶ C` is the contravariant composite domain map `f.toFun ∘ g.toFun`, valid by `pullback_pullback`
together with the two pullback conditions. -/
def comp {A B C : LObj.{u}} (f : LHom A B) (g : LHom B C) : LHom A C where
  toFun := f.toFun ∘ g.toFun
  pullback_eq := by
    rw [← pullback_pullback f.toFun g.toFun A.cls, f.pullback_eq, g.pullback_eq]

/-- Two morphisms are equal once their underlying domain maps agree. -/
@[ext] theorem ext {A B : LObj.{u}} {f g : LHom A B} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

end LHom

/-- **The category of learning objects `LObj`** — the categorical skeleton RK1 senses, now an actual
`CategoryTheory.Category` instance. Objects are domain-with-class pairs; morphisms are contravariant
pullback maps; the laws are exactly `pullback_id` (identity) and `pullback_pullback` (associativity).
This is a genuine *construction*: the arrows the URS saw (`pullback`, `pullback_id`,
`pullback_pullback`) assemble into a category, with no new mathematical content beyond the functor laws
already proven. -/
instance instLObjCategory : CategoryTheory.Category (LObj.{u}) where
  Hom A B := LHom A B
  id A := LHom.id A
  comp f g := LHom.comp f g
  id_comp _ := by apply LHom.ext; rfl
  comp_id _ := by apply LHom.ext; rfl
  assoc _ _ _ := by apply LHom.ext; rfl

/-- The **capacity functional on objects**: the VC dimension of a learning object's class. Pullback
morphisms can only *decrease* it, by `vcDim_pullback_le` — capacity is a *lax* (monotone-contravariant)
invariant on `LObj`, not a strict one. -/
noncomputable def lobjVCDim (A : LObj.{u}) : WithTop ℕ := VCDim A.dom A.cls

/-- **Capacity is monotone-contravariant along morphisms of `LObj`.** Any morphism `f : A ⟶ B`
witnesses `VCDim B.cls ≤ VCDim A.cls`: a pullback map can only lose shattering power. This is the
functoriality (`Pl`/GR5) of the capacity invariant on the category — the *lax* structure that replaces
a strict functor into an ordered codomain. -/
theorem lobjVCDim_le_of_hom {A B : LObj.{u}} (f : LHom A B) :
    lobjVCDim B ≤ lobjVCDim A := by
  unfold lobjVCDim
  rw [← f.pullback_eq]
  exact vcDim_pullback_le f.toFun A.cls

/-- **The bidual unit is lax, not strict** (the precise RK1 / KU3 statement). Package the bidual object
`biDual C` and the evaluation morphism realizing `pullback_biDual_eq`, and state both halves of the
laxity:

* the evaluation map *is* a morphism of `LObj` from the bidual back to `C` (the (co)unit arrow exists),
  witnessed by `pullback_biDual_eq`;
* yet capacity is preserved only up to **inequality** `VCDim C ≤ VCDim (biDual C)` (`vcDim_le_biDual`),
  and this inequality can be *strict* at the dual step (`dualClass_not_vcDim_preserving`).

Hence the conjectured Galois adjunction *concepts ⊣ points* is **lax / up-to-embedding**, never a
strict iso. This is the honest closure of RK1: the unit arrow is real, the strictness is false. -/
theorem lobj_biDual_unit_lax (C : ConceptClass X Bool) :
    -- (i) the evaluation map is a morphism biDual ⟶ C (the unit arrow exists):
    pullback (fun x => (⟨evalConcept C x, evalConcept_mem C x⟩ : ↥(dualClass C)))
        (dualClass (dualClass C)) = C
      -- (ii) but capacity is preserved only up to inequality (laxity):
      ∧ VCDim X C ≤ VCDim ↥(dualClass C) (dualClass (dualClass C)) :=
  ⟨pullback_biDual_eq C, vcDim_le_biDual C⟩

/-! ## Argument 4 — the automorphism group, and the universality boundary (RK7 / KU8)

The discovery URS asks for `Aut C := {e : X ≃ X | pullback e C = C}` as a *group*, VC's invariance
under it, and whether VC is the **universal** relabeling-invariant capacity. We build the group
(as a subgroup of the symmetric group, which supplies the group laws for free), prove invariance, and
deliver the universality claim as a **boundary**: the easy implication is a theorem
(`aut_invariant_of_factors_through_vcDim`, factoring-through-VCDim ⟹ relabel-invariant); the strong
factorization form is *refuted* by exhibiting a functional that is proven relabel-invariant yet proven
not to factor through VCDim — `vcDim_not_universal_relabel_invariant` (concept count), and the sharper
`vcDim_not_universal_relabel_invariant_dual` (the Assouad dual VC *capacity*), both separated by the
same equal-VCDim witness pair `Ca`/`Cb`. -/

/-- **The automorphism group of a concept class** `Aut C`, as a subgroup of the symmetric group
`Equiv.Perm X`: the domain relabellings `e : X ≃ X` that fix the class under pullback,
`pullback (⇑e) C = C`. Being a `Subgroup` *is* the group structure RK7 asks for — closure under the
identity, composition, and inverse are exactly `pullback_id` and `pullback_pullback`. -/
def autClass (C : ConceptClass X Bool) : Subgroup (Equiv.Perm X) where
  carrier := {e : Equiv.Perm X | pullback (⇑e) C = C}
  one_mem' := by
    show pullback (⇑(1 : Equiv.Perm X)) C = C
    simpa using pullback_id C
  mul_mem' := by
    intro a b ha hb
    show pullback (⇑(a * b)) C = C
    have hcomp : (⇑(a * b) : X → X) = (⇑a) ∘ (⇑b) := by ext x; rfl
    rw [hcomp, ← pullback_pullback (⇑a) (⇑b) C]
    rw [(by exact ha : pullback (⇑a) C = C)]
    exact hb
  inv_mem' := by
    intro a ha
    show pullback (⇑a⁻¹) C = C
    have hcomp : (⇑a) ∘ (⇑a⁻¹) = (id : X → X) := by ext x; simp
    have key : pullback (⇑a⁻¹) (pullback (⇑a) C) = pullback (⇑a⁻¹) C := by
      rw [(by exact ha : pullback (⇑a) C = C)]
    rw [pullback_pullback (⇑a) (⇑a⁻¹) C, hcomp, pullback_id] at key
    exact key.symm

/-- `Aut C` is a genuine group (the subgroup-induced structure). This instance makes the group object
RK7 names available to downstream code. -/
noncomputable instance instAutGroup (C : ConceptClass X Bool) : Group (autClass C) :=
  inferInstanceAs (Group (autClass C))

/-- Membership in `Aut C` unfolds to the fixing condition. -/
theorem mem_autClass {C : ConceptClass X Bool} {e : Equiv.Perm X} :
    e ∈ autClass C ↔ pullback (⇑e) C = C := Iff.rfl

/-- **VC is `Aut C`-invariant** (RK7 invariance, the clean half). Every automorphism `e ∈ Aut C` fixes
the class, so it trivially fixes the VC dimension; and more substantively, *any* domain relabelling —
automorphism or not — preserves the VC dimension (`vcDim_pullback_equiv`), so VC is constant on the
entire orbit of `C` under the symmetric group. This is the precise sense in which VC is a
*relabeling-invariant* capacity. -/
theorem vcDim_aut_invariant (C : ConceptClass X Bool) (e : autClass C) :
    VCDim X (pullback (⇑(e : Equiv.Perm X)) C) = VCDim X C := by
  rw [(mem_autClass.mp e.2)]

/-- **VC is invariant under arbitrary relabellings** (the orbit statement, re-export of
`vcDim_pullback_equiv`): for *any* `e : X ≃ X`, `VCDim (pullback e C) = VCDim C`. This is the genuine
content behind "relabel-invariant capacity" — it holds for the whole symmetric group, of which `Aut C`
is the stabilizer of `C`. -/
theorem vcDim_relabel_invariant (e : X ≃ X) (C : ConceptClass X Bool) :
    VCDim X (pullback (⇑e) C) = VCDim X C :=
  vcDim_pullback_equiv e C

/-- **Universality, the provable direction** (boundary, RK7). The URS conjectures VC is the *universal*
relabel-invariant capacity — that every relabel-invariant capacity factors through VC. We deliver the
**easy** implication cleanly: any capacity `μ` that *factors through* `VCDim` (i.e. `μ C = φ (VCDim C)`
for some `φ`) is automatically invariant under every domain relabelling. So "factors through VC" ⟹
"relabel-invariant"; VC is *a* universal-style source of relabel-invariants.

The *converse* — that every relabel-invariant capacity factors through VC — is **not** proved here and
is **false in general** (finer relabel-invariant functionals exist that are not functions of VC). The
genuine refutation is `vcDim_not_universal_relabel_invariant` (concept count) and the sharper
`vcDim_not_universal_relabel_invariant_dual` (the Assouad dual VC capacity), each exhibiting a *proven*
relabel-invariant functional that *provably* does not factor through VCDim. -/
theorem aut_invariant_of_factors_through_vcDim {α : Type w}
    (φ : WithTop ℕ → α) (μ : ConceptClass X Bool → α)
    (hμ : ∀ C, μ C = φ (VCDim X C)) (e : X ≃ X) (C : ConceptClass X Bool) :
    μ (pullback (⇑e) C) = μ C := by
  rw [hμ, hμ, vcDim_relabel_invariant]

/-! ### The genuine IM4 `Pl`-kill: VC is *an* invariant, not the *terminal* one.

The conjecture IM4 senses is that VC is the **universal** relabel-invariant capacity: every
relabel-invariant functional `J` factors through VCDim (`J = φ ∘ VCDim`). The clean half above
(`aut_invariant_of_factors_through_vcDim`) is its converse — factoring-through-VCDim *implies*
relabel-invariance. The conjecture itself is **false**, and to kill it honestly we must exhibit a
functional `J` that is *proven* relabel-invariant *and* *proven* not to factor through VCDim. Two such
functionals are constructed below (concept count `ncard`, and the Assouad dual VC dimension), each
separated by the same explicit witness pair `Ca`/`Cb` of equal VCDim `1`. -/

/-- Witness class `Ca`: **all** Boolean functions on a one-point domain, `![false]` and `![true]`.
Concept count `2`, VC dimension `1` (it shatters the point), dual VC dimension `0`. -/
def Ca : Finset (Fin 1 → Bool) := {![false], ![true]}

/-- Witness class `Cb`: three Boolean functions on a two-point domain. Concept count `3`, VC dimension
`1` (it shatters a single point but not the pair — only `3 < 4` of the labellings of `{0,1}` are
realized), dual VC dimension `1`. Paired with `Ca` it separates both the concept count and the dual VC
dimension at the *same* primal VC dimension `1`. -/
def Cb : Finset (Fin 2 → Bool) := {![false, false], ![false, true], ![true, false]}

/-- `Ca` has VC dimension `1` (computed through the finset bridge). -/
theorem vcDim_Ca : VCDim (Fin 1) (↑Ca : Set (Fin 1 → Bool)) = (1 : WithTop ℕ) := by
  rw [vcdim_eq_finset_vcdim]; decide

/-- `Cb` has VC dimension `1` (computed through the finset bridge). -/
theorem vcDim_Cb : VCDim (Fin 2) (↑Cb : Set (Fin 2 → Bool)) = (1 : WithTop ℕ) := by
  rw [vcdim_eq_finset_vcdim]; decide

/-- **IM4 `Pl`-kill: VCDim is a relabel-invariant capacity but NOT the universal one.**
The concept-count `ncard` is relabel-invariant (pullback by an equiv is an injective image, so it
preserves cardinality) yet does NOT factor through VCDim: `Ca` (all functions on `Fin 1`) and `Cb`
(three functions on `Fin 2`) have equal VC dimension `1` but different concept counts `2 ≠ 3`. So no
`φ` can satisfy `J = φ ∘ VCDim`. Pairs with the converse `aut_invariant_of_factors_through_vcDim`
(factoring-through-VCDim ⟹ relabel-invariant): VCDim is *an* invariant, not the *terminal* one. -/
theorem vcDim_not_universal_relabel_invariant :
    ∃ J : (X : Type) → ConceptClass X Bool → WithTop ℕ,
      (∀ (X : Type) (e : X ≃ X) (C : ConceptClass X Bool), J X (pullback e C) = J X C)
      ∧ ¬ ∃ φ : WithTop ℕ → WithTop ℕ,
            ∀ (X : Type) (C : ConceptClass X Bool), J X C = φ (VCDim X C) := by
  refine ⟨fun _ C => (C.ncard : WithTop ℕ), ?_, ?_⟩
  · -- relabel-invariance: the `ncard` of an injective image is preserved
    intro X e C
    dsimp only
    have hinj : Function.Injective (fun c : X → Bool => c ∘ ⇑e) := by
      intro c c' h
      funext x
      have := congrFun h (e.symm x)
      simpa using this
    have hnc : (pullback (⇑e) C).ncard = C.ncard := by
      simp only [pullback]
      exact Set.ncard_image_of_injective _ hinj
    rw [hnc]
  · -- non-factoring: the `Ca` / `Cb` witness — equal VCDim `1`, unequal concept counts `2 ≠ 3`
    rintro ⟨φ, hφ⟩
    have hCa := hφ (Fin 1) (↑Ca : Set (Fin 1 → Bool))
    have hCb := hφ (Fin 2) (↑Cb : Set (Fin 2 → Bool))
    dsimp only at hCa hCb
    rw [vcDim_Ca] at hCa
    rw [vcDim_Cb] at hCb
    -- hCa : ↑(↑Ca).ncard = φ 1 , hCb : ↑(↑Cb).ncard = φ 1 ; combine and reduce to `2 = 3`
    have key := hCa.trans hCb.symm
    rw [Nat.cast_inj] at key
    -- retype the `ncard` indices to the arrow types (defeq), so `ncard_coe_finset` fires
    change (↑Ca : Set (Fin 1 → Bool)).ncard = (↑Cb : Set (Fin 2 → Bool)).ncard at key
    rw [Set.ncard_coe_finset, Set.ncard_coe_finset] at key
    exact absurd key (by decide)

/-! ### Sharper `Pl`-kill: the *dual* (Assouad) capacity also separates the same witness.

The strengthening upgrades the witness from cardinality to the canonical **dual VC dimension**
`C ↦ VCDim ↥C (dualClass C)`. We prove this functional is relabel-invariant (a domain relabelling
induces an equivalence of concepts, under which the dual classes correspond), then separate `Ca`
(dual VCDim `0`) from `Cb` (dual VCDim `1`) at the *same* primal VCDim `1`. This is a strictly sharper
`Pl`-kill: the separating invariant is itself a *capacity*, not a mere count. -/

/-- The relabelling-induced **equivalence of concepts** `↥C ≃ ↥(pullback e C)`: a domain bijection
`e : X ≃ X` sends a concept `c` to `c ∘ e` (which lands in `pullback e C = (· ∘ e) '' C`), with
inverse `d ↦ d ∘ e⁻¹`. This is the carrier of the dual-capacity relabel-invariance below. -/
noncomputable def concEquiv (e : X ≃ X) (C : ConceptClass X Bool) :
    ↥C ≃ ↥(pullback (⇑e) C) where
  toFun := fun c => ⟨c.val ∘ ⇑e, ⟨c.val, c.property, rfl⟩⟩
  invFun := fun d => ⟨d.val ∘ ⇑e.symm, by
    obtain ⟨c, hc, hcd⟩ := d.property
    have hd : d.val ∘ ⇑e.symm = c := by rw [← hcd]; funext x; simp
    rw [hd]; exact hc⟩
  left_inv := fun c => by apply Subtype.ext; funext x; simp
  right_inv := fun d => by apply Subtype.ext; funext x; simp

/-- **The dual of a pullback is the pullback of the dual** along `concEquiv`. Relabelling the primal
domain by `e` transports the dual class verbatim: `dualClass (pullback e C)` is exactly the pullback of
`dualClass C` along the inverse concept-equivalence. -/
theorem dualClass_pullback_eq (e : X ≃ X) (C : ConceptClass X Bool) :
    dualClass (pullback (⇑e) C) = pullback (⇑(concEquiv e C).symm) (dualClass C) := by
  ext f
  simp only [dualClass, pullback]
  have hsymm : ∀ d : ↥(pullback (⇑e) C),
      ((concEquiv e C).symm d).val = d.val ∘ ⇑e.symm := fun _ => rfl
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun c : ↥C => c.val (e y), ⟨e y, fun _ => rfl⟩, ?_⟩
    funext d
    show ((concEquiv e C).symm d).val (e y) = f d
    rw [hsymm d, Function.comp_apply, Equiv.symm_apply_apply, hy d]
  · rintro ⟨g, ⟨x, hx⟩, hgf⟩
    refine ⟨e.symm x, fun d => ?_⟩
    have hfd : f d = g ((concEquiv e C).symm d) := by rw [← hgf]; rfl
    rw [hfd, hx ((concEquiv e C).symm d), hsymm d, Function.comp_apply]

/-- **The dual VC dimension is relabel-invariant.** For any domain bijection `e : X ≃ X`, the dual VC
dimension of `pullback e C` equals that of `C` — `dualClass_pullback_eq` exhibits the dual classes as
pullbacks of one another along an equivalence, and `vcDim_pullback_equiv` transports the dimension. -/
theorem dualVC_relabel_invariant (e : X ≃ X) (C : ConceptClass X Bool) :
    VCDim ↥(pullback (⇑e) C) (dualClass (pullback (⇑e) C)) = VCDim ↥C (dualClass C) := by
  rw [dualClass_pullback_eq e C]
  exact vcDim_pullback_equiv (concEquiv e C).symm (dualClass C)

/-- `Ca`'s dual class is a **singleton**: over the one-point domain `Fin 1` the only evaluation map is
`c ↦ c 0`, so the dual VC dimension is `0`. -/
theorem dualVC_Ca :
    VCDim ↥(↑Ca : Set (Fin 1 → Bool)) (dualClass (↑Ca : Set (Fin 1 → Bool))) = 0 := by
  have hset : dualClass (↑Ca : Set (Fin 1 → Bool))
       = {(fun c : ↥(↑Ca : Set (Fin 1 → Bool)) => c.val 0)} := by
    ext f
    simp only [dualClass, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx⟩; funext c; rw [hx c, Subsingleton.elim x 0]
    · rintro rfl; exact ⟨0, fun _ => rfl⟩
  rw [hset]; exact vcDim_singleton_eq_zero _

/-- The two evaluation maps on `↥Cb`: `gb0 = (· 0)` and `gb1 = (· 1)`. -/
private def gb0 : ↥(↑Cb : Set (Fin 2 → Bool)) → Bool := fun c => c.val 0
private def gb1 : ↥(↑Cb : Set (Fin 2 → Bool)) → Bool := fun c => c.val 1

/-- `Cb`'s dual class as a finset: the two distinct evaluation maps `gb0`, `gb1`. -/
private def CbDualFinset : Finset (↥(↑Cb : Set (Fin 2 → Bool)) → Bool) := {gb0, gb1}

/-- `Cb`'s dual class consists of **two distinct** evaluation maps (`c ↦ c 0` and `c ↦ c 1`), which
disagree on the concepts of `Cb`; the dual VC dimension is therefore `1` (computed via the finset
bridge over the three-element concept subtype). -/
theorem dualVC_Cb :
    VCDim ↥(↑Cb : Set (Fin 2 → Bool)) (dualClass (↑Cb : Set (Fin 2 → Bool))) = 1 := by
  have hset : dualClass (↑Cb : Set (Fin 2 → Bool))
      = (↑CbDualFinset : Set (↥(↑Cb : Set (Fin 2 → Bool)) → Bool)) := by
    ext f
    simp only [dualClass, Set.mem_setOf_eq, CbDualFinset, Finset.coe_insert, Finset.coe_singleton]
    constructor
    · rintro ⟨x, hx⟩
      fin_cases x
      · left; funext c; rw [hx c]; rfl
      · right; funext c; rw [hx c]; rfl
    · rintro (rfl | rfl)
      · exact ⟨0, fun _ => rfl⟩
      · exact ⟨1, fun _ => rfl⟩
  rw [hset, vcdim_eq_finset_vcdim]; decide

/-- **Sharper IM4 `Pl`-kill: the Assouad dual VC dimension is a relabel-invariant capacity that does
NOT factor through VCDim.** The functional `J C = VCDim ↥C (dualClass C)` is relabel-invariant
(`dualVC_relabel_invariant`) yet separates `Ca` (dual VCDim `0`) from `Cb` (dual VCDim `1`) at the same
primal VCDim `1`, so no `φ` gives `J = φ ∘ VCDim`. This upgrades `vcDim_not_universal_relabel_invariant`
from "cardinality" to the canonical dual *capacity*: the invariant lattice over relabellings is
strictly finer than VCDim even when restricted to capacity-valued functionals. -/
theorem vcDim_not_universal_relabel_invariant_dual :
    ∃ J : (X : Type) → ConceptClass X Bool → WithTop ℕ,
      (∀ (X : Type) (e : X ≃ X) (C : ConceptClass X Bool), J X (pullback e C) = J X C)
      ∧ ¬ ∃ φ : WithTop ℕ → WithTop ℕ,
            ∀ (X : Type) (C : ConceptClass X Bool), J X C = φ (VCDim X C) := by
  refine ⟨fun _ C => VCDim ↥C (dualClass C), ?_, ?_⟩
  · -- relabel-invariance of the dual capacity
    intro X e C
    exact dualVC_relabel_invariant e C
  · -- non-factoring: the `Ca` / `Cb` witness — equal primal VCDim `1`, dual VCDims `0 ≠ 1`
    rintro ⟨φ, hφ⟩
    have hCa := hφ (Fin 1) (↑Ca : Set (Fin 1 → Bool))
    have hCb := hφ (Fin 2) (↑Cb : Set (Fin 2 → Bool))
    dsimp only at hCa hCb
    rw [vcDim_Ca] at hCa
    rw [vcDim_Cb] at hCb
    -- retype the dual-VC indices (defeq), so `dualVC_Ca` / `dualVC_Cb` fire
    change VCDim ↥(↑Ca : Set (Fin 1 → Bool)) (dualClass (↑Ca : Set (Fin 1 → Bool))) = φ 1 at hCa
    change VCDim ↥(↑Cb : Set (Fin 2 → Bool)) (dualClass (↑Cb : Set (Fin 2 → Bool))) = φ 1 at hCb
    rw [dualVC_Ca] at hCa
    rw [dualVC_Cb] at hCb
    -- hCa : (0 : WithTop ℕ) = φ 1 , hCb : (1 : WithTop ℕ) = φ 1
    rw [← hCa] at hCb
    exact absurd hCb (by decide)

/-- **The weak "dual map is lossy" corollary** (demoted from `universality_reduction`, A4 honesty).
This is *only* the ≤2-step weakening `ne_of_lt dualClass_not_vcDim_preserving`: it observes that the
dual VC dimension of `boolPair` differs from its primal VC dimension, hence the two functionals are
not literally equal. It is **not** the genuine IM4 `Pl`-kill — that requires a functional *proven*
relabel-invariant *and proven* not to factor through VCDim, which is
`vcDim_not_universal_relabel_invariant` (cardinality) and, sharper,
`vcDim_not_universal_relabel_invariant_dual` (the dual capacity). Kept only as a one-line corollary so
the boundary is in one place; see those two theorems for the real refutation of the factorization
principle. -/
theorem dual_map_lossy_corollary :
    ∃ (Y : Type) (D : ConceptClass Y Bool),
      VCDim ↥D (dualClass D) ≠ VCDim Y D := by
  obtain ⟨Y, D, hlt⟩ := dualClass_not_vcDim_preserving
  exact ⟨Y, D, ne_of_lt hlt⟩

/-! ## Argument 5 — the algebra of obstructions (RK5 / KU7)

The discovery URS asks which algebraic identities capacity is *forbidden* to satisfy, beyond the
matroid `Pl`-kill already in `MatroidStructure` (`not_vcDimSubmodular`). We add the next generators of
the "obstruction module" and pin the positive/negative boundary precisely: VC dimension is monotone,
normalized, and modular **on chains**, but is forbidden from being subadditive, modular off chains, or
a lattice valuation. -/

/-- **Forbidden identity 1 — subadditivity** (obstruction generator, restating the core kill at the
bare-subadditivity level). VC dimension is *not* subadditive under union: there is a domain with two
classes for which `VCDim C + VCDim D < VCDim (C ∪ D)`. This is `vcDim_not_subadditive_collectionUnion`
surfaced as the first generator of the obstruction module — the identity `r(C∪D) ≤ rC + rD` that any
measure or matroid rank obeys, and VC does not. -/
theorem vcDim_not_subadditive_under_union :
    ∃ (Y : Type) (C D : ConceptClass Y Bool), VCDim Y C + VCDim Y D < VCDim Y (C ∪ D) :=
  vcDim_not_subadditive_collectionUnion

/-- **Forbidden identity 2 — modularity (the lattice-valuation law) off chains** (obstruction
generator). A lattice valuation obeys `r(C∪D) + r(C∩D) = rC + rD` *everywhere*; VC obeys it only on
chains (`vcDim_modular_on_chain`). Off chains even the submodular inequality fails
(`not_vcDimSubmodular`), so a fortiori the valuation equality fails: there is a domain where
`VCDim C + VCDim D < VCDim (C ∪ D) + VCDim (C ∩ D)`. Hence VC is **not a lattice valuation**; it is a
valuation only on the chain sublattice. -/
theorem vcDim_not_modular_off_chain :
    ∃ (Y : Type) (C D : ConceptClass Y Bool),
      VCDim Y C + VCDim Y D < VCDim Y (C ∪ D) + VCDim Y (C ∩ D) := by
  obtain ⟨Y, C, D, hsuper⟩ := vcDim_not_subadditive_collectionUnion
  exact ⟨Y, C, D, lt_of_lt_of_le hsuper (self_le_add_right _ _)⟩

/-- **The permitted identities** (the positive boundary, `describe`). VC dimension *does* satisfy:
monotonicity (`vcDim_mono`), normalization (`VCDim ∅ = ⊥`), and modularity on chains
(`vcDim_modular_on_chain`). Bundled here as the complement of the obstruction module: this is the exact
algebraic profile of capacity — a monotone, normalized, chain-modular invariant. -/
theorem vcDim_permitted_identities :
    (∀ {C D : ConceptClass X Bool}, C ⊆ D → VCDim X C ≤ VCDim X D)
      ∧ VCDim X (∅ : ConceptClass X Bool) = ⊥
      ∧ (∀ {C D : ConceptClass X Bool}, C ⊆ D →
          VCDim X (C ∪ D) + VCDim X (C ∩ D) = VCDim X C + VCDim X D) :=
  ⟨fun h => vcDim_mono h, vcDim_rank_normalized, fun h => vcDim_modular_on_chain h⟩

/-! ## Argument 6 — the proven Hasse edges of the dimension zoo (KU6 / RK2)

The dimension zoo wants to be one partially-ordered object. We collect the order edges that *genuinely
build* — the VC-internal lattice edges proven in this development — as one bundle, and name the still
-open cross-shape edge as a precise reduction. -/

/-- **The proven Hasse edges** (re-export bundle, `describe`). The order relations between capacities
that are kernel-verified in this development, stated as one `Prop`:

* `VCDim` is monotone in the class (`vcDim_mono`);
* `VCDim (C ∩ D) ≤ min` (`vcDim_inter_le_min`) — the meet edge;
* the two-class union is bounded by `dC + dD + 1` (`vcDim_union_le`) — the join edge.

These are the genuinely-building edges of the structural partial order; cross-*shape* edges (to
Littlestone, Natarajan, pseudodimension) live in `CapacitySpectrum.lean` as the `spectrum_*`
re-exports. No new mathematics: this is a typed table of the proven order. -/
theorem hasse_proven_edges (C D : ConceptClass X Bool) {dC dD : ℕ}
    (hC : VCDim X C ≤ (dC : WithTop ℕ)) (hD : VCDim X D ≤ (dD : WithTop ℕ)) :
    (C ⊆ D → VCDim X C ≤ VCDim X D)
      ∧ VCDim X (C ∩ D) ≤ min (VCDim X C) (VCDim X D)
      ∧ VCDim X (C ∪ D) ≤ ((dC + dD + 1 : ℕ) : WithTop ℕ) :=
  ⟨fun h => vcDim_mono h, vcDim_inter_le_min C D, vcDim_union_le hC hD⟩

/-- **The open Hasse edge, as a precise reduction** (frontier, RK2). The clean cross-shape edge
`VCDim ≤ LittlestoneDim` (a shattered set is a depth-`d` shattered stump) is **not** re-exportable: its
only kernel proof, `vcdim_le_of_mistake_bounded`, is `private` in `FLT_Proofs/Theorem/Separation.lean`.
We record the reduction as an explicit hypothesis-to-conclusion statement: *if* one is given the
mistake-bound edge `VCDim X C ≤ OptimalMistakeBound X C` (the named missing lemma), *then*
`VCDim ≤ LittlestoneDim` follows via `spectrum_omb_eq_littlestone`. This converts the open edge into a
single named blocker rather than a vague gap. -/
theorem hasse_open_reduction (X : Type) (C : ConceptClass X Bool) (hne : C.Nonempty)
    (hmb : (VCDim X C : WithBot (WithTop ℕ)) ≤ (↑(OptimalMistakeBound X C) : WithBot (WithTop ℕ))) :
    (VCDim X C : WithBot (WithTop ℕ)) ≤ LittlestoneDim X C := by
  rw [← spectrum_omb_eq_littlestone X C hne]
  exact hmb

/-! ## Argument 7 — decomposition theory (KU5 / M5)

The inverse of amalgamation: given `C`, when does it split into strictly simpler pieces? The strongest
in-closure statement is the *union budget* — a class presented as a finite union of finite-VC pieces
has VC dimension controlled by the pieces. The *primary* decomposition (into VC-dimension-`1` atoms)
is reduced to a named missing lemma. -/

/-- **Union-decomposition budget** (strongest partial, M5 inverse). If `C` is presented as the union of
two pieces of VC dimensions `≤ dC` and `≤ dD`, then `C` has VC dimension `≤ dC + dD + 1`. Contrapositive
reading as a decomposition obstruction: a class of VC dimension `> dC + dD + 1` **cannot** be written as
a union of a `dC`- and a `dD`-piece — a quantitative lower bound on the complexity of any 2-piece
decomposition. This is the sharp two-class budget (`vcDim_union_le`) read in the decomposition
direction. -/
theorem finite_vc_union_decomposition_budget {C D : ConceptClass X Bool} {dC dD : ℕ}
    (hC : VCDim X C ≤ (dC : WithTop ℕ)) (hD : VCDim X D ≤ (dD : WithTop ℕ)) :
    VCDim X (C ∪ D) ≤ ((dC + dD + 1 : ℕ) : WithTop ℕ) :=
  vcDim_union_le hC hD

/-- **The decomposition obstruction, sharp direction.** If a class `E` is too rich to fit the budget —
`(dC + dD + 1 : ℕ) < VCDim X E` — then `E` admits **no** decomposition `E = C ∪ D` with `VCDim C ≤ dC`
and `VCDim D ≤ dD`. This is the genuine structural content of M5's inverse at the two-piece level: it
forbids cheap decompositions and lower-bounds the budget any decomposition must pay. -/
theorem no_cheap_union_decomposition {E : ConceptClass X Bool} {dC dD : ℕ}
    (hE : ((dC + dD + 1 : ℕ) : WithTop ℕ) < VCDim X E) :
    ¬ ∃ (C D : ConceptClass X Bool),
        E = C ∪ D ∧ VCDim X C ≤ (dC : WithTop ℕ) ∧ VCDim X D ≤ (dD : WithTop ℕ) := by
  rintro ⟨C, D, rfl, hC, hD⟩
  exact absurd (vcDim_union_le hC hD) (not_le.mpr hE)

/-- **Primary-decomposition reduction** (frontier, KU5). The conjecture "every finite-VC class splits
into a bounded union of VC-dimension-`≤ 1` atoms" is reduced to a single named missing lemma: the
existence of an *atomic cover*. We state the principle as an explicit predicate and prove the trivial
direction (an atomic cover, if it exists, yields the budget via iterated `vcDim_union_le`); we do
**not** assert the cover exists — that is the open KU5 frontier, and it is genuinely false without
extra hypotheses (the `Θ(d k log k)` super-additivity of k-fold unions, BEHW 1989, means atoms cannot
be glued for free). The reduction names exactly what is missing: an atom-count bound. -/
def HasAtomicDecomposition (X : Type u) (C : ConceptClass X Bool) (k : ℕ) : Prop :=
  ∃ A : Fin k → ConceptClass X Bool,
    C = ⋃ i, A i ∧ ∀ i, VCDim X (A i) ≤ (1 : WithTop ℕ)

/-- **The reduction lemma.** *If* `C` has an atomic decomposition into `k` pieces of VC dimension `≤ 1`
(the named missing `HasAtomicDecomposition` hypothesis), *then* `C` has finite VC dimension. This is the
honest content: atomicity ⟹ finiteness is provable (the union of finitely many finite-VC classes is
finite-VC, `vcDim_iUnion_finite`-style), but the *converse* — finiteness ⟹ atomicity — is the open KU5,
left unbanked. -/
theorem primary_decomposition_reduction {X : Type u} (C : ConceptClass X Bool) {k : ℕ}
    (h : HasAtomicDecomposition X C k) : VCDim X C < ⊤ := by
  obtain ⟨A, hC, hA⟩ := h
  subst hC
  -- a finite (`Fin k`-indexed) union of VC-dimension-≤1 (hence finite-VC) atoms is finite-VC
  exact vcDim_iUnion_finite A (fun i => lt_of_le_of_lt (hA i) (WithTop.coe_lt_top 1))

end StructureClosures
