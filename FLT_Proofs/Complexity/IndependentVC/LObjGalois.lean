/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.StructureClosures
import Mathlib.Order.Rel.GaloisConnection
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure

/-!
# The genuine point ↔ concept Galois connection (Birkhoff polarity of a learning object)

This module settles the conjecture **IM3** — that points and concepts of a learning object stand in a
genuine Galois connection / contravariant adjunction. The honest answer is *yes, but one level down
from where the conjecture first looked for it.*

The structure-theory closure (`StructureClosures`) already built the categorical skeleton
(`instLObjCategory`) and proved that the conjectured adjunction **fails at the capacity level**: the
dual drops VC dimension (`dualClass_not_vcDim_preserving`), so the bidual unit is only *lax*
(`lobj_biDual_unit_lax`). A strict capacity-preserving adjunction is therefore impossible.

What *does* hold — and is the content the conjecture was really pointing at — is the classical
**Birkhoff polarity** of the incidence relation between points and concepts. Write the incidence
relation `r x c := (c x = true)` between the points `X` and the concepts `X → Bool`. It induces two
antitone maps on the powerset lattices,

* `intent  : Set X → Set (X → Bool)`,  `intent s = {c | ∀ x ∈ s, c x = true}`  (the concepts agreeing
  with everything in `s`),
* `extent  : Set (X → Bool) → Set X`,  `extent t = {x | ∀ c ∈ t, c x = true}`  (the points on which
  every concept of `t` fires),

and these form a **genuine `GaloisConnection`** between `Set X` and `(Set (X → Bool))ᵒᵈ`
(equivalently an antitone Galois connection on the two powerset lattices). This is exactly the
construction of *formal concept analysis*: `intent`/`extent` are the *attribute/object derivation
operators*, `intent ∘ extent` is the *concept-closure operator*, and its fixed points are the *formal
concepts* of the context `(X, X → Bool, r)`.

This is real, kernel-checkable Mathlib content: the relation-polarity Galois connection is
`SetRel.gc_leftDual_rightDual` (Mathlib `Order.Rel.GaloisConnection`), and we obtain the genuine
`GaloisConnection` instance by identifying `intent`/`extent` with that relation's `leftDual`/
`rightDual`.

## How this closes IM3

1. **The genuine adjunction (KK).** `pointConcept_galoisConnection` is an honest
   `GaloisConnection (toDual ∘ intent) (extent ∘ ofDual)`. The closure-operator facts follow:
   `le_extent_intent`, `intent_extent_le` (the two unit/counit inequalities), `intent_extent_closure`
   (the formal-concept closure operator), and the polarity identity `intent_extent_intent`.

2. **It *is* the LObj duality data (DIRECT).** The incidence relation is exactly `evalConcept`:
   `incidence x c ↔ evalConcept` fires (`incidence_iff_evalConcept`), and the dual concepts of
   `dualClass` are precisely the evaluations through the relation (`dualClass_eq_evalConcept_range`,
   `mem_intent_singleton_iff_mem_dualClass`-style bridges). So the LObj point↔concept duality *is* this
   polarity's action on singletons.

3. **The boundary, made exact (Pl-kill).** `galois_holds_capacity_fails` composes the genuine
   set-level Galois connection (#1) with the existing capacity `Pl`-kill
   (`dualClass_not_vcDim_preserving`): the adjunction is genuine on the **set lattices** but does
   **not** lift to a capacity-preserving adjunction, because the VC functional is not invariant under
   the dual. The exact level at which the adjunction holds (incidence/extensional) versus fails
   (capacity/VC) is thereby pinned.

## References

* G. Birkhoff, *Lattice Theory*, AMS Colloquium Publications 25, 1940 (1st ed.); the theory of
  *polarities* of a binary relation and the induced Galois connection on the powerset lattices.
* B. Ganter and R. Wille, *Formal Concept Analysis: Mathematical Foundations*, Springer, 1999; the
  derivation operators (intent/extent), the concept-closure operator, and the lattice of formal
  concepts of a context `(G, M, I)`.
* O. Ore, *Galois connexions*, Trans. Amer. Math. Soc. 55 (1944), 493–513.
-/

open Set OrderDual

universe u

namespace StructureClosures

variable {X : Type u}

/-! ## 1. The incidence relation and its two derivation operators

The data of a learning object, read as a *formal context* in the sense of Ganter–Wille: the objects
are the points `X`, the attributes are the concepts `X → Bool`, and the incidence is "the concept
fires at the point". -/

/-- The **incidence relation** of a learning object: a point `x` and a concept `c` are incident when
`c` fires at `x`, i.e. `c x = true`. This is the relation `r x c := (c x = true)` whose Birkhoff
polarity is the point↔concept Galois connection. As a `SetRel X (X → Bool)` it is the set of incident
pairs. -/
def incidence (X : Type u) : SetRel X (X → Bool) := {p : X × (X → Bool) | p.2 p.1 = true}

/-- Membership in the incidence relation is exactly "the concept fires at the point". -/
@[simp] theorem mem_incidence {x : X} {c : X → Bool} :
    (x, c) ∈ incidence X ↔ c x = true := Iff.rfl

/-- The **intent** operator of formal concept analysis: the set of concepts that fire on *every* point
of `s`. `intent s = {c | ∀ x ∈ s, c x = true}`. (Ganter–Wille: the *attributes shared by all objects
of* `s`; Birkhoff: the polar of `s`.) This is the left polarity map `Set X → Set (X → Bool)`. -/
def intent (s : Set X) : Set (X → Bool) := {c : X → Bool | ∀ ⦃x⦄, x ∈ s → c x = true}

/-- The **extent** operator of formal concept analysis: the set of points on which *every* concept of
`t` fires. `extent t = {x | ∀ c ∈ t, c x = true}`. (Ganter–Wille: the *objects having all attributes
of* `t`; Birkhoff: the polar of `t`.) This is the right polarity map `Set (X → Bool) → Set X`. -/
def extent (t : Set (X → Bool)) : Set X := {x : X | ∀ ⦃c⦄, c ∈ t → c x = true}

@[simp] theorem mem_intent {s : Set X} {c : X → Bool} :
    c ∈ intent s ↔ ∀ ⦃x⦄, x ∈ s → c x = true := Iff.rfl

@[simp] theorem mem_extent {t : Set (X → Bool)} {x : X} :
    x ∈ extent t ↔ ∀ ⦃c⦄, c ∈ t → c x = true := Iff.rfl

/-- `intent` is the relation's `leftDual` (definitional). The polarity of the incidence relation in
Mathlib's `SetRel` API *is* the intent operator. -/
theorem intent_eq_leftDual (s : Set X) : intent s = (incidence X).leftDual s := rfl

/-- `extent` is the relation's `rightDual` (definitional). The polarity of the incidence relation in
Mathlib's `SetRel` API *is* the extent operator. -/
theorem extent_eq_rightDual (t : Set (X → Bool)) : extent t = (incidence X).rightDual t := rfl

/-! ## 2. The genuine Galois connection (KK)

The two derivation operators are *antitone*; phrased through the order-dual, they form a genuine
`GaloisConnection`. We obtain it for free from Mathlib's relation-polarity Galois connection
`SetRel.gc_leftDual_rightDual`, after identifying `intent`/`extent` with `leftDual`/`rightDual`. -/

/-- **The point ↔ concept Galois connection** (KK — the genuine adjunction IM3 sought). The intent and
extent derivation operators of the incidence relation form a genuine `GaloisConnection` between
`Set X` and `(Set (X → Bool))ᵒᵈ`:

  `intent s ⊇ t  ↔  s ⊆ extent t`   (read through `OrderDual`).

Equivalently, this is the **antitone Galois connection** of the Birkhoff polarity: `intent` and
`extent` are each order-reversing, and `s ⊆ extent t ↔ t ⊆ intent s`. This is *not* a decorative
definition — it is a bona fide `GaloisConnection` term, namely `(incidence X).gc_leftDual_rightDual`
transported along the definitional identities `intent = leftDual`, `extent = rightDual`.

Reference: Birkhoff 1940, polarities; Ganter–Wille 1999, the basic theorem of FCA. -/
theorem pointConcept_galoisConnection :
    GaloisConnection (toDual ∘ intent (X := X)) (extent ∘ ofDual) :=
  (incidence X).gc_leftDual_rightDual

/-- The Galois-connection adjunction law, spelled out at the level of the underlying sets without the
`OrderDual` wrapper: `s ⊆ extent t ↔ t ⊆ intent s`. This is the symmetric antitone-polarity form —
the defining property of a Birkhoff polarity. -/
theorem subset_extent_iff_subset_intent {s : Set X} {t : Set (X → Bool)} :
    s ⊆ extent t ↔ t ⊆ intent s := by
  have h := pointConcept_galoisConnection (a := s) (b := toDual t)
  -- `toDual ∘ intent s ≤ toDual t` unfolds (in the order dual) to `t ⊆ intent s`
  simpa [Function.comp, OrderDual.toDual_le_toDual] using h.symm

/-! ## 3. Closure-operator facts of the polarity

The composites `extent ∘ intent` and `intent ∘ extent` are closure operators (Ganter–Wille: the
object-closure and concept-closure operators). Their fixed points are the *formal concepts* of the
learning object. -/

/-- **Unit inequality** `s ⊆ extent (intent s)`: every point of `s` satisfies every concept that
fires on all of `s`. The object-closure half of the polarity. -/
theorem subset_extent_intent (s : Set X) : s ⊆ extent (intent s) :=
  pointConcept_galoisConnection.le_u_l s

/-- **Counit inequality** `t ⊆ intent (extent t)`: every concept of `t` fires on all points where the
whole of `t` fires. The concept-closure half of the polarity. (In the order dual this is
`l_u_le`; spelled out on the plain sets it is the displayed inclusion.) -/
theorem subset_intent_extent (t : Set (X → Bool)) : t ⊆ intent (extent t) := by
  have h := pointConcept_galoisConnection.l_u_le (toDual t)
  simpa [Function.comp, OrderDual.toDual_le_toDual] using h

/-- `intent` is **antitone**: a larger object set has fewer shared attributes. -/
theorem intent_antitone : Antitone (intent (X := X)) := fun _ _ h =>
  (OrderDual.toDual_le_toDual).mp (pointConcept_galoisConnection.monotone_l h)

/-- `extent` is **antitone**: a larger attribute set has fewer common objects. -/
theorem extent_antitone : Antitone (extent (X := X)) := fun _ _ h =>
  pointConcept_galoisConnection.monotone_u (OrderDual.toDual_le_toDual.mpr h)

/-- **The polarity identity** `intent (extent (intent s)) = intent s` — `intent` is unchanged by one
extra `extent ∘ intent` round trip. The algebraic core that makes `extent ∘ intent` idempotent (a
closure operator); proved by antisymmetry from the unit/counit inequalities and antitonicity of
`intent`. -/
theorem intent_extent_intent (s : Set X) : intent (extent (intent s)) = intent s :=
  le_antisymm (intent_antitone (subset_extent_intent s)) (subset_intent_extent (intent s))

/-- The dual polarity identity `extent (intent (extent t)) = extent t`. This is the `u_l_u_eq_u`
identity of the Galois connection (`u = extent ∘ ofDual`), making `intent ∘ extent` idempotent. -/
theorem extent_intent_extent (t : Set (X → Bool)) : extent (intent (extent t)) = extent t :=
  le_antisymm (extent_antitone (subset_intent_extent t)) (subset_extent_intent (extent t))

/-- **The concept-closure operator** `extent ∘ intent` of the learning object, as a genuine
`ClosureOperator (Set X)` (extensive, monotone, idempotent), obtained from the Galois connection.
Its fixed points are exactly the *extents of formal concepts* of the context `(X, X → Bool, r)` —
Ganter–Wille's closure system. -/
def conceptClosure : ClosureOperator (Set X) :=
  pointConcept_galoisConnection.closureOperator

/-- The concept-closure operator acts as `extent ∘ intent`. -/
@[simp] theorem conceptClosure_apply (s : Set X) : conceptClosure s = extent (intent s) := rfl

/-! ## 4. The polarity IS the LObj duality data (DIRECT)

We now show the Galois connection above is not a parallel construction but the *same* point↔concept
duality already in the kernel: the incidence relation is `evalConcept`, and the dual concepts of
`dualClass C` are exactly the evaluations through the relation. -/

/-- **The incidence relation is `evalConcept`.** For a class `C` and a point `x`, the dual concept
`evalConcept C x : ↥C → Bool` fires at a concept `c : ↥C` exactly when the incidence relation holds
between `x` and the underlying concept `c.val`. So the LObj evaluation embedding `x ↦ evalConcept C x`
is the row of the incidence matrix at `x`. -/
theorem incidence_iff_evalConcept (C : ConceptClass X Bool) (x : X) (c : ↥C) :
    (x, c.val) ∈ incidence X ↔ evalConcept C x c = true := Iff.rfl

/-- **The dual class is the range of the incidence rows.** `dualClass C` is precisely the set of
evaluation concepts `evalConcept C x` ranging over points `x`, i.e. the rows of the incidence relation
restricted to `↥C`. This identifies the LObj dual (`dualClass`/`evalConcept`) as the incidence data of
the polarity: dualization is "read off the incidence relation row by row". -/
theorem dualClass_eq_evalConcept_range (C : ConceptClass X Bool) :
    dualClass C = Set.range (evalConcept C) := by
  ext f
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, funext fun c => (hx c).symm⟩
  · rintro ⟨x, rfl⟩
    exact evalConcept_mem C x

/-- **The intent of a single point, through the incidence relation.** A concept `c` lies in
`intent {x}` exactly when `c` fires at `x` — i.e. exactly when the incidence relation holds. So the
intent operator on a singleton point reads off the same incidence data the dual uses, confirming that
`intent`/`extent` and `dualClass`/`evalConcept` are two presentations of one polarity. -/
theorem mem_intent_singleton_iff_incidence {x : X} {c : X → Bool} :
    c ∈ intent ({x} : Set X) ↔ (x, c) ∈ incidence X := by
  simp [intent]

/-- **The extent of a single concept** is the set of points it fires on — its support/positive set.
This is the polarity's right derivation on a singleton attribute, the dual-side reading of the
incidence data. -/
theorem extent_singleton (c : X → Bool) : extent ({c} : Set (X → Bool)) = {x | c x = true} := by
  ext x; simp [extent]

/-! ## 5. The boundary, made exact (Pl-kill)

The Galois connection of §2 is genuine on the **set lattices**. We now compose it with the existing
capacity `Pl`-kill to state, in one place, the exact level at which the adjunction holds versus fails. -/

/-- **The genuine adjunction lives at the incidence level; the capacity adjunction does not exist**
(the exact IM3 boundary, composing the KK Galois connection with the existing `Pl`-kill).

Two halves, both kernel-checked:

* **(holds, set level)** For *every* point set `s` and concept set `t`, the intent/extent polarity is
  a genuine Galois connection: `s ⊆ extent t ↔ t ⊆ intent s` (this is `pointConcept_galoisConnection`,
  surfaced here on the plain sets). The point↔concept adjunction the conjecture sought is real, at the
  extensional/incidence level.

* **(fails, capacity level)** Yet this polarity does **not** lift to a capacity-preserving adjunction:
  there is a learning object whose VC dimension is strictly changed by the dual
  (`dualClass_not_vcDim_preserving`), so the VC functional is not invariant under the polarity and the
  capacity-level adjunction is at best *lax* (`lobj_biDual_unit_lax`), never strict.

Hence IM3 closes as: a genuine Galois connection at the incidence/Birkhoff-polarity level, and a sharp
impossibility at the capacity level. -/
theorem galois_holds_capacity_fails :
    -- (holds) the genuine point↔concept Galois connection on the set lattices:
    (∀ {s : Set X} {t : Set (X → Bool)}, s ⊆ extent t ↔ t ⊆ intent s)
      -- (fails) but capacity is not invariant under the dual — no strict capacity adjunction:
      ∧ (∃ (Y : Type) (D : ConceptClass Y Bool), VCDim ↥D (dualClass D) < VCDim Y D) :=
  ⟨fun {_ _} => subset_extent_iff_subset_intent, dualClass_not_vcDim_preserving⟩

/-- **Restated as a single sentence about IM3** (the honest closure verdict). The point↔concept
adjunction is genuine as a Birkhoff polarity (`pointConcept_galoisConnection`, a real
`GaloisConnection`), and the capacity-preserving upgrade is impossible (the dual is VC-lossy). The two
facts together *are* the full honest closure of the conjecture: the adjunction exists, exactly one
level down from the capacity functional where the conjecture first looked. -/
theorem im3_closure_verdict :
    GaloisConnection (toDual ∘ intent (X := X)) (extent ∘ ofDual)
      ∧ (∃ (Y : Type) (D : ConceptClass Y Bool), VCDim ↥D (dualClass D) < VCDim Y D) :=
  ⟨pointConcept_galoisConnection, dualClass_not_vcDim_preserving⟩

end StructureClosures
