/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.VCDimension

/-!
# XOR-shift invariance of VC dimension

Exclusive-or against a fixed pattern `a : X → Bool` permutes the labellings of any sample, so it
sends a shattered set to a shattered set and leaves the VC dimension unchanged. Complement
invariance is the case `a = fun _ => true`.

These are the codomain symmetries of the VC dimension: relabelling the two output values (here, by
a per-point exclusive-or) does not change how much a class can shatter. The domain symmetries
(invariance under a bijection of `X`) are treated elsewhere.

## Main results

* `xorShift`, `negClass`: the exclusive-or-shifted and complemented concept classes.
* `shatters_xorShift`: an exclusive-or shift preserves shattering of every sample.
* `vcDim_xorShift`, `vcDim_negClass`: an exclusive-or shift, and complementation, preserve the
  VC dimension.
-/

universe u

variable {X : Type u}

/-- The pointwise exclusive-or of a concept class by a fixed pattern `a : X → Bool`. -/
def xorShift (a : X → Bool) (C : ConceptClass X Bool) : ConceptClass X Bool :=
  (fun c => fun x => Bool.xor (a x) (c x)) '' C

/-- The complement of a concept class, that is, the exclusive-or shift by the all-`true` pattern. -/
def negClass (C : ConceptClass X Bool) : ConceptClass X Bool :=
  xorShift (fun _ => true) C

private theorem xor_cancel_left (b u v : Bool) (h : Bool.xor b u = Bool.xor b v) : u = v := by
  cases b <;> cases u <;> cases v <;> simp_all

private theorem xor_xor_self (b u : Bool) : Bool.xor b (Bool.xor b u) = u := by
  cases b <;> cases u <;> rfl

/-- An exclusive-or shift preserves shattering of every finite sample. The map
`f ↦ fun x => Bool.xor (a x) (f x)` is an involution on labellings, so every labelling is realized
after the shift exactly when every labelling is realized before it. -/
theorem shatters_xorShift (a : X → Bool) (C : ConceptClass X Bool) (S : Finset X) :
    Shatters X (xorShift a C) S ↔ Shatters X C S := by
  constructor
  · intro h g
    obtain ⟨c', hc', hc'eq⟩ := h (fun x => Bool.xor (a x) (g x))
    obtain ⟨c, hc, rfl⟩ := hc'
    exact ⟨c, hc, fun x => xor_cancel_left (a x) (c x) (g x) (hc'eq x)⟩
  · intro h f
    obtain ⟨c, hc, hceq⟩ := h (fun x => Bool.xor (a x) (f x))
    refine ⟨fun x => Bool.xor (a x) (c x), ⟨c, hc, rfl⟩, fun x => ?_⟩
    show Bool.xor (a x) (c x) = f x
    rw [hceq x]
    exact xor_xor_self (a x) (f x)

/-- An exclusive-or shift preserves the VC dimension: `VCDim (xorShift a C) = VCDim C`. -/
theorem vcDim_xorShift (a : X → Bool) (C : ConceptClass X Bool) :
    VCDim X (xorShift a C) = VCDim X C := by
  unfold VCDim
  simp only [shatters_xorShift]

/-- Complementation preserves the VC dimension: `VCDim (negClass C) = VCDim C`. -/
theorem vcDim_negClass (C : ConceptClass X Bool) :
    VCDim X (negClass C) = VCDim X C :=
  vcDim_xorShift (fun _ => true) C
