/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.Monotone

/-!
# Open route R1: is VC dimension a matroid rank?

A matroid rank function is monotone, normalized, and **submodular**. The VC dimension on the lattice
of concept classes (ordered by inclusion, with join `∪` and meet `∩`) is monotone (`vcDim_mono`) and
normalized (`vcDim_empty` gives `VCDim ∅ = ⊥`), but submodularity
`VCDim(C∪D) + VCDim(C∩D) ≤ VCDim C + VCDim D` **fails on the full lattice**: the union bound
`vcDim_union_le` is sharp at `VCDim C + VCDim D + 1`, one above the submodular ceiling, and the
`k`-fold union grows like `Θ(d k log k)` (`vcDim_not_subadditive_collectionUnion`), far above any
submodular function.

**R1 (open).** Characterize the maximal sublattice on which `VCDimSubmodular` holds, and determine
whether VC dimension admits a submodular surrogate tight to within the `k`-fold log-correction. This
file states the submodularity object and settles the one clean case — chains, where VC dimension is
exactly *modular* (`vcDim_modular_on_chain`). The resolution at the density scale is recorded in
`VCDensity.lean`: VC *density* is subadditive (`hasPolyDegree_booleanComb`), so density, not
dimension, is the rank-compatible invariant. The result is stated, not proved here; R1 is open.

Reference for the matroid–VC connection: J. Bastian, M. Schaefer, et al., on oriented-matroid rank as
the VC dimension of the tope graph (Goodman–Pollack; see arXiv:2312.17365).

## Main results

* `VCDimSubmodular`: the submodularity (matroid-rank) property of VC dimension — R1's central object.
* `vcDim_modular_on_chain`: on a chain, VC dimension is modular (submodularity holds with equality).
-/

open Set

universe u

variable {X : Type u}

/-- **The submodularity (matroid-rank) property of VC dimension** — the central object of R1. VC
dimension is monotone and normalized, but this property is what would make it a genuine matroid rank;
it fails on the full concept-class lattice (the sharp `+1` in `vcDim_union_le`). -/
def VCDimSubmodular (X : Type u) : Prop :=
  ∀ C D : ConceptClass X Bool, VCDim X (C ∪ D) + VCDim X (C ∩ D) ≤ VCDim X C + VCDim X D

/-- **On a chain, VC dimension is modular.** If `C ⊆ D` then `C ∪ D = D` and `C ∩ D = C`, so the
submodular inequality holds with equality. Submodularity can only fail off chains — which is exactly
where the sharp `d + d' + 1` union bound bites. -/
theorem vcDim_modular_on_chain {C D : ConceptClass X Bool} (h : C ⊆ D) :
    VCDim X (C ∪ D) + VCDim X (C ∩ D) = VCDim X C + VCDim X D := by
  rw [union_eq_self_of_subset_left h, inter_eq_self_of_subset_left h]
  exact add_comm _ _
