/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.GrowthMul

/-!
# A shattered set forces the growth function to be `2 ^ m`

If a class shatters a sample then it realizes every labelling of it, so its set of restriction
patterns is everything and the growth function at that size is `2 ^ m`. This is the half of the
finiteness argument that produces the exponential lower bound, to be contradicted against a
polynomial upper bound by `no_unbounded_two_pow_le_poly`.

## Main results

* `restrictionSet_eq_univ_of_shatters`: a shattered sample realizes every pattern.
* `growthFunction_ge_two_pow_of_shatters`: a shattered sample of size `m` forces growth `≥ 2 ^ m`.
-/

universe u

variable {X : Type u}

/-- A shattered sample realizes every labelling, so its restriction-pattern set is everything. -/
theorem restrictionSet_eq_univ_of_shatters {C : ConceptClass X Bool} {S : Finset X}
    (h : Shatters X C S) : restrictionSet C S = Set.univ :=
  Set.eq_univ_of_forall h

/-- A shattered sample of size `m` forces the growth function at `m` to be at least `2 ^ m`. -/
theorem growthFunction_ge_two_pow_of_shatters {C : ConceptClass X Bool} {S : Finset X}
    (h : Shatters X C S) : 2 ^ S.card ≤ GrowthFunction X C S.card := by
  classical
  have hcard : (restrictionSet C S).ncard = 2 ^ S.card := by
    rw [restrictionSet_eq_univ_of_shatters h, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  calc 2 ^ S.card = (restrictionSet C S).ncard := hcard.symm
    _ ≤ GrowthFunction X C S.card := restrictionSet_ncard_le_growthFunction C rfl
