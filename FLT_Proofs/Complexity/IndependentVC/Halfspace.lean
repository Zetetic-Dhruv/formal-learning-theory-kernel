/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.Dudley
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# VC dimension of linear halfspaces (the canonical Dudley corollary)

**Cover (1965), Vapnik–Chervonenkis.** Homogeneous linear halfspaces in `ℝⁿ` have VC dimension
exactly `n`, the ambient dimension. This is the textbook instance of Dudley's bound
(`vcDim_signClass_le`): the relevant function space is the span of the `n` coordinate functionals
`x ↦ xᵢ`, which is the (dual) coordinate space of dimension `n`, so the sign class
`x ↦ (0 < ⟨w, x⟩)` has VC dimension `≤ n`; the `n` standard basis points are shattered, giving the
matching lower bound.

## Main definitions

* `coordSpace n` : the span of the `n` coordinate functionals `(fun x => x i)` inside
  `(Fin n → ℝ) → ℝ`. Its sign class `signClass (coordSpace n)` is the family of homogeneous linear
  halfspaces of `ℝⁿ`.

## Main results

* `finrank_coordSpace`  : `finrank ℝ (coordSpace n) = n`.
* `vcDim_halfspace_le`   : `VCDim (Fin n → ℝ) (signClass (coordSpace n)) ≤ n` (the Dudley upper
  bound — the canonical application of `vcDim_signClass_le`).
* `vcDim_halfspace_eq`   : `VCDim (Fin n → ℝ) (signClass (coordSpace n)) = n` (sharpness: the `n`
  standard basis points are shattered by `±1`-weighted functionals).

## Proof idea

The coordinate functionals are the dual basis of the standard basis: evaluating a vanishing
combination `∑ i, gᵢ • coord i = 0` at the basis point `Pi.single j 1` isolates `gⱼ`, so the family
is linearly independent and its span has `finrank = n` (`finrank_span_eq_card`). Plugging into
Dudley's bound gives `VCDim ≤ n`. For the lower bound we shatter `{Pi.single i 1 | i : Fin n}`: a
labelling `f` is realised by `g = ∑ i, wᵢ • coord i` with `wᵢ = ±1` chosen by `f`, since
`g (Pi.single j 1) = wⱼ` and `0 < wⱼ ↔ f` is `true`. The affine version (`vcDim_affineHalfspace_le`)
adjoins the constant `1`, giving the `(n+1)`-dimensional space of inhomogeneous functionals.
-/

open scoped BigOperators

namespace FLT.Halfspace

/-- The `i`-th coordinate functional `x ↦ x i` on `Fin n → ℝ`, viewed as an element of the function
space `(Fin n → ℝ) → ℝ`. -/
def coord (n : ℕ) (i : Fin n) : (Fin n → ℝ) → ℝ := fun x => x i

/-- The **coordinate space**: the span of the `n` coordinate functionals `(fun x => x i)` inside
`(Fin n → ℝ) → ℝ`. This is the (dual) space of homogeneous linear functionals on `ℝⁿ`; its sign
class is exactly the family of homogeneous linear halfspaces. -/
noncomputable def coordSpace (n : ℕ) : Submodule ℝ ((Fin n → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (coord n))

/-- Evaluating the `i`-th coordinate functional at the `j`-th standard basis point gives the
identity matrix: `coord n i (Pi.single j 1) = if i = j then 1 else 0`. -/
theorem coord_single (n : ℕ) (i j : Fin n) :
    coord n i (Pi.single j (1 : ℝ) : Fin n → ℝ) = if i = j then 1 else 0 := by
  unfold coord
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- **The coordinate functionals are linearly independent.** They are the dual basis of the
standard basis; concretely, evaluating a vanishing combination at each standard basis point
`Pi.single j 1` isolates the `j`-th coefficient. -/
theorem linearIndependent_coord (n : ℕ) : LinearIndependent ℝ (coord n) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  -- Evaluate the vanishing combination `∑ i, g i • coord n i = 0` at `Pi.single j 1`.
  have hj := congrArg (fun (f : (Fin n → ℝ) → ℝ) => f (Pi.single j (1 : ℝ))) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
  -- The sum collapses to `g j` since `coord n i (Pi.single j 1) = [i = j]`.
  rw [Finset.sum_eq_single j] at hj
  · rwa [coord_single, if_pos rfl, mul_one] at hj
  · intro i _ hij
    rw [coord_single, if_neg hij, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The coordinate space is finite-dimensional (it is the span of a finite family). -/
instance finiteDimensional_coordSpace (n : ℕ) : FiniteDimensional ℝ (coordSpace n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- **The dimension of the coordinate space is `n`.** The coordinate functionals form the dual
basis of `ℝⁿ`, so their span has dimension `n`. -/
theorem finrank_coordSpace (n : ℕ) : Module.finrank ℝ (coordSpace n) = n := by
  unfold coordSpace
  rw [finrank_span_eq_card (linearIndependent_coord n), Fintype.card_fin]

/-- **VC dimension of homogeneous linear halfspaces: the Dudley upper bound.**

The class of homogeneous linear halfspaces `x ↦ (0 < ⟨w, x⟩)` in `ℝⁿ` has VC dimension at most `n`.
This is the canonical instance of Dudley's bound (`vcDim_signClass_le`): the underlying function
space is `coordSpace n`, of dimension `n`. (Cover 1965; Vapnik–Chervonenkis.) -/
theorem vcDim_halfspace_le (n : ℕ) :
    VCDim (Fin n → ℝ) (signClass (coordSpace n)) ≤ (n : WithTop ℕ) := by
  have h := vcDim_signClass_le (coordSpace n)
  rwa [finrank_coordSpace n] at h

/-! ## Sharpness: the standard basis points are shattered -/

/-- The `n` standard basis points `{Pi.single i 1 | i : Fin n}` of `ℝⁿ`. These are the witnesses
for the VC-dimension lower bound. -/
noncomputable def basisPoints (n : ℕ) : Finset (Fin n → ℝ) :=
  Finset.image (fun i => Pi.single i (1 : ℝ)) Finset.univ

/-- Each standard basis point lies in `basisPoints n`. -/
theorem single_mem_basisPoints (n : ℕ) (i : Fin n) :
    Pi.single i (1 : ℝ) ∈ basisPoints n :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- The map `i ↦ Pi.single i 1` is injective (the basis points are distinct). -/
theorem single_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => Pi.single i (1 : ℝ)) := by
  intro i j h
  by_contra hij
  have heval : (Pi.single i (1 : ℝ) : Fin n → ℝ) i = (Pi.single j (1 : ℝ) : Fin n → ℝ) i :=
    congrFun h i
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at heval
  exact one_ne_zero heval

/-- There are exactly `n` standard basis points. -/
theorem card_basisPoints (n : ℕ) : (basisPoints n).card = n := by
  unfold basisPoints
  rw [Finset.card_image_of_injective _ (single_injective n), Finset.card_univ, Fintype.card_fin]

/-- A `±1`-weighted coordinate functional belongs to the coordinate space. Concretely, for any
weights `w : Fin n → ℝ`, the functional `x ↦ ∑ i, w i * x i` is a member of `coordSpace n`. -/
theorem weighted_mem_coordSpace (n : ℕ) (w : Fin n → ℝ) :
    (fun x => ∑ i, w i * x i) ∈ coordSpace n := by
  have hsum : (fun x : Fin n → ℝ => ∑ i, w i * x i)
      = ∑ i : Fin n, w i • coord n i := by
    funext x
    simp [coord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- A weighted functional evaluated at a standard basis point returns that point's weight:
`(∑ i, w i * (Pi.single j 1) i) = w j`. -/
theorem weighted_single (n : ℕ) (w : Fin n → ℝ) (j : Fin n) :
    (∑ i, w i * (Pi.single j (1 : ℝ) : Fin n → ℝ) i) = w j := by
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, mul_one]
  · intro i _ hij; rw [Pi.single_eq_of_ne hij, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The standard basis points are shattered by homogeneous halfspaces.** Given any labelling, the
`±1`-weighted functional `g x = ∑ i, w i * x i` with `w i = ±1` selected by the label realises it:
`g (Pi.single j 1) = w j`, and `0 < w j` iff the label is `true`. -/
theorem shatters_basisPoints (n : ℕ) :
    Shatters (Fin n → ℝ) (signClass (coordSpace n)) (basisPoints n) := by
  classical
  intro f
  -- Weights: `+1` for `true`, `-1` for `false`, indexed by the basis point.
  let w : Fin n → ℝ := fun i => if f ⟨Pi.single i 1, single_mem_basisPoints n i⟩ then 1 else -1
  -- The realising halfspace `x ↦ decide (0 < ∑ i, w i * x i)`.
  refine ⟨fun x => decide (0 < ∑ i, w i * x i), ⟨(fun x => ∑ i, w i * x i),
    weighted_mem_coordSpace n w, rfl⟩, ?_⟩
  -- Verify the labelling on each basis point `x = Pi.single j 1`.
  rintro ⟨x, hx⟩
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
  -- The concept evaluated at `Pi.single j 1` is `decide (0 < w j)`.
  show decide (0 < ∑ i, w i * (Pi.single j (1 : ℝ) : Fin n → ℝ) i)
      = f ⟨Pi.single j 1, single_mem_basisPoints n j⟩
  rw [weighted_single n w j]
  -- `w j = +1` if the label is `true`, `-1` if `false`; in either case the sign decides correctly.
  by_cases hf : f ⟨Pi.single j 1, single_mem_basisPoints n j⟩ = true
  · have hwj : w j = 1 := by simp only [w]; rw [if_pos hf]
    rw [hwj, hf]; norm_num
  · rw [Bool.not_eq_true] at hf
    have hwj : w j = -1 := by simp only [w]; rw [if_neg (by simp [hf])]
    rw [hwj, hf]; norm_num

/-- **VC dimension of homogeneous linear halfspaces: the lower bound.** The `n` standard basis
points are shattered, so the VC dimension is at least `n`. -/
theorem vcDim_halfspace_ge (n : ℕ) :
    (n : WithTop ℕ) ≤ VCDim (Fin n → ℝ) (signClass (coordSpace n)) := by
  have h : ((basisPoints n).card : WithTop ℕ) ≤ VCDim (Fin n → ℝ) (signClass (coordSpace n)) :=
    le_iSup₂_of_le (basisPoints n) (shatters_basisPoints n) le_rfl
  rwa [card_basisPoints n] at h

/-- **VC dimension of homogeneous linear halfspaces is exactly `n`** (Cover 1965;
Vapnik–Chervonenkis). The class `signClass (coordSpace n)` of homogeneous linear halfspaces of `ℝⁿ`
has VC dimension equal to the ambient dimension `n`: the Dudley bound gives `≤ n`, and the `n`
standard basis points are shattered, giving `≥ n`. -/
theorem vcDim_halfspace_eq (n : ℕ) :
    VCDim (Fin n → ℝ) (signClass (coordSpace n)) = (n : WithTop ℕ) :=
  le_antisymm (vcDim_halfspace_le n) (vcDim_halfspace_ge n)

/-! ## Affine halfspaces -/

/-- The constant functional `x ↦ 1` on `Fin n → ℝ`. Adjoining it to the coordinates yields the
affine (inhomogeneous) functionals `x ↦ ⟨w, x⟩ + b`. -/
def constFun (n : ℕ) : (Fin n → ℝ) → ℝ := fun _ => 1

/-- The combined family indexing the `n` coordinate functionals together with the constant `1`,
indexed by `Fin n ⊕ Unit`. -/
def affineCoord (n : ℕ) : (Fin n ⊕ Unit) → ((Fin n → ℝ) → ℝ) :=
  Sum.elim (coord n) (fun _ => constFun n)

/-- The **affine coordinate space**: the span of the `n` coordinate functionals together with the
constant `1`. Its sign class is the family of *affine* (inhomogeneous) linear halfspaces
`x ↦ (0 < ⟨w, x⟩ + b)` of `ℝⁿ`. -/
noncomputable def affineCoordSpace (n : ℕ) : Submodule ℝ ((Fin n → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (affineCoord n))

/-- **The coordinate functionals together with the constant `1` are linearly independent.**
Evaluating a vanishing combination at the zero vector isolates the constant's coefficient (all
coordinates vanish there); evaluating at `Pi.single j 1` then isolates the `j`-th coefficient. -/
theorem linearIndependent_affineCoord (n : ℕ) : LinearIndependent ℝ (affineCoord n) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- First evaluate the relation at the zero vector to pin down the constant's coefficient.
  have hg0 := congrFun hg (0 : Fin n → ℝ)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Fintype.sum_sum_type] at hg0
  -- At `x = 0`, every coordinate functional vanishes, so only the constant term survives.
  have hconst : g (Sum.inr ()) = 0 := by
    simpa [affineCoord, constFun, coord] using hg0
  -- Now show every coefficient vanishes; the constant one is already handled.
  rintro (j | u)
  · -- Coordinate coefficient: evaluate the relation at `Pi.single j 1` and split the sum.
    have hgj := congrFun hg (Pi.single j (1 : ℝ) : Fin n → ℝ)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_sum_type] at hgj
    -- The `Unit` block is `g (inr ()) * 1 = 0`; the `Fin n` block collapses to `g (inl j)`.
    rw [Finset.sum_eq_single j] at hgj
    · simp only [affineCoord, Sum.elim_inl, Sum.elim_inr, constFun, coord, Pi.single_eq_same,
        mul_one, hconst, Finset.sum_const] at hgj
      simpa using hgj
    · intro i _ hij
      simp only [affineCoord, Sum.elim_inl, coord]
      rw [Pi.single_eq_of_ne hij, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  · cases u; exact hconst

/-- The affine coordinate space is finite-dimensional. -/
instance finiteDimensional_affineCoordSpace (n : ℕ) :
    FiniteDimensional ℝ (affineCoordSpace n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- **The dimension of the affine coordinate space is `n + 1`.** -/
theorem finrank_affineCoordSpace (n : ℕ) :
    Module.finrank ℝ (affineCoordSpace n) = n + 1 := by
  unfold affineCoordSpace
  rw [finrank_span_eq_card (linearIndependent_affineCoord n)]
  simp [Fintype.card_sum, Fintype.card_fin]

/-- **VC dimension of affine linear halfspaces: the Dudley upper bound.**

The class of affine (inhomogeneous) halfspaces `x ↦ (0 < ⟨w, x⟩ + b)` in `ℝⁿ` has VC dimension at
most `n + 1`. This is the canonical instance of Dudley's bound for the `(n+1)`-dimensional space of
affine functionals. (Cover 1965; Vapnik–Chervonenkis.) -/
theorem vcDim_affineHalfspace_le (n : ℕ) :
    VCDim (Fin n → ℝ) (signClass (affineCoordSpace n)) ≤ ((n + 1 : ℕ) : WithTop ℕ) := by
  have h := vcDim_signClass_le (affineCoordSpace n)
  rwa [finrank_affineCoordSpace n] at h

end FLT.Halfspace
