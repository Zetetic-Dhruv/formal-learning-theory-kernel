import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Binary Matrix VC Dimension and Sauer-Shelah

Pure combinatorics: VC dimension on binary matrices, bridged to Mathlib's
`Finset.Shatters` infrastructure. No learning theory types.
-/

open Classical Finset

universe u

/-- An `m x n` binary matrix, represented as `Fin m -> Fin n -> Bool`. -/
abbrev BinaryMatrix (m n : ℕ) := Fin m → Fin n → Bool

namespace BinaryMatrix

/-- A binary matrix `M` shatters a column set `S` if for every subset `t ⊆ S`,
    there is a row `i` whose `true` columns within `S` are exactly `t`. -/
def shatters {m n : ℕ} (M : BinaryMatrix m n) (S : Finset (Fin n)) : Prop :=
  ∀ t ⊆ S, ∃ i : Fin m, ∀ j ∈ S, (M i j = true) ↔ (j ∈ t)

/-- Transpose of a binary matrix. -/
def transpose {m n : ℕ} (M : BinaryMatrix m n) : BinaryMatrix n m :=
  fun j i => M i j

/-- Convert a binary matrix to a Finset family: each row becomes the set of
    columns where that row is `true`. -/
def toFinsetFamily {m n : ℕ} (M : BinaryMatrix m n) :
    Finset (Finset (Fin n)) :=
  Finset.univ.image (fun i : Fin m => Finset.univ.filter (fun j => M i j = true))

/-- The VC dimension of a binary matrix, defined via the Mathlib Finset family. -/
noncomputable def vcDim {m n : ℕ} (M : BinaryMatrix m n) : ℕ :=
  M.toFinsetFamily.vcDim

/-- Our `shatters` coincides with Mathlib's `Finset.Shatters` on the associated family. -/
theorem shatters_iff {m n : ℕ} (M : BinaryMatrix m n) (S : Finset (Fin n)) :
    M.shatters S ↔ M.toFinsetFamily.Shatters S := by
  constructor
  · -- Forward: our definition → Mathlib's
    intro hM t ht
    obtain ⟨i, hi⟩ := hM t ht
    refine ⟨Finset.univ.filter (fun j => M i j = true), ?_, ?_⟩
    · simp only [toFinsetFamily, mem_image, mem_univ, true_and]
      exact ⟨i, rfl⟩
    · ext j
      simp only [mem_inter, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hj, hMij⟩
        exact (hi j hj).mp hMij
      · intro hjt
        have hjS := ht hjt
        exact ⟨hjS, (hi j hjS).mpr hjt⟩
  · -- Backward: Mathlib's → our definition
    intro hS t ht
    obtain ⟨u, hu, hut⟩ := hS ht
    simp only [toFinsetFamily, mem_image, mem_univ, true_and] at hu
    obtain ⟨i, rfl⟩ := hu
    refine ⟨i, fun j hj => ?_⟩
    constructor
    · intro hMij
      have : j ∈ S ∩ Finset.univ.filter (fun j => M i j = true) := by
        simp only [mem_inter, mem_filter, mem_univ, true_and]
        exact ⟨hj, hMij⟩
      rw [hut] at this
      exact this
    · intro hjt
      have : j ∈ S ∩ Finset.univ.filter (fun j => M i j = true) := by
        rw [hut]; exact hjt
      simp only [mem_inter, mem_filter, mem_univ, true_and] at this
      exact this.2

/-- Two `Bool`-valued functions on `Fin n` that agree on which indices are `true`
    (as witnessed by equal `univ.filter`) are equal. -/
theorem bool_fun_eq_of_filter_eq {n : ℕ} (f g : Fin n → Bool)
    (h : Finset.univ.filter (fun j => f j = true) =
         Finset.univ.filter (fun j => g j = true)) :
    f = g := by
  funext j
  by_cases hf : f j = true <;> by_cases hg : g j = true
  · rw [hf, hg]
  · exfalso
    have : j ∈ Finset.univ.filter (fun j => f j = true) := by
      simp [hf]
    rw [h] at this
    simp [hg] at this
  · exfalso
    have : j ∈ Finset.univ.filter (fun j => g j = true) := by
      simp [hg]
    rw [← h] at this
    simp [hf] at this
  · simp only [Bool.not_eq_true] at hf hg
    rw [hf, hg]

/-- **Sauer-Shelah lemma for binary matrices**: the number of distinct rows in the
    Finset family is bounded by the sum of binomial coefficients up to the VC dimension. -/
theorem card_toFinsetFamily_le {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (hd : M.toFinsetFamily.vcDim ≤ d) :
    M.toFinsetFamily.card ≤ ∑ k ∈ Finset.Iic d, n.choose k := by
  calc M.toFinsetFamily.card
      _ ≤ M.toFinsetFamily.shatterer.card := card_le_card_shatterer _
      _ ≤ ∑ k ∈ Iic M.toFinsetFamily.vcDim, (Fintype.card (Fin n)).choose k :=
          card_shatterer_le_sum_vcDim
      _ = ∑ k ∈ Iic M.toFinsetFamily.vcDim, n.choose k := by
          simp [Fintype.card_fin]
      _ ≤ ∑ k ∈ Iic d, n.choose k := by
          have hsub : Iic M.toFinsetFamily.vcDim ⊆ Iic d := Iic_subset_Iic.mpr hd
          exact le_trans (le_refl _)
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))

end BinaryMatrix
