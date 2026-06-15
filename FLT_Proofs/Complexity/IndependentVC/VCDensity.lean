/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.GrowthMul
import FLT_Proofs.Complexity.IndependentVC.UnionGrowth
import FLT_Proofs.Complexity.IndependentVC.GrowthMono
import FLT_Proofs.Complexity.IndependentVC.GrowthPoly
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# VC density and its subadditivity

The VC density of a class is the infimum of the polynomial degrees that eventually bound its growth
function. We work with the degree-bound predicate `HasPolyDegree C r` (growth eventually `≤ K · m^r`),
which is the object on which density behaves additively.

The headline is `hasPolyDegree_booleanComb`: a pointwise Boolean combination of classes of degrees
`r i` has degree `∑ r i`. This is the sense in which VC *density* is **subadditive** — sharply unlike
VC *dimension*, whose `k`-fold union can grow like `Θ(d k log k)` and so admits no subadditive bound
(`vcDim_not_subadditive_collectionUnion`). The proof is the product growth bound
`growthFunction_booleanComb_le_prod` followed by `m^{r₁} ⋯ m^{r_k} = m^{∑ rᵢ}`. The collection union
takes the maximum degree, and finite VC dimension yields a finite degree.

Reference: M. Aschenbrenner, A. Dolich, D. Haskell, D. Macpherson, S. Starchenko, *Vapnik–Chervonenkis
density in some theories without the independence property, I*, Trans. Amer. Math. Soc. 368 (2016).

The scalar `vcDensity C := sInf {r | HasPolyDegree C r}` packages the degree predicate into a single
real invariant, and `vcDensity_union_le_max` shows it is **union-subadditive**: the density of a
collection union is bounded by the maximum of the two densities. This is the rank-compatible scalar
surrogate that succeeds exactly where the VC *dimension* fails its submodular/subadditive axiom
(`vcDim_not_polymatroid_rank`): the dimension's two-class union budget carries a sharp `+1` defect
(`vcDim_union_le`), so it is not a polymatroid rank, whereas the density one scale below it *is*
max-bounded under union.

## Main results

* `HasPolyDegree`: the eventual polynomial-degree bound on the growth function.
* `hasPolyDegree_booleanComb`: VC density is subadditive under Boolean combination.
* `hasPolyDegree_union`: the collection union has degree the maximum of the two.
* `exists_hasPolyDegree_of_vcDim_lt_top`: finite VC dimension gives a finite degree.
* `hasPolyDegree_mono`: the degree set is upward-closed (an up-set in `ℝ`).
* `vcDensity`: the scalar VC density, the infimal polynomial growth degree.
* `vcDensity_union_le_max`: VC density is union-subadditive (max-bounded).
-/

open Filter Finset

universe u

variable {X : Type u}

/-- `HasPolyDegree C r` means the growth function of `C` is eventually bounded by `K · m^r` for some
constant `K`. The VC density of `C` is the infimum of the `r` for which this holds. -/
def HasPolyDegree (C : ConceptClass X Bool) (r : ℝ) : Prop :=
  ∃ K : ℝ, ∀ᶠ m : ℕ in atTop, (GrowthFunction X C m : ℝ) ≤ K * (m : ℝ) ^ r

/-- A product of real powers of a fixed positive base is the power at the summed exponent. -/
theorem prod_rpow_eq_rpow_sum {ι : Type*} {s : Finset ι} {x : ℝ} (hx : 0 < x) {f : ι → ℝ} :
    ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, Real.rpow_add hx]

/-- **VC density is subadditive under Boolean combination.** If each `C i` has degree `r i`, then the
pointwise Boolean combination `booleanComb φ C` has degree `∑ r i`, uniformly over the combiner `φ`. -/
theorem hasPolyDegree_booleanComb {k : ℕ} (φ : (Fin k → Bool) → Bool)
    (C : Fin k → ConceptClass X Bool) (r : Fin k → ℝ) (h : ∀ i, HasPolyDegree (C i) (r i)) :
    HasPolyDegree (booleanComb φ C) (∑ i, r i) := by
  choose K hK using h
  refine ⟨∏ i, K i, ?_⟩
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i, (GrowthFunction X (C i) m : ℝ) ≤ K i * (m : ℝ) ^ r i :=
    eventually_all.mpr hK
  filter_upwards [hall, eventually_ge_atTop 1] with m hm hm1
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
  calc (GrowthFunction X (booleanComb φ C) m : ℝ)
      ≤ ((∏ i, GrowthFunction X (C i) m : ℕ) : ℝ) := by
        exact_mod_cast growthFunction_booleanComb_le_prod φ C m
    _ = ∏ i, (GrowthFunction X (C i) m : ℝ) := by push_cast; ring
    _ ≤ ∏ i, K i * (m : ℝ) ^ r i := Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hm i)
    _ = (∏ i, K i) * (m : ℝ) ^ ∑ i, r i := by rw [Finset.prod_mul_distrib, prod_rpow_eq_rpow_sum hpos]

/-- **The collection union has degree the maximum of the two.** The growth function of `C ∪ D` is at
most the sum of the growth functions, so it is bounded at the larger degree. -/
theorem hasPolyDegree_union {C D : ConceptClass X Bool} {rC rD : ℝ}
    (hC : HasPolyDegree C rC) (hD : HasPolyDegree D rD) :
    HasPolyDegree (C ∪ D) (max rC rD) := by
  obtain ⟨KC, hKC⟩ := hC
  obtain ⟨KD, hKD⟩ := hD
  refine ⟨|KC| + |KD|, ?_⟩
  filter_upwards [hKC, hKD, eventually_ge_atTop 1] with m hmC hmD hm1
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hpow : ∀ (K : ℝ) {e : ℝ}, e ≤ max rC rD →
      K * (m : ℝ) ^ e ≤ |K| * (m : ℝ) ^ max rC rD := fun K {e} he =>
    calc K * (m : ℝ) ^ e ≤ |K| * (m : ℝ) ^ e :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
      _ ≤ |K| * (m : ℝ) ^ max rC rD :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm1' he) (abs_nonneg _)
  calc (GrowthFunction X (C ∪ D) m : ℝ)
      ≤ (GrowthFunction X C m : ℝ) + GrowthFunction X D m := by
        exact_mod_cast growthFunction_union_le_add C D m
    _ ≤ KC * (m : ℝ) ^ rC + KD * (m : ℝ) ^ rD := add_le_add hmC hmD
    _ ≤ |KC| * (m : ℝ) ^ max rC rD + |KD| * (m : ℝ) ^ max rC rD :=
        add_le_add (hpow KC (le_max_left _ _)) (hpow KD (le_max_right _ _))
    _ = (|KC| + |KD|) * (m : ℝ) ^ max rC rD := by ring

/-- **Finite VC dimension gives a finite degree.** A class of finite VC dimension has a finite VC
density: its growth function is eventually polynomial. -/
theorem exists_hasPolyDegree_of_vcDim_lt_top {C : ConceptClass X Bool} (h : VCDim X C < ⊤) :
    ∃ r : ℝ, HasPolyDegree C r := by
  obtain ⟨K, d, hKd⟩ := vcDim_finite_imp_growth_poly h
  refine ⟨(d : ℝ), K, ?_⟩
  filter_upwards [hKd] with m hm
  rwa [Real.rpow_natCast]

/-- **The degree set is upward-closed.** If `C` has degree `r` and `r ≤ r'`, then `C` has degree `r'`:
for `m ≥ 1` the bound `m^r ≤ m^{r'}` lifts the eventual polynomial bound. Hence `{r | HasPolyDegree C r}`
is an up-set in `ℝ`, the structural fact underlying the infimal characterisation of VC density. -/
theorem hasPolyDegree_mono {C : ConceptClass X Bool} {r r' : ℝ}
    (h : HasPolyDegree C r) (hr : r ≤ r') : HasPolyDegree C r' := by
  obtain ⟨K, hK⟩ := h
  refine ⟨|K|, ?_⟩
  filter_upwards [hK, eventually_ge_atTop 1] with m hm hm1
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  calc (GrowthFunction X C m : ℝ)
      ≤ K * (m : ℝ) ^ r := hm
    _ ≤ |K| * (m : ℝ) ^ r :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |K| * (m : ℝ) ^ r' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm1' hr) (abs_nonneg _)

/-- **The union has every degree of `C`.** Since `GrowthFunction C ≤ GrowthFunction (C ∪ D)`, any
degree bound for the union is a degree bound for `C`. Thus `{r | HasPolyDegree (C ∪ D) r}` is contained
in `{r | HasPolyDegree C r}` (and symmetrically in `D`'s degree set). -/
theorem hasPolyDegree_of_union_left {C D : ConceptClass X Bool} {r : ℝ}
    (h : HasPolyDegree (C ∪ D) r) : HasPolyDegree C r := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, ?_⟩
  filter_upwards [hK] with m hm
  have hmono : (GrowthFunction X C m : ℝ) ≤ GrowthFunction X (C ∪ D) m := by
    exact_mod_cast growthFunction_mono Set.subset_union_left m
  linarith

/-- The symmetric containment: a degree of the union is a degree of `D`. -/
theorem hasPolyDegree_of_union_right {C D : ConceptClass X Bool} {r : ℝ}
    (h : HasPolyDegree (C ∪ D) r) : HasPolyDegree D r := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, ?_⟩
  filter_upwards [hK] with m hm
  have hmono : (GrowthFunction X D m : ℝ) ≤ GrowthFunction X (C ∪ D) m := by
    exact_mod_cast growthFunction_mono Set.subset_union_right m
  linarith

/-- The **VC density** of a concept class: the infimal polynomial growth degree, i.e. the infimum of
the exponents `r` for which the growth function is eventually bounded by `K · m^r`. This is the scalar
invariant living one scale below the VC dimension. -/
noncomputable def vcDensity (C : ConceptClass X Bool) : ℝ := sInf {r | HasPolyDegree C r}

/-- The degree set is nonempty for a class of finite VC dimension. -/
theorem degreeSet_nonempty {C : ConceptClass X Bool} (hC : VCDim X C < ⊤) :
    {r | HasPolyDegree C r}.Nonempty :=
  (exists_hasPolyDegree_of_vcDim_lt_top hC).imp (fun _ h => h)

/-- **VC density is union-subadditive** (max-bounded) — the rank-compatible scalar surrogate that
succeeds exactly where the VC *dimension* rank fails its submodular/subadditive axiom. For finite-VC
classes `C, D`, the density of the collection union `C ∪ D` is at most the maximum of the two densities.

The proof is an ε-approximation: each `vcDensity C + ε` is an attainable degree of `C` (the degree set
is an up-set, `hasPolyDegree_mono`, approached from above via `exists_lt_of_csInf_lt`), so by
`hasPolyDegree_union` the union attains `max (vcDensity C + ε) (vcDensity D + ε) = max .. .. + ε`, and
`csInf_le` gives `vcDensity (C ∪ D) ≤ max .. .. + ε` for all `ε > 0`. The degenerate case where the
union's degree set is unbounded below is forced — via the containments `hasPolyDegree_of_union_left/right`
— to make all three densities the junk value `0`, where the bound is immediate. -/
theorem vcDensity_union_le_max {C D : ConceptClass X Bool}
    (hC : VCDim X C < ⊤) (hD : VCDim X D < ⊤) :
    vcDensity (C ∪ D) ≤ max (vcDensity C) (vcDensity D) := by
  set SC := {r | HasPolyDegree C r} with hSC
  set SD := {r | HasPolyDegree D r} with hSD
  set SU := {r | HasPolyDegree (C ∪ D) r} with hSU
  -- The union's degree set is contained in each of the two single-class degree sets.
  have hsubC : SU ⊆ SC := fun r hr => hasPolyDegree_of_union_left hr
  have hsubD : SU ⊆ SD := fun r hr => hasPolyDegree_of_union_right hr
  by_cases hbdd : BddBelow SU
  · -- Main case: the union's degree set is bounded below, so `csInf_le` applies.
    apply le_of_forall_pos_le_add
    intro ε hε
    have hSCne : SC.Nonempty := degreeSet_nonempty hC
    have hSDne : SD.Nonempty := degreeSet_nonempty hD
    have hltC : sInf SC < vcDensity C + ε := by
      have : vcDensity C < vcDensity C + ε := by linarith
      simpa [vcDensity, hSC] using this
    have hltD : sInf SD < vcDensity D + ε := by
      have : vcDensity D < vcDensity D + ε := by linarith
      simpa [vcDensity, hSD] using this
    obtain ⟨rC, hrCmem, hrClt⟩ := exists_lt_of_csInf_lt hSCne hltC
    obtain ⟨rD, hrDmem, hrDlt⟩ := exists_lt_of_csInf_lt hSDne hltD
    -- Lift the witnesses up to `vcDensity C + ε`, `vcDensity D + ε` (up-set closure).
    have hpC : HasPolyDegree C (vcDensity C + ε) := hasPolyDegree_mono hrCmem (le_of_lt hrClt)
    have hpD : HasPolyDegree D (vcDensity D + ε) := hasPolyDegree_mono hrDmem (le_of_lt hrDlt)
    have hunion : HasPolyDegree (C ∪ D) (max (vcDensity C + ε) (vcDensity D + ε)) :=
      hasPolyDegree_union hpC hpD
    have hmemU : max (vcDensity C) (vcDensity D) + ε ∈ SU := by
      have heq : max (vcDensity C + ε) (vcDensity D + ε)
          = max (vcDensity C) (vcDensity D) + ε := by rw [max_add_add_right]
      rw [heq] at hunion
      exact hunion
    calc vcDensity (C ∪ D) = sInf SU := by rw [vcDensity, ← hSU]
      _ ≤ max (vcDensity C) (vcDensity D) + ε := csInf_le hbdd hmemU
  · -- Degenerate case: `SU` unbounded below ⟹ so are `SC, SD` (supersets), all densities are `0`.
    have hncC : ¬ BddBelow SC := fun h => hbdd (h.mono hsubC)
    have hncD : ¬ BddBelow SD := fun h => hbdd (h.mono hsubD)
    have hU0 : vcDensity (C ∪ D) = 0 := by
      rw [vcDensity, ← hSU]; exact Real.sInf_of_not_bddBelow hbdd
    have hC0 : vcDensity C = 0 := by
      rw [vcDensity, ← hSC]; exact Real.sInf_of_not_bddBelow hncC
    have hD0 : vcDensity D = 0 := by
      rw [vcDensity, ← hSD]; exact Real.sInf_of_not_bddBelow hncD
    rw [hU0, hC0, hD0]; simp
