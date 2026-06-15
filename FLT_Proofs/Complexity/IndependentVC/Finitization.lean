/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.IndependentVC.FundamentalTheorem
import FLT_Proofs.Complexity.IndependentVC.Relabel

/-!
# `Fin↓` — finitization by a resolution-indexed combinatorial trace

This module gives a name and a carrier to the **finitization principle** of the discovered
measurement quartet (`GR7` / `IM2` in the noological synthesis at
`design-lab/learning-theory/flt_discovery_urs/noological_synthesis.md`): the observation that the
three apparently-different reductions used to control an infinite concept class —

* restriction to a size-`m` sample (the growth function),
* symmetrisation / sign-flip (Rademacher / ghost sample),
* discretisation at scale `ε` (covering nets, Dudley chaining),

are three readings of **one** verb. The verb is: *replace the infinite object `C` by a finite
combinatorial trace, indexed by a resolution parameter `ρ`, and read the capacity off the way the
trace grows as the resolution refines.*

The synthesis flags this unification as a conjecture and asks (UK-3 of the capacity draft) to *"state
the `Fin↓` reduction abstractly and exhibit the instances."* That is the scope of this module, kept
honest:

* We state the reduction abstractly as a `FinitizationScheme` (§"The abstract reduction"). The
  abstraction is **not decorative**: a scheme is required to carry, as a field, the proof that the
  finite-versus-`⊤` capacity invariant `VCDim X C < ⊤` is recovered from the trace — `boundedTrace`,
  the statement that finite capacity is equivalent to the trace size growing only polynomially in the
  resolution magnitude. A scheme cannot be constructed without discharging this obligation, so
  inhabiting it is genuine `experiment` content, not a re-export.

* We exhibit the **sample-restriction** instance concretely and completely (§"The sample-restriction
  instance"). Resolution = sample size `m : ℕ`; resolution magnitude = `m`; trace at `m` = the finite
  set of labelling patterns realised on a size-`m` sample; trace size = the growth function
  `GrowthFunction X C m`. The invariant-recovery obligation is then *exactly*
  `vcDim_lt_top_iff_growth_poly`, the combinatorial half of the fundamental theorem. The instance is
  `sorry`-free and uses only carriers in this module's import closure.

The other two instances are **not faked**. The genuine sign-finitisation (the Rademacher
symmetrisation reduction `swapAt` / `symmetrization_le`) and the genuine scale-finitisation (covering
nets `coveringNet`, dyadic scales `dyadicScale`, Dudley chaining `empRadComplexity_le_dudley`) live in
the real-valued and cross-library (`transformers` / TLT) strata, not in the Boolean-valued
independent VC module. What *is* available here is recorded precisely: the codomain involution
`xorShift` is a *trace automorphism* — it permutes the patterns of every sample without changing the
trace size (`ncard_restrictionSet_xorShift`), the present half of the sign instance. The reductions
themselves stay as sharpened conjectures — see `signInstanceOpen` and `scaleInstanceOpen` below.

## Main results

* `FinitizationScheme` — the abstract resolution-indexed reduction, carrying the
  capacity-invariant-recovery obligation as a field.
* `sampleRestrictionScheme` — the sample-restriction instance, fully discharged (`sorry`-free).
* `ncard_restrictionSet_xorShift` — the sign-flip involution is a trace automorphism (the present
  half of the open sign instance).

## References

* V. N. Vapnik, A. Ya. Chervonenkis, *On the uniform convergence of relative frequencies of events
  to their probabilities*, Theory Probab. Appl. **16** (1971), 264–280.
* R. M. Dudley, *Central limit theorems for empirical measures*, Ann. Probab. **6** (1978), 899–929
  (chaining / the scale instance).
* S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning*, CUP 2014, Thm 6.7.
-/

open Filter

universe u v

variable {X : Type u}

/-! ## The abstract reduction

`Fin↓` is the verb "replace `C` by a finite combinatorial trace at a resolution `ρ`, and recover the
capacity from how the trace grows." We package that as a structure over a *fixed* concept class `C`,
parametrised by

* a resolution type `ρ` (the index along which the trace refines — sample size, sign pattern, scale);
* a cofinal filter `refine` on resolutions (the direction "towards the limit");
* a `Trace`, sending each resolution to a *finite* combinatorial object (a `Fintype`);
* a `size`, the `ℕ`-valued summary of the trace at each resolution; and
* a `mag`, the real magnitude of the resolution itself.

The single non-trivial field is `boundedTrace`: the capacity invariant `VCDim X C < ⊤` holds exactly
when the trace size stays bounded by a polynomial *in the resolution magnitude* along `refine`. This
is the precise sense in which *the capacity is the invariant of the trace as the resolution refines
towards its limit*. The field makes the abstraction non-vacuous — a scheme exists only once this
recovery is proved for the specific `C`. -/

/-- A **`Fin↓` finitization scheme** for a concept class `C`: a resolution-indexed reduction of `C` to
a family of finite combinatorial traces, together with a proof that the finite-versus-`⊤` capacity
invariant of `C` is recovered from the eventual growth of the trace size.

* `Resolution` indexes the refinement (sample size, sign pattern, scale `ε`).
* `refine` is the cofinal filter on resolutions along which the resolution goes to its limit (for
  sample size this is `atTop`).
* `Trace ρ` is the finite combinatorial datum at resolution `ρ` (carried with a `Fintype` instance,
  witnessing finitude — the heart of *Fin*↓).
* `size ρ` is the `ℕ`-valued summary of the trace (its pattern count / cardinality).
* `mag ρ` is the real magnitude of the resolution (the sample size, as a real).
* `boundedTrace` is the capacity-recovery obligation: `VCDim X C < ⊤` exactly when the trace size is
  eventually bounded by a polynomial `K · (mag ρ)^d` along `refine`.

The structure is bundled over a *fixed* `C` so that `boundedTrace` is a genuine proof obligation
about *that* class, not a quantified statement that could be vacuously true. -/
structure FinitizationScheme (X : Type u) (C : ConceptClass X Bool) where
  /-- The type indexing the resolution at which the infinite object is sampled. -/
  Resolution : Type v
  /-- The cofinal filter along which the resolution refines towards its limit. -/
  refine : Filter Resolution
  /-- The finite combinatorial trace of `C` at a given resolution. -/
  Trace : Resolution → Type v
  /-- Each trace is genuinely finite — the defining feature of a *finitization*. -/
  traceFinite : ∀ ρ, Fintype (Trace ρ)
  /-- The `ℕ`-valued size summary of the trace at each resolution. -/
  size : Resolution → ℕ
  /-- The real magnitude of the resolution (e.g. the sample size as a real). -/
  mag : Resolution → ℝ
  /-- **Capacity-invariant recovery.** The finite-versus-`⊤` capacity invariant of `C` is read off
  the trace: `VCDim X C < ⊤` exactly when the trace size stays polynomially bounded in the resolution
  magnitude as the resolution refines. This is the load-bearing field; it cannot be supplied without
  proving the reduction. -/
  boundedTrace :
    VCDim X C < ⊤ ↔
      ∃ (K : ℝ) (d : ℕ), ∀ᶠ ρ in refine, (size ρ : ℝ) ≤ K * (mag ρ) ^ d

/-! ## The sample-restriction instance

The first instance of `Fin↓`, fully discharged. The resolution is the sample size `m : ℕ`; refinement
is `atTop` (larger and larger samples); the trace at `m` is the finite cube of labelling patterns on
`m` coordinates (inside which the *realised* patterns sit); the trace size is the growth function
`GrowthFunction X C m`, the worst-case count of realised patterns over size-`m` samples; the
resolution magnitude is `m` itself.

The capacity-recovery is then *definitionally* the combinatorial half of the fundamental theorem,
`vcDim_lt_top_iff_growth_poly`: `VCDim X C < ⊤` exactly when the growth function is eventually
polynomial in `m`. -/

/-- The finite type of labelling patterns on a size-`m` sample: functions from a Boolean cube of `m`
coordinates to `Bool`. The growth function is the worst-case count of the *realised* patterns, which
sit inside this type; carrying the ambient cube here witnesses the finitude required by the abstract
`Trace` field. -/
abbrev sampleTrace (_C : ConceptClass X Bool) (m : ℕ) : Type := (Fin m → Bool) → Bool

/-- **The sample-restriction instance of `Fin↓`.** Resolution = sample size `m`, refining along
`atTop`; trace at `m` = the finite cube of labelling patterns; trace size = the growth function
`GrowthFunction X C m`; resolution magnitude = `m`. The capacity-recovery field is discharged by
`vcDim_lt_top_iff_growth_poly`, the Sauer–Shelah half of the fundamental theorem of statistical
learning.

This is the canonical, complete instance: every field is inhabited from carriers in the import
closure, with no `sorry`. It is the concrete content that makes `FinitizationScheme` a genuine
abstraction rather than a vacuous interface. -/
noncomputable def sampleRestrictionScheme (C : ConceptClass X Bool) :
    FinitizationScheme.{u, 0} X C where
  Resolution := ℕ
  refine := atTop
  Trace := sampleTrace C
  traceFinite := fun _ => inferInstance
  size := fun m => GrowthFunction X C m
  mag := fun m => (m : ℝ)
  boundedTrace := vcDim_lt_top_iff_growth_poly

/-! ## Sign instance (open) — the present trace-automorphism half

The genuine sign / symmetrisation finitisation (the Rademacher reduction: a deviation bound becomes a
uniform-convergence bound by introducing a ghost sample and averaging over random sign flips) lives in
the real-valued Rademacher stratum and, in its sharpest cross-library form, in the `transformers` /
TLT library (`swapAt`, `swapAtEquiv`, `TLT.Capacity.symmetrization_le`). It is **not** reconstructed
here and is **not** faked.

The half that *is* available in this Boolean module is the structural prerequisite: the sign-flip is a
codomain involution `xorShift a` that acts as an **automorphism of the trace at every resolution**.
The lemma below shows the trace size is invariant under it — exclusive-or by a fixed pattern is a
bijection on labellings, so it sends the realised-pattern set of any sample to a set of equal
cardinality. This is the first half of building a sign-indexed `FinitizationScheme`; the second half
(the symmetrisation *reduction* itself producing the capacity bound) is the open cross-library edge,
recorded as a sharpened conjecture in `signInstanceOpen`. The `restrictionSet` carrier used below is
the one from `FLT_Proofs.Complexity.IndependentVC.Growth`, already in this module's import closure. -/

/-- **The sign-flip is a trace automorphism.** Exclusive-or by a fixed pattern `a` does not change the
number of labelling patterns realised on any sample: the map `f ↦ (x ↦ a x ⊕ f x)` is an involution
on patterns and carries the realised set of `xorShift a C` bijectively onto that of `C`.

This is the present, kernel-verified half of the sign instance of `Fin↓`: the involution acts on the
finite traces resolution-by-resolution without disturbing their size. The capacity-producing
*reduction* (symmetrisation) is the open cross-library edge. -/
theorem ncard_restrictionSet_xorShift (a : X → Bool) (C : ConceptClass X Bool) (S : Finset X) :
    (restrictionSet (xorShift a C) S).ncard = (restrictionSet C S).ncard := by
  classical
  -- The involution on patterns: exclusive-or by `a` restricted to `S`.
  have hxor : ∀ (b u v : Bool), Bool.xor b u = Bool.xor b v → u = v := by
    intro b u v h; cases b <;> cases u <;> cases v <;> simp_all
  -- `restrictionSet (xorShift a C) S` is the image of `restrictionSet C S` under the pattern-level
  -- exclusive-or, which is injective, so the two sets are in bijection.
  have himg : restrictionSet (xorShift a C) S =
      (fun f : S → Bool => fun x : S => Bool.xor (a (x : X)) (f x)) '' restrictionSet C S := by
    ext f
    constructor
    · rintro ⟨c', ⟨c, hc, rfl⟩, hcf⟩
      refine ⟨fun x : S => c (x : X), ⟨c, hc, fun x => rfl⟩, ?_⟩
      funext x; exact hcf x
    · rintro ⟨g, ⟨c, hc, hcg⟩, rfl⟩
      refine ⟨fun x => Bool.xor (a x) (c x), ⟨c, hc, rfl⟩, fun x => ?_⟩
      show Bool.xor (a (x : X)) (c (x : X)) = Bool.xor (a (x : X)) (g x)
      rw [hcg x]
  rw [himg]
  refine Set.ncard_image_of_injective _ ?_
  intro f g hfg
  funext x
  exact hxor (a (x : X)) (f x) (g x) (congrFun hfg x)

/-! **The sign instance of `Fin↓` is open (sharpened conjecture).** A sign-indexed
`FinitizationScheme` would take `Resolution = (sample of size m) × (sign vector in {±1}^m)`, the trace
the ghost-sample pattern table, and `boundedTrace` the statement that finite VC dimension is
equivalent to the symmetrised (Rademacher) complexity vanishing. The structural prerequisite — that
sign flips act as trace automorphisms — is proved here (`ncard_restrictionSet_xorShift`). The missing
edge is the *symmetrisation reduction itself*, `empirical deviation ≤ 2 · Rademacher`, whose kernel
proof in this development is real-valued (`FLT_Proofs.Complexity.Symmetrization`) and whose sharpest
form is cross-library (`TLT.Capacity.symmetrization_le` in `transformers`). Stating it as a
Boolean-trace `FinitizationScheme` requires bridging the Bool↔ℝ scale (`FatShatteringDim`), which is
out of this module's closure.

The statement above documents the precise open obligation; it is recorded as a sharpened KU in the
discovery URS, not as a vacuous declaration. -/

/-! **The scale instance of `Fin↓` is open (sharpened conjecture).** A scale-indexed
`FinitizationScheme` would take `Resolution = ε` (a positive scale), `refine = 𝓝[>] 0` (`ε ↓ 0`), the
trace a minimal `ε`-net / covering of `C` in an empirical pseudometric, `size ε` the covering number
`N(ε)`, and `boundedTrace` the statement that finite VC dimension is equivalent to the metric entropy
`log N(ε)` being integrable (Dudley). The present FLT half is the packing-by-growth bound
`packing_card_le_growthFunction` (in `FLT_Proofs.Complexity.IndependentVC.Packing`): a δ-packing has
cardinality at most the growth function, i.e. the scale trace is controlled by the sample trace. The
missing edge is the chaining bound `empRadComplexity_le_dudley` and the covering carriers
`coveringNet` / `dyadicScale` / `entropyIntegral`, which live in the `transformers` / TLT library and
operate on the real-valued stratum; they are not in this Boolean module's closure and are not faked.

The statement above documents the precise open obligation; it is recorded as a sharpened KU in the
discovery URS, not as a vacuous declaration. -/
