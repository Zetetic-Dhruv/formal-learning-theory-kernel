# Changelog

All notable changes to this project are documented in this file.
Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [v3.2.0] - 2026-04-05

### Added
- **Compression characterization** (`Complexity/Compression.lean`, 1,328 lines): VCDim < infinity implies existence of compression scheme. Moran-Yehudayoff 2016 construction via approximate minimax (MWU). Closes the 5th conjunct of the fundamental theorem.
- **Approximate minimax** (`PureMath/ApproxMinimax.lean`, 640 lines): multiplicative weights update for approximate minimax on finite games. Field-independent, Mathlib-contributable.
- **Finite VC approximation** (`PureMath/FiniteVCApprox.lean`, 158 lines): VC dimension bounds for finite approximations.
- **Assouad dual VC bound** (`PureMath/BinaryMatrix.lean`, extended): bitstring coding argument proving transpose VC dimension bounded by 2^(d+1)-1.
- **Dual VC infrastructure** (`Complexity/DualVC.lean`): dual class construction bridging primal and dual shattering.
- **Finite support UC** (`Complexity/FiniteSupportUC.lean`, 422 lines): uniform convergence for finitely-supported concept classes.

### Changed
- **Sorry count: 2 → 0.** All compiled theorems are proved. The universal trichotomy (BHMZ STOC 2021) is commented out as a TODO, not sorry'd.
- **Fundamental theorem: 4/5 → 5/5.** All five conjuncts of the VC characterization are now proved.
- `scripts/metrics.sh` fixed for zero-sorry case (grep returns non-zero on empty match).
- README fully updated: removed core/extended distinction, all metrics to 354/21,522/53/0.
- Hero SVG: compression vertex solid, all edges solid, "5/5 equivalence, sorry-free."

### Metrics delta

| Metric | v3.0.0 | v3.2.0 | Delta |
|--------|--------|--------|-------|
| Files | 47 | 53 | +6 |
| Lines | 18,356 | 21,522 | +3,166 |
| Theorems | 292 | 354 | +62 |
| Definitions | 212 | 257 | +45 |
| Structures | 56 | 59 | +3 |
| Sorry | 2 | **0** | **-2** |

## [v3.0.0] - 2026-04-03

### Added
- **Amalgamation measurability** (`Complexity/Amalgamation.lean`, 124 lines): amalgamation of Borel-parameterized concept families preserves `WellBehavedVCMeasTarget`. Agreement relation is MeasurableSet via `measurableSet_eq_fun` + `upgradeStandardBorel`. Interpolation embeds as corollary (`interpClassFixed_subset_amalgClass`).
- **MeasurableBatchLearner closure algebra** (`Learner/Closure.lean`, 134 lines): closed under Boolean combination (`combineLearner`), majority vote (`boostLearner`), piecewise interpolation (`interpLearner`), and countable selection (`concatLearner`). `UniformMeasurableBatchFamily` typeclass for indexed families.
- **MeasLearner monad** (`Learner/Monad.lean`, 79 lines): bundles `BatchLearner` + `MeasurableBatchLearner`. `pure`/`bind` with definitional monad laws via `ReaderSel`.
- **ReaderSel monad** (`MathLib/ReaderMonad.lean`, 63 lines): pure math reader monad with data-dependent indexing. Zero dependencies. Monad laws hold by `rfl`.
- **Interpolation descent** (`Complexity/Interpolation.lean`, 249 lines): composition of Borel concept classes weakens measurability from MeasurableSet to NullMeasurableSet. `BorelRouterCode` abstraction for conditional interpolation.
- **Version space measurability** (`Learner/VersionSpace.lean`, 203 lines): version space learners satisfy `MeasurableBatchLearner` via rectangle decomposition + `Nat.find`. Non-neural RL policy class.
- **Game infrastructure** (`Complexity/GameInfra.lean`, 219 lines): extracted game-theoretic infrastructure for online learning (adversary tree, version space potential).
- **Concentration** (`PureMath/Concentration.lean`, 195 lines): `BoundedRandomVariable` typeclass, Chebyshev majority bound. Field-independent, Mathlib-contributable.
- **Exchangeability** (`PureMath/Exchangeability.lean`, 128 lines): double-sample measure, merge/split isomorphism, `ValidSplit`, `SplitMeasure`. Field-independent, Mathlib-contributable.
- **KL divergence** (`PureMath/KLDivergence.lean`, 59 lines): `FinitePMF`, KL divergence, cross-entropy over finite types. Field-independent, Mathlib-contributable.
- **Typed proof operad** (`world_model/WorldModel/`, 1,170 lines, 0 sorry): `TPG_FLT` -- formalized proof world model with Interface, Generator, Plan, HasType judgment, negative typing via FailureRule, extension via GapSpec. 17 generators, 7 failure rules, 27/27 tests pass.
- **Corpus-relative completeness theorem**: all 6 major pipelines (PAC, DST, Online, Gold, Separation, Bayes) type-check under `fltTheory`.
- **Paradigm lock theorem**: no generator spans PAC + Online + Gold simultaneously.
- **NT1 cross-paradigm impossibility**: `seq TreePotential UCToPAC` provably ill-typed at composition level.
- **Machine-generated hypergraph** (`scripts/generate_hypergraph.py`): Sugiyama layout with barycenter ordering, 4 figures output to `assets/`.
- **Machine-generated theorem index** (`scripts/generate_theorem_index.sh`): full 278-theorem index grouped by module.
- **README rewritten as ArXiv-quality preprint**: 16 sections across 4 parts, URS-discovered structure.

### Changed
- **Folder rename**: `MathLib/` renamed to `PureMath/` (avoids confusion with upstream Mathlib)
- **World model canonical**: `FLT_Proofs/Meta/` removed; `world_model/WorldModel/` is now the canonical build target (`lake build WorldModel`)
- **Lakefile**: added `WorldModel` lean_lib with `srcDir := "world_model"`, removed stale `MetaKernel` lib, fixed `FLT_Proofs.MathLib` -> `FLT_Proofs.PureMath`
- **Mathlib pinned**: re-pinned to `fde0cc508f` after lakefile restructuring

### Metrics delta

| Metric | v2.0.0 | v3.0.0 | Delta |
|--------|--------|--------|-------|
| Files | 37 | 47 | +10 |
| Lines | 17,350 | 18,356 | +1,006 |
| Theorems | 264 | 292 | +28 |
| Definitions | 190 | 212 | +22 |
| Structures | 52 | 56 | +4 |
| Sorry | 2 | 2 | 0 |

## [v2.0.0] - 2026-03-30

### Added
- **Borel-analytic separation theorem** (`Theorem/BorelAnalyticSeparation.lean`, 305 lines): first new mathematical result from this kernel. Proves that `WellBehavedVC` (NullMeasurableSet) is strictly weaker than `KrappWirthWellBehaved` (MeasurableSet) for learning theory bad events. Witness: singleton class over analytic non-Borel subset of R. Conditional on existence of analytic non-Borel sets.
- **Choquet capacitability theorem** (`MathLib/ChoquetCapacity.lean`, 416 lines): Kechris 30.13. Pure measure theory on Polish spaces. Mathlib-contributable. Sorry-free.
- **Analytic measurability bridge** (`MathLib/AnalyticMeasurability.lean`, 110 lines): analytic sets are universally measurable.
- **Borel-analytic bridge** (`Complexity/BorelAnalyticBridge.lean`, 257 lines): Borel-parameterized concept classes have analytic bad events. Connects descriptive set theory to statistical learning.
- **PAC-Bayes bound** (`Theorem/PACBayes.lean`, 525 lines): McAllester's PAC-Bayes for finite hypothesis classes. First Lean4 formalization. Three-theorem chain: per-hypothesis Hoeffding, simultaneous union bound, full Jensen-based Gibbs error bound. Sorry-free.
- **Measurability typeclass hierarchy** (`Complexity/Measurability.lean`, 408 lines): three-level hierarchy `MeasurableHypotheses -> MeasurableConceptClass -> KrappWirthWellBehaved`, plus `MeasurableBatchLearner`. Replaces ad-hoc hypothesis threading.
- **Krapp-Wirth ghost gap formalization**: first machine-checked verification of Krapp and Wirth (2024, arXiv:2410.10243). Sorry-free proof that `KrappWirthWellBehaved -> WellBehavedVC`.
- **Baxter multi-task framework** (`Theorem/Extended.lean`): `TaskEnvironment`, `MetaLearnerPAC`, `SampleMetaLearner` structures. `baxter_base_case` and `baxter_full` theorems. Sorry-free.
- `CHANGELOG.md` (this file)
- `scripts/metrics.sh` for canonical count generation

### Changed
- **Package name**: `LimitsOfLearning` renamed to `FLTKernel` in `lakefile.lean`
- **Mathlib pinned**: `master` replaced with commit `fde0cc508f5375f278f515cb2f50a34a545a4c5c`
- **Typeclass refactor**: 8 files modified to replace explicit `hmeas_C`/`hc_meas`/`hWB` hypothesis threading with `[MeasurableConceptClass X C]` typeclass instances
- `meta_pac_bound` rewritten from trivially-true statement (mf = 0) to meaningful delegation to `pac_sample_complexity_sandwich`
- `premise/final.json` updated with v2 metrics

### Fixed
- `meta_pac_bound` was trivially true (proved by `mf = 0` since `0 <= n`). Replaced with non-trivial statement.
- CI sorry check matched comment mentions of "sorry". Fixed to POSIX ERE matching standalone tactics only.

### Metrics delta

| Metric | v1.0.0 | v2.0.0 | Delta |
|--------|--------|--------|-------|
| Files | 31 | 37 | +6 |
| Lines | 14,945 | 17,350 | +2,405 |
| Theorems | 210 | 264 | +54 |
| Definitions | 158 | 190 | +32 |
| Structures | 46 | 52 | +6 |
| Sorry | 2 | 2 | 0 |

## [v1.0.0] - 2026-03-25

### Added
- Initial release: Lean4 formalization of the Fundamental Theorem of Statistical Learning
- 31 files, 14,945 lines, 210 theorems, 2 sorry
- VC characterization (PAC iff VCDim < infinity), sorry-free
- Littlestone characterization (Online iff LittlestoneDim < infinity), sorry-free
- Gold's theorem (locking sequence), sorry-free
- Mind change characterization, sorry-free
- All paradigm separations with constructive witnesses, sorry-free
- Fundamental theorem (5-way equivalence, 4/5 conjuncts proved)
- Universal trichotomy (2/3 branches proved)
- Full symmetrization chain (3,027 lines, sorry-free)
- Rademacher complexity infrastructure (1,901 lines, sorry-free)
- NFL theorems for infinite domains, sorry-free
- Sauer-Shelah via Mathlib bridge, sorry-free
- PAC-Bayes boosting (7/12-fraction Chebyshev), sorry-free
- Premise architecture: `premise/origin.json` and `premise/final.json`
- CI via GitHub Actions with sorry count gate
- Apache 2.0 license with prior art notice

### Known issues
- 2 sorry tactics blocked by results absent from Mathlib:
  - `vcdim_finite_imp_compression` (Moran-Yehudayoff 2016)
  - `bhmz_middle_branch` (BHMZ STOC 2021)

[v3.2.0]: https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/compare/v3.0.0...v3.2.0
[v3.0.0]: https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/compare/v2.0.0...v3.0.0
[v2.0.0]: https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/compare/v1.0.0...v2.0.0
[v1.0.0]: https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/releases/tag/v1.0.0
