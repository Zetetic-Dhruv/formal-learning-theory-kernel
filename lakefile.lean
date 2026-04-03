import Lake
open Lake DSL

package LimitsOfLearning where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib FLT_Proofs where
  roots := #[
    `FLT_Proofs.Basic,
    `FLT_Proofs.Computation,
    `FLT_Proofs.Data,
    `FLT_Proofs.Learner,
    `FLT_Proofs.Learner.Core,
    `FLT_Proofs.Learner.Properties,
    `FLT_Proofs.Learner.Active,
    `FLT_Proofs.Learner.Bayesian,
    `FLT_Proofs.Learner.Closure,
    `FLT_Proofs.Learner.Attention,
    `FLT_Proofs.Learner.Monad,
    `FLT_Proofs.Criterion,
    `FLT_Proofs.Criterion.Gold,
    `FLT_Proofs.Criterion.PAC,
    `FLT_Proofs.Criterion.Online,
    `FLT_Proofs.Criterion.Extended,
    `FLT_Proofs.Complexity,
    `FLT_Proofs.Complexity.VCDimension,
    `FLT_Proofs.Complexity.Littlestone,
    `FLT_Proofs.Complexity.Ordinal,
    `FLT_Proofs.Complexity.MindChange,
    `FLT_Proofs.Complexity.Generalization,
    `FLT_Proofs.Complexity.Rademacher,
    `FLT_Proofs.Complexity.Symmetrization,
    `FLT_Proofs.Complexity.GeneralizationResults,
    `FLT_Proofs.Complexity.Structures,
    `FLT_Proofs.Complexity.Measurability,
    `FLT_Proofs.Complexity.BorelAnalyticBridge,
    `FLT_Proofs.Complexity.Amalgamation,
    `FLT_Proofs.Complexity.Interpolation,
    `FLT_Proofs.Complexity.Attention,
    `FLT_Proofs.Complexity.FiniteRouting,
    `FLT_Proofs.PureMath.ChoquetCapacity,
    `FLT_Proofs.PureMath.AnalyticMeasurability,
    `FLT_Proofs.PureMath.KLDivergence,
    `FLT_Proofs.PureMath.Concentration,
    `FLT_Proofs.PureMath.Exchangeability,
    `FLT_Proofs.PureMath.ReaderMonad,
    `FLT_Proofs.PureMath.BinaryMatrix,
    `FLT_Proofs.Theorem,
    `FLT_Proofs.Theorem.Gold,
    `FLT_Proofs.Theorem.PAC,
    `FLT_Proofs.Theorem.Online,
    `FLT_Proofs.Theorem.Separation,
    `FLT_Proofs.Theorem.Extended,
    `FLT_Proofs.Theorem.BorelAnalyticSeparation,
    `FLT_Proofs.Theorem.PACBayes,
    `FLT_Proofs.Process,
    `FLT_Proofs.Bridge,
    `FLT_Proofs.Meta.ProofOperad,
    `FLT_Proofs.Meta.ProofOperadInstances,
    `FLT_Proofs.Meta.ProofOperadTheorems,
    `FLT_Proofs.Meta.BridgeTactic,
    `FLT_Proofs.Meta.BridgeTests,
    `FLT_Proofs.Meta.NonTrivialTests,
    `FLT_Proofs.Meta.BridgeRealTests
  ]

lean_lib MetaKernel where
  roots := #[
    `MetaKernel.Core,
    `MetaKernel.Tactics,
    `MetaKernel.Measure,
    `MetaKernel.Phi,
    `MetaKernel.Discovery,
    `MetaKernel.WorldModel.PriorArt,
    `MetaKernel.WorldModel.MeasuredTactic,
    `MetaKernel.WorldModel.Feedback,
    `MetaKernel.Test
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
