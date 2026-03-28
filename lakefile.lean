import Lake
open Lake DSL

package «reflexive-architecture-nonexhaustibility-lean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

@[default_target]
lean_lib «ReflexiveArchitectureNonexhaustibilityLean» where
  roots := #[
    `ReflexiveArchitectureNonexhaustibilityLean,
    `ReflexiveArchitectureNonexhaustibility.Basic,
    `ReflexiveArchitectureNonexhaustibility.Modes,
    `ReflexiveArchitectureNonexhaustibility.Residuals,
    `ReflexiveArchitectureNonexhaustibility.Interfaces,
    `ReflexiveArchitectureNonexhaustibility.Barriers,
    `ReflexiveArchitectureNonexhaustibility.SyntacticModeCover,
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Attempt,
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Profiles,
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Mediation,
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Classification,
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.GenuinenessCandidates,
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.WeakerBurdenSearch,
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.D002ResidualWitnessTarget,
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.AnchoredFlagship,
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.LayerDiscipline,
    `ReflexiveArchitectureNonexhaustibility.Universal,
    `ReflexiveArchitectureNonexhaustibility.Adequacy,
    `ReflexiveArchitectureNonexhaustibility.InfinityCompression,
    `ReflexiveArchitectureNonexhaustibility.Instances.ONE,
    `ReflexiveArchitectureNonexhaustibility.RouteCanonicality]
