import Lake
open Lake DSL

package «reflexive-architecture-nonexhaustibility-lean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

-- =============================================================================
-- **BIG NOTE — D-001 / EPIC_012 / nems-lean (path pin; full D-001)**
--
-- Active **`require`** uses **path** `../../nems-lean` relative to this file (two dirs up from
-- `reflexive-architecture-nonexhaustibility-lean/`, then **`nems-lean`**). **CI** must clone or
-- link **`nems-lean`** there, **or** switch to a **git** pin + read credential (**SPEC_018_PN1**).
--
-- After edits: **`lake update`**, commit **`lake-manifest.json`**. Smoke: **`NemS.Prelude`** in
-- **`EngineDependencyPinning.lean`**, optional **`NemsStructuralProgramLink.lean`**.
--
-- Example **git** pin when the engine repo is public:
--   require «nems-lean» from git "https://github.com/ORG/nems-lean.git" @ "deadbeef..."
--
-- Governance: **SPEC_018_PN1**, root **README.md**, **docs/002_DEVELOPER_SETUP.md**.
--
-- **Sibling checkout tested in development:** `nems-lean` at **d25eefd7f4794b13d77c8438bd8fe750b7838137**
-- (reflection/`bh` closure obstructions: `ToReflection.false_of_encodedNontrivial_aligns_univ`,
-- `UnitypedNatReprObstruction.not_nonempty_sri0'_nat_equiv_eq`, …).
-- =============================================================================
require «nems-lean» from ".." / ".." / "nems-lean"
-- require «nems-lean» from git "https://github.com/REPLACE_ORG/nems-lean.git" @ "REPLACE_REV"

@[default_target]
lean_lib «ReflexiveArchitectureNonexhaustibilityLean» where
  roots := #[
    `ReflexiveArchitectureNonexhaustibilityLean,
    `ReflexiveArchitectureNonexhaustibility.EngineDependencyPinning,
    `ReflexiveArchitectureNonexhaustibility.NemsStructuralProgramLink,
    `ReflexiveArchitectureNonexhaustibility.EngineReflexiveMorphism,
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
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.PaperDAnchoredChain,
    `ReflexiveArchitectureNonexhaustibility.AbstractModeCover.PostFailureResidual,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Payloads,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.EnrichedWitness,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Promotion,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Summit,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromRI,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromRFO,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromSEM,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromMixedTriple,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromNativeTraces,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromNEMSProgramV,
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.MixedPayloadDesignNotes,
    `ReflexiveArchitectureNonexhaustibility.Universal,
    `ReflexiveArchitectureNonexhaustibility.Adequacy,
    `ReflexiveArchitectureNonexhaustibility.InfinityCompression,
    `ReflexiveArchitectureNonexhaustibility.ResidualDynamics,
    `ReflexiveArchitectureNonexhaustibility.Instances.ONE,
    `ReflexiveArchitectureNonexhaustibility.RouteCanonicality,
    `ReflexiveArchitectureNonexhaustibility.U123ReprAugmentedSemanticLink,
    `ReflexiveArchitectureNonexhaustibility.KleenePredicatedResidualSummit,
    `ReflexiveArchitectureNonexhaustibility.ProvBicU123EnrichedR4Alignment]
