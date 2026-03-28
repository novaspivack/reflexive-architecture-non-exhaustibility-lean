import Lake
open Lake DSL

package «reflexive-architecture-nonexhaustibility-lean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

-- =============================================================================
-- **BIG NOTE — D-001 / EPIC_012 / nems-lean (DEFERRED, REPO IS PRIVATE)**
--
-- **nems-lean** must stay **private** for now. This package **does not** `require`
-- it in the default `lakefile`, so **`lake build` works** for contributors and CI
-- **without** access to nems.
--
-- **When nems is public OR CI has a read secret (deploy key / token):**
-- 1. Uncomment **one** of the `require` lines below (prefer **git @ fixed rev**
--    for reproducibility; **path** is fine for local dev).
-- 2. In `ReflexiveArchitectureNonexhaustibility/EngineDependencyPinning.lean`, switch
--    the import to `import NemS.Prelude` (or another smoke module).
-- 3. Run `lake update` and commit `lake-manifest.json`.
--
-- Example **git** pin (replace ORG + REV):
--   require «nems-lean» from git "https://github.com/ORG/nems-lean.git" @ "deadbeef..."
--
-- Example **path** pin (sibling of **parent** repo — local layout only):
--   require «nems-lean» from ".." / ".." / "nems-lean"
--
-- Governance: **SPEC_018_PN1**, root **README.md**, **docs/002_DEVELOPER_SETUP.md**.
-- =============================================================================
-- require «nems-lean» from git "https://github.com/REPLACE_ORG/nems-lean.git" @ "REPLACE_REV"
-- require «nems-lean» from ".." / ".." / "nems-lean"

@[default_target]
lean_lib «ReflexiveArchitectureNonexhaustibilityLean» where
  roots := #[
    `ReflexiveArchitectureNonexhaustibilityLean,
    `ReflexiveArchitectureNonexhaustibility.EngineDependencyPinning,
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
    `ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.MixedPayloadDesignNotes,
    `ReflexiveArchitectureNonexhaustibility.Universal,
    `ReflexiveArchitectureNonexhaustibility.Adequacy,
    `ReflexiveArchitectureNonexhaustibility.InfinityCompression,
    `ReflexiveArchitectureNonexhaustibility.Instances.ONE,
    `ReflexiveArchitectureNonexhaustibility.RouteCanonicality]
