import ReflexiveArchitectureNonexhaustibility.Residuals
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Payloads

/-!
# Enriched **R₄** residual witness (**SPEC_016_ER1**, **EPIC_011**)

Pairs a **barrier-linked-style** **`ResidualWitness`** (tagged **R₄**) with a **sigma-indexed** payload from
**`ResidualPayloadFamily`**.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**Engine-enriched** positive residual witness: **R₄** base witness + obstruction-tagged payload.

**Note:** **`base`** will usually be **`barrierLinkedR4ResidualWitness`** after promotion (**`Promotion.lean`**).
-/
structure EnrichedR4ResidualWitness (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : ResidualPayloadFamily A) : Type 2 where
  base : ResidualWitness
  isR4 : IsR4PositiveSurvivor base
  adm : AdmissibleResidual base
  sig : ObstructionSignature
  payload : PayloadFor F sig

end StructuredNonexhaustibility
