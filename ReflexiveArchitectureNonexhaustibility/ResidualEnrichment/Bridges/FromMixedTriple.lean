import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromRI
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromRFO
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromSEM

/-!
# Bridge — simultaneous triple-column (**mixedTriple**) payload (**EPIC_011**, **SPEC_017_MX1**)

**Distinct from single-column bridges:** those answer “which column is highlighted?” via **`SigmaResidualPayload`** with
one tag. This module answers “what obstruction **content** is present when **U₁–U₃** hold **together**?” — a **named
three-field record** (product) of the same Π–**`PLift`** column types as **`FromRI`**, **`FromRFO`**, **`FromSEM`**.

**Do not** remove or merge the single-column bridges; both layers are intentional (**SPEC_017_MX1** §5).
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**Mixed triple obstruction payload:** all three column payloads **at once** (simultaneous barriers).
-/
structure MixedTripleObstructionPayload (A : ReflexiveArchitecture World Obs Repr Claim) where
  /-- Representational / RI column (Π **`ρ`**, **`PLift (¬ repr_success)`**). -/
  repr : ReprObstructionPayload A
  /-- Closure / RFO column (Π **`Cl`**, **`PLift (¬ closure_success)`**). -/
  closure : ClosureObstructionPayload A
  /-- Certification / SEM column (Π **`τ`**, **`PLift (¬ cert_success)`**). -/
  cert : CertObstructionPayload A

/--
Package **`U123BarrierData`** into the **product** of the three extractors already used by the per-column bridges.
-/
def mixedTripleObstructionPayloadOfU123 {A : ReflexiveArchitecture World Obs Repr Claim}
    (b : U123BarrierData A) : MixedTripleObstructionPayload A where
  repr := reprObstructionPayloadOfU123 b
  closure := closureObstructionPayloadOfU123 b
  cert := certObstructionPayloadOfU123 b

/--
**Singleton family** for **`mixedTriple`** only: single-column **`PayloadFor`** arms **`ULift Empty`**.
-/
def mixedTripleResidualPayloadFamily (A : ReflexiveArchitecture World Obs Repr Claim) : ResidualPayloadFamily A where
  reprPayload := ULift Empty
  closurePayload := ULift Empty
  certPayload := ULift Empty
  mixedPayload := ULift (MixedTripleObstructionPayload A)

/--
**`PayloadPromotionBridge`** tagging **`ObstructionSignature.mixedTriple`**.
-/
def mixedTriplePayloadPromotionBridge (A : ReflexiveArchitecture World Obs Repr Claim) :
    PayloadPromotionBridge A (mixedTripleResidualPayloadFamily A) where
  promote b :=
    ⟨ObstructionSignature.mixedTriple, ULift.up (mixedTripleObstructionPayloadOfU123 b)⟩

/--
**End-to-end:** under **U₁–U₃**, enriched **R₄** witness whose payload carries **all three** Π–**`PLift`** columns.
-/
def enrichedR4_tripleBarriers_withMixedTriplePayload (A : ReflexiveArchitecture World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface A) (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    EnrichedR4ResidualWitness A (mixedTripleResidualPayloadFamily A) :=
  enriched_r4_from_triple_barriers_and_bridge A (mixedTripleResidualPayloadFamily A)
    (mixedTriplePayloadPromotionBridge A) d1 d2 d3

/--
**From **`U123BarrierData`** directly.
-/
def enrichedR4_u123_withMixedTriplePayload (A : ReflexiveArchitecture World Obs Repr Claim) (b : U123BarrierData A) :
    EnrichedR4ResidualWitness A (mixedTripleResidualPayloadFamily A) :=
  promote_barrier_pack_to_enriched_r4 A (mixedTripleResidualPayloadFamily A) (mixedTriplePayloadPromotionBridge A) b

end StructuredNonexhaustibility
