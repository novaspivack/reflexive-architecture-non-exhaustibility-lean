import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.D002ResidualWitnessTarget
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.EnrichedWitness

/-!
# Payload promotion (**SPEC_016_ER1**, **EPIC_011** phase F2)

**Residual payload promotion theorem:** given **`U123BarrierData`** and a **bridge** into **`SigmaResidualPayload`**,
build an **`EnrichedR4ResidualWitness`** on top of **`barrierLinkedR4ResidualWitness`**.

This **does not** replace abstract **D-002**; it **extends** it when optional engine content is available via
**`PayloadPromotionBridge`** hypotheses.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**Bridge hypothesis:** promote a **triple barrier pack** to a **sigma-indexed** payload.

Concrete engines (**`ResidualEnrichment/Bridges/*`**, **D-001**) supply **`promote`**; the abstract theorem is
**polymorphic** in **`F`**.
-/
structure PayloadPromotionBridge (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : ResidualPayloadFamily A) : Type where
  promote : U123BarrierData A → SigmaResidualPayload F

/--
**Promotion (constructive):** barrier-linked **R₄** witness + bridge **⇒** enriched witness.
-/
def promote_barrier_pack_to_enriched_r4 (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : ResidualPayloadFamily A) (br : PayloadPromotionBridge A F) (b : U123BarrierData A) :
    EnrichedR4ResidualWitness A F :=
  let sp := br.promote b
  let rw := barrierLinkedR4ResidualWitness b.reprBarrier b.closureBarrier b.certBarrier
  { base := rw
    isR4 := isR4_barrierLinkedR4ResidualWitness b.reprBarrier b.closureBarrier b.certBarrier
    adm := admissible_barrierLinkedR4ResidualWitness b.reprBarrier b.closureBarrier b.certBarrier
    sig := sp.sig
    payload := sp.val }

/--
**Paper F2 certificate:** same as **`promote_barrier_pack_to_enriched_r4`** (`theorem` reserved for **`Prop`**; this is **data**).
-/
abbrev residual_payload_promotion (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : ResidualPayloadFamily A) (br : PayloadPromotionBridge A F) (b : U123BarrierData A) :
    EnrichedR4ResidualWitness A F :=
  promote_barrier_pack_to_enriched_r4 A F br b

/--
**Triple-barrier hypotheses:** package **`d₁–d₃`** then promote with **`br`**.
-/
def enriched_r4_from_triple_barriers_and_bridge (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : ResidualPayloadFamily A) (br : PayloadPromotionBridge A F)
    (d1 : DiagonalRepresentationalInterface A) (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    EnrichedR4ResidualWitness A F :=
  promote_barrier_pack_to_enriched_r4 A F br ⟨d1, d2, d3⟩

end StructuredNonexhaustibility
