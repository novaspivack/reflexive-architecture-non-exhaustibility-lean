import Mathlib.Data.Set.Defs
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Promotion

/-!
# Bridge — closure / RFO column (**EPIC_011** **F3b**)

**Dynamics forward (**SPEC_023_RG1** **D2**):** closure obstruction lives in this column; **`ResidualDynamics.lean`** now
defines **`closureIterate`** / **`InClosureIterateImage`** / **`OutsideClosureIterateImage`** for **RFO**-shaped **`Set World`**
operators. **`RegimeSnapshot`** / **`ResidualResponseStep.reconfiguration`** models changing **`ReflexiveArchitecture`**
(including **`closure_success`**). A **fold** theorem linking honesty to **`OutsideClosureIterateImage`** remains **EPIC_015**
**P3**.

**Pattern (same as **`FromRI.lean`** / **F3a):** **`ClosureObstructionInterface`** is **`∀ Cl, ¬ A.closure_success Cl`** (**`Prop`**).
Lift to **`Type`** with **`PLift`** per closure candidate **`Cl : Set World → Set World`**.

**D-001:** replace **`ClosureObstructionPayload`** with an RFO-native trace when imports are pinned; keep
**`PayloadPromotionBridge`** as the seam.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**RFO-flavored obstruction payload:** for each proposed closure **`Cl`**, a **data** witness that **`closure_success`** fails.
-/
def ClosureObstructionPayload (A : ReflexiveArchitecture World Obs Repr Claim) : Type :=
  (Cl : Set World → Set World) → PLift (¬ A.closure_success Cl)

/--
Extract the closure column from **`U123BarrierData`** as Π-**`PLift`** witnesses.
-/
def closureObstructionPayloadOfU123 {A : ReflexiveArchitecture World Obs Repr Claim}
    (b : U123BarrierData A) : ClosureObstructionPayload A :=
  fun Cl => PLift.up (b.closureBarrier Cl)

/--
**Residual family** focused on the closure slot; other carriers **`Empty`**.
-/
def rfoResidualPayloadFamily (A : ReflexiveArchitecture World Obs Repr Claim) : ResidualPayloadFamily A where
  reprPayload := ULift Empty
  closurePayload := ULift (ClosureObstructionPayload A)
  certPayload := ULift Empty
  mixedPayload := ULift Empty

/--
**Concrete bridge:** tag **`closureObstruction`**, payload from **`b.closureBarrier`**.
-/
def rfoPayloadPromotionBridge (A : ReflexiveArchitecture World Obs Repr Claim) :
    PayloadPromotionBridge A (rfoResidualPayloadFamily A) where
  promote b := ⟨ObstructionSignature.closureObstruction, ULift.up (closureObstructionPayloadOfU123 b)⟩

/--
**End-to-end:** triple barriers + RFO-family bridge **⇒** enriched **R₄** with closure payload.
-/
def enrichedR4_tripleBarriers_withClosurePayload (A : ReflexiveArchitecture World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface A) (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    EnrichedR4ResidualWitness A (rfoResidualPayloadFamily A) :=
  enriched_r4_from_triple_barriers_and_bridge A (rfoResidualPayloadFamily A) (rfoPayloadPromotionBridge A) d1 d2 d3

/--
**From **`U123BarrierData`** directly. -/
def enrichedR4_u123_withClosurePayload (A : ReflexiveArchitecture World Obs Repr Claim) (b : U123BarrierData A) :
    EnrichedR4ResidualWitness A (rfoResidualPayloadFamily A) :=
  promote_barrier_pack_to_enriched_r4 A (rfoResidualPayloadFamily A) (rfoPayloadPromotionBridge A) b

end StructuredNonexhaustibility
