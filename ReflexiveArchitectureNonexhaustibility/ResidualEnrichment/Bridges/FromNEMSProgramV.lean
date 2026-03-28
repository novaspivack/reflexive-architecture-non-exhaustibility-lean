import NemS.Prelude
import StructuralNonExhaustibility.Core.ReflexiveSystem
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromRI
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Promotion

/-!
# NemS Program V native certificate + RI Π–`PLift` (**EPIC_012** **D-001**)

**Concrete NemS typing:** payloads carry a **`StructuralNonExhaustibility.ReflexiveSystem`** together with **data**
witnessing **`rs.BarrierHyp`** (**`PLift`** — real **proof** content, not a tag rename).

**Promotion:** the **representational** column is **`ReprObstructionPayload A × NemsProgramVBarrierCertificate`**
(dependent product; **`NemsProgramVBarrierCertificate`** may sit in a larger universe, so this slot need not use **`ULift`**
the way the purely **`Type`**-valued **FromRI** column does).

**Engine link, not magic extraction:** **`certFn : U123BarrierData A → NemsProgramVBarrierCertificate`** is the
**attachment** (morphism / elaborator) that relates this architecture’s triple barriers to a NemS Program V shell.
There is **no** canonical **`certFn`** from **`U123BarrierData` alone** without instance-specific mathematics — this is
honest **D-001** transport.

**Seam:** **`PayloadPromotionBridge`** unchanged; **`mixedTriple`** / other bridges **unchanged**.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

variable (A : ReflexiveArchitecture World Obs Repr Claim)

/--
**NemS-typed** payload component: a Program V **`ReflexiveSystem`** plus **lifted** barrier hypothesis (**proof**).
-/
structure NemsProgramVBarrierCertificate where
  rs : StructuralNonExhaustibility.ReflexiveSystem
  /-- Witness of **`rs.BarrierHyp`** as **`Type`-valued data. -/
  barrierPf : PLift rs.BarrierHyp

/--
**Residual family:** repr slot = Π–`PLift` **×** **`NemsProgramVBarrierCertificate`**; other columns **`Empty`**.
The **second** component’s **value** is chosen by **`certFn`** in **`augmentedReprNemsProgramVPromotionBridge`**.
-/
def augmentedReprResidualPayloadFamily : ResidualPayloadFamily A where
  reprPayload := ReprObstructionPayload A × NemsProgramVBarrierCertificate
  closurePayload := ULift Empty
  certPayload := ULift Empty
  mixedPayload := ULift Empty

/--
**Bridge:** **`U123BarrierData`** **⇒** **`reprDiag`** tag; payload = **`(Π-witness from b, certFn b)`**.
-/
def augmentedReprNemsProgramVPromotionBridge (certFn : U123BarrierData A → NemsProgramVBarrierCertificate) :
    PayloadPromotionBridge A (augmentedReprResidualPayloadFamily A) where
  promote b :=
    ⟨ObstructionSignature.reprDiag, (reprObstructionPayloadOfU123 b, certFn b)⟩

/--
**End-to-end** enriched **R₄** witness with **NemS-typed** second component.
-/
def enrichedR4_u123_withAugmentedNemsProgramVRepr (certFn : U123BarrierData A → NemsProgramVBarrierCertificate)
    (b : U123BarrierData A) :
    EnrichedR4ResidualWitness A (augmentedReprResidualPayloadFamily A) :=
  promote_barrier_pack_to_enriched_r4 A (augmentedReprResidualPayloadFamily A)
    (augmentedReprNemsProgramVPromotionBridge A certFn) b

def enrichedR4_tripleBarriers_withAugmentedNemsProgramVRepr
    (certFn : U123BarrierData A → NemsProgramVBarrierCertificate)
    (d1 : DiagonalRepresentationalInterface A) (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    EnrichedR4ResidualWitness A (augmentedReprResidualPayloadFamily A) :=
  enriched_r4_from_triple_barriers_and_bridge A (augmentedReprResidualPayloadFamily A)
    (augmentedReprNemsProgramVPromotionBridge A certFn) d1 d2 d3

end StructuredNonexhaustibility
