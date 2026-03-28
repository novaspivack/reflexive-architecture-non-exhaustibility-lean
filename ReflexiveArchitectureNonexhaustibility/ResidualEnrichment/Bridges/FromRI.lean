import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Promotion

/-!
# Bridge — representational / diagonal column (**EPIC_011** **F3**)

**Scope:** first **end-to-end** **`PayloadPromotionBridge`** (see also **`FromRFO`**, **`FromSEM`** for the other
columns). **D-001** upgrades this payload **type** with NEMS / RI-native traces.

**Payload content:** the representational barrier is **`∀ ρ, ¬ A.repr_success ρ`** (**`DiagonalRepresentationalInterface`**,
**`Interfaces.lean`**). As a **`Prop`** it is not usable as **`PayloadFor`** data; we use **`PLift`** at each
internal gadget **`ρ`** so the carrier is a **Π-type in `Type`**: fiber-wise witnesses of **failure** for every
proposed representational totalization. That is **intrinsic obstruction** content (what RI instantiations prove), not a
relabelling of **`U123BarrierData`**.

**Universes:** **`ResidualPayloadFamily`** payload slots live in **`Type 1`** (so NemS-sized **D-001** carriers fit).
We wrap this column with **`ULift`**; **`ULift.up`** / **`ULift.down`** are the bookkeeping-free isomorphism at use sites.

**Shared pattern (all three columns):** extract a **Π–PLift** witness from a field of **`U123BarrierData`**, tag with
the matching **`ObstructionSignature`**, call **`promote_barrier_pack_to_enriched_r4`**.

**Still TODO after D-001:** swap **`ReprObstructionPayload`** for a richer **engine-native** trace type (diagonal
witness, Gödelized obstruction, …) and keep **`PayloadPromotionBridge`** as the seam.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**RI-flavored obstruction payload:** for each proposed **`ρ`**, a **data** witness that **`repr_success`** fails.
-/
def ReprObstructionPayload (A : ReflexiveArchitecture World Obs Repr Claim) : Type :=
  (ρ : World → Repr) → PLift (¬ A.repr_success ρ)

/--
From **`U123BarrierData`**, extract the representational column as **`Type`**-valued Π-witnesses.
-/
def reprObstructionPayloadOfU123 {A : ReflexiveArchitecture World Obs Repr Claim}
    (b : U123BarrierData A) : ReprObstructionPayload A :=
  fun ρ => PLift.up (b.reprBarrier ρ)

/--
**Residual family** focused on the representational slot; other carriers are **`Empty`** so **only** the RI column is
inhabited for this bridge.
-/
def riResidualPayloadFamily (A : ReflexiveArchitecture World Obs Repr Claim) : ResidualPayloadFamily A where
  reprPayload := ULift (ReprObstructionPayload A)
  closurePayload := ULift Empty
  certPayload := ULift Empty
  mixedPayload := ULift Empty

/--
**Concrete bridge (interface-native):** tag **`reprDiag`** and populate the payload from **`b.reprBarrier`**.
-/
def riPayloadPromotionBridge (A : ReflexiveArchitecture World Obs Repr Claim) :
    PayloadPromotionBridge A (riResidualPayloadFamily A) where
  promote b := ⟨ObstructionSignature.reprDiag, ULift.up (reprObstructionPayloadOfU123 b)⟩

/--
**End-to-end:** triple barriers + RI-family bridge **⇒** **`EnrichedR4ResidualWitness`** with **`reprDiag`** payload.
-/
def enrichedR4_tripleBarriers_withReprPayload (A : ReflexiveArchitecture World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface A) (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    EnrichedR4ResidualWitness A (riResidualPayloadFamily A) :=
  enriched_r4_from_triple_barriers_and_bridge A (riResidualPayloadFamily A) (riPayloadPromotionBridge A) d1 d2 d3

/--
**Certificate** (“engine obstruction **⇒** enriched witness”): same data as **`enrichedR4_tripleBarriers_withReprPayload`**,
packaged for readers who pass **`U123BarrierData`** directly.
-/
def enrichedR4_u123_withReprPayload (A : ReflexiveArchitecture World Obs Repr Claim) (b : U123BarrierData A) :
    EnrichedR4ResidualWitness A (riResidualPayloadFamily A) :=
  promote_barrier_pack_to_enriched_r4 A (riResidualPayloadFamily A) (riPayloadPromotionBridge A) b

end StructuredNonexhaustibility
