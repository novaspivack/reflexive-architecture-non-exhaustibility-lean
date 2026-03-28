import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Promotion

/-!
# Bridge — certification / ICA–SEM column (**EPIC_011** **F3b**)

**Pattern (same as **`FromRI` / `FromRFO`):** **`SemanticCertificationInterface`** is **`∀ τ, ¬ A.cert_success τ`** (**`Prop`**).
Lift to **`Type`** with **`PLift`** per certifier **`τ : Claim → Bool`**.

**D-001:** replace **`CertObstructionPayload`** with engine-native certification obstruction when imports are pinned.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**SEM-flavored obstruction payload:** for each proposed **`τ`**, a **data** witness that **`cert_success`** fails.
-/
def CertObstructionPayload (A : ReflexiveArchitecture World Obs Repr Claim) : Type :=
  (τ : Claim → Bool) → PLift (¬ A.cert_success τ)

/--
Extract the certification column from **`U123BarrierData`** as Π-**`PLift`** witnesses.
-/
def certObstructionPayloadOfU123 {A : ReflexiveArchitecture World Obs Repr Claim}
    (b : U123BarrierData A) : CertObstructionPayload A :=
  fun τ => PLift.up (b.certBarrier τ)

/--
**Residual family** focused on the cert slot; other carriers **`Empty`**.
-/
def semResidualPayloadFamily (A : ReflexiveArchitecture World Obs Repr Claim) : ResidualPayloadFamily A where
  reprPayload := Empty
  closurePayload := Empty
  certPayload := CertObstructionPayload A
  mixedPayload := Empty

/--
**Concrete bridge:** tag **`certSemantic`**, payload from **`b.certBarrier`**.
-/
def semPayloadPromotionBridge (A : ReflexiveArchitecture World Obs Repr Claim) :
    PayloadPromotionBridge A (semResidualPayloadFamily A) where
  promote b := ⟨ObstructionSignature.certSemantic, certObstructionPayloadOfU123 b⟩

/--
**End-to-end:** triple barriers + SEM-family bridge **⇒** enriched **R₄** with cert payload.
-/
def enrichedR4_tripleBarriers_withCertPayload (A : ReflexiveArchitecture World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface A) (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    EnrichedR4ResidualWitness A (semResidualPayloadFamily A) :=
  enriched_r4_from_triple_barriers_and_bridge A (semResidualPayloadFamily A) (semPayloadPromotionBridge A) d1 d2 d3

/--
**From **`U123BarrierData`** directly. -/
def enrichedR4_u123_withCertPayload (A : ReflexiveArchitecture World Obs Repr Claim) (b : U123BarrierData A) :
    EnrichedR4ResidualWitness A (semResidualPayloadFamily A) :=
  promote_barrier_pack_to_enriched_r4 A (semResidualPayloadFamily A) (semPayloadPromotionBridge A) b

end StructuredNonexhaustibility
