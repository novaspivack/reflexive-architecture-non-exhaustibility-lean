import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.D002ResidualWitnessTarget
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.EnrichedWitness
import ReflexiveArchitectureNonexhaustibility.ResidualDynamics

/-!
# Payload promotion (**SPEC_016_ER1**, **EPIC_011** phase F2)

**Residual payload promotion theorem:** given **`U123BarrierData`** and a **bridge** into **`SigmaResidualPayload`**,
build an **`EnrichedR4ResidualWitness`** on top of **`barrierLinkedR4ResidualWitness`**.

This **does not** replace abstract **D-002**; it **extends** it when optional engine content is available via
**`PayloadPromotionBridge`** hypotheses.

**SPEC_023_RG1 D3 (bridge-grade):** **`standingResidualBurden_promotion_bridge_irrelevant`** — any **`Prop`** predicated on the
**promoted `.base`** **`ResidualWitness`** is unchanged when swapping **`ResidualPayloadFamily`** / **`PayloadPromotionBridge`**
(because **`promote_enriched_base_independent_of_family_and_bridge`**). **Not** relocation along **`EngineReflexiveMorphism`** /
cross-architecture maps — that remains **open**.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**Bridge hypothesis:** promote a **triple barrier pack** to a **sigma-indexed** payload.

Concrete engines (**`ResidualEnrichment/Bridges/*`**, **D-001**) supply **`promote`**; the abstract theorem is
**polymorphic** in **`F`**.
-/
structure PayloadPromotionBridge (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : ResidualPayloadFamily A) : Type 2 where
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

/--
**Bridge irrelevance for the underlying R₄ skeleton:** promotion only uses **`br`** for the
**sigma-shaped** certificate + payload; the **`base`** **`ResidualWitness`** is **`barrierLinkedR4ResidualWitness`**
of the **same** **`U123BarrierData`**.
-/
theorem promote_enriched_base_eq_barrier_linked
    (A : ReflexiveArchitecture World Obs Repr Claim) (F : ResidualPayloadFamily A)
    (br : PayloadPromotionBridge A F) (b : U123BarrierData A) :
    (promote_barrier_pack_to_enriched_r4 A F br b).base =
      barrierLinkedR4ResidualWitness b.reprBarrier b.closureBarrier b.certBarrier :=
  rfl

theorem promote_enriched_base_independent_of_family_and_bridge
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F₁ F₂ : ResidualPayloadFamily A) (br₁ : PayloadPromotionBridge A F₁)
    (br₂ : PayloadPromotionBridge A F₂) (b : U123BarrierData A) :
    (promote_barrier_pack_to_enriched_r4 A F₁ br₁ b).base =
      (promote_barrier_pack_to_enriched_r4 A F₂ br₂ b).base :=
  rfl

/--
**D3 (bridge-level):** **`StandingResidualBurden`** on a **`Prop`** about the **barrier-linked base** witness does **not** depend
on which **`PayloadPromotionBridge`** / payload family promoted the enrichment — only **`σ`** / engine tagging differs.

Combine with **`standingResidualBurden_of_imp`** to repackage obligations after changing bridges **without** claiming burden
vanished. Cross-**`ReflexiveArchitecture`** functorial transport stays **out of scope** here.
-/
theorem standingResidualBurden_promotion_bridge_irrelevant
    (A : ReflexiveArchitecture World Obs Repr Claim) (P : ResidualWitness → Prop)
    (F₁ F₂ : ResidualPayloadFamily A) (br₁ : PayloadPromotionBridge A F₁)
    (br₂ : PayloadPromotionBridge A F₂) (b : U123BarrierData A) :
    StandingResidualBurden (P (promote_barrier_pack_to_enriched_r4 A F₁ br₁ b).base) ↔
      StandingResidualBurden (P (promote_barrier_pack_to_enriched_r4 A F₂ br₂ b).base) := by
  rw [promote_enriched_base_independent_of_family_and_bridge A F₁ F₂ br₁ br₂ b]

end StructuredNonexhaustibility
