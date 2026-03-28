import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromRFO
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromRI
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromSEM
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Promotion

/-!
# Native-trace **`PayloadPromotionBridge`** (**EPIC_012** **PN4**, **SPEC_018_PN1**)

**Interface-native** Π–**`PLift`** bridges (**`FromRI` / `FromRFO` / `FromSEM`**) stay the default.

This module adds a **parallel seam:** pick arbitrary **`Type 1`** carriers **`R`, `C`, `S`** for
engine-native obstruction traces and supply **`promote : U123BarrierData A → SigmaResidualPayload F`**.
When **PN1** lands, **`R`, `C`, `S`** become real NemS trace types; until then the carriers are
**parameters** — no fake engine definitions. (Use **`ULift T`** when a **`Type`**-valued trace must sit in **`Type 1`**.)

**Refinement maps** into Π–`PLift` columns record logical agreement (**SPEC_003_BT1** alignment)
without identifying payload types definitionally.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

variable (A : ReflexiveArchitecture World Obs Repr Claim)

/--
**Triple-column** residual family: arbitrary native carriers; **`mixed`** slot **`Empty`** —
use **`FromMixedTriple`** when simultaneous triple content is required.
-/
def nativeTripleResidualPayloadFamily (reprNat closureNat certNat : Type 1) :
    ResidualPayloadFamily A where
  reprPayload := reprNat
  closurePayload := closureNat
  certPayload := certNat
  mixedPayload := ULift Empty

/--
Assemble a **`PayloadPromotionBridge`** from any **`promote`** function — the **native** seam.
-/
abbrev nativeTriplePayloadPromotionBridge (R C S : Type 1)
    (promote : U123BarrierData A → SigmaResidualPayload (nativeTripleResidualPayloadFamily A R C S)) :
    PayloadPromotionBridge A (nativeTripleResidualPayloadFamily A R C S) :=
  ⟨promote⟩

/--
**End-to-end** enriched witness from native bridge + barriers.
-/
def enrichedR4_u123_withNativeTriple (R C S : Type 1)
    (br : PayloadPromotionBridge A (nativeTripleResidualPayloadFamily A R C S)) (b : U123BarrierData A) :
    EnrichedR4ResidualWitness A (nativeTripleResidualPayloadFamily A R C S) :=
  promote_barrier_pack_to_enriched_r4 A (nativeTripleResidualPayloadFamily A R C S) br b

/--
Maps from declared native carriers into the **interface-native** Π–`PLift` columns (**EPIC_011**).
-/
structure NativeObstructionTraceRefinement (reprNat closureNat certNat : Type 1) where
  reprι : reprNat → ReprObstructionPayload A
  closureι : closureNat → ClosureObstructionPayload A
  certι : certNat → CertObstructionPayload A

/--
The native **`promote`** path **agrees** with **`reprObstructionPayloadOfU123`** after refinement.
-/
abbrev NativeReprColumnCoherent (R C S : Type 1)
    (ι : NativeObstructionTraceRefinement A R C S)
    (promote : U123BarrierData A → SigmaResidualPayload (nativeTripleResidualPayloadFamily A R C S)) :
    Prop :=
  ∀ b : U123BarrierData A,
    ∃ w : R, promote b = ⟨ObstructionSignature.reprDiag, w⟩ ∧ ι.reprι w = reprObstructionPayloadOfU123 b

/--
Same pattern for the closure column (signature **`closureObstruction`**).
-/
abbrev NativeClosureColumnCoherent (R C S : Type 1)
    (ι : NativeObstructionTraceRefinement A R C S)
    (promote : U123BarrierData A → SigmaResidualPayload (nativeTripleResidualPayloadFamily A R C S)) :
    Prop :=
  ∀ b : U123BarrierData A,
    ∃ w : C, promote b = ⟨ObstructionSignature.closureObstruction, w⟩ ∧
      ι.closureι w = closureObstructionPayloadOfU123 b

/--
Same pattern for the certification column (signature **`certSemantic`**).
-/
abbrev NativeCertColumnCoherent (R C S : Type 1)
    (ι : NativeObstructionTraceRefinement A R C S)
    (promote : U123BarrierData A → SigmaResidualPayload (nativeTripleResidualPayloadFamily A R C S)) :
    Prop :=
  ∀ b : U123BarrierData A,
    ∃ w : S, promote b = ⟨ObstructionSignature.certSemantic, w⟩ ∧ ι.certι w = certObstructionPayloadOfU123 b

end StructuredNonexhaustibility
