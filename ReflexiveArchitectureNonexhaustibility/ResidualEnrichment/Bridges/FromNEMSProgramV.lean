import NemS.Prelude
import StructuralNonExhaustibility.Core.ReflexiveSystem
import StructuralNonExhaustibility.Bridges.ToSemanticSelfDescription
import SemanticSelfDescription.Core.Claims
import ReflexiveArchitectureNonexhaustibility.EngineReflexiveMorphism
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromRI
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Promotion

/-!
# NemS Program V native certificate + RI Π–`PLift` (**EPIC_012** **D-001**)

**Concrete NemS typing:** payloads carry a **`StructuralNonExhaustibility.ReflexiveSystem`** together with **data**
witnessing **`rs.BarrierHyp`** (**`PLift`** — real **proof** content, not a tag rename).

**Promotion:** the **representational** column is **`ReprObstructionPayload A × NemsProgramVBarrierCertificate`**
(dependent product; **`NemsProgramVBarrierCertificate`** may sit in a larger universe, so this slot need not use **`ULift`**
the way the purely **`Type`**-valued **FromRI** column does).

**Parameterized seam (legacy hook):** **`certFn : U123BarrierData A → NemsProgramVBarrierCertificate`** — arbitrary
attachment at the **`PayloadPromotionBridge`** boundary.

**Morphism-native attachment (preferred):** **`EngineNemsBarrierSync`** packages an **`EngineReflexiveMorphism`**, a
**`toNems : E → ReflexiveSystem`** elaboration, and **proves** that for **every** engine point **`e`**, any
**`U123BarrierData (φ.toReflexive e)`** yields **`(toNems e).BarrierHyp`**. The certificate at **`e₀`** is then
**forced** to be **`⟨toNems e₀, sync e₀ b⟩`** — **no** free choice of **`rs`** per barrier pack beyond **`toNems`**.
Real engines instantiate **`sync`** with their Program V barrier lemmas (**not** definitional magic from **`U123`** alone).

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

variable {E : Type}

/--
**Structured NemS attachment** over **`EngineReflexiveMorphism`**: Program V shells vary with **`e : E`**, and
**`sync`** is the **engine proof obligation** tying **abstract** **`U123BarrierData`** on **`φ.toReflexive e`** to
**`BarrierHyp`** of **`toNems e`**.
-/
structure EngineNemsBarrierSync (φ : EngineReflexiveMorphism E World Obs Repr Claim) : Type 1 where
  /-- NemS reflexive system at each engine point (**Program V** stage). -/
  toNems : E → StructuralNonExhaustibility.ReflexiveSystem
  /-- **Content:** barriers on the **image** architecture imply the NemS barrier hypothesis at **`e`**. -/
  sync : ∀ e (_ : U123BarrierData (φ.toReflexive e)), PLift (toNems e).BarrierHyp

/--
**Certificate** forced by **`sync`** at **`e`** (still **data**-typed via **`PLift`**).
-/
def nemsCertificate_of_sync {φ : EngineReflexiveMorphism E World Obs Repr Claim}
    (S : EngineNemsBarrierSync φ) (e : E) (b : U123BarrierData (φ.toReflexive e)) :
    NemsProgramVBarrierCertificate :=
  ⟨S.toNems e, S.sync e b⟩

/-!
### Constructible **`EngineNemsBarrierSync`** values (**D-001**)

**Constant barrier proof:** if **`rs.BarrierHyp`** is already a **theorem**, then **`sync`** may ignore the abstract
**`U123BarrierData`** — this is **not** smuggling (the hypothesis was proved **before**) but is **weak** unless **`rs`**
comes from a **real** NemS / paper bridge.

**Trivial NemS shell:** **`nemsTrivialBarrierReflexiveSystem`** remains for **CI / scaffolding**
(`BarrierHyp := True`).

**Semantic native shell (`EPIC_012` nontrivial tranche):** **`reflexiveSystem_ofSelfSemanticFrame`** in
**`StructuralNonExhaustibility.Bridges.ToSemanticSelfDescription`** (`nems-lean`) — real **`BarrierHyp`**
(`Nonempty (BarrierHypotheses F)`). Use **`EngineNemsBarrierSync.ofSemanticSelfDescriptionFrame`** when the engine can
prove **`sync`** (paper barriers → nonempty semantic hypotheses). **`sync`** is **not** definitional from **`U123`** alone.
-/

/-- **Scaffolding** NemS shell: **`BarrierHyp`** is **True** (real **`ReflexiveSystem`**, illustrative content only). -/
def nemsTrivialBarrierReflexiveSystem : StructuralNonExhaustibility.ReflexiveSystem where
  System := Unit
  Claim := Unit
  SelfInvolving := fun _ => True
  TotalExhaustiveInternal := True
  BarrierHyp := True

theorem nemsTrivialBarrierReflexiveSystem_barrier : nemsTrivialBarrierReflexiveSystem.BarrierHyp := trivial

/--
**Any** morphism carries a **constant** NemS point with **fixed** barrier theorem (**paper / engine supplied**).
-/
def EngineNemsBarrierSync.ofConstantBarrier {E : Type}
    (φ : EngineReflexiveMorphism E World Obs Repr Claim)
    (rs : StructuralNonExhaustibility.ReflexiveSystem) (HBarrier : rs.BarrierHyp) :
    EngineNemsBarrierSync φ where
  toNems := fun _ => rs
  sync := fun _ _ => PLift.up HBarrier

/--
**First runnable instance:** trivial Program V shell at every **`e`** (**`PLift`** of **`trivial`**).
-/
def EngineNemsBarrierSync.trivialBarrier (φ : EngineReflexiveMorphism E World Obs Repr Claim) :
    EngineNemsBarrierSync φ :=
  ofConstantBarrier φ nemsTrivialBarrierReflexiveSystem nemsTrivialBarrierReflexiveSystem_barrier

/--
**Semantic self-description** NemS point (constant in **`e`**): **`toNems`** is **`reflexiveSystem_ofSelfSemanticFrame F`**.

**Proof obligation **`h`:** for each engine point and **`U123BarrierData`**, supply **`Nonempty (BarrierHypotheses F)`** —
typically from a **mathematical** bridge (reflection / diagonal closure, etc.), **not** from notation alone.
-/
def EngineNemsBarrierSync.ofSemanticSelfDescriptionFrame {W : Type}
    (φ : EngineReflexiveMorphism E World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    (h :
      ∀ e (_ : U123BarrierData (φ.toReflexive e)), Nonempty (SemanticSelfDescription.BarrierHypotheses F)) :
    EngineNemsBarrierSync φ where
  toNems := fun _ => StructuralNonExhaustibility.reflexiveSystem_ofSelfSemanticFrame F
  sync := fun e b => PLift.up (h e b)

/--
**Recover** **`NemsProgramVBarrierCertificate`** from the trivial sync at **`e₀`** (dependent only on **`φ`**, **`e₀`**).
-/
def nemsTrivialCertificate {E : Type} (φ : EngineReflexiveMorphism E World Obs Repr Claim) (e₀ : E)
    (b : U123BarrierData (φ.toReflexive e₀)) : NemsProgramVBarrierCertificate :=
  nemsCertificate_of_sync (EngineNemsBarrierSync.trivialBarrier φ) e₀ b

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
**Morphism-native bridge** at engine point **`e₀`**: **`A = φ.toReflexive e₀`** — certificate determined by **`S.sync`**.
-/
def augmentedReprNemsProgramVSyncPromotionBridge
    (φ : EngineReflexiveMorphism E World Obs Repr Claim) (S : EngineNemsBarrierSync φ) (e₀ : E) :
    PayloadPromotionBridge (φ.toReflexive e₀) (augmentedReprResidualPayloadFamily (φ.toReflexive e₀)) where
  promote b :=
    ⟨ObstructionSignature.reprDiag,
      (reprObstructionPayloadOfU123 b, nemsCertificate_of_sync S e₀ b)⟩

/--
**Recover** the **parameterized** bridge from **`sync`** (definitional **unfold** of **`nemsCertificate_of_sync`**).
-/
theorem augmentedReprNemsProgramVPromotionBridge_eq_sync
    (φ : EngineReflexiveMorphism E World Obs Repr Claim) (S : EngineNemsBarrierSync φ) (e₀ : E) :
    augmentedReprNemsProgramVPromotionBridge (φ.toReflexive e₀)
        (fun b => nemsCertificate_of_sync S e₀ b) =
      augmentedReprNemsProgramVSyncPromotionBridge φ S e₀ := by
  rfl

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

def enrichedR4_u123_withAugmentedNemsProgramVRepr_sync
    (φ : EngineReflexiveMorphism E World Obs Repr Claim) (S : EngineNemsBarrierSync φ) (e₀ : E)
    (b : U123BarrierData (φ.toReflexive e₀)) :
    EnrichedR4ResidualWitness (φ.toReflexive e₀) (augmentedReprResidualPayloadFamily (φ.toReflexive e₀)) :=
  promote_barrier_pack_to_enriched_r4 (φ.toReflexive e₀) (augmentedReprResidualPayloadFamily (φ.toReflexive e₀))
    (augmentedReprNemsProgramVSyncPromotionBridge φ S e₀) b

/--
**End-to-end** enriched **R₄** with **`NemsProgramVBarrierCertificate`** tied to a **semantic** Program V shell and a
user-supplied **`sync`** proof **`h`** (**`ofSemanticSelfDescriptionFrame`**).
-/
def enrichedR4_u123_withAugmentedNemsProgramVRepr_semanticSync
    {W : Type} (φ : EngineReflexiveMorphism E World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    (h :
      ∀ e (_ : U123BarrierData (φ.toReflexive e)), Nonempty (SemanticSelfDescription.BarrierHypotheses F))
    (e₀ : E) (b : U123BarrierData (φ.toReflexive e₀)) :
    EnrichedR4ResidualWitness (φ.toReflexive e₀) (augmentedReprResidualPayloadFamily (φ.toReflexive e₀)) :=
  enrichedR4_u123_withAugmentedNemsProgramVRepr_sync φ (EngineNemsBarrierSync.ofSemanticSelfDescriptionFrame φ F h) e₀ b

def enrichedR4_tripleBarriers_withAugmentedNemsProgramVRepr_sync
    (φ : EngineReflexiveMorphism E World Obs Repr Claim) (S : EngineNemsBarrierSync φ) (e₀ : E)
    (d1 : DiagonalRepresentationalInterface (φ.toReflexive e₀))
    (d2 : ClosureObstructionInterface (φ.toReflexive e₀))
    (d3 : SemanticCertificationInterface (φ.toReflexive e₀)) :
    EnrichedR4ResidualWitness (φ.toReflexive e₀) (augmentedReprResidualPayloadFamily (φ.toReflexive e₀)) :=
  enriched_r4_from_triple_barriers_and_bridge (φ.toReflexive e₀) (augmentedReprResidualPayloadFamily (φ.toReflexive e₀))
    (augmentedReprNemsProgramVSyncPromotionBridge φ S e₀) d1 d2 d3

end StructuredNonexhaustibility
