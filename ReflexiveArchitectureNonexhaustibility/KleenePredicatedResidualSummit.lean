import SemanticSelfDescription.Bridge.AugmentBarrierHypotheses
import SemanticSelfDescription.Instances.KleenePartrec
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Interfaces
import ReflexiveArchitectureNonexhaustibility.EngineReflexiveMorphism
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromNEMSProgramV

/-!
# Kleene / Partrec **predicated residual summit** (**SPEC_019_PS1**)

**Summit statement:** the concrete computational Paper 51 frame **`kleenePartrecFrame`** supports the full
**predicated** chain

`F_Kleene` → **`BarrierHypothesesPred`** (**`Computable`**) → repr-augmented **`U123SemanticBarrierPredLink`** →
**`enrichedR4_u123_withAugmentedNemsProgramVRepr_predLinkSync`**.

This is the **achieved** computational target. Unconditional **`BarrierHypotheses`** remains a **strictly stronger,
optional** layer (needs **all**-transformer Rogers / reflection — **not** supplied by the Kleene instance).

See **`SemanticSelfDescription.Theorems.KleenePredicatedSummit`** and
**`StructuralNonExhaustibility.Bridges.ToSemanticSelfDescription`** (**`reflexiveSystem_ofSelfSemanticFramePred`**).
-/

set_option autoImplicit false

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
Constant **predicated** `U123` link for **`kleenePartrecFrame`**: adjoin the global `(U₁)` conjunct from **`b.reprBarrier`**.
-/
def u123SemanticBarrierPredLink_kleeneReprAugment
    (A : ReflexiveArchitecture World Obs Repr Claim) :
    U123SemanticBarrierPredLink A SemanticSelfDescription.kleenePartrecFrame
      SemanticSelfDescription.kleeneComputableTransformerPred where
  barrierHypothesesPred_of b :=
    SemanticSelfDescription.barrierHypothesesPred_augment_withGlobalConjunct
      (F := SemanticSelfDescription.kleenePartrecFrame) SemanticSelfDescription.kleeneComputationalBarrierHypotheses
      (DiagonalRepresentationalInterface A) b.reprBarrier

variable {E : Type}

/--
**Kleene predicated summit** on an engine morphism: **enriched R₄** at **`e₀`** from **`U123BarrierData`**.
-/
def enrichedR4_Kleene_predReprSummit
    (φ : EngineReflexiveMorphism E World Obs Repr Claim) (e₀ : E) (b : U123BarrierData (φ.toReflexive e₀)) :
    EnrichedR4ResidualWitness (φ.toReflexive e₀) (augmentedReprResidualPayloadFamily (φ.toReflexive e₀)) :=
  enrichedR4_u123_withAugmentedNemsProgramVRepr_predLinkSync φ SemanticSelfDescription.kleenePartrecFrame
    (fun e => u123SemanticBarrierPredLink_kleeneReprAugment (φ.toReflexive e)) e₀ b

/--
**Summit-grade existence:** from any engine point and **D‑002** barrier pack on the image architecture, the Kleene
predicated pipeline yields an **enriched R₄** witness.
-/
theorem kleene_predicated_residual_summit_nonempty
    (φ : EngineReflexiveMorphism E World Obs Repr Claim) (e₀ : E) (b : U123BarrierData (φ.toReflexive e₀)) :
    Nonempty
      (EnrichedR4ResidualWitness (φ.toReflexive e₀) (augmentedReprResidualPayloadFamily (φ.toReflexive e₀))) :=
  ⟨enrichedR4_Kleene_predReprSummit φ e₀ b⟩

end StructuredNonexhaustibility
