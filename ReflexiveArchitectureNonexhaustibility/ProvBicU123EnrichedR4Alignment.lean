import SelfReference.Instances.Godel
import SemanticSelfDescription.Bridge.AugmentBarrierHypotheses
import SemanticSelfDescription.Instances.GodelProvBic
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Interfaces
import ReflexiveArchitectureNonexhaustibility.EngineReflexiveMorphism
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromNEMSProgramV

open SelfReference.Instances

/-!
# ProvBic → **`U123`** → enriched **R₄** (**SPEC_022_RA1**)

## **A_link_const** (frozen baseline)

* **A₁–A₃:** **`GodelSystem`**, **`ProvBicArithmeticalSemantics`**, **`godelProvBicBarrierHypotheses`**.
* **A₄:** **`U123SemanticBarrierLink.ofConstant bh`** — ignores **`b`** for the semantic bundle.
* **A₅:** **`EngineReflexiveMorphism`**, **`e₀`**, **`U123BarrierData`**.

## **A_link_dep** (repr-first — **non-constant in `b`**)

**`u123SemanticBarrierLink_provBicReprAugment`:** same global-conjunct pattern as the Kleene line
(**`barrierHypothesesPred_augment_withGlobalConjunct`** there), but here **`barrierHypotheses_augment_withGlobalConjunct`**
on **full** **`godelProvBicBarrierHypotheses`**, with **`Q := DiagonalRepresentationalInterface A`** and witness **`b.reprBarrier`**.

**Honesty:** **`barrierHypotheses_of b`** **uses** **`b.reprBarrier`** (not a discarded pattern match). The augmenting **`Prop`**
is **fixed** for **`A`**. **`closureBarrier` / `certBarrier`** unused here. **Not** an unconditional **`U123 ⇒ …`** theorem.

Both seams target **`enrichedR4_u123_withAugmentedNemsProgramVRepr_u123DrivenSync`**.
-/

set_option autoImplicit false

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**A₄ (constant link):** from **any** `ReflexiveArchitecture`, the ProvBic full summit yields a
**`U123SemanticBarrierLink`** by ignoring barrier-pack variation.
-/
def u123SemanticBarrierLink_provBicConstant
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (G : Godel.GodelSystem) (S : SemanticSelfDescription.ProvBicArithmeticalSemantics G) :
    U123SemanticBarrierLink A (SemanticSelfDescription.godelProvBicFrame G S) :=
  U123SemanticBarrierLink.ofConstant (SemanticSelfDescription.godelProvBicBarrierHypotheses G S)

variable {E : Type}

/--
**T1:** enriched **R₄** witness from the ProvBic summit through **`u123DrivenSync`**.
-/
def enrichedR4_provBic_u123ConstantSync
    (φ : EngineReflexiveMorphism E World Obs Repr Claim)
    (G : Godel.GodelSystem) (S : SemanticSelfDescription.ProvBicArithmeticalSemantics G)
    (e₀ : E) (b : U123BarrierData (φ.toReflexive e₀)) :
    EnrichedR4ResidualWitness (φ.toReflexive e₀)
      (augmentedReprResidualPayloadFamily (φ.toReflexive e₀)) :=
  enrichedR4_u123_withAugmentedNemsProgramVRepr_u123DrivenSync
    (φ := φ) (F := SemanticSelfDescription.godelProvBicFrame G S)
    (L := fun _ => u123SemanticBarrierLink_provBicConstant (φ.toReflexive _) G S) e₀ b

theorem enrichedR4_provBic_u123ConstantSync_nonempty
    (φ : EngineReflexiveMorphism E World Obs Repr Claim)
    (G : Godel.GodelSystem) (S : SemanticSelfDescription.ProvBicArithmeticalSemantics G)
    (e₀ : E) (b : U123BarrierData (φ.toReflexive e₀)) :
    Nonempty
      (EnrichedR4ResidualWitness (φ.toReflexive e₀)
        (augmentedReprResidualPayloadFamily (φ.toReflexive e₀))) :=
  ⟨enrichedR4_provBic_u123ConstantSync φ G S e₀ b⟩

/--
**A_link_dep:** **`U123SemanticBarrierLink`** whose **`barrierHypotheses_of b`** adjoins **`(U₁)`** / repr obstruction
via **`b.reprBarrier`** (cf. **`u123SemanticBarrierPredLink_kleeneReprAugment`** for **`BarrierHypothesesPred`**).
-/
def u123SemanticBarrierLink_provBicReprAugment
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (G : Godel.GodelSystem) (S : SemanticSelfDescription.ProvBicArithmeticalSemantics G) :
    U123SemanticBarrierLink A (SemanticSelfDescription.godelProvBicFrame G S) where
  barrierHypotheses_of b :=
    SemanticSelfDescription.barrierHypotheses_augment_withGlobalConjunct
      (bh := SemanticSelfDescription.godelProvBicBarrierHypotheses G S)
      (P := DiagonalRepresentationalInterface A) (hP := b.reprBarrier)

/--
**T2:** enriched **R₄** with **repr-augmented** dependent **`U123`** link.
-/
def enrichedR4_provBic_u123ReprAugmentSync
    (φ : EngineReflexiveMorphism E World Obs Repr Claim)
    (G : Godel.GodelSystem) (S : SemanticSelfDescription.ProvBicArithmeticalSemantics G)
    (e₀ : E) (b : U123BarrierData (φ.toReflexive e₀)) :
    EnrichedR4ResidualWitness (φ.toReflexive e₀)
      (augmentedReprResidualPayloadFamily (φ.toReflexive e₀)) :=
  enrichedR4_u123_withAugmentedNemsProgramVRepr_u123DrivenSync
    (φ := φ) (F := SemanticSelfDescription.godelProvBicFrame G S)
    (L := fun e => u123SemanticBarrierLink_provBicReprAugment (φ.toReflexive e) G S) e₀ b

theorem enrichedR4_provBic_u123ReprAugmentSync_nonempty
    (φ : EngineReflexiveMorphism E World Obs Repr Claim)
    (G : Godel.GodelSystem) (S : SemanticSelfDescription.ProvBicArithmeticalSemantics G)
    (e₀ : E) (b : U123BarrierData (φ.toReflexive e₀)) :
    Nonempty
      (EnrichedR4ResidualWitness (φ.toReflexive e₀)
        (augmentedReprResidualPayloadFamily (φ.toReflexive e₀))) :=
  ⟨enrichedR4_provBic_u123ReprAugmentSync φ G S e₀ b⟩

end StructuredNonexhaustibility
