import SelfReference.Instances.Godel
import SemanticSelfDescription.Instances.GodelProvBic
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Interfaces
import ReflexiveArchitectureNonexhaustibility.EngineReflexiveMorphism
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromNEMSProgramV

open SelfReference.Instances

/-!
# ProvBic → **`U123`** → enriched **R₄** (**SPEC_022_RA1**, **A_link_const**)

**Conditional O7 / reflexive alignment** at the **minimal** honest package:

* **A₁–A₃:** a **`GodelSystem`** + **`ProvBicArithmeticalSemantics`** + canonical **`godelProvBicBarrierHypotheses`**.
* **A₄:** **`U123SemanticBarrierLink.ofConstant bh`** — the semantic link is **constant** in the D-002 pack **`b`**
  (every pack maps to the **same** full **`BarrierHypotheses`** witness).
* **A₅:** an **`EngineReflexiveMorphism`** + a chosen point **`e₀`** + **`U123BarrierData`** on **`φ.toReflexive e₀`**.

**Not implied:** pack-dependent certificates (**`A_link_dep`**), frame isomorphism with Kleene, or any new unconditional
bridge from **`U123`** alone.

**Target:** reuse **`enrichedR4_u123_withAugmentedNemsProgramVRepr_u123DrivenSync`** (full **`U123SemanticBarrierLink`**, not
the predicated Kleene link).
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

end StructuredNonexhaustibility
