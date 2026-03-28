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

## **C₁** — disciplined **full `U123` pack** on **`CodeEquiv`** (**SPEC_022_RA1**)

**`godelProvBicBarrierHypotheses_u123Augmented`** chains **`barrierHypotheses_augment_withGlobalConjunct`** three times
**(repr → closure → cert)**, matching **`U123BarrierData`** (**`Interfaces.lean`**). Each conjunct is the **paper-side**
abbreviation for the column; witnesses are **`b.reprBarrier`**, **`b.closureBarrier`**, **`b.certBarrier`** — **no** dummy
**`b`**.

**`u123SemanticBarrierLink_provBicU123TripleAugment`** packages this as **`U123SemanticBarrierLink`**; **`…Sync`** feeds enriched **R₄**
like **T1**/**T2**.

**Honesty:** this **strengthens** **`CodeEquiv`** with abstract **U₁–U₃** *interface* assumptions (not a claim that **ProvBic**
internal lemmas now mention **`Set World`** or **`Bool`** literals). Same honesty pattern as **T2** for **`(U₁)`**.

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

/--
**C₁ (core construction):** Gödel–**ProvBic** **`BarrierHypotheses`**, then global conjuncts for **`(U₁)∧(U₂)∧(U₃)`**
using the **three** fields of **`b : U123BarrierData A`**.
-/
def godelProvBicBarrierHypotheses_u123Augmented
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (G : Godel.GodelSystem) (S : SemanticSelfDescription.ProvBicArithmeticalSemantics G)
    (b : U123BarrierData A) :
    SemanticSelfDescription.BarrierHypotheses (SemanticSelfDescription.godelProvBicFrame G S) :=
  let bh0 := SemanticSelfDescription.godelProvBicBarrierHypotheses G S
  let bh1 := SemanticSelfDescription.barrierHypotheses_augment_withGlobalConjunct
    (bh := bh0) (P := DiagonalRepresentationalInterface A) (hP := b.reprBarrier)
  let bh2 := SemanticSelfDescription.barrierHypotheses_augment_withGlobalConjunct
    (bh := bh1) (P := ClosureObstructionInterface A) (hP := b.closureBarrier)
  SemanticSelfDescription.barrierHypotheses_augment_withGlobalConjunct
    (bh := bh2) (P := SemanticCertificationInterface A) (hP := b.certBarrier)

/--
**C₁:** **`U123SemanticBarrierLink`** with **`barrierHypotheses_of b := godelProvBicBarrierHypotheses_u123Augmented … b`**.
-/
def u123SemanticBarrierLink_provBicU123TripleAugment
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (G : Godel.GodelSystem) (S : SemanticSelfDescription.ProvBicArithmeticalSemantics G) :
    U123SemanticBarrierLink A (SemanticSelfDescription.godelProvBicFrame G S) where
  barrierHypotheses_of b := godelProvBicBarrierHypotheses_u123Augmented A G S b

/--
**T3:** enriched **R₄** with **triple-augmented** (**full **`U123`**) dependent link.
-/
def enrichedR4_provBic_u123TripleAugmentSync
    (φ : EngineReflexiveMorphism E World Obs Repr Claim)
    (G : Godel.GodelSystem) (S : SemanticSelfDescription.ProvBicArithmeticalSemantics G)
    (e₀ : E) (b : U123BarrierData (φ.toReflexive e₀)) :
    EnrichedR4ResidualWitness (φ.toReflexive e₀)
      (augmentedReprResidualPayloadFamily (φ.toReflexive e₀)) :=
  enrichedR4_u123_withAugmentedNemsProgramVRepr_u123DrivenSync
    (φ := φ) (F := SemanticSelfDescription.godelProvBicFrame G S)
    (L := fun e => u123SemanticBarrierLink_provBicU123TripleAugment (φ.toReflexive e) G S) e₀ b

theorem enrichedR4_provBic_u123TripleAugmentSync_nonempty
    (φ : EngineReflexiveMorphism E World Obs Repr Claim)
    (G : Godel.GodelSystem) (S : SemanticSelfDescription.ProvBicArithmeticalSemantics G)
    (e₀ : E) (b : U123BarrierData (φ.toReflexive e₀)) :
    Nonempty
      (EnrichedR4ResidualWitness (φ.toReflexive e₀)
        (augmentedReprResidualPayloadFamily (φ.toReflexive e₀))) :=
  ⟨enrichedR4_provBic_u123TripleAugmentSync φ G S e₀ b⟩

end StructuredNonexhaustibility
