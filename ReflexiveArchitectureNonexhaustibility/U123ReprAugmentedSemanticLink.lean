import SemanticSelfDescription.Bridge.AugmentBarrierHypotheses
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Interfaces
import ReflexiveArchitectureNonexhaustibility.EngineReflexiveMorphism
import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Bridges.FromNEMSProgramV

/-!
# Representational **`U123`** augmentation of Paper 51 barriers (**EPIC_012** concrete link)

This is the **first** non-constant **`U123SemanticBarrierLink`** pattern endorsed by the repo:

* **Frame / base hypotheses** `bh : BarrierHypotheses F` come from NemS (**e.g.** `barrier_hypotheses_from_reflection` on a
  certified `SelfSemanticFrame`).
* **Paper U₁** enters as a **global conjunct** on `CodeEquiv`, with proof supplied by **`b.reprBarrier`**.
* **`barrierHypotheses_of b`** is **`barrierHypotheses_augment_withGlobalConjunct`** applied to **`b.reprBarrier`** —
  so **`sync`** in **`ofU123SemanticBarrierLink`** is **not** constant in **`b`** at the **proof-term** level (the
  witness for the `∧ P` Half of `hFP` is **literally** `b.reprBarrier`).

**Architecture-specific:** the predicate **`∀ ρ, ¬ A.repr_success ρ`** and the **`U123BarrierData`** interface.

**Frame-specific:** the choice of **`F`** and **`bh`** (reflection encodeability, nontrivial codes, …).

**Reusable:** `SemanticSelfDescription.Bridge.AugmentBarrierHypotheses` (nems-lean) + this wrapper.

**Closed computational witness (Kleene / `Nat.Partrec.Code`):** **`SemanticSelfDescription.Instances.KleenePartrec`**
gives **`kleenePartrecFrame`**, **`kleeneComputationalBarrierHypotheses`** (**`BarrierHypothesesPred`** with
**`P = Computable`**), extensional **`kleeneCodeEquiv`**, and **`EncodedNontrivial`**. This does **not** collapse to
unconditional **`BarrierHypotheses`** (Rogers fixed points are only assumed for **computable** maps). Use
**`barrierHypothesesPred_augment_withGlobalConjunct`** for the same **`(U₁)`** global conjunct as below; upgrade to
**`BarrierHypotheses`** only when **`BarrierHypothesesPred.toBarrierHypotheses`** applies (**`∀ F', P F'`**).

**Closing the loop (parameter-free unconditional `bh`):** still needs **full** **`BarrierHypotheses`** together with
**`EncodedNontrivial`** and representability beyond the **`Computable`**-predicate boundary.
**nems-lean** pins the tensions: **`false_of_encodedNontrivial_*`**, **`not_nonempty_sri0'_nat_equiv_eq`**, …
**`enrichedR4_trivialArchitecture_reprAugmentedU123Sync`** takes unconditional **`bh`**; for Kleene use the
**pred** augment path unless **`toBarrierHypotheses`** is available.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
Layer‑1 **vacuous** obstruction: every proposed gadget fails because success predicates are **`False`** outright.

Useful as a **minimal** carrier for a real **`U123BarrierData`** (all three barriers are immediate).
-/
def trivialObstructionReflexiveArchitecture (World Obs Repr Claim : Type) (obs₀ : Obs) :
    ReflexiveArchitecture World Obs Repr Claim where
  observe := fun _ => obs₀
  repr_success := fun _ => False
  closure_success := fun _ => False
  cert_success := fun _ => False

/--
Canonical triple barrier pack for **`trivialObstructionReflexiveArchitecture`**.
-/
def trivialObstructionU123BarrierData (World Obs Repr Claim : Type) (obs₀ : Obs) :
    U123BarrierData (trivialObstructionReflexiveArchitecture World Obs Repr Claim obs₀) :=
  ⟨fun _ h => False.elim h, fun _ h => False.elim h, fun _ h => False.elim h⟩

variable {W : Type}

/--
**Augment** a fixed NemS **`bh`** with the representational half of **`b`** (global `(U₁)`).

`barrierHypotheses_of b` **mentions** `b.reprBarrier` — not **`const`** after η‑expansion.
-/
def barrierHypotheses_u123ReprAugment
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    (bh : SemanticSelfDescription.BarrierHypotheses F)
    (b : U123BarrierData A) :
    SemanticSelfDescription.BarrierHypotheses F :=
  SemanticSelfDescription.barrierHypotheses_augment_withGlobalConjunct F bh (∀ ρ, ¬ A.repr_success ρ) b.reprBarrier

/--
Same **global `(U₁)`** conjunct for **`BarrierHypothesesPred`** (Kleene / Rogers **`P`** preserved).
-/
def barrierHypothesesPred_u123ReprAugment
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    {P : (F.Code → F.Code) → Prop}
    (bh : SemanticSelfDescription.BarrierHypothesesPred F P)
    (b : U123BarrierData A) :
    SemanticSelfDescription.BarrierHypothesesPred F P :=
  SemanticSelfDescription.barrierHypothesesPred_augment_withGlobalConjunct F bh (∀ ρ, ¬ A.repr_success ρ) b.reprBarrier

@[simp]
theorem barrierHypotheses_u123ReprAugment_eq
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    (bh : SemanticSelfDescription.BarrierHypotheses F) (b : U123BarrierData A) :
    barrierHypotheses_u123ReprAugment A F bh b =
      SemanticSelfDescription.barrierHypotheses_augment_withGlobalConjunct F bh (∀ ρ, ¬ A.repr_success ρ) b.reprBarrier :=
  rfl

@[simp]
theorem barrierHypothesesPred_u123ReprAugment_eq
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    {P : (F.Code → F.Code) → Prop}
    (bh : SemanticSelfDescription.BarrierHypothesesPred F P) (b : U123BarrierData A) :
    barrierHypothesesPred_u123ReprAugment A F bh b =
      SemanticSelfDescription.barrierHypothesesPred_augment_withGlobalConjunct F bh (∀ ρ, ¬ A.repr_success ρ)
        b.reprBarrier :=
  rfl

/--
**`U123SemanticBarrierLink`** obtained by representational augmentation of **`bh`**.
-/
def u123SemanticBarrierLink_reprAugment
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    (bh : SemanticSelfDescription.BarrierHypotheses F) :
    U123SemanticBarrierLink A F where
  barrierHypotheses_of b := barrierHypotheses_u123ReprAugment A F bh b

/--
Reference **`barrierHypothesesPred_u123ReprAugment`**; yields unconditional **`BarrierHypotheses`** only after
**`BarrierHypothesesPred.toBarrierHypotheses`** (i.e. when **`P F'`** is automatic for every **`F'`**).
-/
def u123SemanticBarrierLink_predReprAugment
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    {P : (F.Code → F.Code) → Prop}
    (bh : SemanticSelfDescription.BarrierHypothesesPred F P)
    (hP : ∀ F' : F.Code → F.Code, P F') :
    U123SemanticBarrierLink A F where
  barrierHypotheses_of b :=
    SemanticSelfDescription.BarrierHypothesesPred.toBarrierHypotheses (F := F)
      (barrierHypothesesPred_u123ReprAugment A F bh b) hP

variable {E : Type}

/--
Constant engine morphism to a fixed architecture (**identity-on-carrier** pattern).
-/
def engineMorphism_constArchitecture (A : ReflexiveArchitecture World Obs Repr Claim) :
    EngineReflexiveMorphism E World Obs Repr Claim :=
  ⟨fun _ => A⟩

/--
**EngineNemsBarrierSync** for **`u123SemanticBarrierLink_reprAugment`** at every engine point.
-/
def engineNemsSync_u123ReprAugment
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    (bh : SemanticSelfDescription.BarrierHypotheses F) :
    EngineNemsBarrierSync (engineMorphism_constArchitecture (E := E) A) :=
  EngineNemsBarrierSync.ofU123SemanticBarrierLink
    (engineMorphism_constArchitecture (E := E) A) F fun _ => u123SemanticBarrierLink_reprAugment A F bh

/--
**`EngineNemsBarrierSync`** when the repr-augmented package stays at **`BarrierHypothesesPred`** level until **`hP`** closes **`P`** for all transformers.
-/
def engineNemsSync_u123PredReprAugment
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    {P : (F.Code → F.Code) → Prop}
    (bh : SemanticSelfDescription.BarrierHypothesesPred F P)
    (hP : ∀ F' : F.Code → F.Code, P F') :
    EngineNemsBarrierSync (engineMorphism_constArchitecture (E := E) A) :=
  EngineNemsBarrierSync.ofU123SemanticBarrierLink
    (engineMorphism_constArchitecture (E := E) A) F fun _ => u123SemanticBarrierLink_predReprAugment A F bh hP

/--
**End-to-end enriched R₄** for the constant morphism, **repr**‑augmented NemS sync, and an arbitrary **`b`**.
-/
def enrichedR4_u123ReprAugmentSync
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    (bh : SemanticSelfDescription.BarrierHypotheses F)
    (e₀ : E) (b : U123BarrierData A) :
    EnrichedR4ResidualWitness A (augmentedReprResidualPayloadFamily A) :=
  enrichedR4_u123_withAugmentedNemsProgramVRepr_sync
    (engineMorphism_constArchitecture (E := E) A)
    (engineNemsSync_u123ReprAugment (E := E) A F bh) e₀ b

/--
**Enriched R₄** with repr-augmented **`BarrierHypothesesPred`** + **`hP`** (same **`b`** slot as **`enrichedR4_u123ReprAugmentSync`**).
-/
def enrichedR4_u123PredReprAugmentSync
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    {P : (F.Code → F.Code) → Prop}
    (bh : SemanticSelfDescription.BarrierHypothesesPred F P)
    (hP : ∀ F' : F.Code → F.Code, P F')
    (e₀ : E) (b : U123BarrierData A) :
    EnrichedR4ResidualWitness A (augmentedReprResidualPayloadFamily A) :=
  enrichedR4_u123_withAugmentedNemsProgramVRepr_sync
    (engineMorphism_constArchitecture (E := E) A)
    (engineNemsSync_u123PredReprAugment (E := E) A F bh hP) e₀ b

/--
**Specialization** to the **trivial** obstruction architecture (minimal **`b`** family above).
-/
def enrichedR4_trivialArchitecture_reprAugmentedU123Sync
    (World Obs Repr Claim : Type) (obs₀ : Obs)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    (bh : SemanticSelfDescription.BarrierHypotheses F)
    (e₀ : E)
    (b :
      U123BarrierData (trivialObstructionReflexiveArchitecture World Obs Repr Claim obs₀)) :
    EnrichedR4ResidualWitness (trivialObstructionReflexiveArchitecture World Obs Repr Claim obs₀)
      (augmentedReprResidualPayloadFamily (trivialObstructionReflexiveArchitecture World Obs Repr Claim obs₀)) :=
  enrichedR4_u123ReprAugmentSync (trivialObstructionReflexiveArchitecture World Obs Repr Claim obs₀) F bh e₀ b

/--
**Trivial** architecture + **`BarrierHypothesesPred`** path (**requires** **`hP`**).
-/
def enrichedR4_trivialArchitecture_predReprAugmentedU123Sync
    (World Obs Repr Claim : Type) (obs₀ : Obs)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    {P : (F.Code → F.Code) → Prop}
    (bh : SemanticSelfDescription.BarrierHypothesesPred F P)
    (hP : ∀ F' : F.Code → F.Code, P F')
    (e₀ : E)
    (b :
      U123BarrierData (trivialObstructionReflexiveArchitecture World Obs Repr Claim obs₀)) :
    EnrichedR4ResidualWitness (trivialObstructionReflexiveArchitecture World Obs Repr Claim obs₀)
      (augmentedReprResidualPayloadFamily (trivialObstructionReflexiveArchitecture World Obs Repr Claim obs₀)) :=
  enrichedR4_u123PredReprAugmentSync (trivialObstructionReflexiveArchitecture World Obs Repr Claim obs₀) F bh hP e₀ b

end StructuredNonexhaustibility
