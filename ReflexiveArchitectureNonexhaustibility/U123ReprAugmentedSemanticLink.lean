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

**Closing the loop:** specialize **`F`**, prove **`bh`** via **`SemanticSelfDescription.barrier_hypotheses_from_reflection`**,
pick the trivial obstruction architecture below for **`b`**, then call **`enrichedR4_trivialArchitecture_reprAugmentedU123Sync`**.
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

@[simp]
theorem barrierHypotheses_u123ReprAugment_eq
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    (bh : SemanticSelfDescription.BarrierHypotheses F) (b : U123BarrierData A) :
    barrierHypotheses_u123ReprAugment A F bh b =
      SemanticSelfDescription.barrierHypotheses_augment_withGlobalConjunct F bh (∀ ρ, ¬ A.repr_success ρ) b.reprBarrier :=
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

end StructuredNonexhaustibility
