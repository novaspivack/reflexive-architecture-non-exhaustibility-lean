import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Interfaces
import ReflexiveArchitectureNonexhaustibility.Instances.ONE

/-!
# Engine → reflexive morphism (**EPIC_012** **PN3**, **SPEC_003_BT1**)

**PN1–PN2 deferred:** there is no pinned **`NemS`** import in the default build. This module
standardises the **attachment shape** real engines are expected to publish: a type of engine
carriers and a map into **`ReflexiveArchitecture`**, with **U₁–U₃** expressed as **`U123BarrierData`**
on the **image** architecture.

**Anti-smuggling:** we **do not** import conjectural NemS types; **`EngineCarrier`** is an
arbitrary parameter until **D-001** enables **`require «nems-lean»`**.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**PN3 morphism:** any functorial presentation **`E → ReflexiveArchitecture`** is the canonical
hook for engine transport. NemS (or any sibling) should elaborate this map; barriers are **per**
**`A`**, hence **per engine point** when **`A` varies** with **`e : E`**.
-/
structure EngineReflexiveMorphism (EngineCarrier : Type) (World Obs Repr Claim : Type) where
  /-- Engine-published map into the reflexive carrier (**SPEC_002_AM1** fields live on the codomain). -/
  toReflexive : EngineCarrier → ReflexiveArchitecture World Obs Repr Claim

/--
**U₁–U₃** certificate at a chosen engine point — exactly **`U123BarrierData (φ.toReflexive e)`**,
aligned with **`Interfaces.lean`** (**`SPEC_003_BT1`**).
-/
abbrev EngineU123BarrierData {E : Type} (φ : EngineReflexiveMorphism E World Obs Repr Claim) (e : E) :
    Type :=
  U123BarrierData (φ.toReflexive e)

/--
Bundle a fixed architecture with its barriers — **identity** “morphism” case used when the engine
already **is** a **`ReflexiveArchitecture`**.
-/
structure ReflexiveBarrierBundle (World Obs Repr Claim : Type) where
  arch : ReflexiveArchitecture World Obs Repr Claim
  bar : U123BarrierData arch

/--
**EPIC_007 / ONE:** a barrier bundle yields **`OneRouteDiscipline`** on **`arch`**.
-/
theorem oneRouteDiscipline_of_barrier_bundle (B : ReflexiveBarrierBundle World Obs Repr Claim) :
    OneRouteDiscipline B.arch :=
  ⟨B.bar.reprBarrier, B.bar.closureBarrier, B.bar.certBarrier⟩

end StructuredNonexhaustibility
