import NemS.Prelude
import StructuralNonExhaustibility.Core.ReflexiveSystem
import ReflexiveArchitectureNonexhaustibility.Basic

/-!
# NemS Program V ↔ paper carriers (**EPIC_012** **D-001**, **SPEC_018_PN1`)

**Import smoke:** `StructuralNonExhaustibility.ReflexiveSystem` (**nems-lean** Program V shell)
is available alongside this repo’s **`ReflexiveArchitecture`** (**SPEC_002_AM1**).

**Anti-smuggling:** we **do not** define a blanket isomorphism `ReflexiveSystem ≃ ReflexiveArchitecture`.
Meaningful functors are **instantiation-specific** (engine lemmas supply Obs/Repr/success predicates).

**See also:** **`EngineReflexiveMorphism`** — generic **`E → ReflexiveArchitecture`** hook for published engine maps.
-/

namespace StructuredNonexhaustibility

universe u v

/--
**Readable alias** for NemS’s Program V reflexive-system **schema** (universe **levels match**
`StructuralNonExhaustibility.ReflexiveSystem`).
-/
abbrev NemsReflexiveSystemSchema : Type (max (u + 1) (v + 1)) :=
  StructuralNonExhaustibility.ReflexiveSystem.{u, v}

end StructuredNonexhaustibility
