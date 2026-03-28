import NemS.Prelude
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.EngineReflexiveMorphism

/-!
# D-001 — engine dependency pinning (**EPIC_012**, **SPEC_018_PN1**)

**Status:** **`nems-lean`** is **`require`d** (**path** pin in **`lakefile.lean`**). **`import NemS.Prelude`** is the
**smoke** surface; heavier NemS barrels stay **optional** per task.

**Also:** **`NemsStructuralProgramLink`** (Program V **`ReflexiveSystem`** alias), **`EngineReflexiveMorphism`**,
**`FromNativeTraces`** — morphism + **native-trace** **`PayloadPromotionBridge`** seam.
-/

namespace StructuredNonexhaustibility

/-- **`NemS.Prelude`** / **`nems-lean`** resolve under the active **`lakefile`** pin. -/
theorem nems_engine_dependency_ok : True := trivial

end StructuredNonexhaustibility
