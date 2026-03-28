import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.EngineReflexiveMorphism

/-!
# D-001 — engine dependency pinning (**EPIC_012**, **SPEC_018_PN1**)

**Status:** **`nems-lean` pin is DEFERRED** — that library is **private**; this repo’s default **`lake build`**
must **not** depend on it. See the **BIG NOTE** block in **`lakefile.lean`** and the root **`README.md`**.

**When the pin is enabled:** replace **`import ReflexiveArchitectureNonexhaustibility.EngineReflexiveMorphism`** with
e.g. **`import NemS.Prelude`** **additionally** (after uncommenting **`require «nems-lean» …`** and running **`lake update`**).

**PN3–PN4 (engine-agnostic):** **`EngineReflexiveMorphism`** + **`ResidualEnrichment/Bridges/FromNativeTraces`**
provide the morphism and **native-trace** **`PayloadPromotionBridge`** seam; default bridges remain **interface-native**.
-/

namespace StructuredNonexhaustibility

end StructuredNonexhaustibility
