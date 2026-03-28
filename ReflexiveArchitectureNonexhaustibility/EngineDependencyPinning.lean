import ReflexiveArchitectureNonexhaustibility.Basic

/-!
# D-001 — engine dependency pinning (**EPIC_012**, **SPEC_018_PN1**)

**Status:** **`nems-lean` pin is DEFERRED** — that library is **private**; this repo’s default **`lake build`**
must **not** depend on it. See the **BIG NOTE** block in **`lakefile.lean`** and the root **`README.md`**.

**When the pin is enabled:** replace this import with e.g. **`import NemS.Prelude`** (after uncommenting
**`require «nems-lean» …`** and running **`lake update`**).

**Policy:** **`PayloadPromotionBridge`** / **`ResidualEnrichment`** stay **interface-native** until **PN3–PN4**.
-/

namespace StructuredNonexhaustibility

end StructuredNonexhaustibility
