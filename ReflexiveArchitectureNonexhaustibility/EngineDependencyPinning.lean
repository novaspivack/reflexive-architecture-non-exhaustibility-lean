import NemS.Prelude

/-!
# D-001 — engine dependency pinning (**EPIC_012**, **SPEC_018_PN1**)

**PN1:** **`lakefile.lean`** requires sibling **`../../nems-lean`** (package **`«nems-lean»`**, toolchain **v4.29.0-rc6**).

**PN2 (this file):** minimal **import** from **nems-lean** so `lake build` proves the dependency **resolves**. Heavier
**NemS** modules stay out until **PN3–PN4** morphisms land.

**Policy:** **`PayloadPromotionBridge`** / **`ResidualEnrichment`** unchanged; native traces follow **SPEC_018_PN1**.
-/

namespace StructuredNonexhaustibility

-- Import-only: elaboration of `NemS.Prelude` is the **PN2** dependency check.

end StructuredNonexhaustibility
