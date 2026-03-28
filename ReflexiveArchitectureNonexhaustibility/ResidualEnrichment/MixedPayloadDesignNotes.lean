import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Payloads

/-!
# Mixed residual payload — design notes (**SPEC_017_MX1**)

**No implementation in this module** — only a **Lean-anchored** pointer for agents and `rg`.

**F3 column pattern (common schema):** for each canonical column, a Π-type over the column’s gadget type with
fiberwise **`PLift (¬ success …)`**, extracted from the matching field of **`U123BarrierData`**, packaged as
**`PayloadPromotionBridge`** into **`SigmaResidualPayload`** with the matching **`ObstructionSignature`**.

**Mixed (multi-column) recommendation:** under **simultaneous** U₁–U₃, model **`mixedTriple`** payloads as a **three-field
record** (product) of the **same** column payload types used in **`FromRI`**, **`FromRFO`**, and **`FromSEM`** — **not**
as a coproduct of those types. The coproduct / sigma shape is already **`SigmaResidualPayload`** for **single-column**
selection.

**Alternates (see spec):** optional-field records for **partial** barrier packs; finite-support families if the
obstruction taxonomy grows beyond three fixed columns.

**Normative design (parent repo):** `specs/INCOMPLETE/IN-PROCESS/EPIC_011_ENGINE_ENRICHED_RESIDUAL_SUMMIT/SPEC_017_MX1_MIXED_RESIDUAL_CONTENT_DESIGN.md`.
-/

namespace StructuredNonexhaustibility

end StructuredNonexhaustibility
