import ReflexiveArchitectureNonexhaustibility.ResidualEnrichment.Payloads

/-!
# Mixed residual payload — design notes

**Implementation:** **`Bridges/FromMixedTriple.lean`** — **`MixedTripleObstructionPayload`**, **`mixedTriplePayloadPromotionBridge`**,
**`enrichedR4_tripleBarriers_withMixedTriplePayload`**. This module remains a short **design rationale** anchor.

**F3 column pattern (common schema):** for each canonical column, a Π-type over the column’s gadget type with
fiberwise **`PLift (¬ success …)`**, extracted from the matching field of **`U123BarrierData`**, packaged as
**`PayloadPromotionBridge`** into **`SigmaResidualPayload`** with the matching **`ObstructionSignature`**.

**Mixed (multi-column) recommendation:** under **simultaneous** U₁–U₃, model **`mixedTriple`** payloads as a **three-field
record** (product) of the **same** column payload types used in **`FromRI`**, **`FromRFO`**, and **`FromSEM`** — **not**
as a coproduct of those types. The coproduct / sigma shape is already **`SigmaResidualPayload`** for **single-column**
selection.

**Alternates:** optional-field records for **partial** barrier packs; finite-support families if the
obstruction taxonomy grows beyond three fixed columns.
-/

namespace StructuredNonexhaustibility

end StructuredNonexhaustibility
