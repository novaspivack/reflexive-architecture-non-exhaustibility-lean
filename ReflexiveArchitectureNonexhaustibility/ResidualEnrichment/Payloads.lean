import ReflexiveArchitectureNonexhaustibility.Basic

/-!
# Residual payload interfaces (**SPEC_016_ER1**, **EPIC_011**)

**Post–abstract D-002:** obstruction hypotheses are already packaged in **`U123BarrierData`**. This module adds
**typed payload slots** so concrete engines (**D-001**) can transport **content** — not only the bare barrier
triple — without importing heavyweight repos here.

**Anti-smuggling:** payload carriers are **parameters** (`Type` slots per architecture). We **do not** assert
that payloads encode “successful completion” or collapse R₄ into a fourth mode.

**Paper phases:** F1 (interfaces) — this file; F2 (promotion) — **`Promotion.lean`**; F3 (bridges) — **`Bridges/*`**.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**Signature** tagging which obstruction family’s payload is carried (**interface-only**).

Used for **sigma-style** indexed payloads (`**SigmaResidualPayload**`).
-/
inductive ObstructionSignature : Type where
  /-- Representational / diagonal-style obstruction payload. -/
  | reprDiag : ObstructionSignature
  /-- Closure / hull-style obstruction payload. -/
  | closureObstruction : ObstructionSignature
  /-- Certification / self-semantic obstruction payload. -/
  | certSemantic : ObstructionSignature
  /-- Mixed / triple-linked payload (all three families coordinated). -/
  | mixedTriple : ObstructionSignature

/--
**Payload family:** four **`Type`** carriers per architecture — **engines** (**D-001**) populate these; the
abstract layer **quantifies** over them.
-/
structure ResidualPayloadFamily (A : ReflexiveArchitecture World Obs Repr Claim) where
  reprPayload : Type
  closurePayload : Type
  certPayload : Type
  mixedPayload : Type

/--
Indexed payload type for a given **ObstructionSignature**.
-/
def PayloadFor {A : ReflexiveArchitecture World Obs Repr Claim} (F : ResidualPayloadFamily A) :
    ObstructionSignature → Type
  | .reprDiag => F.reprPayload
  | .closureObstruction => F.closurePayload
  | .certSemantic => F.certPayload
  | .mixedTriple => F.mixedPayload

/--
**Dependent pair:** chosen obstruction tag + value in the matching payload carrier.
-/
structure SigmaResidualPayload {A : ReflexiveArchitecture World Obs Repr Claim}
    (F : ResidualPayloadFamily A) : Type where
  sig : ObstructionSignature
  val : PayloadFor F sig

end StructuredNonexhaustibility
