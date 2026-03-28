import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Interfaces
import ReflexiveArchitectureNonexhaustibility.Residuals

/-!
# D-002 — barrier-linked positive residual witness (**EPIC_004**, **SPEC_004_RC1**)

**Registry:** parent-repo **D-002** in `docs/006_TECHNICAL_DEBT_REGISTRY.md`.

**Abstract solution (Option B, 2026-03-28):** package **U₁–U₃** into **`U123BarrierData A`** (**`Interfaces.lean`**)
and build **`ResidualWitness`** with **`carrier := U123BarrierData A`** and witness point **the pack itself**.
This is **genuinely barrier-linked**: the witness is **not** **`trivialR4ResidualWitness`** (**`Unit`**, **`()`**);
hypotheses **`d₁–d₃`** appear in the **construction** — eliminating them from context would change the **typed**
witness data (unlike a constant **`Unit`** map ignoring arguments).

**Concrete engines (RI / RFO / ICA-SEM payloads):** still optional (**D-001**); this file stays **interface-native**.

**Stage 0 upgrade:** **`PostFailureResidual.lean`** now uses **`barrierLinkedR4ResidualWitness`** in the forced
**`PositiveResidualProfile`** theorem.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**D-002 target:** from **U₁–U₃** on `A`, produce an **R₄-class** admissible residual witness suitable for opaque
positive-branch linkage.
-/
def D002BarrierLinkedR4WitnessTarget (A : ReflexiveArchitecture World Obs Repr Claim) : Prop :=
  DiagonalRepresentationalInterface A →
    ClosureObstructionInterface A →
      SemanticCertificationInterface A →
        ∃ w : ResidualWitness, IsR4PositiveSurvivor w ∧ AdmissibleResidual w

/--
**Barrier-linked R₄ witness:** **`carrier`** is **`U123BarrierData A`**, **`witness`** is **`⟨d₁,d₂,d₃⟩`** — not
**`Unit`** / **`()`**.
-/
def barrierLinkedR4ResidualWitness {A : ReflexiveArchitecture World Obs Repr Claim}
    (d1 : DiagonalRepresentationalInterface A)
    (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) : ResidualWitness :=
  ⟨ResidualClass.R4, U123BarrierData A, ⟨d1, d2, d3⟩⟩

theorem isR4_barrierLinkedR4ResidualWitness {A : ReflexiveArchitecture World Obs Repr Claim}
    (d1 : DiagonalRepresentationalInterface A)
    (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    IsR4PositiveSurvivor (barrierLinkedR4ResidualWitness d1 d2 d3) :=
  rfl

theorem admissible_barrierLinkedR4ResidualWitness {A : ReflexiveArchitecture World Obs Repr Claim}
    (d1 : DiagonalRepresentationalInterface A)
    (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    AdmissibleResidual (barrierLinkedR4ResidualWitness d1 d2 d3) := by
  right
  refine ⟨World, Obs, Repr, Claim, A, d1, d2, d3, ?_⟩
  rfl

/--
**D-002 (abstract layer):** barrier-linked **R₄** witness **constructively** from **U₁–U₃**.
-/
theorem d002_barrier_linked_r4_witness_holds (A : ReflexiveArchitecture World Obs Repr Claim) :
    D002BarrierLinkedR4WitnessTarget A := by
  intro d1 d2 d3
  refine ⟨barrierLinkedR4ResidualWitness d1 d2 d3, ?_, ?_⟩
  · exact isR4_barrierLinkedR4ResidualWitness d1 d2 d3
  · exact admissible_barrierLinkedR4ResidualWitness d1 d2 d3

end StructuredNonexhaustibility
