import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Interfaces
import ReflexiveArchitectureNonexhaustibility.Residuals

/-!
# D-002 — barrier-linked positive residual witness target (**EPIC_004**, **SPEC_004_RC1**)

**Registry:** parent-repo **D-002** in `docs/006_TECHNICAL_DEBT_REGISTRY.md`.

**Support for EPIC_005:** the **positive** disjunct of the abstract cover should eventually admit **typed**
`ResidualWitness`es that are **honestly tied** to architectural barrier / survivor data — not only the
schematic **`trivialR4ResidualWitness`** chain under triple anchored failure.

**Status:** this file **names** the composition-shaped obligation. **No** nontrivial barrier-to-witness
construction is claimed here yet (**TODO** below).

**Stage 0 (proved elsewhere):** **`PostFailureResidual.lean`** shows **U₁–U₃** force **`PositiveResidualProfile`**
with the **schematic** **`trivialR4ResidualWitness`** — the **post-failure** disjunct, **not** honest anchored
completion. **D-002** targets a **strictly stronger** barrier-linked witness when a **non-schematic** story is
required.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**D-002 (named target, open refinement):** from the three **U₁–U₃** interface hypotheses on `A`, exhibit
an **R₄-class** admissible residual witness suitable for downstream linkage with the **opaque** positive
branch.

**TODO (D-002):** construct **nontrivial** witnesses (or morphism + witness) from barrier content; prove
this target **without** ignoring the hypotheses. Until then, **`AbstractModeCover`/`Profiles`** may use
`trivialR4ResidualWitness` only as a **schematic** positive branch.
-/
def D002BarrierLinkedR4WitnessTarget (A : ReflexiveArchitecture World Obs Repr Claim) : Prop :=
  DiagonalRepresentationalInterface A →
    ClosureObstructionInterface A →
      SemanticCertificationInterface A →
        ∃ w : ResidualWitness, IsR4PositiveSurvivor w ∧ AdmissibleResidual w

end StructuredNonexhaustibility
