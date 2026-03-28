import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.D002ResidualWitnessTarget
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Profiles
import ReflexiveArchitectureNonexhaustibility.Interfaces

/-!
# Post-failure residual (Layer 1 aftermath) (**SPEC_004_RC1**, **SPEC_010_US1**, **D-002**)

**Layer 1 impossibility:** **`barriered_architecture_admits_no_true_honest_anchored_internal_completion`**
(**`PaperDAnchoredChain.lean`**) — no architecture satisfying **U₁–U₃** admits a **true**
**`HonestAnchoredInternalCompletion`** package. **Positive R₄** is **not** a fourth **burden-faithful**
“completion mode” in that story.

**This file (Layer 2 / aftermath hook):** for **any** opaque attempt over `arch`, the three **barrier
interfaces** force **failure** of the three **anchored** canonical success profiles at `anchor`. Hence
**`PositiveResidualProfile`** holds **intuitionistically**, using **`barrierLinkedR4ResidualWitness`** from
**`D002ResidualWitnessTarget.lean`** (**`U123BarrierData`** on **`carrier`**, not **`Unit`**).

**Reading:** this is the **forced survivor disjunct** once M₁–M₃ **success** is ruled out at the anchor — **not**
“internal completion succeeds through R₄.”

**Engines:** further **payload** refinement (RI / RFO / ICA-SEM data in a witness) waits on **D-001** pinning;
the abstract **barrier-pack** linkage is **proved** (**`d002_barrier_linked_r4_witness_holds`**).
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

theorem not_representationalProfile_of_diagonalBarrier
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface a.arch) :
    ¬RepresentationalProfile a :=
  fun h => d1 (a.reprAt a.anchor) h

theorem not_closureProfile_of_closureBarrier
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (d2 : ClosureObstructionInterface a.arch) :
    ¬ClosureProfile a :=
  fun h => d2 (a.closureAt a.anchor) h

theorem not_certificatoryProfile_of_semanticBarrier
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (d3 : SemanticCertificationInterface a.arch) :
    ¬CertificatoryProfile a :=
  fun h => d3 (a.certAt a.anchor) h

/--
**Post-failure (barrier-linked R₄):** **U₁–U₃** on `a.arch` force **`PositiveResidualProfile a`** with
**`barrierLinkedR4ResidualWitness d₁ d₂ d₃`** — **intuitionistic**; witness **depends on** the barrier
hypotheses via **`U123BarrierData a.arch`** on **`carrier`**.
-/
theorem positive_residual_profile_of_triple_barriers_at_anchor
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface a.arch)
    (d2 : ClosureObstructionInterface a.arch)
    (d3 : SemanticCertificationInterface a.arch) :
    PositiveResidualProfile a :=
  ⟨barrierLinkedR4ResidualWitness d1 d2 d3,
    isR4_barrierLinkedR4ResidualWitness d1 d2 d3,
    not_representationalProfile_of_diagonalBarrier a d1,
    not_closureProfile_of_closureBarrier a d2,
    not_certificatoryProfile_of_semanticBarrier a d3⟩

end StructuredNonexhaustibility
