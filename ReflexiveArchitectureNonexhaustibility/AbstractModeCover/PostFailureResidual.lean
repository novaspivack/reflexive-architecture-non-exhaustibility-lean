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
**`PositiveResidualProfile`** holds **intuitionistically**, via the existing **`positive_residual_profile_of_three_failures`**
packaging — currently with the **schematic** **`trivialR4ResidualWitness`**.

**Reading:** this is the **forced survivor disjunct** once M₁–M₃ **success** is ruled out at the anchor — **not**
“internal completion succeeds through R₄.” It is the mathematical locus for **what the cover leaves** once
barriers kill canonical completion.

**D-002:** **`D002BarrierLinkedR4WitnessTarget`** asks for a **nontrivial barrier-derived** witness, not the
schematic stub. That strengthening is **orthogonal** to the Layer 1 impossibility theorem and remains the
right place for engine-linked / witness-production mathematics.
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
**Post-failure (schematic R₄):** **U₁–U₃** on `a.arch` force **`PositiveResidualProfile a`** with the current
**trivial** **R₄** witness — **intuitionistic**, no classical case split.
-/
theorem positive_residual_profile_of_triple_barriers_at_anchor
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface a.arch)
    (d2 : ClosureObstructionInterface a.arch)
    (d3 : SemanticCertificationInterface a.arch) :
    PositiveResidualProfile a :=
  positive_residual_profile_of_three_failures
    (not_representationalProfile_of_diagonalBarrier a d1)
    (not_closureProfile_of_closureBarrier a d2)
    (not_certificatoryProfile_of_semanticBarrier a d3)

end StructuredNonexhaustibility
