import Mathlib.Data.Set.Defs
import ReflexiveArchitectureNonexhaustibility.Residuals
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Attempt

/-!
# Structural mode profiles (**SPEC_015_KM2**, **Profiles**)

Profiles are **predicates** on `OpaqueTotalizationAttempt`. Overlap is allowed at this layer; a
later **classification** theorem may impose disjointness / priority rules.
-/

namespace StructuredNonexhaustibility

variable {World Obs Repr Claim : Type}

def RepresentationalProfile (a : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  a.arch.repr_success (a.reprAt a.anchor)

def ClosureProfile (a : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  a.arch.closure_success (a.closureAt a.anchor)

def CertificatoryProfile (a : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  a.arch.cert_success (a.certAt a.anchor)

/--
**R₄ (positive residual) profile:** an **R₄-class** admissible witness, and **none** of the three
canonical mode-success predicates hold at `anchor`.

This **does not** let every attempt invent `⟨R4, carrier, anchor⟩` to cheat the cover: linkage to the
attempt’s anchor alone was vacuous. The substantive condition is **failure of M₁–M₃** at the nominated
gadgets (**SPEC_004_RC1** / BACKGROUND: survivor when representational, closure, and certificatory
**success** all fail).

**Refinement:** witness payloads / barrier-produced witnesses (**D-002**).
-/
def PositiveResidualProfile (a : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  ∃ w : ResidualWitness,
    IsR4PositiveSurvivor w ∧ AdmissibleResidual w ∧
      ¬ RepresentationalProfile a ∧ ¬ ClosureProfile a ∧ ¬ CertificatoryProfile a

theorem positive_residual_profile_of_three_failures
    {a : OpaqueTotalizationAttempt World Obs Repr Claim}
    (hR : ¬ RepresentationalProfile a) (hC : ¬ ClosureProfile a) (hK : ¬ CertificatoryProfile a) :
    PositiveResidualProfile a :=
  ⟨trivialR4ResidualWitness, isR4_trivialR4, trivial, hR, hC, hK⟩

theorem not_representational_of_positive_residual
    {a : OpaqueTotalizationAttempt World Obs Repr Claim} (hp : PositiveResidualProfile a) :
    ¬ RepresentationalProfile a := by
  rcases hp with ⟨_, _, _, hn, _, _⟩
  exact hn

end StructuredNonexhaustibility
