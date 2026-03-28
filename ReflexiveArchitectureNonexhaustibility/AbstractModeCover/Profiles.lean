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
Positive residual profile: **R₄** survivor attested by a witness.

**Refinement:** strengthen linkage between `ResidualWitness` and `a.carrier` when **R₄** sharpens
(**TODO-075_RN7**).
-/
def PositiveResidualProfile (a : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  ∃ w : ResidualWitness,
    IsR4PositiveSurvivor w ∧ AdmissibleResidual w ∧
      ∃ h : w.carrier = a.carrier, cast h w.witness = a.anchor

end StructuredNonexhaustibility
