import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Attempt
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Profiles

/-!
# Success mediation (**SPEC_015_KM2**, **Mediation**)

Operational readings of “success is **mediated** representationally, by closure, or by
certification” coincide with the profile predicates at `anchor` **given** the current architecture
success predicates (**SPEC_002_AM1**).

**Summit targets** below are **`Prop`-valued names** for the obligations—**not** theorems until
proved without `sorry` or new `axiom`s.
-/

namespace StructuredNonexhaustibility

variable {World Obs Repr Claim : Type}

abbrev SuccessRepresentationallyMediated (a : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  RepresentationalProfile a

abbrev SuccessViaClosureMediation (a : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  ClosureProfile a

abbrev SuccessViaCertMediation (a : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  CertificatoryProfile a

/--
**Target:** mediation decomposition — residual-positive **or** one of the three internal
mediation routes. Proof deferred; see **SPEC_015_KM2** §immediate target.
-/
def AbstractMediationDecompositionTarget (World Obs Repr Claim : Type) : Prop :=
  ∀ (a : OpaqueTotalizationAttempt World Obs Repr Claim),
    GenuineInternalTotalizationAttempt a →
    (PositiveResidualProfile a ∨
      (¬ PositiveResidualProfile a →
        (SuccessRepresentationallyMediated a ∨
          SuccessViaClosureMediation a ∨
            SuccessViaCertMediation a)))

/--
**Target:** alternative packaging — every genuine attempt falls under a profile disjunct.
Equivalent to `AbstractOpaqueModeCoverTarget` in **Classification** once profiles are aligned.
-/
def AbstractFourWayMediationStatement (World Obs Repr Claim : Type) : Prop :=
  ∀ (a : OpaqueTotalizationAttempt World Obs Repr Claim),
    GenuineInternalTotalizationAttempt a →
    (RepresentationalProfile a ∨
      ClosureProfile a ∨
        CertificatoryProfile a ∨
          PositiveResidualProfile a)

end StructuredNonexhaustibility
