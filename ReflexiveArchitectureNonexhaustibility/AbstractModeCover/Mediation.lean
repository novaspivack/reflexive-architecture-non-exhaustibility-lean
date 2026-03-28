import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Attempt
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Profiles

/-!
# Success mediation (**SPEC_015_KM2**, **Mediation**)

Operational readings of “success is **mediated** representationally, by closure, or by
certification” coincide with the profile predicates at `anchor` **given** the current architecture
success predicates (**SPEC_002_AM1**).

**Summit targets** below are **`Prop`-valued names** for the obligations—**not** theorems until
proved without `sorry` or new `axiom`s.

## What is already proved

- **Forward (intuitionistic):** `mediation_decomposition_of_four_profiles` — four-way **profile**
  disjunction implies the **mediation-shaped** packaging.
- **vs `AbstractOpaqueModeCoverTarget`:** coverage-implication lemmas are in **Classification.lean**
  (same file as the cover `def`, to avoid import cycles).
- **Reverse** (cover from mediation): **classical** case split — see **Classification.lean**.

This does **not** discharge the summit: it links the two target `Prop`s once **profiles** are
available. Deriving those profiles from **`GenuineInternalTotalizationAttempt` alone** remains open
(**Outcome B** notes in **MANIFEST** / **SPEC_015_KM2**). Implications between summit `Prop`s live
in **Classification.lean** (imports both `Mediation` and `AbstractOpaqueModeCoverTarget`).
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

/--
Four-way profile OR **packages** intuitionistically into the mediation disjunction
(`PositiveResidual ∨ (¬ Positive → repr ∨ closure ∨ cert)`).
-/
theorem mediation_decomposition_of_four_profiles
    {a : OpaqueTotalizationAttempt World Obs Repr Claim} :
    (RepresentationalProfile a ∨ ClosureProfile a ∨ CertificatoryProfile a ∨
        PositiveResidualProfile a) →
    (PositiveResidualProfile a ∨
      (¬ PositiveResidualProfile a →
        (SuccessRepresentationallyMediated a ∨ SuccessViaClosureMediation a ∨
          SuccessViaCertMediation a))) := by
  intro h
  rcases h with hR | hC | hK | hP
  · right
    intro _
    left
    exact hR
  · right
    intro _
    right; left
    exact hC
  · right
    intro _
    right; right
    exact hK
  · left
    exact hP

end StructuredNonexhaustibility
