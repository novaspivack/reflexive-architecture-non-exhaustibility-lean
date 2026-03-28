import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.AnchoredFlagship
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.D002ResidualWitnessTarget
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.PostFailureResidual
import ReflexiveArchitectureNonexhaustibility.Interfaces
import ReflexiveArchitectureNonexhaustibility.ResidualDynamics
import ReflexiveArchitectureNonexhaustibility.Residuals

/-!
# Adequacy / admissibility (**SPEC_012_AA1**, **EPIC_008**)

**Dynamics (**SPEC_023_RG1** / **EPIC_015**): **`d3_adequacy_aftermath_standing_burden`** repackages
**`honest_aftermath_carries_admissible_r4`** as **`StandingResidualBurden`** — same mathematical content, dynamics
vocabulary for “burden does not vanish under triple barriers; it is organized into admissible **R₄**.”
**`U123BarrierData`** / **`RegimeSnapshot`** entry points: **`d3_adequacy_aftermath_standing_burden_of_u123BarrierData`**,
**`…_of_nonempty_u123_arch`**, **`…_of_regime_arch_eq_u123`** (**`u123BarrierData_cast`**); matching **R₄ core**
**`d3_aftermath_standing_r4_admissible_core_of_*`** (**weakens** to **`∃ w, IsR4 ∧ Admissible`** only).

**Cross-walk (baseline → anchored flagship):**

| Artifact | Role |
|----------|------|
| **`OpaqueAttemptWithClaim`** | Naked **`internalCompletionClaim`** is **logically idle** for M₁–M₃ until tied to profiles (**`claim_independent_of_profiles`** in **`GenuinenessCandidates.lean`**). |
| **`IsBurdenFaithfulClaim`** | **Admissible discipline** for “internal completion”: a **true** claim must **bear** at least one of M₁–M₃ at **`anchor`**. |
| **`HonestAnchoredInternalCompletion`** | Flagship package = claim + **witnessed** burden-faithfulness (**`AnchoredFlagship.lean`**). |
| **`AdmissibleResidual`** | **Non-vacuous** in **`Residuals.lean`**: **R₄** requires **`U123BarrierData`-shaped** carrier; **`PositiveResidualProfile`** stays **schematic** (**`Profiles.lean`**). |
| **`CertificateWorldConsistent`** | **World–certificate alignment:** burden-faithful asserted claims forbid joint three-way anchored failure (**definition** + **`certificateWorldConsistent_holds`**). |

**Anti-smuggling:** burden-faithfulness is **not** the four-way disjunction, **not** **`Genuine` alone**, and **not** a tag
that renames **`PositiveResidualProfile`**.

**Legacy:** **`GenuineInternalCompletion`** keeps a readable name for older spec phrasing (**Layer 1** target is
**`HonestAnchoredInternalCompletion`**).
-/

namespace StructuredNonexhaustibility

variable {World Obs Repr Claim : Type}

/--
**Joint three-way anchored failure:** all three canonical profile predicates are false at **`anchor`**.

This is the **success-geometry** configuration that **positive residual** targets (**`Profiles.lean`**) when the claim does
**not** bear M₁–M₃.
-/
abbrev ThreeWayAnchorFailures (attempt : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  ¬ RepresentationalProfile attempt ∧ ¬ ClosureProfile attempt ∧ ¬ CertificatoryProfile attempt

/--
**Adequacy lemma (operational):** **`IsBurdenFaithfulClaim`** forbids asserting internal completion while **all three**
canonical modes fail at **`anchor`**.
-/
theorem burdenFaithful_claim_implies_not_threeWayFailures
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim) (hf : IsBurdenFaithfulClaim wc) (hcl : wc.internalCompletionClaim) :
    ¬ ThreeWayAnchorFailures wc.attempt := by
  intro ⟨hR, hC, hK⟩
  exact burdenFaithful_claim_incompatible_with_threeFailures wc hf hcl hR hC hK

/--
**Certificate / world consistency (**SPEC_012_AA1**): asserts the same discipline as
**`burdenFaithful_claim_implies_not_threeWayFailures`** — packaged globally per universe of attempts.
-/
def CertificateWorldConsistent (W O R C : Type) : Prop :=
  ∀ (wc : OpaqueAttemptWithClaim W O R C),
    IsBurdenFaithfulClaim wc → wc.internalCompletionClaim → ¬ ThreeWayAnchorFailures wc.attempt

theorem certificateWorldConsistent_holds (W O R C : Type) : CertificateWorldConsistent W O R C := by
  intro wc hf hcl
  exact burdenFaithful_claim_implies_not_threeWayFailures wc hf hcl

/-- Legacy reader anchor; the **Layer 1** interface is **`HonestAnchoredInternalCompletion`**. -/
def GenuineInternalCompletion : Prop := True

/--
**Flagship corollary:** **`HonestAnchoredInternalCompletion`** is exactly the packaged witness of that discipline.
-/
theorem honestAnchored_claim_implies_not_threeWayFailures
    (h : HonestAnchoredInternalCompletion World Obs Repr Claim) (hcl : h.base.internalCompletionClaim) :
    ¬ ThreeWayAnchorFailures h.base.attempt :=
  burdenFaithful_claim_implies_not_threeWayFailures _ h.burdenFaithfulness hcl

/--
**Aftermath / admissibility link:** under **U₁–U₃**, the **forced** **`barrierLinkedR4ResidualWitness`** is **both**
**R₄** and **`AdmissibleResidual`** while the three anchored mode profiles fail — the honest **Layer 1** companion to
schematic **`PositiveResidualProfile`**.
-/
theorem honest_aftermath_carries_admissible_r4
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface a.arch)
    (d2 : ClosureObstructionInterface a.arch)
    (d3 : SemanticCertificationInterface a.arch) :
    ∃ w : ResidualWitness,
      IsR4PositiveSurvivor w ∧ AdmissibleResidual w ∧
        ¬ RepresentationalProfile a ∧ ¬ ClosureProfile a ∧ ¬ CertificatoryProfile a :=
  ⟨barrierLinkedR4ResidualWitness d1 d2 d3, isR4_barrierLinkedR4ResidualWitness d1 d2 d3,
    admissible_barrierLinkedR4ResidualWitness d1 d2 d3,
    not_representationalProfile_of_diagonalBarrier a d1,
    not_closureProfile_of_closureBarrier a d2,
    not_certificatoryProfile_of_semanticBarrier a d3⟩

/--
**D3 seed (**SPEC_023_RG1**):** triple-barrier honest aftermath is literally a **`StandingResidualBurden`** — the same
conjunction as **`honest_aftermath_carries_admissible_r4`**, phrased in the dynamical-layer alias.

**Not** claiming full “burden relocation along morphisms” yet: that needs explicit **response** / transport operators
along **`PayloadPromotionBridge`** (**`FromRFO`**, **`FromRI`**, …).
-/
theorem d3_adequacy_aftermath_standing_burden
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface a.arch)
    (d2 : ClosureObstructionInterface a.arch)
    (d3 : SemanticCertificationInterface a.arch) :
    StandingResidualBurden
      (∃ w : ResidualWitness,
        IsR4PositiveSurvivor w ∧ AdmissibleResidual w ∧
          ¬ RepresentationalProfile a ∧ ¬ ClosureProfile a ∧ ¬ CertificatoryProfile a) :=
  honest_aftermath_carries_admissible_r4 a d1 d2 d3

/--
**D3 transport (example):** the same triple-barrier aftermath **specializes** to **`StandingResidualBurden`** of “there is
admissible **R₄** witness data” **without** erasing the stronger full package—**propositional weakening** via
**`standingResidualBurden_of_imp`**.
-/
theorem d3_aftermath_standing_r4_admissible_core
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface a.arch)
    (d2 : ClosureObstructionInterface a.arch)
    (d3 : SemanticCertificationInterface a.arch) :
    StandingResidualBurden
      (∃ w : ResidualWitness, IsR4PositiveSurvivor w ∧ AdmissibleResidual w) :=
  standingResidualBurden_of_imp
    (by
      rintro ⟨w, hwR, hwA, _, _, _⟩
      exact ⟨w, hwR, hwA⟩)
    (d3_adequacy_aftermath_standing_burden a d1 d2 d3)

/--
**D3** aftermath from a **typed** **`U123BarrierData a.arch`** pack (**SPEC_003_BT1** / **D-002**) — definitionally the same
input family as **`d3_adequacy_aftermath_standing_burden`**, repackaged for **`U123BarrierData`** consumers.
-/
theorem d3_adequacy_aftermath_standing_burden_of_u123BarrierData
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (b : U123BarrierData a.arch) :
    StandingResidualBurden
      (∃ w : ResidualWitness,
        IsR4PositiveSurvivor w ∧ AdmissibleResidual w ∧
          ¬ RepresentationalProfile a ∧ ¬ ClosureProfile a ∧ ¬ CertificatoryProfile a) :=
  d3_adequacy_aftermath_standing_burden a b.reprBarrier b.closureBarrier b.certBarrier

/--
**D3** aftermath from **`Nonempty (U123BarrierData a.arch)`** (e.g. dynamics-layer **`…_u123RegimeHypotheses`** on **`RegimeSnapshot.arch`**
once aligned with **`a.arch`**).
-/
theorem d3_adequacy_aftermath_standing_burden_of_nonempty_u123_arch
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (hb : Nonempty (U123BarrierData a.arch)) :
    StandingResidualBurden
      (∃ w : ResidualWitness,
        IsR4PositiveSurvivor w ∧ AdmissibleResidual w ∧
          ¬ RepresentationalProfile a ∧ ¬ ClosureProfile a ∧ ¬ CertificatoryProfile a) :=
  Nonempty.elim hb (d3_adequacy_aftermath_standing_burden_of_u123BarrierData a)

/--
**Regime snapshot** **`s.arch`** carries **`U123BarrierData`** and matches **`a.arch`** ⇒ **D3** on **`a`**
(**`u123BarrierData_cast`** along **`a.arch = s.arch`**).
-/
theorem d3_adequacy_aftermath_standing_burden_of_regime_arch_eq_u123
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (s : RegimeSnapshot World Obs Repr Claim)
    (harch : a.arch = s.arch)
    (b : U123BarrierData s.arch) :
    StandingResidualBurden
      (∃ w : ResidualWitness,
        IsR4PositiveSurvivor w ∧ AdmissibleResidual w ∧
          ¬ RepresentationalProfile a ∧ ¬ ClosureProfile a ∧ ¬ CertificatoryProfile a) :=
  d3_adequacy_aftermath_standing_burden_of_u123BarrierData a (u123BarrierData_cast harch.symm b)

/--
**Nonempty** **`U123BarrierData s.arch`** + **`a.arch = s.arch`** ⇒ **D3** on **`a`**.
-/
theorem d3_adequacy_aftermath_standing_burden_of_regime_arch_eq_nonempty_u123
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (s : RegimeSnapshot World Obs Repr Claim)
    (harch : a.arch = s.arch)
    (hb : Nonempty (U123BarrierData s.arch)) :
    StandingResidualBurden
      (∃ w : ResidualWitness,
        IsR4PositiveSurvivor w ∧ AdmissibleResidual w ∧
          ¬ RepresentationalProfile a ∧ ¬ ClosureProfile a ∧ ¬ CertificatoryProfile a) :=
  Nonempty.elim hb (d3_adequacy_aftermath_standing_burden_of_regime_arch_eq_u123 a s harch)

/--
**R₄ admissible core** (**`d3_aftermath_standing_r4_admissible_core`**) from **`U123BarrierData a.arch`**.

Same weakening as the **`d1–d3`** entry path; packaged for **D-002** **`U123BarrierData`** consumers.
-/
theorem d3_aftermath_standing_r4_admissible_core_of_u123BarrierData
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (b : U123BarrierData a.arch) :
    StandingResidualBurden
      (∃ w : ResidualWitness, IsR4PositiveSurvivor w ∧ AdmissibleResidual w) :=
  d3_aftermath_standing_r4_admissible_core a b.reprBarrier b.closureBarrier b.certBarrier

theorem d3_aftermath_standing_r4_admissible_core_of_nonempty_u123_arch
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (hb : Nonempty (U123BarrierData a.arch)) :
    StandingResidualBurden
      (∃ w : ResidualWitness, IsR4PositiveSurvivor w ∧ AdmissibleResidual w) :=
  Nonempty.elim hb (d3_aftermath_standing_r4_admissible_core_of_u123BarrierData a)

theorem d3_aftermath_standing_r4_admissible_core_of_regime_arch_eq_u123
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (s : RegimeSnapshot World Obs Repr Claim)
    (harch : a.arch = s.arch)
    (b : U123BarrierData s.arch) :
    StandingResidualBurden
      (∃ w : ResidualWitness, IsR4PositiveSurvivor w ∧ AdmissibleResidual w) :=
  d3_aftermath_standing_r4_admissible_core_of_u123BarrierData a (u123BarrierData_cast harch.symm b)

theorem d3_aftermath_standing_r4_admissible_core_of_regime_arch_eq_nonempty_u123
    (a : OpaqueTotalizationAttempt World Obs Repr Claim)
    (s : RegimeSnapshot World Obs Repr Claim)
    (harch : a.arch = s.arch)
    (hb : Nonempty (U123BarrierData s.arch)) :
    StandingResidualBurden
      (∃ w : ResidualWitness, IsR4PositiveSurvivor w ∧ AdmissibleResidual w) :=
  Nonempty.elim hb (d3_aftermath_standing_r4_admissible_core_of_regime_arch_eq_u123 a s harch)

end StructuredNonexhaustibility
