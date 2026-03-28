import Mathlib.Data.Set.Defs
import ReflexiveArchitectureNonexhaustibility.Modes
import ReflexiveArchitectureNonexhaustibility.Residuals
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Attempt

/-!
# Structural mode profiles (**SPEC_015_KM2**, **Profiles**)

Profiles are **predicates** on `OpaqueTotalizationAttempt`. Overlap is allowed at this layer; a
later **classification** theorem may impose disjointness / priority rules.

**Paper D bridge (**`Modes.lean`**): anchored profiles imply matching **`Mode*i*Success`** on `arch` (nominations at **`anchor`**); see **`PaperDAnchoredChain.lean`**.
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
**Mode-calculus bridge (**`Modes.lean`**): anchored representational profile is a **witness** of **M₁ success**
for the underlying architecture (nomination at `anchor`).
-/
theorem representationalProfile_implies_mode1Success
    (a : OpaqueTotalizationAttempt World Obs Repr Claim) (h : RepresentationalProfile a) :
    Mode1Success a.arch :=
  ⟨a.reprAt a.anchor, h⟩

theorem closureProfile_implies_mode2Success
    (a : OpaqueTotalizationAttempt World Obs Repr Claim) (h : ClosureProfile a) :
    Mode2Success a.arch :=
  ⟨a.closureAt a.anchor, h⟩

theorem certificatoryProfile_implies_mode3Success
    (a : OpaqueTotalizationAttempt World Obs Repr Claim) (h : CertificatoryProfile a) :
    Mode3Success a.arch :=
  ⟨a.certAt a.anchor, h⟩

/-- **M₁ success at** `p` (not necessarily `anchor`). -/
def RepresentationalProfileAt (a : OpaqueTotalizationAttempt World Obs Repr Claim) (p : a.carrier) :
    Prop :=
  a.arch.repr_success (a.reprAt p)

/-- **M₂ success at** `p`. -/
def ClosureProfileAt (a : OpaqueTotalizationAttempt World Obs Repr Claim) (p : a.carrier) : Prop :=
  a.arch.closure_success (a.closureAt p)

/-- **M₃ success at** `p`. -/
def CertificatoryProfileAt (a : OpaqueTotalizationAttempt World Obs Repr Claim) (p : a.carrier) :
    Prop :=
  a.arch.cert_success (a.certAt p)

@[simp]
theorem representationalProfileAt_anchor (a : OpaqueTotalizationAttempt World Obs Repr Claim) :
    RepresentationalProfileAt a a.anchor = RepresentationalProfile a := rfl

@[simp]
theorem closureProfileAt_anchor (a : OpaqueTotalizationAttempt World Obs Repr Claim) :
    ClosureProfileAt a a.anchor = ClosureProfile a := rfl

@[simp]
theorem certificatoryProfileAt_anchor (a : OpaqueTotalizationAttempt World Obs Repr Claim) :
    CertificatoryProfileAt a a.anchor = CertificatoryProfile a := rfl

/--
**R₄ (positive residual) profile:** an **R₄-class** admissible witness, and **none** of the three
canonical mode-success predicates hold at `anchor`.

This **does not** let every attempt invent `⟨R4, carrier, anchor⟩` to cheat the cover: linkage to the
attempt’s anchor alone was vacuous. The substantive condition is **failure of M₁–M₃** at the nominated
gadgets (**SPEC_004_RC1** / BACKGROUND: survivor when representational, closure, and certificatory
**success** all fail).

**Refinement:** **`positive_residual_profile_of_three_failures`** still uses **`trivialR4ResidualWitness`**; barrier-linked packaging lives in **`barrierLinkedR4ResidualWitness`** (**`D002ResidualWitnessTarget.lean`**).
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
