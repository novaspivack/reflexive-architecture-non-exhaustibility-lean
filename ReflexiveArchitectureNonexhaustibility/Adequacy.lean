import ReflexiveArchitectureNonexhaustibility.Residuals
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.AnchoredFlagship
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.PostFailureResidual
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.D002ResidualWitnessTarget

/-!
# Adequacy / admissibility (**SPEC_012_AA1**, **EPIC_008**)

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

end StructuredNonexhaustibility
