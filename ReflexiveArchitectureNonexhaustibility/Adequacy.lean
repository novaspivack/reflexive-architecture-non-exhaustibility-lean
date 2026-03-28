import ReflexiveArchitectureNonexhaustibility.Residuals
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.AnchoredFlagship

/-!
# Adequacy / admissibility (**SPEC_012_AA1**, **EPIC_008**)

**Cross-walk (baseline → anchored flagship):**

| Artifact | Role |
|----------|------|
| **`OpaqueAttemptWithClaim`** | Naked **`internalCompletionClaim`** is **logically idle** for M₁–M₃ until tied to profiles (**`claim_independent_of_profiles`** in **`GenuinenessCandidates.lean`**). |
| **`IsBurdenFaithfulClaim`** | **Admissible discipline** for “internal completion”: a **true** claim must **bear** at least one of M₁–M₃ at **`anchor`**. |
| **`HonestAnchoredInternalCompletion`** | Flagship package = claim + **witnessed** burden-faithfulness (**`AnchoredFlagship.lean`**). |
| **`AdmissibleResidual`** | Residual-calculus hook (**`Residuals.lean`**); still the **trivial** predicate until **SPEC_012** refines it. |

**Anti-smuggling:** burden-faithfulness is **not** the four-way disjunction, **not** **`Genuine` alone**, and **not** a tag
that renames **`PositiveResidualProfile`**.

**Placeholder defs** below keep older spec phrases locatable; replace with real world–certificate semantics when **§2** of
**SPEC_012_AA1** lands.
-/

namespace StructuredNonexhaustibility

variable {World Obs Repr Claim : Type}

/-- Certificate–world consistency placeholder (**SPEC_012_AA1** §certificate). -/
def CertificateWorldConsistent : Prop := True

/-- Legacy reader anchor; the **Layer 1** interface is **`HonestAnchoredInternalCompletion`**. -/
def GenuineInternalCompletion : Prop := True

theorem admissible_trivial_residual (w : ResidualWitness) : AdmissibleResidual w := trivial

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
**Flagship corollary:** **`HonestAnchoredInternalCompletion`** is exactly the packaged witness of that discipline.
-/
theorem honestAnchored_claim_implies_not_threeWayFailures
    (h : HonestAnchoredInternalCompletion World Obs Repr Claim) (hcl : h.base.internalCompletionClaim) :
    ¬ ThreeWayAnchorFailures h.base.attempt :=
  burdenFaithful_claim_implies_not_threeWayFailures _ h.burdenFaithfulness hcl

end StructuredNonexhaustibility
