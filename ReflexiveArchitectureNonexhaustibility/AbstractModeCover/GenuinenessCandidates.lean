import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Attempt
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Profiles
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Classification

/-!
# Genuineness enrichment candidates (**SPEC_015_KM2**, **minimal-strengthening search**)

**Specification discipline:** test a **small** ordered family of strengthenings; avoid ad hoc proliferation. **Paper D
flagship** packaging: **`HonestAnchoredInternalCompletion`** / **`AnchoredFlagshipUniversalCover`** in
**`AnchoredFlagship.lean`**.

## Status in this file (summary)

- **Candidate A** — `OpaqueAttemptWithClaim`: explicit `internalCompletionClaim : Prop`. **Insufficiency:**
  `claim_independent_of_profiles`.
- **Candidate B** — **operational burden-faithfulness** (`IsBurdenFaithfulClaim`): `claim → M₁ ∨ M₂ ∨ M₃` at
  anchor. **Intuitionistic** four-way cover from a **true** claim (`abstract_four_way_of_burdenFaithful_claim`).
  **Sharp obstruction:** `burdenFaithful_claim_incompatible_with_threeFailures` (faithful claim + true claim + all
  three failures = absurd). **Insufficiency of a naked soundness layer:** `trivial_soundness_does_not_force_profiles`
  — `OpaqueAttemptWithSoundness` with `soundness := fun _ => True` does **not** tie claim to architecture.
- **Candidate C** — **`OpaqueAttemptWithProfileDeterminacy`:** per-attempt `Decidable` on the three profiles at
  anchor → **intuitionistic** four-way cover via `abstract_opaque_mode_cover_of_decidable`.

## Relation to the classical blanket theorem

`abstract_opaque_mode_cover_classical` in **Classification.lean** discharges `AbstractOpaqueModeCoverTarget`
using **LEM** on the three profile propositions. The enrichments here are the **constructive / burden-bearing**
routes: they classify **without** that classical case split, at the cost of **extra** (honest) structure.

## Anti-smuggling

- **Burden-faithfulness** is **not** defined as the full four-way disjunction: it mentions **only** M₁–M₃ at
  anchor. Residual enters the four-way conclusion as an **unused** disjunct in the faithful-claim branch, or via
  determinacy / failures in other branches.
- **`OpaqueAttemptWithSoundness`** keeps a **type-family** slot `claim → Prop` for future **SPEC_012**-grade
  refinements; the insufficiency theorem shows the slot alone is logically idle without axioms on `soundness`.
-/

namespace StructuredNonexhaustibility

variable {World Obs Repr Claim : Type}

/-- **Candidate A:** opaque attempt + naked propositional “completion” claim. -/
structure OpaqueAttemptWithClaim (World Obs Repr Claim : Type) where
  attempt : OpaqueTotalizationAttempt World Obs Repr Claim
  internalCompletionClaim : Prop

/--
**Candidate A — insufficiency:** the claim carries **no logical force** for the profile predicates
until additional structure relates `internalCompletionClaim` to `arch.*_success`.
-/
theorem claim_independent_of_profiles
    (op : OpaqueTotalizationAttempt World Obs Repr Claim) (p q : Prop) :
    ∃ c₁ c₂ : OpaqueAttemptWithClaim World Obs Repr Claim,
      c₁.attempt = op ∧ c₂.attempt = op ∧
        c₁.internalCompletionClaim = p ∧ c₂.internalCompletionClaim = q := by
  refine ⟨⟨op, p⟩, ⟨op, q⟩, rfl, rfl, rfl, rfl⟩

/--
**Candidate B (core discipline):** whenever the completion claim is asserted, at least one **canonical**
mode succeeds at `anchor` on the nominated gadgets (M₁–M₃ only — **no** residual in the antecedent).

This is **operational soundness** in the sense: a true “internal completion” claim **bears the architectural
burden** of witnessing success along one classical mediation shape.
-/
def IsBurdenFaithfulClaim (wc : OpaqueAttemptWithClaim World Obs Repr Claim) : Prop :=
  wc.internalCompletionClaim →
    RepresentationalProfile wc.attempt ∨
      ClosureProfile wc.attempt ∨
        CertificatoryProfile wc.attempt

/--
**Candidate B — summand (packed):** claim data + a witness that the claim is burden-faithful.
-/
structure OpaqueAttemptWithBurdenFaithfulClaim (World Obs Repr Claim : Type) where
  base : OpaqueAttemptWithClaim World Obs Repr Claim
  burdenFaithfulness : IsBurdenFaithfulClaim base

/--
**Minimal mediation from burden-faithful totalization** (**intuitionistic**): a **true** burden-faithful
completion claim yields the abstract four-way disjunction immediately — in fact **always** through one of the
first three disjuncts (the residual branch is not needed).

This is the honest “success claim + soundness discipline” summit **at the M₁–M₃ boundary**: it cannot subsume
**positive residual with a simultaneously true burden-faithful completion claim** (see the incompatibility
lemma below).
-/
theorem abstract_four_way_of_burdenFaithful_claim
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim)
    (hf : IsBurdenFaithfulClaim wc) (hcl : wc.internalCompletionClaim) :
    RepresentationalProfile wc.attempt ∨
      ClosureProfile wc.attempt ∨
        CertificatoryProfile wc.attempt ∨
          PositiveResidualProfile wc.attempt := by
  rcases hf hcl with hR | hC | hK
  · exact Or.inl hR
  · exact Or.inr (Or.inl hC)
  · exact Or.inr (Or.inr (Or.inl hK))

theorem abstract_four_way_of_burdenFaithful
    (p : OpaqueAttemptWithBurdenFaithfulClaim World Obs Repr Claim) (hcl : p.base.internalCompletionClaim) :
    RepresentationalProfile p.base.attempt ∨
      ClosureProfile p.base.attempt ∨
        CertificatoryProfile p.base.attempt ∨
          PositiveResidualProfile p.base.attempt :=
  abstract_four_way_of_burdenFaithful_claim _ p.burdenFaithfulness hcl

/--
**Sharp obstruction:** a **true** burden-faithful claim is **incompatible** with **simultaneous** failure of
all three canonical profiles. Equivalently: **positive residual** (`Profiles.lean`: ¬M₁ ∧ ¬M₂ ∧ ¬M₃ with R₄
witness) cannot sit under a **burden-faithful completion claim** that is actually asserted.

**Philosophical reading:** if “internal completion” is asserted in the **burden-bearing** sense, the attempt is
not — by definition — in the **honest** M₁–M₃-failure / R₄-positive configuration.
-/
theorem burdenFaithful_claim_incompatible_with_threeFailures
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim)
    (hf : IsBurdenFaithfulClaim wc) (hcl : wc.internalCompletionClaim)
    (hR : ¬ RepresentationalProfile wc.attempt)
    (hC : ¬ ClosureProfile wc.attempt)
    (hK : ¬ CertificatoryProfile wc.attempt) :
    False := by
  rcases hf hcl with hR' | hC' | hK'
  · exact hR hR'
  · exact hC hC'
  · exact hK hK'

/--
**Candidate B (generic interface):** claim + **unspecified** soundness layer `claim → Prop`.

**Anti-smuggling note:** `soundness` is **not** constrained; substantive content must be conveyed by **axioms**
on `soundness` or by **specializing** to `IsBurdenFaithfulClaim` (or stronger **SPEC_012** predicates).
-/
structure OpaqueAttemptWithSoundness (World Obs Repr Claim : Type) where
  withClaim : OpaqueAttemptWithClaim World Obs Repr Claim
  /-- Refine under **SPEC_012_AA1** / Paper C semantics; compare `IsBurdenFaithfulClaim`. -/
  soundness : withClaim.internalCompletionClaim → Prop

/--
**Insufficiency:** arbitrary `soundness` can be **pointwise** `True`, with **true** `internalCompletionClaim`,
yet all three canonical profiles fail — so the **slot** `soundness` adds **no** link to `arch.*_success` until
further discipline is imposed.
-/
theorem trivial_soundness_does_not_force_profiles
    (op : OpaqueTotalizationAttempt World Obs Repr Claim)
    (hR : ¬ RepresentationalProfile op)
    (hC : ¬ ClosureProfile op)
    (hK : ¬ CertificatoryProfile op) :
    ∃ s : OpaqueAttemptWithSoundness World Obs Repr Claim,
      s.withClaim.attempt = op ∧
        s.withClaim.internalCompletionClaim ∧
          (∀ h : s.withClaim.internalCompletionClaim, s.soundness h) ∧
            ¬ RepresentationalProfile s.withClaim.attempt ∧
              ¬ ClosureProfile s.withClaim.attempt ∧ ¬ CertificatoryProfile s.withClaim.attempt := by
  refine ⟨{ withClaim := ⟨op, True⟩, soundness := fun _ => True }, ?_, ?_, ?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · rfl
  · trivial
  · intro _
    trivial
  · simpa using hR
  · simpa using hC
  · simpa using hK

/--
**Candidate C:** profile **determinacy** at the anchor — `Decidable` witnesses for M₁–M₃.

This is **internal inspectability** data: enough structure to run the perimeter case-split **intuitionistically**
on the three profiles; the residual branch is forced **positively** when all three fail.
-/
structure OpaqueAttemptWithProfileDeterminacy (World Obs Repr Claim : Type) where
  attempt : OpaqueTotalizationAttempt World Obs Repr Claim
  decR : Decidable (RepresentationalProfile attempt)
  decC : Decidable (ClosureProfile attempt)
  decK : Decidable (CertificatoryProfile attempt)

/--
**Candidate C — classification:** determinacy alone yields the four-way cover **without** `classical`.
-/
theorem abstract_four_way_of_profileDeterminacy
    (d : OpaqueAttemptWithProfileDeterminacy World Obs Repr Claim) :
    RepresentationalProfile d.attempt ∨
      ClosureProfile d.attempt ∨
        CertificatoryProfile d.attempt ∨
          PositiveResidualProfile d.attempt :=
  abstract_opaque_mode_cover_of_decidable World Obs Repr Claim d.attempt d.decR d.decC d.decK

end StructuredNonexhaustibility
