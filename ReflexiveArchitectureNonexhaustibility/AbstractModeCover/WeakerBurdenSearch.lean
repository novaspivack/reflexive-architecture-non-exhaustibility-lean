import Mathlib.Data.Set.Defs
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Attempt
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Profiles
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.GenuinenessCandidates

/-!
# Principled weaker-burden search (**SPEC_015_KM2**)

**Goal:** systematize obligations **strictly weaker** than anchor **burden-faithfulness**
(`IsBurdenFaithfulClaim` in **GenuinenessCandidates.lean**) and record what **does** and **does not**
imply anchored “completion-mode” success.

**Scope discipline:** a finite menu of definition families + implication/counterexample lemmas — not an
open-ended candidate zoo.

## Taxonomy (informal)

- **Somewhere-faithfulness** — M₁\(\lor\)M₂\(\lor\)M₃ holds at **some** `p : carrier`, not necessarily `anchor`.
  **Strictly weaker** than anchor burden-faithfulness (**Lemma** `exists_somewhereFaithful_trueClaim_without_anchor_threeWay`).
  **Does not** imply **joint-failure ruled out** (**Lemma** `somewhereFaithful_does_not_imply_jointFailureRuledOut_toy`).
- **Joint-failure ruled out** — `claim → ¬(¬M₁ ∧ ¬M₂ ∧ ¬M₃)` at `anchor`. Implied by burden-faithfulness
  (intuitionistic). **Classically** equivalent to burden-faithfulness (**Lemma**
  `jointFailureRuledOut_iff_burdenFaithful_claim_classical`).
- **Double-negation shift** — `claim → ¬¬(M₁ ∨ M₂ ∨ M₃)`. Implied by burden-faithfulness; still **no**
  anchored disjunction without further principles.
- **Omit-one bundles** at `anchor` — each **implies** burden-faithfulness; **burden-faithfulness does not**
  imply any omit-one bundle (**single-mode witnesses**).

**Conclusion:** among **uniform non-smuggling strengthenings** in this file, **somewhere-faithfulness** is the
main **constructive weakening** that **relocates** architectural success off `anchor`. **Propositional**
weakenings between `¬(¬M₁∧…)` and `M₁∨…∨M₃` stay **intuitionistically** subtle; **classically** they collapse
to anchor burden-faithfulness.

**Frozen distinction (2026-03-27):** **anchored completion** (profiles at **`anchor`**) and **relocated /
off-anchor success** (`ProfileAt p` for some `p`) are **non-equivalent** theorem subjects. See section
**AnchorNecessityBoundary** and **SPEC_015_KM2** / **MANIFEST** “two theorem layers.”
-/

namespace StructuredNonexhaustibility

variable {World Obs Repr Claim : Type}

/-- Anchored M₁–M₃ disjunction (completion-mode side; **excludes** packaged R₄). -/
def ThreeWayAnchorModes (a : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  RepresentationalProfile a ∨ ClosureProfile a ∨ CertificatoryProfile a

section SomewhereFaithfulness

/--
**Weaker burden B0 (spatial):** a true completion claim forces **some** internal parameter—not necessarily
`anchor`—to carry M₁–M₃ success on its nominated gadgets.
-/
def IsBurdenFaithfulSomewhereClaim (wc : OpaqueAttemptWithClaim World Obs Repr Claim) : Prop :=
  wc.internalCompletionClaim →
    ∃ p : wc.attempt.carrier,
      RepresentationalProfileAt wc.attempt p ∨
        ClosureProfileAt wc.attempt p ∨
          CertificatoryProfileAt wc.attempt p

theorem burdenFaithful_claim_implies_somewhereFaithful
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim) :
    IsBurdenFaithfulClaim wc → IsBurdenFaithfulSomewhereClaim wc := by
  intro hf hcl
  rcases hf hcl with hR | hC | hK
  · exact ⟨wc.attempt.anchor, Or.inl (by simpa [representationalProfileAt_anchor] using hR)⟩
  · exact ⟨wc.attempt.anchor, Or.inr (Or.inl (by simpa [closureProfileAt_anchor] using hC))⟩
  · exact ⟨wc.attempt.anchor, Or.inr (Or.inr (by simpa [certificatoryProfileAt_anchor] using hK))⟩

/--
When **every** `p : carrier` is definitionally `anchor` (e.g. `carrier := Unit`), **somewhere** success is
**equivalent** to **anchor** burden-faithfulness: spatial weakening **disappears**.
-/
theorem isSomewhereFaithful_iff_burdenFaithful_of_subsingleton_carrier
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim)
    (hsub : ∀ p q : wc.attempt.carrier, p = q) :
    IsBurdenFaithfulSomewhereClaim wc ↔ IsBurdenFaithfulClaim wc := by
  refine Iff.intro (fun hs hcl => ?_) (burdenFaithful_claim_implies_somewhereFaithful wc)
  rcases hs hcl with ⟨p, hp | hp | hp⟩
  · have hpEq : p = wc.attempt.anchor := hsub p wc.attempt.anchor
    subst hpEq
    left
    simpa [representationalProfileAt_anchor] using hp
  · have hpEq : p = wc.attempt.anchor := hsub p wc.attempt.anchor
    subst hpEq
    right; left
    simpa [closureProfileAt_anchor] using hp
  · have hpEq : p = wc.attempt.anchor := hsub p wc.attempt.anchor
    subst hpEq
    right; right
    simpa [certificatoryProfileAt_anchor] using hp

end SomewhereFaithfulness

section JointFailureLayer

/--
**Weaker burden B¬∧ (propositional):** a true claim rules out **simultaneous** anchored failure of all three
canonical profiles.
-/
def IsJointFailureRuledOut (wc : OpaqueAttemptWithClaim World Obs Repr Claim) : Prop :=
  wc.internalCompletionClaim →
    ¬(¬ RepresentationalProfile wc.attempt ∧
        ¬ ClosureProfile wc.attempt ∧
          ¬ CertificatoryProfile wc.attempt)

theorem burdenFaithful_implies_jointFailureRuledOut
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim) :
    IsBurdenFaithfulClaim wc → IsJointFailureRuledOut wc := by
  intro hf hcl ⟨nR, nC, nK⟩
  rcases hf hcl with hR | hC | hK
  · exact nR hR
  · exact nC hC
  · exact nK hK

theorem jointFailureRuledOut_iff_burdenFaithful_claim_classical
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim) :
    IsJointFailureRuledOut wc ↔ IsBurdenFaithfulClaim wc := by
  classical
  refine Iff.intro (fun hj hcl => ?_) (burdenFaithful_implies_jointFailureRuledOut wc)
  by_cases hR : RepresentationalProfile wc.attempt
  · exact Or.inl hR
  · by_cases hC : ClosureProfile wc.attempt
    · exact Or.inr (Or.inl hC)
    · by_cases hK : CertificatoryProfile wc.attempt
      · exact Or.inr (Or.inr hK)
      · exact False.elim (hj hcl ⟨hR, hC, hK⟩)

end JointFailureLayer

section DoubleNegationLayer

/-- **Weaker (intuitionistic) weakening:** double-negated anchored three-way disjunction. -/
def IsWeakDNTripleModesClaim (wc : OpaqueAttemptWithClaim World Obs Repr Claim) : Prop :=
  wc.internalCompletionClaim → ¬¬ ThreeWayAnchorModes wc.attempt

theorem burdenFaithful_implies_weakDNTriple
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim) :
    IsBurdenFaithfulClaim wc → IsWeakDNTripleModesClaim wc := by
  intro hf hcl n3
  rcases hf hcl with hR | hC | hK
  · exact n3 (Or.inl hR)
  · exact n3 (Or.inr (Or.inl hC))
  · exact n3 (Or.inr (Or.inr hK))

end DoubleNegationLayer

section OmitOneStrictening

/--
**Omit-one bundles (stricter modes):** success attributed to **only two** mechanism classes at `anchor`.
Each **implies** full anchor burden-faithfulness; the converse fails when the **omitted** mode is exactly the
only one that succeeds.
-/

def OmitReprBurden (wc : OpaqueAttemptWithClaim World Obs Repr Claim) : Prop :=
  wc.internalCompletionClaim →
    ClosureProfile wc.attempt ∨ CertificatoryProfile wc.attempt

def OmitClosureBurden (wc : OpaqueAttemptWithClaim World Obs Repr Claim) : Prop :=
  wc.internalCompletionClaim →
    RepresentationalProfile wc.attempt ∨ CertificatoryProfile wc.attempt

def OmitCertBurden (wc : OpaqueAttemptWithClaim World Obs Repr Claim) : Prop :=
  wc.internalCompletionClaim →
    RepresentationalProfile wc.attempt ∨ ClosureProfile wc.attempt

theorem omitRepr_implies_burdenFaithful
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim) :
    OmitReprBurden wc → IsBurdenFaithfulClaim wc := by
  intro ho hcl
  exact Or.inr (ho hcl)

theorem omitClosure_implies_burdenFaithful
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim) :
    OmitClosureBurden wc → IsBurdenFaithfulClaim wc := by
  intro ho hcl
  rcases ho hcl with hR | hK
  · exact Or.inl hR
  · exact Or.inr (Or.inr hK)

theorem omitCert_implies_burdenFaithful
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim) :
    OmitCertBurden wc → IsBurdenFaithfulClaim wc := by
  intro ho hcl
  rcases ho hcl with hR | hC
  · exact Or.inl hR
  · exact Or.inr (Or.inl hC)

end OmitOneStrictening

section ToyCounterexamples

/-- Minimal architecture: **M₃** is the only potentially successful mode at the level of predicates. -/
def toyArchCertOnly : ReflexiveArchitecture Unit Unit Bool Unit where
  observe := fun _ => ()
  repr_success _ := False
  closure_success _ := False
  cert_success τ := τ () = true

/-- Representational success **only** at `p = true`; `anchor = false` has triple **anchored** failure. -/
def toyAttemptCertSomewhereOffAnchor : OpaqueTotalizationAttempt Unit Unit Bool Unit where
  arch := toyArchCertOnly
  carrier := Bool
  anchor := false
  reprAt := fun _ _ => false
  closureAt := fun _ s => s
  certAt
    | true => fun _ => true
    | false => fun _ => false

/-- **M₁** is the only potentially successful mode. -/
def toyArchReprOnly : ReflexiveArchitecture Unit Unit Bool Unit where
  observe := fun _ => ()
  repr_success ρ := ρ () = true
  closure_success _ := False
  cert_success _ := False

def toyAttemptReprOnlyAtAnchor : OpaqueTotalizationAttempt Unit Unit Bool Unit where
  arch := toyArchReprOnly
  carrier := Unit
  anchor := ()
  reprAt := fun _ _ => true
  closureAt := fun _ s => s
  certAt := fun _ _ => false

theorem toyCertSomewhere_threeAnchoredFailures :
    ¬ RepresentationalProfile toyAttemptCertSomewhereOffAnchor ∧
      ¬ ClosureProfile toyAttemptCertSomewhereOffAnchor ∧
        ¬ CertificatoryProfile toyAttemptCertSomewhereOffAnchor := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp [RepresentationalProfile, ClosureProfile, CertificatoryProfile,
    toyAttemptCertSomewhereOffAnchor, toyArchCertOnly] at h

theorem toyCertSomewhere_somewhereFaithful :
    IsBurdenFaithfulSomewhereClaim
      ⟨toyAttemptCertSomewhereOffAnchor, True⟩ := by
  intro _
  refine ⟨true, ?_⟩
  right; right
  simp [CertificatoryProfileAt, toyAttemptCertSomewhereOffAnchor, toyArchCertOnly]

theorem toyCertSomewhere_not_burdenFaithful :
    ¬ IsBurdenFaithfulClaim ⟨toyAttemptCertSomewhereOffAnchor, True⟩ := by
  intro hf
  have h3 := hf trivial
  simp [RepresentationalProfile, ClosureProfile, CertificatoryProfile, toyAttemptCertSomewhereOffAnchor,
    toyArchCertOnly] at h3

theorem toyCertSomewhere_not_threeWay_manual :
    ¬ ThreeWayAnchorModes toyAttemptCertSomewhereOffAnchor := by
  intro h
  rcases toyCertSomewhere_threeAnchoredFailures with ⟨nR, nC, nK⟩
  rcases h with hR | hC | hK
  · exact nR hR
  · exact nC hC
  · exact nK hK

theorem exists_somewhereFaithful_trueClaim_without_anchor_threeWay :
    ∃ wc : OpaqueAttemptWithClaim Unit Unit Bool Unit,
      IsBurdenFaithfulSomewhereClaim wc ∧ wc.internalCompletionClaim ∧
        ¬ ThreeWayAnchorModes wc.attempt :=
  ⟨_, toyCertSomewhere_somewhereFaithful, trivial, toyCertSomewhere_not_threeWay_manual⟩

theorem toyCertSomewhere_not_jointFailureRuledOut :
    ¬ IsJointFailureRuledOut ⟨toyAttemptCertSomewhereOffAnchor, True⟩ := by
  intro H
  have hj := H trivial
  rcases toyCertSomewhere_threeAnchoredFailures with ⟨nR, nC, nK⟩
  exact hj ⟨nR, nC, nK⟩

theorem somewhereFaithful_does_not_imply_jointFailureRuledOut_toy :
    IsBurdenFaithfulSomewhereClaim ⟨toyAttemptCertSomewhereOffAnchor, True⟩ ∧
      ¬ IsJointFailureRuledOut ⟨toyAttemptCertSomewhereOffAnchor, True⟩ :=
  ⟨toyCertSomewhere_somewhereFaithful, toyCertSomewhere_not_jointFailureRuledOut⟩

theorem toyReprOnly_burdenFaithful_not_omitRepr :
    IsBurdenFaithfulClaim ⟨toyAttemptReprOnlyAtAnchor, True⟩ ∧
      ¬ OmitReprBurden ⟨toyAttemptReprOnlyAtAnchor, True⟩ := by
  refine ⟨?_, ?_⟩
  · intro _
    left
    simp [RepresentationalProfile, toyAttemptReprOnlyAtAnchor, toyArchReprOnly]
  · intro ho
    have := ho trivial
    simp [ClosureProfile, CertificatoryProfile, toyAttemptReprOnlyAtAnchor, toyArchReprOnly] at this

end ToyCounterexamples

section AnchorNecessityBoundary

/-!
## Anchor necessity for anchored three-way completion modes (**boundary theorem**)

**Specification:** The flagship “honest internal completion” layer in **SPEC_015_KM2** targets obligations
**at `anchor`** (`RepresentationalProfile`, …). **`IsBurdenFaithfulSomewhereClaim`** is **not** a weaker
substitute for that layer: it is **relocated success geometry**. This section packages the **negative**
(non-entailment) and **collapse** (subsingleton carrier) facts so the repo can cite a single boundary API.

**Do not** treat somewhere-faithfulness as “almost enough” for anchored classification.
-/

/--
**Boundary (negative):** universal “somewhere-faithful + true claim ⇒ anchored `ThreeWayAnchorModes`” is
**false** already for `OpaqueAttemptWithClaim Unit Unit Bool Unit` (same toy as
`exists_somewhereFaithful_trueClaim_without_anchor_threeWay`).
-/
theorem anchored_threeWay_modes_not_entailed_by_somewhereFaithful_claim_utype :
    ¬ (∀ wc : OpaqueAttemptWithClaim Unit Unit Bool Unit,
        IsBurdenFaithfulSomewhereClaim wc →
          wc.internalCompletionClaim → ThreeWayAnchorModes wc.attempt) := by
  intro H
  rcases exists_somewhereFaithful_trueClaim_without_anchor_threeWay with ⟨wc, hsf, hcl, hn3⟩
  exact hn3 (H wc hsf hcl)

/--
**Boundary (collapse):** when every `p : carrier` is **`anchor`**, spatial weakening coincides with anchor
burden-faithfulness (**anchor identification** / subsingleton carrier).
-/
theorem anchor_identification_collapses_somewhereFaithful_to_burdenFaithful
    (wc : OpaqueAttemptWithClaim World Obs Repr Claim)
    (hsub : ∀ p q : wc.attempt.carrier, p = q) :
    IsBurdenFaithfulSomewhereClaim wc ↔ IsBurdenFaithfulClaim wc :=
  isSomewhereFaithful_iff_burdenFaithful_of_subsingleton_carrier wc hsub

/--
**Packaged boundary witness** for citations: separation, universal refutation, orthogonality
(somewhere \(\nRightarrow\) `IsJointFailureRuledOut` on toy).
-/
theorem anchor_necessity_boundary_bundle_utype :
    (∃ wc : OpaqueAttemptWithClaim Unit Unit Bool Unit,
        IsBurdenFaithfulSomewhereClaim wc ∧ wc.internalCompletionClaim ∧
          ¬ ThreeWayAnchorModes wc.attempt) ∧
      (¬ (∀ wc : OpaqueAttemptWithClaim Unit Unit Bool Unit,
            IsBurdenFaithfulSomewhereClaim wc →
              wc.internalCompletionClaim → ThreeWayAnchorModes wc.attempt)) ∧
      (IsBurdenFaithfulSomewhereClaim ⟨toyAttemptCertSomewhereOffAnchor, True⟩ ∧
        ¬ IsJointFailureRuledOut ⟨toyAttemptCertSomewhereOffAnchor, True⟩) :=
  ⟨exists_somewhereFaithful_trueClaim_without_anchor_threeWay,
    anchored_threeWay_modes_not_entailed_by_somewhereFaithful_claim_utype,
    somewhereFaithful_does_not_imply_jointFailureRuledOut_toy⟩

end AnchorNecessityBoundary

end StructuredNonexhaustibility
