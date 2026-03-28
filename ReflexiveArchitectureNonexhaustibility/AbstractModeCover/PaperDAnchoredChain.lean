import ReflexiveArchitectureNonexhaustibility.Universal
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Profiles
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.AnchoredFlagship

/-!
# Paper D — anchored composition chain (**SPEC_010_US1**, **SPEC_015_KM2**)

**End-to-end spine (anchored flagship + barriers):**

1. **`HonestAnchoredInternalCompletion`** with **true** `internalCompletionClaim` and **`IsBurdenFaithfulClaim`**
   forces **at least one** of the **anchored** canonical profiles M₁–M₃ (**`AnchoredFlagship` /
   `abstract_four_way_of_burdenFaithful`** — the residual disjunct is **not** used).
2. Each such profile **implies** the corresponding **`Mode*i*Success`** on `attempt.arch` via nominations at
   **`anchor`** (**`Profiles.lean`** bridge lemmas).
3. **`no_success_any_canonical_mode`** (**`Universal.lean`**, U₁–U₃ interfaces) refutes **M₁ ∨ M₂ ∨ M₃ success**.

**Conclusion:** the **conjunction** of a **true** anchored burden-faithful completion package over `arch` and
the **triple barrier** interfaces on the **same** `arch` is **absurd** — the flagship **structured
nonexhaustibility** consequence for this layer.

**Alternate proof** (same logical content, no `Mode` disjunction): barriers yield **¬**each anchored profile;
use **`burdenFaithful_claim_incompatible_with_threeFailures`** (**`GenuinenessCandidates.lean`**).

**Not** the **`Genuine` alone** / arbitrary opaque attempt story: quantification here is **interface-equipped**
(**`HonestAnchoredInternalCompletion`**), matching **`LayerDiscipline.lean`**.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**Paper D (anchored chain):** true **`HonestAnchoredInternalCompletion`** contradicts **U₁–U₃** on the same
architecture.

**Proof:** burden-faithfulness + true claim ⇒ anchored M₁–M₃ profile ⇒ corresponding **`Mode` success** ⇒
contradiction with **`no_success_any_canonical_mode`**.
-/
theorem paper_d_anchored_honest_completion_refutes_triple_barriers
    (p : HonestAnchoredInternalCompletion World Obs Repr Claim)
    (hcl : p.base.internalCompletionClaim)
    (d1 : DiagonalRepresentationalInterface p.base.attempt.arch)
    (d2 : ClosureObstructionInterface p.base.attempt.arch)
    (d3 : SemanticCertificationInterface p.base.attempt.arch) :
    False := by
  rcases p.burdenFaithfulness hcl with hR | hC | hK
  · exact no_success_any_canonical_mode p.base.attempt.arch d1 d2 d3
      (Or.inl (representationalProfile_implies_mode1Success p.base.attempt hR))
  · exact no_success_any_canonical_mode p.base.attempt.arch d1 d2 d3
      (Or.inr (Or.inl (closureProfile_implies_mode2Success p.base.attempt hC)))
  · exact no_success_any_canonical_mode p.base.attempt.arch d1 d2 d3
      (Or.inr (Or.inr (certificatoryProfile_implies_mode3Success p.base.attempt hK)))

end StructuredNonexhaustibility
