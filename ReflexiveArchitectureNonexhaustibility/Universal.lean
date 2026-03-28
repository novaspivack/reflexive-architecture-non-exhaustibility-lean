import ReflexiveArchitectureNonexhaustibility.Barriers
import ReflexiveArchitectureNonexhaustibility.Modes

/-!
# Universal structured non-exhaustibility — **composition layer** (**SPEC_010_US1**)

**Layering:** this file proves **mode-calculus** barriers (**U₁–U₃**) vs `Mode*i*Success`. **Anchored**
opaque cover + barrier composition (interface-equipped **I_anch**) is **`PaperDAnchoredChain.lean`**:
**`paper_d_anchored_honest_completion_refutes_triple_barriers`** factors **`no_success_any_canonical_mode`**
with profile **`→` `Mode` success** bridges (**`Profiles.lean`**) and **`HonestAnchoredInternalCompletion`**
(**SPEC_010_US1**, **SPEC_015_KM2**). **`fromSyntactic`** remains the tag-carrying reflection lane.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

variable (A : ReflexiveArchitecture World Obs Repr Claim)

theorem no_success_any_canonical_mode
    (d1 : DiagonalRepresentationalInterface A)
    (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    ¬ (Mode1Success A ∨ Mode2Success A ∨ Mode3Success A) := by
  intro h
  cases h with
  | inl h1 => exact barrier_mode1 A d1 h1
  | inr h2 =>
    cases h2 with
    | inl h2 => exact barrier_mode2 A d2 h2
    | inr h3 => exact barrier_mode3 A d3 h3

theorem no_success_each_mode_separately
    (d1 : DiagonalRepresentationalInterface A)
    (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    ¬ Mode1Success A ∧ ¬ Mode2Success A ∧ ¬ Mode3Success A :=
  barriers_triple A d1 d2 d3

end StructuredNonexhaustibility
