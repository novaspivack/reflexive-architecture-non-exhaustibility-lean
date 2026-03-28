import Mathlib.Data.Set.Defs
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Modes

/-!
# Interfaces — abstract obstruction hypotheses (**SPEC_003_BT1**)

These are **meaningful** hypotheses: each asserts **no** proposed gadget in that class
satisfies the architecture’s success predicate. Instantiating them for concrete
architectures is where RI / RFO / ICA–SEM mathematics enters.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

variable (A : ReflexiveArchitecture World Obs Repr Claim)

/-- RI-style representational obstruction: every internal ρ **fails** `repr_success`. -/
abbrev DiagonalRepresentationalInterface : Prop :=
  ∀ ρ : World → Repr, ¬ A.repr_success ρ

/-- RFO-style closure obstruction. -/
abbrev ClosureObstructionInterface : Prop :=
  ∀ Cl : Set World → Set World, ¬ A.closure_success Cl

/-- ICA/SEM-style certification obstruction. -/
abbrev SemanticCertificationInterface : Prop :=
  ∀ τ : Claim → Bool, ¬ A.cert_success τ

end StructuredNonexhaustibility
