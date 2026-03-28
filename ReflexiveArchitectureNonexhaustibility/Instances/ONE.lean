import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Interfaces
import ReflexiveArchitectureNonexhaustibility.Modes
import ReflexiveArchitectureNonexhaustibility.Universal

/-!
# ONE discipline — **conservative** instance scaffolding (**SPEC_011_OI1**)
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

structure OneRouteDiscipline (A : ReflexiveArchitecture World Obs Repr Claim) : Prop where
  hasDiagonal : DiagonalRepresentationalInterface A
  hasClosure : ClosureObstructionInterface A
  hasSemantic : SemanticCertificationInterface A

theorem one_discipline_implies_no_canonical_success
    (A : ReflexiveArchitecture World Obs Repr Claim) (D : OneRouteDiscipline A) :
    ¬ (Mode1Success A ∨ Mode2Success A ∨ Mode3Success A) :=
  no_success_any_canonical_mode A D.hasDiagonal D.hasClosure D.hasSemantic

end StructuredNonexhaustibility
