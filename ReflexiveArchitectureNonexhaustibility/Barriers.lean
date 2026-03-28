import ReflexiveArchitectureNonexhaustibility.Interfaces

/-!
# Barriers — U₁–U₃ as honest consequences of interfaces (**SPEC_003_BT1**)

All proofs are **intuitionistic**; content lies in supplying the interfaces for a concrete `A`.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

variable (A : ReflexiveArchitecture World Obs Repr Claim)

/-- **U₁** — representational mode cannot succeed under diagonal interface. -/
theorem barrier_mode1 (h : DiagonalRepresentationalInterface A) : ¬ Mode1Success A := by
  rintro ⟨ρ, hp⟩
  exact h ρ hp

/-- **U₂** -/
theorem barrier_mode2 (h : ClosureObstructionInterface A) : ¬ Mode2Success A := by
  rintro ⟨Cl, hp⟩
  exact h Cl hp

/-- **U₃** -/
theorem barrier_mode3 (h : SemanticCertificationInterface A) : ¬ Mode3Success A := by
  rintro ⟨τ, hp⟩
  exact h τ hp

/-- Packaging the three obstacles as a conjunction of failures. -/
theorem barriers_triple
    (d1 : DiagonalRepresentationalInterface A)
    (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    ¬ Mode1Success A ∧ ¬ Mode2Success A ∧ ¬ Mode3Success A :=
  ⟨barrier_mode1 A d1, barrier_mode2 A d2, barrier_mode3 A d3⟩

end StructuredNonexhaustibility
