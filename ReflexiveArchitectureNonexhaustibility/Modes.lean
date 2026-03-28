import Mathlib.Data.Set.Defs
import ReflexiveArchitectureNonexhaustibility.Basic

/-!
# Modes — proposals vs successes (**SPEC_002_AM1**)

Separating **proposal** (some internal gadget is put forward) from **success** (the
architecture’s own success predicate holds). Barriers target **success**, not mere
existence of a gadget.
-/

namespace StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

variable (A : ReflexiveArchitecture World Obs Repr Claim)

/-- Some internal representation map is proposed (M₁ *attempt* in the loose sense). -/
def Mode1Proposal : Prop := Nonempty (World → Repr)


/-- M₁ **success**: some proposed map satisfies the architecture’s `repr_success`. -/
def Mode1Success : Prop := ∃ ρ : World → Repr, A.repr_success ρ

/-- Proposes a closure / hull operator (M₂ attempt, loose). -/
def Mode2Proposal : Prop := Nonempty (Set World → Set World)

/-- M₂ success. -/
def Mode2Success : Prop := ∃ Cl : Set World → Set World, A.closure_success Cl

/-- Proposes a Boolean classifier (M₃ attempt, loose). -/
def Mode3Proposal : Prop := Nonempty (Claim → Bool)

/-- M₃ success. -/
def Mode3Success : Prop := ∃ τ : Claim → Bool, A.cert_success τ

/-- Bundled triple proposal (convenient for product lemmas). -/
structure TripleProposal where
  ρ : World → Repr
  Cl : Set World → Set World
  τ : Claim → Bool

end StructuredNonexhaustibility
