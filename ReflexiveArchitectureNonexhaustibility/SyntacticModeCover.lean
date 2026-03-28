import Mathlib.Data.Set.Defs
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Residuals

/-!
# Syntactic mode cover (**SPEC_009_MC1** — syntactic layer; see **MANIFEST**).
-/

namespace StructuredNonexhaustibility

/-- Syntactic tagged exhaustion shapes (pedagogical / scaffolding). -/
inductive SyntacticTotalization (World Repr Claim : Type) where
  | repr (ρ : World → Repr)
  | closure (Cl : Set World → Set World)
  | cert (τ : Claim → Bool)
  | positive (w : ResidualWitness)

theorem syntactic_four_way {World Repr Claim : Type} (t : SyntacticTotalization World Repr Claim) :
    (∃ ρ, t = SyntacticTotalization.repr ρ) ∨
    (∃ Cl, t = SyntacticTotalization.closure Cl) ∨
    (∃ τ, t = SyntacticTotalization.cert τ) ∨
    (∃ w, t = SyntacticTotalization.positive w) := by
  cases t
  case repr ρ => left; exact ⟨ρ, rfl⟩
  case closure Cl => right; left; exact ⟨Cl, rfl⟩
  case cert τ => right; right; left; exact ⟨τ, rfl⟩
  case positive w => right; right; right; exact ⟨w, rfl⟩

def SyntacticGenuine {World Repr Claim : Type} (_t : SyntacticTotalization World Repr Claim) : Prop :=
  True

theorem syntactic_mode_cover_for_genuine {World Repr Claim : Type}
    (t : SyntacticTotalization World Repr Claim) (_hg : SyntacticGenuine t) :
    (∃ ρ, t = SyntacticTotalization.repr ρ) ∨
    (∃ Cl, t = SyntacticTotalization.closure Cl) ∨
    (∃ τ, t = SyntacticTotalization.cert τ) ∨
    (∃ w, t = SyntacticTotalization.positive w) :=
  syntactic_four_way t

end StructuredNonexhaustibility
