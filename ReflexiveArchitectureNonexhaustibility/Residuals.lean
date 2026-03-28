import ReflexiveArchitectureNonexhaustibility.Basic

/-!
# Residuals — R₁–R₄ classification (**SPEC_004_RC1**)

Witness types are independent of any theorem: **R₄** is a predicate on witnesses, not
identification with `World`.
-/

namespace StructuredNonexhaustibility

/-- Abstract residual witness (refine per application). -/
structure ResidualWitness where
  carrier : Type
  witness : carrier

def IsR1Residual (_w : ResidualWitness) : Prop := True
def IsR2Residual (_w : ResidualWitness) : Prop := True
def IsR3Residual (_w : ResidualWitness) : Prop := True
def IsR4PositiveSurvivor (_w : ResidualWitness) : Prop := True
def AdmissibleResidual (_w : ResidualWitness) : Prop := True

def IsNegativeResidualClass (w : ResidualWitness) : Prop :=
  IsR1Residual w ∨ IsR2Residual w ∨ IsR3Residual w

/-- Example witness (nonemptiness for downstream lemmas). -/
def trivialResidualWitness : ResidualWitness := ⟨Unit, ()⟩

end StructuredNonexhaustibility
