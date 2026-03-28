import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Interfaces

/-!
# Residuals — R₁–R₄ classification (**SPEC_004_RC1**)

Each witness carries a **declared class** `rc : ResidualClass` (taxonomy tag). Predicates
`IsR1Residual` … `IsR4PositiveSurvivor` are **not** globally `True`: they hold exactly when
`rc` matches the corresponding constructor.

This is appropriate for the **residual calculus** spec (classification of witness roles).
It does **not** import the mode-cover conclusion into predicates by fiat.

**Admissibility** (**SPEC_012_AA1** / **EPIC_008**): **R₄** survivors used in the **honest** aftermath story must carry
**`U123BarrierData`-shaped** carriers (**D-002**); other residual **classes** are admissible without that linkage. The
abstract **mode-cover** **`PositiveResidualProfile`** (**`Profiles.lean`**) does **not** restate this predicate — see module
doc there.

**Cross-repo (EPIC_004 / D-001):** NemS **Program V** (**`nems-lean`**, e.g. **SurvivorCalculus**) is the sibling
discipline for **positive survivor** content; this file’s **`R4`** tag stays **paper C**-native — link morphisms at
**`EngineReflexiveMorphism`** / enrichment bridges, **not** by redefining **`ResidualClass`** here.
-/

namespace StructuredNonexhaustibility

/-- Negative / positive **roles** per **SPEC_004_RC1** table (Paper C). -/
inductive ResidualClass where
  /-- R₁ — diagonal / uncaptured self-reference. -/
  | R1 : ResidualClass
  /-- R₂ — transition / outside invariant-preserving internal reachability. -/
  | R2 : ResidualClass
  /-- R₃ — semantic / adequacy outside total internal theory. -/
  | R3 : ResidualClass
  /-- R₄ — positive structured survivor (multi-aspect coordination; not mere failure residue). -/
  | R4 : ResidualClass

/--
Residual witness: typed point + explicit **declared** class.
-/
structure ResidualWitness where
  rc : ResidualClass
  carrier : Type
  witness : carrier

def IsR1Residual (w : ResidualWitness) : Prop :=
  w.rc = ResidualClass.R1

def IsR2Residual (w : ResidualWitness) : Prop :=
  w.rc = ResidualClass.R2

def IsR3Residual (w : ResidualWitness) : Prop :=
  w.rc = ResidualClass.R3

def IsR4PositiveSurvivor (w : ResidualWitness) : Prop :=
  w.rc = ResidualClass.R4

/--
**Admissible residual witness (**SPEC_012_AA1** first real slice): either **not** tagged **R₄**, or the witness
**package** exposes a **barrier-pack** carrier (**`U123BarrierData A`**) for some architecture.

**Anti-smuggling:** this does **not** redefine **`PositiveResidualProfile`**; mode cover keeps a **schematic** R₄ branch
without importing this discipline (**`Profiles.lean`**).
-/
def AdmissibleResidual (w : ResidualWitness) : Prop :=
  ¬ IsR4PositiveSurvivor w ∨
    ∃ (World : Type) (Obs : ObsTy) (Repr : ReprTy) (Claim : ClaimTy)
      (A : ReflexiveArchitecture World Obs Repr Claim), w.carrier = U123BarrierData A

theorem admissible_of_not_r4 {w : ResidualWitness} (h : ¬ IsR4PositiveSurvivor w) : AdmissibleResidual w :=
  Or.inl h

def IsNegativeResidualClass (w : ResidualWitness) : Prop :=
  IsR1Residual w ∨ IsR2Residual w ∨ IsR3Residual w

/-- Example witness: **R₁** (nonemptiness for downstream lemmas). -/
def trivialResidualWitness : ResidualWitness :=
  ⟨ResidualClass.R1, Unit, ()⟩

/-- Example **R₄** witness (structured positive branch scaffolding). -/
def trivialR4ResidualWitness : ResidualWitness :=
  ⟨ResidualClass.R4, Unit, ()⟩

theorem isR1_trivial : IsR1Residual trivialResidualWitness :=
  rfl

theorem isR4_trivialR4 : IsR4PositiveSurvivor trivialR4ResidualWitness :=
  rfl

theorem ne_r1_r4 : ResidualClass.R1 ≠ ResidualClass.R4 := by
  intro e; cases e

theorem ne_r2_r4 : ResidualClass.R2 ≠ ResidualClass.R4 := by
  intro e; cases e

theorem ne_r3_r4 : ResidualClass.R3 ≠ ResidualClass.R4 := by
  intro e; cases e

theorem residual_r1_not_r4 {w : ResidualWitness} :
    IsR1Residual w → IsR4PositiveSurvivor w → False := by
  intro h1 h4
  simp [IsR1Residual, IsR4PositiveSurvivor] at h1 h4
  exact ne_r1_r4 (h1.symm.trans h4)

theorem negative_not_r4 (w : ResidualWitness) (hn : IsNegativeResidualClass w)
    (h4 : IsR4PositiveSurvivor w) : False := by
  rcases hn with h1 | h2 | h3
  · exact residual_r1_not_r4 h1 h4
  · simp [IsR2Residual, IsR4PositiveSurvivor] at h2 h4
    exact ne_r2_r4 (h2.symm.trans h4)
  · simp [IsR3Residual, IsR4PositiveSurvivor] at h3 h4
    exact ne_r3_r4 (h3.symm.trans h4)

theorem admissible_of_negativeClass {w : ResidualWitness} (hn : IsNegativeResidualClass w) : AdmissibleResidual w :=
  admissible_of_not_r4 fun h4 => negative_not_r4 w hn h4

theorem IsNegativeResidualClass_or_IsR4 (w : ResidualWitness) :
    IsNegativeResidualClass w ∨ IsR4PositiveSurvivor w := by
  rcases w with ⟨rc, γ, p⟩
  cases rc
  · left; left; rfl
  · left; right; left; rfl
  · left; right; right; rfl
  · right; rfl

end StructuredNonexhaustibility
