import Mathlib.Data.Set.Defs
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.SyntacticModeCover
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Attempt
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Profiles
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Mediation
import ReflexiveArchitectureNonexhaustibility.Adequacy

/-!
# Abstract classification + syntactic reflection (**SPEC_015_KM2**, **Classification**)

**Summit:** `AbstractOpaqueModeCoverTarget` names the opaque four-way obligation.

**Proved now:** reflection from `SyntacticTotalization` — embedding + four-way profiles for
syntactic instances (sanity check / base case; **not** the abstract theorem).
-/

namespace StructuredNonexhaustibility

variable {World Obs Repr Claim : Type}

/--
**Abstract mode-cover obligation** (opaque layer). Unproved as a `theorem` until the mediation stack
earns it; safe as a `def` of type `Prop`.
-/
def AbstractOpaqueModeCoverTarget (World Obs Repr Claim : Type) : Prop :=
  (∀ (a : OpaqueTotalizationAttempt World Obs Repr Claim),
    GenuineInternalTotalizationAttempt a →
    (RepresentationalProfile a ∨
      ClosureProfile a ∨
        CertificatoryProfile a ∨
          PositiveResidualProfile a))

theorem abstract_mode_cover_eq_mediation_stmnt (W O R C : Type) :
    AbstractOpaqueModeCoverTarget W O R C = AbstractFourWayMediationStatement W O R C :=
  rfl

/--
Embed tagged syntax into opaque attempts. Off-axis nominations are **explicit dummy** parameters.
For `SyntacticTotalization.positive w`, the residual witness **occupies** `carrier` so the
positive branch has structural contact with the attempt.
-/
def fromSyntactic (A : ReflexiveArchitecture World Obs Repr Claim)
    (dummyρ : World → Repr) (dummyCl : Set World → Set World) (dummyτ : Claim → Bool) :
    SyntacticTotalization World Repr Claim → OpaqueTotalizationAttempt World Obs Repr Claim
  | .repr ρ =>
    { arch := A
      carrier := Unit
      anchor := ()
      reprAt := fun _ => ρ
      closureAt := fun _ => dummyCl
      certAt := fun _ => dummyτ }
  | .closure Cl =>
    { arch := A
      carrier := Unit
      anchor := ()
      reprAt := fun _ => dummyρ
      closureAt := fun _ => Cl
      certAt := fun _ => dummyτ }
  | .cert τ =>
    { arch := A
      carrier := Unit
      anchor := ()
      reprAt := fun _ => dummyρ
      closureAt := fun _ => dummyCl
      certAt := fun _ => τ }
  | .positive w =>
    { arch := A
      carrier := w.carrier
      anchor := w.witness
      reprAt := fun _ => dummyρ
      closureAt := fun _ => dummyCl
      certAt := fun _ => dummyτ }

@[simp]
theorem reprAt_fromSyntactic_repr (A : ReflexiveArchitecture World Obs Repr Claim)
    (dummyρ : World → Repr) (dummyCl : Set World → Set World) (dummyτ : Claim → Bool)
    (ρ : World → Repr) :
    (fromSyntactic A dummyρ dummyCl dummyτ (.repr ρ)).reprAt () = ρ := rfl

@[simp]
theorem closureAt_fromSyntactic_closure (A : ReflexiveArchitecture World Obs Repr Claim)
    (dummyρ : World → Repr) (dummyCl : Set World → Set World) (dummyτ : Claim → Bool)
    (Cl : Set World → Set World) :
    (fromSyntactic A dummyρ dummyCl dummyτ (.closure Cl)).closureAt () = Cl := rfl

@[simp]
theorem certAt_fromSyntactic_cert (A : ReflexiveArchitecture World Obs Repr Claim)
    (dummyρ : World → Repr) (dummyCl : Set World → Set World) (dummyτ : Claim → Bool)
    (τ : Claim → Bool) :
    (fromSyntactic A dummyρ dummyCl dummyτ (.cert τ)).certAt () = τ := rfl

theorem representational_profile_of_repr (A : ReflexiveArchitecture World Obs Repr Claim)
    (dummyρ : World → Repr) (dummyCl : Set World → Set World) (dummyτ : Claim → Bool)
    (ρ : World → Repr) :
    RepresentationalProfile (fromSyntactic A dummyρ dummyCl dummyτ (.repr ρ)) ↔
      A.repr_success ρ := by
  simp [RepresentationalProfile, fromSyntactic]

theorem closure_profile_of_closure (A : ReflexiveArchitecture World Obs Repr Claim)
    (dummyρ : World → Repr) (dummyCl : Set World → Set World) (dummyτ : Claim → Bool)
    (Cl : Set World → Set World) :
    ClosureProfile (fromSyntactic A dummyρ dummyCl dummyτ (.closure Cl)) ↔
      A.closure_success Cl := by
  simp [ClosureProfile, fromSyntactic]

theorem cert_profile_of_cert (A : ReflexiveArchitecture World Obs Repr Claim)
    (dummyρ : World → Repr) (dummyCl : Set World → Set World) (dummyτ : Claim → Bool)
    (τ : Claim → Bool) :
    CertificatoryProfile (fromSyntactic A dummyρ dummyCl dummyτ (.cert τ)) ↔
      A.cert_success τ := by
  simp [CertificatoryProfile, fromSyntactic]

theorem positive_profile_of_positive (A : ReflexiveArchitecture World Obs Repr Claim)
    (dummyρ : World → Repr) (dummyCl : Set World → Set World) (dummyτ : Claim → Bool)
    (w : ResidualWitness) (hw : IsR4PositiveSurvivor w) :
    PositiveResidualProfile (fromSyntactic A dummyρ dummyCl dummyτ (.positive w)) := by
  refine ⟨w, hw, admissible_trivial_residual w, rfl, by rfl⟩

theorem syntactic_embedding_carrier_nonempty (A : ReflexiveArchitecture World Obs Repr Claim)
    (dρ : World → Repr) (dCl : Set World → Set World) (dτ : Claim → Bool)
    (t : SyntacticTotalization World Repr Claim) :
    Nonempty (fromSyntactic A dρ dCl dτ t).carrier := by
  cases t
  case repr => exact ⟨()⟩
  case closure => exact ⟨()⟩
  case cert => exact ⟨()⟩
  case positive w => exact ⟨w.witness⟩

/--
**Reflection (conditional):** for a syntactic shape, if the architecture’s success predicate
holds on the **active** axis encoded by that shape, then the corresponding profile holds; the
`.positive w` branch satisfies `PositiveResidualProfile` when `w` is **R₄** (`IsR4PositiveSurvivor w`).

Unconditional four-way OR of profiles is **false** in general (e.g. `.repr ρ` with `¬ repr_success ρ`
and dummy gadgets failing the other modes).
-/
theorem syntactic_reflection_four_way_of_axis_success
    (A : ReflexiveArchitecture World Obs Repr Claim)
    (dρ : World → Repr) (dCl : Set World → Set World) (dτ : Claim → Bool)
    (t : SyntacticTotalization World Repr Claim)
    (hρ : ∀ ρ, t = .repr ρ → A.repr_success ρ)
    (hCl : ∀ Cl, t = .closure Cl → A.closure_success Cl)
    (hτ : ∀ τ, t = .cert τ → A.cert_success τ)
    (hpos : ∀ w, t = .positive w → IsR4PositiveSurvivor w) :
    RepresentationalProfile (fromSyntactic A dρ dCl dτ t) ∨
      ClosureProfile (fromSyntactic A dρ dCl dτ t) ∨
        CertificatoryProfile (fromSyntactic A dρ dCl dτ t) ∨
          PositiveResidualProfile (fromSyntactic A dρ dCl dτ t) := by
  rcases syntactic_four_way t with h | h | h | h
  · rcases h with ⟨ρ, rfl⟩
    left
    exact (representational_profile_of_repr A dρ dCl dτ ρ).mpr (hρ ρ rfl)
  · rcases h with ⟨Cl, rfl⟩
    right; left
    exact (closure_profile_of_closure A dρ dCl dτ Cl).mpr (hCl Cl rfl)
  · rcases h with ⟨τ, rfl⟩
    right; right; left
    exact (cert_profile_of_cert A dρ dCl dτ τ).mpr (hτ τ rfl)
  · rcases h with ⟨w, rfl⟩
    right; right; right
    exact positive_profile_of_positive A dρ dCl dτ w (hpos w rfl)

end StructuredNonexhaustibility
