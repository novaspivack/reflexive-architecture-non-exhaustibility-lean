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

**Proved now:** reflection from `SyntacticTotalization`; **summit (classical):**
`abstract_opaque_mode_cover_classical` proves **`AbstractOpaqueModeCoverTarget`** with explicit
`classical` (**LEM** on the three mode profiles) given the **non-vacuous** `PositiveResidualProfile`
(**Profiles.lean**). **Intuitionistic:** `abstract_opaque_mode_cover_of_decidable` per-attempt
`Decidable` on those three predicates. Packaging / mediation iff lemmas; see **MANIFEST**.
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

theorem abstract_cover_implies_mediation_decomposition_target (W O R C : Type) :
    AbstractOpaqueModeCoverTarget W O R C → AbstractMediationDecompositionTarget W O R C := by
  intro H a hg
  exact mediation_decomposition_of_four_profiles (H a hg)

/--
**Classical** (explicit `classical` tactic): mediation-shaped target implies four-way cover.
Intuitionistically only the forward direction (`abstract_cover_implies_mediation_decomposition_target`)
holds in general.
-/
theorem abstract_mediation_implies_cover_classical (W O R C : Type) :
    AbstractMediationDecompositionTarget W O R C → AbstractOpaqueModeCoverTarget W O R C := by
  classical
  intro H a hg
  rcases H a hg with hPos | himp
  · exact Or.inr (Or.inr (Or.inr hPos))
  · by_cases hpos : PositiveResidualProfile a
    · exact Or.inr (Or.inr (Or.inr hpos))
    · rcases himp hpos with hR | hC | hK
      · exact Or.inl hR
      · exact Or.inr (Or.inl hC)
      · exact Or.inr (Or.inr (Or.inl hK))

theorem abstract_mediation_iff_cover_classical (W O R C : Type) :
    AbstractMediationDecompositionTarget W O R C ↔ AbstractOpaqueModeCoverTarget W O R C :=
  Iff.intro (abstract_mediation_implies_cover_classical W O R C)
    (abstract_cover_implies_mediation_decomposition_target W O R C)

/--
**Classical abstract mode cover** — `Genuine` is redundant here (theorem ignores it); kept for spec
alignment. Uses **LEM** on each of the three canonical profile propositions at `anchor`.
-/
theorem abstract_opaque_mode_cover_classical (W O R C : Type) :
    AbstractOpaqueModeCoverTarget W O R C := by
  classical
  intro a hg
  by_cases hR : RepresentationalProfile a
  · exact Or.inl hR
  · by_cases hC : ClosureProfile a
    · exact Or.inr (Or.inl hC)
    · by_cases hK : CertificatoryProfile a
      · exact Or.inr (Or.inr (Or.inl hK))
      · exact Or.inr (Or.inr (Or.inr (positive_residual_profile_of_three_failures hR hC hK)))

/--
**Intuitionistic:** same disjunction with per-attempt decidability on the three mode profiles.
-/
theorem abstract_opaque_mode_cover_of_decidable (W O R C : Type)
    (a : OpaqueTotalizationAttempt W O R C)
    (dR : Decidable (RepresentationalProfile a))
    (dC : Decidable (ClosureProfile a))
    (dK : Decidable (CertificatoryProfile a)) :
    RepresentationalProfile a ∨ ClosureProfile a ∨ CertificatoryProfile a ∨
      PositiveResidualProfile a := by
  rcases @Decidable.em _ dR with hR | hR
  · exact Or.inl hR
  · rcases @Decidable.em _ dC with hC | hC
    · exact Or.inr (Or.inl hC)
    · rcases @Decidable.em _ dK with hK | hK
      · exact Or.inr (Or.inr (Or.inl hK))
      · exact Or.inr (Or.inr (Or.inr (positive_residual_profile_of_three_failures hR hC hK)))

theorem abstract_opaque_mode_cover_target_of_pointwiseDecidable (W O R C : Type)
    (decR :
      ∀ (a : OpaqueTotalizationAttempt W O R C) (_ : GenuineInternalTotalizationAttempt a),
        Decidable (RepresentationalProfile a))
    (decC :
      ∀ (a : OpaqueTotalizationAttempt W O R C) (_ : GenuineInternalTotalizationAttempt a),
        Decidable (ClosureProfile a))
    (decK :
      ∀ (a : OpaqueTotalizationAttempt W O R C) (_ : GenuineInternalTotalizationAttempt a),
        Decidable (CertificatoryProfile a)) :
    AbstractOpaqueModeCoverTarget W O R C := by
  intro a hg
  exact abstract_opaque_mode_cover_of_decidable W O R C a (decR a hg) (decC a hg) (decK a hg)

theorem abstract_mediation_decomposition_target_classical (W O R C : Type) :
    AbstractMediationDecompositionTarget W O R C :=
  abstract_cover_implies_mediation_decomposition_target W O R C
    (abstract_opaque_mode_cover_classical W O R C)

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

theorem representational_profile_of_positive_embed (A : ReflexiveArchitecture World Obs Repr Claim)
    (dρ : World → Repr) (dCl : Set World → Set World) (dτ : Claim → Bool) (w : ResidualWitness) :
    RepresentationalProfile (fromSyntactic A dρ dCl dτ (.positive w)) ↔ A.repr_success dρ := by
  simp [RepresentationalProfile, fromSyntactic]

theorem closure_profile_of_positive_embed (A : ReflexiveArchitecture World Obs Repr Claim)
    (dρ : World → Repr) (dCl : Set World → Set World) (dτ : Claim → Bool) (w : ResidualWitness) :
    ClosureProfile (fromSyntactic A dρ dCl dτ (.positive w)) ↔ A.closure_success dCl := by
  simp [ClosureProfile, fromSyntactic]

theorem cert_profile_of_positive_embed (A : ReflexiveArchitecture World Obs Repr Claim)
    (dρ : World → Repr) (dCl : Set World → Set World) (dτ : Claim → Bool) (w : ResidualWitness) :
    CertificatoryProfile (fromSyntactic A dρ dCl dτ (.positive w)) ↔ A.cert_success dτ := by
  simp [CertificatoryProfile, fromSyntactic]

theorem positive_profile_of_positive (A : ReflexiveArchitecture World Obs Repr Claim)
    (dummyρ : World → Repr) (dummyCl : Set World → Set World) (dummyτ : Claim → Bool)
    (w : ResidualWitness) (hw : IsR4PositiveSurvivor w)
    (hR : ¬ RepresentationalProfile (fromSyntactic A dummyρ dummyCl dummyτ (.positive w)))
    (hC : ¬ ClosureProfile (fromSyntactic A dummyρ dummyCl dummyτ (.positive w)))
    (hK : ¬ CertificatoryProfile (fromSyntactic A dummyρ dummyCl dummyτ (.positive w))) :
    PositiveResidualProfile (fromSyntactic A dummyρ dummyCl dummyτ (.positive w)) := by
  refine ⟨w, hw, trivial, hR, hC, hK⟩

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
`.positive w` branch needs **R₄** witness, and **failure** of the three dummy-axis successes
(`¬ repr_success dρ` etc.): otherwise the attempt is not residually positive in the **Profile** sense.

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
    (hpos : ∀ w, t = .positive w → IsR4PositiveSurvivor w)
    (hpos₃ :
      ∀ w, t = .positive w →
        ¬ A.repr_success dρ ∧ ¬ A.closure_success dCl ∧ ¬ A.cert_success dτ) :
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
    rcases hpos₃ w rfl with ⟨nr, nc, nk⟩
    refine positive_profile_of_positive A dρ dCl dτ w (hpos w rfl) ?_ ?_ ?_
    · exact mt (representational_profile_of_positive_embed A dρ dCl dτ w).mpr nr
    · exact mt (closure_profile_of_positive_embed A dρ dCl dτ w).mpr nc
    · exact mt (cert_profile_of_positive_embed A dρ dCl dτ w).mpr nk

end StructuredNonexhaustibility
