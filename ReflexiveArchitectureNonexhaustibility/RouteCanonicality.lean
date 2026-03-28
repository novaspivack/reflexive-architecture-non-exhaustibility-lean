import Mathlib.Data.Set.Defs
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Modes
import ReflexiveArchitectureNonexhaustibility.Universal
import ReflexiveArchitectureNonexhaustibility.Interfaces
import ReflexiveArchitectureNonexhaustibility.Instances.ONE

/-!
# Route completeness & canonical-mode stability (**SPEC_014_CC1**, **EPIC_010**)

This epic is **strictly stronger** than mode **cover** (**SPEC_009_MC1**): it pins down the **M₁ / M₂ / M₃**
**success spectrum** as the canonical internal **routes** for the **`ReflexiveArchitecture`** signature
and records **stability** when success predicates **coarsen**.

**ONE / barriers:** **`OneRouteDiscipline`** + **`no_success_any_canonical_mode`** = **route completeness**
in the sense that **U₁–U₃** leave **no** successful traversal of the three canonical **success** slots.

**NEMS:** NemS Program V (`StructuralNonExhaustibility.ReflexiveSystem`, **`nems-lean`**) is a **parallel**
reflexive-system schema — compare at the **attachment** layer (**`EngineReflexiveMorphism`**, **`NemsStructuralProgramLink`**),
not by definitional identification.
-/

namespace StructuredNonexhaustibility.RouteCanonicality

open StructuredNonexhaustibility

variable {World : Type} {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**Canonical success spectrum** for **`ReflexiveArchitecture`**: representational, closure, or certification
success (**`Modes.lean`** / **SPEC_002_AM1**).
-/
abbrev CanonicalModeSuccessSpectrum (A : ReflexiveArchitecture World Obs Repr Claim) : Prop :=
  Mode1Success A ∨ Mode2Success A ∨ Mode3Success A

/--
**Route-blocking lemma (ONE packaging):** triple barriers forbid the **entire** canonical spectrum.
-/
theorem barriers_forbid_canonical_mode_spectrum (A : ReflexiveArchitecture World Obs Repr Claim)
    (d1 : DiagonalRepresentationalInterface A) (d2 : ClosureObstructionInterface A)
    (d3 : SemanticCertificationInterface A) :
    ¬ CanonicalModeSuccessSpectrum A :=
  no_success_any_canonical_mode A d1 d2 d3

/--
**ONE discipline** forbids the canonical spectrum — specialization of **`barriers_forbid_canonical_mode_spectrum`**.
-/
theorem oneRouteDiscipline_forbids_canonical_spectrum (A : ReflexiveArchitecture World Obs Repr Claim)
    (D : OneRouteDiscipline A) : ¬ CanonicalModeSuccessSpectrum A :=
  barriers_forbid_canonical_mode_spectrum A D.hasDiagonal D.hasClosure D.hasSemantic

/-!
## Stability (functorial flavor)

If **`A'`**’s success predicates are **implied** by **`A`**’s on the **same** gadgets, then **`Mode*i*Success`**
on **`A'`** implies **`Mode*i*Success`** on **`A`**. Thus **refinements** of architectures that **only make success
easier** are **monotone** along the canonical routes — no ad hoc fourth “success kind” is introduced at this layer.
-/

theorem mode1_success_of_repr_mono {A A' : ReflexiveArchitecture World Obs Repr Claim}
    (h : ∀ ρ : World → Repr, A'.repr_success ρ → A.repr_success ρ) :
    Mode1Success A' → Mode1Success A := by
  rintro ⟨ρ, hρ⟩
  exact ⟨ρ, h ρ hρ⟩

theorem mode2_success_of_closure_mono {A A' : ReflexiveArchitecture World Obs Repr Claim}
    (h : ∀ Cl : Set World → Set World, A'.closure_success Cl → A.closure_success Cl) :
    Mode2Success A' → Mode2Success A := by
  rintro ⟨Cl, hCl⟩
  exact ⟨Cl, h Cl hCl⟩

theorem mode3_success_of_cert_mono {A A' : ReflexiveArchitecture World Obs Repr Claim}
    (h : ∀ τ : Claim → Bool, A'.cert_success τ → A.cert_success τ) :
    Mode3Success A' → Mode3Success A := by
  rintro ⟨τ, hτ⟩
  exact ⟨τ, h τ hτ⟩

theorem canonical_spectrum_mono {A A' : ReflexiveArchitecture World Obs Repr Claim}
    (hρ : ∀ ρ, A'.repr_success ρ → A.repr_success ρ)
    (hCl : ∀ Cl, A'.closure_success Cl → A.closure_success Cl)
    (hτ : ∀ τ, A'.cert_success τ → A.cert_success τ) :
    CanonicalModeSuccessSpectrum A' → CanonicalModeSuccessSpectrum A := by
  intro h
  rcases h with h1 | h2 | h3
  · exact Or.inl (mode1_success_of_repr_mono hρ h1)
  · exact Or.inr (Or.inl (mode2_success_of_closure_mono hCl h2))
  · exact Or.inr (Or.inr (mode3_success_of_cert_mono hτ h3))

/-!
## Tranche 2 (**SPEC_014** **F2-1** extension) — alternative route taxonomies

**Anchor theorem shape:** **`canonical_spectrum_mono`**. Here: label type **`L`**, gadget-shaped tagging, and a **parameter**
**`successful : L → Prop`** — **not** defined as **`CanonicalModeSuccessSpectrum`** (anti-smuggling). **`TaxonomySound`**
states that **successful** labels **map** gadget-level architecture successes into the canonical **`Mode*i*Success`**
predicates.
-/

/--
**Alternative route taxonomy:** labels for each gadget class (**`SPEC_014`** Tranche 2 packaging).
-/
structure AltRouteTaxonomy (L : Type) (World Obs Repr Claim : Type) where
  reprTag : (World → Repr) → L
  closureTag : (Set World → Set World) → L
  certTag : (Claim → Bool) → L

/--
**Soundness (comparison / refinement):** **successful** labels **refine** into canonical mode successes when the
architecture **actually** succeeds on the tagged gadget.
-/
def TaxonomySound (L : Type) (T : AltRouteTaxonomy L World Obs Repr Claim)
    (A : ReflexiveArchitecture World Obs Repr Claim) (successful : L → Prop) : Prop :=
  (∀ ρ, successful (T.reprTag ρ) → A.repr_success ρ → Mode1Success A) ∧
    (∀ Cl, successful (T.closureTag Cl) → A.closure_success Cl → Mode2Success A) ∧
      (∀ τ, successful (T.certTag τ) → A.cert_success τ → Mode3Success A)

/--
**Completeness (coverage, not uniqueness):** each **canonical** mode success forces some **successful** gadget label on the
matching axis — **dual** to **`TaxonomySound`** for **iff** packaging with **`CanonicalModeSuccessSpectrum`**.
-/
def TaxonomyComplete (L : Type) (T : AltRouteTaxonomy L World Obs Repr Claim)
    (A : ReflexiveArchitecture World Obs Repr Claim) (successful : L → Prop) : Prop :=
  (Mode1Success A → ∃ ρ, A.repr_success ρ ∧ successful (T.reprTag ρ)) ∧
    (Mode2Success A → ∃ Cl, A.closure_success Cl ∧ successful (T.closureTag Cl)) ∧
      (Mode3Success A → ∃ τ, A.cert_success τ ∧ successful (T.certTag τ))

theorem canonical_spectrum_iff_labeled_successes
    (L : Type) (T : AltRouteTaxonomy L World Obs Repr Claim)
    (A : ReflexiveArchitecture World Obs Repr Claim) (successful : L → Prop)
    (hS : TaxonomySound L T A successful) (hC : TaxonomyComplete L T A successful) :
    CanonicalModeSuccessSpectrum A ↔
      (∃ ρ, A.repr_success ρ ∧ successful (T.reprTag ρ)) ∨
        (∃ Cl, A.closure_success Cl ∧ successful (T.closureTag Cl)) ∨
          (∃ τ, A.cert_success τ ∧ successful (T.certTag τ)) := by
  rcases hS with ⟨s1, s2, s3⟩
  rcases hC with ⟨c1, c2, c3⟩
  constructor
  · intro h
    rcases h with h1 | h2 | h3
    · exact Or.inl (c1 h1)
    · exact Or.inr (Or.inl (c2 h2))
    · exact Or.inr (Or.inr (c3 h3))
  · intro h
    rcases h with hρ | hCl | hτ
    · rcases hρ with ⟨ρ, hρ, hs⟩
      exact Or.inl (s1 ρ hs hρ)
    · rcases hCl with ⟨Cl, hCl, hs⟩
      exact Or.inr (Or.inl (s2 Cl hs hCl))
    · rcases hτ with ⟨τ, hτ, hs⟩
      exact Or.inr (Or.inr (s3 τ hs hτ))

/--
**F2-1 hook:** **`canonical_spectrum_mono`** **functorially** transports **`CanonicalModeSuccessSpectrum`** along easier
success on **`A'`**; combine with **`canonical_spectrum_iff_labeled_successes`** to compare **labeled** success **sets**
under sound + complete taxonomies (**no uniqueness**).
-/
theorem canonical_spectrum_mono_labeled {L : Type} (T : AltRouteTaxonomy L World Obs Repr Claim)
    (successful : L → Prop) {A A' : ReflexiveArchitecture World Obs Repr Claim}
    (hρ : ∀ ρ, A'.repr_success ρ → A.repr_success ρ)
    (hCl : ∀ Cl, A'.closure_success Cl → A.closure_success Cl)
    (hτ : ∀ τ, A'.cert_success τ → A.cert_success τ)
    (hS : TaxonomySound L T A successful) (hS' : TaxonomySound L T A' successful)
    (hC : TaxonomyComplete L T A successful) (hC' : TaxonomyComplete L T A' successful) :
    ((∃ ρ, A'.repr_success ρ ∧ successful (T.reprTag ρ)) ∨
        (∃ Cl, A'.closure_success Cl ∧ successful (T.closureTag Cl)) ∨
          (∃ τ, A'.cert_success τ ∧ successful (T.certTag τ))) →
      ((∃ ρ, A.repr_success ρ ∧ successful (T.reprTag ρ)) ∨
          (∃ Cl, A.closure_success Cl ∧ successful (T.closureTag Cl)) ∨
            (∃ τ, A.cert_success τ ∧ successful (T.certTag τ))) := by
  intro hlab
  have hsA' : CanonicalModeSuccessSpectrum A' := (canonical_spectrum_iff_labeled_successes L T A' successful hS' hC').2 hlab
  have hsA : CanonicalModeSuccessSpectrum A := canonical_spectrum_mono hρ hCl hτ hsA'
  exact (canonical_spectrum_iff_labeled_successes L T A successful hS hC).1 hsA

end StructuredNonexhaustibility.RouteCanonicality
