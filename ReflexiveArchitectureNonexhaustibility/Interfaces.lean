import Mathlib.Data.Set.Defs
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Modes

/-!
# Interfaces — abstract obstruction hypotheses (**SPEC_003_BT1**)

These are **meaningful** hypotheses: each asserts **no** proposed gadget in that class
satisfies the architecture’s success predicate. Instantiating them for concrete
architectures is where RI / RFO / ICA–SEM mathematics enters.

**D3:** **U₁–U₃** **transport** along pointwise **`↔`** of the three success predicates (**no** bundled **`A = A'`**).
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

/--
**U₁–U₃ barrier pack (**D-002**, **SPEC_003_BT1**): a **Type**-valued record of the three hypotheses.

Used to make **`ResidualWitness.carrier`** depend on **actual** obstruction assumptions (not merely **`Unit`**),
so positive-survivor scaffolding can be **barrier-linked** at the type level.
-/
structure U123BarrierData (A : ReflexiveArchitecture World Obs Repr Claim) : Type where
  reprBarrier : DiagonalRepresentationalInterface A
  closureBarrier : ClosureObstructionInterface A
  certBarrier : SemanticCertificationInterface A

/--
Transport a **U₁–U₃** pack along **`ReflexiveArchitecture`** equality (**SPEC_003_BT1** / **D3** relocation seed).

When **`h : A = A'`** is **`rfl`**, this is **definitionally** the identity on **`U123BarrierData A`**.
-/
def u123BarrierData_cast {A A' : ReflexiveArchitecture World Obs Repr Claim} (h : A = A')
    (b : U123BarrierData A) : U123BarrierData A' :=
  match h with
  | rfl => b

@[simp]
theorem u123BarrierData_cast_rfl {A : ReflexiveArchitecture World Obs Repr Claim} (b : U123BarrierData A) :
    u123BarrierData_cast (rfl : A = A) b = b :=
  rfl

section D3_success_field_iff

variable {A A' : ReflexiveArchitecture World Obs Repr Claim}

theorem diagonalRepresentationalInterface_iff_of_repr_success_iff
    (h : ∀ ρ : World → Repr, A.repr_success ρ ↔ A'.repr_success ρ) :
    DiagonalRepresentationalInterface A ↔ DiagonalRepresentationalInterface A' :=
  Iff.intro (fun H ρ hA' => H ρ ((h ρ).mpr hA')) fun H' ρ hA => H' ρ ((h ρ).mp hA)

theorem closureObstructionInterface_iff_of_closure_success_iff
    (h : ∀ Cl : Set World → Set World, A.closure_success Cl ↔ A'.closure_success Cl) :
    ClosureObstructionInterface A ↔ ClosureObstructionInterface A' :=
  Iff.intro (fun H Cl hA' => H Cl ((h Cl).mpr hA')) fun H' Cl hA => H' Cl ((h Cl).mp hA)

theorem semanticCertificationInterface_iff_of_cert_success_iff
    (h : ∀ τ : Claim → Bool, A.cert_success τ ↔ A'.cert_success τ) :
    SemanticCertificationInterface A ↔ SemanticCertificationInterface A' :=
  Iff.intro (fun H τ hA' => H τ ((h τ).mpr hA')) fun H' τ hA => H' τ ((h τ).mp hA)

/--
Relabel **U₁–U₃** content across **`A`**, **`A'`** when success predicates agree **pointwise** (**`↔`**).

**Promotion** **`ResidualWitness.base`** **equality** across **`U123BarrierData A`** vs **`U123BarrierData A'`** still needs
identification of carriers (**`A = A'`** or **`HEq`**); this is the honest **pack-level** relocation step.
-/
def u123BarrierData_transport_of_success_field_iff (hρ : ∀ ρ, A.repr_success ρ ↔ A'.repr_success ρ)
    (hCl : ∀ Cl, A.closure_success Cl ↔ A'.closure_success Cl) (hτ : ∀ τ, A.cert_success τ ↔ A'.cert_success τ)
    (b : U123BarrierData A) : U123BarrierData A' where
  reprBarrier := (diagonalRepresentationalInterface_iff_of_repr_success_iff hρ).mp b.reprBarrier
  closureBarrier := (closureObstructionInterface_iff_of_closure_success_iff hCl).mp b.closureBarrier
  certBarrier := (semanticCertificationInterface_iff_of_cert_success_iff hτ).mp b.certBarrier

theorem nonempty_u123BarrierData_iff_of_success_field_iff (hρ : ∀ ρ, A.repr_success ρ ↔ A'.repr_success ρ)
    (hCl : ∀ Cl, A.closure_success Cl ↔ A'.closure_success Cl)
    (hτ : ∀ τ, A.cert_success τ ↔ A'.cert_success τ) :
    Nonempty (U123BarrierData A) ↔ Nonempty (U123BarrierData A') :=
  Iff.intro (fun ⟨b⟩ => ⟨u123BarrierData_transport_of_success_field_iff hρ hCl hτ b⟩) fun ⟨b'⟩ =>
    ⟨{ reprBarrier := (diagonalRepresentationalInterface_iff_of_repr_success_iff hρ).mpr b'.reprBarrier
       closureBarrier := (closureObstructionInterface_iff_of_closure_success_iff hCl).mpr b'.closureBarrier
       certBarrier := (semanticCertificationInterface_iff_of_cert_success_iff hτ).mpr b'.certBarrier }⟩

end D3_success_field_iff

section D3_success_field_morphism

/-!
## **P4** — one-way (**non-**`↔`**) success morphisms

Transport **U₁–U₃** across **`ReflexiveArchitecture`** pairs when successes refine along an implication (**forward**
**`A → A'`** or **backward** **`A' → A`** on each success predicate). These lemmas are **strictly weaker** than the
pointwise **`↔`** block above; they match forgetful / directed simulation morphisms rather than definitional relabeling.
-/

variable {A A' : ReflexiveArchitecture World Obs Repr Claim}

/-- **`A.repr_success` ⇒ `A'.repr_success`:** barriers on **`A'`** **subimply** barriers on **`A`**. -/
theorem diagonalRepresentationalInterface_of_repr_success_imp_of_right
    (h : ∀ ρ : World → Repr, A.repr_success ρ → A'.repr_success ρ) :
    DiagonalRepresentationalInterface A' → DiagonalRepresentationalInterface A := fun H' ρ hA =>
  H' ρ (h ρ hA)

/-- Dual: successes grow from **`A'`** to **`A`**. -/
theorem diagonalRepresentationalInterface_of_repr_success_imp_of_left
    (h : ∀ ρ : World → Repr, A'.repr_success ρ → A.repr_success ρ) :
    DiagonalRepresentationalInterface A → DiagonalRepresentationalInterface A' := fun H ρ hA' =>
  H ρ (h ρ hA')

theorem closureObstructionInterface_of_closure_success_imp_of_right
    (h : ∀ Cl : Set World → Set World, A.closure_success Cl → A'.closure_success Cl) :
    ClosureObstructionInterface A' → ClosureObstructionInterface A := fun H' Cl hA =>
  H' Cl (h Cl hA)

theorem closureObstructionInterface_of_closure_success_imp_of_left
    (h : ∀ Cl : Set World → Set World, A'.closure_success Cl → A.closure_success Cl) :
    ClosureObstructionInterface A → ClosureObstructionInterface A' := fun H Cl hA' =>
  H Cl (h Cl hA')

theorem semanticCertificationInterface_of_cert_success_imp_of_right
    (h : ∀ τ : Claim → Bool, A.cert_success τ → A'.cert_success τ) :
    SemanticCertificationInterface A' → SemanticCertificationInterface A := fun H' τ hA =>
  H' τ (h τ hA)

theorem semanticCertificationInterface_of_cert_success_imp_of_left
    (h : ∀ τ : Claim → Bool, A'.cert_success τ → A.cert_success τ) :
    SemanticCertificationInterface A → SemanticCertificationInterface A' := fun H τ hA' =>
  H τ (h τ hA')

/--
From a barrier pack on **`A'`**, build one on **`A`** when every success on **`A`** is already a success on **`A'`** (same pattern
as **`diagonalRepresentationalInterface_of_repr_success_imp_of_right`** componentwise).
-/
def u123BarrierData_pull_of_succImp_to_right
    (hρ : ∀ ρ, A.repr_success ρ → A'.repr_success ρ)
    (hCl : ∀ Cl, A.closure_success Cl → A'.closure_success Cl)
    (hτ : ∀ τ, A.cert_success τ → A'.cert_success τ)
    (b' : U123BarrierData A') : U123BarrierData A where
  reprBarrier := fun ρ hA => b'.reprBarrier ρ (hρ ρ hA)
  closureBarrier := fun Cl hClA => b'.closureBarrier Cl (hCl Cl hClA)
  certBarrier := fun τ hτA => b'.certBarrier τ (hτ τ hτA)

/--
Dual: push a pack from **`A`** to **`A'`** along **`A'.success ⇒ A.success`**.
-/
def u123BarrierData_push_of_succImp_to_left
    (hρ : ∀ ρ, A'.repr_success ρ → A.repr_success ρ)
    (hCl : ∀ Cl, A'.closure_success Cl → A.closure_success Cl)
    (hτ : ∀ τ, A'.cert_success τ → A.cert_success τ)
    (b : U123BarrierData A) : U123BarrierData A' where
  reprBarrier := fun ρ hA' => b.reprBarrier ρ (hρ ρ hA')
  closureBarrier := fun Cl hClA' => b.closureBarrier Cl (hCl Cl hClA')
  certBarrier := fun τ hτA' => b.certBarrier τ (hτ τ hτA')

theorem nonempty_u123BarrierData_pull_of_succImp_to_right
    (hρ : ∀ ρ, A.repr_success ρ → A'.repr_success ρ)
    (hCl : ∀ Cl, A.closure_success Cl → A'.closure_success Cl)
    (hτ : ∀ τ, A.cert_success τ → A'.cert_success τ) :
    Nonempty (U123BarrierData A') → Nonempty (U123BarrierData A) := fun ⟨b'⟩ =>
  ⟨u123BarrierData_pull_of_succImp_to_right hρ hCl hτ b'⟩

theorem nonempty_u123BarrierData_push_of_succImp_to_left
    (hρ : ∀ ρ, A'.repr_success ρ → A.repr_success ρ)
    (hCl : ∀ Cl, A'.closure_success Cl → A.closure_success Cl)
    (hτ : ∀ τ, A'.cert_success τ → A.cert_success τ) :
    Nonempty (U123BarrierData A) → Nonempty (U123BarrierData A') := fun ⟨b⟩ =>
  ⟨u123BarrierData_push_of_succImp_to_left hρ hCl hτ b⟩

end D3_success_field_morphism

end StructuredNonexhaustibility
