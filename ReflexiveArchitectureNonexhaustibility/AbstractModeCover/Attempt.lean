import ReflexiveArchitectureNonexhaustibility.Basic

/-!
# Abstract mode cover — opaque attempts (**SPEC_015_KM2**, **Attempt**)

An **opaque** internal totalization attempt fixes an architecture and a **parameter space**
(`carrier`) with an **anchor** `carrier`. At every parameter it nominates concrete gadgets for
the three canonical mechanism *shapes* (representation map, closure operator, Boolean certifier).

**Non-smuggling discipline:** there is **no** inductive tag selecting which mode applies. Mode
is recovered only via **`Profiles` predicates** (whether `arch.repr_success` / `closure_success` /
`cert_success` hold for the nominations at `anchor`, and **R₄** structure for residual).

Dummy nominations for off-axes construction paths are **parameters** (`dummyρ`, `dummyCl`, `dummyτ`)
so we avoid choice axioms for inhabitation.
-/

namespace StructuredNonexhaustibility

variable {World Obs Repr Claim : Type}

/--
Opaque internal totalization attempt relative to a fixed reflexive architecture.

The data is **not** a sum type of modes: profiles are defined separately as propositions.
-/
structure OpaqueTotalizationAttempt (World Obs Repr Claim : Type) where
  arch : ReflexiveArchitecture World Obs Repr Claim
  /-- Parameter space (internal states, bookkeeping, …). -/
  carrier : Type
  anchor : carrier
  reprAt : carrier → World → Repr
  closureAt : carrier → Set World → Set World
  certAt : carrier → Claim → Bool

/--
Minimal “genuine / admissible carrier” condition: the anchor is inhabited in a nonempty carrier.

**Refinement:** replace with **SPEC_012_AA1** / adequacy layered conditions; must **not** assert
mediation trichotomy or four-way cover by fiat.
-/
def GenuineInternalTotalizationAttempt (a : OpaqueTotalizationAttempt World Obs Repr Claim) : Prop :=
  Nonempty a.carrier

theorem genuine_of_nonempty (a : OpaqueTotalizationAttempt World Obs Repr Claim) :
    Nonempty a.carrier → GenuineInternalTotalizationAttempt a :=
  fun h => h

end StructuredNonexhaustibility
