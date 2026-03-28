import Mathlib.Data.Set.Defs

/-!
# Basic — reflexive architecture carrier (**SPEC_002_AM1**)

`repr_success`, `closure_success`, and `cert_success` are **per-architecture** notions of
when a proposed internal totalization would count as *objectively* successful.
No global “failure” is baked in: engines **instantiate** these predicates and prove
interface lemmas such as `∀ ρ, ¬ repr_success ρ` under diagonal hypotheses.
-/

namespace StructuredNonexhaustibility

abbrev ObsTy := Type
abbrev ReprTy := Type
abbrev ClaimTy := Type

/--
Core reflexive architecture: world + observation + abstract success predicates for
the three canonical exhaustion modes.
-/
structure ReflexiveArchitecture (World : Type) (Obs : ObsTy) (Repr : ReprTy) (Claim : ClaimTy)
    where
  observe : World → Obs
  /-- When does ρ count as representational exhaustion succeeding? -/
  repr_success : (World → Repr) → Prop
  /-- When does a closure operator count as exhaustive for architectural moves? -/
  closure_success : (Set World → Set World) → Prop
  /-- When does a Boolean classifier count as certifying all relevant claims? -/
  cert_success : (Claim → Bool) → Prop

end StructuredNonexhaustibility
