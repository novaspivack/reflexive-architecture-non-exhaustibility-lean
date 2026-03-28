import ReflexiveArchitectureNonexhaustibility.Basic

/-!
# Residual dynamics — **SPEC_023_RG1** / **EPIC_015** phase **P0**

Abstract scaffolding for a **dynamical** layer on top of the static barrier/residual science:

* **Observational refinement** as an inclusion between identification relations (coarser = more pairs lumped).
* **Regime** as a snapshot of **`ReflexiveArchitecture`** data (carriers fixed; regulator predicates may change).
* A disjoint sum **`ResidualResponseStep`** tagging either refinement or regulatory reconfiguration.

**Scope:** definitions + elementary implications only. **D0** (persistence under non-resolving refinement),
**D1** (response dichotomy), and **D2** (fold / regime shift) are **not** proved here—see **SPEC_023_RG1**.

**Anti-smuggling:** no axiom that every residual forces a nontrivial step; no identification of "self-improvement"
with this data.
-/

namespace StructuredNonexhaustibility

/-! ## Identification and refinement (generic carrier) -/

variable {α : Type _}

/-- `x` and `y` are identified at the current observation level (same fiber / quotient class). -/
abbrev Identification (α : Type _) :=
  α → α → Prop

/--
**Refinement** step: the **fine** relation is **subsumed** by the **coarse** one (`fine ⊆ coarse` as proofs).

So any pair identified after refinement was already identified coarsely; new distinctions may appear, but the
step cannot **create** new identifications without them holding coarsely.
-/
def IsRefinementStep (coarse fine : Identification α) : Prop :=
  ∀ x y, fine x y → coarse x y

/--
A pair is **split** by moving from `coarse` to `fine`: lumped coarsely, distinguished finely.
-/
def PairSplitByRefinement (coarse fine : Identification α) (x y : α) : Prop :=
  coarse x y ∧ ¬ fine x y

variable {coarse fine : Identification α}

theorem fine_subsumes_coarse_rw (h : IsRefinementStep coarse fine) {x y : α} (hxy : fine x y) :
    coarse x y :=
  h x y hxy

theorem not_fine_of_not_coarse (h : IsRefinementStep coarse fine) {x y : α} (hc : ¬ coarse x y) :
    ¬ fine x y :=
  fun hf => hc (h x y hf)

/-! ## Regime snapshots and response tagging -/

/--
A **regulatory regime** snapshot: the success predicates carried by **`ReflexiveArchitecture`** at one moment.

**SPEC_023_RG1** uses "regime shift" for passage between distinguishable snapshots on the *same* carrier tuple.
-/
structure RegimeSnapshot (World Obs Repr Claim : Type) where
  arch : ReflexiveArchitecture World Obs Repr Claim

/--
Distinct snapshots (purely **extensional** inequality on the architecture record).
-/
def RegimeSnapshotsDiffer {World Obs Repr Claim : Type} (s t : RegimeSnapshot World Obs Repr Claim) : Prop :=
  s.arch ≠ t.arch

/--
A single **residual response** step at the P0 level: either tighten an identification relation (abstract refinement)
or replace the regulatory snapshot (reconfiguration).

Downstream (**D1**/**D2**) will supply obligations tying these steps to **ResidualWitness** / barrier data / fold
obstruction—without collapsing "response" to a theorem here.
-/
inductive ResidualResponseStep (α World Obs Repr Claim : Type) : Type
  | refinement (coarse fine : Identification α) (h : IsRefinementStep coarse fine) :
      ResidualResponseStep α World Obs Repr Claim
  | reconfiguration (before after : RegimeSnapshot World Obs Repr Claim) :
      ResidualResponseStep α World Obs Repr Claim

namespace ResidualResponseStep

variable {α World Obs Repr Claim : Type}

/-- A step used **observational** refinement rather than regulatory change. -/
def isRefinement (step : ResidualResponseStep α World Obs Repr Claim) : Bool :=
  match step with
  | refinement _ _ _ => true
  | reconfiguration _ _ => false

/-- True iff the step is a **reconfiguration** of **`RegimeSnapshot`**. -/
def isReconfiguration (step : ResidualResponseStep α World Obs Repr Claim) : Bool :=
  match step with
  | refinement _ _ _ => false
  | reconfiguration _ _ => true

theorem refinement_reconfiguration_disjoint (step : ResidualResponseStep α World Obs Repr Claim)
    (hr : isRefinement step = true) (hrc : isReconfiguration step = true) :
    False := by
  cases step with
  | refinement _ _ _ =>
      simp [isRefinement, isReconfiguration] at hr hrc
  | reconfiguration _ _ =>
      simp [isRefinement, isReconfiguration] at hr hrc

end ResidualResponseStep

/-! ## Standing burden (pure `Prop` parameter — **D0** hook) -/

/--
**P0 hook for D0:** `P` names an obligation that counts as **standing residual burden** in a dynamical episode.

Later lemmas (**IC** / kernel formalism in **SPEC_013_IC1**) show how to **instantiate** `P` from non-resolving
refinement without defining `P` to be "whatever makes the theorem true."
-/
abbrev StandingResidualBurden (P : Prop) : Prop := P

end StructuredNonexhaustibility
