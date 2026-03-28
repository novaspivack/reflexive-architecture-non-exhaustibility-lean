import ReflexiveArchitectureNonexhaustibility.Basic

/-!
# Residual dynamics — **SPEC_023_RG1** / **EPIC_015** phase **P0**

Abstract scaffolding for a **dynamical** layer on top of the static barrier/residual science:

* **Observational refinement** as an inclusion between identification relations (coarser = more pairs lumped).
* **Regime** as a snapshot of **`ReflexiveArchitecture`** data (carriers fixed; regulator predicates may change).
* A disjoint sum **`ResidualResponseStep`** tagging either refinement or regulatory reconfiguration.

**Scope:** **P0** scaffolding plus a **relational D0 seed** (**kernel witness** + **non-resolving** refinement:
still `fine`-identified ⇒ **not** separated by the step). **D1** (response dichotomy), **D2** (fold / regime shift),
and **D3** (adequacy relocation) are **not** proved here—see **SPEC_023_RG1**. Instantiating **`KernelWitness`**
from **IC** fibers / forgetful maps is **SPEC_013_IC1**.

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

/--
**P0 / D0 hook:** `P` names an obligation that counts as **standing residual burden** in a dynamical episode.

Instantiations from **IC** / kernel formalism: **SPEC_013_IC1**; lemmas below use this alias for readability.
-/
abbrev StandingResidualBurden (P : Prop) : Prop := P

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
      simp [isReconfiguration] at hrc
  | reconfiguration _ _ =>
      simp [isRefinement] at hr

end ResidualResponseStep

/-! ## D0 — kernel witness / non-resolving refinement (**SPEC_023_RG1** **P1** relational seed)

An abstract **kernel** predicate `K` tags pairs “in the same formal fiber” (IC: preimage of a forgetful map).
A **refinement** step **separates** such a witness iff it **splits** the pair between `coarse` and `fine`.

The lemmas below are **purely relational**: they do not import Infinity Compression. They still capture the
hinge implication *non-resolving refinement does not eliminate the witness’s failure to become separated*.
-/

/--
Distinct points `x,y` tagged by the kernel predicate **K**.

Downstream (**SPEC_013_IC1**): take `K x y := f x = f y` for a forgetful `f`, or the IC remainder kernel.
-/
structure KernelWitness (α : Type _) (K : α → α → Prop) where
  x : α
  y : α
  kem : K x y
  ne : x ≠ y

/--
This witness is **separated** by `(coarse,fine)` iff the refinement exhibits a **split** on `(x,y)`.
-/
def WitnessSeparatedByRefinement {α : Type _} {K : α → α → Prop} (coarse fine : Identification α)
    (w : KernelWitness α K) : Prop :=
  PairSplitByRefinement coarse fine w.x w.y

/--
**D0 (relational core).** If `x` and `y` remain `fine`-identified after the step, the refinement **did not**
separate them—regardless of whether `IsRefinementStep` adds new distinctions elsewhere.

(`IsRefinementStep` is kept as a parameter so callers marking a **refinement episode** thread the same hypotheses
used in **`ResidualResponseStep.refinement`**.)
-/
theorem d0_witness_not_separated_of_still_fine {K : α → α → Prop} {w : KernelWitness α K}
    {coarse fine : Identification α} (_hstep : IsRefinementStep coarse fine) (hfine : fine w.x w.y) :
    ¬ WitnessSeparatedByRefinement coarse fine w :=
  fun hsplit => hsplit.2 hfine

/--
**D0 packaging (standing identification).** The proposition “this pair stays `fine`-identified” is a literal
**standing** burden in the dynamics hook sense.
-/
theorem d0_standing_fine_identification {K : α → α → Prop} {w : KernelWitness α K} {fine : Identification α}
    (hfine : fine w.x w.y) :
    StandingResidualBurden (fine w.x w.y) :=
  hfine

/--
**D0 + external separation goal.** If an independent obligation `Need` says the witness ought to be separated,
and the pair remains `fine`-identified, then the conjunction is **standing burden** (not discharged by the step).

`Need` is **not** defined here—avoiding definition smuggling. Typical use: `Need` comes from adequacy / barrier
certificates once linked at the enrichment layer.
-/
theorem d0_standing_unmet_need {K : α → α → Prop} {w : KernelWitness α K} {fine : Identification α} (Need : Prop)
    (hneed : Need) (hfine : fine w.x w.y) :
    StandingResidualBurden (Need ∧ fine w.x w.y) :=
  And.intro hneed hfine

/-! ## Forgetful-map kernel (**SPEC_013_IC1** geometric pattern)

The “geometry of what maps forget”: two points lie in the same **fiber** of `f` iff `f x = f y`.
This is the standard IC-style kernel before importing a sibling **infinity-compression** package.
-/

variable {α β : Type _}

/--
Kernel relation induced by a map `f : α → β` (**equal images ⇔ same formal fiber**).
-/
def KernelOfMap (f : α → β) : Identification α :=
  fun x y => f x = f y

/--
Build a **`KernelWitness`** from a **nontrivial** fiber coincidence (`f x = f y` but `x ≠ y`).
-/
def kernelWitness_of_map {f : α → β} {x y : α} (hf : f x = f y) (hne : x ≠ y) :
    KernelWitness α (KernelOfMap f) where
  x := x
  y := y
  kem := hf
  ne := hne

/--
**D0** for a forgetful kernel: still `fine`-identified ⇒ not separated — specialization of **`d0_witness_not_separated_of_still_fine`**.
-/
theorem d0_forgetfulKernel_notSeparated_of_still_fine {f : α → β} {x y : α} {coarse fine : Identification α}
    (hf : f x = f y) (hne : x ≠ y) (hstep : IsRefinementStep coarse fine) (hfine : fine x y) :
    ¬ WitnessSeparatedByRefinement coarse fine (kernelWitness_of_map hf hne) :=
  d0_witness_not_separated_of_still_fine (w := kernelWitness_of_map hf hne) hstep hfine

/--
Standing **fine** identification for a forgetful-kernel witness.
-/
theorem d0_forgetfulKernel_standing_fine {f : α → β} {x y : α} {fine : Identification α}
    (hf : f x = f y) (hne : x ≠ y) (hfine : fine x y) :
    StandingResidualBurden (fine x y) :=
  d0_standing_fine_identification (w := kernelWitness_of_map hf hne) hfine

end StructuredNonexhaustibility
