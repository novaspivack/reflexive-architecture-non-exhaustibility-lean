import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.Attempt
import ReflexiveArchitectureNonexhaustibility.AbstractModeCover.D002ResidualWitnessTarget
import ReflexiveArchitectureNonexhaustibility.Basic
import ReflexiveArchitectureNonexhaustibility.Residuals

/-!
# Residual dynamics — **SPEC_023_RG1** / **EPIC_015** phase **P0**

Abstract scaffolding for a **dynamical** layer on top of the static barrier/residual science:

* **Observational refinement** as an inclusion between identification relations (coarser = more pairs lumped).
* **Regime** as a snapshot of **`ReflexiveArchitecture`** data (carriers fixed; regulator predicates may change).
* A disjoint sum **`ResidualResponseStep`** tagging either refinement or regulatory reconfiguration.

**Scope:** **P0–D3** notes + **D2** **iterate scaffold** + **fold / obstruction packaging** + **iterate-backed** bundles
(**`IterateBackedReflexiveArchitecture`**, **`OpaqueAttemptClosureIterateBacking`**) where adequacy is **packaged**, not proved from thin air;
**joint** forgetful **R₂** + barrier-linked **R₄** coexistence; imports **`Attempt`**, **`D002ResidualWitnessTarget`** for those bridges.
**Promotion:** **`standingResidualBurden_enriched_obstruction_sig`** (**σ**). **D3** field-**iff** transport lives in **`Interfaces.lean`**.
Forgetful kernel: **SPEC_013_IC1** (**`InfinityCompression`**, **`ICKernel`**).

**Anti-smuggling:** no axiom that every residual forces a nontrivial step; no identification of "self-improvement"
with this data.

**D3 bridge note:** **`standingResidualBurden_promotion_bridge_irrelevant`** lives in **`ResidualEnrichment/Promotion.lean`**
(imports this file) so **`PayloadPromotion`** can cite **`StandingResidualBurden`** without a module cycle.
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

/--
**Definitional unfolding:** dynamics-layer naming is **synonymous** with the underlying **`Prop`**.
-/
theorem standingResidualBurden_iff (P : Prop) : StandingResidualBurden P ↔ P :=
  Iff.rfl

/--
**D3 transport (generic):** any implication **`P → Q`** sends **`StandingResidualBurden P`** to **`StandingResidualBurden Q`**.

Use after **`d3_adequacy_aftermath_standing_burden`** to **weaken** or **repackage** the aftermath conjunction
(along lemmas such as **`And.left`** / **`And.right`**, or future morphism lemmas) **without** claiming burden
vanishes—it is only **relocated** in propositional content.
-/
theorem standingResidualBurden_of_imp {P Q : Prop} (h : P → Q) (hp : StandingResidualBurden P) :
    StandingResidualBurden Q :=
  h hp

/--
Conjunction of two standing burdens (**independent** episodes composed).
-/
theorem standingResidualBurden_and {P Q : Prop} (hp : StandingResidualBurden P) (hq : StandingResidualBurden Q) :
    StandingResidualBurden (P ∧ Q) :=
  And.intro hp hq

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
**Strong D1 (regulatory):** a reconfiguration counts as a **proper regime change** when regulators differ.
-/
abbrev IsProperRegimeChange {World Obs Repr Claim : Type} (before after : RegimeSnapshot World Obs Repr Claim) :
    Prop :=
  RegimeSnapshotsDiffer before after

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

/-! ### D1 — tag-level response dichotomy (**SPEC_023_RG1** **P2** seed)

Every **`ResidualResponseStep`** is **either** an observational refinement (carrying **`IsRefinementStep`** data)
**or** a regulatory reconfiguration (carrying two **`RegimeSnapshot`**s). This is the disjoint-sum reading of
“refine **or** reconfigure”; it does **not** yet quantify “preserve vs discharge” residual obligations (**stronger D1**).
-/

/--
**D1 (exhaustive).** Intuitionistic `'or'` from the two constructors—no **LEM** on composite dynamics.
-/
theorem d1_response_step_exhaustive (step : ResidualResponseStep α World Obs Repr Claim) :
    (∃ coarse fine h, step = refinement coarse fine h) ∨
      ∃ before after, step = reconfiguration before after := by
  cases step with
  | refinement coarse fine h => exact Or.inl ⟨coarse, fine, h, rfl⟩
  | reconfiguration before after => exact Or.inr ⟨before, after, rfl⟩

/--
If the step is **not** tagged as refinement data, it **is** a **reconfiguration** (contrapositive routing).
-/
theorem d1_not_refinement_then_reconfiguration (step : ResidualResponseStep α World Obs Repr Claim)
    (h : ¬∃ coarse fine hstep, step = refinement coarse fine hstep) :
    ∃ before after, step = reconfiguration before after := by
  cases step with
  | refinement coarse fine hstep => exact False.elim (h ⟨coarse, fine, hstep, rfl⟩)
  | reconfiguration before after => exact ⟨before, after, rfl⟩

/--
**`Bool` guard** **`isRefinement`** ↔ **`∃`** refinement payload (**decidable** tag).
-/
theorem isRefinement_eq_true_iff (step : ResidualResponseStep α World Obs Repr Claim) :
    isRefinement step = true ↔ ∃ coarse fine h, step = refinement coarse fine h := by
  constructor
  · intro hs
    cases step with
    | refinement coarse fine h => exact ⟨coarse, fine, h, rfl⟩
    | reconfiguration _ _ => simp [isRefinement] at hs
  · rintro ⟨coarse, fine, h, rfl⟩
    rfl

/--
**`Bool` guard** **`isReconfiguration`** ↔ **`∃`** regime **before/after** pair.
-/
theorem isReconfiguration_eq_true_iff (step : ResidualResponseStep α World Obs Repr Claim) :
    isReconfiguration step = true ↔ ∃ before after, step = reconfiguration before after := by
  constructor
  · intro hs
    cases step with
    | refinement _ _ _ => simp [isReconfiguration] at hs
    | reconfiguration before after => exact ⟨before, after, rfl⟩
  · rintro ⟨before, after, rfl⟩
    rfl

/--
**Stronger D1 (classical on regulator equality).** Every step is **either**:

* observational refinement, **or**
* regulatory reconfiguration that **changes** **`RegimeSnapshot.arch`**, **or**
* regulatory reconfiguration that leaves **`arch`** **equal** (presentation-only / bookkeeping reconfiguration).

Discharged with the **`classical`** tactic (**LEM** on `before.arch = after.arch`) because **`ReflexiveArchitecture`**
carries no decidability instance. For **D2** / RFO, the middle disjunct is the **regime-shift** locus; the last disjunct
is explicitly **not** a proper regime change at the carrier level.
-/
theorem d1_response_step_classical_trilemma (step : ResidualResponseStep α World Obs Repr Claim) :
    (∃ coarse fine h, step = refinement coarse fine h) ∨
      (∃ before after, step = reconfiguration before after ∧ IsProperRegimeChange before after) ∨
      ∃ before after, step = reconfiguration before after ∧ before.arch = after.arch := by
  classical
  rcases d1_response_step_exhaustive step with href | hrec
  · exact Or.inl href
  · rcases hrec with ⟨before, after, rfl⟩
    by_cases heq : before.arch = after.arch
    · exact Or.inr (Or.inr ⟨before, after, rfl, heq⟩)
    · exact Or.inr (Or.inl ⟨before, after, rfl, heq⟩)

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

/-! ### **KernelWitness** → **`ResidualWitness`** (**SPEC_023_RG1** / **EPIC_009** hook)

Paper **C** residual point with **R₂** tag and carrier **`α × α`**: the distinguished pair is the witness **data**.
This is **not** barrier-linked **R₄** (still **`U123BarrierData`**); it **is** an honest, **admissible** (**negative class**)
typed residual for the same kernel geometry **IC** uses.
-/

/--
Package a **`KernelWitness`** as a **`ResidualWitness`** tagged **R₂**.

**Not** **R₄** / **`trivialR4ResidualWitness`**; enrichment to **R₄** payloads stays at **`ResidualEnrichment`**
/ **D-002** with extra hypotheses. **Carrier discipline:** **`ResidualWitness.carrier : Type`** — when re-exporting through **`forgetfulKernel_*`**
lemmas, take **`α : Type`** (not an arbitrary **`Type u`**) so **`α × α`** fits the witness carrier slot.
-/
def residualWitness_of_kernelWitness {α : Type _} {K : α → α → Prop} (w : KernelWitness α K) : ResidualWitness :=
  ⟨ResidualClass.R2, α × α, (w.x, w.y)⟩

theorem isR2Residual_residualWitness_of_kernelWitness {α : Type _} {K : α → α → Prop} (w : KernelWitness α K) :
    IsR2Residual (residualWitness_of_kernelWitness w) :=
  rfl

theorem not_isR4Residual_residualWitness_of_kernelWitness {α : Type _} {K : α → α → Prop} (w : KernelWitness α K) :
    ¬ IsR4PositiveSurvivor (residualWitness_of_kernelWitness w) :=
  fun h4 => negative_not_r4 (residualWitness_of_kernelWitness w) (Or.inr (Or.inl rfl)) h4

theorem residualWitness_of_kernelWitness_ne_trivialR4 {α : Type _} {K : α → α → Prop} (w : KernelWitness α K) :
    residualWitness_of_kernelWitness w ≠ trivialR4ResidualWitness := by
  intro he
  have h4 : IsR4PositiveSurvivor (residualWitness_of_kernelWitness w) := by
    rw [he]
    exact isR4_trivialR4
  exact not_isR4Residual_residualWitness_of_kernelWitness w h4

theorem isNegativeResidualClass_residualWitness_of_kernelWitness {α : Type _} {K : α → α → Prop}
    (w : KernelWitness α K) : IsNegativeResidualClass (residualWitness_of_kernelWitness w) :=
  Or.inr (Or.inl rfl)

theorem admissibleResidual_residualWitness_of_kernelWitness {α : Type _} {K : α → α → Prop}
    (w : KernelWitness α K) : AdmissibleResidual (residualWitness_of_kernelWitness w) :=
  admissible_of_negativeClass (isNegativeResidualClass_residualWitness_of_kernelWitness w)

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
**Definitional link:** forgetful **`kernelWitness_of_map`** then **`residualWitness_of_kernelWitness`** is the explicit **R₂**
pair on **`α × α`**.
-/
theorem residualWitness_kernelWitness_of_map_eq {α β : Type} {f : α → β} {x y : α} (hf : f x = f y) (hne : x ≠ y) :
    residualWitness_of_kernelWitness (kernelWitness_of_map hf hne) =
      ⟨ResidualClass.R2, α × α, (x, y)⟩ :=
  rfl

/--
Conjunction of **R₂** / admissibility / nontriviality for **`residualWitness_of_kernelWitness w`** (**forgetful** chain).

Split out so **`Exists.intro`** elaborates without **`⟨·,·,·,·⟩`** parsing pitfalls.

**Universe:** **`α β : Type`** aligns with **`ResidualWitness.carrier : Type`** (Paper **C** witness carrier discipline).
-/
theorem forgetfulKernel_residual_r2_admissible_nontrivial_props {α β : Type} {f : α → β}
    (w : KernelWitness α (KernelOfMap f)) :
    IsR2Residual (residualWitness_of_kernelWitness w) ∧
      AdmissibleResidual (residualWitness_of_kernelWitness w) ∧
      residualWitness_of_kernelWitness w ≠ trivialR4ResidualWitness :=
  And.intro (isR2Residual_residualWitness_of_kernelWitness w)
    (And.intro (admissibleResidual_residualWitness_of_kernelWitness w)
      (residualWitness_of_kernelWitness_ne_trivialR4 w))

/--
**D0 → Paper C calculus (forgetful core):** nontrivial equal-image **`f x = f y`**, **`x ≠ y`** ⇒ some **admissible** **R₂**
**`ResidualWitness`** incompatible with **`trivialR4ResidualWitness`**.

This is the **IC-style** fiber collision packaged for **`Residuals.lean`** consumers **without** claiming barrier-linked **R₄**.
-/
theorem d0_forgetfulKernel_obtains_admissible_r2_residual {α β : Type} {f : α → β} {x y : α} (hf : f x = f y)
    (hne : x ≠ y) :
    ∃ rw : ResidualWitness,
      IsR2Residual rw ∧ AdmissibleResidual rw ∧ rw ≠ trivialR4ResidualWitness :=
  Exists.intro (residualWitness_of_kernelWitness (kernelWitness_of_map hf hne))
    (forgetfulKernel_residual_r2_admissible_nontrivial_props (kernelWitness_of_map hf hne))

/--
**D0 / dynamics hook:** same as **`d0_forgetfulKernel_obtains_admissible_r2_residual`** under **`StandingResidualBurden`** (**`≡`** **`Prop`** identity).
-/
theorem standingResidualBurden_forgetfulKernel_exists_admissible_r2 {α β : Type} {f : α → β} {x y : α} (hf : f x = f y)
    (hne : x ≠ y) :
    StandingResidualBurden
      (∃ rw : ResidualWitness, IsR2Residual rw ∧ AdmissibleResidual rw ∧ rw ≠ trivialR4ResidualWitness) :=
  d0_forgetfulKernel_obtains_admissible_r2_residual hf hne

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

/-! ### Forgetful **kernel** + **U₁–U₃** (**joint** certificates — not an **R₂ → R₄** promotion)

**SPEC_023_RG1 / EPIC_015:** an **IC-style** fiber collision yields an **honest** **R₂** **`ResidualWitness`**
(**`residualWitness_of_kernelWitness`** chain). **Independently**, **`U123BarrierData`** fixes the **D-002**
**`barrierLinkedR4ResidualWitness`**. This lemma **coexistence** packages **both** when hypotheses are **simultaneously**
available — **not** a claim that **`KernelWitness`** *becomes* barrier-linked **R₄** without **extra** typing identification.
-/

variable {World Obs Repr Claim : Type} {A : ReflexiveArchitecture World Obs Repr Claim}

/--
**Joint existence:** forgetful **R₂** certificate + the **canonical** barrier-linked **R₄** witness from **`b`**.
-/
theorem exists_admissible_r2_and_barrier_linked_r4_joint {α β : Type} {f : α → β} {x y : α} (hf : f x = f y)
    (hne : x ≠ y) (b : U123BarrierData A) :
    ∃ r2 r4 : ResidualWitness,
      IsR2Residual r2 ∧
        AdmissibleResidual r2 ∧
          r2 ≠ trivialR4ResidualWitness ∧
            IsR4PositiveSurvivor r4 ∧
              AdmissibleResidual r4 ∧
                r4 = barrierLinkedR4ResidualWitness b.reprBarrier b.closureBarrier b.certBarrier := by
  refine
    Exists.intro (residualWitness_of_kernelWitness (kernelWitness_of_map hf hne))
      (Exists.intro (barrierLinkedR4ResidualWitness b.reprBarrier b.closureBarrier b.certBarrier) ?_)
  refine And.intro (isR2Residual_residualWitness_of_kernelWitness _) ?_
  refine And.intro (admissibleResidual_residualWitness_of_kernelWitness _) ?_
  refine And.intro (residualWitness_of_kernelWitness_ne_trivialR4 _) ?_
  refine And.intro (isR4_barrierLinkedR4ResidualWitness _ _ _) ?_
  refine And.intro (admissible_barrierLinkedR4ResidualWitness _ _ _) ?_
  rfl

/--
**Same** content under **`StandingResidualBurden`** (**synonymous** with the existential **`Prop`**).
-/
theorem standingResidualBurden_joint_forgetful_r2_and_barrier_r4 {α β : Type} {f : α → β} {x y : α} (hf : f x = f y)
    (hne : x ≠ y) (b : U123BarrierData A) :
    StandingResidualBurden
      (∃ r2 r4 : ResidualWitness,
        IsR2Residual r2 ∧
          AdmissibleResidual r2 ∧
            r2 ≠ trivialR4ResidualWitness ∧
              IsR4PositiveSurvivor r4 ∧
                AdmissibleResidual r4 ∧
                  r4 =
                    barrierLinkedR4ResidualWitness b.reprBarrier b.closureBarrier b.certBarrier) :=
  exists_admissible_r2_and_barrier_linked_r4_joint hf hne b

/-! ## D2 — internal closure iteration scaffold (**SPEC_023_RG1** **P3**)

Aligns with the **RFO** column (**`Set World → Set World`** candidates in **`ClosureObstructionInterface`** / **`FromRFO.lean`**).
**Iteration** semantics stay **parametric** in **`Cl`**; the **fold** subsection adds **`ClosureIterateSoundness`** /
**`ClosureIterateAdequacy`** hypotheses (**sound** link from **`closure_success`** to **`InClosureIterateImage`**)—not a definitional identification.

Anti-smuggling: **`closureIterate`** does **not** read **`closure_success`** except through those explicit hypotheses.
-/

variable {World : Type}

/--
**Iterative closure step** on **`Set World`** (same **functional** shape as closure candidates in **`Interfaces.lean`**).
-/
abbrev ClosureOperator (World : Type) :=
  Set World → Set World

/--
**`n`-fold** iteration: **`0` ⇒** identity on **`S`**; **`Nat.succ n` ⇒** apply **`Cl`** after the **`n`**-fold result.
-/
def closureIterate (Cl : ClosureOperator World) : Nat → Set World → Set World :=
  Nat.rec (motive := fun _ => Set World → Set World) (fun S => S) fun _ rec S => Cl (rec S)

@[simp]
theorem closureIterate_zero (Cl : ClosureOperator World) (S : Set World) :
    closureIterate Cl 0 S = S :=
  rfl

@[simp]
theorem closureIterate_succ (Cl : ClosureOperator World) (n : Nat) (S : Set World) :
    closureIterate Cl (Nat.succ n) S = Cl (closureIterate Cl n S) :=
  rfl

theorem closureIterate_one (Cl : ClosureOperator World) (S : Set World) :
    closureIterate Cl 1 S = Cl S :=
  rfl

/--
Some iterate of **`Cl`** from **`S₀`** equals **`B`** (**`∃ n`**).
-/
def InClosureIterateImage (Cl : ClosureOperator World) (S₀ B : Set World) : Prop :=
  ∃ n, closureIterate Cl n S₀ = B

/--
**Semigroup law** for iteration: **`(n + m)`** steps from **`S`** = **`n`** steps from the **`m`**-fold partial image.

**D2** fodder: “reachable in **`r + s`** steps” factors through an intermediate **`m`**-fold set—without yet identifying **`m`**
with an honest architectural timeline.
-/
theorem closureIterate_add (Cl : ClosureOperator World) (n m : Nat) (S : Set World) :
    closureIterate Cl (n + m) S = closureIterate Cl n (closureIterate Cl m S) := by
  induction n with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ k ih =>
    rw [Nat.succ_add, closureIterate_succ, ih, closureIterate_succ]

/--
**Transitivity** of **`InClosureIterateImage`** along the **same** closure operator: **`S₀ ↝ B`** and **`B ↝ C`** ⇒ **`S₀ ↝ C`**.
-/
theorem inClosureIterateImage_trans {Cl : ClosureOperator World} {S₀ B C : Set World}
    (h₁ : InClosureIterateImage Cl S₀ B) (h₂ : InClosureIterateImage Cl B C) :
    InClosureIterateImage Cl S₀ C := by
  rcases h₁ with ⟨n, hn⟩
  rcases h₂ with ⟨m, hm⟩
  refine ⟨m + n, ?_⟩
  rw [closureIterate_add, hn, hm]

/--
**No** iterate lands on **`B`** (**non-reach** in the **internal** iterate sense for this **`Cl`** / **`S₀`**).
-/
def OutsideClosureIterateImage (Cl : ClosureOperator World) (S₀ B : Set World) : Prop :=
  ∀ n, closureIterate Cl n S₀ ≠ B

theorem outsideClosureIterate_of_not_in_iterate {Cl : ClosureOperator World} {S₀ B : Set World}
    (h : ¬InClosureIterateImage Cl S₀ B) : OutsideClosureIterateImage Cl S₀ B :=
  fun _ heq => h ⟨_, heq⟩

theorem not_in_iterate_of_outside {Cl : ClosureOperator World} {S₀ B : Set World}
    (h : OutsideClosureIterateImage Cl S₀ B) : ¬InClosureIterateImage Cl S₀ B
  | ⟨_, heq⟩ => h _ heq

theorem outsideClosureIterate_iff_not_in_iterate (Cl : ClosureOperator World) (S₀ B : Set World) :
    OutsideClosureIterateImage Cl S₀ B ↔ ¬InClosureIterateImage Cl S₀ B :=
  Iff.intro not_in_iterate_of_outside outsideClosureIterate_of_not_in_iterate

/-! ### D2 — fold / RFO column (**explicit** iterate–success link)

**Anti-smuggling:** we do **not** identify **`closure_success`** with **`InClosureIterateImage`** by definition. The abbreviations
below are named **hypotheses** a regime may assume or prove under further domain science; from them, **outside-iterate**
geometry refutes success—and **universal** outside combines with **adequacy** to yield **`ClosureObstructionInterface`**
(alternate route to the RFO column of **U₁–U₃**).
-/

variable {Obs : ObsTy} {Repr : ReprTy} {Claim : ClaimTy}

/--
**Per-closure** soundness: if **`closure_success Cl`** holds, the **internal** iterate semantics reaches **`B`** from **`S₀`**.
-/
abbrev ClosureIterateSoundness (A : ReflexiveArchitecture World Obs Repr Claim) (S₀ B : Set World)
    (Cl : ClosureOperator World) : Prop :=
  A.closure_success Cl → InClosureIterateImage Cl S₀ B

/--
**Regime-wide** iterate adequacy: **every** successful closure candidate is **internally** reachable (**`∃ n`**) from **`S₀`** to **`B`**.
-/
abbrev ClosureIterateAdequacy (A : ReflexiveArchitecture World Obs Repr Claim) (S₀ B : Set World) : Prop :=
  ∀ Cl : ClosureOperator World, ClosureIterateSoundness A S₀ B Cl

/--
**Fold obstruction (pointwise):** outside **internal** reachability contradicts **`closure_success`** once iterate soundness is assumed.
-/
theorem not_closure_success_of_outside_iterate {A : ReflexiveArchitecture World Obs Repr Claim} {S₀ B : Set World}
    {Cl : ClosureOperator World} (hout : OutsideClosureIterateImage Cl S₀ B)
    (hsound : ClosureIterateSoundness A S₀ B Cl) : ¬ A.closure_success Cl := fun hsucc =>
  not_in_iterate_of_outside hout (hsound hsucc)

/--
Variant with a **universal** adequacy hypothesis packaged in **`ClosureIterateAdequacy`**.
-/
theorem not_closure_success_of_outside_iterate_of_adequacy {A : ReflexiveArchitecture World Obs Repr Claim}
    {S₀ B : Set World} {Cl : ClosureOperator World} (hout : OutsideClosureIterateImage Cl S₀ B)
    (had : ClosureIterateAdequacy A S₀ B) : ¬ A.closure_success Cl :=
  not_closure_success_of_outside_iterate hout (had Cl)

/--
**Global RFO barrier** from **iterate geometry:** if **every** closure operator fails **internal** reachability to **`B`**, and
success **would** imply reachability, then **`ClosureObstructionInterface`** holds.
-/
theorem closure_obstruction_of_iterate_adequacy_and_universal_outside
    {A : ReflexiveArchitecture World Obs Repr Claim} {S₀ B : Set World} (had : ClosureIterateAdequacy A S₀ B)
    (hout : ∀ Cl : ClosureOperator World, OutsideClosureIterateImage Cl S₀ B) : ClosureObstructionInterface A :=
  fun Cl hsucc => not_in_iterate_of_outside (hout Cl) (had Cl hsucc)

/-! ### D2 — iterate-backed regime (**intrinsic `ClosureIterateAdequacy` relative to packaging**)

There is **no** theorem **`∀ A, ClosureIterateAdequacy A S₀ B`** from **`ReflexiveArchitecture` alone**: **`closure_success`**
is an abstract **SPEC_002_AM1** slot. What *is* **intrinsic** is: **given** a record bundling **`arch`** with **`closureSeed`**
/ **`closureTarget`** and **`closure_iterate_sound`**, **`ClosureIterateAdequacy arch …`** is **definitionally** the soundness field.

Engines that **commit** to iterate-reachability semantics publish such a bundle; **opaque** attempts admit the same pattern.
-/

/--
**Iterate-backed** architecture: **explicit** witness that **`closure_success`** is **sound** for **`InClosureIterateImage`**
from **`closureSeed`** to **`closureTarget`**.
-/
structure IterateBackedReflexiveArchitecture (World Obs Repr Claim : Type) where
  arch : ReflexiveArchitecture World Obs Repr Claim
  closureSeed : Set World
  closureTarget : Set World
  closure_iterate_sound :
    ∀ Cl : ClosureOperator World, arch.closure_success Cl → InClosureIterateImage Cl closureSeed closureTarget

/--
**Definitional** extraction: bundled soundness **is** adequacy for **`arch`**.
-/
theorem closureIterateAdequacy_iterateBacked (Ib : IterateBackedReflexiveArchitecture World Obs Repr Claim) :
    ClosureIterateAdequacy Ib.arch Ib.closureSeed Ib.closureTarget :=
  Ib.closure_iterate_sound

/--
**RFO** obstruction from a **backed** architecture + **universal** outside-iterate **geometry** on its packaged seed/target.
-/
theorem closure_obstruction_of_iterateBacked_and_universal_outside
    (Ib : IterateBackedReflexiveArchitecture World Obs Repr Claim)
    (hout : ∀ Cl : ClosureOperator World, OutsideClosureIterateImage Cl Ib.closureSeed Ib.closureTarget) :
    ClosureObstructionInterface Ib.arch :=
  closure_obstruction_of_iterate_adequacy_and_universal_outside (closureIterateAdequacy_iterateBacked Ib) hout

/--
**Opaque** attempt + the same **iterate-soundness** commitment (**carrier** / nominations irrelevant to this judgment).
-/
structure OpaqueAttemptClosureIterateBacking (World Obs Repr Claim : Type) where
  attempt : OpaqueTotalizationAttempt World Obs Repr Claim
  closureSeed : Set World
  closureTarget : Set World
  closure_iterate_sound :
    ∀ Cl : ClosureOperator World, attempt.arch.closure_success Cl → InClosureIterateImage Cl closureSeed closureTarget

theorem closureIterateAdequacy_opaqueAttemptClosureIterate
    (B : OpaqueAttemptClosureIterateBacking World Obs Repr Claim) :
    ClosureIterateAdequacy B.attempt.arch B.closureSeed B.closureTarget :=
  B.closure_iterate_sound

theorem closure_obstruction_of_opaqueAttemptIterateBacking_and_universal_outside
    (B : OpaqueAttemptClosureIterateBacking World Obs Repr Claim)
    (hout : ∀ Cl : ClosureOperator World, OutsideClosureIterateImage Cl B.closureSeed B.closureTarget) :
    ClosureObstructionInterface B.attempt.arch :=
  closure_obstruction_of_iterate_adequacy_and_universal_outside (closureIterateAdequacy_opaqueAttemptClosureIterate B) hout

end StructuredNonexhaustibility
