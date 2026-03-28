# reflexive-architecture-nonexhaustibility-lean — MANIFEST

**Toolchain:** `leanprover/lean4:v4.29.0-rc6` (see `lean-toolchain`).  
**Mathlib:** `v4.29.0-rc6` (see `lake-manifest.json` after `lake update`).

**Program focus (parent repo):** **Layer 1** Paper D nonexistence + **D-002 abstract** witness are proved. **EPIC_011** (**SPEC_016/017**): **`ResidualEnrichment`** + four bridges + **`mixedTriple`**. **EPIC_012** (**D-001**): **nems** pin **deferred** (private); **`lakefile`** has commented **`require`** + root **`README`** BIG NOTE. **EPIC_010** deferred. See parent [`QUEUE.md`](../QUEUE.md).

## `sorry` / `axiom` audit

| Item | Count | Notes |
|------|-------|-------|
| `sorry` | **0** | `rg 'sorry' --glob '*.lean'` |
| `axiom` | **0** | Summit targets are named `def … : Prop`, not postulated |

## Module map (namespace `StructuredNonexhaustibility`)

| File | Role |
|------|------|
| `EngineDependencyPinning.lean` | **D-001:** stub (**nems** private); enable **`NemS.Prelude`** when **`require`** uncommented — **`SPEC_018_PN1`** |
| `Basic.lean` | `ReflexiveArchitecture` + per-architecture success predicates |
| `Modes.lean` | `Mode*i*Success` / proposal predicates |
| `Residuals.lean` | `ResidualClass`, `ResidualWitness`; **R₁–R₄** predicates by `rc` tag; disjointness lemmas (**SPEC_004_RC1**) |
| `Interfaces.lean` | `DiagonalRepresentationalInterface`, closure, semantic interfaces; **`U123BarrierData`** (**D-002** pack) |
| `Barriers.lean` | **U₁–U₃** (`barrier_mode*`) — intuitionistic |
| `SyntacticModeCover.lean` | **Proved** four-way split for `SyntacticTotalization` (tagged syntax **only**) — **base / not the summit** |
| `AbstractModeCover/Attempt.lean` | `OpaqueTotalizationAttempt`; `GenuineInternalTotalizationAttempt` (**SPEC_015_KM2**) |
| `AbstractModeCover/Profiles.lean` | Structural profiles on opaque attempts (**not** datatype tags) |
| `AbstractModeCover/Mediation.lean` | Mediation aliases + **`AbstractMediationDecompositionTarget`** (open `Prop`) |
| `AbstractModeCover/Classification.lean` | **`AbstractOpaqueModeCoverTarget`** (**proved** as `abstract_opaque_mode_cover_classical`; explicit **`classical`**); `fromSyntactic`; conditional reflection |
| `AbstractModeCover/GenuinenessCandidates.lean` | **Minimal-strengthening search:** claim / burden-faithfulness / generic soundness slot / profile determinacy (**SPEC_015_KM2**) |
| `AbstractModeCover/WeakerBurdenSearch.lean` | **Principled weaker-burden sweep** + **`genuine_alone_does_not_imply_threeWayAnchorModes`** ( **`Genuine` alone** does not force anchored M₁–M₃) |
| `AbstractModeCover/D002ResidualWitnessTarget.lean` | **D-002 proved (abstract):** **`U123BarrierData`**-carrying **`barrierLinkedR4ResidualWitness`**; theorem **`d002_barrier_linked_r4_witness_holds`** |
| `ResidualEnrichment/Payloads.lean` | **SPEC_016_ER1 F1:** **`ObstructionSignature`**, **`ResidualPayloadFamily`**, **`SigmaResidualPayload`** |
| `ResidualEnrichment/EnrichedWitness.lean` | **SPEC_016_ER1 F1:** **`EnrichedR4ResidualWitness`** — base witness + signature + payload |
| `ResidualEnrichment/Promotion.lean` | **SPEC_016_ER1 F2:** **`PayloadPromotionBridge`**, **`promote_barrier_pack_to_enriched_r4`** (and aliases); promotion is **data** (`def`/`abbrev`), not `theorem` |
| `ResidualEnrichment/Summit.lean` | Narrative hub for engine-enriched residual summit |
| `ResidualEnrichment/MixedPayloadDesignNotes.lean` | Pointer + summary: **SPEC_017_MX1** mixed payload shape (**product** of three columns); **no** defs |
| `ResidualEnrichment/Bridges/FromRI.lean` | **F3a:** **`riPayloadPromotionBridge`** (RI column); **`ReprObstructionPayload`** = Π-**`PLift`** negations from **`reprBarrier`**; **D-001** for richer NEMS/RI traces |
| `ResidualEnrichment/Bridges/FromRFO.lean` | **F3b:** **`rfoPayloadPromotionBridge`**; **`ClosureObstructionPayload`** = Π **`Cl`**, **`PLift (¬ closure_success)`**; **D-001** for RFO-native traces |
| `ResidualEnrichment/Bridges/FromSEM.lean` | **F3b:** **`semPayloadPromotionBridge`**; **`CertObstructionPayload`** = Π **`τ`**, **`PLift (¬ cert_success)`**; **D-001** for SEM traces |
| `ResidualEnrichment/Bridges/FromMixedTriple.lean` | **`mixedTriple`:** **`MixedTripleObstructionPayload`**, **`mixedTriplePayloadPromotionBridge`**, **`enrichedR4_*_withMixedTriplePayload`** (**SPEC_017_MX1**) |
| `AbstractModeCover/AnchoredFlagship.lean` | **`HonestAnchoredInternalCompletion`**, **`AnchoredFlagshipUniversalCover`** (proved); Paper D **anchored** bridge (**SPEC_015**, **SPEC_010_US1**) |
| `AbstractModeCover/LayerDiscipline.lean` | **Anti-drift narrative + official target name:** **`OfficialLayerOneAnchoredCompletionTarget`**, theorem **`official_layer_one_anchored_completion_target_holds`** (= flagship universal cover); states Layer 2 (**`WeakerBurdenSearch.lean`**) is **boundary**, not a rival Line-1 flagship |
| `AbstractModeCover/PaperDAnchoredChain.lean` | **Layer 1 Paper D flagship (nonexistence):** **`paper_d_anchored_honest_completion_refutes_triple_barriers`**; **displayed** **`barriered_architecture_admits_no_true_honest_anchored_internal_completion`** — no **true** **`HonestAnchoredInternalCompletion`** over `arch` under **U₁–U₃** |
| `AbstractModeCover/PostFailureResidual.lean` | **Aftermath (barrier-linked R₄):** **`positive_residual_profile_of_triple_barriers_at_anchor`** — **`barrierLinkedR4ResidualWitness`** (**`U123BarrierData`** on **`carrier`**) |
| `Universal.lean` | `no_success_any_canonical_mode` — **U₁–U₃** vs **`Mode*i*Success`** (composed in **`PaperDAnchoredChain.lean`** for anchored flagship) |
| `Adequacy.lean` | Admissibility scaffolding (**SPEC_012_AA1**) |
| `InfinityCompression.lean` | IC sketch (**SPEC_013_IC1**) |
| `Instances/ONE.lean` | `OneRouteDiscipline` bundle (**SPEC_011_OI1**) |
| `RouteCanonicality.lean` | Deferred (**SPEC_014_CC1**) |

## Two theorem layers — anchored completion vs relocated success (**frozen distinction**)

| **Layer** | **Meaning (Lean)** | **Program role** |
|-----------|-------------------|------------------|
| **Layer 1 — Anchored completion** | `RepresentationalProfile` / `ClosureProfile` / `CertificatoryProfile` use nominations **at `anchor`** | **Official Paper D completion target:** **`HonestAnchoredInternalCompletion`** (`AnchoredFlagship.lean`) = claim + **`IsBurdenFaithfulClaim`**; **`OfficialLayerOneAnchoredCompletionTarget`** / **`official_layer_one_anchored_completion_target_holds`** (`LayerDiscipline.lean`) = same universal **intuitionistic** four-way cover. **Not** the same as **`AbstractOpaqueModeCoverTarget`** (∀ bare attempts + **`Genuine` alone**). |
| **Layer 2 — Relocated / off-anchor success** | `RepresentationalProfileAt a p`, … for some `p : carrier`; **`IsBurdenFaithfulSomewhereClaim`** | **Boundary** structural family (not a rival flagship): **success geometry** with parameters distinct from `anchor`. **Does not** supersede Layer 1 — see **`AnchorNecessityBoundary`** in **`WeakerBurdenSearch.lean`** and **`LayerDiscipline.lean`**. |

**Boundary theorem (packaged):** `anchored_threeWay_modes_not_entailed_by_somewhereFaithful_claim_utype`,
`anchor_identification_collapses_somewhereFaithful_to_burdenFaithful`, `anchor_necessity_boundary_bundle_utype`.

**Do not mix layers in prose or proofs** without saying so: anchored classification theorems **require** anchored obligations; allowing relocation changes the **theorem subject**.

## Disclosure — three “mode cover” layers

1. **Syntactic (proved):** `SyntacticTotalization` carries its regime as a **constructor tag**; `syntactic_four_way` is proof-by-cases. This is the **control theorem**; it does **not** solve BACKGROUND §VII for opaque attempts.
2. **Abstract — definitions + reflection (in progress):** `AbstractModeCover/*` introduces **non-tag-carrying** `OpaqueTotalizationAttempt`, profile predicates **at `anchor`**, and **`fromSyntactic`** (embedding). **`syntactic_reflection_four_way_of_axis_success`** is **conditional**: unconditional four-way disjunction of profiles is **false** for arbitrary architectures (see docstring there).
3. **Abstract — summit (`Prop` targets):** `AbstractOpaqueModeCoverTarget` is a **`theorem`** via **`abstract_opaque_mode_cover_classical`** (disclosed **LEM** on M₁–M₃ profiles at `anchor`). **`AbstractMediationDecompositionTarget`** is likewise discharged **classically** via `abstract_mediation_decomposition_target_classical`. **Constructive / burden-bearing** routes live in **`GenuinenessCandidates.lean`** (anchored **`IsBurdenFaithfulClaim`**; per-attempt `Decidable` on profiles).

## Summit targets — logical packaging (**partial**, does not close the gap)

| Lemma | Content |
|-------|--------|
| `mediation_decomposition_of_four_profiles` | Four-way **profile** OR \(\Rightarrow\) mediation-shaped OR (**purely intuitionistic**). |
| `abstract_cover_implies_mediation_decomposition_target` | **`AbstractOpaqueModeCoverTarget` \(\Rightarrow\) `AbstractMediationDecompositionTarget`**. |
| `abstract_mediation_implies_cover_classical` / `abstract_mediation_iff_cover_classical` | Converse and iff use **`classical`** (case split on `PositiveResidualProfile`). **Documented** — not hidden choice. |
| `abstract_opaque_mode_cover_classical` | **LEM** on M₁–M₃ \(\Rightarrow\) four-way cover (R₄ branch: `positive_residual_profile_of_three_failures`). |
| `abstract_four_way_of_burdenFaithful_claim` | **Intuitionistic:** true claim + **`IsBurdenFaithfulClaim`** \(\Rightarrow\) cover (**M₁–M₃** disjunct; residual unused). |
| `burdenFaithful_claim_incompatible_with_threeFailures` | **Faithful true claim** incompatible with ¬M₁∧¬M₂∧¬M₃ (so **not** honest positive-residual data). |
| `abstract_four_way_of_profileDeterminacy` | **Intuitionistic:** `Decidable` on three profiles \(\Rightarrow\) four-way cover. |
| `trivial_soundness_does_not_force_profiles` | Generic `soundness : claim → Prop` slot **insufficient** without discipline. |
| `anchored_threeWay_modes_not_entailed_by_somewhereFaithful_claim_utype` | **Layer 2 \(\nRightarrow\) Layer 1:** somewhere-faithful + true claim **does not** force anchored `ThreeWayAnchorModes` (proof refutes universal implication). |
| `anchor_identification_collapses_somewhereFaithful_to_burdenFaithful` | **Subsingleton carrier:** spatial weakening **collapses** to anchor burden-faithfulness. |
| `anchor_necessity_boundary_bundle_utype` | One-shot `And` packaging of separation + refutation + orthogonality toy. |
| `genuine_alone_does_not_imply_threeWayAnchorModes` | Refutes **`Genuine` ⇒ anchored `ThreeWayAnchorModes`** universally; **R₄** disjunct is separate (**`AbstractOpaqueModeCoverTarget`** not refuted here). |
| `representationalProfile_implies_mode1Success` / `closureProfile_implies_mode2Success` / `certificatoryProfile_implies_mode3Success` | **Opaque profile at `anchor` ⇒** matching **`Mode*i*Success`** on `attempt.arch` (**Paper D morphism** to mode calculus). |
| `paper_d_anchored_honest_completion_refutes_triple_barriers` | **Paper D chain:** **I_anch** (true **`HonestAnchoredInternalCompletion`**) + **U₁–U₃** on same `arch` \(\Rightarrow\) **`False`** (**`PaperDAnchoredChain.lean`**, intuitionistic). |
| `barriered_architecture_admits_no_true_honest_anchored_internal_completion` | **Global nonexistence:** **¬∃** true **`HonestAnchoredInternalCompletion`** package with `arch = A` under **U₁–U₃** on **`A`**. |
| `positive_residual_profile_of_triple_barriers_at_anchor` | **Post-failure:** **U₁–U₃** \(\Rightarrow\) **`PositiveResidualProfile`** with **`barrierLinkedR4ResidualWitness`**. |
| `d002_barrier_linked_r4_witness_holds` | **D-002 abstract:** **`D002BarrierLinkedR4WitnessTarget`** is a **`theorem`**. |
| `barrierLinkedR4ResidualWitness` | **R₄** witness with **`carrier = U123BarrierData A`**, point **`⟨d₁,d₂,d₃⟩`** — barrier-linked at **type** level. |

**Still open (philosophical / constructive core):** universal classification from **`GenuineInternalTotalizationAttempt` (= `Nonempty carrier`) alone** without **either** classical case-split **or** an **honest enrichment** (claim soundness, determinacy, **SPEC_012**, …). The gap is **interface under-determination**, not missing packaging of an already classical fact.

**Weaker-burden search (2026-03-27, principled):** `WeakerBurdenSearch.lean` — **`IsBurdenFaithfulSomewhereClaim`** is **strictly weaker** than **`IsBurdenFaithfulClaim`** (success at **some** `p : carrier`, not `anchor`; **Bool** carrier toy). **Spatial weakening collapses** on a **subsingleton** carrier (`isSomewhereFaithful_iff_burdenFaithful_of_subsingleton_carrier`). **`IsJointFailureRuledOut`** is **classically** equivalent to anchor burden-faithfulness; **somewhere** \(\nRightarrow\) joint-failure (same toy: anchored triple failure + off-anchor cert success). **Omit-one** bundles (`OmitReprBurden`, ...) **imply** burden-faithfulness; **burden** \(\nRightarrow\) **omitRepr** (**Repr-only** witness).

## Outcome B — under-determination of the current opaque layer

**Why `GenuineInternalTotalizationAttempt` does not entail profiles (intuitionistically):** it is only **`Nonempty a.carrier`**. Profiles require **`arch.repr_success (reprAt anchor)`** (or closure/cert analogues) or **`PositiveResidualProfile`**, which adds **existential residual linkage**. None of this follows from mere nonemptiness of parameters.

**Earned enrichment lemmas** (see **`GenuinenessCandidates.lean`**, ordered **A \(\to\) B \(\to\) C**):

1. **Candidate A — naked claim:** still insufficient (`claim_independent_of_profiles`).
2. **Candidate B — burden-faithful claim (`IsBurdenFaithfulClaim`):** if the claim is **true**, it **constructively** forces M₁\(\lor\)M₂\(\lor\)M₃ at `anchor`, hence the four-way `Prop` (**residual branch unused**). **Sharp fact:** a **simultaneous** honest positive-residual configuration (all three failures) **contradicts** a **true** burden-faithful claim (`burdenFaithful_claim_incompatible_with_threeFailures`). A generic `soundness : claim → Prop` layer **alone** does not force architecture (`trivial_soundness_does_not_force_profiles`).
3. **Candidate C — profile determinacy:** `Decidable` on the three profiles gives **intuitionistic** four-way cover (`abstract_four_way_of_profileDeterminacy`).

**Still minimal beyond carrier:** **SPEC_012_AA1** / adequacy refinements; **D-001** for **engine** witness payloads beyond abstract **`U123BarrierData`** (**governance:** subordinate to **SPEC_015_KM2**).

## Smuggling-risk audit (ongoing)

| Topic | Risk | Mitigation in-repo |
|------|------|---------------------|
| `GenuineInternalTotalizationAttempt` | Collapsing to “already classified” | Currently **minimal**: `Nonempty carrier` only — tighten via **SPEC_012_AA1**, not via disjunctive conclusion |
| `PositiveResidualProfile` | Catch-all “none of the above” | Requires **R₄** + admissibility + **typed linkage** `cast h witness = anchor` (not mere `∃` trivial witness) |
| Profile OR | Vacuity if one disjunct is always true | Residual branch is **not** automatic for repr/closure/cert syntax without witness linkage |

## Strength notes

- **Barriers:** Mathematical content lives in **instantiating** the three `*Interface` hypotheses for concrete `A` (nems / ONE / etc.).
- **R₁–R₄:** Declared by **`ResidualWitness.rc`** (not vacuous `True` on every witness). **Admissibility** still a hook (**SPEC_012**). Optional: dependent payloads per class (**D-002** / future work).

## Build

```bash
lake build
```
