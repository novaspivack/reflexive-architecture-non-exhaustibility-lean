# reflexive-architecture-nonexhaustibility-lean — MANIFEST

**Toolchain:** `leanprover/lean4:v4.29.0-rc6` (see `lean-toolchain`).  
**Mathlib:** `v4.29.0-rc6` (see `lake-manifest.json` after `lake update`).

**Program focus (parent repo):** **Layer 1** Paper D nonexistence + **D-002 abstract** witness are proved. **EPIC_011** (**SPEC_016/017**): **`ResidualEnrichment`** + bridges + **`mixedTriple`**. **EPIC_012** (**D-001**): **`require «nems-lean»`** (**path**) + **`NemS.Prelude`** + **`NemsStructuralProgramLink`**; **`EngineReflexiveMorphism`**, **`FromNativeTraces`**. **EPIC_010** (**SPEC_014**): **`RouteCanonicality.lean`**. **EPIC_013** (**SPEC_020_PT1**): proof-theoretic **`godelProvBicBarrierHypotheses`** lives in **nems-lean** (parent epic **complete**). **EPIC_014** (**SPEC_021_SC1**, **SPEC_022_RA1**): Paper 51 **comparison** + O7 **T1–T3** (**`ProvBicU123EnrichedR4Alignment.lean`**) — **integration arc frozen** (2026-03-28); more integration Lean = **new phase** (parent **[`EPIC_014_MASTER_ORCHESTRATION.md`](../specs/INCOMPLETE/IN-PROCESS/EPIC_014_SUMMIT_INTEGRATION_LAYER/EPIC_014_MASTER_ORCHESTRATION.md)** §Summit freeze). **EPIC_015** (**SPEC_023_RG1**): **dynamical** tranche — residual **persistence / response / regime shift** (**[`EPIC_015_MASTER_ORCHESTRATION.md`](../specs/INCOMPLETE/IN-PROCESS/EPIC_015_RESIDUAL_GENERATIVITY_AND_REGIME_CHANGE/EPIC_015_MASTER_ORCHESTRATION.md)**). See parent [`QUEUE.md`](../QUEUE.md).

## Paper 51 integration stack (**frozen** tranche — parent specs)

| Layer | Parent spec | Lean touchpoint |
|-------|-------------|-----------------|
| Proof-theoretic summit | **SPEC_020_PT1** (**EPIC_013**) | **`SemanticSelfDescription/Instances/GodelProvBic.lean`** (**nems-lean**) |
| Summit **comparison** | **SPEC_021_SC1** | **`SummitComparison.lean`** (**nems-lean**) |
| O7 → **U123** → enriched **R₄** | **SPEC_022_RA1** (**EPIC_014**) | **`ProvBicU123EnrichedR4Alignment.lean`**: **T1** const link, **T2** repr **`A_link_dep`**, **T3** **`C₁`** triple augment |

## `sorry` / `axiom` audit

| Item | Count | Notes |
|------|-------|-------|
| `sorry` | **0** | `rg 'sorry' --glob '*.lean'` |
| `axiom` | **0** | Summit targets are named `def … : Prop`, not postulated |

## Module map (namespace `StructuredNonexhaustibility`)

| File | Role |
|------|------|
| `EngineDependencyPinning.lean` | **D-001:** **`import NemS.Prelude`**, **`nems_engine_dependency_ok`**; **`EngineReflexiveMorphism`** — **`SPEC_018_PN1`** |
| `NemsStructuralProgramLink.lean` | **D-001 / NemS:** **`NemsReflexiveSystemSchema`** alias for **`StructuralNonExhaustibility.ReflexiveSystem`** (**Program V** shell) |
| `EngineReflexiveMorphism.lean` | **PN3:** **`EngineReflexiveMorphism`**, **`ReflexiveBarrierBundle`**, **`EngineU123BarrierData`**, **`oneRouteDiscipline_of_barrier_bundle`** — **`SPEC_003_BT1`** attachment shape (no NemS types) |
| `Basic.lean` | `ReflexiveArchitecture` + per-architecture success predicates |
| `Modes.lean` | `Mode*i*Success` / proposal predicates |
| `Residuals.lean` | `ResidualClass`, `ResidualWitness`; **R₁–R₄**; **`AdmissibleResidual`** (**R₄** ⇔ **defeq** with **`barrierLinkedR4ResidualWitness`** data); **`admissible_residual_r4_iff_barrier_pack`** |
| `Interfaces.lean` | `DiagonalRepresentationalInterface`, closure, semantic interfaces; **`U123BarrierData`** (**D-002** pack) |
| `Barriers.lean` | **U₁–U₃** (`barrier_mode*`) — intuitionistic |
| `SyntacticModeCover.lean` | **Proved** four-way split for `SyntacticTotalization` (tagged syntax **only**) — **base / not the summit** |
| `AbstractModeCover/Attempt.lean` | `OpaqueTotalizationAttempt`; `GenuineInternalTotalizationAttempt` (**SPEC_015_KM2**) |
| `AbstractModeCover/Profiles.lean` | Structural profiles on opaque attempts (**not** datatype tags) |
| `AbstractModeCover/Mediation.lean` | Mediation aliases + **`AbstractMediationDecompositionTarget`** (open `Prop`) |
| `AbstractModeCover/Classification.lean` | **`AbstractOpaqueModeCoverTarget`** (classical + **`Decidable`** + **explicit LEM-on-profiles** lemmas); **SPEC_015** bare-`Genuine` **boundary** (doc + spec) |
| `AbstractModeCover/GenuinenessCandidates.lean` | **Minimal-strengthening search:** claim / burden-faithfulness / generic soundness slot / profile determinacy (**SPEC_015_KM2**) |
| `AbstractModeCover/WeakerBurdenSearch.lean` | **Principled weaker-burden sweep** + **`genuine_alone_does_not_imply_threeWayAnchorModes`** ( **`Genuine` alone** does not force anchored M₁–M₃) |
| `AbstractModeCover/D002ResidualWitnessTarget.lean` | **D-002 proved (abstract):** **`U123BarrierData`**-carrying **`barrierLinkedR4ResidualWitness`**; theorem **`d002_barrier_linked_r4_witness_holds`** |
| `ResidualEnrichment/Payloads.lean` | **SPEC_016_ER1 F1:** **`ObstructionSignature`**, **`ResidualPayloadFamily`** (**`Type 1`** payload slots for **D-001**), **`SigmaResidualPayload`** |
| `ResidualEnrichment/EnrichedWitness.lean` | **SPEC_016_ER1 F1:** **`EnrichedR4ResidualWitness`** — base witness + signature + payload |
| `ResidualEnrichment/Promotion.lean` | **SPEC_016_ER1 F2:** **`PayloadPromotionBridge`** (**`Type 2`** — aligns with **`SigmaResidualPayload`** universe), **`promote_barrier_pack_to_enriched_r4`** (and aliases); **`promote_enriched_base_*`** lemmas (**base** independent of bridge / family) |
| `ResidualEnrichment/Summit.lean` | Narrative hub for engine-enriched residual summit |
| `ResidualEnrichment/MixedPayloadDesignNotes.lean` | Pointer + summary: **SPEC_017_MX1** mixed payload shape (**product** of three columns); **no** defs |
| `ResidualEnrichment/Bridges/FromRI.lean` | **F3a:** **`riPayloadPromotionBridge`** (RI column); carriers use **`ULift`** for **`Type 1`** slots; **`ReprObstructionPayload`** = Π-**`PLift`** negations from **`reprBarrier`**; **D-001** for richer NEMS/RI traces |
| `ResidualEnrichment/Bridges/FromRFO.lean` | **F3b:** **`rfoPayloadPromotionBridge`**; **`ClosureObstructionPayload`** = Π **`Cl`**, **`PLift (¬ closure_success)`**; **D-001** for RFO-native traces |
| `ResidualEnrichment/Bridges/FromSEM.lean` | **F3b:** **`semPayloadPromotionBridge`**; **`CertObstructionPayload`** = Π **`τ`**, **`PLift (¬ cert_success)`**; **D-001** for SEM traces |
| `ResidualEnrichment/Bridges/FromMixedTriple.lean` | **`mixedTriple`:** **`MixedTripleObstructionPayload`**, **`mixedTriplePayloadPromotionBridge`**, **`enrichedR4_*_withMixedTriplePayload`** (**SPEC_017_MX1**) |
| `ResidualEnrichment/Bridges/FromNativeTraces.lean` | **PN4:** **`nativeTripleResidualPayloadFamily`**, **`nativeTriplePayloadPromotionBridge`**, **`NativeObstructionTraceRefinement`**, column coherence **`Prop`**s — native carriers at **`Type 1`**; **`SPEC_018_PN1`** |
| `ResidualEnrichment/Bridges/FromNEMSProgramV.lean` | **D-001 / EPIC_012:** **`U123SemanticBarrierLink`**, **`ofU123SemanticBarrierLink`** (**`b`**.indexed **`sync`**), **`ofSemanticSelfDescriptionFrame`**, **`enrichedR4_*_u123DrivenSync`**, **`enrichedR4_*_semanticSync`**, **`enrichedR4_*_reflectionSync`**, **`trivialBarrier`**, **`certFn`**; **O7** seam: **`ProvBicU123EnrichedR4Alignment.lean`** (**SPEC_022_RA1**, **EPIC_014** **frozen**) |
| `AbstractModeCover/AnchoredFlagship.lean` | **`HonestAnchoredInternalCompletion`**, **`AnchoredFlagshipUniversalCover`** (proved); Paper D **anchored** bridge (**SPEC_015**, **SPEC_010_US1**) |
| `AbstractModeCover/LayerDiscipline.lean` | **Anti-drift narrative + official target name:** **`OfficialLayerOneAnchoredCompletionTarget`**, theorem **`official_layer_one_anchored_completion_target_holds`** (= flagship universal cover); states Layer 2 (**`WeakerBurdenSearch.lean`**) is **boundary**, not a rival Line-1 flagship |
| `AbstractModeCover/PaperDAnchoredChain.lean` | **Layer 1 Paper D flagship (nonexistence):** **`paper_d_anchored_honest_completion_refutes_triple_barriers`**; **displayed** **`barriered_architecture_admits_no_true_honest_anchored_internal_completion`** — no **true** **`HonestAnchoredInternalCompletion`** over `arch` under **U₁–U₃** |
| `AbstractModeCover/PostFailureResidual.lean` | **Aftermath:** **`positive_residual_profile_of_triple_barriers_at_anchor`** (schematic **`PositiveResidualProfile`**); companion **`honest_aftermath_carries_admissible_r4`** in **`Adequacy.lean`** |
| `Universal.lean` | `no_success_any_canonical_mode` — **U₁–U₃** vs **`Mode*i*Success`** (composed in **`PaperDAnchoredChain.lean`** for anchored flagship) |
| `Adequacy.lean` | **SPEC_012_AA1:** **`CertificateWorldConsistent`**, **`certificateWorldConsistent_holds`**, **`honest_aftermath_carries_admissible_r4`**, joint-failure / flagship lemmas |
| `InfinityCompression.lean` | IC sketch (**SPEC_013_IC1**) |
| `ResidualDynamics.lean` | **EPIC_015 / SPEC_023_RG1:** **`Identification`**, **`IsRefinementStep`**, **`PairSplitByRefinement`**, **`RegimeSnapshot`**, **`ResidualResponseStep`**, **`KernelWitness`**, **`WitnessSeparatedByRefinement`**; **D0** relational: **`d0_witness_not_separated_of_still_fine`**, **`d0_standing_fine_identification`**, **`d0_standing_unmet_need`**; **D1**–**D3** **open** |
| `Instances/ONE.lean` | `OneRouteDiscipline` bundle (**SPEC_011_OI1**) |
| `RouteCanonicality.lean` | **EPIC_010 / SPEC_014:** spectrum + **`canonical_spectrum_mono`**; **`AltRouteTaxonomy`**, **`TaxonomySound`**, **`TaxonomyComplete`**, **`canonical_spectrum_iff_labeled_successes`**, **`canonical_spectrum_iff_labeled_successes_of_pred_equiv`**, **`canonical_spectrum_mono_labeled`**, **`taxonomy_sound_of_successful_mono`**, **`taxonomy_complete_of_successful_mono`**, **`canonical_spectrum_mono_labeled_pair`** |
| `U123ReprAugmentedSemanticLink.lean` | **EPIC_012:** non-constant **`U123SemanticBarrierLink`** via **`barrierHypotheses_u123ReprAugment`** (**`b.reprBarrier`**); **`trivialObstruction*`** + **`enrichedR4_*_reprAugmentedU123Sync`** (**`bh`** parameter until a concrete **`EncodedNontrivial`** **×** intermediate-equiv frame lands in **nems-lean**; see **`ToReflection`** / **`UnitypedNatReprObstruction`**) |
| `KleenePredicatedResidualSummit.lean` | **SPEC_019_PS1:** Kleene **`BarrierHypothesesPred`** + repr augmentation → **`enrichedR4_u123_withAugmentedNemsProgramVRepr_predLinkSync`** |
| `ProvBicU123EnrichedR4Alignment.lean` | **SPEC_022_RA1** / **EPIC_014** (**O7**, **frozen**): **T1** **`A_link_const`**, **T2** repr **`A_link_dep`**, **T3** **`C₁`** (**`godelProvBicBarrierHypotheses_u123Augmented`**, **`u123SemanticBarrierLink_provBicU123TripleAugment`**) → **`u123DrivenSync`** enriched **R₄** |

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
| `positive_residual_profile_of_triple_barriers_at_anchor` | **Post-failure:** **U₁–U₃** \(\Rightarrow\) schematic **`PositiveResidualProfile`** + **`barrierLinkedR4ResidualWitness`**. |
| `honest_aftermath_carries_admissible_r4` | **`Adequacy.lean`:** same barriers \(\Rightarrow\) **R₄** witness is **`AdmissibleResidual`** + triple profile failure — honest **SPEC_012** companion. |
| `canonical_spectrum_iff_labeled_successes` | **RouteCanonicality:** **F2-1** + **sound + complete** taxonomy \(\Leftrightarrow\) labeled gadget successes. |
| `canonical_spectrum_mono_labeled` | **RouteCanonicality:** transport labeled successes across **`canonical_spectrum_mono`**. |
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
