# reflexive-architecture-nonexhaustibility-lean — MANIFEST

**Toolchain:** `leanprover/lean4:v4.29.0-rc6` (see `lean-toolchain`).  
**Mathlib:** `v4.29.0-rc6` (see `lake-manifest.json` after `lake update`).

**Program focus (parent repo):** Next work is **EPIC_005**-centered (opaque mediation / decomposition). **EPIC_004** / **D-002** are **support-only** for that stack; **EPIC_010** stays deferred. See parent [`QUEUE.md`](../QUEUE.md) “Owner steering.”

## `sorry` / `axiom` audit

| Item | Count | Notes |
|------|-------|-------|
| `sorry` | **0** | `rg 'sorry' --glob '*.lean'` |
| `axiom` | **0** | Summit targets are named `def … : Prop`, not postulated |

## Module map (namespace `StructuredNonexhaustibility`)

| File | Role |
|------|------|
| `Basic.lean` | `ReflexiveArchitecture` + per-architecture success predicates |
| `Modes.lean` | `Mode*i*Success` / proposal predicates |
| `Residuals.lean` | `ResidualClass`, `ResidualWitness`; **R₁–R₄** predicates by `rc` tag; disjointness lemmas (**SPEC_004_RC1**) |
| `Interfaces.lean` | `DiagonalRepresentationalInterface`, closure, semantic interfaces |
| `Barriers.lean` | **U₁–U₃** (`barrier_mode*`) — intuitionistic |
| `SyntacticModeCover.lean` | **Proved** four-way split for `SyntacticTotalization` (tagged syntax **only**) — **base / not the summit** |
| `AbstractModeCover/Attempt.lean` | `OpaqueTotalizationAttempt`; `GenuineInternalTotalizationAttempt` (**SPEC_015_KM2**) |
| `AbstractModeCover/Profiles.lean` | Structural profiles on opaque attempts (**not** datatype tags) |
| `AbstractModeCover/Mediation.lean` | Mediation aliases + **`AbstractMediationDecompositionTarget`** (open `Prop`) |
| `AbstractModeCover/Classification.lean` | **`AbstractOpaqueModeCoverTarget`** (open `Prop`); `fromSyntactic`; conditional reflection |
| `Universal.lean` | `no_success_any_canonical_mode` — flagship **composition** |
| `Adequacy.lean` | Admissibility scaffolding (**SPEC_012_AA1**) |
| `InfinityCompression.lean` | IC sketch (**SPEC_013_IC1**) |
| `Instances/ONE.lean` | `OneRouteDiscipline` bundle (**SPEC_011_OI1**) |
| `RouteCanonicality.lean` | Deferred (**SPEC_014_CC1**) |

## Disclosure — three “mode cover” layers

1. **Syntactic (proved):** `SyntacticTotalization` carries its regime as a **constructor tag**; `syntactic_four_way` is proof-by-cases. This is the **control theorem**; it does **not** solve BACKGROUND §VII for opaque attempts.
2. **Abstract — definitions + reflection (in progress):** `AbstractModeCover/*` introduces **non-tag-carrying** `OpaqueTotalizationAttempt`, profile predicates, and **`fromSyntactic`** (embedding). **`syntactic_reflection_four_way_of_axis_success`** is **conditional**: unconditional four-way disjunction of profiles is **false** for arbitrary architectures (see docstring there).
3. **Abstract — summit (`Prop` targets):** `AbstractOpaqueModeCoverTarget` and `AbstractMediationDecompositionTarget` name what must be **proved** to earn the philosophical classification **without** smuggling. **Not** asserted as axioms.

## Summit targets — logical packaging (**partial**, does not close the gap)

| Lemma | Content |
|-------|--------|
| `mediation_decomposition_of_four_profiles` | Four-way **profile** OR \(\Rightarrow\) mediation-shaped OR (**purely intuitionistic**). |
| `abstract_cover_implies_mediation_decomposition_target` | **`AbstractOpaqueModeCoverTarget` \(\Rightarrow\) `AbstractMediationDecompositionTarget`**. |
| `abstract_mediation_implies_cover_classical` / `abstract_mediation_iff_cover_classical` | Converse and iff use **`classical`** (case split on `PositiveResidualProfile`). **Documented** — not hidden choice. |

**Still open:** \(\forall a,\, \texttt{Genuine}\,a \Rightarrow\) profile disjunction — no connection from `Nonempty carrier` alone to `repr_success` / `closure_success` / `cert_success` at `anchor`.

## Outcome B — under-determination of the current opaque layer

**Why `GenuineInternalTotalizationAttempt` does not entail profiles:** it is only **`Nonempty a.carrier`**. Profiles require **`arch.repr_success (reprAt anchor)`** (or closure/cert analogues) or **`PositiveResidualProfile`**, which adds **existential residual linkage**. None of this follows from mere nonemptiness of parameters.

**Minimal enrichment directions** (non-exhaustive; must not smuggle the four-way conclusion as data):

1. An explicit **`claimsInternalCompletion : Prop`** (or family) for the attempt + **soundness** lemmas tying claims to the right profile (**SPEC_012_AA1** / adequacy).
2. **Determinacy** / priority axioms when several success predicates could hold (avoid collapsing to ambiguous “everything at once” without a story).
3. **EPIC_004 / D-002** support for the **positive** branch: typed `ResidualWitness` **R₄** when hypotheses support survivor structure (**owner:** subordinate to **SPEC_015_KM2**).

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
