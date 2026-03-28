# reflexive-architecture-nonexhaustibility-lean — MANIFEST

**Toolchain:** `leanprover/lean4:v4.29.0-rc6` (see `lean-toolchain`).  
**Mathlib:** `v4.29.0-rc6` (see `lake-manifest.json` after `lake update`).

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
