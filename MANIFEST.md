# reflexive-architecture-nonexhaustibility-lean — MANIFEST

**Toolchain:** `leanprover/lean4:v4.29.0-rc6` (see `lean-toolchain`).  
**Mathlib:** `v4.29.0-rc6` (see `lake-manifest.json` after `lake update`).

## `sorry` / `axiom` audit

| Item | Count | Notes |
|------|-------|--------|
| `sorry` | **0** | `rg 'sorry' --glob '*.lean'` |
| `axiom` | **0** | No postulated mode cover for **opaque** attempts |

## Module map (namespace `StructuredNonexhaustibility`)

| File | Role |
|------|------|
| `Basic.lean` | `ReflexiveArchitecture` + per-architecture success predicates |
| `Modes.lean` | `Mode*i*Success` / proposal predicates |
| `Residuals.lean` | `ResidualWitness`, R₁–R₄ placeholders (sharpen per **SPEC_004_RC1**) |
| `Interfaces.lean` | `DiagonalRepresentationalInterface`, closure, semantic interfaces |
| `Barriers.lean` | **U₁–U₃** (`barrier_mode*`) — intuitionistic |
| `SyntacticModeCover.lean` | **Proved** four-way split for `SyntacticTotalization` (tagged syntax **only**) |
| `Universal.lean` | `no_success_any_canonical_mode` — flagship **composition** |
| `Adequacy.lean` | Admissibility scaffolding (**SPEC_012_AA1**) |
| `InfinityCompression.lean` | IC sketch (**SPEC_013_IC1**) |
| `Instances/ONE.lean` | `OneRouteDiscipline` bundle (**SPEC_011_OI1**) |
| `RouteCanonicality.lean` | Deferred (**SPEC_014_CC1**) |

## Disclosure — two “mode cover” layers

1. **Syntactic:** `SyntacticTotalization` carries its regime as a **constructor tag**; `syntactic_four_way` is proof-by-cases (not the philosophical BACKGROUND §VII step for **opaque** internal totalizations).
2. **Abstract / philosophical:** No `axiom` is used. Closing **SPEC_009_MC1** for a **non-tag-carrying** attempt type is **open research**; this library is designed so barriers and composition do **not** depend on smuggling that gap into definitions.

## Strength notes

- **Barriers:** Mathematical content lives in **instantiating** the three `*Interface` hypotheses for concrete `A` (nems / ONE / etc.).
- **R₁–R₄:** Currently **placeholder** `True` predicates — not a claim that all residuals collapse; sharpen before citing in papers.

## Build

```bash
lake build
```
