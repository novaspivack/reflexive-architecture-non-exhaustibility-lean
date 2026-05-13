# reflexive-architecture-nonexhaustibility-lean


## Research Program

This repository is part of the **Reflexive Reality** research program by [Nova Spivack](https://www.novaspivack.com/).

**What this formalizes:** Reflexive Architecture Nonexhaustibility (§B5g): anchored completion limits, barrier families, residual aftermath, and the Reflexive Development Law.

| Link | Description |
|------|-------------|
| [Research page](https://www.novaspivack.com/research/) | Full index of all papers, programs, and Lean archives |
| [Full abstracts](https://novaspivack.github.io/research/abstracts/#b5g-reflexive-architecture-nonexhaustibility) | Complete abstract for this library's papers |
| [Zenodo program hub](https://doi.org/10.5281/zenodo.19429270) | Citable DOI hub for the NEMS program |

All results are machine-checked in Lean 4 with a zero-sorry policy on proof targets.
See [MANIFEST.md](MANIFEST.md) for the sorry audit (if present).

---

Lean 4 library for **Reflexive Architecture Nonexhaustibility** — the general science of reflexive systems: anchored completion limits, barrier families, typed residual aftermath, and the Reflexive Development Law.

**Toolchain:** `leanprover/lean4:v4.29.1` — see `lean-toolchain`.

## What it proves

- **Barriered anchored completion is impossible**: in a broad class of reflexive systems, strong demands for internal self-completion are provably blocked — not as formless collapse but via classifiable barrier families.
- **Structured aftermath is forced**: after a barrier, a typed residual remains — witnesses, enrichment channels, semantic regimes.
- **Reflexive Development Law**: standing residual drives lawful response — refinement, regime shift, or fold-obstruction transition.

## Build

```bash
lake update
lake exe cache get   # pre-built Mathlib .olean files (strongly recommended)
lake build
```

## Documentation

See [MANIFEST.md](MANIFEST.md) for the module map, theorem inventory, and sorry-status accounting. The companion paper is published on Zenodo — see [novaspivack.com/research](https://www.novaspivack.com/research).
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429252
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
