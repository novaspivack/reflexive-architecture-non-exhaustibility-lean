# reflexive-architecture-nonexhaustibility-lean

Lean 4 library for **Reflexive-Architecture-Nonexhaustibility** (nested git repository; parent registers this as a **submodule**).

**Toolchain:** `leanprover/lean4:v4.29.0-rc6` — see parent [`docs/003_LEAN_TOOLCHAIN_PIN.md`](../docs/003_LEAN_TOOLCHAIN_PIN.md).

## Build

```bash
cd reflexive-architecture-nonexhaustibility-lean
lake build
```

**nems-lean (D-001):** **not** required by default — **`nems-lean` is private**; see **`lakefile.lean`** BIG NOTE and parent [**`README.md`**](../README.md).

## Git

This directory is a **separate repository**.

```bash
# After cloning the parent:
git submodule update --init --recursive
```

Lean commits: from **this directory**. Parent docs/specs: **parent repo root**.

When publishing, set the submodule `url` in the parent `.gitmodules` to this library’s public remote.
