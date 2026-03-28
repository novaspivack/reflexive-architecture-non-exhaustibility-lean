import InfinityCompression.MetaProof.ReflectiveRouteComparison
import ReflexiveArchitectureNonexhaustibility.ResidualDynamics

/-!
# Sibling **infinity-compression** link (**EPIC_009**, **SPEC_013_IC1**)

**Lake:** `require «infinity-compression»` from **`../../infinity-compression/infinity-compression-lean`** (see root **`lakefile.lean`**).

This module is intentionally **thin**: it imports only **`ProperExtensionViaForgetful`** (Route **DQ4.4** core) and packages a
**`KernelWitness`** on **`KernelOfMap`** — the same fiber-collision geometry as **`kernelWitness_of_map`** in
**`ResidualDynamics`**. Heavier IC summit theorems stay **consumer-side** optional corollaries.
-/

namespace StructuredNonexhaustibility

universe u

open InfinityCompression.MetaProof

/--
**IC **``ProperExtensionViaForgetful`` **⇒** **paper C** **`KernelWitness`** on **`KernelOfMap`** — literal alignment of
“distinct points, same forgetful image” with **`ResidualDynamics`**’ **`kernelWitness_of_map`**.
-/
theorem exists_kernelWitness_of_properExtensionViaForgetful {α β : Type u} {f : α → β}
    (h : ProperExtensionViaForgetful f) :
    ∃ _w : KernelWitness α (KernelOfMap f), True :=
  let ⟨x₁, x₂, hne, heq⟩ := h
  ⟨kernelWitness_of_map (f := f) (x := x₁) (y := x₂) heq hne, trivial⟩

end StructuredNonexhaustibility
