import ReflexiveArchitectureNonexhaustibility.ResidualDynamics
import ReflexiveArchitectureNonexhaustibility.Residuals

/-!
# Infinity Compression remainder hooks (**SPEC_013_IC1**)

**Kernel / fiber discipline (local):** **`KernelOfMap`**, **`kernelWitness_of_map`**, and forgetful **D0** lemmas live in
**`ResidualDynamics.lean`**—the standard “equal images ⇔ same fiber” pattern used by **SPEC_023_RG1**. Sibling
**infinity-compression** library imports remain **future** scope control (see spec §Scope control).

**Dynamics forward:** **`IsRefinementStep`**, **`PairSplitByRefinement`** compose with **`d0_forgetfulKernel_notSeparated_of_still_fine`**.

**Sketch:** **`ICRemainderSketch`** stays an abstract “remainder flag” keyed by **`kernel_nonempty`** until ported lemmas
replace or refine it.
-/

namespace StructuredNonexhaustibility

/--
**SPEC_013_IC1** re-export: IC-style fiber kernel for a forgetful map (alias for **`KernelOfMap`**).
-/
abbrev ICKernel {α β : Type _} (f : α → β) : Identification α :=
  KernelOfMap f

structure ICRemainderSketch where
  kernel_nonempty : Prop

def sketchToWitness (_s : ICRemainderSketch) : ResidualWitness := trivialR4ResidualWitness

theorem ic_sketch_tags_r4 (s : ICRemainderSketch) :
    IsR4PositiveSurvivor (sketchToWitness s) :=
  isR4_trivialR4

end StructuredNonexhaustibility
