import ReflexiveArchitectureNonexhaustibility.Residuals

/-!
# Infinity Compression remainder hooks (**SPEC_013_IC1**)
-/

namespace StructuredNonexhaustibility

structure ICRemainderSketch where
  kernel_nonempty : Prop

def sketchToWitness (_s : ICRemainderSketch) : ResidualWitness := trivialR4ResidualWitness

theorem ic_sketch_tags_r4 (s : ICRemainderSketch) :
    IsR4PositiveSurvivor (sketchToWitness s) :=
  isR4_trivialR4

end StructuredNonexhaustibility
