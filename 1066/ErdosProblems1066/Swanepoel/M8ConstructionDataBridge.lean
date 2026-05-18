import ErdosProblems1066.Swanepoel.M8ConstructionInterface
import ErdosProblems1066.Swanepoel.M8PipelineClosure

set_option autoImplicit false

/-!
# Bridge from clean M8 construction data to separated pipeline fields

This module repackages the clean construction-interface data as the separated
fields consumed by `M8PipelineClosure`.  It contains no new geometric or
combinatorial content; all witnesses are the fields already stored in
`M8ConstructionInterface.M8ConstructionData`.
-/

namespace ErdosProblems1066
namespace Swanepoel

open M8ConstructionInterface
open M8PipelineClosure
open MinimalGraphFacts

noncomputable section

namespace M8ConstructionInterface
namespace M8ConstructionData

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Repackage the clean construction-interface data as the separated fields
used by `M8PipelineClosure`. -/
def toM8SeparatedConstructionFields
    (D : M8ConstructionData C hmin) :
    M8SeparatedConstructionFields C hmin where
  predicates := D.localLabels.predicates
  turn := D.turnBounds.turn
  turnBounds := {
    nonnegative := D.turnBounds.turn_nonnegative
    total_lt_pi_div_three := D.turnBounds.total_turn_lt_pi_div_three
  }
  windowGeometry := {
    figure8_separated := D.windowGeometry.figure8
    figure9_adjacent_left := D.windowGeometry.figure9_left
  }
  lateTriples := {
    lateTriples := D.lateTriples.toHonestLateTriples
  }

/-- A fixed clean construction-interface package gives the checked pipeline
contradiction through the separated-field bridge. -/
theorem contradiction
    (D : M8ConstructionData C hmin) :
    False :=
  D.toM8SeparatedConstructionFields.contradiction

end M8ConstructionData
end M8ConstructionInterface

namespace M8ConstructionDataBridge

/-! ## Uniform eliminator -/

/-- A uniform clean construction-interface eliminator for minimal cleared
failures. -/
def MinimalFailureM8ConstructionDataEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (M8ConstructionData C hmin)

/-- A uniform clean construction-interface eliminator supplies the separated
construction eliminator expected by `M8PipelineClosure`. -/
theorem separatedConstructionEliminator_of_constructionDataEliminator
    (hbuild : MinimalFailureM8ConstructionDataEliminator) :
    MinimalFailureM8SeparatedConstructionEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D =>
      exact Nonempty.intro D.toM8SeparatedConstructionFields

/-- The clean construction-interface eliminator rules out every minimal
cleared failure via the separated pipeline closure. -/
theorem no_minimalClearedFailure_of_constructionDataEliminator
    (hbuild : MinimalFailureM8ConstructionDataEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  exact
    no_minimalClearedFailure_of_separatedConstructionEliminator
      (separatedConstructionEliminator_of_constructionDataEliminator hbuild)

end

end M8ConstructionDataBridge
end Swanepoel
end ErdosProblems1066
