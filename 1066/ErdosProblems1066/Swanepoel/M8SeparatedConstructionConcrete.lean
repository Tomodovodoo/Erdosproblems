import ErdosProblems1066.Swanepoel.FinalConditional
import ErdosProblems1066.Swanepoel.M8LabelsFromBoundaryInterface
import ErdosProblems1066.Swanepoel.M8LateTriplesFromNoEarly
import ErdosProblems1066.Swanepoel.M8MinimalFailureEliminatorInterface
import ErdosProblems1066.Swanepoel.M8TurnBoundsFromArc
import ErdosProblems1066.Swanepoel.M8WindowGeometryFromContainment

set_option autoImplicit false

/-!
# Concrete aggregator for the separated `m = 8` construction

This module is only an aggregator.  It does not assert that the separated
construction exists for every minimal failure.  Instead, it records the
smallest explicit component package used by the current interfaces and checks
that those components assemble into
`M8PipelineClosure.M8SeparatedConstructionFields`, hence into the final
conditional Swanepoel target.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8SeparatedConstructionConcrete

open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8LateTriplesFromNoEarly
open M8MinimalFailureEliminatorInterface
open M8PipelineClosure
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalGraphFacts

noncomputable section

/-! ## One fixed minimal failure -/

/-- The explicit components needed for one fixed minimal cleared failure.

The fields are intentionally the upstream component interfaces, not a restated
copy of the final separated fields:

* `labels` supplies the boundary/Lemma 8 local labels.
* `arc` supplies the normalized nonconcave-arc turn bounds.
* `noEarlyTriples` supplies the Lemma 9 no-early-triple input.
* `windowContainment` supplies the Figure 8/Figure 9 containment data.
-/
structure M8SeparatedConstructionComponentPackage {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labels : M8LabelsFromBoundaryData C
  arc : NonconcaveArcTurnData
  noEarlyTriples :
    M8ConstructionNoEarlyTriples labels.toM8LocalLabels
  windowContainment :
    M8WindowContainment labels.toM8LocalLabels arc.toM8TurnBounds

namespace M8SeparatedConstructionComponentPackage

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The component package assembled as the clean construction-interface data.
-/
def toM8ConstructionData
    (P : M8SeparatedConstructionComponentPackage C hmin) :
    M8ConstructionData C hmin where
  localLabels := P.labels.toM8LocalLabels
  turnBounds := P.arc.toM8TurnBounds
  lateTriples := P.noEarlyTriples.toM8LateTriples
  windowGeometry := P.windowContainment.toM8WindowGeometry

/-- The component package assembled as the separated fields consumed by
`M8PipelineClosure`. -/
def toM8SeparatedConstructionFields
    (P : M8SeparatedConstructionComponentPackage C hmin) :
    M8SeparatedConstructionFields C hmin where
  predicates := P.labels.toM8LocalLabels.predicates
  turn := P.arc.turn
  turnBounds := {
    nonnegative := P.arc.turn_nonnegative
    total_lt_pi_div_three := P.arc.totalTurn_turn_lt_pi_div_three
  }
  windowGeometry := {
    figure8_separated := P.windowContainment.figure8WindowGeometry
    figure9_adjacent_left := P.windowContainment.figure9LeftWindowGeometry
  }
  lateTriples := {
    lateTriples := P.noEarlyTriples.toHonestLateTriples
  }

/-- A fixed package is contradictory, because it produces the separated fields
required by the checked pipeline closure. -/
theorem contradiction
    (P : M8SeparatedConstructionComponentPackage C hmin) :
    False :=
  P.toM8SeparatedConstructionFields.contradiction

end M8SeparatedConstructionComponentPackage

/-! ## Uniform package and final conditional target -/

/-- A uniform explicit component package for every minimal cleared failure.

This is still conditional data: it asks the caller to provide the components
for each minimal failure and only checks the assembly route.
-/
structure M8SeparatedConstructionComponents where
  componentPackage :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8SeparatedConstructionComponentPackage C hmin

namespace M8SeparatedConstructionComponents

/-- Assemble the uniform component package into the separated-field eliminator
used by `FinalConditional`. -/
def toSeparatedConstructionEliminator
    (H : M8SeparatedConstructionComponents) :
    FinalConditional.MinimalFailureM8SeparatedConstructionEliminator := by
  intro n C hmin
  exact
    Nonempty.intro
      ((H.componentPackage C hmin).toM8SeparatedConstructionFields)

/-- Assemble the uniform component package into the slightly more structured
minimal-failure eliminator interface. -/
def toM8MinimalFailureEliminator
    (H : M8SeparatedConstructionComponents) :
    M8MinimalFailureEliminator where
  constructionFields := fun C hmin =>
    (H.componentPackage C hmin).toM8SeparatedConstructionFields

/-- The uniform component package rules out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : M8SeparatedConstructionComponents) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toM8MinimalFailureEliminator.no_minimalClearedFailure

/-- Final conditional Swanepoel target from the explicit component package. -/
theorem targetLowerBoundEightThirtyOne
    (H : M8SeparatedConstructionComponents) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  FinalConditional.targetLowerBoundEightThirtyOne
    H.toSeparatedConstructionEliminator

end M8SeparatedConstructionComponents

/-- The theorem-form aggregator requested by the final conditional module:
from explicit components, produce the final conditional target. -/
theorem targetLowerBoundEightThirtyOne_of_componentPackage
    (H : M8SeparatedConstructionComponents) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

end

end M8SeparatedConstructionConcrete
end Swanepoel
end ErdosProblems1066
