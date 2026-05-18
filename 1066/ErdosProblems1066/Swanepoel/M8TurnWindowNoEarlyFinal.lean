import ErdosProblems1066.Swanepoel.M8PipelineClosure
import ErdosProblems1066.Swanepoel.M8TurnBoundsFromArc
import ErdosProblems1066.Swanepoel.M8WindowGeometryFromContainment
import ErdosProblems1066.Swanepoel.NoEarlyTripleConcrete

set_option autoImplicit false

/-!
# M8 construction fields from turn, window, and no-early data

This module is a final integration layer for one fixed minimal cleared
failure.  It combines:

* nonconcave-arc turn data,
* five concrete no-early-triple exclusions, and
* Figure 8/Figure 9 window-containment data

into the `lateTriples`, `turnBounds`, and `windowGeometry` fields required by
`M8ConstructionInterface.M8ConstructionData`, and also exposes the stronger
window/no-early and separated-field views from `M8PipelineClosure`.

The package is conditional data for one fixed minimal cleared failure: no
theorem here constructs such a package from minimality alone.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace M8TurnWindowNoEarlyFinal

open M8ConstructionInterface
open M8LateTriplesFromNoEarly
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalGraphFacts
open NoEarlyTripleConcrete

/-! ## Fixed-package assembly -/

/-- The explicit data needed to assemble the three remaining fields of
`M8ConstructionInterface.M8ConstructionData` for a fixed minimal cleared
failure.

The local labels are kept as a field because the turn, no-early, and window
packages are all indexed by the same honest labelled local configuration.
The minimality proof is only the downstream index for the contradiction; none
of the four fields below is inferred from it in this module.
-/
structure M8TurnWindowNoEarlyPackage {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localLabels : M8LocalLabels C
  arc : NonconcaveArcTurnData
  noEarlyTriples :
    M8ConcreteNoEarlyTripleEquality localLabels.predicates.data
  windowContainment :
    M8WindowContainment localLabels arc.toM8TurnBounds

namespace M8TurnWindowNoEarlyPackage

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The turn-bound field required by `M8ConstructionInterface`. -/
def turnBounds
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8TurnBounds :=
  P.arc.toM8TurnBounds

/-- The raw no-early-triple equality exclusion supplied by the concrete
five-start package. -/
theorem noEarlyTripleEquality
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    LateTriplesInterface.M8NoEarlyTripleEquality
      P.localLabels.predicates.data :=
  P.noEarlyTriples.toNoEarlyTripleEquality

/-- The construction-interface no-early package induced by the five concrete
early exclusions. -/
def constructionNoEarlyTriples
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8ConstructionNoEarlyTriples P.localLabels where
  noEarlyTripleEquality := P.noEarlyTripleEquality

/-- The pipeline no-early package induced by the same five concrete early
exclusions. -/
def pipelineNoEarlyTriples
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8PipelineNoEarlyTriples P.localLabels.predicates where
  noEarlyTripleEquality := P.noEarlyTripleEquality

/-- The late-triples field required by `M8ConstructionInterface`. -/
def lateTriples
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8LateTriples P.localLabels :=
  P.constructionNoEarlyTriples.toM8LateTriples

/-- The late-triples field in the separated `M8PipelineClosure` format. -/
def pipelineLateTriplesField
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8PipelineClosure.M8LateTriplesField P.localLabels.predicates :=
  P.pipelineNoEarlyTriples.toM8LateTriplesField

/-- The window-geometry field required by `M8ConstructionInterface`. -/
def windowGeometry
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8WindowGeometry P.localLabels P.turnBounds :=
  P.windowContainment.toM8WindowGeometry

/-- The input package viewed as the existing arc-plus-containment bridge. -/
def toM8ArcContainmentData
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8ArcContainmentData P.localLabels where
  arc := P.arc
  containment := by
    simpa using P.windowContainment.toAngleContainmentBridges

/-- Build the package from the current arc-containment bridge plus concrete
no-early exclusions. -/
def ofM8ArcContainmentData
    {localLabels : M8LocalLabels C}
    (D : M8ArcContainmentData localLabels)
    (H : M8ConcreteNoEarlyTripleEquality localLabels.predicates.data) :
    M8TurnWindowNoEarlyPackage C hmin where
  localLabels := localLabels
  arc := D.arc
  noEarlyTriples := H
  windowContainment := by
    simpa using M8WindowContainment.ofAngleContainmentBridges D.containment

/-- The turn-bound field in the separated `M8PipelineClosure` format. -/
def pipelineTurnBounds
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8PipelineClosure.M8TurnBounds P.arc.turn where
  nonnegative := P.arc.turn_nonnegative
  total_lt_pi_div_three := P.arc.totalTurn_turn_lt_pi_div_three

/-- The window-geometry field in the separated `M8PipelineClosure` format. -/
def pipelineWindowGeometry
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8PipelineClosure.M8WindowGeometry
      P.localLabels.predicates P.arc.turn where
  figure8_separated := by
    intro i j hi hsep hj hbad_i hbad_j
    simpa using
      P.windowContainment.figure8WindowGeometry
        (i := i) (j := j) hi hsep hj hbad_i hbad_j
  figure9_adjacent_left := by
    intro i hi hi_next hbad_i hbad_next
    simpa using
      P.windowContainment.figure9LeftWindowGeometry
        (i := i) hi hi_next hbad_i hbad_next

/-- The package assembled as the strongest current pipeline gate: explicit
window geometry plus raw no-early triples. -/
def toM8WindowNoEarlyConstructionFields
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8PipelineClosure.M8WindowNoEarlyConstructionFields C hmin where
  predicates := P.localLabels.predicates
  turn := P.arc.turn
  turnBounds := P.pipelineTurnBounds
  windowGeometry := P.pipelineWindowGeometry
  noEarlyTripleEquality := P.noEarlyTripleEquality

/-- Forget the strongest current gate to direct E22/E23 plus no-early fields.
-/
def toM8E22E23NoEarlyConstructionFields
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8PipelineClosure.M8E22E23NoEarlyConstructionFields C hmin :=
  P.toM8WindowNoEarlyConstructionFields.toE22E23NoEarlyConstructionFields

/-- Forget the strongest current gate to the separated construction fields. -/
def toM8SeparatedConstructionFields
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  P.toM8WindowNoEarlyConstructionFields.toSeparatedConstructionFields

/-- Assemble the package as construction data whose window geometry is still
remembered as explicit containment data. -/
def toM8ConstructionDataFromContainment
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8ConstructionDataFromContainment C hmin where
  localLabels := P.localLabels
  turnBounds := P.turnBounds
  lateTriples := P.lateTriples
  windowContainment := P.windowContainment

/-- Assemble the fixed package as clean `M8ConstructionInterface` data. -/
def toM8ConstructionData
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8ConstructionData C hmin :=
  P.toM8ConstructionDataFromContainment.toM8ConstructionData

/-- Forget the clean package to the existing broken-lattice minimal-failure
construction data. -/
def toBrokenLatticeMinimalFailure
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  P.toM8ConstructionData.toBrokenLatticeMinimalFailure

/-- A fixed minimal cleared failure equipped with the assembled turn, window,
and no-early package is contradictory. -/
theorem contradiction
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    False :=
  P.toM8WindowNoEarlyConstructionFields.contradiction

end M8TurnWindowNoEarlyPackage

end M8TurnWindowNoEarlyFinal
end Swanepoel
end ErdosProblems1066

end
