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
`M8ConstructionInterface.M8ConstructionData`.
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

/-- The construction-interface no-early package induced by the five concrete
early exclusions. -/
def constructionNoEarlyTriples
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8ConstructionNoEarlyTriples P.localLabels where
  noEarlyTripleEquality := P.noEarlyTriples.toNoEarlyTripleEquality

/-- The late-triples field required by `M8ConstructionInterface`. -/
def lateTriples
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8LateTriples P.localLabels :=
  P.constructionNoEarlyTriples.toM8LateTriples

/-- The window-geometry field required by `M8ConstructionInterface`. -/
def windowGeometry
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8WindowGeometry P.localLabels P.turnBounds :=
  P.windowContainment.toM8WindowGeometry

/-- Assemble the fixed package as clean `M8ConstructionInterface` data. -/
def toM8ConstructionData
    (P : M8TurnWindowNoEarlyPackage C hmin) :
    M8ConstructionData C hmin where
  localLabels := P.localLabels
  turnBounds := P.turnBounds
  lateTriples := P.lateTriples
  windowGeometry := P.windowGeometry

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
  P.toBrokenLatticeMinimalFailure.contradiction

end M8TurnWindowNoEarlyPackage

end M8TurnWindowNoEarlyFinal
end Swanepoel
end ErdosProblems1066

end
