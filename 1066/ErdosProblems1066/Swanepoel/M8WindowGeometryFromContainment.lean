import ErdosProblems1066.Swanepoel.AngleContainmentInterface
import ErdosProblems1066.Swanepoel.Lemma10WindowGeometry
import ErdosProblems1066.Swanepoel.M8ConstructionInterface

/-!
# M8 window geometry from angle containment

This module connects the concrete Figure 8/Figure 9 angle-containment
interfaces to the window-geometry fields expected by
`M8ConstructionInterface.M8ConstructionData`.

The containment assumptions stay explicit: callers provide the Figure 8
central-angle containment and the Figure 9 left-angle containment through the
records from `AngleContainmentInterface`; this file only repackages those
records into the existential window-geometry predicates used by
`Lemma10WindowGeometry`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace M8WindowGeometryFromContainment

open AngleContainmentInterface
open AngleGeometry
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open M8ConstructionInterface
open MinimalGraphFacts

universe u

/-! ## Generic Figure 8/Figure 9 containment to window geometry -/

/-- A concrete Figure 8 containment interface supplies the existential
Figure 8 separated-window geometry used by `Lemma10WindowGeometry`. -/
def figure8SeparatedWindowGeometry_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedWindowGeometry good turn := by
  intro i j hi hsep hj hbad_i hbad_j
  let D := H.extractedData hi hsep hj hbad_i hbad_j
  exact Exists.intro D.p
    (Exists.intro D.qi
      (Exists.intro D.qj
        (Exists.intro D.s
          (Exists.intro D.r
            (And.intro D.distanceData
              (H.central_angle_le_separatedTurn
                hi hsep hj hbad_i hbad_j D.distanceData))))))

/-- A concrete Figure 9 left-containment interface supplies the existential
Figure 9 adjacent left-window geometry used by `Lemma10WindowGeometry`. -/
def figure9AdjacentLeftWindowGeometry_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentLeftWindowGeometry good turn := by
  intro i hi hi_next hbad_i hbad_next
  let D := H.extractedData hi hi_next hbad_i hbad_next
  exact Exists.intro D.p
    (Exists.intro D.qi
      (Exists.intro D.qj
        (Exists.intro D.s
          (Exists.intro D.r
            (And.intro D.distanceData
              (H.left_angle_le_adjacentTurn
                hi hi_next hbad_i hbad_next D.distanceData))))))

/-- Figure 8 containment gives the E22 lower-bound hypothesis through the
window-geometry route. -/
theorem figure8SeparatedWindowLowerE22_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  figure8SeparatedWindowLowerE22_of_windowGeometry
    (figure8SeparatedWindowGeometry_of_containmentInterface H)

/-- Figure 9 left-containment gives the E23 lower-bound hypothesis through
the window-geometry route. -/
theorem figure9AdjacentWindowLowerE23_of_leftContainmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  figure9AdjacentWindowLowerE23_of_leftWindowGeometry
    (figure9AdjacentLeftWindowGeometry_of_containmentInterface H)

/-- The combined containment bridge forgets to the pair of Figure 8/Figure 9
window-geometry predicates. -/
def windowGeometryPair_of_angleContainmentBridges
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AngleContainmentBridges good turn) :
    Figure8SeparatedWindowGeometry good turn /\
      Figure9AdjacentLeftWindowGeometry good turn :=
  And.intro
    (figure8SeparatedWindowGeometry_of_containmentInterface H.figure8)
    (figure9AdjacentLeftWindowGeometry_of_containmentInterface H.figure9)

/-- The combined containment bridge gives E22/E23 through the
`Lemma10WindowGeometry` conversions. -/
theorem E22_E23_of_angleContainmentBridges_via_windowGeometry
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AngleContainmentBridges good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  E22_E23_of_leftWindowGeometry
    (figure8SeparatedWindowGeometry_of_containmentInterface H.figure8)
    (figure9AdjacentLeftWindowGeometry_of_containmentInterface H.figure9)

/-! ## Honest M8 specializations -/

/-- Figure 8 containment specialized to the honest M8 predicate package. -/
def honestFigure8SeparatedWindowGeometry_of_containmentInterface
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood P.data) turn) :
    HonestFigure8SeparatedWindowGeometry P turn :=
  figure8SeparatedWindowGeometry_of_containmentInterface H

/-- Figure 9 left-containment specialized to the honest M8 predicate package. -/
def honestFigure9AdjacentLeftWindowGeometry_of_containmentInterface
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood P.data) turn) :
    HonestFigure9AdjacentLeftWindowGeometry P turn :=
  figure9AdjacentLeftWindowGeometry_of_containmentInterface H

/-- Honest M8 Figure 8 containment gives the E22 lower-bound hypothesis. -/
theorem honestFigure8SeparatedWindowLowerE22_of_containmentInterface
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood P.data) turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn :=
  honestFigure8SeparatedWindowLowerE22_of_windowGeometry
    (honestFigure8SeparatedWindowGeometry_of_containmentInterface H)

/-- Honest M8 Figure 9 left-containment gives the E23 lower-bound hypothesis. -/
theorem honestFigure9AdjacentWindowLowerE23_of_leftContainmentInterface
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood P.data) turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  honestFigure9AdjacentWindowLowerE23_of_leftWindowGeometry
    (honestFigure9AdjacentLeftWindowGeometry_of_containmentInterface H)

/-! ## M8 construction-interface packaging -/

/-- The explicit containment data needed to build the M8 window-geometry field
of `M8ConstructionInterface.M8ConstructionData`. -/
structure M8WindowContainment {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8LocalLabels C)
    (turnBounds : M8TurnBounds) where
  figure8 :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn
  figure9_left :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn

namespace M8WindowContainment

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- Repackage the explicit M8 containment fields as the generic combined
angle-containment bridge. -/
def toAngleContainmentBridges
    (W : M8WindowContainment localLabels turnBounds) :
    AngleContainmentBridges
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn where
  figure8 := W.figure8
  figure9 := W.figure9_left

/-- Build the explicit M8 containment package from the generic combined
angle-containment bridge. -/
def ofAngleContainmentBridges
    (H :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    M8WindowContainment localLabels turnBounds where
  figure8 := H.figure8
  figure9_left := H.figure9

/-- The Figure 8 containment field converted to honest window geometry. -/
def figure8WindowGeometry
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowGeometry
      localLabels.predicates turnBounds.turn :=
  honestFigure8SeparatedWindowGeometry_of_containmentInterface W.figure8

/-- The Figure 9 left-containment field converted to honest window geometry. -/
def figure9LeftWindowGeometry
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentLeftWindowGeometry
      localLabels.predicates turnBounds.turn :=
  honestFigure9AdjacentLeftWindowGeometry_of_containmentInterface
    W.figure9_left

/-- Convert explicit containment data to the M8 construction-interface
window-geometry package. -/
def toM8WindowGeometry
    (W : M8WindowContainment localLabels turnBounds) :
    M8ConstructionInterface.M8WindowGeometry localLabels turnBounds where
  figure8 := W.figure8WindowGeometry
  figure9_left := W.figure9LeftWindowGeometry

/-- Projection of the E22 lower-bound field after conversion. -/
theorem figure8_E22
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  M8ConstructionInterface.M8WindowGeometry.figure8_E22
    W.toM8WindowGeometry

/-- Projection of the E23 lower-bound field after conversion. -/
theorem figure9_E23
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  M8ConstructionInterface.M8WindowGeometry.figure9_E23
    W.toM8WindowGeometry

end M8WindowContainment

/-- A construction-data package whose window geometry is supplied as explicit
Figure 8/Figure 9 containment data. -/
structure M8ConstructionDataFromContainment {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localLabels : M8LocalLabels C
  turnBounds : M8TurnBounds
  lateTriples : M8LateTriples localLabels
  windowContainment : M8WindowContainment localLabels turnBounds

namespace M8ConstructionDataFromContainment

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The window-geometry field produced from explicit containment data. -/
def windowGeometry
    (D : M8ConstructionDataFromContainment C hmin) :
    M8ConstructionInterface.M8WindowGeometry D.localLabels D.turnBounds :=
  D.windowContainment.toM8WindowGeometry

/-- Forget explicit containment into the clean
`M8ConstructionInterface.M8ConstructionData` package. -/
def toM8ConstructionData
    (D : M8ConstructionDataFromContainment C hmin) :
    M8ConstructionInterface.M8ConstructionData C hmin where
  localLabels := D.localLabels
  turnBounds := D.turnBounds
  lateTriples := D.lateTriples
  windowGeometry := D.windowGeometry

/-- Compose with the existing conversion to the broken-lattice minimal-failure
construction data. -/
def toBrokenLatticeMinimalFailure
    (D : M8ConstructionDataFromContainment C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  D.toM8ConstructionData.toBrokenLatticeMinimalFailure

/-- A fixed minimal cleared failure equipped with this containment package is
contradictory via the existing construction interface. -/
theorem contradiction
    (D : M8ConstructionDataFromContainment C hmin) :
    False :=
  D.toBrokenLatticeMinimalFailure.contradiction

end M8ConstructionDataFromContainment

end M8WindowGeometryFromContainment
end Swanepoel
end ErdosProblems1066

end
