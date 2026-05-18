import ErdosProblems1066.Swanepoel.M8WindowGeometryFromContainment
import ErdosProblems1066.Swanepoel.Lemma10WindowGeometry
import ErdosProblems1066.Swanepoel.Lemma10AnalyticBridge

/-!
# Concrete M8 window-geometry projections

This module is a projection layer over `M8WindowGeometryFromContainment`.
It exposes the honest Figure 8 and Figure 9 window-geometry fields, and the
corresponding E22/E23 lower-bound projections, directly from containment data.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace M8WindowGeometryConcrete

open AngleContainmentInterface
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10WindowGeometry
open M8ConstructionInterface
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-! ## Honest projections from the containment package -/

/-- The Figure 8 containment field projected as honest window geometry. -/
theorem honestFigure8WindowGeometry_of_containment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowGeometry
      localLabels.predicates turnBounds.turn :=
  W.figure8WindowGeometry

/-- The Figure 9 left-containment field projected as honest window geometry. -/
theorem honestFigure9LeftWindowGeometry_of_containment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentLeftWindowGeometry
      localLabels.predicates turnBounds.turn :=
  W.figure9LeftWindowGeometry

/-- Containment data projected to the construction-interface window geometry. -/
def m8WindowGeometry_of_containment
    (W : M8WindowContainment localLabels turnBounds) :
    M8WindowGeometry localLabels turnBounds :=
  W.toM8WindowGeometry

/-- The Figure 8 field of the projected `M8WindowGeometry`. -/
theorem m8WindowGeometry_figure8_of_containment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowGeometry
      localLabels.predicates turnBounds.turn :=
  (m8WindowGeometry_of_containment W).figure8

/-- The Figure 9-left field of the projected `M8WindowGeometry`. -/
theorem m8WindowGeometry_figure9_left_of_containment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentLeftWindowGeometry
      localLabels.predicates turnBounds.turn :=
  (m8WindowGeometry_of_containment W).figure9_left

/-- The Figure 8 projection gives the honest E22 lower-bound hypothesis. -/
theorem honestFigure8_E22_of_containment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  (m8WindowGeometry_of_containment W).figure8_E22

/-- The Figure 9-left projection gives the honest E23 lower-bound hypothesis. -/
theorem honestFigure9_E23_of_containment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  (m8WindowGeometry_of_containment W).figure9_E23

/-- The containment package supplies both honest analytic lower bounds. -/
theorem honestE22_E23_of_containment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  And.intro
    (honestFigure8_E22_of_containment W)
    (honestFigure9_E23_of_containment W)

/-! ## Direct construction from the two containment interfaces -/

/-- Build the construction-interface window geometry directly from the two
concrete containment interfaces. -/
def m8WindowGeometry_of_containmentInterfaces
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    M8WindowGeometry localLabels turnBounds :=
  (M8WindowContainment.mk figure8 figure9_left).toM8WindowGeometry

/-- Figure 8 projection from separately supplied containment interfaces. -/
theorem honestFigure8WindowGeometry_of_containmentInterfaces
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    HonestFigure8SeparatedWindowGeometry
      localLabels.predicates turnBounds.turn :=
  (m8WindowGeometry_of_containmentInterfaces
    (localLabels := localLabels) (turnBounds := turnBounds)
    figure8 figure9_left).figure8

/-- Figure 9-left projection from separately supplied containment interfaces. -/
theorem honestFigure9LeftWindowGeometry_of_containmentInterfaces
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    HonestFigure9AdjacentLeftWindowGeometry
      localLabels.predicates turnBounds.turn :=
  (m8WindowGeometry_of_containmentInterfaces
    (localLabels := localLabels) (turnBounds := turnBounds)
    figure8 figure9_left).figure9_left

/-- E22 projected from separately supplied containment interfaces. -/
theorem honestFigure8_E22_of_containmentInterfaces
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  (m8WindowGeometry_of_containmentInterfaces
    (localLabels := localLabels) (turnBounds := turnBounds)
    figure8 figure9_left).figure8_E22

/-- E23 projected from separately supplied containment interfaces. -/
theorem honestFigure9_E23_of_containmentInterfaces
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  (m8WindowGeometry_of_containmentInterfaces
    (localLabels := localLabels) (turnBounds := turnBounds)
    figure8 figure9_left).figure9_E23

end M8WindowGeometryConcrete
end Swanepoel
end ErdosProblems1066

end
