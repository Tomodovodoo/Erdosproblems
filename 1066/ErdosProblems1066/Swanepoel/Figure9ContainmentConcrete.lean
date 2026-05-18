import ErdosProblems1066.Swanepoel.AngleContainmentInterface
import ErdosProblems1066.Swanepoel.M8WindowGeometryConcrete
import ErdosProblems1066.Swanepoel.Lemma10WindowGeometry

/-!
# Figure 9 adjacent-left containment projections

This module isolates the Figure 9 side of the Lemma 10 window reduction.
The inputs remain explicit: a Figure 9 distance package and a proof that the
left comparison angle is contained in the adjacent turn window.  The lemmas
below only package and project that data to the named E23 lower-bound
hypothesis.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure9ContainmentConcrete

open AngleBridgeFacts
open AngleContainmentInterface
open AngleGeometry
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open M8ConstructionInterface
open M8WindowGeometryConcrete
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Single adjacent-left witness -/

/-- Package explicit Figure 9 distance data and left-angle containment as the
contained-data record used by the containment interface. -/
def containedData_of_explicitDistanceContainment
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    Figure9AdjacentLeftContainedData turn i where
  p := p
  qi := qi
  qj := qj
  s := s
  r := r
  distanceData := D
  left_angle_le_adjacentTurn := hcontained

/-- The local explicit Figure 9 adjacent-left data gives the adjacent turn
lower bound. -/
theorem adjacentTurn_lower_of_explicitDistanceContainment
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  adjacentTurn_lower_of_figure9DistanceData_left D hcontained

/-- Projection from contained-data form to the local adjacent turn lower
bound. -/
theorem adjacentTurn_lower_of_containedData
    {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftContainedData turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  D.adjacentTurn_lower

/-- Forget a contained Figure 9 adjacent-left record to the existential window
geometry witness expected by `Lemma10WindowGeometry`. -/
def windowWitness_of_containedData
    {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftContainedData turn i) :
    Exists fun p : Point =>
    Exists fun qi : Point =>
    Exists fun qj : Point =>
    Exists fun s : Point =>
    Exists fun r : Point =>
      Figure9DistanceData p qi qj s r /\
        angleAt p qi s <= adjacentTurn turn i :=
  Exists.intro D.p
    (Exists.intro D.qi
      (Exists.intro D.qj
        (Exists.intro D.s
          (Exists.intro D.r
            (And.intro D.distanceData D.left_angle_le_adjacentTurn)))))

/-! ## Uniform adjacent-left witnesses to E23 -/

/-- Uniform explicit Figure 9 adjacent-left contained witnesses for every
adjacent failed pair in the Lemma 10 window. -/
def Figure9AdjacentLeftContainedWitnesses
    (good : Nat -> Prop) (turn : Nat -> Real) : Type :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
      Figure9AdjacentLeftContainedData turn i

/-- Explicit contained witnesses supply the Figure 9 adjacent-left window
geometry predicate. -/
def leftWindowGeometry_of_containedWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainedWitnesses good turn) :
    Figure9AdjacentLeftWindowGeometry good turn := by
  intro i hi hi_next hbad_i hbad_next
  exact windowWitness_of_containedData
    (H (i := i) hi hi_next hbad_i hbad_next)

/-- The same reduction, stated directly for the window-geometry hypothesis. -/
theorem E23_of_leftWindowGeometry
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftWindowGeometry good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  figure9AdjacentWindowLowerE23_of_leftWindowGeometry H

/-- Uniform explicit Figure 9 adjacent-left contained witnesses imply the
named E23 lower-bound hypothesis. -/
theorem E23_of_containedWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainedWitnesses good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_leftWindowGeometry
    (leftWindowGeometry_of_containedWitnesses H)

/-- A Figure 9 adjacent-left containment interface supplies the existential
window-geometry predicate through its selected contained witnesses. -/
def leftWindowGeometry_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentLeftWindowGeometry good turn :=
  leftWindowGeometry_of_containedWitnesses
    (fun {i} hi hi_next hbad_i hbad_next =>
      H.containedData (i := i) hi hi_next hbad_i hbad_next)

/-- A Figure 9 adjacent-left containment interface implies the named E23
lower-bound hypothesis through the window-geometry route. -/
theorem E23_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_leftWindowGeometry
    (leftWindowGeometry_of_containmentInterface H)

/-! ## Honest M8 projections -/

/-- Honest M8 specialization of the explicit contained-witness predicate. -/
def HonestFigure9AdjacentLeftContainedWitnesses
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Type :=
  Figure9AdjacentLeftContainedWitnesses
    (M8BrokenLatticeGood P.data) turn

/-- Honest M8 contained witnesses supply the Figure 9 adjacent-left window
geometry predicate. -/
def honestLeftWindowGeometry_of_containedWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftContainedWitnesses P turn) :
    HonestFigure9AdjacentLeftWindowGeometry P turn :=
  leftWindowGeometry_of_containedWitnesses H

/-- Honest M8 contained witnesses imply the named E23 lower-bound hypothesis. -/
theorem honestE23_of_containedWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftContainedWitnesses P turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  honestFigure9AdjacentWindowLowerE23_of_leftWindowGeometry
    (honestLeftWindowGeometry_of_containedWitnesses H)

/-- Honest M8 Figure 9 adjacent-left containment implies the named E23
lower-bound hypothesis. -/
theorem honestE23_of_containmentInterface
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood P.data) turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  honestFigure9AdjacentWindowLowerE23_of_leftWindowGeometry
    (leftWindowGeometry_of_containmentInterface H)

/-- Projection of the Figure 9 E23 field from the concrete M8 window
containment package. -/
theorem honestE23_of_windowContainment
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  honestFigure9_E23_of_containment W

/-- Projection of the Figure 9 E23 field from separately supplied concrete
M8 Figure 8 and Figure 9 containment interfaces. -/
theorem honestE23_of_containmentInterfaces
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
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
  honestFigure9_E23_of_containmentInterfaces
    (localLabels := localLabels) (turnBounds := turnBounds)
    figure8 figure9_left

end Figure9ContainmentConcrete
end Swanepoel
end ErdosProblems1066

end
