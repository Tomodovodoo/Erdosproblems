import ErdosProblems1066.Swanepoel.Figure9ContainmentConcrete
import ErdosProblems1066.Swanepoel.Lemma10EuclideanBridge

/-!
# Figure 9 Euclidean facts for the adjacent-left window

This module keeps the reusable Figure 9 Euclidean/trigonometric consequences
close to the concrete containment adapters.

The distance package already proves the square-distance and dot-product facts
in `Lemma10EuclideanBridge`; the angle files turn those facts into
`pi / 3` lower bounds for the concrete mathlib angle.  The final turn-window
step still needs an explicit adjacent-left containment proof, so the selected
witness packages below convert to the existing E23 and honest M8 interfaces
without introducing any hidden analytic assumption.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure9EuclideanFactsConcrete

open AngleBridgeFacts
open AngleContainmentInterface
open AngleGeometry
open Figure9ContainmentConcrete
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10EuclideanBridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open M8ConstructionInterface
open MinimalGraphFacts
open TriangleAngleFacts

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Reusable Euclidean/trigonometric consequences -/

/-- The dot-product, square-distance, and angle lower-bound facts extracted
from a concrete Figure 9 distance package. -/
structure Figure9DistanceEuclideanFacts (p qi qj s r : Point) : Prop where
  dotFacts : Figure9DotFacts p qi qj s r
  central_sqDist_ge_one : 1 <= sqDist qi qj
  left_sqDist_ge_one : 1 <= sqDist p s
  right_sqDist_ge_one : 1 <= sqDist p r
  comparison_sqDist_ge_one : 1 <= sqDist s r
  central_angle_lower : Real.pi / 3 <= angleAt qi p qj
  left_angle_lower : Real.pi / 3 <= angleAt p qi s
  right_angle_lower : Real.pi / 3 <= angleAt p qj r

/-- Figure 9 distance data supplies all currently reusable Euclidean facts:
dot-product bounds, separated base distances, and the three local angle lower
bounds. -/
def euclideanFacts_of_distanceData {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    Figure9DistanceEuclideanFacts p qi qj s r where
  dotFacts := figure9DotFacts_of_distanceData D
  central_sqDist_ge_one := one_le_sqDist_of_eucSeparated D.qi_qj_sep
  left_sqDist_ge_one := D.left_base_sqDist_ge_one
  right_sqDist_ge_one := D.right_base_sqDist_ge_one
  comparison_sqDist_ge_one := D.comparison_chord_sqDist_ge_one
  central_angle_lower := figure9CentralAngle_lower_of_distanceData D
  left_angle_lower := figure9LeftAngle_lower_of_distanceData D
  right_angle_lower := figure9RightAngle_lower_of_distanceData D

/-- A left comparison dot bound plus the two unit sides gives the Figure 9
left-angle lower bound.  This is the reusable trig core behind the
adjacent-left route. -/
theorem leftAngle_lower_of_dotFacts_eucUnits
    {p qi qj s r : Point}
    (F : Figure9DotFacts p qi qj s r)
    (hpqi : EucUnit p qi) (hqi_s : EucUnit qi s) :
    Real.pi / 3 <= angleAt p qi s :=
  pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half
    (sqDist_eq_one_of_eucUnit hpqi)
    (sqDist_eq_one_of_eucUnit (eucUnit_comm hqi_s))
    F.left_dotAt_le_half

/-- Projection of the Figure 9 left-angle lower bound from distance data. -/
theorem leftAngle_lower_of_distanceData
    {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    Real.pi / 3 <= angleAt p qi s :=
  (euclideanFacts_of_distanceData D).left_angle_lower

/-- Projection of the Figure 9 central-angle lower bound from distance data. -/
theorem centralAngle_lower_of_distanceData
    {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    Real.pi / 3 <= angleAt qi p qj :=
  (euclideanFacts_of_distanceData D).central_angle_lower

/-- Projection of the Figure 9 right-angle lower bound from distance data. -/
theorem rightAngle_lower_of_distanceData
    {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    Real.pi / 3 <= angleAt p qj r :=
  (euclideanFacts_of_distanceData D).right_angle_lower

/-- Distance data plus adjacent-left containment gives the local E23 turn
lower bound. -/
theorem adjacentTurn_lower_of_distanceData_leftContainment
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  le_trans (leftAngle_lower_of_distanceData D) hcontained

/-! ## Selected adjacent-left fact packages -/

/-- A selected Figure 9 adjacent-left witness together with its derived
Euclidean facts and the explicit angle containment into the adjacent turn
window. -/
structure Figure9AdjacentLeftEuclideanFacts
    (turn : Nat -> Real) (i : Nat) where
  p : Point
  qi : Point
  qj : Point
  s : Point
  r : Point
  distanceData : Figure9DistanceData p qi qj s r
  euclideanFacts : Figure9DistanceEuclideanFacts p qi qj s r
  left_angle_le_adjacentTurn : angleAt p qi s <= adjacentTurn turn i

/-- Build the selected adjacent-left fact package from the raw distance data
and the explicit containment proof. -/
def adjacentLeftFacts_of_distanceContainment
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    Figure9AdjacentLeftEuclideanFacts turn i where
  p := p
  qi := qi
  qj := qj
  s := s
  r := r
  distanceData := D
  euclideanFacts := euclideanFacts_of_distanceData D
  left_angle_le_adjacentTurn := hcontained

namespace Figure9AdjacentLeftEuclideanFacts

/-- The derived left-angle lower bound carried by a selected Figure 9
adjacent-left fact package. -/
theorem left_angle_lower {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftEuclideanFacts turn i) :
    Real.pi / 3 <= angleAt D.p D.qi D.s :=
  D.euclideanFacts.left_angle_lower

/-- The selected package implies the local adjacent-window lower bound. -/
theorem adjacentTurn_lower {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftEuclideanFacts turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  le_trans D.left_angle_lower D.left_angle_le_adjacentTurn

/-- Forget the Euclidean fact package to the contained-data record used by the
existing Figure 9 containment layer. -/
def toContainedData {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftEuclideanFacts turn i) :
    Figure9AdjacentLeftContainedData turn i where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData
  left_angle_le_adjacentTurn := D.left_angle_le_adjacentTurn

/-- Forget the selected package to the existential window-geometry witness. -/
def toWindowWitness {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftEuclideanFacts turn i) :
    Exists fun p : Point =>
    Exists fun qi : Point =>
    Exists fun qj : Point =>
    Exists fun s : Point =>
    Exists fun r : Point =>
      Figure9DistanceData p qi qj s r /\
        angleAt p qi s <= adjacentTurn turn i :=
  windowWitness_of_containedData D.toContainedData

end Figure9AdjacentLeftEuclideanFacts

/-! ## Uniform witnesses to E23 -/

/-- Uniform selected Figure 9 adjacent-left Euclidean facts for every adjacent
failed pair in the Lemma 10 window. -/
def Figure9AdjacentLeftEuclideanFactWitnesses
    (good : Nat -> Prop) (turn : Nat -> Real) : Type :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
      Figure9AdjacentLeftEuclideanFacts turn i

/-- Forget selected Euclidean fact witnesses to the contained-witness predicate
from `Figure9ContainmentConcrete`. -/
def containedWitnesses_of_euclideanFactWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftEuclideanFactWitnesses good turn) :
    Figure9AdjacentLeftContainedWitnesses good turn :=
  fun {i} hi hi_next hbad_i hbad_next =>
    (H (i := i) hi hi_next hbad_i hbad_next).toContainedData

/-- Uniform selected Euclidean fact witnesses supply the Figure 9 adjacent-left
window-geometry predicate. -/
def leftWindowGeometry_of_euclideanFactWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftEuclideanFactWitnesses good turn) :
    Figure9AdjacentLeftWindowGeometry good turn :=
  leftWindowGeometry_of_containedWitnesses
    (containedWitnesses_of_euclideanFactWitnesses H)

/-- Uniform selected Euclidean fact witnesses imply the named E23 lower-bound
hypothesis. -/
theorem E23_of_euclideanFactWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftEuclideanFactWitnesses good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_containedWitnesses
    (containedWitnesses_of_euclideanFactWitnesses H)

/-- The same E23 conclusion proved directly from the derived local turn lower
bound carried by each selected witness. -/
theorem E23_of_euclideanFactWitnesses_direct
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftEuclideanFactWitnesses good turn) :
    Figure9AdjacentWindowLowerE23 good turn := by
  intro i hi hi_next hbad_i hbad_next
  exact (H (i := i) hi hi_next hbad_i hbad_next).adjacentTurn_lower

/-! ## Honest M8 projections -/

/-- Honest M8 specialization of the selected Euclidean fact witnesses. -/
abbrev HonestFigure9AdjacentLeftEuclideanFactWitnesses
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) :=
  Figure9AdjacentLeftEuclideanFactWitnesses
    (M8BrokenLatticeGood P.data) turn

/-- Honest M8 selected Euclidean facts supply the Figure 9 adjacent-left
window-geometry predicate. -/
def honestLeftWindowGeometry_of_euclideanFactWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftEuclideanFactWitnesses P turn) :
    HonestFigure9AdjacentLeftWindowGeometry P turn :=
  @leftWindowGeometry_of_euclideanFactWitnesses
    (M8BrokenLatticeGood P.data) turn H

/-- Honest M8 selected Euclidean fact witnesses imply the named E23
lower-bound hypothesis. -/
theorem honestE23_of_euclideanFactWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftEuclideanFactWitnesses P turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  honestFigure9AdjacentWindowLowerE23_of_leftWindowGeometry
    (honestLeftWindowGeometry_of_euclideanFactWitnesses H)

end Figure9EuclideanFactsConcrete
end Swanepoel
end ErdosProblems1066

end
