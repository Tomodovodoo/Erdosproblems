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
open M8WindowGeometryFromContainment
open MinimalGraphFacts
open TriangleAngleFacts

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Reusable Euclidean/trigonometric consequences -/

/-- The left side of the Figure 9 central angle is unit squared-distance. -/
lemma central_left_sqDist_eq_one {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    sqDist qi p = 1 :=
  sqDist_eq_one_of_eucUnit (eucUnit_comm D.p_qi)

/-- The right side of the Figure 9 central angle is unit squared-distance. -/
lemma central_right_sqDist_eq_one {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    sqDist qj p = 1 :=
  sqDist_eq_one_of_eucUnit (eucUnit_comm D.p_qj)

/-- The first side of the Figure 9 left comparison angle is unit
squared-distance. -/
lemma left_first_sqDist_eq_one {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    sqDist p qi = 1 :=
  sqDist_eq_one_of_eucUnit D.p_qi

/-- The second side of the Figure 9 left comparison angle is unit
squared-distance. -/
lemma left_second_sqDist_eq_one {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    sqDist s qi = 1 :=
  sqDist_eq_one_of_eucUnit (eucUnit_comm D.qi_s)

/-- The first side of the Figure 9 right comparison angle is unit
squared-distance. -/
lemma right_first_sqDist_eq_one {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    sqDist p qj = 1 :=
  sqDist_eq_one_of_eucUnit D.p_qj

/-- The second side of the Figure 9 right comparison angle is unit
squared-distance. -/
lemma right_second_sqDist_eq_one {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    sqDist r qj = 1 :=
  sqDist_eq_one_of_eucUnit (eucUnit_comm D.qj_r)

/-- The Figure 9 central chord has squared-distance at least one. -/
lemma central_sqDist_ge_one {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    1 <= sqDist qi qj :=
  one_le_sqDist_of_eucSeparated D.qi_qj_sep

/-- The Figure 9 left comparison chord has squared-distance at least one. -/
lemma left_sqDist_ge_one {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    1 <= sqDist p s :=
  D.left_base_sqDist_ge_one

/-- The Figure 9 right comparison chord has squared-distance at least one. -/
lemma right_sqDist_ge_one {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    1 <= sqDist p r :=
  D.right_base_sqDist_ge_one

/-- The Figure 9 comparison chord has squared-distance at least one. -/
lemma comparison_sqDist_ge_one {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    1 <= sqDist s r :=
  D.comparison_chord_sqDist_ge_one

/-- The central Figure 9 dot product is at most `1 / 2`. -/
lemma central_dotAt_le_half {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    dotAt qi p qj <= 1 / 2 :=
  D.central_dotAt_le_half

/-- The left Figure 9 comparison dot product is at most `1 / 2`. -/
lemma left_dotAt_le_half {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    dotAt p qi s <= 1 / 2 :=
  D.left_comparison_dotAt_le_half

/-- The right Figure 9 comparison dot product is at most `1 / 2`. -/
lemma right_dotAt_le_half {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    dotAt p qj r <= 1 / 2 :=
  D.right_comparison_dotAt_le_half

/-- Bundle the available Figure 9 dot/squared-distance consequences. -/
lemma dotFacts {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    Figure9DotFacts p qi qj s r :=
  figure9DotFacts_of_distanceData D

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

/-- Build the selected adjacent-left fact package from the contained-data
record used by the Figure 9 containment layer. -/
def adjacentLeftFacts_of_containedData
    {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftContainedData turn i) :
    Figure9AdjacentLeftEuclideanFacts turn i :=
  adjacentLeftFacts_of_distanceContainment
    D.distanceData D.left_angle_le_adjacentTurn

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

/-- Upgrade explicit contained witnesses to selected Euclidean fact witnesses.
This direction extracts only facts already present in the contained distance
package and keeps the angle containment as an explicit input. -/
def euclideanFactWitnesses_of_containedWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainedWitnesses good turn) :
    Figure9AdjacentLeftEuclideanFactWitnesses good turn :=
  fun {i} hi hi_next hbad_i hbad_next =>
    adjacentLeftFacts_of_containedData
      (H (i := i) hi hi_next hbad_i hbad_next)

/-- Upgrade the selected containment facade from failed adjacent comparisons
to selected Euclidean fact witnesses. -/
def euclideanFactWitnesses_of_windowContainment
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftWindowContainment good turn) :
    Figure9AdjacentLeftEuclideanFactWitnesses good turn :=
  euclideanFactWitnesses_of_containedWitnesses H.toContainedWitnesses

/-- Upgrade a Figure 9 left-containment interface to selected Euclidean fact
witnesses. -/
def euclideanFactWitnesses_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentLeftEuclideanFactWitnesses good turn := by
  intro i hi hi_next hbad_i hbad_next
  exact adjacentLeftFacts_of_containedData
    (H.containedData (i := i) hi hi_next hbad_i hbad_next)

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

/-- Contained witnesses imply E23 through the Euclidean fact package. -/
theorem E23_of_containedWitnesses_via_euclideanFacts
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainedWitnesses good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_euclideanFactWitnesses_direct
    (euclideanFactWitnesses_of_containedWitnesses H)

/-- A Figure 9 selected containment facade implies E23 through the Euclidean
fact package. -/
theorem E23_of_windowContainment_via_euclideanFacts
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftWindowContainment good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_euclideanFactWitnesses_direct
    (euclideanFactWitnesses_of_windowContainment H)

/-- A Figure 9 left-containment interface implies E23 through the Euclidean
fact package. -/
theorem E23_of_containmentInterface_via_euclideanFacts
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_euclideanFactWitnesses_direct
    (euclideanFactWitnesses_of_containmentInterface H)

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

/-! ## Failed-label projections from existing containment packages -/

/-- Honest selected containment witnesses, indexed by failed local
comparisons, upgraded to selected Figure 9 Euclidean fact witnesses. -/
def honestEuclideanFactWitnesses_of_windowContainment
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn) :
    HonestFigure9AdjacentLeftEuclideanFactWitnesses P turn :=
  euclideanFactWitnesses_of_windowContainment H

/-- Select the Figure 9 adjacent-left Euclidean fact package determined by
adjacent failed honest labels.  The labels only select the existing contained
witness; the metric and angle facts come from that witness. -/
def honestAdjacentLeftEuclideanFacts_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Figure9AdjacentLeftEuclideanFacts turn i :=
  adjacentLeftFacts_of_containedData
    (Figure9ContainmentConcrete.honestContainedData_of_labelFailures
      H hi hi_next hbad_i hbad_next)

/-- The concrete Figure 9 distance package selected by adjacent failed honest
labels. -/
theorem honestDistanceData_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Figure9DistanceData
      (honestAdjacentLeftEuclideanFacts_of_labelFailures H
        hi hi_next hbad_i hbad_next).p
      (honestAdjacentLeftEuclideanFacts_of_labelFailures H
        hi hi_next hbad_i hbad_next).qi
      (honestAdjacentLeftEuclideanFacts_of_labelFailures H
        hi hi_next hbad_i hbad_next).qj
      (honestAdjacentLeftEuclideanFacts_of_labelFailures H
        hi hi_next hbad_i hbad_next).s
      (honestAdjacentLeftEuclideanFacts_of_labelFailures H
        hi hi_next hbad_i hbad_next).r :=
  (honestAdjacentLeftEuclideanFacts_of_labelFailures H
    hi hi_next hbad_i hbad_next).distanceData

/-- The full Euclidean fact bundle selected by adjacent failed honest labels. -/
theorem honestEuclideanFacts_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Figure9DistanceEuclideanFacts
      (honestAdjacentLeftEuclideanFacts_of_labelFailures H
        hi hi_next hbad_i hbad_next).p
      (honestAdjacentLeftEuclideanFacts_of_labelFailures H
        hi hi_next hbad_i hbad_next).qi
      (honestAdjacentLeftEuclideanFacts_of_labelFailures H
        hi hi_next hbad_i hbad_next).qj
      (honestAdjacentLeftEuclideanFacts_of_labelFailures H
        hi hi_next hbad_i hbad_next).s
      (honestAdjacentLeftEuclideanFacts_of_labelFailures H
        hi hi_next hbad_i hbad_next).r :=
  (honestAdjacentLeftEuclideanFacts_of_labelFailures H
    hi hi_next hbad_i hbad_next).euclideanFacts

/-- Adjacent failed honest labels select a Figure 9 left-angle lower bound. -/
theorem honest_left_angle_lower_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Real.pi / 3 <=
      angleAt
        (honestAdjacentLeftEuclideanFacts_of_labelFailures H
          hi hi_next hbad_i hbad_next).p
        (honestAdjacentLeftEuclideanFacts_of_labelFailures H
          hi hi_next hbad_i hbad_next).qi
        (honestAdjacentLeftEuclideanFacts_of_labelFailures H
          hi hi_next hbad_i hbad_next).s :=
  (honestAdjacentLeftEuclideanFacts_of_labelFailures H
    hi hi_next hbad_i hbad_next).left_angle_lower

/-- Adjacent failed honest labels, with the selected Figure 9 containment
witness, give the local adjacent-window lower bound. -/
theorem honestAdjacentTurn_lower_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Real.pi / 3 <= adjacentTurn turn i :=
  (honestAdjacentLeftEuclideanFacts_of_labelFailures H
    hi hi_next hbad_i hbad_next).adjacentTurn_lower

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- The Figure 9 field of an M8 window-containment package as selected
Euclidean fact witnesses. -/
def honestEuclideanFactWitnesses_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentLeftEuclideanFactWitnesses
      localLabels.predicates turnBounds.turn :=
  euclideanFactWitnesses_of_containmentInterface W.figure9_left

/-- Select Figure 9 adjacent-left Euclidean facts from an M8 window-containment
package using adjacent failed honest labels. -/
def honestAdjacentLeftEuclideanFacts_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    Figure9AdjacentLeftEuclideanFacts turnBounds.turn i :=
  adjacentLeftFacts_of_containedData
    (Figure9ContainmentConcrete.honestContainedData_of_m8WindowContainment_labelFailures
      W hi hi_next hbad_i hbad_next)

/-- Adjacent failed honest labels select a Figure 9 left-angle lower bound from
an M8 window-containment package. -/
theorem honest_left_angle_lower_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    Real.pi / 3 <=
      angleAt
        (honestAdjacentLeftEuclideanFacts_of_m8WindowContainment_labelFailures
          W hi hi_next hbad_i hbad_next).p
        (honestAdjacentLeftEuclideanFacts_of_m8WindowContainment_labelFailures
          W hi hi_next hbad_i hbad_next).qi
        (honestAdjacentLeftEuclideanFacts_of_m8WindowContainment_labelFailures
          W hi hi_next hbad_i hbad_next).s :=
  (honestAdjacentLeftEuclideanFacts_of_m8WindowContainment_labelFailures
    W hi hi_next hbad_i hbad_next).left_angle_lower

/-- Adjacent failed honest labels, selected through an M8 window-containment
package, give the local adjacent-window lower bound. -/
theorem honestAdjacentTurn_lower_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    Real.pi / 3 <= adjacentTurn turnBounds.turn i :=
  (honestAdjacentLeftEuclideanFacts_of_m8WindowContainment_labelFailures
    W hi hi_next hbad_i hbad_next).adjacentTurn_lower

end Figure9EuclideanFactsConcrete
end Swanepoel
end ErdosProblems1066

end
