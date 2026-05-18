import ErdosProblems1066.Swanepoel.Figure8ContainmentConcrete
import ErdosProblems1066.Swanepoel.Lemma10AngleToTurn

set_option autoImplicit false

/-!
# Concrete Figure 8 Euclidean facts

This file records the reusable Figure 8 Euclidean/trigonometric facts that are
already available from the distance package, and isolates the one remaining
explicit input needed to reach E22: containment of the central angle in the
separated turn window.

The central-angle lower bound is proved from `Figure8DistanceData`.  The turn
window containment cannot be recovered from those metric facts alone, since it
depends on the external `turn` data, so the final package keeps that
containment as an explicit field and proves that it yields the Figure 8 E22
interfaces.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure8EuclideanFactsConcrete

open AngleBridgeFacts
open AngleContainmentInterface
open AngleGeometry
open Figure8ContainmentConcrete
open Lemma10AnalyticBridge
open Lemma10AngleToTurn
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

/-! ## Reusable Figure 8 metric and angle consequences -/

/-- The left side of the Figure 8 central angle is unit squared-distance. -/
lemma central_left_sqDist_eq_one {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r) :
    sqDist qi p = 1 :=
  sqDist_eq_one_of_eucUnit (eucUnit_comm D.p_qi)

/-- The right side of the Figure 8 central angle is unit squared-distance. -/
lemma central_right_sqDist_eq_one {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r) :
    sqDist qj p = 1 :=
  sqDist_eq_one_of_eucUnit (eucUnit_comm D.p_qj)

/-- The Figure 8 central chord has squared-distance at least one. -/
lemma central_sqDist_ge_one {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r) :
    1 <= sqDist qi qj :=
  D.qi_qj_sqDist_ge_one

/-- The Figure 8 comparison chord has squared-distance at least one. -/
lemma comparison_sqDist_ge_one {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r) :
    1 <= sqDist s r :=
  D.s_r_sqDist_ge_one

/-- The central Figure 8 dot product is at most `1 / 2`. -/
lemma central_dotAt_le_half {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r) :
    dotAt qi p qj <= 1 / 2 :=
  D.central_dotAt_le_half

/-- Bundle the available Figure 8 dot/squared-distance consequences. -/
lemma dotFacts {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r) :
    Figure8DotFacts p qi qj s r :=
  figure8DotFacts_of_distanceData D

/-- The central Figure 8 angle is at least `pi / 3`. -/
lemma central_angle_lower {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r) :
    Real.pi / 3 <= angleAt qi p qj :=
  figure8CentralAngle_lower_of_distanceData D

/-- Dot facts plus the two unit central sides imply the central angle lower
bound.  This is useful when a caller has already unpacked the Euclidean facts
instead of keeping the original `Figure8DistanceData`. -/
lemma central_angle_lower_of_dotFacts {p qi qj s r : Point}
    (F : Figure8DotFacts p qi qj s r)
    (hleft : sqDist qi p = 1) (hright : sqDist qj p = 1) :
    Real.pi / 3 <= angleAt qi p qj :=
  centralAngle_lower_of_figure8DotFacts F hleft hright

/-- Figure 8 distance data plus central-angle containment gives the separated
turn lower bound. -/
lemma separatedTurn_lower_of_central_containment
    {turn : Nat -> Real} {i j : Nat} {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r)
    (hcontained : angleAt qi p qj <= separatedTurn turn i j) :
    Real.pi / 3 <= separatedTurn turn i j :=
  Lemma10WindowGeometry.separatedTurn_lower_of_figure8DistanceData
    D hcontained

/-! ## Minimal explicit package for the remaining containment fact -/

/-- Explicit Figure 8 Euclidean data for separated failures, together with the
minimal turn-window fact not forced by the metric data alone.

The first field supplies a Figure 8 distance configuration.  The second field
states the central-angle containment for any Figure 8 distance data at the same
indices; this matches the angle-to-turn bridge and is strong enough to yield
E22 without choosing witnesses by classical choice. -/
structure Figure8ExplicitEuclideanFacts
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop where
  distance_data :
    forall {i j : Nat},
      1 <= i -> i + 1 < j -> j <= 10 ->
      Not (good i) -> Not (good j) ->
        Exists fun p : Point =>
        Exists fun qi : Point =>
        Exists fun qj : Point =>
        Exists fun s : Point =>
        Exists fun r : Point =>
          Figure8DistanceData p qi qj s r
  central_angle_le_separatedTurn :
    forall {i j : Nat} {p qi qj s r : Point},
      1 <= i -> i + 1 < j -> j <= 10 ->
      Not (good i) -> Not (good j) ->
      Figure8DistanceData p qi qj s r ->
        angleAt qi p qj <= separatedTurn turn i j

namespace Figure8ExplicitEuclideanFacts

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- Forget the explicit facts to the existing angle-to-turn bridge. -/
def toAngleToTurnBridge
    (H : Figure8ExplicitEuclideanFacts good turn) :
    Figure8SeparatedAngleToTurnBridge good turn where
  distance_data := by
    intro i j hi hsep hj hbad_i hbad_j
    exact H.distance_data hi hsep hj hbad_i hbad_j
  central_angle_le_separatedTurn := by
    intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
    exact H.central_angle_le_separatedTurn hi hsep hj hbad_i hbad_j D

/-- Convert from the existing angle-to-turn bridge to the explicit fact
package in this file. -/
def ofAngleToTurnBridge
    (H : Figure8SeparatedAngleToTurnBridge good turn) :
    Figure8ExplicitEuclideanFacts good turn where
  distance_data := by
    intro i j hi hsep hj hbad_i hbad_j
    exact H.distance_data hi hsep hj hbad_i hbad_j
  central_angle_le_separatedTurn := by
    intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
    exact H.central_angle_le_separatedTurn hi hsep hj hbad_i hbad_j D

/-- Convert from the concrete containment interface. -/
def ofContainmentInterface
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8ExplicitEuclideanFacts good turn where
  distance_data := by
    intro i j hi hsep hj hbad_i hbad_j
    let D := H.extractedData hi hsep hj hbad_i hbad_j
    exact Exists.intro D.p
      (Exists.intro D.qi
        (Exists.intro D.qj
          (Exists.intro D.s
            (Exists.intro D.r D.distanceData))))
  central_angle_le_separatedTurn := by
    intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
    exact H.central_angle_le_separatedTurn hi hsep hj hbad_i hbad_j D

/-- The explicit Figure 8 facts yield the named E22 lower-bound interface. -/
theorem E22
    (H : Figure8ExplicitEuclideanFacts good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  figure8SeparatedWindowLowerE22_of_angleToTurnBridge
    H.toAngleToTurnBridge

/-- Pointwise form of the E22 lower-bound projection. -/
theorem E22_apply
    (H : Figure8ExplicitEuclideanFacts good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Real.pi / 3 <= separatedTurn turn i j :=
  H.E22 hi hsep hj hbad_i hbad_j

/-- The concrete containment interface yields E22 through the explicit fact
package. -/
theorem E22_of_containmentInterface
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  (ofContainmentInterface H).E22

end Figure8ExplicitEuclideanFacts

/-! ## `m = 8` specializations -/

/-- Explicit Figure 8 Euclidean facts specialized to the local `m = 8`
predicate package. -/
def M8Figure8ExplicitEuclideanFacts
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Prop :=
  Figure8ExplicitEuclideanFacts (M8BrokenLatticeGood P) turn

/-- Explicit Figure 8 Euclidean facts specialized to an honest local `m = 8`
package. -/
def HonestFigure8ExplicitEuclideanFacts
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Prop :=
  M8Figure8ExplicitEuclideanFacts P.data turn

/-- Explicit `m = 8` Figure 8 facts give the local E22 hypothesis. -/
theorem m8Figure8SeparatedWindowLowerE22_of_explicitEuclideanFacts
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure8ExplicitEuclideanFacts P turn) :
    M8Figure8SeparatedWindowLowerE22 P turn :=
  H.E22

/-- Explicit honest Figure 8 facts give the honest E22 hypothesis. -/
theorem honestFigure8SeparatedWindowLowerE22_of_explicitEuclideanFacts
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8ExplicitEuclideanFacts P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn :=
  H.E22

/-! ## Projections from existing containment packages -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- The Figure 8 containment field of an M8 window-containment package as the
explicit Euclidean fact package in this file. -/
def honestExplicitEuclideanFacts_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8ExplicitEuclideanFacts
      localLabels.predicates turnBounds.turn :=
  Figure8ExplicitEuclideanFacts.ofContainmentInterface W.figure8

/-- Projection to honest E22 through the explicit Euclidean fact package. -/
theorem honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  (honestExplicitEuclideanFacts_of_m8WindowContainment W).E22

/-- The same E22 projection agrees with the existing Figure 8 containment
facade. -/
theorem honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment_containment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  Figure8ContainmentConcrete.honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment
    W

end Figure8EuclideanFactsConcrete
end Swanepoel
end ErdosProblems1066

end
