import ErdosProblems1066.Swanepoel.AngleGeometry
import ErdosProblems1066.Swanepoel.Lemma10EuclideanBridge

/-!
# Swanepoel Lemma 10 angle-to-turn bridge

This module is the next explicit layer between the Euclidean Figure 8/Figure 9
facts and the named E22/E23 turn-window hypotheses.

The new content is deliberately assumption-forward.  We prove the local
dot-product-to-`angleAt` estimates from the existing Figure facts, and then
convert those estimates into `separatedTurn`/`adjacentTurn` lower bounds only
under an explicit assumption that the relevant geometric angle is contained in
the corresponding turn window.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma10AngleToTurn

open AngleBridgeFacts
open AngleGeometry
open Lemma10AnalyticBridge
open Lemma10EuclideanBridge
open Lemma10Inequalities
open TriangleAngleFacts

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Pure angle-to-turn conversions -/

/-- If a geometric angle is at least `pi / 3` and the turn window contains that
angle, then the separated turn window has the E22 lower bound. -/
lemma separatedTurn_lower_of_angleAt_le_separatedTurn
    {turn : Nat -> Real} {i j : Nat} {a b c : Point}
    (hangle : Real.pi / 3 <= angleAt a b c)
    (hcontained : angleAt a b c <= separatedTurn turn i j) :
    Real.pi / 3 <= separatedTurn turn i j := by
  exact le_trans hangle hcontained

/-- If a geometric angle is at least `pi / 3` and the adjacent turn window
contains that angle, then the adjacent turn window has the E23 lower bound. -/
lemma adjacentTurn_lower_of_angleAt_le_adjacentTurn
    {turn : Nat -> Real} {i : Nat} {a b c : Point}
    (hangle : Real.pi / 3 <= angleAt a b c)
    (hcontained : angleAt a b c <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i := by
  exact le_trans hangle hcontained

/-! ## Figure dot facts give concrete `angleAt` lower bounds -/

/-- Figure 8 central dot fact plus explicit unit-side facts gives the central
`angleAt` lower bound. -/
lemma centralAngle_lower_of_figure8DotFacts
    {p qi qj s r : Point}
    (F : Figure8DotFacts p qi qj s r)
    (hpqi : sqDist qi p = 1) (hpqj : sqDist qj p = 1) :
    Real.pi / 3 <= angleAt qi p qj :=
  pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half
    hpqi hpqj F.central_dotAt_le_half

/-- Figure 9 central dot fact plus explicit unit-side facts gives the central
`angleAt` lower bound. -/
lemma centralAngle_lower_of_figure9DotFacts
    {p qi qj s r : Point}
    (F : Figure9DotFacts p qi qj s r)
    (hpqi : sqDist qi p = 1) (hpqj : sqDist qj p = 1) :
    Real.pi / 3 <= angleAt qi p qj :=
  pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half
    hpqi hpqj F.central_dotAt_le_half

/-- Figure 9 left comparison dot fact plus explicit unit-side facts gives the
left comparison `angleAt` lower bound. -/
lemma leftAngle_lower_of_figure9DotFacts
    {p qi qj s r : Point}
    (F : Figure9DotFacts p qi qj s r)
    (hpqi : sqDist p qi = 1) (hsqi : sqDist s qi = 1) :
    Real.pi / 3 <= angleAt p qi s :=
  pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half
    hpqi hsqi F.left_dotAt_le_half

/-- Figure 9 right comparison dot fact plus explicit unit-side facts gives the
right comparison `angleAt` lower bound. -/
lemma rightAngle_lower_of_figure9DotFacts
    {p qi qj s r : Point}
    (F : Figure9DotFacts p qi qj s r)
    (hpqj : sqDist p qj = 1) (hrqj : sqDist r qj = 1) :
    Real.pi / 3 <= angleAt p qj r :=
  pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half
    hpqj hrqj F.right_dotAt_le_half

/-! ## Figure facts to turn-window lower bounds -/

/-- Figure 8 dot facts imply the separated turn lower bound once the central
angle is explicitly known to be contained in the separated turn window. -/
lemma separatedTurn_lower_of_figure8DotFacts
    {turn : Nat -> Real} {i j : Nat} {p qi qj s r : Point}
    (F : Figure8DotFacts p qi qj s r)
    (hpqi : sqDist qi p = 1) (hpqj : sqDist qj p = 1)
    (hcontained : angleAt qi p qj <= separatedTurn turn i j) :
    Real.pi / 3 <= separatedTurn turn i j :=
  separatedTurn_lower_of_angleAt_le_separatedTurn
    (centralAngle_lower_of_figure8DotFacts F hpqi hpqj)
    hcontained

/-- Figure 8 distance data supplies the unit sides and dot fact needed for the
central-angle route to the separated turn lower bound. -/
lemma separatedTurn_lower_of_figure8DistanceData
    {turn : Nat -> Real} {i j : Nat} {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r)
    (hcontained : angleAt qi p qj <= separatedTurn turn i j) :
    Real.pi / 3 <= separatedTurn turn i j := by
  refine separatedTurn_lower_of_figure8DotFacts
    (figure8DotFacts_of_distanceData D) ?_ ?_ hcontained
  · exact sqDist_eq_one_of_eucUnit (eucUnit_comm D.p_qi)
  · exact sqDist_eq_one_of_eucUnit (eucUnit_comm D.p_qj)

/-- Figure 9 central dot facts imply the adjacent turn lower bound once the
central angle is explicitly known to be contained in the adjacent turn window. -/
lemma adjacentTurn_lower_of_figure9CentralDotFacts
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (F : Figure9DotFacts p qi qj s r)
    (hpqi : sqDist qi p = 1) (hpqj : sqDist qj p = 1)
    (hcontained : angleAt qi p qj <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  adjacentTurn_lower_of_angleAt_le_adjacentTurn
    (centralAngle_lower_of_figure9DotFacts F hpqi hpqj)
    hcontained

/-- Figure 9 left comparison dot facts imply the adjacent turn lower bound once
the left comparison angle is explicitly known to be contained in the adjacent
turn window. -/
lemma adjacentTurn_lower_of_figure9LeftDotFacts
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (F : Figure9DotFacts p qi qj s r)
    (hpqi : sqDist p qi = 1) (hsqi : sqDist s qi = 1)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  adjacentTurn_lower_of_angleAt_le_adjacentTurn
    (leftAngle_lower_of_figure9DotFacts F hpqi hsqi)
    hcontained

/-- Figure 9 right comparison dot facts imply the adjacent turn lower bound once
the right comparison angle is explicitly known to be contained in the adjacent
turn window. -/
lemma adjacentTurn_lower_of_figure9RightDotFacts
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (F : Figure9DotFacts p qi qj s r)
    (hpqj : sqDist p qj = 1) (hrqj : sqDist r qj = 1)
    (hcontained : angleAt p qj r <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  adjacentTurn_lower_of_angleAt_le_adjacentTurn
    (rightAngle_lower_of_figure9DotFacts F hpqj hrqj)
    hcontained

/-- Figure 9 distance data supplies the unit sides and dot fact needed for the
left-angle route to the adjacent turn lower bound. -/
lemma adjacentTurn_lower_of_figure9DistanceData_left
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i := by
  refine adjacentTurn_lower_of_figure9LeftDotFacts
    (figure9DotFacts_of_distanceData D) ?_ ?_ hcontained
  · exact sqDist_eq_one_of_eucUnit D.p_qi
  · exact sqDist_eq_one_of_eucUnit (eucUnit_comm D.qi_s)

/-- Figure 9 distance data supplies the unit sides and dot fact needed for the
right-angle route to the adjacent turn lower bound. -/
lemma adjacentTurn_lower_of_figure9DistanceData_right
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qj r <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i := by
  refine adjacentTurn_lower_of_figure9RightDotFacts
    (figure9DotFacts_of_distanceData D) ?_ ?_ hcontained
  · exact sqDist_eq_one_of_eucUnit D.p_qj
  · exact sqDist_eq_one_of_eucUnit (eucUnit_comm D.qj_r)

/-! ## Assumption-forward bridge structures for E22/E23 -/

/-- Figure 8 angle-to-turn bridge: distance data is Euclidean; the only
remaining analytic/topological assumption is that the central angle is contained
in the separated turn window. -/
structure Figure8SeparatedAngleToTurnBridge
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

/-- The Figure 8 angle-to-turn bridge yields the named E22 lower-bound
hypothesis. -/
theorem figure8SeparatedWindowLowerE22_of_angleToTurnBridge
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedAngleToTurnBridge good turn) :
    Figure8SeparatedWindowLowerE22 good turn := by
  intro i j hi hsep hj hbad_i hbad_j
  match H.distance_data hi hsep hj hbad_i hbad_j with
  | Exists.intro p hp =>
    match hp with
    | Exists.intro qi hqi =>
      match hqi with
      | Exists.intro qj hqj =>
        match hqj with
        | Exists.intro s hs =>
          match hs with
          | Exists.intro r D =>
            exact separatedTurn_lower_of_figure8DistanceData D
              (H.central_angle_le_separatedTurn
                hi hsep hj hbad_i hbad_j D)

/-- Figure 9 angle-to-turn bridge using the left comparison angle as the
explicit angle contained in the adjacent turn window. -/
structure Figure9AdjacentLeftAngleToTurnBridge
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop where
  distance_data :
    forall {i : Nat},
      1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
        Exists fun p : Point =>
        Exists fun qi : Point =>
        Exists fun qj : Point =>
        Exists fun s : Point =>
        Exists fun r : Point =>
          Figure9DistanceData p qi qj s r
  left_angle_le_adjacentTurn :
    forall {i : Nat} {p qi qj s r : Point},
      1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
      Figure9DistanceData p qi qj s r ->
        angleAt p qi s <= adjacentTurn turn i

/-- The Figure 9 left-angle bridge yields the named E23 lower-bound
hypothesis. -/
theorem figure9AdjacentWindowLowerE23_of_leftAngleToTurnBridge
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftAngleToTurnBridge good turn) :
    Figure9AdjacentWindowLowerE23 good turn := by
  intro i hi hi_next hbad_i hbad_next
  match H.distance_data hi hi_next hbad_i hbad_next with
  | Exists.intro p hp =>
    match hp with
    | Exists.intro qi hqi =>
      match hqi with
      | Exists.intro qj hqj =>
        match hqj with
        | Exists.intro s hs =>
          match hs with
          | Exists.intro r D =>
            exact adjacentTurn_lower_of_figure9DistanceData_left D
              (H.left_angle_le_adjacentTurn
                hi hi_next hbad_i hbad_next D)

/-- Combined angle-to-turn bridge to the pair of named analytic hypotheses used
by `Lemma10AnalyticBridge`. -/
theorem E22_E23_of_angleToTurnBridges
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H8 : Figure8SeparatedAngleToTurnBridge good turn)
    (H9 : Figure9AdjacentLeftAngleToTurnBridge good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  And.intro
    (figure8SeparatedWindowLowerE22_of_angleToTurnBridge H8)
    (figure9AdjacentWindowLowerE23_of_leftAngleToTurnBridge H9)

end Lemma10AngleToTurn
end Swanepoel
end ErdosProblems1066

end
