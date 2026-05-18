import ErdosProblems1066.Swanepoel.Lemma10AngleToTurn

/-!
# Concrete angle-containment interface for Swanepoel Lemma 10

`Lemma10AngleToTurn` already proves the route from Figure 8/Figure 9 distance
data plus angle-containment assumptions to the named E22/E23 turn-window
hypotheses.  This file adds a slightly more concrete interface around the
remaining assumptions: callers may record the extracted Figure data as named
witnesses, together with the uniform containment facts needed by the existing
bridge theorem.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace AngleContainmentInterface

open AngleBridgeFacts
open AngleGeometry
open Lemma10AnalyticBridge
open Lemma10AngleToTurn
open Lemma10Inequalities

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Per-index extracted data -/

/-- A chosen Figure 8 distance witness for a separated pair of failed
comparisons. -/
structure Figure8SeparatedExtractedData where
  p : Point
  qi : Point
  qj : Point
  s : Point
  r : Point
  distanceData : Figure8DistanceData p qi qj s r

/-- A chosen Figure 8 witness together with the local central-angle containment
for one separated pair. -/
structure Figure8SeparatedContainedData
    (turn : Nat -> Real) (i j : Nat) where
  p : Point
  qi : Point
  qj : Point
  s : Point
  r : Point
  distanceData : Figure8DistanceData p qi qj s r
  central_angle_le_separatedTurn :
    angleAt qi p qj <= separatedTurn turn i j

namespace Figure8SeparatedExtractedData

/-- Attach a containment proof to a chosen Figure 8 distance witness. -/
def withContainment {turn : Nat -> Real} {i j : Nat}
    (D : Figure8SeparatedExtractedData)
    (hcontained : angleAt D.qi D.p D.qj <= separatedTurn turn i j) :
    Figure8SeparatedContainedData turn i j where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData
  central_angle_le_separatedTurn := hcontained

end Figure8SeparatedExtractedData

namespace Figure8SeparatedContainedData

/-- A locally contained Figure 8 witness gives the E22 lower bound for that
pair. -/
theorem separatedTurn_lower {turn : Nat -> Real} {i j : Nat}
    (D : Figure8SeparatedContainedData turn i j) :
    Real.pi / 3 <= separatedTurn turn i j :=
  separatedTurn_lower_of_figure8DistanceData
    D.distanceData D.central_angle_le_separatedTurn

end Figure8SeparatedContainedData

/-- A chosen Figure 9 distance witness for an adjacent pair of failed
comparisons. -/
structure Figure9AdjacentExtractedData where
  p : Point
  qi : Point
  qj : Point
  s : Point
  r : Point
  distanceData : Figure9DistanceData p qi qj s r

/-- A chosen Figure 9 witness together with the local left-angle containment
for one adjacent pair.  This matches the Figure 9 route currently consumed by
`Lemma10AngleToTurn.E22_E23_of_angleToTurnBridges`. -/
structure Figure9AdjacentLeftContainedData
    (turn : Nat -> Real) (i : Nat) where
  p : Point
  qi : Point
  qj : Point
  s : Point
  r : Point
  distanceData : Figure9DistanceData p qi qj s r
  left_angle_le_adjacentTurn :
    angleAt p qi s <= adjacentTurn turn i

namespace Figure9AdjacentExtractedData

/-- Attach a left-angle containment proof to a chosen Figure 9 distance
witness. -/
def withLeftContainment {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentExtractedData)
    (hcontained : angleAt D.p D.qi D.s <= adjacentTurn turn i) :
    Figure9AdjacentLeftContainedData turn i where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData
  left_angle_le_adjacentTurn := hcontained

end Figure9AdjacentExtractedData

namespace Figure9AdjacentLeftContainedData

/-- A locally contained Figure 9 left-angle witness gives the E23 lower bound
for that adjacent pair. -/
theorem adjacentTurn_lower {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftContainedData turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  adjacentTurn_lower_of_figure9DistanceData_left
    D.distanceData D.left_angle_le_adjacentTurn

end Figure9AdjacentLeftContainedData

/-! ## Uniform extraction packages -/

/-- Concrete Figure 8 extraction data plus the uniform central-angle
containment hypothesis required by the angle-to-turn bridge.

The `extractedData` field keeps the selected Figure 8 witnesses available as
data; the uniform containment field is intentionally separate because the
existing bridge theorem asks for containment for any Figure 8 distance package
appearing at the same indices. -/
structure Figure8SeparatedContainmentInterface
    (good : Nat -> Prop) (turn : Nat -> Real) where
  extractedData :
    forall {i j : Nat},
      1 <= i -> i + 1 < j -> j <= 10 ->
      Not (good i) -> Not (good j) ->
        Figure8SeparatedExtractedData
  central_angle_le_separatedTurn :
    forall {i j : Nat} {p qi qj s r : Point},
      1 <= i -> i + 1 < j -> j <= 10 ->
      Not (good i) -> Not (good j) ->
      Figure8DistanceData p qi qj s r ->
        angleAt qi p qj <= separatedTurn turn i j

namespace Figure8SeparatedContainmentInterface

/-- The selected Figure 8 witness, with its containment proof attached. -/
def containedData {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedContainmentInterface good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Figure8SeparatedContainedData turn i j :=
  let D := H.extractedData hi hsep hj hbad_i hbad_j
  D.withContainment
    (H.central_angle_le_separatedTurn hi hsep hj hbad_i hbad_j
      D.distanceData)

/-- Forget the concrete selected-witness interface to the existing
`Lemma10AngleToTurn` Figure 8 bridge. -/
def toAngleToTurnBridge {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedAngleToTurnBridge good turn where
  distance_data := by
    intro i j hi hsep hj hbad_i hbad_j
    let D := H.extractedData hi hsep hj hbad_i hbad_j
    exact ⟨D.p, D.qi, D.qj, D.s, D.r, D.distanceData⟩
  central_angle_le_separatedTurn := by
    intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
    exact H.central_angle_le_separatedTurn hi hsep hj hbad_i hbad_j D

/-- Route the Figure 8 containment interface through the existing wrapper. -/
theorem separatedWindowLowerE22 {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  figure8SeparatedWindowLowerE22_of_angleToTurnBridge
    H.toAngleToTurnBridge

end Figure8SeparatedContainmentInterface

/-- Concrete Figure 9 extraction data plus the uniform left-angle containment
hypothesis required by the angle-to-turn bridge. -/
structure Figure9AdjacentLeftContainmentInterface
    (good : Nat -> Prop) (turn : Nat -> Real) where
  extractedData :
    forall {i : Nat},
      1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
        Figure9AdjacentExtractedData
  left_angle_le_adjacentTurn :
    forall {i : Nat} {p qi qj s r : Point},
      1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
      Figure9DistanceData p qi qj s r ->
        angleAt p qi s <= adjacentTurn turn i

namespace Figure9AdjacentLeftContainmentInterface

/-- The selected Figure 9 witness, with its left-angle containment proof
attached. -/
def containedData {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Figure9AdjacentLeftContainedData turn i :=
  let D := H.extractedData hi hi_next hbad_i hbad_next
  D.withLeftContainment
    (H.left_angle_le_adjacentTurn hi hi_next hbad_i hbad_next
      D.distanceData)

/-- Forget the concrete selected-witness interface to the existing
`Lemma10AngleToTurn` Figure 9 left-angle bridge. -/
def toAngleToTurnBridge {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentLeftAngleToTurnBridge good turn where
  distance_data := by
    intro i hi hi_next hbad_i hbad_next
    let D := H.extractedData hi hi_next hbad_i hbad_next
    exact ⟨D.p, D.qi, D.qj, D.s, D.r, D.distanceData⟩
  left_angle_le_adjacentTurn := by
    intro i p qi qj s r hi hi_next hbad_i hbad_next D
    exact H.left_angle_le_adjacentTurn hi hi_next hbad_i hbad_next D

/-- Route the Figure 9 containment interface through the existing wrapper. -/
theorem adjacentWindowLowerE23 {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  figure9AdjacentWindowLowerE23_of_leftAngleToTurnBridge
    H.toAngleToTurnBridge

end Figure9AdjacentLeftContainmentInterface

/-! ## Combined routing to E22/E23 -/

/-- The combined concrete angle-containment interface for the two remaining
Lemma 10 angle-to-turn obligations. -/
structure AngleContainmentBridges
    (good : Nat -> Prop) (turn : Nat -> Real) where
  figure8 : Figure8SeparatedContainmentInterface good turn
  figure9 : Figure9AdjacentLeftContainmentInterface good turn

namespace AngleContainmentBridges

/-- Forget the concrete interface to the pair of existing angle-to-turn bridge
records. -/
def toAngleToTurnBridges {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AngleContainmentBridges good turn) :
    Figure8SeparatedAngleToTurnBridge good turn /\
      Figure9AdjacentLeftAngleToTurnBridge good turn :=
  And.intro H.figure8.toAngleToTurnBridge H.figure9.toAngleToTurnBridge

/-- Route the concrete containment interface through
`Lemma10AngleToTurn.E22_E23_of_angleToTurnBridges`. -/
theorem E22_E23 {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AngleContainmentBridges good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  E22_E23_of_angleToTurnBridges
    H.figure8.toAngleToTurnBridge H.figure9.toAngleToTurnBridge

/-- Projection of `AngleContainmentBridges.E22_E23` to the separated-window
lower bound. -/
theorem E22 {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AngleContainmentBridges good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  (H.E22_E23).1

/-- Projection of `AngleContainmentBridges.E22_E23` to the adjacent-window
lower bound. -/
theorem E23 {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AngleContainmentBridges good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  (H.E22_E23).2

end AngleContainmentBridges

end AngleContainmentInterface
end Swanepoel
end ErdosProblems1066

end
