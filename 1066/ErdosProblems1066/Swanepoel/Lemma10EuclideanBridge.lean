import ErdosProblems1066.Swanepoel.AngleBridgeFacts
import ErdosProblems1066.Swanepoel.Lemma10AnalyticBridge

/-!
# Swanepoel Lemma 10 Euclidean bridge

This module bridges the concrete Figure 8/Figure 9 distance packages to the
named E22/E23 turn-window hypotheses from `Lemma10AnalyticBridge`.

The currently available Euclidean files prove distance-to-dot-product algebra,
but they do not yet contain the analytic angle estimate turning those facts
into a lower bound for the appropriate turn window.  Accordingly, the final
bridge structures below expose that remaining analytic step as an explicit
`turn_lower` field.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma10EuclideanBridge

open AngleArithmetic
open AngleBridgeFacts
open Lemma10AnalyticBridge
open Lemma10Inequalities
open TriangleAngleFacts

abbrev Point : Type :=
  AngleBridgeFacts.Point

/-! ## Kernel-checked Euclidean fact packages -/

/-- Dot-product and squared-distance consequences extracted from Figure 8
distance hypotheses. -/
structure Figure8DotFacts (p qi qj s r : Point) : Prop where
  central_dotAt_le_half : dotAt qi p qj <= 1 / 2
  central_sqDist_ge_one : 1 <= sqDist qi qj
  comparison_sqDist_ge_one : 1 <= sqDist s r

/-- Figure 8 distance data implies the dot/squared-distance facts currently
available from the Euclidean algebra library. -/
theorem figure8DotFacts_of_distanceData {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r) :
    Figure8DotFacts p qi qj s r where
  central_dotAt_le_half := D.central_dotAt_le_half
  central_sqDist_ge_one := D.qi_qj_sqDist_ge_one
  comparison_sqDist_ge_one := D.s_r_sqDist_ge_one

/-- Dot-product and squared-distance consequences extracted from Figure 9
distance hypotheses. -/
structure Figure9DotFacts (p qi qj s r : Point) : Prop where
  central_dotAt_le_half : dotAt qi p qj <= 1 / 2
  left_dotAt_le_half : dotAt p qi s <= 1 / 2
  right_dotAt_le_half : dotAt p qj r <= 1 / 2
  left_sqDist_ge_one : 1 <= sqDist p s
  right_sqDist_ge_one : 1 <= sqDist p r
  comparison_sqDist_ge_one : 1 <= sqDist s r

/-- Figure 9 distance data implies the dot/squared-distance facts currently
available from the Euclidean algebra library. -/
theorem figure9DotFacts_of_distanceData {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    Figure9DotFacts p qi qj s r where
  central_dotAt_le_half := D.central_dotAt_le_half
  left_dotAt_le_half := D.left_comparison_dotAt_le_half
  right_dotAt_le_half := D.right_comparison_dotAt_le_half
  left_sqDist_ge_one := D.left_base_sqDist_ge_one
  right_sqDist_ge_one := D.right_base_sqDist_ge_one
  comparison_sqDist_ge_one := D.comparison_chord_sqDist_ge_one

/-! ## Figure 8 to E22 -/

/-- Honest Figure 8 Euclidean bridge data for separated failed comparisons.

The `distance_data` field supplies the concrete Figure 8 configuration for
each separated pair of failures.  The `turn_lower` field is the remaining
analytic angle estimate: it states that the dot/squared-distance facts already
proved from those distances imply the E22 turn-window lower bound. -/
structure Figure8SeparatedEuclideanBridge
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
  turn_lower :
    forall {i j : Nat} {p qi qj s r : Point},
      1 <= i -> i + 1 < j -> j <= 10 ->
      Not (good i) -> Not (good j) ->
      Figure8DotFacts p qi qj s r ->
        Real.pi / 3 <= separatedTurn turn i j

/-- Figure 8 Euclidean bridge data yields the named E22 lower-bound shape. -/
theorem figure8SeparatedWindowLowerE22_of_euclideanBridge
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedEuclideanBridge good turn) :
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
            exact H.turn_lower hi hsep hj hbad_i hbad_j
              (figure8DotFacts_of_distanceData D)

/-! ## Figure 9 to E23 -/

/-- Honest Figure 9 Euclidean bridge data for adjacent failed comparisons.

As in the Figure 8 bridge, all distance-to-dot consequences are proved here;
only the analytic conversion from those facts to the turn-window lower bound
remains as the explicit `turn_lower` field. -/
structure Figure9AdjacentEuclideanBridge
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
  turn_lower :
    forall {i : Nat} {p qi qj s r : Point},
      1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
      Figure9DotFacts p qi qj s r ->
        Real.pi / 3 <= adjacentTurn turn i

/-- Figure 9 Euclidean bridge data yields the named E23 lower-bound shape. -/
theorem figure9AdjacentWindowLowerE23_of_euclideanBridge
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentEuclideanBridge good turn) :
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
            exact H.turn_lower hi hi_next hbad_i hbad_next
              (figure9DotFacts_of_distanceData D)

/-- Combined Euclidean bridge to the pair of named analytic hypotheses used by
`Lemma10AnalyticBridge`. -/
theorem E22_E23_of_euclideanBridges
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H8 : Figure8SeparatedEuclideanBridge good turn)
    (H9 : Figure9AdjacentEuclideanBridge good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  And.intro
    (figure8SeparatedWindowLowerE22_of_euclideanBridge H8)
    (figure9AdjacentWindowLowerE23_of_euclideanBridge H9)

end Lemma10EuclideanBridge
end Swanepoel
end ErdosProblems1066

end
