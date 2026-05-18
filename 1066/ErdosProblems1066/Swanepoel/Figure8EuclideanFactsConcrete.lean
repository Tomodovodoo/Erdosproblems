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

/-! ## Selected separated-window Euclidean facts -/

/-- Dot-product, square-distance, and angle consequences extracted from a
concrete Figure 8 distance package. -/
structure Figure8DistanceEuclideanFacts (p qi qj s r : Point) : Prop where
  dotFacts : Figure8DotFacts p qi qj s r
  central_left_sqDist_eq_one : sqDist qi p = 1
  central_right_sqDist_eq_one : sqDist qj p = 1
  central_sqDist_ge_one : 1 <= sqDist qi qj
  comparison_sqDist_ge_one : 1 <= sqDist s r
  central_dotAt_le_half : dotAt qi p qj <= 1 / 2
  central_angle_lower : Real.pi / 3 <= angleAt qi p qj

/-- Figure 8 distance data supplies all reusable Euclidean facts needed by the
separated-window route. -/
def euclideanFacts_of_distanceData {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r) :
    Figure8DistanceEuclideanFacts p qi qj s r where
  dotFacts := dotFacts D
  central_left_sqDist_eq_one := central_left_sqDist_eq_one D
  central_right_sqDist_eq_one := central_right_sqDist_eq_one D
  central_sqDist_ge_one := central_sqDist_ge_one D
  comparison_sqDist_ge_one := comparison_sqDist_ge_one D
  central_dotAt_le_half := central_dotAt_le_half D
  central_angle_lower := central_angle_lower D

/-- A selected Figure 8 separated witness together with its derived Euclidean
facts and the explicit central-angle containment in the separated turn
window. -/
structure Figure8SeparatedEuclideanFacts
    (turn : Nat -> Real) (i j : Nat) where
  p : Point
  qi : Point
  qj : Point
  s : Point
  r : Point
  distanceData : Figure8DistanceData p qi qj s r
  euclideanFacts : Figure8DistanceEuclideanFacts p qi qj s r
  central_angle_le_separatedTurn :
    angleAt qi p qj <= separatedTurn turn i j

/-- Build the selected separated Figure 8 fact package from raw distance data
and the existing central-angle containment proof. -/
def separatedFacts_of_distanceContainment
    {turn : Nat -> Real} {i j : Nat} {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r)
    (hcontained : angleAt qi p qj <= separatedTurn turn i j) :
    Figure8SeparatedEuclideanFacts turn i j where
  p := p
  qi := qi
  qj := qj
  s := s
  r := r
  distanceData := D
  euclideanFacts := euclideanFacts_of_distanceData D
  central_angle_le_separatedTurn := hcontained

namespace Figure8SeparatedEuclideanFacts

/-- The derived central-angle lower bound carried by a selected Figure 8 fact
package. -/
theorem central_angle_lower {turn : Nat -> Real} {i j : Nat}
    (D : Figure8SeparatedEuclideanFacts turn i j) :
    Real.pi / 3 <= angleAt D.qi D.p D.qj :=
  D.euclideanFacts.central_angle_lower

/-- The selected Figure 8 package implies the local separated-window lower
bound. -/
theorem separatedTurn_lower {turn : Nat -> Real} {i j : Nat}
    (D : Figure8SeparatedEuclideanFacts turn i j) :
    Real.pi / 3 <= separatedTurn turn i j :=
  le_trans D.central_angle_lower D.central_angle_le_separatedTurn

/-- Forget the selected Euclidean fact package to the contained-data record
used by the existing Figure 8 containment layer. -/
def toContainedData {turn : Nat -> Real} {i j : Nat}
    (D : Figure8SeparatedEuclideanFacts turn i j) :
    Figure8SeparatedContainedData turn i j where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData
  central_angle_le_separatedTurn := D.central_angle_le_separatedTurn

/-- Forget the selected package to the existential window-geometry witness. -/
def toWindowWitness {turn : Nat -> Real} {i j : Nat}
    (D : Figure8SeparatedEuclideanFacts turn i j) :
    Exists fun p : Point =>
    Exists fun qi : Point =>
    Exists fun qj : Point =>
    Exists fun s : Point =>
    Exists fun r : Point =>
      Figure8DistanceData p qi qj s r /\
        angleAt qi p qj <= separatedTurn turn i j :=
  Figure8ContainmentConcrete.windowWitness_of_containedData
    D.toContainedData

end Figure8SeparatedEuclideanFacts

/-- Extract selected Figure 8 Euclidean facts from an already-contained
Figure 8 separated witness. -/
def separatedFacts_of_containedData
    {turn : Nat -> Real} {i j : Nat}
    (D : Figure8SeparatedContainedData turn i j) :
    Figure8SeparatedEuclideanFacts turn i j where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData
  euclideanFacts := euclideanFacts_of_distanceData D.distanceData
  central_angle_le_separatedTurn := D.central_angle_le_separatedTurn

/-- Uniform selected Figure 8 Euclidean facts for every separated failed pair
in the Lemma 10 window. -/
def Figure8SeparatedEuclideanFactWitnesses
    (good : Nat -> Prop) (turn : Nat -> Real) : Type :=
  forall {i j : Nat},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not (good i) -> Not (good j) ->
      Figure8SeparatedEuclideanFacts turn i j

/-- Forget selected Euclidean fact witnesses to the contained-witness
predicate from `Figure8ContainmentConcrete`. -/
def containedWitnesses_of_euclideanFactWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedEuclideanFactWitnesses good turn) :
    Figure8SeparatedContainedWitnesses good turn :=
  fun {i j} hi hsep hj hbad_i hbad_j =>
    (H (i := i) (j := j) hi hsep hj hbad_i hbad_j).toContainedData

/-- Uniform selected Euclidean fact witnesses supply the Figure 8 separated
window-geometry predicate. -/
def windowGeometry_of_euclideanFactWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedEuclideanFactWitnesses good turn) :
    Figure8SeparatedWindowGeometry good turn :=
  Figure8ContainmentConcrete.windowGeometry_of_containedWitnesses
    (containedWitnesses_of_euclideanFactWitnesses H)

/-- Uniform selected Euclidean fact witnesses imply the named E22 lower-bound
hypothesis. -/
theorem E22_of_euclideanFactWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedEuclideanFactWitnesses good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  Figure8ContainmentConcrete.E22_of_containedWitnesses
    (containedWitnesses_of_euclideanFactWitnesses H)

/-- The same E22 conclusion, proved directly from each selected witness's
central-angle lower bound and containment proof. -/
theorem E22_of_euclideanFactWitnesses_direct
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedEuclideanFactWitnesses good turn) :
    Figure8SeparatedWindowLowerE22 good turn := by
  intro i j hi hsep hj hbad_i hbad_j
  exact
    (H (i := i) (j := j) hi hsep hj hbad_i hbad_j).separatedTurn_lower

/-- Convert explicit selected Figure 8 containment into selected Euclidean
fact witnesses. -/
def euclideanFactWitnesses_of_windowContainment
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedWindowContainment good turn) :
    Figure8SeparatedEuclideanFactWitnesses good turn :=
  fun {i j} hi hsep hj hbad_i hbad_j =>
    separatedFacts_of_containedData
      (H.data (i := i) (j := j) hi hsep hj hbad_i hbad_j)

/-- Convert the stronger containment interface into selected Euclidean fact
witnesses. -/
def euclideanFactWitnesses_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedEuclideanFactWitnesses good turn :=
  euclideanFactWitnesses_of_windowContainment
    (Figure8SeparatedWindowContainment.ofContainmentInterface H)

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

/-- Selected Figure 8 Euclidean fact witnesses specialized to the local
`m = 8` predicate package. -/
def M8Figure8SeparatedEuclideanFactWitnesses
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Type :=
  Figure8SeparatedEuclideanFactWitnesses (M8BrokenLatticeGood P) turn

/-- Selected Figure 8 Euclidean fact witnesses specialized to an honest local
`m = 8` package. -/
abbrev HonestFigure8SeparatedEuclideanFactWitnesses
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) :=
  M8Figure8SeparatedEuclideanFactWitnesses P.data turn

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

/-- Selected `m = 8` Figure 8 Euclidean fact witnesses give the local E22
hypothesis. -/
theorem m8Figure8SeparatedWindowLowerE22_of_euclideanFactWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure8SeparatedEuclideanFactWitnesses P turn) :
    M8Figure8SeparatedWindowLowerE22 P turn :=
  E22_of_euclideanFactWitnesses H

/-- Selected honest Figure 8 Euclidean fact witnesses give the honest E22
hypothesis. -/
theorem honestFigure8SeparatedWindowLowerE22_of_euclideanFactWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedEuclideanFactWitnesses P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn :=
  E22_of_euclideanFactWitnesses H

/-! ## Failed-label adapters for honest `m = 8` packages -/

/-- A failed honest label equality is a failed named local comparison. -/
theorem not_m8BrokenLatticeGood_of_not_m8LabelGood
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {i : Nat}
    (hbad : Not (M8LabelGood P.data.labels i)) :
    Not (M8BrokenLatticeGood P.data i) := by
  intro hgood
  exact hbad ((P.good_iff_labelGood i).1 hgood)

/-- Select Figure 8 Euclidean facts from separated failed label
equalities. -/
def honestSeparatedEuclideanFacts_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedEuclideanFactWitnesses P turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_j : Not (M8LabelGood P.data.labels j)) :
    Figure8SeparatedEuclideanFacts turn i j :=
  H hi hsep hj
    (not_m8BrokenLatticeGood_of_not_m8LabelGood hbad_i)
    (not_m8BrokenLatticeGood_of_not_m8LabelGood hbad_j)

/-- Convert honest Figure 8 window containment into selected Euclidean facts
at separated failed label equalities. -/
def honestSeparatedEuclideanFacts_of_windowContainment_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedWindowContainment P turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_j : Not (M8LabelGood P.data.labels j)) :
    Figure8SeparatedEuclideanFacts turn i j :=
  honestSeparatedEuclideanFacts_of_labelFailures
    (euclideanFactWitnesses_of_windowContainment H)
    hi hsep hj hbad_i hbad_j

/-- Select Figure 8 contained data from separated failed label equalities. -/
def honestContainedData_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedWindowContainment P turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_j : Not (M8LabelGood P.data.labels j)) :
    Figure8SeparatedContainedData turn i j :=
  (honestSeparatedEuclideanFacts_of_windowContainment_labelFailures H
    hi hsep hj hbad_i hbad_j).toContainedData

/-- Project the raw Figure 8 distance witness selected by separated failed
label equalities. -/
def honestExtractedData_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedWindowContainment P turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_j : Not (M8LabelGood P.data.labels j)) :
    Figure8SeparatedExtractedData where
  p := (honestContainedData_of_labelFailures H hi hsep hj
    hbad_i hbad_j).p
  qi := (honestContainedData_of_labelFailures H hi hsep hj
    hbad_i hbad_j).qi
  qj := (honestContainedData_of_labelFailures H hi hsep hj
    hbad_i hbad_j).qj
  s := (honestContainedData_of_labelFailures H hi hsep hj
    hbad_i hbad_j).s
  r := (honestContainedData_of_labelFailures H hi hsep hj
    hbad_i hbad_j).r
  distanceData := (honestContainedData_of_labelFailures H hi hsep hj
    hbad_i hbad_j).distanceData

/-- Project the concrete Figure 8 distance package selected by separated
failed label equalities. -/
theorem honestDistanceData_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedWindowContainment P turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_j : Not (M8LabelGood P.data.labels j)) :
    Figure8DistanceData
      (honestContainedData_of_labelFailures H hi hsep hj
        hbad_i hbad_j).p
      (honestContainedData_of_labelFailures H hi hsep hj
        hbad_i hbad_j).qi
      (honestContainedData_of_labelFailures H hi hsep hj
        hbad_i hbad_j).qj
      (honestContainedData_of_labelFailures H hi hsep hj
        hbad_i hbad_j).s
      (honestContainedData_of_labelFailures H hi hsep hj
        hbad_i hbad_j).r :=
  (honestContainedData_of_labelFailures H hi hsep hj
    hbad_i hbad_j).distanceData

/-- Project the central-angle containment selected by separated failed label
equalities. -/
theorem honest_central_angle_le_separatedTurn_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedWindowContainment P turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_j : Not (M8LabelGood P.data.labels j)) :
    angleAt
        (honestContainedData_of_labelFailures H hi hsep hj
          hbad_i hbad_j).qi
        (honestContainedData_of_labelFailures H hi hsep hj
          hbad_i hbad_j).p
        (honestContainedData_of_labelFailures H hi hsep hj
          hbad_i hbad_j).qj <=
      separatedTurn turn i j :=
  (honestContainedData_of_labelFailures H hi hsep hj
    hbad_i hbad_j).central_angle_le_separatedTurn

/-- The selected Figure 8 distance package from separated failed labels gives
the central-angle lower bound. -/
theorem honestCentralAngle_lower_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedWindowContainment P turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_j : Not (M8LabelGood P.data.labels j)) :
    Real.pi / 3 <=
      angleAt
        (honestContainedData_of_labelFailures H hi hsep hj
          hbad_i hbad_j).qi
        (honestContainedData_of_labelFailures H hi hsep hj
          hbad_i hbad_j).p
        (honestContainedData_of_labelFailures H hi hsep hj
          hbad_i hbad_j).qj :=
  (honestSeparatedEuclideanFacts_of_windowContainment_labelFailures H
    hi hsep hj hbad_i hbad_j).central_angle_lower

/-- Separated failed label equalities force the honest Figure 8 E22 lower
bound pointwise. -/
theorem honestSeparatedTurn_lower_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedWindowContainment P turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_j : Not (M8LabelGood P.data.labels j)) :
    Real.pi / 3 <= separatedTurn turn i j :=
  (honestSeparatedEuclideanFacts_of_windowContainment_labelFailures H
    hi hsep hj hbad_i hbad_j).separatedTurn_lower

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

/-- The Figure 8 part of an M8 window-containment package as selected
Euclidean fact witnesses. -/
def honestEuclideanFactWitnesses_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedEuclideanFactWitnesses
      localLabels.predicates turnBounds.turn :=
  euclideanFactWitnesses_of_containmentInterface W.figure8

/-- Select Figure 8 Euclidean facts from an M8 window-containment package
using separated failed label equalities. -/
def honestSeparatedEuclideanFacts_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_j :
      Not (M8LabelGood localLabels.predicates.data.labels j)) :
    Figure8SeparatedEuclideanFacts turnBounds.turn i j :=
  honestSeparatedEuclideanFacts_of_labelFailures
    (honestEuclideanFactWitnesses_of_m8WindowContainment W)
    hi hsep hj hbad_i hbad_j

/-- Select Figure 8 contained data from an M8 window-containment package using
separated failed label equalities. -/
def honestContainedData_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_j :
      Not (M8LabelGood localLabels.predicates.data.labels j)) :
    Figure8SeparatedContainedData turnBounds.turn i j :=
  (honestSeparatedEuclideanFacts_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).toContainedData

/-- Project the raw Figure 8 distance witness from an M8 window-containment
package using separated failed label equalities. -/
def honestExtractedData_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_j :
      Not (M8LabelGood localLabels.predicates.data.labels j)) :
    Figure8SeparatedExtractedData where
  p := (honestContainedData_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).p
  qi := (honestContainedData_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).qi
  qj := (honestContainedData_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).qj
  s := (honestContainedData_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).s
  r := (honestContainedData_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).r
  distanceData := (honestContainedData_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).distanceData

/-- Project the concrete Figure 8 distance package from an M8
window-containment package using separated failed label equalities. -/
theorem honestDistanceData_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_j :
      Not (M8LabelGood localLabels.predicates.data.labels j)) :
    Figure8DistanceData
      (honestContainedData_of_m8WindowContainment_labelFailures W
        hi hsep hj hbad_i hbad_j).p
      (honestContainedData_of_m8WindowContainment_labelFailures W
        hi hsep hj hbad_i hbad_j).qi
      (honestContainedData_of_m8WindowContainment_labelFailures W
        hi hsep hj hbad_i hbad_j).qj
      (honestContainedData_of_m8WindowContainment_labelFailures W
        hi hsep hj hbad_i hbad_j).s
      (honestContainedData_of_m8WindowContainment_labelFailures W
        hi hsep hj hbad_i hbad_j).r :=
  (honestContainedData_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).distanceData

/-- Project the selected central-angle containment from an M8
window-containment package using separated failed label equalities. -/
theorem
    honest_central_angle_le_separatedTurn_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_j :
      Not (M8LabelGood localLabels.predicates.data.labels j)) :
    angleAt
        (honestContainedData_of_m8WindowContainment_labelFailures W
          hi hsep hj hbad_i hbad_j).qi
        (honestContainedData_of_m8WindowContainment_labelFailures W
          hi hsep hj hbad_i hbad_j).p
        (honestContainedData_of_m8WindowContainment_labelFailures W
          hi hsep hj hbad_i hbad_j).qj <=
      separatedTurn turnBounds.turn i j :=
  (honestContainedData_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).central_angle_le_separatedTurn

/-- The selected Figure 8 distance package from an M8 window-containment
package and separated failed label equalities gives the central-angle lower
bound. -/
theorem honestCentralAngle_lower_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_j :
      Not (M8LabelGood localLabels.predicates.data.labels j)) :
    Real.pi / 3 <=
      angleAt
        (honestContainedData_of_m8WindowContainment_labelFailures W
          hi hsep hj hbad_i hbad_j).qi
        (honestContainedData_of_m8WindowContainment_labelFailures W
          hi hsep hj hbad_i hbad_j).p
        (honestContainedData_of_m8WindowContainment_labelFailures W
          hi hsep hj hbad_i hbad_j).qj :=
  (honestSeparatedEuclideanFacts_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).central_angle_lower

/-- Projection to honest E22 through the explicit Euclidean fact package. -/
theorem honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  (honestExplicitEuclideanFacts_of_m8WindowContainment W).E22

/-- Pointwise honest E22 projection from an M8 window-containment package,
stated for separated failed label equalities. -/
theorem honestFigure8SeparatedWindowLowerE22_apply_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_j :
      Not (M8LabelGood localLabels.predicates.data.labels j)) :
    Real.pi / 3 <= separatedTurn turnBounds.turn i j :=
  (honestSeparatedEuclideanFacts_of_m8WindowContainment_labelFailures W
    hi hsep hj hbad_i hbad_j).separatedTurn_lower

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
