import ErdosProblems1066.Swanepoel.BoundaryAngleCertificatesConcrete
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

/-! ## Figure 9 left-angle upper bounds from cosine data -/

/-- If two unit sides have dot product at least the cosine of a turn value in
`[0, pi]`, the concrete angle at the unit-side vertex is bounded by that turn.

This is the monotone-cosine half of the law-of-cosines route needed for the
remaining Figure 9 middle-turn upper-bound row. -/
theorem angleAt_le_of_unit_sides_cos_turn_le_dotAt
    {a b c : Point} {theta : Real}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (htheta_nonneg : 0 <= theta) (htheta_le_pi : theta <= Real.pi)
    (hcos_le_dot : Real.cos theta <= dotAt a b c) :
    angleAt a b c <= theta := by
  have hangle_mem : Set.Icc 0 Real.pi (angleAt a b c) :=
    angleAt_mem_Icc_zero_pi a b c
  have htheta_mem : Set.Icc 0 Real.pi theta :=
    Set.mem_Icc.mpr ⟨htheta_nonneg, htheta_le_pi⟩
  have hcos_angle :
      Real.cos (angleAt a b c) = dotAt a b c :=
    cos_angleAt_eq_dotAt_of_unit_sides hab hcb
  have hcos :
      Real.cos theta <= Real.cos (angleAt a b c) := by
    simpa [hcos_angle] using hcos_le_dot
  exact (Real.strictAntiOn_cos.le_iff_ge htheta_mem hangle_mem).mp hcos

/-- On `[0, pi]`, a unit-side angle is at most `theta` exactly when its dot
product is at least `cos theta`. -/
theorem angleAt_le_iff_cos_turn_le_dotAt_of_unit_sides
    {a b c : Point} {theta : Real}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (htheta_nonneg : 0 <= theta) (htheta_le_pi : theta <= Real.pi) :
    angleAt a b c <= theta <-> Real.cos theta <= dotAt a b c := by
  have hangle_mem : Set.Icc 0 Real.pi (angleAt a b c) :=
    angleAt_mem_Icc_zero_pi a b c
  have htheta_mem : Set.Icc 0 Real.pi theta :=
    Set.mem_Icc.mpr (And.intro htheta_nonneg htheta_le_pi)
  have hcos_angle :
      Real.cos (angleAt a b c) = dotAt a b c :=
    cos_angleAt_eq_dotAt_of_unit_sides hab hcb
  constructor
  · intro hangle_le
    have hcos :
        Real.cos theta <= Real.cos (angleAt a b c) :=
      (Real.strictAntiOn_cos.le_iff_ge htheta_mem hangle_mem).mpr
        hangle_le
    simpa [hcos_angle] using hcos
  · intro hcos_le_dot
    exact angleAt_le_of_unit_sides_cos_turn_le_dotAt
      hab hcb htheta_nonneg htheta_le_pi hcos_le_dot

/-- Unit-side law-of-cosines algebra: an upper bound on the base squared
distance gives the cosine comparison required for the angle upper bound. -/
theorem cos_turn_le_dotAt_of_unit_sides_sqDist_le_turnChord
    {a b c : Point} {theta : Real}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hbase :
      sqDist a c <= 2 - 2 * Real.cos theta) :
    Real.cos theta <= dotAt a b c := by
  have hsq :
      sqDist a c = 2 - 2 * dotAt a b c :=
    sqDist_eq_two_sub_two_dotAt_of_unit_sides hab hcb
  have hbase' :
      2 - 2 * dotAt a b c <= 2 - 2 * Real.cos theta := by
    simpa [hsq] using hbase
  nlinarith

/-- Unit-side law-of-cosines algebra in the opposite direction: the cosine
comparison gives the matching upper bound on the base squared distance. -/
theorem sqDist_le_turnChord_of_unit_sides_cos_turn_le_dotAt
    {a b c : Point} {theta : Real}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hcos_le_dot : Real.cos theta <= dotAt a b c) :
    sqDist a c <= 2 - 2 * Real.cos theta := by
  have hsq :
      sqDist a c = 2 - 2 * dotAt a b c :=
    sqDist_eq_two_sub_two_dotAt_of_unit_sides hab hcb
  nlinarith

/-- For unit sides, the cosine comparison and the corresponding turn-chord
bound are equivalent. -/
theorem cos_turn_le_dotAt_iff_sqDist_le_turnChord_of_unit_sides
    {a b c : Point} {theta : Real}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1) :
    Real.cos theta <= dotAt a b c <->
      sqDist a c <= 2 - 2 * Real.cos theta :=
  Iff.intro
    (fun hcos_le_dot =>
      sqDist_le_turnChord_of_unit_sides_cos_turn_le_dotAt
        hab hcb hcos_le_dot)
    (fun hbase =>
      cos_turn_le_dotAt_of_unit_sides_sqDist_le_turnChord
        hab hcb hbase)

/-- Law-of-cosines form of the Figure 9 angle upper criterion: for unit sides,
if the base chord is at most the chord cut out by `theta`, and `theta` is in
`[0, pi]`, then the geometric angle is at most `theta`. -/
theorem angleAt_le_of_unit_sides_sqDist_le_turnChord
    {a b c : Point} {theta : Real}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (htheta_nonneg : 0 <= theta) (htheta_le_pi : theta <= Real.pi)
    (hbase :
      sqDist a c <= 2 - 2 * Real.cos theta) :
    angleAt a b c <= theta :=
  angleAt_le_of_unit_sides_cos_turn_le_dotAt
    hab hcb htheta_nonneg htheta_le_pi
    (cos_turn_le_dotAt_of_unit_sides_sqDist_le_turnChord
      hab hcb hbase)

/-- For unit sides and `theta` in `[0, pi]`, the angle upper bound is
equivalent to the corresponding turn-chord upper bound. -/
theorem angleAt_le_iff_sqDist_le_turnChord_of_unit_sides
    {a b c : Point} {theta : Real}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (htheta_nonneg : 0 <= theta) (htheta_le_pi : theta <= Real.pi) :
    angleAt a b c <= theta <->
      sqDist a c <= 2 - 2 * Real.cos theta :=
  (angleAt_le_iff_cos_turn_le_dotAt_of_unit_sides
    hab hcb htheta_nonneg htheta_le_pi).trans
    (cos_turn_le_dotAt_iff_sqDist_le_turnChord_of_unit_sides hab hcb)

/-- If the Figure 9 left comparison angle is bounded by a concrete turn value
in `[0, pi]`, the corresponding pointwise cosine comparison follows. -/
theorem cos_turn_le_left_dotAt_of_distanceData_leftAngle_le
    {theta : Real} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (htheta_nonneg : 0 <= theta) (htheta_le_pi : theta <= Real.pi)
    (hangle : angleAt p qi s <= theta) :
    Real.cos theta <= dotAt p qi s :=
  (angleAt_le_iff_cos_turn_le_dotAt_of_unit_sides
    (sqDist_eq_one_of_eucUnit D.p_qi)
    (sqDist_eq_one_of_eucUnit (eucUnit_comm D.qi_s))
    htheta_nonneg htheta_le_pi).mp hangle

/-- If the Figure 9 left comparison angle is bounded by a concrete turn value
in `[0, pi]`, the law-of-cosines turn-chord comparison follows. -/
theorem left_sqDist_le_turnChord_of_distanceData_leftAngle_le
    {theta : Real} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (htheta_nonneg : 0 <= theta) (htheta_le_pi : theta <= Real.pi)
    (hangle : angleAt p qi s <= theta) :
    sqDist p s <= 2 - 2 * Real.cos theta :=
  (angleAt_le_iff_sqDist_le_turnChord_of_unit_sides
    (sqDist_eq_one_of_eucUnit D.p_qi)
    (sqDist_eq_one_of_eucUnit (eucUnit_comm D.qi_s))
    htheta_nonneg htheta_le_pi).mp hangle

/-- A concrete boundary turn-angle certificate whose value contains the Figure
9 left comparison angle supplies the pointwise cosine comparison needed by the
turn-angle Figure 9 rows. -/
theorem unitSeparatedAngle_cos_value_le_left_dotAt_of_distanceData_leftAngle_le
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {p qi qj s r : Point}
    (A : BoundaryAngleCertificatesConcrete.UnitSeparatedAngle G)
    (D : Figure9DistanceData p qi qj s r)
    (hangle : angleAt p qi s <= A.value) :
    Real.cos A.value <= dotAt p qi s :=
  cos_turn_le_left_dotAt_of_distanceData_leftAngle_le
    D A.value_nonnegative A.value_le_pi hangle

/-- A concrete boundary turn-angle certificate whose value contains the Figure
9 left comparison angle supplies the law-of-cosines turn-chord comparison
needed by the turn-angle Figure 9 rows. -/
theorem unitSeparatedAngle_left_sqDist_le_valueChord_of_distanceData_leftAngle_le
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {p qi qj s r : Point}
    (A : BoundaryAngleCertificatesConcrete.UnitSeparatedAngle G)
    (D : Figure9DistanceData p qi qj s r)
    (hangle : angleAt p qi s <= A.value) :
    sqDist p s <= 2 - 2 * Real.cos A.value :=
  left_sqDist_le_turnChord_of_distanceData_leftAngle_le
    D A.value_nonnegative A.value_le_pi hangle

/-- Equality form for the common turn-angle geometry case: if the certified
turn-angle value is exactly the Figure 9 left comparison angle, its cosine is
bounded by the left dot product. -/
theorem unitSeparatedAngle_cos_value_le_left_dotAt_of_distanceData_value_eq_leftAngle
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {p qi qj s r : Point}
    (A : BoundaryAngleCertificatesConcrete.UnitSeparatedAngle G)
    (D : Figure9DistanceData p qi qj s r)
    (hvalue : A.value = angleAt p qi s) :
    Real.cos A.value <= dotAt p qi s :=
  unitSeparatedAngle_cos_value_le_left_dotAt_of_distanceData_leftAngle_le
    A D (by rw [hvalue])

/-- Equality form for the common turn-angle geometry case: if the certified
turn-angle value is exactly the Figure 9 left comparison angle, the matching
turn-chord inequality follows. -/
theorem unitSeparatedAngle_left_sqDist_le_valueChord_of_distanceData_value_eq_leftAngle
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {p qi qj s r : Point}
    (A : BoundaryAngleCertificatesConcrete.UnitSeparatedAngle G)
    (D : Figure9DistanceData p qi qj s r)
    (hvalue : A.value = angleAt p qi s) :
    sqDist p s <= 2 - 2 * Real.cos A.value :=
  unitSeparatedAngle_left_sqDist_le_valueChord_of_distanceData_leftAngle_le
    A D (by rw [hvalue])

/-- Figure 9 left-angle upper bound from a direct cosine comparison with the
middle turn.  The unit-side hypotheses come from the Figure 9 distance data. -/
theorem leftAngle_le_middleTurn_of_distanceData_cos_turn_le_dotAt
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hturn_nonneg : 0 <= turn (i + 1))
    (hturn_le_pi : turn (i + 1) <= Real.pi)
    (hcos_le_dot : Real.cos (turn (i + 1)) <= dotAt p qi s) :
    angleAt p qi s <= turn (i + 1) :=
  angleAt_le_of_unit_sides_cos_turn_le_dotAt
    (sqDist_eq_one_of_eucUnit D.p_qi)
    (sqDist_eq_one_of_eucUnit (eucUnit_comm D.qi_s))
    hturn_nonneg hturn_le_pi hcos_le_dot

/-- Figure 9 left-angle upper bound from the law-of-cosines chord inequality
for the base `p-s`. -/
theorem leftAngle_le_middleTurn_of_distanceData_sqDist_le_turnChord
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hturn_nonneg : 0 <= turn (i + 1))
    (hturn_le_pi : turn (i + 1) <= Real.pi)
    (hbase :
      sqDist p s <= 2 - 2 * Real.cos (turn (i + 1))) :
    angleAt p qi s <= turn (i + 1) :=
  angleAt_le_of_unit_sides_sqDist_le_turnChord
    (sqDist_eq_one_of_eucUnit D.p_qi)
    (sqDist_eq_one_of_eucUnit (eucUnit_comm D.qi_s))
    hturn_nonneg hturn_le_pi hbase

/-- Figure 9 pointwise cosine criterion for bounding the left angle by the
middle turn. -/
theorem leftAngle_le_middleTurn_iff_cos_turn_le_dotAt_of_distanceData
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hturn_nonneg : 0 <= turn (i + 1))
    (hturn_le_pi : turn (i + 1) <= Real.pi) :
    angleAt p qi s <= turn (i + 1) <->
      Real.cos (turn (i + 1)) <= dotAt p qi s :=
  angleAt_le_iff_cos_turn_le_dotAt_of_unit_sides
    (sqDist_eq_one_of_eucUnit D.p_qi)
    (sqDist_eq_one_of_eucUnit (eucUnit_comm D.qi_s))
    hturn_nonneg hturn_le_pi

/-- Figure 9 pointwise chord criterion for bounding the left angle by the
middle turn. -/
theorem leftAngle_le_middleTurn_iff_sqDist_le_turnChord_of_distanceData
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hturn_nonneg : 0 <= turn (i + 1))
    (hturn_le_pi : turn (i + 1) <= Real.pi) :
    angleAt p qi s <= turn (i + 1) <->
      sqDist p s <= 2 - 2 * Real.cos (turn (i + 1)) :=
  angleAt_le_iff_sqDist_le_turnChord_of_unit_sides
    (sqDist_eq_one_of_eucUnit D.p_qi)
    (sqDist_eq_one_of_eucUnit (eucUnit_comm D.qi_s))
    hturn_nonneg hturn_le_pi

/-- Uniform cosine rows that imply the remaining Figure 9 middle-turn upper
bound for every adjacent failed pair. -/
def Figure9AdjacentLeftCosineTurnRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
    Figure9DistanceData p qi qj s r ->
      0 <= turn (i + 1) /\
      turn (i + 1) <= Real.pi /\
      Real.cos (turn (i + 1)) <= dotAt p qi s

/-- Uniform chord rows: the law-of-cosines distance form of
`Figure9AdjacentLeftCosineTurnRows`. -/
def Figure9AdjacentLeftTurnChordRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
    Figure9DistanceData p qi qj s r ->
      0 <= turn (i + 1) /\
      turn (i + 1) <= Real.pi /\
      sqDist p s <= 2 - 2 * Real.cos (turn (i + 1))

/-- A single middle turn in a legal adjacent Figure 9 window is at most `pi`
under the usual nonnegative total-turn budget. -/
theorem middleTurn_le_pi_of_totalTurn_lt_pi_div_three
    {turn : Nat -> Real} {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3) :
    turn (i + 1) <= Real.pi := by
  have hsub : ({i + 1} : Finset Nat) <= turnIndexSet := by
    intro k hk
    have hk_eq : k = i + 1 := by
      simpa using hk
    subst k
    exact Finset.mem_Icc.mpr (And.intro (by omega) (by omega))
  have hsingle_le_total :
      ({i + 1} : Finset Nat).sum turn <= totalTurn turn :=
    sum_le_totalTurn_of_subset hsub hnonneg
  have hturn_le_total : turn (i + 1) <= totalTurn turn := by
    simpa using hsingle_le_total
  have hthird_le_pi : Real.pi / 3 <= Real.pi := by
    nlinarith [Real.pi_pos]
  exact le_trans hturn_le_total (le_trans (le_of_lt htotal) hthird_le_pi)

/-- The nonnegative total-turn budget supplies the `[0, pi]` range needed by
the cosine/chord middle-turn criteria. -/
theorem middleTurn_mem_Icc_zero_pi_of_totalTurn_lt_pi_div_three
    {turn : Nat -> Real} {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3) :
    Set.Icc 0 Real.pi (turn (i + 1)) :=
  Set.mem_Icc.mpr
    (And.intro (hnonneg (i + 1))
      (middleTurn_le_pi_of_totalTurn_lt_pi_div_three
        hi hi_next hnonneg htotal))

/-- A cosine row can be restated as the equivalent turn-chord row by the
unit-side law of cosines from the Figure 9 distance package. -/
theorem turnChordRows_of_cosineTurnRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftCosineTurnRows good turn) :
    Figure9AdjacentLeftTurnChordRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  have hrow := H hi hi_next hbad_i hbad_next D
  exact And.intro hrow.1
    (And.intro hrow.2.1
      (sqDist_le_turnChord_of_unit_sides_cos_turn_le_dotAt
        (sqDist_eq_one_of_eucUnit D.p_qi)
        (sqDist_eq_one_of_eucUnit (eucUnit_comm D.qi_s))
        hrow.2.2))

/-- A turn-chord row can be restated as the equivalent cosine row by the
unit-side law of cosines from the Figure 9 distance package. -/
theorem cosineTurnRows_of_turnChordRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftTurnChordRows good turn) :
    Figure9AdjacentLeftCosineTurnRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  have hrow := H hi hi_next hbad_i hbad_next D
  exact And.intro hrow.1
    (And.intro hrow.2.1
      (cos_turn_le_dotAt_of_unit_sides_sqDist_le_turnChord
        (sqDist_eq_one_of_eucUnit D.p_qi)
        (sqDist_eq_one_of_eucUnit (eucUnit_comm D.qi_s))
        hrow.2.2))

/-- The cosine and turn-chord row surfaces are equivalent for Figure 9
adjacent-left distance data. -/
theorem cosineTurnRows_iff_turnChordRows
    {good : Nat -> Prop} {turn : Nat -> Real} :
    Figure9AdjacentLeftCosineTurnRows good turn <->
      Figure9AdjacentLeftTurnChordRows good turn :=
  Iff.intro
    (fun H => turnChordRows_of_cosineTurnRows H)
    (fun H => cosineTurnRows_of_turnChordRows H)

/-- Build cosine-turn rows from the usual total-turn budget and just the
pointwise cosine comparisons. -/
theorem cosineTurnRows_of_totalTurn_and_cosineComparisons
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (Hcos :
      forall {i : Nat} {p qi qj s r : Point},
        1 <= i -> i + 1 <= 10 ->
        Not (good i) -> Not (good (i + 1)) ->
        Figure9DistanceData p qi qj s r ->
          Real.cos (turn (i + 1)) <= dotAt p qi s) :
    Figure9AdjacentLeftCosineTurnRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  exact And.intro (hnonneg (i + 1))
    (And.intro
      (middleTurn_le_pi_of_totalTurn_lt_pi_div_three
        hi hi_next hnonneg htotal)
      (Hcos hi hi_next hbad_i hbad_next D))

/-- Build turn-chord rows from the usual total-turn budget and just the
pointwise chord comparisons. -/
theorem turnChordRows_of_totalTurn_and_chordComparisons
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (Hchord :
      forall {i : Nat} {p qi qj s r : Point},
        1 <= i -> i + 1 <= 10 ->
        Not (good i) -> Not (good (i + 1)) ->
        Figure9DistanceData p qi qj s r ->
          sqDist p s <= 2 - 2 * Real.cos (turn (i + 1))) :
    Figure9AdjacentLeftTurnChordRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  exact And.intro (hnonneg (i + 1))
    (And.intro
      (middleTurn_le_pi_of_totalTurn_lt_pi_div_three
        hi hi_next hnonneg htotal)
      (Hchord hi hi_next hbad_i hbad_next D))

/-- Build the Figure 9 middle-turn angle rows directly from the total-turn
budget and pointwise cosine comparisons. -/
theorem angleLeMiddleTurnRows_of_totalTurn_and_cosineComparisons
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (Hcos :
      forall {i : Nat} {p qi qj s r : Point},
        1 <= i -> i + 1 <= 10 ->
        Not (good i) -> Not (good (i + 1)) ->
        Figure9DistanceData p qi qj s r ->
          Real.cos (turn (i + 1)) <= dotAt p qi s) :
    Figure9AdjacentLeftAngleLeMiddleTurnRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  exact leftAngle_le_middleTurn_of_distanceData_cos_turn_le_dotAt
    D (hnonneg (i + 1))
    (middleTurn_le_pi_of_totalTurn_lt_pi_div_three
      hi hi_next hnonneg htotal)
    (Hcos hi hi_next hbad_i hbad_next D)

/-- Build the Figure 9 middle-turn angle rows directly from the total-turn
budget and pointwise chord comparisons. -/
theorem angleLeMiddleTurnRows_of_totalTurn_and_chordComparisons
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (Hchord :
      forall {i : Nat} {p qi qj s r : Point},
        1 <= i -> i + 1 <= 10 ->
        Not (good i) -> Not (good (i + 1)) ->
        Figure9DistanceData p qi qj s r ->
          sqDist p s <= 2 - 2 * Real.cos (turn (i + 1))) :
    Figure9AdjacentLeftAngleLeMiddleTurnRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  exact leftAngle_le_middleTurn_of_distanceData_sqDist_le_turnChord
    D (hnonneg (i + 1))
    (middleTurn_le_pi_of_totalTurn_lt_pi_div_three
      hi hi_next hnonneg htotal)
    (Hchord hi hi_next hbad_i hbad_next D)

/-- Cosine rows produce the exact pointwise middle-turn upper-bound rows used
by the Figure 9 containment bridge. -/
theorem angleLeMiddleTurnRows_of_cosineTurnRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftCosineTurnRows good turn) :
    Figure9AdjacentLeftAngleLeMiddleTurnRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  rcases H hi hi_next hbad_i hbad_next D with
    ⟨hturn_nonneg, hturn_le_pi, hcos_le_dot⟩
  exact leftAngle_le_middleTurn_of_distanceData_cos_turn_le_dotAt
    D hturn_nonneg hturn_le_pi hcos_le_dot

/-- Chord rows produce the exact pointwise middle-turn upper-bound rows used
by the Figure 9 containment bridge. -/
theorem angleLeMiddleTurnRows_of_turnChordRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftTurnChordRows good turn) :
    Figure9AdjacentLeftAngleLeMiddleTurnRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  rcases H hi hi_next hbad_i hbad_next D with
    ⟨hturn_nonneg, hturn_le_pi, hbase⟩
  exact leftAngle_le_middleTurn_of_distanceData_sqDist_le_turnChord
    D hturn_nonneg hturn_le_pi hbase

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

/-! ## Minimal explicit package for the remaining containment fact -/

/-- Explicit Figure 9 Euclidean data for adjacent failures, together with the
left-angle turn-window fact not forced by the metric data alone.

This is the Figure 9 analogue of `Figure8ExplicitEuclideanFacts`: distance
data supplies the checked Euclidean/trigonometric lower bound, and the
left-angle containment supplies the external turn-window comparison needed for
E23. -/
structure Figure9ExplicitEuclideanFacts
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

namespace Figure9ExplicitEuclideanFacts

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- Forget the explicit facts to the existing Figure 9 left angle-to-turn
bridge. -/
def toAngleToTurnBridge
    (H : Figure9ExplicitEuclideanFacts good turn) :
    Figure9AdjacentLeftAngleToTurnBridge good turn where
  distance_data := by
    intro i hi hi_next hbad_i hbad_next
    exact H.distance_data hi hi_next hbad_i hbad_next
  left_angle_le_adjacentTurn := by
    intro i p qi qj s r hi hi_next hbad_i hbad_next D
    exact H.left_angle_le_adjacentTurn hi hi_next hbad_i hbad_next D

/-- Convert from the existing Figure 9 left angle-to-turn bridge to the
explicit fact package in this file. -/
def ofAngleToTurnBridge
    (H : Figure9AdjacentLeftAngleToTurnBridge good turn) :
    Figure9ExplicitEuclideanFacts good turn where
  distance_data := by
    intro i hi hi_next hbad_i hbad_next
    exact H.distance_data hi hi_next hbad_i hbad_next
  left_angle_le_adjacentTurn := by
    intro i p qi qj s r hi hi_next hbad_i hbad_next D
    exact H.left_angle_le_adjacentTurn hi hi_next hbad_i hbad_next D

/-- Convert from the concrete Figure 9 left-containment interface. -/
def ofContainmentInterface
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9ExplicitEuclideanFacts good turn where
  distance_data := by
    intro i hi hi_next hbad_i hbad_next
    let D := H.extractedData hi hi_next hbad_i hbad_next
    exact Exists.intro D.p
      (Exists.intro D.qi
        (Exists.intro D.qj
          (Exists.intro D.s
            (Exists.intro D.r D.distanceData))))
  left_angle_le_adjacentTurn := by
    intro i p qi qj s r hi hi_next hbad_i hbad_next D
    exact H.left_angle_le_adjacentTurn hi hi_next hbad_i hbad_next D

/-- The explicit Figure 9 facts yield the named E23 lower-bound interface by
using the checked left-angle lower bound from the selected distance data. -/
theorem E23
    (H : Figure9ExplicitEuclideanFacts good turn) :
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
            exact adjacentTurn_lower_of_distanceData_leftContainment D
              (H.left_angle_le_adjacentTurn
                hi hi_next hbad_i hbad_next D)

/-- Pointwise form of the E23 lower-bound projection. -/
theorem E23_apply
    (H : Figure9ExplicitEuclideanFacts good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Real.pi / 3 <= adjacentTurn turn i :=
  H.E23 hi hi_next hbad_i hbad_next

/-- The concrete Figure 9 left-containment interface yields E23 through the
explicit Euclidean fact package. -/
theorem E23_of_containmentInterface
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  (ofContainmentInterface H).E23

end Figure9ExplicitEuclideanFacts

/-! ## Honest M8 projections -/

/-- Explicit Figure 9 Euclidean facts specialized to the local `m = 8`
predicate package. -/
def M8Figure9ExplicitEuclideanFacts
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Prop :=
  Figure9ExplicitEuclideanFacts (M8BrokenLatticeGood P) turn

/-- Explicit Figure 9 Euclidean facts specialized to an honest local `m = 8`
package. -/
def HonestFigure9ExplicitEuclideanFacts
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Prop :=
  M8Figure9ExplicitEuclideanFacts P.data turn

/-- Explicit `m = 8` Figure 9 facts give the local E23 hypothesis. -/
theorem m8Figure9AdjacentWindowLowerE23_of_explicitEuclideanFacts
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure9ExplicitEuclideanFacts P turn) :
    M8Figure9AdjacentWindowLowerE23 P turn :=
  H.E23

/-- Explicit honest Figure 9 facts give the honest E23 hypothesis. -/
theorem honestFigure9AdjacentWindowLowerE23_of_explicitEuclideanFacts
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9ExplicitEuclideanFacts P turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  H.E23

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

/-- The Figure 9 field of an M8 window-containment package as the explicit
Euclidean fact package in this file. -/
def honestExplicitEuclideanFacts_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9ExplicitEuclideanFacts
      localLabels.predicates turnBounds.turn :=
  Figure9ExplicitEuclideanFacts.ofContainmentInterface W.figure9_left

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

/-- Projection to honest E23 through the explicit Euclidean fact package. -/
theorem honestFigure9AdjacentWindowLowerE23_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  (honestExplicitEuclideanFacts_of_m8WindowContainment W).E23

/-- Pointwise honest E23 projection from an M8 window-containment package,
stated for adjacent failed label equalities. -/
theorem honestFigure9AdjacentWindowLowerE23_apply_of_m8WindowContainment_labelFailures
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
