import ErdosProblems1066.PachToth.UnitVectorGeometry
import ErdosProblems1066.PachToth.HingedTransitionInterface
import ErdosProblems1066.PachToth.ConnectorEquationFacts

set_option autoImplicit false

/-!
# Algebra for unit-circle hinge targets

This module collects small reusable algebraic facts for non-rigid
Pach--Toth transition work.  The lemmas are intentionally point-level:
connector targets may be supplied as unit-circle hinge points rather than as
a single rigid translate of the next block.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace HingeAlgebra

open FiniteGraph
open FiniteGraph.LocalVertex
open UnitVectorGeometry

abbrev R2 := Prod Real Real

/-- Squared Euclidean distance, kept algebraic to avoid square roots. -/
def distSq (p q : R2) : Real :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

@[simp]
theorem distSq_self (p : R2) : distSq p p = 0 := by
  simp [distSq]

theorem distSq_comm (p q : R2) : distSq p q = distSq q p := by
  simp [distSq]
  ring

theorem distSq_eq_root_eucDist_sq (p q : R2) :
    distSq p q = _root_.eucDist p q ^ 2 := by
  rw [_root_.eucDist_sq]
  rfl

theorem root_eucDist_eq_one_iff_distSq (p q : R2) :
    _root_.eucDist p q = 1 <-> distSq p q = 1 := by
  rw [_root_.eucDist_eq_one_iff]
  rfl

theorem geometry_eucDist_eq_root_eucDist (p q : R2) :
    ErdosProblems1066.Geometry.Distance.eucDist p q = _root_.eucDist p q :=
  rfl

@[simp]
theorem distSq_center_hingePoint (center : R2) (theta : Real) :
    distSq center (hingePoint center theta) = 1 := by
  dsimp [distSq, hingePoint, add, unitVec]
  ring_nf
  exact Real.cos_sq_add_sin_sq theta

@[simp]
theorem distSq_hingePoint_center (center : R2) (theta : Real) :
    distSq (hingePoint center theta) center = 1 := by
  rw [distSq_comm]
  exact distSq_center_hingePoint center theta

theorem root_eucDist_center_hingePoint (center : R2) (theta : Real) :
    _root_.eucDist center (hingePoint center theta) = 1 := by
  simpa [geometry_eucDist_eq_root_eucDist] using
    UnitVectorGeometry.eucDist_center_hingePoint center theta

theorem root_eucDist_hingePoint_center (center : R2) (theta : Real) :
    _root_.eucDist (hingePoint center theta) center = 1 := by
  simpa [geometry_eucDist_eq_root_eucDist] using
    UnitVectorGeometry.eucDist_hingePoint_center center theta

theorem distSq_unitVec_unitVec (theta phi : Real) :
    distSq (unitVec theta) (unitVec phi) =
      2 - 2 * Real.cos (theta - phi) := by
  simpa [distSq] using UnitVectorGeometry.sqDist_unitVec_unitVec theta phi

theorem distSq_hingePoint_hingePoint_same_center
    (center : R2) (theta phi : Real) :
    distSq (hingePoint center theta) (hingePoint center phi) =
      2 - 2 * Real.cos (theta - phi) := by
  dsimp [distSq, hingePoint, add, unitVec]
  rw [Real.cos_sub]
  nlinarith [Real.cos_sq_add_sin_sq theta, Real.cos_sq_add_sin_sq phi]

theorem root_eucDist_hingePoint_hingePoint_eq_one_iff
    (center : R2) (theta phi : Real) :
    _root_.eucDist (hingePoint center theta) (hingePoint center phi) = 1 <->
      2 - 2 * Real.cos (theta - phi) = 1 := by
  rw [root_eucDist_eq_one_iff_distSq]
  rw [distSq_hingePoint_hingePoint_same_center]

theorem cos_sub_eq_half_of_hingePoint_pair_unit
    {center : R2} {theta phi : Real}
    (hunit :
      _root_.eucDist (hingePoint center theta) (hingePoint center phi) = 1) :
    Real.cos (theta - phi) = 1 / 2 := by
  have hsq :=
    (root_eucDist_hingePoint_hingePoint_eq_one_iff center theta phi).mp hunit
  nlinarith

theorem hingePoint_pair_unit_of_cos_sub_eq_half
    (center : R2) {theta phi : Real}
    (hcos : Real.cos (theta - phi) = 1 / 2) :
    _root_.eucDist (hingePoint center theta) (hingePoint center phi) = 1 := by
  rw [root_eucDist_hingePoint_hingePoint_eq_one_iff]
  nlinarith

theorem distSq_hingePoint_hingePoint_expand
    (left right : R2) (theta phi : Real) :
    distSq (hingePoint left theta) (hingePoint right phi) =
      distSq left right +
        (2 - 2 * Real.cos (theta - phi)) +
        2 *
          ((left.1 - right.1) * (Real.cos theta - Real.cos phi) +
            (left.2 - right.2) * (Real.sin theta - Real.sin phi)) := by
  dsimp [distSq, hingePoint, add, unitVec]
  rw [Real.cos_sub]
  nlinarith [Real.cos_sq_add_sin_sq theta, Real.cos_sq_add_sin_sq phi]

/-- If two hinges reach the same target, their centers are separated by the
same squared distance as the two unit vectors used by the hinge arms. -/
theorem distSq_centers_of_shared_hinge_target
    {left right : R2} {theta phi : Real}
    (hshared : hingePoint left theta = hingePoint right phi) :
    distSq left right = 2 - 2 * Real.cos (theta - phi) := by
  have hx : left.1 - right.1 = Real.cos phi - Real.cos theta := by
    have hfst := congrArg Prod.fst hshared
    dsimp [hingePoint, add, unitVec] at hfst
    linarith
  have hy : left.2 - right.2 = Real.sin phi - Real.sin theta := by
    have hsnd := congrArg Prod.snd hshared
    dsimp [hingePoint, add, unitVec] at hsnd
    linarith
  dsimp [distSq]
  rw [hx, hy, Real.cos_sub]
  nlinarith [Real.cos_sq_add_sin_sq theta, Real.cos_sq_add_sin_sq phi]

/-- Two common hinge targets give the same algebraic chord length when read
from either hinge center. -/
theorem shared_hinge_targets_angle_equation
    {left right : R2} {theta1 theta2 phi1 phi2 : Real}
    (hfirst : hingePoint left theta1 = hingePoint right phi1)
    (hsecond : hingePoint left theta2 = hingePoint right phi2) :
    2 - 2 * Real.cos (theta1 - theta2) =
      2 - 2 * Real.cos (phi1 - phi2) := by
  calc
    2 - 2 * Real.cos (theta1 - theta2) =
        distSq (hingePoint left theta1) (hingePoint left theta2) := by
      exact (distSq_hingePoint_hingePoint_same_center left theta1 theta2).symm
    _ = distSq (hingePoint right phi1) (hingePoint right phi2) := by
      rw [hfirst, hsecond]
    _ = 2 - 2 * Real.cos (phi1 - phi2) := by
      exact distSq_hingePoint_hingePoint_same_center right phi1 phi2

theorem shared_hinge_targets_unit_iff
    {left right : R2} {theta1 theta2 phi1 phi2 : Real}
    (hfirst : hingePoint left theta1 = hingePoint right phi1)
    (hsecond : hingePoint left theta2 = hingePoint right phi2) :
    _root_.eucDist (hingePoint left theta1) (hingePoint left theta2) = 1 <->
      _root_.eucDist (hingePoint right phi1) (hingePoint right phi2) = 1 := by
  rw [hfirst, hsecond]

theorem right_cos_sub_eq_half_of_shared_hinge_targets_left_unit
    {left right : R2} {theta1 theta2 phi1 phi2 : Real}
    (hfirst : hingePoint left theta1 = hingePoint right phi1)
    (hsecond : hingePoint left theta2 = hingePoint right phi2)
    (hunit :
      _root_.eucDist (hingePoint left theta1) (hingePoint left theta2) = 1) :
    Real.cos (phi1 - phi2) = 1 / 2 := by
  have hunitRight :=
    (shared_hinge_targets_unit_iff hfirst hsecond).mp hunit
  exact cos_sub_eq_half_of_hingePoint_pair_unit hunitRight

/-- A point lying on two unit circles satisfies the radical-axis linear
equation for the two centers. -/
theorem shared_unit_target_linear
    {left right target : R2}
    (hleft : _root_.eucDist left target = 1)
    (hright : _root_.eucDist right target = 1) :
    2 * ((right.1 - left.1) * target.1 +
        (right.2 - left.2) * target.2) =
      right.1 ^ 2 + right.2 ^ 2 - (left.1 ^ 2 + left.2 ^ 2) := by
  have hleftSq := (root_eucDist_eq_one_iff_distSq left target).mp hleft
  have hrightSq := (root_eucDist_eq_one_iff_distSq right target).mp hright
  dsimp [distSq] at hleftSq hrightSq
  nlinarith

/-- The chord through two common unit-circle targets is perpendicular to the
line joining the two hinge centers. -/
theorem shared_unit_targets_difference_orthogonal
    {left right first second : R2}
    (hleftFirst : _root_.eucDist left first = 1)
    (hrightFirst : _root_.eucDist right first = 1)
    (hleftSecond : _root_.eucDist left second = 1)
    (hrightSecond : _root_.eucDist right second = 1) :
    (right.1 - left.1) * (first.1 - second.1) +
      (right.2 - left.2) * (first.2 - second.2) = 0 := by
  have hfirst :=
    shared_unit_target_linear hleftFirst hrightFirst
  have hsecond :=
    shared_unit_target_linear hleftSecond hrightSecond
  nlinarith

/-- The finite Pach--Toth connector relation consists of exactly four pairs. -/
theorem nextConnector_cases {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v) :
    (u = T2_2 /\ v = T1_1) \/
      (u = T2_2 /\ v = T1_2) \/
      (u = T4_0 /\ v = T0_0) \/
      (u = T4_0 /\ v = T0_2) := by
  revert u v
  decide

/-- Four hinge equations for the connector targets imply the connector-unit
field used by the hinged transition interface. -/
theorem connectorUnitEdges_of_hinge_target_eqs
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (angle211 angle212 angle400 angle402 :
      (LocalVertex -> R2) -> Real)
    (h211 :
      forall source : LocalVertex -> R2,
        placeNext source T1_1 =
          hingePoint (source T2_2) (angle211 source))
    (h212 :
      forall source : LocalVertex -> R2,
        placeNext source T1_2 =
          hingePoint (source T2_2) (angle212 source))
    (h400 :
      forall source : LocalVertex -> R2,
        placeNext source T0_0 =
          hingePoint (source T4_0) (angle400 source))
    (h402 :
      forall source : LocalVertex -> R2,
        placeNext source T0_2 =
          hingePoint (source T4_0) (angle402 source)) :
    HingedTransitionInterface.ConnectorUnitEdges placeNext := by
  intro source u v hconn
  match nextConnector_cases hconn with
  | Or.inl h =>
      rw [h.left, h.right]
      rw [h211]
      exact root_eucDist_center_hingePoint (source T2_2) (angle211 source)
  | Or.inr (Or.inl h) =>
      rw [h.left, h.right]
      rw [h212]
      exact root_eucDist_center_hingePoint (source T2_2) (angle212 source)
  | Or.inr (Or.inr (Or.inl h)) =>
      rw [h.left, h.right]
      rw [h400]
      exact root_eucDist_center_hingePoint (source T4_0) (angle400 source)
  | Or.inr (Or.inr (Or.inr h)) =>
      rw [h.left, h.right]
      rw [h402]
      exact root_eucDist_center_hingePoint (source T4_0) (angle402 source)

theorem translated_T2_2_T1_1_unit_iff_eq211
    (offset : R2) :
    _root_.eucDist (ExactLocalGeometry.localPoint T2_2)
        (AffineLocalGeometry.translatedLocalPoint offset T1_1) = 1 <->
      ConnectorEquationFacts.eq211 offset.1 offset.2 ExactLocalGeometry.h := by
  rw [_root_.eucDist_eq_one_iff]
  change AffineLocalGeometry.distSq (ExactLocalGeometry.localPoint T2_2)
        (AffineLocalGeometry.translatedLocalPoint offset T1_1) = 1 <->
      ConnectorEquationFacts.eq211 offset.1 offset.2 ExactLocalGeometry.h
  rw [ConnectorEquationFacts.distSq_T2_2_translated_T1_1]
  rfl

theorem translated_T2_2_T1_2_unit_iff_eq212
    (offset : R2) :
    _root_.eucDist (ExactLocalGeometry.localPoint T2_2)
        (AffineLocalGeometry.translatedLocalPoint offset T1_2) = 1 <->
      ConnectorEquationFacts.eq212 offset.1 offset.2 ExactLocalGeometry.h := by
  rw [_root_.eucDist_eq_one_iff]
  change AffineLocalGeometry.distSq (ExactLocalGeometry.localPoint T2_2)
        (AffineLocalGeometry.translatedLocalPoint offset T1_2) = 1 <->
      ConnectorEquationFacts.eq212 offset.1 offset.2 ExactLocalGeometry.h
  rw [ConnectorEquationFacts.distSq_T2_2_translated_T1_2]
  rfl

theorem translated_T4_0_T0_0_unit_iff_eq400
    (offset : R2) :
    _root_.eucDist (ExactLocalGeometry.localPoint T4_0)
        (AffineLocalGeometry.translatedLocalPoint offset T0_0) = 1 <->
      ConnectorEquationFacts.eq400 offset.1 offset.2 ExactLocalGeometry.h := by
  rw [_root_.eucDist_eq_one_iff]
  change AffineLocalGeometry.distSq (ExactLocalGeometry.localPoint T4_0)
        (AffineLocalGeometry.translatedLocalPoint offset T0_0) = 1 <->
      ConnectorEquationFacts.eq400 offset.1 offset.2 ExactLocalGeometry.h
  rw [ConnectorEquationFacts.distSq_T4_0_translated_T0_0]
  rfl

theorem translated_T4_0_T0_2_unit_iff_eq402
    (offset : R2) :
    _root_.eucDist (ExactLocalGeometry.localPoint T4_0)
        (AffineLocalGeometry.translatedLocalPoint offset T0_2) = 1 <->
      ConnectorEquationFacts.eq402 offset.1 offset.2 ExactLocalGeometry.h := by
  rw [_root_.eucDist_eq_one_iff]
  change AffineLocalGeometry.distSq (ExactLocalGeometry.localPoint T4_0)
        (AffineLocalGeometry.translatedLocalPoint offset T0_2) = 1 <->
      ConnectorEquationFacts.eq402 offset.1 offset.2 ExactLocalGeometry.h
  rw [ConnectorEquationFacts.distSq_T4_0_translated_T0_2]
  rfl

end HingeAlgebra
end PachToth
end ErdosProblems1066

end
