import ErdosProblems1066.Swanepoel.BoundaryArcW12
import ErdosProblems1066.Swanepoel.M8TurnBoundsFromArc
import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary
import ErdosProblems1066.Swanepoel.M8TurnPackageW12

set_option autoImplicit false

/-!
# Boundary arc instantiation to normalized M8 data

This module ties the W12 boundary-arc certificate to the boundary-attached
nonconcave-arc turn budget over the same planar boundary.  It contains only
checked bookkeeping: the boundary arc forgets to finite `p/q` spine data, and
the boundary turn budget forgets to normalized M8 arc and turn-bound data.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryArcInstantiationW13

open BoundaryArcW12
open BoundaryFaceCountingToM8
open BoundarySpineFiniteCertificate
open Lemma10Inequalities
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat}

/-! ## Source data -/

/--
Boundary arc data and the boundary-attached turn budget for the same selected
planar boundary.

The `boundaryArc` field supplies the finite boundary labels `p_i, q_i`.  The
turn fields are the remaining nonconcave-arc budget input used to normalize the
raw thirteen turns into construction-level M8 turn bounds.
-/
structure BoundaryArcInstantiation
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C)) where
  boundaryArc : M8BoundaryArcCertificate D
  rawTurn : Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k
  boundaryAngleBudget : BoundaryAngleBudget D rawTurn

namespace BoundaryArcInstantiation

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}

/-! ## Boundary arc to finite spine data -/

/-- Forget the boundary-arc markers to the finite `p/q` spine certificate. -/
def toFinitePQSpineCertificate
    (A : BoundaryArcInstantiation D) :
    M8FinitePQSpineCertificate D :=
  A.boundaryArc.toFinitePQSpineCertificate

@[simp]
theorem toFinitePQSpineCertificate_pIndex
    (A : BoundaryArcInstantiation D) (i : M8BoundaryIndex) :
    A.toFinitePQSpineCertificate.pIndex i =
      A.boundaryArc.pIndex i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_p
    (A : BoundaryArcInstantiation D) (i : M8BoundaryIndex) :
    A.toFinitePQSpineCertificate.p i =
      A.boundaryArc.p i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_q
    (A : BoundaryArcInstantiation D) (i : M8TriangleIndex) :
    A.toFinitePQSpineCertificate.q i =
      A.boundaryArc.q i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_leftEndpoint
    (A : BoundaryArcInstantiation D) :
    A.toFinitePQSpineCertificate.pIndex m8ArcFirstBoundaryIndex =
      A.boundaryArc.leftEndpoint :=
  A.boundaryArc.leftEndpoint_eq_p0

@[simp]
theorem toFinitePQSpineCertificate_rightEndpoint
    (A : BoundaryArcInstantiation D) :
    A.toFinitePQSpineCertificate.pIndex m8ArcLastBoundaryIndex =
      A.boundaryArc.rightEndpoint :=
  A.boundaryArc.rightEndpoint_eq_p13

theorem toFinitePQSpineCertificate_cyclicOrder
    (A : BoundaryArcInstantiation D) (i : M8TriangleIndex) :
    A.toFinitePQSpineCertificate.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (A.toFinitePQSpineCertificate.pIndex (m8BoundaryIndexLeft i)) :=
  A.boundaryArc.cyclicOrder i

theorem toFinitePQSpineCertificate_boundaryEdge
    (A : BoundaryArcInstantiation D) (i : M8TriangleIndex) :
    (GraphBridge.unitDistanceLocalGraph C).Adj
      (A.toFinitePQSpineCertificate.p (m8BoundaryIndexLeft i))
      (A.toFinitePQSpineCertificate.p (m8BoundaryIndexRight i)) :=
  A.boundaryArc.boundaryEdge i

theorem toFinitePQSpineCertificate_triangleWitness
    (A : BoundaryArcInstantiation D) (i : M8TriangleIndex) :
    (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor
      (A.toFinitePQSpineCertificate.p (m8BoundaryIndexLeft i))
      (A.toFinitePQSpineCertificate.p (m8BoundaryIndexRight i))
      (A.toFinitePQSpineCertificate.q i) :=
  A.boundaryArc.triangleWitness_holds i

/-- The finite certificate also forgets to the planar-boundary skeleton. -/
def toSkeleton
    (A : BoundaryArcInstantiation D) :
    BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton D :=
  A.toFinitePQSpineCertificate.toSkeleton

@[simp]
theorem toSkeleton_pIndex
    (A : BoundaryArcInstantiation D) (i : M8BoundaryIndex) :
    A.toSkeleton.pIndex i = A.boundaryArc.pIndex i :=
  rfl

@[simp]
theorem toSkeleton_q
    (A : BoundaryArcInstantiation D) (i : M8TriangleIndex) :
    A.toSkeleton.q i = A.boundaryArc.q i :=
  rfl

@[simp]
theorem toSkeleton_p
    (A : BoundaryArcInstantiation D) (i : M8BoundaryIndex) :
    A.toSkeleton.p i = A.boundaryArc.p i := by
  simp [toSkeleton]

/-- Validity of the skeleton follows from the boundary arc certificate. -/
def toSkeletonValid
    (A : BoundaryArcInstantiation D)
    (connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton.Valid
      connectedNoCut hmin A.toSkeleton :=
  A.toFinitePQSpineCertificate.toSkeletonValid

/-- Boundary labels obtained from the finite certificate and a Lemma 8 row. -/
def toM8LocalLabels
    (A : BoundaryArcInstantiation D)
    (connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (A.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    M8LocalLabels C :=
  A.toFinitePQSpineCertificate.toM8LocalLabels
    connectedNoCut hmin lemma8

@[simp]
theorem toM8LocalLabels_labels_p
    (A : BoundaryArcInstantiation D)
    (connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (A.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin))
    (i : M8BoundaryIndex) :
    (A.toM8LocalLabels connectedNoCut hmin lemma8).labels.p i =
      A.boundaryArc.p i :=
  rfl

@[simp]
theorem toM8LocalLabels_labels_q
    (A : BoundaryArcInstantiation D)
    (connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (A.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (A.toM8LocalLabels connectedNoCut hmin lemma8).labels.q i =
      A.boundaryArc.q i :=
  rfl

/-! ## Boundary budget to normalized turn data -/

/-- Repackage the source turn budget as boundary-attached budget data. -/
def toNonconcaveArcBoundaryBudgetData
    (A : BoundaryArcInstantiation D) :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalUDGraph C) where
  planarBoundary := D
  rawTurn := A.rawTurn
  rawTurn_nonnegative_on_arc := A.rawTurn_nonnegative_on_arc
  boundaryAngleBudget := A.boundaryAngleBudget

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary
    (A : BoundaryArcInstantiation D) :
    A.toNonconcaveArcBoundaryBudgetData.planarBoundary = D :=
  rfl

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_rawTurn
    (A : BoundaryArcInstantiation D) :
    A.toNonconcaveArcBoundaryBudgetData.rawTurn = A.rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_boundaryAngleBudget
    (A : BoundaryArcInstantiation D) :
    A.toNonconcaveArcBoundaryBudgetData.boundaryAngleBudget =
      A.boundaryAngleBudget :=
  rfl

/-- Generic nonconcave-arc angle facts extracted from the same boundary data. -/
def toNonconcaveArcGeometricAngleFacts
    (A : BoundaryArcInstantiation D) :
    NonconcaveArcAngleFacts.NonconcaveArcGeometricAngleFacts :=
  A.toNonconcaveArcBoundaryBudgetData.toNonconcaveArcGeometricAngleFacts

@[simp]
theorem toNonconcaveArcGeometricAngleFacts_rawTurn
    (A : BoundaryArcInstantiation D) :
    A.toNonconcaveArcGeometricAngleFacts.rawTurn = A.rawTurn :=
  rfl

/-- Normalized nonconcave-arc turn data for the M8 route. -/
def toNonconcaveArcTurnData
    (A : BoundaryArcInstantiation D) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  A.toNonconcaveArcBoundaryBudgetData.toNonconcaveArcTurnData

@[simp]
theorem toNonconcaveArcTurnData_rawTurn
    (A : BoundaryArcInstantiation D) :
    A.toNonconcaveArcTurnData.rawTurn = A.rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcTurnData_turn
    (A : BoundaryArcInstantiation D) :
    A.toNonconcaveArcTurnData.turn =
      A.toNonconcaveArcGeometricAngleFacts.normalizedTurn :=
  A.toNonconcaveArcBoundaryBudgetData.toNonconcaveArcTurnData_turn

/-- Honest turn bounds for the normalized turn function. -/
def toHonestTurnBounds
    (A : BoundaryArcInstantiation D) :
    TurnBoundsInterface.HonestTurnBounds :=
  A.toNonconcaveArcBoundaryBudgetData.toHonestTurnBounds

@[simp]
theorem toHonestTurnBounds_turn
    (A : BoundaryArcInstantiation D) :
    A.toHonestTurnBounds.turn =
      A.toNonconcaveArcGeometricAngleFacts.normalizedTurn :=
  A.toNonconcaveArcBoundaryBudgetData.toHonestTurnBounds_turn

/-- Construction-level M8 turn bounds for the normalized turn function. -/
def toM8TurnBounds
    (A : BoundaryArcInstantiation D) :
    M8TurnBounds :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds

@[simp]
theorem toM8TurnBounds_turn
    (A : BoundaryArcInstantiation D) :
    A.toM8TurnBounds.turn =
      A.toNonconcaveArcGeometricAngleFacts.normalizedTurn :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_turn

theorem toM8TurnBounds_turn_eq_arcTurn
    (A : BoundaryArcInstantiation D) :
    A.toM8TurnBounds.turn = A.toNonconcaveArcTurnData.turn := by
  rw [A.toM8TurnBounds_turn, A.toNonconcaveArcTurnData_turn]

@[simp]
theorem toM8TurnBounds_turn_of_mem
    (A : BoundaryArcInstantiation D) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    A.toM8TurnBounds.turn k = A.rawTurn k :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_turn_of_mem hk

@[simp]
theorem toM8TurnBounds_turn_of_not_mem
    (A : BoundaryArcInstantiation D) {k : Nat}
    (hk : Not (Membership.mem turnIndexSet k)) :
    A.toM8TurnBounds.turn k = 0 :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_turn_of_not_mem hk

theorem toM8TurnBounds_turn_nonnegative
    (A : BoundaryArcInstantiation D) (k : Nat) :
    0 <= A.toM8TurnBounds.turn k :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_turn_nonnegative k

theorem raw_totalTurn_lt_pi_div_three
    (A : BoundaryArcInstantiation D) :
    totalTurn A.rawTurn < Real.pi / 3 :=
  A.toNonconcaveArcBoundaryBudgetData.raw_totalTurn_lt_pi_div_three

theorem raw_totalTurn_eq_m8ThirteenTurnSum
    (A : BoundaryArcInstantiation D) :
    totalTurn A.rawTurn = m8ThirteenTurnSum A.rawTurn :=
  A.toNonconcaveArcBoundaryBudgetData.raw_totalTurn_eq_m8ThirteenTurnSum

theorem toM8TurnBounds_totalTurn_eq_rawTurn
    (A : BoundaryArcInstantiation D) :
    totalTurn A.toM8TurnBounds.turn = totalTurn A.rawTurn :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_totalTurn_eq_rawTurn

theorem toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum
    (A : BoundaryArcInstantiation D) :
    totalTurn A.toM8TurnBounds.turn =
      m8ThirteenTurnSum A.toM8TurnBounds.turn :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum

theorem toM8TurnBounds_m8ThirteenTurnSum_eq_raw
    (A : BoundaryArcInstantiation D) :
    m8ThirteenTurnSum A.toM8TurnBounds.turn =
      m8ThirteenTurnSum A.rawTurn :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_m8ThirteenTurnSum_eq_raw

theorem toM8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum
    (A : BoundaryArcInstantiation D) :
    totalTurn A.toM8TurnBounds.turn =
      m8ThirteenTurnSum A.rawTurn :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum

theorem toM8TurnBounds_totalTurn_le_boundaryBudget
    (A : BoundaryArcInstantiation D) :
    totalTurn A.toM8TurnBounds.turn <=
      A.boundaryAngleBudget.geometricAngleBudget :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_totalTurn_le_boundaryBudget

theorem toM8TurnBounds_totalTurn_lt_pi_div_three
    (A : BoundaryArcInstantiation D) :
    totalTurn A.toM8TurnBounds.turn < Real.pi / 3 :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_totalTurn_lt_pi_div_three

theorem toM8TurnBounds_m8ThirteenTurnSum_le_boundaryBudget
    (A : BoundaryArcInstantiation D) :
    m8ThirteenTurnSum A.toM8TurnBounds.turn <=
      A.boundaryAngleBudget.geometricAngleBudget :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_m8ThirteenTurnSum_le_boundaryBudget

theorem toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three
    (A : BoundaryArcInstantiation D) :
    m8ThirteenTurnSum A.toM8TurnBounds.turn < Real.pi / 3 :=
  A.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three

/-! ## W12 turn package facade -/

/-- The W12 turn package built from the same boundary budget data. -/
def toBoundaryLongArcM8TurnPackage
    (A : BoundaryArcInstantiation D) :
    M8TurnPackageW12.BoundaryLongArcM8TurnPackage
      A.toNonconcaveArcBoundaryBudgetData :=
  M8TurnPackageW12.BoundaryLongArcM8TurnPackage.ofBoundaryBudgetData
    A.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem toBoundaryLongArcM8TurnPackage_turnBounds
    (A : BoundaryArcInstantiation D) :
    A.toBoundaryLongArcM8TurnPackage.turnBounds = A.toM8TurnBounds :=
  rfl

/-- The W12 thirteen-turn and window consequences for the normalized turns. -/
def thirteenWindowData
    (A : BoundaryArcInstantiation D) :
    M8TurnPackageW12.M8ThirteenTurnWindowData A.toM8TurnBounds :=
  M8TurnPackageW12.M8ThirteenTurnWindowData.ofTurnBounds A.toM8TurnBounds

theorem thirteenWindowData_totalTurn_eq_thirteen
    (A : BoundaryArcInstantiation D) :
    totalTurn A.toM8TurnBounds.turn =
      m8ThirteenTurnSum A.toM8TurnBounds.turn :=
  A.thirteenWindowData.totalTurn_eq_thirteen

theorem thirteenWindowData_thirteen_lt_pi_div_three
    (A : BoundaryArcInstantiation D) :
    m8ThirteenTurnSum A.toM8TurnBounds.turn < Real.pi / 3 :=
  A.thirteenWindowData.thirteen_lt_pi_div_three

theorem thirteenWindowData_separatedTurn_nonnegative
    (A : BoundaryArcInstantiation D) (i j : Nat) :
    0 <= separatedTurn A.toM8TurnBounds.turn i j :=
  A.thirteenWindowData.separated_nonnegative i j

theorem thirteenWindowData_adjacentTurn_nonnegative
    (A : BoundaryArcInstantiation D) (i : Nat) :
    0 <= adjacentTurn A.toM8TurnBounds.turn i :=
  A.thirteenWindowData.adjacent_nonnegative i

theorem thirteenWindowData_separatedTurn_lt_pi_div_three
    (A : BoundaryArcInstantiation D) {i j : Nat}
    (hi : 1 <= i) (hj : j <= 10) :
    separatedTurn A.toM8TurnBounds.turn i j < Real.pi / 3 :=
  A.thirteenWindowData.separated_lt_pi_div_three hi hj

theorem thirteenWindowData_adjacentTurn_lt_pi_div_three
    (A : BoundaryArcInstantiation D) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10) :
    adjacentTurn A.toM8TurnBounds.turn i < Real.pi / 3 :=
  A.thirteenWindowData.adjacent_lt_pi_div_three hi hi_next

/-- The reusable boundary-to-M8 turn-bound field package from W12. -/
def boundaryToM8TurnBoundFields
    (A : BoundaryArcInstantiation D) :
    NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields
      A.toNonconcaveArcBoundaryBudgetData :=
  A.toNonconcaveArcBoundaryBudgetData.boundaryToM8TurnBoundFields

@[simp]
theorem boundaryToM8TurnBoundFields_m8TurnBounds
    (A : BoundaryArcInstantiation D) :
    A.boundaryToM8TurnBoundFields.m8TurnBounds =
      A.toM8TurnBounds :=
  rfl

@[simp]
theorem boundaryToM8TurnBoundFields_arcData
    (A : BoundaryArcInstantiation D) :
    A.boundaryToM8TurnBoundFields.arcData =
      A.toNonconcaveArcTurnData :=
  rfl

end BoundaryArcInstantiation

end

end BoundaryArcInstantiationW13
end Swanepoel
end ErdosProblems1066
