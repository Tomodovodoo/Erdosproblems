import ErdosProblems1066.Swanepoel.NonconcaveArcAngleFacts
import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal
import ErdosProblems1066.Swanepoel.BoundaryCounting

set_option autoImplicit false

/-!
# Nonconcave arc budget from planar boundary data

This file is the narrow adapter between the planar boundary/subpolygon counting
facade and the nonconcave-arc turn-budget facade.

The checked planar side already supplies the E12/E13 boundary-counting
conclusions through `PlanarBoundaryFinal`.  The remaining geometric ingredient
for a particular nonconcave arc is isolated as `BoundaryAngleBudget`: a real
angle budget, attached to the chosen planar-boundary package and raw arc turn
function, whose only obligations are

* the raw total turn is at most that budget; and
* the budget is strictly below `pi / 3`.

Together with pointwise nonnegativity of the raw turns on `1, ..., 13`, this is
exactly the `NonconcaveArcGeometricAngleFacts` record consumed downstream.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NonconcaveArcBudgetFromBoundary

open BoundaryCounting
open Lemma10Inequalities
open NonconcaveArcAngleFacts

universe u

variable {n : Nat}

/-! ## The explicit M8 thirteen-turn sum -/

/-- The thirteen-term turn sum used by the `m = 8` specialization. -/
def m8ThirteenTurnSum (turn : Nat -> Real) : Real :=
  turn 1 + turn 2 + turn 3 + turn 4 + turn 5 + turn 6 + turn 7 +
    turn 8 + turn 9 + turn 10 + turn 11 + turn 12 + turn 13

/-- The abstract total turn is exactly the explicit thirteen-term M8 sum. -/
theorem totalTurn_eq_m8ThirteenTurnSum (turn : Nat -> Real) :
    totalTurn turn = m8ThirteenTurnSum turn := by
  unfold m8ThirteenTurnSum totalTurn turnIndexSet
  norm_num [Finset.sum_Icc_succ_top, add_assoc]

/-! ## Minimal boundary-attached arc budget -/

/--
The remaining geometric budget comparison for one raw nonconcave-arc turn
function, attached to a chosen planar-boundary data package.

The planar-boundary parameter keeps the budget tied to the same outer-boundary
and subpolygon data used for the checked count inequalities, but the record
contains only the two angle-budget facts still missing from boundary geometry.
-/
structure BoundaryAngleBudget
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (rawTurn : Nat -> Real) where
  geometricAngleBudget : Real
  totalTurn_le_geometricAngleBudget :
    totalTurn rawTurn <= geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :
    geometricAngleBudget < Real.pi / 3

namespace BoundaryAngleBudget

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
variable {rawTurn : Nat -> Real}

/-- Add raw-turn nonnegativity to the boundary-attached budget, yielding the
generic nonconcave-arc geometric facts used by the turn-bound pipeline. -/
def toNonconcaveArcGeometricAngleFacts
    (B : BoundaryAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    NonconcaveArcGeometricAngleFacts where
  rawTurn := rawTurn
  geometricAngleBudget := B.geometricAngleBudget
  rawTurn_nonnegative_on_arc := hraw_nonnegative
  totalTurn_le_geometricAngleBudget :=
    B.totalTurn_le_geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :=
    B.geometricAngleBudget_lt_pi_div_three

@[simp]
theorem toNonconcaveArcGeometricAngleFacts_rawTurn
    (B : BoundaryAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toNonconcaveArcGeometricAngleFacts hraw_nonnegative).rawTurn =
      rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcGeometricAngleFacts_geometricAngleBudget
    (B : BoundaryAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toNonconcaveArcGeometricAngleFacts hraw_nonnegative).geometricAngleBudget =
      B.geometricAngleBudget :=
  rfl

/-- The boundary-attached budget immediately gives the strict raw total-turn
bound once raw-turn nonnegativity has been supplied. -/
theorem raw_totalTurn_lt_pi_div_three
    (B : BoundaryAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    totalTurn rawTurn < Real.pi / 3 :=
  (B.toNonconcaveArcGeometricAngleFacts
    hraw_nonnegative).raw_totalTurn_lt_pi_div_three

/-- The raw total turn is the explicit thirteen-term M8 arc sum. -/
theorem raw_totalTurn_eq_m8ThirteenTurnSum
    (B : BoundaryAngleBudget D rawTurn) :
    totalTurn rawTurn = m8ThirteenTurnSum rawTurn := by
  have _hbudget : totalTurn rawTurn <= B.geometricAngleBudget :=
    B.totalTurn_le_geometricAngleBudget
  exact totalTurn_eq_m8ThirteenTurnSum rawTurn

/-- The explicit thirteen-term raw turn sum is bounded by the geometric
boundary-attached budget. -/
theorem raw_m8ThirteenTurnSum_le_geometricAngleBudget
    (B : BoundaryAngleBudget D rawTurn) :
    m8ThirteenTurnSum rawTurn <= B.geometricAngleBudget := by
  simpa [B.raw_totalTurn_eq_m8ThirteenTurnSum] using
    B.totalTurn_le_geometricAngleBudget

/-- The explicit thirteen-term raw turn sum is below `pi / 3`. -/
theorem raw_m8ThirteenTurnSum_lt_pi_div_three
    (B : BoundaryAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    m8ThirteenTurnSum rawTurn < Real.pi / 3 := by
  simpa [B.raw_totalTurn_eq_m8ThirteenTurnSum] using
    B.raw_totalTurn_lt_pi_div_three hraw_nonnegative

/-- The geometric angle budget is nonnegative whenever the raw arc turns are
nonnegative on the turn-index set. -/
theorem geometricAngleBudget_nonnegative
    (B : BoundaryAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    0 <= B.geometricAngleBudget :=
  (B.toNonconcaveArcGeometricAngleFacts
    hraw_nonnegative).geometricAngleBudget_nonnegative

end BoundaryAngleBudget

/-! ## Planar boundary data plus the remaining arc budget -/

/--
Planar boundary/subpolygon data together with the minimal remaining
nonconcave-arc budget comparison.

The `planarBoundary` field carries all checked outer-boundary and subpolygon
counting input.  The `boundaryAngleBudget` field is the isolated geometric
fact still needed to convert the raw turns into M8 turn bounds.
-/
structure NonconcaveArcBoundaryBudgetData
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G
  rawTurn : Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k
  boundaryAngleBudget :
    BoundaryAngleBudget planarBoundary rawTurn

namespace NonconcaveArcBoundaryBudgetData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-! ### Boundary and subpolygon counting projections -/

/-- The concrete planar face-counting package exposed by
`PlanarBoundaryFinal`. -/
def concreteFaceCountingData
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      D.planarBoundary :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData
    D.planarBoundary

/-- The checked outer-boundary angle lower bound carried by the planar data. -/
theorem boundaryAngleLowerBound
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.planarBoundary.outerBoundaryCounts.AngleLowerBound :=
  PlanarBoundaryFinal.PlanarBoundaryData.outerBoundaryAngleLowerBound
    D.planarBoundary

/-- The checked subpolygon angle lower bound carried by the planar data. -/
theorem subpolygonAngleLowerBound
    (D : NonconcaveArcBoundaryBudgetData.{u} G)
    (S : D.planarBoundary.Subpolygon) :
    (D.planarBoundary.subpolygonData S).counts.AngleLowerBound :=
  PlanarBoundaryFinal.PlanarBoundaryData.subpolygonAngleLowerBound
    D.planarBoundary S

/-- The bundled face-counting conclusions routed through
`PlanarBoundaryFinal`. -/
theorem faceCountingTheorems
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      D.planarBoundary :=
  PlanarBoundaryFinal.PlanarBoundaryData.faceCountingTheorems_of_concreteData
    D.planarBoundary

/-- The outer-boundary E12 inequality remains available alongside the
nonconcave-arc budget. -/
theorem boundaryAngleCount
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.planarBoundary.outerBoundaryCounts.d5 +
          2 * D.planarBoundary.outerBoundaryCounts.d6 +
          D.planarBoundary.outerBoundaryCounts.b +
          D.planarBoundary.outerBoundaryCounts.B + 6 <=
        D.planarBoundary.outerBoundaryCounts.d3 :=
  D.faceCountingTheorems.boundaryAngleCount

/-- The negative-element form of E12 remains available alongside the arc
budget. -/
theorem boundaryNegativeCount
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.planarBoundary.outerBoundaryCounts.negativeCount +
          D.planarBoundary.outerBoundaryCounts.B + 6 <=
        D.planarBoundary.outerBoundaryCounts.d3 :=
  D.faceCountingTheorems.boundaryNegativeCount

/-- E13 with high-degree slack remains available for every supplied
subpolygon. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (D : NonconcaveArcBoundaryBudgetData.{u} G)
    (S : D.planarBoundary.Subpolygon) :
    (D.planarBoundary.subpolygonData S).counts.D5 +
          2 * (D.planarBoundary.subpolygonData S).counts.D6 + 6 <=
        2 * (D.planarBoundary.subpolygonData S).counts.D2 +
          (D.planarBoundary.subpolygonData S).counts.D3 :=
  D.faceCountingTheorems.subpolygonLowDegreeWithHighDegreeSlack S

/-- Swanepoel's low-degree subpolygon conclusion remains available for every
supplied subpolygon. -/
theorem subpolygonLowDegree
    (D : NonconcaveArcBoundaryBudgetData.{u} G)
    (S : D.planarBoundary.Subpolygon) :
    6 <= 2 * (D.planarBoundary.subpolygonData S).counts.D2 +
      (D.planarBoundary.subpolygonData S).counts.D3 :=
  D.faceCountingTheorems.subpolygonLowDegree S

/-! ### Reusable checked boundary angle/count fields -/

/--
All checked boundary and subpolygon counting fields attached to the same
planar-boundary package as the nonconcave-arc budget.

This is a reusable projection record: downstream callers can consume the
concrete `PlanarBoundaryFinal` package, the proposition-valued angle lower
bounds, or the already-cleared E12/E13 count inequalities without rebuilding
the route through the facade.
-/
structure BoundaryAngleCountFields
    (D : NonconcaveArcBoundaryBudgetData.{u} G) where
  concrete :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      D.planarBoundary
  boundaryAngleLowerBound :
    D.planarBoundary.outerBoundaryCounts.AngleLowerBound
  boundaryAngleCount :
    D.planarBoundary.outerBoundaryCounts.d5 +
          2 * D.planarBoundary.outerBoundaryCounts.d6 +
          D.planarBoundary.outerBoundaryCounts.b +
          D.planarBoundary.outerBoundaryCounts.B + 6 <=
        D.planarBoundary.outerBoundaryCounts.d3
  boundaryNegativeCount :
    D.planarBoundary.outerBoundaryCounts.negativeCount +
          D.planarBoundary.outerBoundaryCounts.B + 6 <=
        D.planarBoundary.outerBoundaryCounts.d3
  subpolygonAngleLowerBound :
    forall S : D.planarBoundary.Subpolygon,
      (D.planarBoundary.subpolygonData S).counts.AngleLowerBound
  subpolygonLowDegreeWithHighDegreeSlack :
    forall S : D.planarBoundary.Subpolygon,
      (D.planarBoundary.subpolygonData S).counts.D5 +
            2 * (D.planarBoundary.subpolygonData S).counts.D6 + 6 <=
          2 * (D.planarBoundary.subpolygonData S).counts.D2 +
            (D.planarBoundary.subpolygonData S).counts.D3
  subpolygonLowDegree :
    forall S : D.planarBoundary.Subpolygon,
      6 <= 2 * (D.planarBoundary.subpolygonData S).counts.D2 +
        (D.planarBoundary.subpolygonData S).counts.D3
  concreteBoundaryAngleLowerBound :
    concrete.boundaryCounts.AngleLowerBound
  concreteBoundaryAngleCount :
    concrete.boundaryCounts.d5 + 2 * concrete.boundaryCounts.d6 +
          concrete.boundaryCounts.b + concrete.boundaryCounts.B + 6 <=
        concrete.boundaryCounts.d3
  concreteBoundaryNegativeCount :
    concrete.boundaryCounts.negativeCount +
          concrete.boundaryCounts.B + 6 <=
        concrete.boundaryCounts.d3
  concreteSubpolygonAngleLowerBound :
    forall S : concrete.Subpolygon,
      (concrete.subpolygonCounts S).AngleLowerBound
  concreteSubpolygonLowDegreeWithHighDegreeSlack :
    forall S : concrete.Subpolygon,
      (concrete.subpolygonCounts S).D5 +
            2 * (concrete.subpolygonCounts S).D6 + 6 <=
          2 * (concrete.subpolygonCounts S).D2 +
            (concrete.subpolygonCounts S).D3
  concreteSubpolygonLowDegree :
    forall S : concrete.Subpolygon,
      6 <= 2 * (concrete.subpolygonCounts S).D2 +
        (concrete.subpolygonCounts S).D3

/-- Extract the reusable boundary angle/count field package. -/
def boundaryAngleCountFields
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    BoundaryAngleCountFields D where
  concrete := D.concreteFaceCountingData
  boundaryAngleLowerBound := D.boundaryAngleLowerBound
  boundaryAngleCount := D.boundaryAngleCount
  boundaryNegativeCount := D.boundaryNegativeCount
  subpolygonAngleLowerBound := D.subpolygonAngleLowerBound
  subpolygonLowDegreeWithHighDegreeSlack :=
    D.subpolygonLowDegreeWithHighDegreeSlack
  subpolygonLowDegree := D.subpolygonLowDegree
  concreteBoundaryAngleLowerBound :=
    D.concreteFaceCountingData.boundaryAngleLowerBound
  concreteBoundaryAngleCount :=
    D.concreteFaceCountingData.boundaryAngleCount
  concreteBoundaryNegativeCount :=
    D.concreteFaceCountingData.boundaryNegativeCount
  concreteSubpolygonAngleLowerBound :=
    D.concreteFaceCountingData.subpolygonAngleLowerBound
  concreteSubpolygonLowDegreeWithHighDegreeSlack :=
    D.concreteFaceCountingData.subpolygonLowDegreeWithHighDegreeSlack
  concreteSubpolygonLowDegree :=
    D.concreteFaceCountingData.subpolygonLowDegree

/-! ### Conversion to nonconcave-arc turn facts -/

/-- Forget the boundary attachment and produce the generic nonconcave-arc
geometric angle facts. -/
def toNonconcaveArcGeometricAngleFacts
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    NonconcaveArcGeometricAngleFacts :=
  D.boundaryAngleBudget.toNonconcaveArcGeometricAngleFacts
    D.rawTurn_nonnegative_on_arc

@[simp]
theorem toNonconcaveArcGeometricAngleFacts_rawTurn
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toNonconcaveArcGeometricAngleFacts.rawTurn = D.rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcGeometricAngleFacts_geometricAngleBudget
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toNonconcaveArcGeometricAngleFacts.geometricAngleBudget =
      D.boundaryAngleBudget.geometricAngleBudget :=
  rfl

/-- The raw total turn is below `pi / 3` by the boundary-attached budget. -/
theorem raw_totalTurn_lt_pi_div_three
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.rawTurn < Real.pi / 3 :=
  D.toNonconcaveArcGeometricAngleFacts.raw_totalTurn_lt_pi_div_three

/-- The raw boundary-attached total turn is the explicit thirteen-term M8
arc sum. -/
theorem raw_totalTurn_eq_m8ThirteenTurnSum
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.rawTurn = m8ThirteenTurnSum D.rawTurn :=
  totalTurn_eq_m8ThirteenTurnSum D.rawTurn

/-- The explicit thirteen-term raw turn sum is bounded by the
boundary-attached angle budget. -/
theorem raw_m8ThirteenTurnSum_le_boundaryBudget
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum D.rawTurn <=
      D.boundaryAngleBudget.geometricAngleBudget := by
  simpa [D.raw_totalTurn_eq_m8ThirteenTurnSum] using
    D.boundaryAngleBudget.totalTurn_le_geometricAngleBudget

/-- The explicit thirteen-term raw turn sum is below `pi / 3`. -/
theorem raw_m8ThirteenTurnSum_lt_pi_div_three
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum D.rawTurn < Real.pi / 3 := by
  simpa [D.raw_totalTurn_eq_m8ThirteenTurnSum] using
    D.raw_totalTurn_lt_pi_div_three

/-- The boundary-attached angle budget is nonnegative. -/
theorem boundaryAngleBudget_nonnegative
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    0 <= D.boundaryAngleBudget.geometricAngleBudget :=
  D.boundaryAngleBudget.geometricAngleBudget_nonnegative
    D.rawTurn_nonnegative_on_arc

/-- Convert to the normalized nonconcave-arc turn data expected by the M8
turn-bound pipeline. -/
def toNonconcaveArcTurnData
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  D.toNonconcaveArcGeometricAngleFacts.toNonconcaveArcTurnData

@[simp]
theorem toNonconcaveArcTurnData_rawTurn
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toNonconcaveArcTurnData.rawTurn = D.rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcTurnData_turn
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toNonconcaveArcTurnData.turn =
      D.toNonconcaveArcGeometricAngleFacts.normalizedTurn :=
  D.toNonconcaveArcGeometricAngleFacts.toNonconcaveArcTurnData_turn

/-- Convert to honest turn bounds. -/
def toHonestTurnBounds
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    TurnBoundsInterface.HonestTurnBounds :=
  D.toNonconcaveArcGeometricAngleFacts.toHonestTurnBounds

@[simp]
theorem toHonestTurnBounds_turn
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toHonestTurnBounds.turn =
      D.toNonconcaveArcGeometricAngleFacts.normalizedTurn :=
  D.toNonconcaveArcGeometricAngleFacts.toHonestTurnBounds_turn

/-- Convert to the construction-level M8 turn-bound package. -/
def toM8TurnBounds
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    M8ConstructionInterface.M8TurnBounds :=
  D.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds

@[simp]
theorem toM8TurnBounds_turn
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toM8TurnBounds.turn =
      D.toNonconcaveArcGeometricAngleFacts.normalizedTurn :=
  D.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_turn

/-- Pointwise nonnegativity of the normalized M8 turn function. -/
theorem toM8TurnBounds_turn_nonnegative
    (D : NonconcaveArcBoundaryBudgetData.{u} G) (k : Nat) :
    0 <= D.toM8TurnBounds.turn k :=
  D.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_turn_nonnegative k

@[simp]
theorem toM8TurnBounds_turn_of_mem
    (D : NonconcaveArcBoundaryBudgetData.{u} G) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    D.toM8TurnBounds.turn k = D.rawTurn k := by
  simpa [D.toM8TurnBounds_turn] using
    D.toNonconcaveArcGeometricAngleFacts.normalizedTurn_of_mem hk

@[simp]
theorem toM8TurnBounds_turn_of_not_mem
    (D : NonconcaveArcBoundaryBudgetData.{u} G) {k : Nat}
    (hk : Not (Membership.mem turnIndexSet k)) :
    D.toM8TurnBounds.turn k = 0 := by
  simpa [D.toM8TurnBounds_turn] using
    D.toNonconcaveArcGeometricAngleFacts.normalizedTurn_of_not_mem hk

/-- Normalization preserves the raw total turn on the M8 turn-bound package. -/
theorem toM8TurnBounds_totalTurn_eq_rawTurn
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.toM8TurnBounds.turn = totalTurn D.rawTurn := by
  simpa [D.toM8TurnBounds_turn] using
    D.toNonconcaveArcGeometricAngleFacts.totalTurn_normalizedTurn_eq_rawTurn

/-- The normalized M8 total turn is the explicit thirteen-term sum of the
M8 turn function. -/
theorem toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.toM8TurnBounds.turn =
      m8ThirteenTurnSum D.toM8TurnBounds.turn :=
  totalTurn_eq_m8ThirteenTurnSum D.toM8TurnBounds.turn

/-- The normalized M8 thirteen-term sum agrees with the raw thirteen-term
boundary arc sum. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_eq_raw
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum D.toM8TurnBounds.turn =
      m8ThirteenTurnSum D.rawTurn := by
  have htotal := D.toM8TurnBounds_totalTurn_eq_rawTurn
  rw [D.toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum,
    D.raw_totalTurn_eq_m8ThirteenTurnSum] at htotal
  exact htotal

/-- The normalized M8 total turn is the explicit raw thirteen-term arc sum. -/
theorem toM8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.toM8TurnBounds.turn =
      m8ThirteenTurnSum D.rawTurn := by
  simpa [D.raw_totalTurn_eq_m8ThirteenTurnSum] using
    D.toM8TurnBounds_totalTurn_eq_rawTurn

/-- The normalized M8 total turn is bounded by the boundary angle budget. -/
theorem toM8TurnBounds_totalTurn_le_boundaryBudget
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.toM8TurnBounds.turn <=
      D.boundaryAngleBudget.geometricAngleBudget := by
  simpa using
    NonconcaveArcGeometricAngleFacts.toM8TurnBounds_totalTurn_le_geometricAngleBudget
      D.toNonconcaveArcGeometricAngleFacts

/-- The normalized M8 total turn is below `pi / 3`. -/
theorem toM8TurnBounds_totalTurn_lt_pi_div_three
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.toM8TurnBounds.turn < Real.pi / 3 :=
  NonconcaveArcGeometricAngleFacts.toM8TurnBounds_totalTurn_lt_pi_div_three
    D.toNonconcaveArcGeometricAngleFacts

/-- Boundary data supplies the `turn_nonnegative` field of the construction
level `M8TurnBounds` package. -/
theorem toM8TurnBounds_turn_nonnegative_field
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    forall k : Nat, 0 <= D.toM8TurnBounds.turn k :=
  D.toM8TurnBounds.turn_nonnegative

/-- Boundary data supplies the `total_turn_lt_pi_div_three` field of the
construction-level `M8TurnBounds` package. -/
theorem toM8TurnBounds_total_turn_lt_pi_div_three_field
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.toM8TurnBounds.turn < Real.pi / 3 :=
  D.toM8TurnBounds.total_turn_lt_pi_div_three

/-- The explicit normalized M8 thirteen-turn sum is below `pi / 3`. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum D.toM8TurnBounds.turn < Real.pi / 3 := by
  rw [← D.toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum]
  exact D.toM8TurnBounds_total_turn_lt_pi_div_three_field

/-- The explicit normalized M8 thirteen-turn sum is bounded by the boundary
angle budget. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_le_boundaryBudget
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum D.toM8TurnBounds.turn <=
      D.boundaryAngleBudget.geometricAngleBudget := by
  rw [← D.toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum]
  exact D.toM8TurnBounds_totalTurn_le_boundaryBudget

/-! ### Reusable boundary-to-M8 turn-bound fields -/

/--
The explicit reusable route from the boundary-attached angle/count data to the
M8 turn-bound package.

The fields keep the boundary count package, the intermediate geometric angle
facts, the normalized arc data, and both turn-bound records available together
with the normalization and budget inequalities that downstream M8 assembly
steps usually need.
-/
structure BoundaryToM8TurnBoundFields
    (D : NonconcaveArcBoundaryBudgetData.{u} G) where
  boundaryCounts : BoundaryAngleCountFields D
  angleFacts : NonconcaveArcGeometricAngleFacts
  arcData : M8TurnBoundsFromArc.NonconcaveArcTurnData
  honestTurnBounds : TurnBoundsInterface.HonestTurnBounds
  m8TurnBounds : M8ConstructionInterface.M8TurnBounds
  angleFacts_rawTurn : angleFacts.rawTurn = D.rawTurn
  angleFacts_geometricAngleBudget :
    angleFacts.geometricAngleBudget =
      D.boundaryAngleBudget.geometricAngleBudget
  arcData_rawTurn : arcData.rawTurn = D.rawTurn
  arcData_turn : arcData.turn = angleFacts.normalizedTurn
  honestTurnBounds_turn :
    honestTurnBounds.turn = angleFacts.normalizedTurn
  m8TurnBounds_turn :
    m8TurnBounds.turn = angleFacts.normalizedTurn
  raw_totalTurn_lt_pi_div_three :
    totalTurn D.rawTurn < Real.pi / 3
  boundaryAngleBudget_nonnegative :
    0 <= D.boundaryAngleBudget.geometricAngleBudget
  m8TurnBounds_turn_nonnegative :
    forall k : Nat, 0 <= m8TurnBounds.turn k
  m8TurnBounds_totalTurn_eq_rawTurn :
    totalTurn m8TurnBounds.turn = totalTurn D.rawTurn
  raw_totalTurn_eq_m8ThirteenTurnSum :
    totalTurn D.rawTurn = m8ThirteenTurnSum D.rawTurn
  raw_m8ThirteenTurnSum_le_boundaryBudget :
    m8ThirteenTurnSum D.rawTurn <=
      D.boundaryAngleBudget.geometricAngleBudget
  raw_m8ThirteenTurnSum_lt_pi_div_three :
    m8ThirteenTurnSum D.rawTurn < Real.pi / 3
  m8TurnBounds_totalTurn_eq_m8ThirteenTurnSum :
    totalTurn m8TurnBounds.turn =
      m8ThirteenTurnSum m8TurnBounds.turn
  m8TurnBounds_m8ThirteenTurnSum_eq_raw :
    m8ThirteenTurnSum m8TurnBounds.turn =
      m8ThirteenTurnSum D.rawTurn
  m8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum :
    totalTurn m8TurnBounds.turn = m8ThirteenTurnSum D.rawTurn
  m8TurnBounds_totalTurn_le_boundaryBudget :
    totalTurn m8TurnBounds.turn <=
      D.boundaryAngleBudget.geometricAngleBudget
  m8TurnBounds_totalTurn_lt_pi_div_three :
    totalTurn m8TurnBounds.turn < Real.pi / 3
  m8TurnBounds_total_turn_lt_pi_div_three_field :
    totalTurn m8TurnBounds.turn < Real.pi / 3
  m8TurnBounds_m8ThirteenTurnSum_le_boundaryBudget :
    m8ThirteenTurnSum m8TurnBounds.turn <=
      D.boundaryAngleBudget.geometricAngleBudget
  m8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three :
    m8ThirteenTurnSum m8TurnBounds.turn < Real.pi / 3

/-- Extract all reusable fields in the boundary-to-M8 turn-bound route. -/
def boundaryToM8TurnBoundFields
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    BoundaryToM8TurnBoundFields D where
  boundaryCounts := D.boundaryAngleCountFields
  angleFacts := D.toNonconcaveArcGeometricAngleFacts
  arcData := D.toNonconcaveArcTurnData
  honestTurnBounds := D.toHonestTurnBounds
  m8TurnBounds := D.toM8TurnBounds
  angleFacts_rawTurn := rfl
  angleFacts_geometricAngleBudget := rfl
  arcData_rawTurn := rfl
  arcData_turn := D.toNonconcaveArcTurnData_turn
  honestTurnBounds_turn := D.toHonestTurnBounds_turn
  m8TurnBounds_turn := D.toM8TurnBounds_turn
  raw_totalTurn_lt_pi_div_three := D.raw_totalTurn_lt_pi_div_three
  boundaryAngleBudget_nonnegative := D.boundaryAngleBudget_nonnegative
  m8TurnBounds_turn_nonnegative := D.toM8TurnBounds_turn_nonnegative
  m8TurnBounds_totalTurn_eq_rawTurn :=
    D.toM8TurnBounds_totalTurn_eq_rawTurn
  raw_totalTurn_eq_m8ThirteenTurnSum :=
    D.raw_totalTurn_eq_m8ThirteenTurnSum
  raw_m8ThirteenTurnSum_le_boundaryBudget :=
    D.raw_m8ThirteenTurnSum_le_boundaryBudget
  raw_m8ThirteenTurnSum_lt_pi_div_three :=
    D.raw_m8ThirteenTurnSum_lt_pi_div_three
  m8TurnBounds_totalTurn_eq_m8ThirteenTurnSum :=
    D.toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum
  m8TurnBounds_m8ThirteenTurnSum_eq_raw :=
    D.toM8TurnBounds_m8ThirteenTurnSum_eq_raw
  m8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum :=
    D.toM8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum
  m8TurnBounds_totalTurn_le_boundaryBudget :=
    D.toM8TurnBounds_totalTurn_le_boundaryBudget
  m8TurnBounds_totalTurn_lt_pi_div_three :=
    D.toM8TurnBounds_totalTurn_lt_pi_div_three
  m8TurnBounds_total_turn_lt_pi_div_three_field :=
    D.toM8TurnBounds_total_turn_lt_pi_div_three_field
  m8TurnBounds_m8ThirteenTurnSum_le_boundaryBudget :=
    D.toM8TurnBounds_m8ThirteenTurnSum_le_boundaryBudget
  m8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three :=
    D.toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three

@[simp]
theorem boundaryToM8TurnBoundFields_m8TurnBounds
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.boundaryToM8TurnBoundFields.m8TurnBounds =
      D.toM8TurnBounds :=
  rfl

@[simp]
theorem boundaryToM8TurnBoundFields_honestTurnBounds
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.boundaryToM8TurnBoundFields.honestTurnBounds =
      D.toHonestTurnBounds :=
  rfl

end NonconcaveArcBoundaryBudgetData

end NonconcaveArcBudgetFromBoundary
end Swanepoel
end ErdosProblems1066

end
