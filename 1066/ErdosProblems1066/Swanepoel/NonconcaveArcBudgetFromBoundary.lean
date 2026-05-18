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

/-- Convert to the normalized nonconcave-arc turn data expected by the M8
turn-bound pipeline. -/
def toNonconcaveArcTurnData
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  D.toNonconcaveArcGeometricAngleFacts.toNonconcaveArcTurnData

/-- Convert to honest turn bounds. -/
def toHonestTurnBounds
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    TurnBoundsInterface.HonestTurnBounds :=
  D.toNonconcaveArcGeometricAngleFacts.toHonestTurnBounds

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

end NonconcaveArcBoundaryBudgetData

end NonconcaveArcBudgetFromBoundary
end Swanepoel
end ErdosProblems1066

end
