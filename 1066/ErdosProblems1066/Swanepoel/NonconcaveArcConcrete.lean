import ErdosProblems1066.Swanepoel.M8TurnBoundsFromArc
import ErdosProblems1066.Swanepoel.M8TurnBoundsConcrete
import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal

set_option autoImplicit false

/-!
# Concrete nonconcave-arc turn package

This file is a standalone reduction layer for the remaining nonconcave-arc
input in the Swanepoel `m = 8` route.  The outer-boundary and subpolygon
geometry is carried by `PlanarBoundaryClosure.PlanarBoundaryData` and exposed
through `PlanarBoundaryFinal`; the actual nonconcave-arc angle work is kept as
explicit real inequalities.

Once the caller supplies nonnegativity of each turn on the arc indices and a
geometric angle budget below `pi / 3`, the data reduces to
`M8TurnBoundsFromArc.NonconcaveArcTurnData`, hence to the checked M8 turn-bound
interfaces.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NonconcaveArcConcrete

open Lemma10Inequalities
open M8TurnBoundsConcrete
open M8TurnBoundsFromArc

universe u

variable {n : Nat}

/-! ## Explicit arc angle inequalities -/

/--
The remaining angle facts needed to turn a raw nonconcave-arc turn function
into `NonconcaveArcTurnData`.

The `geometricAngleBudget` field is intentionally abstract: it may be the
angle sum extracted from the outer boundary, from a subpolygon comparison, or
from a combined paper argument.  This layer only checks the real-inequality
reduction.
-/
structure NonconcaveArcAngleInequalities where
  rawTurn : Nat -> Real
  geometricAngleBudget : Real
  rawTurn_nonnegative_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k
  totalTurn_le_geometricAngleBudget :
    totalTurn rawTurn <= geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :
    geometricAngleBudget < Real.pi / 3

namespace NonconcaveArcAngleInequalities

/-- The supplied angle inequalities give the raw total-turn bound required by
`NonconcaveArcTurnData`. -/
theorem raw_totalTurn_lt_pi_div_three
    (A : NonconcaveArcAngleInequalities) :
    totalTurn A.rawTurn < Real.pi / 3 :=
  lt_of_le_of_lt A.totalTurn_le_geometricAngleBudget
    A.geometricAngleBudget_lt_pi_div_three

/-- Construct the nonconcave-arc turn data from explicit angle inequalities. -/
def toNonconcaveArcTurnData
    (A : NonconcaveArcAngleInequalities) :
    NonconcaveArcTurnData where
  rawTurn := A.rawTurn
  rawTurn_nonnegative_on_arc := A.rawTurn_nonnegative_on_arc
  raw_totalTurn_lt_pi_div_three := A.raw_totalTurn_lt_pi_div_three

@[simp] theorem toNonconcaveArcTurnData_rawTurn
    (A : NonconcaveArcAngleInequalities) :
    A.toNonconcaveArcTurnData.rawTurn = A.rawTurn :=
  rfl

/-- The normalized turn attached to the constructed arc data. -/
def turn (A : NonconcaveArcAngleInequalities) (k : Nat) : Real :=
  A.toNonconcaveArcTurnData.turn k

@[simp] theorem turn_eq
    (A : NonconcaveArcAngleInequalities) :
    A.turn = A.toNonconcaveArcTurnData.turn :=
  rfl

/-- Pointwise turn nonnegativity after the standard off-arc normalization. -/
theorem turn_nonnegative
    (A : NonconcaveArcAngleInequalities) (k : Nat) :
    0 <= A.turn k :=
  A.toNonconcaveArcTurnData.turn_nonnegative k

/-- The normalized total turn is below `pi / 3`. -/
theorem totalTurn_turn_lt_pi_div_three
    (A : NonconcaveArcAngleInequalities) :
    totalTurn A.turn < Real.pi / 3 := by
  simpa [turn] using
    A.toNonconcaveArcTurnData.totalTurn_turn_lt_pi_div_three

/-- The honest turn-bound package obtained from the supplied inequalities. -/
def toHonestTurnBounds
    (A : NonconcaveArcAngleInequalities) :
    TurnBoundsInterface.HonestTurnBounds :=
  M8TurnBoundsConcrete.honestTurnBounds A.toNonconcaveArcTurnData

/-- The construction-level M8 turn-bound package obtained from the supplied
inequalities. -/
def toM8TurnBounds
    (A : NonconcaveArcAngleInequalities) :
    M8ConstructionInterface.M8TurnBounds :=
  M8TurnBoundsConcrete.m8TurnBounds A.toNonconcaveArcTurnData

@[simp] theorem toM8TurnBounds_turn
    (A : NonconcaveArcAngleInequalities) :
    A.toM8TurnBounds.turn = A.turn :=
  rfl

/-- M8-package pointwise turn nonnegativity from the explicit inequalities. -/
theorem toM8TurnBounds_nonnegative
    (A : NonconcaveArcAngleInequalities) (k : Nat) :
    0 <= A.toM8TurnBounds.turn k :=
  M8TurnBoundsConcrete.m8TurnBounds_nonnegative
    A.toNonconcaveArcTurnData k

/-- M8-package total-turn bound from the explicit inequalities. -/
theorem toM8TurnBounds_total_turn_lt_pi_div_three
    (A : NonconcaveArcAngleInequalities) :
    totalTurn A.toM8TurnBounds.turn < Real.pi / 3 :=
  M8TurnBoundsConcrete.m8TurnBounds_total_turn_lt_pi_div_three
    A.toNonconcaveArcTurnData

end NonconcaveArcAngleInequalities

/-! ## Boundary and subpolygon geometry carrying the arc inequalities -/

/--
Outer-boundary/subpolygon geometry plus the explicit angle inequalities for
one nonconcave arc.

`planarBoundary` is the checked geometry/counting package assembled by the
outer-boundary and subpolygon layers.  The `arcAngles` field records the
remaining nonconcave-arc angle facts; the definitions below reduce it to the
turn packages consumed by the M8 construction.
-/
structure NonconcaveArcBoundaryData
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G
  arcAngles : NonconcaveArcAngleInequalities

namespace NonconcaveArcBoundaryData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- The concrete outer-boundary and subpolygon counting data exposed by
`PlanarBoundaryFinal`. -/
def concreteFaceCountingData
    (D : NonconcaveArcBoundaryData.{u} G) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      D.planarBoundary :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData
    D.planarBoundary

/-- The proposition-valued face-counting conclusions already checked from the
outer-boundary/subpolygon geometry. -/
theorem faceCountingTheorems
    (D : NonconcaveArcBoundaryData.{u} G) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      D.planarBoundary :=
  PlanarBoundaryFinal.PlanarBoundaryData.faceCountingTheorems_of_concreteData
    D.planarBoundary

/-- Reduce the boundary/subpolygon arc package to `NonconcaveArcTurnData`. -/
def toNonconcaveArcTurnData
    (D : NonconcaveArcBoundaryData.{u} G) :
    NonconcaveArcTurnData :=
  D.arcAngles.toNonconcaveArcTurnData

/-- Reduce the boundary/subpolygon arc package to honest turn bounds. -/
def toHonestTurnBounds
    (D : NonconcaveArcBoundaryData.{u} G) :
    TurnBoundsInterface.HonestTurnBounds :=
  D.arcAngles.toHonestTurnBounds

/-- Reduce the boundary/subpolygon arc package to construction-level M8 turn
bounds. -/
def toM8TurnBounds
    (D : NonconcaveArcBoundaryData.{u} G) :
    M8ConstructionInterface.M8TurnBounds :=
  D.arcAngles.toM8TurnBounds

/-- Pointwise turn nonnegativity obtained from the supplied arc angle
inequalities. -/
theorem turn_nonnegative
    (D : NonconcaveArcBoundaryData.{u} G) (k : Nat) :
    0 <= D.toM8TurnBounds.turn k :=
  D.arcAngles.toM8TurnBounds_nonnegative k

/-- Total turn below `pi / 3` obtained from the supplied arc angle
inequalities. -/
theorem total_turn_lt_pi_div_three
    (D : NonconcaveArcBoundaryData.{u} G) :
    totalTurn D.toM8TurnBounds.turn < Real.pi / 3 :=
  D.arcAngles.toM8TurnBounds_total_turn_lt_pi_div_three

/-- The boundary count inequality remains available alongside the arc turn
reduction. -/
theorem boundaryAngleCount
    (D : NonconcaveArcBoundaryData.{u} G) :
    D.planarBoundary.outerBoundaryCounts.d5 +
          2 * D.planarBoundary.outerBoundaryCounts.d6 +
          D.planarBoundary.outerBoundaryCounts.b +
          D.planarBoundary.outerBoundaryCounts.B + 6 <=
        D.planarBoundary.outerBoundaryCounts.d3 :=
  D.faceCountingTheorems.boundaryAngleCount

/-- The subpolygon low-degree inequality remains available alongside the arc
turn reduction. -/
theorem subpolygonLowDegree
    (D : NonconcaveArcBoundaryData.{u} G)
    (S : D.planarBoundary.Subpolygon) :
    6 <= 2 * (D.planarBoundary.subpolygonData S).counts.D2 +
      (D.planarBoundary.subpolygonData S).counts.D3 :=
  D.faceCountingTheorems.subpolygonLowDegree S

end NonconcaveArcBoundaryData

end NonconcaveArcConcrete
end Swanepoel
end ErdosProblems1066

end
