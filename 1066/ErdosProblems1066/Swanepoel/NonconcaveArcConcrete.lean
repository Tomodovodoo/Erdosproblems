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

/-! ## The explicit M8 thirteen-turn sum -/

/-- The thirteen-term turn sum used by the `m = 8` arc. -/
def m8ThirteenTurnSum (turn : Nat -> Real) : Real :=
  turn 1 + turn 2 + turn 3 + turn 4 + turn 5 + turn 6 + turn 7 +
    turn 8 + turn 9 + turn 10 + turn 11 + turn 12 + turn 13

/-- The abstract total turn is exactly the explicit thirteen-term M8 sum. -/
theorem totalTurn_eq_m8ThirteenTurnSum (turn : Nat -> Real) :
    totalTurn turn = m8ThirteenTurnSum turn := by
  unfold m8ThirteenTurnSum totalTurn turnIndexSet
  norm_num [Finset.sum_Icc_succ_top, add_assoc]

/-- A total turn is nonnegative when all arc-index turns are nonnegative. -/
theorem totalTurn_nonnegative_of_nonnegative_on_arc
    (rawTurn : Nat -> Real)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    0 <= totalTurn rawTurn := by
  unfold totalTurn
  exact Finset.sum_nonneg fun k hk => hraw_nonnegative k hk

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

/-- The raw total turn is nonnegative from pointwise arc nonnegativity. -/
theorem raw_totalTurn_nonnegative
    (A : NonconcaveArcAngleInequalities) :
    0 <= totalTurn A.rawTurn :=
  totalTurn_nonnegative_of_nonnegative_on_arc A.rawTurn
    A.rawTurn_nonnegative_on_arc

/-- The geometric angle budget is nonnegative once it bounds the raw total
turn. -/
theorem geometricAngleBudget_nonnegative
    (A : NonconcaveArcAngleInequalities) :
    0 <= A.geometricAngleBudget :=
  le_trans A.raw_totalTurn_nonnegative
    A.totalTurn_le_geometricAngleBudget

/-- The raw total turn is the explicit thirteen-term M8 sum. -/
theorem raw_totalTurn_eq_m8ThirteenTurnSum
    (A : NonconcaveArcAngleInequalities) :
    totalTurn A.rawTurn = m8ThirteenTurnSum A.rawTurn :=
  totalTurn_eq_m8ThirteenTurnSum A.rawTurn

/-- The explicit thirteen-term raw sum is bounded by the geometric budget. -/
theorem raw_m8ThirteenTurnSum_le_geometricAngleBudget
    (A : NonconcaveArcAngleInequalities) :
    m8ThirteenTurnSum A.rawTurn <= A.geometricAngleBudget := by
  simpa [A.raw_totalTurn_eq_m8ThirteenTurnSum] using
    A.totalTurn_le_geometricAngleBudget

/-- The explicit thirteen-term raw sum is below `pi / 3`. -/
theorem raw_m8ThirteenTurnSum_lt_pi_div_three
    (A : NonconcaveArcAngleInequalities) :
    m8ThirteenTurnSum A.rawTurn < Real.pi / 3 := by
  simpa [A.raw_totalTurn_eq_m8ThirteenTurnSum] using
    A.raw_totalTurn_lt_pi_div_three

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

/-- On arc indices, the normalized turn is the raw turn. -/
@[simp] theorem turn_of_mem
    (A : NonconcaveArcAngleInequalities) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    A.turn k = A.rawTurn k := by
  simpa [turn] using
    A.toNonconcaveArcTurnData.turn_of_mem hk

/-- Off arc indices, the normalized turn is zero. -/
@[simp] theorem turn_of_not_mem
    (A : NonconcaveArcAngleInequalities) {k : Nat}
    (hk : Not (Membership.mem turnIndexSet k)) :
    A.turn k = 0 := by
  simpa [turn] using
    A.toNonconcaveArcTurnData.turn_of_not_mem hk

/-- Normalization does not change the total turn. -/
theorem totalTurn_turn_eq_rawTurn
    (A : NonconcaveArcAngleInequalities) :
    totalTurn A.turn = totalTurn A.rawTurn := by
  simpa [turn] using
    A.toNonconcaveArcTurnData.totalTurn_turn_eq_rawTurn

/-- The normalized total turn is bounded by the geometric budget. -/
theorem totalTurn_turn_le_geometricAngleBudget
    (A : NonconcaveArcAngleInequalities) :
    totalTurn A.turn <= A.geometricAngleBudget := by
  simpa [A.totalTurn_turn_eq_rawTurn] using
    A.totalTurn_le_geometricAngleBudget

/-- The normalized total turn is below `pi / 3`. -/
theorem totalTurn_turn_lt_pi_div_three
    (A : NonconcaveArcAngleInequalities) :
    totalTurn A.turn < Real.pi / 3 := by
  simpa [turn] using
    A.toNonconcaveArcTurnData.totalTurn_turn_lt_pi_div_three

/-- The normalized thirteen-term sum agrees with the raw thirteen-term sum. -/
theorem turn_m8ThirteenTurnSum_eq_raw
    (A : NonconcaveArcAngleInequalities) :
    m8ThirteenTurnSum A.turn = m8ThirteenTurnSum A.rawTurn := by
  calc
    m8ThirteenTurnSum A.turn = totalTurn A.turn :=
      (totalTurn_eq_m8ThirteenTurnSum A.turn).symm
    _ = totalTurn A.rawTurn :=
      A.totalTurn_turn_eq_rawTurn
    _ = m8ThirteenTurnSum A.rawTurn :=
      totalTurn_eq_m8ThirteenTurnSum A.rawTurn

/-- The normalized thirteen-term sum is bounded by the geometric budget. -/
theorem turn_m8ThirteenTurnSum_le_geometricAngleBudget
    (A : NonconcaveArcAngleInequalities) :
    m8ThirteenTurnSum A.turn <= A.geometricAngleBudget := by
  simpa [A.turn_m8ThirteenTurnSum_eq_raw] using
    A.raw_m8ThirteenTurnSum_le_geometricAngleBudget

/-- The normalized thirteen-term sum is below `pi / 3`. -/
theorem turn_m8ThirteenTurnSum_lt_pi_div_three
    (A : NonconcaveArcAngleInequalities) :
    m8ThirteenTurnSum A.turn < Real.pi / 3 := by
  simpa [A.turn_m8ThirteenTurnSum_eq_raw] using
    A.raw_m8ThirteenTurnSum_lt_pi_div_three

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

/-- The M8 package total turn is the raw arc total turn. -/
theorem toM8TurnBounds_totalTurn_eq_rawTurn
    (A : NonconcaveArcAngleInequalities) :
    totalTurn A.toM8TurnBounds.turn = totalTurn A.rawTurn := by
  simpa [toM8TurnBounds] using
    M8TurnBoundsConcrete.m8TurnBounds_totalTurn_eq_rawTurn
      A.toNonconcaveArcTurnData

/-- The M8 package total turn is bounded by the geometric budget. -/
theorem toM8TurnBounds_totalTurn_le_geometricAngleBudget
    (A : NonconcaveArcAngleInequalities) :
    totalTurn A.toM8TurnBounds.turn <= A.geometricAngleBudget := by
  simpa [A.toM8TurnBounds_totalTurn_eq_rawTurn] using
    A.totalTurn_le_geometricAngleBudget

/-- The M8 package thirteen-term sum is the raw thirteen-term arc sum. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_eq_raw
    (A : NonconcaveArcAngleInequalities) :
    m8ThirteenTurnSum A.toM8TurnBounds.turn =
      m8ThirteenTurnSum A.rawTurn := by
  calc
    m8ThirteenTurnSum A.toM8TurnBounds.turn =
        totalTurn A.toM8TurnBounds.turn :=
      (totalTurn_eq_m8ThirteenTurnSum A.toM8TurnBounds.turn).symm
    _ = totalTurn A.rawTurn :=
      A.toM8TurnBounds_totalTurn_eq_rawTurn
    _ = m8ThirteenTurnSum A.rawTurn :=
      totalTurn_eq_m8ThirteenTurnSum A.rawTurn

/-- The M8 package thirteen-term sum is bounded by the geometric budget. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget
    (A : NonconcaveArcAngleInequalities) :
    m8ThirteenTurnSum A.toM8TurnBounds.turn <=
      A.geometricAngleBudget := by
  simpa [A.toM8TurnBounds_m8ThirteenTurnSum_eq_raw] using
    A.raw_m8ThirteenTurnSum_le_geometricAngleBudget

/-- The M8 package thirteen-term sum is below `pi / 3`. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three
    (A : NonconcaveArcAngleInequalities) :
    m8ThirteenTurnSum A.toM8TurnBounds.turn < Real.pi / 3 := by
  simpa [A.toM8TurnBounds_m8ThirteenTurnSum_eq_raw] using
    A.raw_m8ThirteenTurnSum_lt_pi_div_three

end NonconcaveArcAngleInequalities

/-! ## Boundary-attached arc budgets -/

/--
A boundary-attached angle budget for one raw arc turn function.

The planar-boundary parameter ties the budget to the same checked boundary
and subpolygon package used in the face-counting reducers.  The fields are
only the two real inequalities needed to turn a concrete boundary arc into
the nonconcave-arc data consumed by the M8 turn pipeline.
-/
structure BoundaryArcAngleBudget
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (rawTurn : Nat -> Real) where
  geometricAngleBudget : Real
  totalTurn_le_geometricAngleBudget :
    totalTurn rawTurn <= geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :
    geometricAngleBudget < Real.pi / 3

namespace BoundaryArcAngleBudget

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
variable {rawTurn : Nat -> Real}

/-- Add raw-turn nonnegativity to a boundary-attached budget, producing the
angle-inequality package used by the concrete nonconcave-arc reducer. -/
def toNonconcaveArcAngleInequalities
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    NonconcaveArcAngleInequalities where
  rawTurn := rawTurn
  geometricAngleBudget := B.geometricAngleBudget
  rawTurn_nonnegative_on_arc := hraw_nonnegative
  totalTurn_le_geometricAngleBudget :=
    B.totalTurn_le_geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :=
    B.geometricAngleBudget_lt_pi_div_three

@[simp] theorem toNonconcaveArcAngleInequalities_rawTurn
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toNonconcaveArcAngleInequalities hraw_nonnegative).rawTurn =
      rawTurn :=
  rfl

@[simp] theorem toNonconcaveArcAngleInequalities_geometricAngleBudget
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toNonconcaveArcAngleInequalities hraw_nonnegative).geometricAngleBudget =
      B.geometricAngleBudget :=
  rfl

/-- The boundary-attached budget gives the strict raw total-turn bound once
raw nonnegativity has been supplied. -/
theorem raw_totalTurn_lt_pi_div_three
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    totalTurn rawTurn < Real.pi / 3 :=
  (B.toNonconcaveArcAngleInequalities
    hraw_nonnegative).raw_totalTurn_lt_pi_div_three

/-- The boundary-attached budget is nonnegative once the raw turns are
nonnegative on the arc. -/
theorem geometricAngleBudget_nonnegative
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    0 <= B.geometricAngleBudget :=
  (B.toNonconcaveArcAngleInequalities
    hraw_nonnegative).geometricAngleBudget_nonnegative

/-- The explicit thirteen-term raw arc sum is bounded by the boundary budget.
-/
theorem raw_m8ThirteenTurnSum_le_geometricAngleBudget
    (B : BoundaryArcAngleBudget D rawTurn) :
    m8ThirteenTurnSum rawTurn <= B.geometricAngleBudget := by
  simpa [totalTurn_eq_m8ThirteenTurnSum rawTurn] using
    B.totalTurn_le_geometricAngleBudget

/-- The explicit thirteen-term raw arc sum is below `pi / 3`. -/
theorem raw_m8ThirteenTurnSum_lt_pi_div_three
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    m8ThirteenTurnSum rawTurn < Real.pi / 3 := by
  simpa [totalTurn_eq_m8ThirteenTurnSum rawTurn] using
    B.raw_totalTurn_lt_pi_div_three hraw_nonnegative

/-- Convert the boundary-attached budget to normalized arc turn data. -/
def toNonconcaveArcTurnData
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    NonconcaveArcTurnData :=
  (B.toNonconcaveArcAngleInequalities
    hraw_nonnegative).toNonconcaveArcTurnData

@[simp] theorem toNonconcaveArcTurnData_rawTurn
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toNonconcaveArcTurnData hraw_nonnegative).rawTurn = rawTurn :=
  rfl

/-- Convert the boundary-attached budget to honest turn bounds. -/
def toHonestTurnBounds
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    TurnBoundsInterface.HonestTurnBounds :=
  (B.toNonconcaveArcAngleInequalities hraw_nonnegative).toHonestTurnBounds

/-- Convert the boundary-attached budget to construction-level M8 turn bounds.
-/
def toM8TurnBounds
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    M8ConstructionInterface.M8TurnBounds :=
  (B.toNonconcaveArcAngleInequalities hraw_nonnegative).toM8TurnBounds

/-- The M8 turn package obtained from a boundary budget is pointwise
nonnegative. -/
theorem toM8TurnBounds_turn_nonnegative
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k)
    (k : Nat) :
    0 <= (B.toM8TurnBounds hraw_nonnegative).turn k :=
  (B.toNonconcaveArcAngleInequalities
    hraw_nonnegative).toM8TurnBounds_nonnegative k

/-- The M8 total turn obtained from a boundary budget is bounded by that
budget. -/
theorem toM8TurnBounds_totalTurn_le_geometricAngleBudget
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    totalTurn (B.toM8TurnBounds hraw_nonnegative).turn <=
      B.geometricAngleBudget :=
  (B.toNonconcaveArcAngleInequalities
    hraw_nonnegative).toM8TurnBounds_totalTurn_le_geometricAngleBudget

/-- The M8 total turn obtained from a boundary budget is below `pi / 3`. -/
theorem toM8TurnBounds_totalTurn_lt_pi_div_three
    (B : BoundaryArcAngleBudget D rawTurn)
    (hraw_nonnegative :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    totalTurn (B.toM8TurnBounds hraw_nonnegative).turn < Real.pi / 3 :=
  (B.toNonconcaveArcAngleInequalities
    hraw_nonnegative).toM8TurnBounds_total_turn_lt_pi_div_three

end BoundaryArcAngleBudget

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

/-! ## Boundary budget data with explicit raw arc turns -/

/--
Planar boundary/subpolygon data together with a boundary-attached angle budget
for the selected nonconcave arc.

This keeps the raw turn function and its arc-index nonnegativity separate from
the two budget inequalities.  The reducers below build the older
`NonconcaveArcBoundaryData` facade and the normalized M8 turn-bound packages
without introducing any additional existence assumption.
-/
structure NonconcaveArcBoundaryBudgetData
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G
  rawTurn : Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k
  boundaryAngleBudget :
    BoundaryArcAngleBudget planarBoundary rawTurn

namespace NonconcaveArcBoundaryBudgetData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- Constructor from the concrete boundary arc facts. -/
def ofBoundaryArcBudget
    (planarBoundary :
      PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (rawTurn : Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k)
    (geometricAngleBudget : Real)
    (totalTurn_le_geometricAngleBudget :
      totalTurn rawTurn <= geometricAngleBudget)
    (geometricAngleBudget_lt_pi_div_three :
      geometricAngleBudget < Real.pi / 3) :
    NonconcaveArcBoundaryBudgetData.{u} G where
  planarBoundary := planarBoundary
  rawTurn := rawTurn
  rawTurn_nonnegative_on_arc := rawTurn_nonnegative_on_arc
  boundaryAngleBudget :=
    { geometricAngleBudget := geometricAngleBudget
      totalTurn_le_geometricAngleBudget :=
        totalTurn_le_geometricAngleBudget
      geometricAngleBudget_lt_pi_div_three :=
        geometricAngleBudget_lt_pi_div_three }

/-- The explicit angle-inequality package extracted from boundary arc facts.
-/
def toNonconcaveArcAngleInequalities
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    NonconcaveArcAngleInequalities :=
  D.boundaryAngleBudget.toNonconcaveArcAngleInequalities
    D.rawTurn_nonnegative_on_arc

@[simp] theorem toNonconcaveArcAngleInequalities_rawTurn
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toNonconcaveArcAngleInequalities.rawTurn = D.rawTurn :=
  rfl

@[simp] theorem toNonconcaveArcAngleInequalities_geometricAngleBudget
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toNonconcaveArcAngleInequalities.geometricAngleBudget =
      D.boundaryAngleBudget.geometricAngleBudget :=
  rfl

/-- Forget the raw/budget split and obtain the older boundary arc facade. -/
def toNonconcaveArcBoundaryData
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    NonconcaveArcBoundaryData.{u} G where
  planarBoundary := D.planarBoundary
  arcAngles := D.toNonconcaveArcAngleInequalities

@[simp] theorem toNonconcaveArcBoundaryData_planarBoundary
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toNonconcaveArcBoundaryData.planarBoundary = D.planarBoundary :=
  rfl

@[simp] theorem toNonconcaveArcBoundaryData_arcAngles
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toNonconcaveArcBoundaryData.arcAngles =
      D.toNonconcaveArcAngleInequalities :=
  rfl

/-- The concrete outer-boundary and subpolygon counting data remains attached
to the same planar-boundary package. -/
def concreteFaceCountingData
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      D.planarBoundary :=
  D.toNonconcaveArcBoundaryData.concreteFaceCountingData

/-- The checked face-counting conclusions remain available after adding the
boundary arc budget. -/
theorem faceCountingTheorems
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      D.planarBoundary :=
  D.toNonconcaveArcBoundaryData.faceCountingTheorems

/-- The boundary count inequality remains available alongside the raw arc
budget. -/
theorem boundaryAngleCount
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.planarBoundary.outerBoundaryCounts.d5 +
          2 * D.planarBoundary.outerBoundaryCounts.d6 +
          D.planarBoundary.outerBoundaryCounts.b +
          D.planarBoundary.outerBoundaryCounts.B + 6 <=
        D.planarBoundary.outerBoundaryCounts.d3 :=
  D.toNonconcaveArcBoundaryData.boundaryAngleCount

/-- The subpolygon low-degree inequality remains available alongside the raw
arc budget. -/
theorem subpolygonLowDegree
    (D : NonconcaveArcBoundaryBudgetData.{u} G)
    (S : D.planarBoundary.Subpolygon) :
    6 <= 2 * (D.planarBoundary.subpolygonData S).counts.D2 +
      (D.planarBoundary.subpolygonData S).counts.D3 :=
  D.toNonconcaveArcBoundaryData.subpolygonLowDegree S

/-- Reduce boundary arc budget data to normalized nonconcave-arc turn data. -/
def toNonconcaveArcTurnData
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    NonconcaveArcTurnData :=
  D.toNonconcaveArcAngleInequalities.toNonconcaveArcTurnData

@[simp] theorem toNonconcaveArcTurnData_rawTurn
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toNonconcaveArcTurnData.rawTurn = D.rawTurn :=
  rfl

/-- Reduce boundary arc budget data to honest turn bounds. -/
def toHonestTurnBounds
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    TurnBoundsInterface.HonestTurnBounds :=
  D.toNonconcaveArcAngleInequalities.toHonestTurnBounds

/-- Reduce boundary arc budget data to construction-level M8 turn bounds. -/
def toM8TurnBounds
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    M8ConstructionInterface.M8TurnBounds :=
  D.toNonconcaveArcAngleInequalities.toM8TurnBounds

@[simp] theorem toM8TurnBounds_turn
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    D.toM8TurnBounds.turn =
      D.toNonconcaveArcTurnData.turn :=
  rfl

@[simp] theorem toM8TurnBounds_turn_of_mem
    (D : NonconcaveArcBoundaryBudgetData.{u} G) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    D.toM8TurnBounds.turn k = D.rawTurn k := by
  simpa [toM8TurnBounds] using
    M8TurnBoundsConcrete.m8TurnBounds_turn_of_mem
      D.toNonconcaveArcTurnData hk

@[simp] theorem toM8TurnBounds_turn_of_not_mem
    (D : NonconcaveArcBoundaryBudgetData.{u} G) {k : Nat}
    (hk : Not (Membership.mem turnIndexSet k)) :
    D.toM8TurnBounds.turn k = 0 := by
  simpa [toM8TurnBounds] using
    M8TurnBoundsConcrete.m8TurnBounds_turn_of_not_mem
      D.toNonconcaveArcTurnData hk

/-- Pointwise nonnegativity of the normalized M8 turn package. -/
theorem toM8TurnBounds_turn_nonnegative
    (D : NonconcaveArcBoundaryBudgetData.{u} G) (k : Nat) :
    0 <= D.toM8TurnBounds.turn k :=
  D.toNonconcaveArcAngleInequalities.toM8TurnBounds_nonnegative k

/-- The raw total turn is nonnegative. -/
theorem raw_totalTurn_nonnegative
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    0 <= totalTurn D.rawTurn :=
  D.toNonconcaveArcAngleInequalities.raw_totalTurn_nonnegative

/-- The raw total turn is below `pi / 3` by the boundary-attached budget. -/
theorem raw_totalTurn_lt_pi_div_three
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.rawTurn < Real.pi / 3 :=
  D.toNonconcaveArcAngleInequalities.raw_totalTurn_lt_pi_div_three

/-- The boundary-attached angle budget is nonnegative. -/
theorem boundaryAngleBudget_nonnegative
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    0 <= D.boundaryAngleBudget.geometricAngleBudget :=
  D.toNonconcaveArcAngleInequalities.geometricAngleBudget_nonnegative

/-- The raw total turn is the explicit thirteen-term M8 arc sum. -/
theorem raw_totalTurn_eq_m8ThirteenTurnSum
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.rawTurn = m8ThirteenTurnSum D.rawTurn :=
  D.toNonconcaveArcAngleInequalities.raw_totalTurn_eq_m8ThirteenTurnSum

/-- The explicit thirteen-term raw sum is bounded by the boundary budget. -/
theorem raw_m8ThirteenTurnSum_le_boundaryAngleBudget
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum D.rawTurn <=
      D.boundaryAngleBudget.geometricAngleBudget :=
  NonconcaveArcAngleInequalities.raw_m8ThirteenTurnSum_le_geometricAngleBudget
    D.toNonconcaveArcAngleInequalities

/-- The explicit thirteen-term raw sum is below `pi / 3`. -/
theorem raw_m8ThirteenTurnSum_lt_pi_div_three
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum D.rawTurn < Real.pi / 3 :=
  NonconcaveArcAngleInequalities.raw_m8ThirteenTurnSum_lt_pi_div_three
    D.toNonconcaveArcAngleInequalities

/-- Normalization preserves the raw total turn on the M8 package. -/
theorem toM8TurnBounds_totalTurn_eq_rawTurn
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.toM8TurnBounds.turn = totalTurn D.rawTurn :=
  D.toNonconcaveArcAngleInequalities.toM8TurnBounds_totalTurn_eq_rawTurn

/-- The normalized M8 total turn is bounded by the boundary angle budget. -/
theorem toM8TurnBounds_totalTurn_le_boundaryAngleBudget
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.toM8TurnBounds.turn <=
      D.boundaryAngleBudget.geometricAngleBudget :=
  NonconcaveArcAngleInequalities.toM8TurnBounds_totalTurn_le_geometricAngleBudget
    D.toNonconcaveArcAngleInequalities

/-- The normalized M8 total turn is below `pi / 3`. -/
theorem toM8TurnBounds_totalTurn_lt_pi_div_three
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn D.toM8TurnBounds.turn < Real.pi / 3 :=
  NonconcaveArcAngleInequalities.toM8TurnBounds_total_turn_lt_pi_div_three
    D.toNonconcaveArcAngleInequalities

/-- The normalized M8 thirteen-term sum is the raw thirteen-term arc sum. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_eq_raw
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum D.toM8TurnBounds.turn =
      m8ThirteenTurnSum D.rawTurn :=
  NonconcaveArcAngleInequalities.toM8TurnBounds_m8ThirteenTurnSum_eq_raw
    D.toNonconcaveArcAngleInequalities

/-- The normalized M8 thirteen-term sum is bounded by the boundary budget. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_le_boundaryAngleBudget
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum D.toM8TurnBounds.turn <=
      D.boundaryAngleBudget.geometricAngleBudget :=
  NonconcaveArcAngleInequalities.toM8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget
    D.toNonconcaveArcAngleInequalities

/-- The normalized M8 thirteen-term sum is below `pi / 3`. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum D.toM8TurnBounds.turn < Real.pi / 3 :=
  NonconcaveArcAngleInequalities.toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three
    D.toNonconcaveArcAngleInequalities

end NonconcaveArcBoundaryBudgetData

/-! ## Finite long-arc selection from boundary facts -/

/--
Finite boundary long-arc facts sufficient to select a nonconcave long arc and
turn it into boundary-budget data.

The count inequality is the final combinatorial shape of Lemma 5: there are
strictly more long arcs than concave long arcs.  The `concave_iff` field ties
that finite predicate to the actual turn sum, so the selected nonconcave arc
gets a concrete budget, namely its own total turn.
-/
structure BoundaryLongArcFacts
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  LongArc : Type u
  longArcFintype : Fintype LongArc
  concave : LongArc -> Prop
  concaveLongArcFintype : Fintype {a : LongArc // concave a}
  concaveLongArcCount_lt_longArcCount :
    @Fintype.card {a : LongArc // concave a} concaveLongArcFintype <
      @Fintype.card LongArc longArcFintype
  rawTurn : LongArc -> Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall a : LongArc,
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k
  concave_iff :
    forall a : LongArc, concave a <-> Real.pi / 3 <= totalTurn (rawTurn a)

namespace BoundaryLongArcFacts

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- The count gap produces an actual long arc which is not concave. -/
theorem exists_nonconcave_longArc
    (F : BoundaryLongArcFacts.{u} D) :
    Exists fun a : F.LongArc => Not (F.concave a) := by
  letI : Fintype F.LongArc := F.longArcFintype
  letI : Fintype {a : F.LongArc // F.concave a} :=
    F.concaveLongArcFintype
  by_contra hnone
  have hall : forall a : F.LongArc, F.concave a := by
    intro a
    by_contra ha
    exact hnone (Exists.intro a ha)
  let e : F.LongArc ≃ {a : F.LongArc // F.concave a} :=
    { toFun := fun a => ⟨a, hall a⟩
      invFun := fun a => a.1
      left_inv := fun _ => rfl
      right_inv := by
        intro a
        ext
        rfl }
  have hcard :
      Fintype.card F.LongArc =
        Fintype.card {a : F.LongArc // F.concave a} :=
    Fintype.card_congr e
  have hlt : Fintype.card F.LongArc < Fintype.card F.LongArc := by
    simpa [hcard] using F.concaveLongArcCount_lt_longArcCount
  exact (Nat.lt_irrefl _) hlt

/-- A nonconcave long arc has total turn below `pi / 3`. -/
theorem totalTurn_lt_pi_div_three_of_not_concave
    (F : BoundaryLongArcFacts.{u} D) {a : F.LongArc}
    (ha : Not (F.concave a)) :
    totalTurn (F.rawTurn a) < Real.pi / 3 := by
  have hnot :
      Not (Real.pi / 3 <= totalTurn (F.rawTurn a)) := by
    intro hle
    exact ha ((F.concave_iff a).2 hle)
  exact lt_of_not_ge hnot

/-- The concrete boundary angle budget attached to a nonconcave long arc. -/
def boundaryAngleBudgetOfNonconcave
    (F : BoundaryLongArcFacts.{u} D) {a : F.LongArc}
    (ha : Not (F.concave a)) :
    BoundaryArcAngleBudget D (F.rawTurn a) where
  geometricAngleBudget := totalTurn (F.rawTurn a)
  totalTurn_le_geometricAngleBudget := le_rfl
  geometricAngleBudget_lt_pi_div_three :=
    F.totalTurn_lt_pi_div_three_of_not_concave ha

@[simp] theorem boundaryAngleBudgetOfNonconcave_geometricAngleBudget
    (F : BoundaryLongArcFacts.{u} D) {a : F.LongArc}
    (ha : Not (F.concave a)) :
    (F.boundaryAngleBudgetOfNonconcave ha).geometricAngleBudget =
      totalTurn (F.rawTurn a) :=
  rfl

/-- Package one proved nonconcave long arc as boundary-budget data. -/
def toNonconcaveArcBoundaryBudgetDataOfNonconcave
    (F : BoundaryLongArcFacts.{u} D) {a : F.LongArc}
    (ha : Not (F.concave a)) :
    NonconcaveArcBoundaryBudgetData.{u} G where
  planarBoundary := D
  rawTurn := F.rawTurn a
  rawTurn_nonnegative_on_arc := F.rawTurn_nonnegative_on_arc a
  boundaryAngleBudget := F.boundaryAngleBudgetOfNonconcave ha

@[simp] theorem toNonconcaveArcBoundaryBudgetDataOfNonconcave_rawTurn
    (F : BoundaryLongArcFacts.{u} D) {a : F.LongArc}
    (ha : Not (F.concave a)) :
    (F.toNonconcaveArcBoundaryBudgetDataOfNonconcave ha).rawTurn =
      F.rawTurn a :=
  rfl

@[simp] theorem toNonconcaveArcBoundaryBudgetDataOfNonconcave_budget
    (F : BoundaryLongArcFacts.{u} D) {a : F.LongArc}
    (ha : Not (F.concave a)) :
    BoundaryArcAngleBudget.geometricAngleBudget
        ((F.toNonconcaveArcBoundaryBudgetDataOfNonconcave ha).boundaryAngleBudget) =
      totalTurn (F.rawTurn a) :=
  rfl

/-- The selected nonconcave long arc supplied by the finite count gap. -/
noncomputable def selectedLongArc
    (F : BoundaryLongArcFacts.{u} D) : F.LongArc :=
  Classical.choose F.exists_nonconcave_longArc

/-- The selected long arc is nonconcave. -/
theorem selectedLongArc_not_concave
    (F : BoundaryLongArcFacts.{u} D) :
    Not (F.concave F.selectedLongArc) :=
  Classical.choose_spec F.exists_nonconcave_longArc

/-- The selected long arc has total turn below `pi / 3`. -/
theorem selectedLongArc_totalTurn_lt_pi_div_three
    (F : BoundaryLongArcFacts.{u} D) :
    totalTurn (F.rawTurn F.selectedLongArc) < Real.pi / 3 :=
  F.totalTurn_lt_pi_div_three_of_not_concave
    F.selectedLongArc_not_concave

/-- Select a concrete nonconcave long arc and package it as boundary-budget
data. -/
noncomputable def toNonconcaveArcBoundaryBudgetData
    (F : BoundaryLongArcFacts.{u} D) :
    NonconcaveArcBoundaryBudgetData.{u} G :=
  F.toNonconcaveArcBoundaryBudgetDataOfNonconcave
    F.selectedLongArc_not_concave

@[simp] theorem toNonconcaveArcBoundaryBudgetData_rawTurn
    (F : BoundaryLongArcFacts.{u} D) :
    F.toNonconcaveArcBoundaryBudgetData.rawTurn =
      F.rawTurn F.selectedLongArc :=
  rfl

/-- The selected boundary-budget data has the selected arc's total turn as its
angle budget. -/
@[simp] theorem toNonconcaveArcBoundaryBudgetData_geometricAngleBudget
    (F : BoundaryLongArcFacts.{u} D) :
    BoundaryArcAngleBudget.geometricAngleBudget
      F.toNonconcaveArcBoundaryBudgetData.boundaryAngleBudget =
      totalTurn (F.rawTurn F.selectedLongArc) :=
  rfl

/-- The selected boundary-budget data reduces to normalized M8 turn bounds. -/
def toM8TurnBounds
    (F : BoundaryLongArcFacts.{u} D) :
    M8ConstructionInterface.M8TurnBounds :=
  F.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds

/-- The selected M8 turn function is nonnegative. -/
theorem toM8TurnBounds_turn_nonnegative
    (F : BoundaryLongArcFacts.{u} D) (k : Nat) :
    0 <= F.toM8TurnBounds.turn k :=
  F.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_turn_nonnegative k

/-- The selected M8 total turn is below `pi / 3`. -/
theorem toM8TurnBounds_totalTurn_lt_pi_div_three
    (F : BoundaryLongArcFacts.{u} D) :
    totalTurn F.toM8TurnBounds.turn < Real.pi / 3 :=
  F.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_totalTurn_lt_pi_div_three

end BoundaryLongArcFacts

end NonconcaveArcConcrete
end Swanepoel
end ErdosProblems1066

end
