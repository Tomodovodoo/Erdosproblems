import ErdosProblems1066.Swanepoel.NonconcaveArcConcrete
import ErdosProblems1066.Swanepoel.M8TurnBoundsConcrete

set_option autoImplicit false

/-!
# Nonconcave arc angle facts

This file isolates the remaining nonconcave-arc angle input as a small real
inequality package and proves the arithmetic consequences needed by the
existing turn-bound pipeline.

The checked content here is only normalization and budget arithmetic.  The
geometric angle estimates themselves remain explicit fields:

* raw turns are nonnegative on the arc indices `1, ..., 13`;
* the raw total turn is bounded by a geometric angle budget;
* that budget is below `pi / 3`.

Those facts are enough to build `M8TurnBoundsFromArc.NonconcaveArcTurnData`,
and hence the concrete M8 turn-bound records.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NonconcaveArcAngleFacts

open Lemma10Inequalities
open M8TurnBoundsConcrete
open M8TurnBoundsFromArc
open NonconcaveArcConcrete

/-! ## Raw angle-budget facts -/

/--
Minimal remaining geometric input for one nonconcave arc.

The field `totalTurn_le_geometricAngleBudget` is the place where the actual
outer-boundary/subpolygon angle comparison enters.  Everything below this
structure is a checked reduction from those real inequalities to the turn data
used by the M8 construction.
-/
structure NonconcaveArcGeometricAngleFacts where
  rawTurn : Nat -> Real
  geometricAngleBudget : Real
  rawTurn_nonnegative_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k
  totalTurn_le_geometricAngleBudget :
    totalTurn rawTurn <= geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :
    geometricAngleBudget < Real.pi / 3

namespace NonconcaveArcGeometricAngleFacts

/-- The raw total turn inherits the strict `pi / 3` bound from the geometric
budget. -/
theorem raw_totalTurn_lt_pi_div_three
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.rawTurn < Real.pi / 3 :=
  lt_of_le_of_lt A.totalTurn_le_geometricAngleBudget
    A.geometricAngleBudget_lt_pi_div_three

/-- The raw total turn is nonnegative because each arc turn is nonnegative. -/
theorem raw_totalTurn_nonnegative
    (A : NonconcaveArcGeometricAngleFacts) :
    0 <= totalTurn A.rawTurn := by
  unfold totalTurn
  exact Finset.sum_nonneg fun k hk =>
    A.rawTurn_nonnegative_on_arc k hk

/-- The geometric budget is nonnegative as a consequence of the raw total-turn
lower bound and the supplied budget comparison. -/
theorem geometricAngleBudget_nonnegative
    (A : NonconcaveArcGeometricAngleFacts) :
    0 <= A.geometricAngleBudget :=
  le_trans A.raw_totalTurn_nonnegative
    A.totalTurn_le_geometricAngleBudget

/-- Expand the total turn into the thirteen raw arc turns. -/
theorem raw_totalTurn_eq_sum_thirteen
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.rawTurn =
      A.rawTurn 1 + A.rawTurn 2 + A.rawTurn 3 + A.rawTurn 4 +
      A.rawTurn 5 + A.rawTurn 6 + A.rawTurn 7 + A.rawTurn 8 +
      A.rawTurn 9 + A.rawTurn 10 + A.rawTurn 11 + A.rawTurn 12 +
      A.rawTurn 13 := by
  unfold totalTurn turnIndexSet
  norm_num [Finset.sum_Icc_succ_top, add_assoc]

/-! ## Normalization off the arc -/

/-- The normalized turn function keeps raw turns on `1, ..., 13` and is zero
outside those arc indices. -/
def normalizedTurn (A : NonconcaveArcGeometricAngleFacts) (k : Nat) :
    Real :=
  if Membership.mem turnIndexSet k then A.rawTurn k else 0

@[simp]
theorem normalizedTurn_of_mem
    (A : NonconcaveArcGeometricAngleFacts) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    A.normalizedTurn k = A.rawTurn k := by
  simp [normalizedTurn, hk]

@[simp]
theorem normalizedTurn_of_not_mem
    (A : NonconcaveArcGeometricAngleFacts) {k : Nat}
    (hk : Not (Membership.mem turnIndexSet k)) :
    A.normalizedTurn k = 0 := by
  simp [normalizedTurn, hk]

/-- The normalized turn is nonnegative at every natural index. -/
theorem normalizedTurn_nonnegative
    (A : NonconcaveArcGeometricAngleFacts) (k : Nat) :
    0 <= A.normalizedTurn k := by
  by_cases hk : Membership.mem turnIndexSet k
  case pos =>
    simpa [normalizedTurn, hk] using
      A.rawTurn_nonnegative_on_arc k hk
  case neg =>
    simp [normalizedTurn, hk]

/-- Normalization does not change the total turn, since the total only sums
over the arc index set. -/
theorem totalTurn_normalizedTurn_eq_rawTurn
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.normalizedTurn = totalTurn A.rawTurn := by
  unfold totalTurn
  apply Finset.sum_congr rfl
  intro k hk
  exact A.normalizedTurn_of_mem hk

/-- The normalized total turn is bounded by the same geometric budget. -/
theorem totalTurn_normalizedTurn_le_geometricAngleBudget
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.normalizedTurn <= A.geometricAngleBudget := by
  simpa [A.totalTurn_normalizedTurn_eq_rawTurn] using
    A.totalTurn_le_geometricAngleBudget

/-- The normalized total turn is below `pi / 3`. -/
theorem totalTurn_normalizedTurn_lt_pi_div_three
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.normalizedTurn < Real.pi / 3 := by
  simpa [A.totalTurn_normalizedTurn_eq_rawTurn] using
    A.raw_totalTurn_lt_pi_div_three

/-! ## Conversion to existing concrete interfaces -/

/-- Repackage the geometric facts as the existing concrete angle-inequality
record. -/
def toNonconcaveArcAngleInequalities
    (A : NonconcaveArcGeometricAngleFacts) :
    NonconcaveArcAngleInequalities where
  rawTurn := A.rawTurn
  geometricAngleBudget := A.geometricAngleBudget
  rawTurn_nonnegative_on_arc := A.rawTurn_nonnegative_on_arc
  totalTurn_le_geometricAngleBudget :=
    A.totalTurn_le_geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :=
    A.geometricAngleBudget_lt_pi_div_three

@[simp]
theorem toNonconcaveArcAngleInequalities_rawTurn
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toNonconcaveArcAngleInequalities.rawTurn = A.rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcAngleInequalities_geometricAngleBudget
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toNonconcaveArcAngleInequalities.geometricAngleBudget =
      A.geometricAngleBudget :=
  rfl

/-- The minimal geometric angle facts produce the arc turn data expected by
`M8TurnBoundsFromArc`. -/
def toNonconcaveArcTurnData
    (A : NonconcaveArcGeometricAngleFacts) :
    NonconcaveArcTurnData where
  rawTurn := A.rawTurn
  rawTurn_nonnegative_on_arc := A.rawTurn_nonnegative_on_arc
  raw_totalTurn_lt_pi_div_three :=
    A.raw_totalTurn_lt_pi_div_three

@[simp]
theorem toNonconcaveArcTurnData_rawTurn
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toNonconcaveArcTurnData.rawTurn = A.rawTurn :=
  rfl

/-- The normalized turn used in this file agrees with the normalization in
`NonconcaveArcTurnData`. -/
@[simp]
theorem toNonconcaveArcTurnData_turn
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toNonconcaveArcTurnData.turn = A.normalizedTurn := by
  funext k
  by_cases hk : Membership.mem turnIndexSet k
  case pos =>
    simp [NonconcaveArcTurnData.turn, normalizedTurn, hk]
  case neg =>
    simp [NonconcaveArcTurnData.turn, normalizedTurn, hk]

/-- The conversion through `NonconcaveArcConcrete` gives the same raw turn
data as the direct construction above. -/
theorem concrete_toNonconcaveArcTurnData_eq
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toNonconcaveArcAngleInequalities.toNonconcaveArcTurnData =
      A.toNonconcaveArcTurnData :=
  rfl

/-- The existing arc-data total-turn normalization is the same equality proved
directly above. -/
theorem arcData_totalTurn_turn_eq_rawTurn
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.toNonconcaveArcTurnData.turn =
      totalTurn A.rawTurn := by
  simpa [A.toNonconcaveArcTurnData_turn] using
    A.totalTurn_normalizedTurn_eq_rawTurn

/-- Honest turn bounds produced from the minimal geometric facts. -/
def toHonestTurnBounds
    (A : NonconcaveArcGeometricAngleFacts) :
    TurnBoundsInterface.HonestTurnBounds :=
  M8TurnBoundsConcrete.honestTurnBounds A.toNonconcaveArcTurnData

/-- Construction-level M8 turn bounds produced from the minimal geometric
facts. -/
def toM8TurnBounds
    (A : NonconcaveArcGeometricAngleFacts) :
    M8ConstructionInterface.M8TurnBounds :=
  M8TurnBoundsConcrete.m8TurnBounds A.toNonconcaveArcTurnData

@[simp]
theorem toHonestTurnBounds_turn
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toHonestTurnBounds.turn = A.normalizedTurn := by
  simp [toHonestTurnBounds,
    A.toNonconcaveArcTurnData_turn
  ]

@[simp]
theorem toM8TurnBounds_turn
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toM8TurnBounds.turn = A.normalizedTurn := by
  simp [toM8TurnBounds,
    A.toNonconcaveArcTurnData_turn
  ]

/-- Pointwise M8 turn nonnegativity after normalization. -/
theorem toM8TurnBounds_turn_nonnegative
    (A : NonconcaveArcGeometricAngleFacts) (k : Nat) :
    0 <= A.toM8TurnBounds.turn k := by
  simpa [A.toM8TurnBounds_turn] using
    A.normalizedTurn_nonnegative k

/-- The M8 total turn is bounded by the supplied geometric angle budget. -/
theorem toM8TurnBounds_totalTurn_le_geometricAngleBudget
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.toM8TurnBounds.turn <= A.geometricAngleBudget := by
  simpa [A.toM8TurnBounds_turn] using
    A.totalTurn_normalizedTurn_le_geometricAngleBudget

/-- The M8 total turn is below `pi / 3`. -/
theorem toM8TurnBounds_totalTurn_lt_pi_div_three
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.toM8TurnBounds.turn < Real.pi / 3 := by
  simpa [A.toM8TurnBounds_turn] using
    A.totalTurn_normalizedTurn_lt_pi_div_three

end NonconcaveArcGeometricAngleFacts

end NonconcaveArcAngleFacts
end Swanepoel
end ErdosProblems1066

end
