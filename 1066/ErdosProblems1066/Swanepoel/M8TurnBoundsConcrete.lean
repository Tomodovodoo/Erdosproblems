import ErdosProblems1066.Swanepoel.M8TurnBoundsFromArc
import ErdosProblems1066.Swanepoel.TurnBoundsInterface
import ErdosProblems1066.Swanepoel.Lemma10Inequalities

/-!
# Concrete M8 turn-bound projections

This module is a standalone projection layer from explicit nonconcave-arc turn
data to the two turn-bound records already used by the M8 pipeline:
`TurnBoundsInterface.HonestTurnBounds` and
`M8ConstructionInterface.M8TurnBounds`.

No new geometric content is introduced here.  All facts are field projections
or consequences of the normalization in `M8TurnBoundsFromArc` and the finite
turn-window inequalities in `Lemma10Inequalities`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace M8TurnBoundsConcrete

open Lemma10Inequalities
open M8ConstructionInterface
open M8TurnBoundsFromArc
open TurnBoundsInterface

/-! ## Concrete packages from nonconcave arc data -/

/-- The honest turn-bound package determined by explicit nonconcave arc data. -/
def honestTurnBounds (A : NonconcaveArcTurnData) :
    HonestTurnBounds :=
  A.toHonestTurnBounds

/-- The construction-level M8 turn-bound package determined by explicit
nonconcave arc data. -/
def m8TurnBounds (A : NonconcaveArcTurnData) :
    M8ConstructionInterface.M8TurnBounds :=
  A.toM8TurnBounds

@[simp] theorem honestTurnBounds_turn (A : NonconcaveArcTurnData) :
    (honestTurnBounds A).turn = A.turn :=
  rfl

@[simp] theorem m8TurnBounds_turn (A : NonconcaveArcTurnData) :
    (m8TurnBounds A).turn = A.turn :=
  rfl

/-- Forgetting the concrete M8 turn bounds gives back the same honest turn
package. -/
theorem honestTurnBounds_of_m8TurnBounds_eq
    (A : NonconcaveArcTurnData) :
    honestTurnBounds_of_m8TurnBounds (m8TurnBounds A) =
      honestTurnBounds A :=
  rfl

/-- Repackaging the honest turn bounds gives back the same concrete M8 turn
bounds. -/
theorem m8TurnBounds_of_honestTurnBounds_eq
    (A : NonconcaveArcTurnData) :
    m8TurnBounds_of_honestTurnBounds (honestTurnBounds A) =
      m8TurnBounds A :=
  rfl

/-! ## Pointwise projections -/

/-- On the arc indices `1, ..., 13`, the M8 turn function is the supplied raw
turn function. -/
@[simp] theorem m8TurnBounds_turn_of_mem
    (A : NonconcaveArcTurnData) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    (m8TurnBounds A).turn k = A.rawTurn k := by
  simpa [m8TurnBounds] using A.turn_of_mem hk

/-- Off the arc indices, the M8 turn function is normalized to zero. -/
@[simp] theorem m8TurnBounds_turn_of_not_mem
    (A : NonconcaveArcTurnData) {k : Nat}
    (hk : Not (Membership.mem turnIndexSet k)) :
    (m8TurnBounds A).turn k = 0 := by
  simpa [m8TurnBounds] using A.turn_of_not_mem hk

/-- The concrete M8 package projects the global nonnegativity field. -/
theorem m8TurnBounds_nonnegative
    (A : NonconcaveArcTurnData) (k : Nat) :
    0 <= (m8TurnBounds A).turn k :=
  (m8TurnBounds A).turn_nonnegative k

/-- The concrete M8 package projects the global total-turn bound. -/
theorem m8TurnBounds_total_turn_lt_pi_div_three
    (A : NonconcaveArcTurnData) :
    totalTurn (m8TurnBounds A).turn < Real.pi / 3 :=
  (m8TurnBounds A).total_turn_lt_pi_div_three

/-- The normalized M8 total turn is exactly the raw arc total turn. -/
theorem m8TurnBounds_totalTurn_eq_rawTurn
    (A : NonconcaveArcTurnData) :
    totalTurn (m8TurnBounds A).turn = totalTurn A.rawTurn := by
  simpa [m8TurnBounds] using A.totalTurn_turn_eq_rawTurn

/-! ## Honest-bound projections -/

/-- The honest package projects the same global nonnegativity field. -/
theorem honestTurnBounds_nonnegative
    (A : NonconcaveArcTurnData) (k : Nat) :
    0 <= (honestTurnBounds A).turn k :=
  (honestTurnBounds A).turn_nonnegative k

/-- The honest package projects the same total-turn bound. -/
theorem honestTurnBounds_total_turn_lt_pi_div_three
    (A : NonconcaveArcTurnData) :
    totalTurn (honestTurnBounds A).turn < Real.pi / 3 :=
  (honestTurnBounds A).total_turn_lt_pi_div_three

/-- The construction-level and honest turn functions agree definitionally. -/
theorem m8TurnBounds_turn_eq_honestTurnBounds_turn
    (A : NonconcaveArcTurnData) :
    (m8TurnBounds A).turn = (honestTurnBounds A).turn :=
  rfl

/-- The construction-level and honest total turns agree definitionally. -/
theorem m8TurnBounds_totalTurn_eq_honestTurnBounds_totalTurn
    (A : NonconcaveArcTurnData) :
    totalTurn (m8TurnBounds A).turn =
      totalTurn (honestTurnBounds A).turn :=
  rfl

/-! ## Lemma 10 window-budget projections -/

/-- Any finite sub-sum inside the M8 arc lies below the concrete M8 total turn. -/
theorem m8TurnBounds_sum_le_totalTurn_of_subset
    (A : NonconcaveArcTurnData) {s : Finset Nat}
    (hsub : s <= turnIndexSet) :
    s.sum (m8TurnBounds A).turn <= totalTurn (m8TurnBounds A).turn :=
  Lemma10Inequalities.sum_le_totalTurn_of_subset hsub
    (m8TurnBounds A).turn_nonnegative

/-- Separated windows inherit nonnegativity from the concrete M8 turn bounds. -/
theorem m8TurnBounds_separatedTurn_nonnegative
    (A : NonconcaveArcTurnData) (i j : Nat) :
    0 <= separatedTurn (m8TurnBounds A).turn i j := by
  unfold separatedTurn
  exact Finset.sum_nonneg fun k _ => (m8TurnBounds A).turn_nonnegative k

/-- Adjacent windows inherit nonnegativity from the concrete M8 turn bounds. -/
theorem m8TurnBounds_adjacentTurn_nonnegative
    (A : NonconcaveArcTurnData) (i : Nat) :
    0 <= adjacentTurn (m8TurnBounds A).turn i := by
  unfold adjacentTurn
  exact Finset.sum_nonneg fun k _ => (m8TurnBounds A).turn_nonnegative k

/-- Every separated Lemma 10 turn window sits below the concrete M8 total turn
when its indices lie in the M8 range. -/
theorem m8TurnBounds_separatedTurn_le_totalTurn
    (A : NonconcaveArcTurnData) {i j : Nat}
    (hi : 1 <= i) (hj : j <= 10) :
    separatedTurn (m8TurnBounds A).turn i j <=
      totalTurn (m8TurnBounds A).turn :=
  Lemma10Inequalities.separatedTurn_le_totalTurn hi hj
    (m8TurnBounds A).turn_nonnegative

/-- Every adjacent Lemma 10 turn window sits below the concrete M8 total turn
when its indices lie in the M8 range. -/
theorem m8TurnBounds_adjacentTurn_le_totalTurn
    (A : NonconcaveArcTurnData) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10) :
    adjacentTurn (m8TurnBounds A).turn i <=
      totalTurn (m8TurnBounds A).turn :=
  Lemma10Inequalities.adjacentTurn_le_totalTurn hi hi_next
    (m8TurnBounds A).turn_nonnegative

/-! ## Raw arc restatements -/

/-- The concrete M8 total-turn bound restated on the raw arc turn function. -/
theorem raw_totalTurn_lt_pi_div_three
    (A : NonconcaveArcTurnData) :
    totalTurn A.rawTurn < Real.pi / 3 :=
  A.raw_totalTurn_lt_pi_div_three

/-- The concrete M8 pointwise nonnegativity restated on arc indices of the raw
turn function. -/
theorem rawTurn_nonnegative_on_arc
    (A : NonconcaveArcTurnData) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    0 <= A.rawTurn k :=
  A.rawTurn_nonnegative_on_arc k hk

end M8TurnBoundsConcrete
end Swanepoel
end ErdosProblems1066

end
