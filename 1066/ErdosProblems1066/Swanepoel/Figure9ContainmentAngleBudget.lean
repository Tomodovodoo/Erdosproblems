import ErdosProblems1066.Swanepoel.Figure9EuclideanFactsConcrete
import ErdosProblems1066.Swanepoel.TurnBoundsInterface

/-!
# Figure 9 adjacent-left containment against the turn budget

`Figure9EuclideanFactsConcrete` reduces an adjacent-left Figure 9 containment
witness to the local E23 lower bound `pi / 3 <= adjacentTurn turn i`.  This
module keeps the final numeric budget consequences reusable: an honest turn
package bounds every adjacent window by the total turn, so such a contained
adjacent-left witness is incompatible with the strict global `pi / 3` budget.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure9ContainmentAngleBudget

open AngleBridgeFacts
open AngleContainmentInterface
open AngleGeometry
open Figure9EuclideanFactsConcrete
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10EuclideanBridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open M8ConstructionInterface
open MinimalGraphFacts
open TurnBoundsInterface

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Local adjacent-left containment and the budget -/

/-- The reusable local Figure 9 adjacent-left lower bound, restated in the
angle-budget namespace. -/
theorem adjacentTurn_lower_of_leftContainment
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  adjacentTurn_lower_of_distanceData_leftContainment D hcontained

/-- An honest turn package places every legal adjacent window below `pi / 3`.
This is the minimal numeric budget fact used to rule out a contained
adjacent-left Figure 9 witness. -/
theorem adjacentTurn_lt_pi_div_three_of_honestTurnBounds
    (T : HonestTurnBounds) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10) :
    adjacentTurn T.turn i < Real.pi / 3 :=
  lt_of_le_of_lt (T.adjacentTurn_le_totalTurn hi hi_next)
    T.totalTurn_lt_pi_div_three

/-- A contained adjacent-left Figure 9 witness contradicts the honest global
turn budget on the same adjacent window. -/
theorem false_of_leftContainment_honestTurnBudget
    (T : HonestTurnBounds) {i : Nat} {p qi qj s r : Point}
    (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn T.turn i) :
    False := by
  have hlower : Real.pi / 3 <= adjacentTurn T.turn i :=
    adjacentTurn_lower_of_leftContainment D hcontained
  have hupper : adjacentTurn T.turn i < Real.pi / 3 :=
    adjacentTurn_lt_pi_div_three_of_honestTurnBounds T hi hi_next
  linarith

/-! ## Selected adjacent-left fact packages -/

/-- A selected adjacent-left Euclidean fact package carries the local E23 lower
bound. -/
theorem adjacentTurn_lower_of_euclideanFacts
    {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftEuclideanFacts turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  D.adjacentTurn_lower

/-- A selected adjacent-left Euclidean fact package contradicts an honest turn
budget for the same legal adjacent window. -/
theorem false_of_euclideanFacts_honestTurnBudget
    (T : HonestTurnBounds) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (D : Figure9AdjacentLeftEuclideanFacts T.turn i) :
    False := by
  have hlower : Real.pi / 3 <= adjacentTurn T.turn i :=
    adjacentTurn_lower_of_euclideanFacts D
  have hupper : adjacentTurn T.turn i < Real.pi / 3 :=
    adjacentTurn_lt_pi_div_three_of_honestTurnBounds T hi hi_next
  linarith

/-! ## Uniform witnesses and E23 -/

/-- Uniform selected adjacent-left Euclidean facts imply E23.  This restates
the direct route from `Figure9EuclideanFactsConcrete` for downstream modules
that import the budget layer. -/
theorem E23_of_adjacentLeftEuclideanFacts
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftEuclideanFactWitnesses good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_euclideanFactWitnesses_direct H

/-- E23 from selected adjacent-left facts converted to the raw adjacent
force-turn interface used by the finite turn arithmetic. -/
theorem adjacentFailuresForceTurn_of_adjacentLeftEuclideanFacts
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftEuclideanFactWitnesses good turn) :
    AdjacentFailuresForceTurn good turn :=
  adjacentFailuresForceTurn_of_E23
    (E23_of_adjacentLeftEuclideanFacts H)

/-- Under an honest turn budget, selected adjacent-left Euclidean witnesses
rule out any adjacent pair of failed comparisons. -/
theorem adjacent_failures_impossible_of_euclideanFactWitnesses
    {good : Nat -> Prop} (T : HonestTurnBounds)
    (H : Figure9AdjacentLeftEuclideanFactWitnesses good T.turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    False :=
  false_of_euclideanFacts_honestTurnBudget T hi hi_next
    (H (i := i) hi hi_next hbad_i hbad_next)

/-! ## Honest M8 projection -/

/-- Honest M8 selected adjacent-left Euclidean facts imply the named E23
hypothesis. -/
theorem honestE23_of_adjacentLeftEuclideanFacts
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftEuclideanFactWitnesses P turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  honestE23_of_euclideanFactWitnesses H

/-- Under an honest turn budget, honest M8 selected adjacent-left facts rule
out any adjacent pair of broken-lattice failures. -/
theorem honest_adjacent_failures_impossible_of_euclideanFactWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} (T : HonestTurnBounds)
    (H : HonestFigure9AdjacentLeftEuclideanFactWitnesses P T.turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood P.data i))
    (hbad_next : Not (M8BrokenLatticeGood P.data (i + 1))) :
    False :=
  adjacent_failures_impossible_of_euclideanFactWitnesses T H
    hi hi_next hbad_i hbad_next

end Figure9ContainmentAngleBudget
end Swanepoel
end ErdosProblems1066

end
