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
open M8WindowGeometryFromContainment
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

/-- The named E23 lower bound is already incompatible with an honest global
turn budget at any legal adjacent pair of failures. -/
theorem adjacent_failures_impossible_of_E23
    {good : Nat -> Prop} (T : HonestTurnBounds)
    (hE23 : Figure9AdjacentWindowLowerE23 good T.turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    False := by
  have hlower : Real.pi / 3 <= adjacentTurn T.turn i :=
    hE23 hi hi_next hbad_i hbad_next
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

/-! ## Contained witnesses and containment interfaces -/

/-- Projection from contained-data form to the adjacent turn lower bound. -/
theorem adjacentTurn_lower_of_containedData
    {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftContainedData turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  adjacentTurn_lower_of_leftContainment
    D.distanceData D.left_angle_le_adjacentTurn

/-- A contained-data Figure 9 witness contradicts an honest turn budget on
the same legal adjacent window. -/
theorem false_of_containedData_honestTurnBudget
    (T : HonestTurnBounds) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (D : Figure9AdjacentLeftContainedData T.turn i) :
    False :=
  false_of_leftContainment_honestTurnBudget T hi hi_next
    D.distanceData D.left_angle_le_adjacentTurn

/-- Convert a concrete Figure 9 containment interface into selected
Euclidean-fact witnesses.  This keeps callers from repeatedly unpacking the
chosen contained witness. -/
def adjacentLeftEuclideanFacts_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentLeftEuclideanFactWitnesses good turn := by
  intro i hi hi_next hbad_i hbad_next
  let D := H.containedData (i := i) hi hi_next hbad_i hbad_next
  exact adjacentLeftFacts_of_distanceContainment
    D.distanceData D.left_angle_le_adjacentTurn

/-- Pointwise adjacent-window lower bound from a Figure 9 containment
interface. -/
theorem adjacentTurn_lower_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Real.pi / 3 <= adjacentTurn turn i :=
  adjacentTurn_lower_of_containedData
    (H.containedData (i := i) hi hi_next hbad_i hbad_next)

/-- A Figure 9 containment interface gives the named E23 lower-bound
hypothesis directly through the angle-budget layer. -/
theorem E23_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentWindowLowerE23 good turn := by
  intro i hi hi_next hbad_i hbad_next
  exact adjacentTurn_lower_of_containmentInterface H
    hi hi_next hbad_i hbad_next

/-- A Figure 9 containment interface gives the raw adjacent-failures
force-turn hypothesis. -/
theorem adjacentFailuresForceTurn_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    AdjacentFailuresForceTurn good turn :=
  adjacentFailuresForceTurn_of_E23
    (E23_of_containmentInterface H)

/-- Under an honest turn budget, a Figure 9 containment interface rules out
the adjacent failed pair that selected its witness. -/
theorem adjacent_failures_impossible_of_containmentInterface
    {good : Nat -> Prop} (T : HonestTurnBounds)
    (H : Figure9AdjacentLeftContainmentInterface good T.turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    False :=
  false_of_containedData_honestTurnBudget T hi hi_next
    (H.containedData (i := i) hi hi_next hbad_i hbad_next)

/-! ## Combined containment bridges -/

/-- Projection of the Figure 9 / E23 half of a combined containment bridge. -/
theorem E23_of_angleContainmentBridges
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AngleContainmentBridges good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_containmentInterface H.figure9

/-- Projection of the raw adjacent-failures force-turn interface from a
combined containment bridge. -/
theorem adjacentFailuresForceTurn_of_angleContainmentBridges
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AngleContainmentBridges good turn) :
    AdjacentFailuresForceTurn good turn :=
  adjacentFailuresForceTurn_of_containmentInterface H.figure9

/-- Under an honest turn budget, a combined containment bridge rules out
adjacent failed comparisons. -/
theorem adjacent_failures_impossible_of_angleContainmentBridges
    {good : Nat -> Prop} (T : HonestTurnBounds)
    (H : AngleContainmentBridges good T.turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    False :=
  adjacent_failures_impossible_of_containmentInterface T H.figure9
    hi hi_next hbad_i hbad_next

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

/-- Honest M8 form of the generic E23 contradiction for adjacent failures. -/
theorem honest_adjacent_failures_impossible_of_E23
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} (T : HonestTurnBounds)
    (hE23 : HonestFigure9AdjacentWindowLowerE23 P T.turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood P.data i))
    (hbad_next : Not (M8BrokenLatticeGood P.data (i + 1))) :
    False :=
  adjacent_failures_impossible_of_E23
    (good := M8BrokenLatticeGood P.data) T hE23
    hi hi_next hbad_i hbad_next

/-- Honest M8 Figure 9 containment implies the named E23 hypothesis through
the angle-budget facade. -/
theorem honestE23_of_containmentInterface
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood P.data) turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  E23_of_containmentInterface H

/-- Honest M8 Figure 9 containment projected to the raw adjacent-failures
force-turn interface. -/
theorem honestAdjacentFailuresForceTurn_of_containmentInterface
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood P.data) turn) :
    AdjacentFailuresForceTurn (M8BrokenLatticeGood P.data) turn :=
  adjacentFailuresForceTurn_of_containmentInterface H

/-- Under an honest turn budget, honest M8 Figure 9 containment rules out
adjacent broken-lattice failures. -/
theorem honest_adjacent_failures_impossible_of_containmentInterface
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} (T : HonestTurnBounds)
    (H :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood P.data) T.turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood P.data i))
    (hbad_next : Not (M8BrokenLatticeGood P.data (i + 1))) :
    False :=
  adjacent_failures_impossible_of_containmentInterface T H
    hi hi_next hbad_i hbad_next

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

/-! ## Projections from existing M8 window-containment packages -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- Forget construction-level M8 turn bounds to the generic honest turn-budget
record used by the local contradiction lemmas. -/
def honestTurnBounds_of_constructionTurnBounds
    (T : M8TurnBounds) : HonestTurnBounds where
  turn := T.turn
  turn_nonnegative := T.turn_nonnegative
  total_turn_lt_pi_div_three := T.total_turn_lt_pi_div_three

/-- Construction-level M8 turn bounds put every legal adjacent window below
`pi / 3`. -/
theorem adjacentTurn_lt_pi_div_three_of_m8TurnBounds
    (T : M8TurnBounds) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10) :
    adjacentTurn T.turn i < Real.pi / 3 :=
  adjacentTurn_lt_pi_div_three_of_honestTurnBounds
    (honestTurnBounds_of_constructionTurnBounds T) hi hi_next

/-- The Figure 9 field of an M8 window-containment package as selected
Euclidean-fact witnesses. -/
def honestAdjacentLeftEuclideanFacts_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentLeftEuclideanFactWitnesses
      localLabels.predicates turnBounds.turn :=
  adjacentLeftEuclideanFacts_of_containmentInterface W.figure9_left

/-- Projection to honest E23 through the Figure 9 angle-budget facade. -/
theorem honestFigure9AdjacentWindowLowerE23_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  honestE23_of_containmentInterface W.figure9_left

/-- Projection to the raw adjacent-failures force-turn interface through the
Figure 9 angle-budget facade. -/
theorem honestAdjacentFailuresForceTurn_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    AdjacentFailuresForceTurn
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  adjacentFailuresForceTurn_of_containmentInterface W.figure9_left

/-- Under construction-level M8 turn bounds, the Figure 9 window-containment
field rules out adjacent broken-lattice failures. -/
theorem honest_adjacent_failures_impossible_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1))) :
    False :=
  honest_adjacent_failures_impossible_of_containmentInterface
    (P := localLabels.predicates)
    (honestTurnBounds_of_constructionTurnBounds turnBounds)
    W.figure9_left hi hi_next hbad_i hbad_next

end Figure9ContainmentAngleBudget
end Swanepoel
end ErdosProblems1066

end
