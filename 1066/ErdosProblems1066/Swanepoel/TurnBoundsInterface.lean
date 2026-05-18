import ErdosProblems1066.Swanepoel.AngleContainmentInterface
import ErdosProblems1066.Swanepoel.BrokenLatticeMinimalFailure

/-!
# Swanepoel turn-bounds interface

This file packages the turn function data supplied by the long-arc/broken-
lattice construction: nonnegative turns and total turn below `pi / 3`.
It then routes that honest turn package through the existing Lemma 10
angle-to-turn and broken-lattice interfaces.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace TurnBoundsInterface

open AngleContainmentInterface
open Lemma10AnalyticBridge
open Lemma10AngleToTurn
open Lemma10Bridge
open Lemma10Inequalities
open LocalConfigurations
open MinimalGraphFacts
open BrokenLatticeInterface
open BrokenLatticeMinimalFailure
open GraphBridge

open scoped BigOperators

universe u

/-! ## Honest turn bounds -/

/-- An honest turn function with exactly the global bounds needed by Lemma 10:
every turn is nonnegative and the total turn on indices `1, ..., 13` is below
`pi / 3`. -/
structure HonestTurnBounds where
  turn : Nat -> Real
  turn_nonnegative : forall k : Nat, 0 <= turn k
  total_turn_lt_pi_div_three : totalTurn turn < Real.pi / 3

namespace HonestTurnBounds

/-- Field projection as a named lemma for callers that want the pointwise
nonnegativity hypothesis. -/
theorem nonnegative (T : HonestTurnBounds) (k : Nat) :
    0 <= T.turn k :=
  T.turn_nonnegative k

/-- Field projection as a named lemma for callers that want the total-turn
bound. -/
theorem totalTurn_lt_pi_div_three (T : HonestTurnBounds) :
    totalTurn T.turn < Real.pi / 3 :=
  T.total_turn_lt_pi_div_three

/-- The total turn sum is nonnegative. -/
lemma totalTurn_nonnegative (T : HonestTurnBounds) :
    0 <= totalTurn T.turn := by
  unfold totalTurn turnIndexSet
  exact Finset.sum_nonneg fun k _ => T.turn_nonnegative k

/-- Every separated turn window is nonnegative. -/
lemma separatedTurn_nonnegative (T : HonestTurnBounds) (i j : Nat) :
    0 <= separatedTurn T.turn i j := by
  unfold separatedTurn
  exact Finset.sum_nonneg fun k _ => T.turn_nonnegative k

/-- Every adjacent turn window is nonnegative. -/
lemma adjacentTurn_nonnegative (T : HonestTurnBounds) (i : Nat) :
    0 <= adjacentTurn T.turn i := by
  unfold adjacentTurn
  exact Finset.sum_nonneg fun k _ => T.turn_nonnegative k

/-- The existing Lemma 10 finite-sum bound specialized to an honest turn
package. -/
lemma sum_le_totalTurn_of_subset (T : HonestTurnBounds) {s : Finset Nat}
    (hsub : s <= turnIndexSet) :
    s.sum T.turn <= totalTurn T.turn :=
  Lemma10Inequalities.sum_le_totalTurn_of_subset hsub T.turn_nonnegative

/-- A separated turn window sits inside the total turn budget. -/
lemma separatedTurn_le_totalTurn (T : HonestTurnBounds) {i j : Nat}
    (hi : 1 <= i) (hj : j <= 10) :
    separatedTurn T.turn i j <= totalTurn T.turn :=
  Lemma10Inequalities.separatedTurn_le_totalTurn hi hj
    T.turn_nonnegative

/-- An adjacent turn window sits inside the total turn budget. -/
lemma adjacentTurn_le_totalTurn (T : HonestTurnBounds) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10) :
    adjacentTurn T.turn i <= totalTurn T.turn :=
  Lemma10Inequalities.adjacentTurn_le_totalTurn hi hi_next
    T.turn_nonnegative

end HonestTurnBounds

/-! ## Generic Lemma 10 package -/

/-- A Lemma 10 turn package: honest turn bounds plus the two angle-to-turn
bridges that produce the E22/E23 turn-window lower bounds. -/
structure Lemma10TurnPackage (good : Nat -> Prop)
    extends HonestTurnBounds where
  figure8 : Figure8SeparatedAngleToTurnBridge good turn
  figure9 : Figure9AdjacentLeftAngleToTurnBridge good turn

namespace Lemma10TurnPackage

/-- Build a generic Lemma 10 turn package from explicit honest turn bounds and
the existing angle-to-turn bridge records. -/
def ofAngleToTurnBridges {good : Nat -> Prop}
    (T : HonestTurnBounds)
    (H8 : Figure8SeparatedAngleToTurnBridge good T.turn)
    (H9 : Figure9AdjacentLeftAngleToTurnBridge good T.turn) :
    Lemma10TurnPackage good where
  toHonestTurnBounds := T
  figure8 := H8
  figure9 := H9

/-- Build a generic Lemma 10 turn package from the more concrete containment
interface. -/
def ofAngleContainmentBridges {good : Nat -> Prop}
    (T : HonestTurnBounds)
    (H : AngleContainmentBridges good T.turn) :
    Lemma10TurnPackage good :=
  ofAngleToTurnBridges T
    H.figure8.toAngleToTurnBridge H.figure9.toAngleToTurnBridge

/-- Forget a turn package to the pair of angle-to-turn bridges. -/
def toAngleToTurnBridges {good : Nat -> Prop}
    (H : Lemma10TurnPackage good) :
    Figure8SeparatedAngleToTurnBridge good H.turn /\
      Figure9AdjacentLeftAngleToTurnBridge good H.turn :=
  And.intro H.figure8 H.figure9

/-- Convert the angle-to-turn bridges to the named E22/E23 hypotheses. -/
theorem E22_E23 {good : Nat -> Prop}
    (H : Lemma10TurnPackage good) :
    Figure8SeparatedWindowLowerE22 good H.turn /\
      Figure9AdjacentWindowLowerE23 good H.turn :=
  E22_E23_of_angleToTurnBridges H.figure8 H.figure9

/-- Projection of the converted Figure 8 / E22 turn-window hypothesis. -/
theorem E22 {good : Nat -> Prop}
    (H : Lemma10TurnPackage good) :
    Figure8SeparatedWindowLowerE22 good H.turn :=
  (H.E22_E23).1

/-- Projection of the converted Figure 9 / E23 turn-window hypothesis. -/
theorem E23 {good : Nat -> Prop}
    (H : Lemma10TurnPackage good) :
    Figure9AdjacentWindowLowerE23 good H.turn :=
  (H.E22_E23).2

/-- Convert the Figure 8 / E22 hypothesis into the raw turn-force interface
used by `Lemma10Inequalities`. -/
theorem separatedFailuresForceTurn {good : Nat -> Prop}
    (H : Lemma10TurnPackage good) :
    SeparatedFailuresForceTurn good H.turn :=
  separatedFailuresForceTurn_of_E22 H.E22

/-- Convert the Figure 9 / E23 hypothesis into the raw turn-force interface
used by `Lemma10Inequalities`. -/
theorem adjacentFailuresForceTurn {good : Nat -> Prop}
    (H : Lemma10TurnPackage good) :
    AdjacentFailuresForceTurn good H.turn :=
  adjacentFailuresForceTurn_of_E23 H.E23

/-- The generic Lemma 10 finite consequence supplied by an honest turn package
and angle-to-turn bridges. -/
theorem card_le_one_failures {good : Nat -> Prop}
    [DecidablePred good] (H : Lemma10TurnPackage good) :
    ((Finset.Icc 1 10).filter fun i => Not (good i)).card <= 1 :=
  card_le_one_failures_of_E22_E23 good H.turn H.turn_nonnegative
    H.total_turn_lt_pi_div_three H.E22 H.E23

end Lemma10TurnPackage

/-! ## Honest `m = 8` broken-lattice package -/

/-- An honest `m = 8` broken-lattice turn package.  The local predicate
package supplies the actual Lemma 10 good predicate; the turn package supplies
nonnegativity, the total-turn bound, and the Figure 8/Figure 9 angle-to-turn
bridges. -/
structure M8HonestTurnPackage
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G)
    extends HonestTurnBounds where
  figure8 :
    Figure8SeparatedAngleToTurnBridge
      (M8BrokenLatticeGood P.data) turn
  figure9 :
    Figure9AdjacentLeftAngleToTurnBridge
      (M8BrokenLatticeGood P.data) turn

namespace M8HonestTurnPackage

variable {V : Type u} {G : LocalGraph V}
variable {P : M8HonestLocalPredicates G}

/-- Build an honest `m = 8` turn package from explicit turn bounds and
angle-to-turn bridge records. -/
def ofAngleToTurnBridges
    (T : HonestTurnBounds)
    (H8 :
      Figure8SeparatedAngleToTurnBridge
        (M8BrokenLatticeGood P.data) T.turn)
    (H9 :
      Figure9AdjacentLeftAngleToTurnBridge
        (M8BrokenLatticeGood P.data) T.turn) :
    M8HonestTurnPackage P where
  toHonestTurnBounds := T
  figure8 := H8
  figure9 := H9

/-- Build an honest `m = 8` turn package from the concrete containment
interface. -/
def ofAngleContainmentBridges
    (T : HonestTurnBounds)
    (H : AngleContainmentBridges (M8BrokenLatticeGood P.data) T.turn) :
    M8HonestTurnPackage P :=
  ofAngleToTurnBridges T
    H.figure8.toAngleToTurnBridge H.figure9.toAngleToTurnBridge

/-- Forget an honest broken-lattice turn package to the generic Lemma 10
package for its underlying good predicate. -/
def toLemma10TurnPackage (H : M8HonestTurnPackage P) :
    Lemma10TurnPackage (M8BrokenLatticeGood P.data) where
  toHonestTurnBounds := H.toHonestTurnBounds
  figure8 := H.figure8
  figure9 := H.figure9

/-- Convert the honest broken-lattice turn package to the pair of named
E22/E23 hypotheses. -/
theorem E22_E23 (H : M8HonestTurnPackage P) :
    HonestFigure8SeparatedWindowLowerE22 P H.turn /\
      HonestFigure9AdjacentWindowLowerE23 P H.turn := by
  simpa [HonestFigure8SeparatedWindowLowerE22,
    HonestFigure9AdjacentWindowLowerE23,
    M8Figure8SeparatedWindowLowerE22,
    M8Figure9AdjacentWindowLowerE23] using
    H.toLemma10TurnPackage.E22_E23

/-- Projection of the honest Figure 8 / E22 turn-window hypothesis. -/
theorem E22 (H : M8HonestTurnPackage P) :
    HonestFigure8SeparatedWindowLowerE22 P H.turn :=
  (H.E22_E23).1

/-- Projection of the honest Figure 9 / E23 turn-window hypothesis. -/
theorem E23 (H : M8HonestTurnPackage P) :
    HonestFigure9AdjacentWindowLowerE23 P H.turn :=
  (H.E22_E23).2

/-- The honest turn package supplies the local Lemma 10 at-most-one-failure
conclusion. -/
theorem atMostOneFailure (H : M8HonestTurnPackage P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    P.AtMostOneFailure :=
  m8_atMostOneFailure_of_E22_E23 P.data H.turn
    H.turn_nonnegative H.total_turn_lt_pi_div_three H.E22 H.E23

/-- The honest turn package plus Lemma 9 late triples gives the checked
broken-lattice contradiction. -/
theorem contradiction (H : M8HonestTurnPackage P)
    (hlate : P.LateTriples) :
    False :=
  honestContradiction_of_E22_E23 P H.turn
    H.turn_nonnegative H.total_turn_lt_pi_div_three
    H.E22 H.E23 hlate

/-- Convert an honest turn package into the construction-data package consumed
by `BrokenLatticeMinimalFailure`. -/
def toConstructionData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {Q : M8HonestLocalPredicates (unitDistanceLocalGraph C)}
    (H : M8HonestTurnPackage Q)
    (hlate : Q.LateTriples) :
    M8ConstructionData C hmin where
  predicates := Q
  turn := H.turn
  turn_nonnegative := H.turn_nonnegative
  total_turn_lt_pi_div_three := H.total_turn_lt_pi_div_three
  figure8_E22 := H.E22
  figure9_E23 := H.E23
  lateTriples := hlate

/-- Convert an honest turn package directly into the broken-lattice interface
package. -/
def toBrokenLatticeData
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    {Q : M8HonestLocalPredicates (unitDistanceLocalGraph C)}
    (H : M8HonestTurnPackage Q)
    (hlate : Q.LateTriples) :
    M8MinimalFailureBrokenLatticeData C where
  minimalFailure := hmin
  predicates := Q
  turn := H.turn
  turn_nonnegative := H.turn_nonnegative
  total_turn_lt_pi_div_three := H.total_turn_lt_pi_div_three
  figure8_E22 := H.E22
  figure9_E23 := H.E23
  lateTriples := hlate

/-- Direct contradiction for a minimal cleared failure once the honest turn
package and late-triples hypothesis are supplied. -/
theorem contradiction_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    {Q : M8HonestLocalPredicates (unitDistanceLocalGraph C)}
    (H : M8HonestTurnPackage Q)
    (hlate : Q.LateTriples) :
    False :=
  (toBrokenLatticeData hmin H hlate).contradiction

end M8HonestTurnPackage

end TurnBoundsInterface
end Swanepoel
end ErdosProblems1066

end
