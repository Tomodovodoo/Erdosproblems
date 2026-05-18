import ErdosProblems1066.Swanepoel.AngleArithmetic
import ErdosProblems1066.Swanepoel.Lemma10Pipeline

/-!
# Swanepoel Lemma 10 analytic bridge

This module names the two Euclidean analytic obligations used in Swanepoel's
Lemma 10 and transports them into the existing finite turn-budget interfaces.

The trigonometric content is not proved here.  `Figure8SeparatedWindowLowerE22`
and `Figure9AdjacentWindowLowerE23` are explicit hypotheses, already reduced to
the turn-window inequalities consumed by `Swanepoel.Lemma10Inequalities`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma10AnalyticBridge

open AngleArithmetic
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10Pipeline
open LocalConfigurations

universe u

noncomputable section

/-! ## Named analytic hypotheses -/

/-- E22 / Figure 8 analytic obligation, after the Euclidean angle accounting
has reduced it to the separated-failure turn window used by the finite
pipeline. -/
def Figure8SeparatedWindowLowerE22
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  SeparatedWindowLower good turn

/-- E23 / Figure 9 analytic obligation, after the Euclidean angle accounting
has reduced it to the adjacent-failure turn window used by the finite
pipeline. -/
def Figure9AdjacentWindowLowerE23
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  AdjacentWindowLower good turn

theorem separatedWindowLower_of_E22
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hE22 : Figure8SeparatedWindowLowerE22 good turn) :
    SeparatedWindowLower good turn :=
  hE22

theorem adjacentWindowLower_of_E23
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hE23 : Figure9AdjacentWindowLowerE23 good turn) :
    AdjacentWindowLower good turn :=
  hE23

theorem separatedFailuresForceTurn_of_E22
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hE22 : Figure8SeparatedWindowLowerE22 good turn) :
    SeparatedFailuresForceTurn good turn :=
  separatedFailuresForceTurn_of_windowLower
    (separatedWindowLower_of_E22 hE22)

theorem adjacentFailuresForceTurn_of_E23
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hE23 : Figure9AdjacentWindowLowerE23 good turn) :
    AdjacentFailuresForceTurn good turn :=
  adjacentFailuresForceTurn_of_windowLower
    (adjacentWindowLower_of_E23 hE23)

/-! ## Generic finite consequence -/

/-- E22 and E23 are exactly the named analytic assumptions needed by the
existing abstract Lemma 10 cardinal theorem. -/
theorem card_le_one_failures_of_E22_E23
    (good : Nat -> Prop) [DecidablePred good] (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hE22 : Figure8SeparatedWindowLowerE22 good turn)
    (hE23 : Figure9AdjacentWindowLowerE23 good turn) :
    ((Finset.Icc 1 10).filter fun i => Not (good i)).card <= 1 := by
  exact card_le_one_failures_of_window_lowers good turn hnonneg htotal
    (separatedWindowLower_of_E22 hE22)
    (adjacentWindowLower_of_E23 hE23)

/-! ## `m = 8` broken-lattice plumbing -/

/-- E22 specialized to the named local `m = 8` Lemma 10 predicate. -/
def M8Figure8SeparatedWindowLowerE22
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Prop :=
  Figure8SeparatedWindowLowerE22 (M8BrokenLatticeGood P) turn

/-- E23 specialized to the named local `m = 8` Lemma 10 predicate. -/
def M8Figure9AdjacentWindowLowerE23
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Prop :=
  Figure9AdjacentWindowLowerE23 (M8BrokenLatticeGood P) turn

theorem separatedFailuresForceTurn_of_m8_E22
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (hE22 : M8Figure8SeparatedWindowLowerE22 P turn) :
    SeparatedFailuresForceTurn (M8BrokenLatticeGood P) turn :=
  separatedFailuresForceTurn_of_E22 hE22

theorem adjacentFailuresForceTurn_of_m8_E23
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (hE23 : M8Figure9AdjacentWindowLowerE23 P turn) :
    AdjacentFailuresForceTurn (M8BrokenLatticeGood P) turn :=
  adjacentFailuresForceTurn_of_E23 hE23

/-- The named E22/E23 analytic hypotheses imply the local Lemma 10 conclusion:
among indices `1, ..., 10`, at most one named comparison fails. -/
theorem m8_atMostOneFailure_of_E22_E23
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real)
    [DecidablePred (M8BrokenLatticeGood P)]
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hE22 : M8Figure8SeparatedWindowLowerE22 P turn)
    (hE23 : M8Figure9AdjacentWindowLowerE23 P turn) :
    M8AtMostOneBrokenLatticeFailure P := by
  classical
  simpa [M8AtMostOneBrokenLatticeFailure, M8BrokenLatticeFailures] using
    card_le_one_failures_of_E22_E23 (M8BrokenLatticeGood P) turn
      hnonneg htotal hE22 hE23

/-- E22/E23 form of the existing local `m = 8` contradiction. -/
theorem contradiction_of_E22_E23
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hE22 : M8Figure8SeparatedWindowLowerE22 P turn)
    (hE23 : M8Figure9AdjacentWindowLowerE23 P turn)
    (htriple :
      forall a : M8TripleStartIndex,
        P.tripleEquality a <-> M8BrokenLatticeTriple P a)
    (hlate : M8BrokenLatticeLateTriples P) :
    False := by
  exact contradiction_of_turn_hypotheses P turn hnonneg htotal
    (separatedFailuresForceTurn_of_m8_E22 hE22)
    (adjacentFailuresForceTurn_of_m8_E23 hE23)
    htriple hlate

/-! ## Honest-package form -/

/-- E22 specialized to an honest local `m = 8` package. -/
def HonestFigure8SeparatedWindowLowerE22
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Prop :=
  M8Figure8SeparatedWindowLowerE22 P.data turn

/-- E23 specialized to an honest local `m = 8` package. -/
def HonestFigure9AdjacentWindowLowerE23
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Prop :=
  M8Figure9AdjacentWindowLowerE23 P.data turn

/-- Honest-package E22/E23 form of the local finite contradiction. -/
theorem honestContradiction_of_E22_E23
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hE22 : HonestFigure8SeparatedWindowLowerE22 P turn)
    (hE23 : HonestFigure9AdjacentWindowLowerE23 P turn)
    (hlate : P.LateTriples) :
    False := by
  exact honestContradiction_of_turn_hypotheses P turn hnonneg htotal
    (separatedFailuresForceTurn_of_m8_E22 hE22)
    (adjacentFailuresForceTurn_of_m8_E23 hE23)
    hlate

end

end Lemma10AnalyticBridge
end Swanepoel
end ErdosProblems1066
