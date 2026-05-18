import ErdosProblems1066.Swanepoel.GraphBridge
import ErdosProblems1066.Swanepoel.Lemma10AnalyticBridge
import ErdosProblems1066.Swanepoel.MinimalGraphFacts

/-!
# Swanepoel broken-lattice minimal-failure interface

This module is a thin conditional interface around the existing Lemma 10
analytic bridge.  It does not prove the geometric extraction of a broken
lattice, the E22/E23 analytic estimates, or the late-triple fact.  Instead it
records those hard predicates explicitly for a minimal cleared failure and
routes them to `Lemma10AnalyticBridge.honestContradiction_of_E22_E23`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticeInterface

open GraphBridge
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open MinimalGraphFacts

noncomputable section

/-! ## Explicit minimal-failure package -/

/-- The full conditional `m = 8` broken-lattice package attached to a minimal
cleared failure.

The fields are deliberately assumptions.  In particular, the structure does
not manufacture the honest local predicates, the turn function, the E22/E23
window bounds, or the Lemma 9 late-triple predicate from minimality. -/
structure M8MinimalFailureBrokenLatticeData {n : Nat}
    (C : _root_.UDConfig n) where
  minimalFailure : IsMinimalClearedFailure C
  predicates : M8HonestLocalPredicates (unitDistanceLocalGraph C)
  turn : Nat -> Real
  turn_nonnegative : forall k : Nat, 0 <= turn k
  total_turn_lt_pi_div_three : totalTurn turn < Real.pi / 3
  figure8_E22 : HonestFigure8SeparatedWindowLowerE22 predicates turn
  figure9_E23 : HonestFigure9AdjacentWindowLowerE23 predicates turn
  lateTriples : predicates.LateTriples

namespace M8MinimalFailureBrokenLatticeData

/-- The packaged minimal-failure broken-lattice data is contradictory by the
existing honest E22/E23 analytic bridge. -/
theorem contradiction {n : Nat} {C : _root_.UDConfig n}
    (H : M8MinimalFailureBrokenLatticeData C) :
    False := by
  exact honestContradiction_of_E22_E23 H.predicates H.turn
    H.turn_nonnegative H.total_turn_lt_pi_div_three
    H.figure8_E22 H.figure9_E23 H.lateTriples

end M8MinimalFailureBrokenLatticeData

/-! ## Direct argument form -/

/-- Direct interface theorem with every hard predicate exposed as an argument.

The minimal-failure hypothesis identifies the intended source of the local
data; the contradiction itself is exactly the existing
`Lemma10AnalyticBridge.honestContradiction_of_E22_E23` route. -/
theorem contradiction_of_minimalFailure_brokenLattice
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (P : M8HonestLocalPredicates (unitDistanceLocalGraph C))
    (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hE22 : HonestFigure8SeparatedWindowLowerE22 P turn)
    (hE23 : HonestFigure9AdjacentWindowLowerE23 P turn)
    (hlate : P.LateTriples) :
    False := by
  let H : M8MinimalFailureBrokenLatticeData C :=
    { minimalFailure := hmin
      predicates := P
      turn := turn
      turn_nonnegative := hnonneg
      total_turn_lt_pi_div_three := htotal
      figure8_E22 := hE22
      figure9_E23 := hE23
      lateTriples := hlate }
  exact H.contradiction

/-- Negated form of the packaged interface. -/
theorem not_minimalFailure_brokenLatticeData
    {n : Nat} {C : _root_.UDConfig n} :
    M8MinimalFailureBrokenLatticeData C -> False := by
  intro H
  exact H.contradiction

end

end BrokenLatticeInterface
end Swanepoel
end ErdosProblems1066
