import ErdosProblems1066.Swanepoel.Lemma10Bridge
import ErdosProblems1066.Swanepoel.Lemma10Inequalities

/-!
# Swanepoel Lemma 10 Pipeline

This module composes the abstract turn-inequality reduction with the checked
`m = 8` broken-lattice contradiction.  It still does not prove the Euclidean
turn inequalities; those remain explicit hypotheses.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma10Pipeline

open Lemma10Bridge
open Lemma10Inequalities
open LocalConfigurations

universe u

noncomputable section

/-- Turn hypotheses imply the local finite contradiction for an `m = 8`
broken-lattice predicate package. -/
theorem contradiction_of_turn_hypotheses
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8)
    (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hseparated :
      SeparatedFailuresForceTurn (M8BrokenLatticeGood P) turn)
    (hadjacent :
      AdjacentFailuresForceTurn (M8BrokenLatticeGood P) turn)
    (htriple :
      forall a : M8TripleStartIndex,
        P.tripleEquality a <-> M8BrokenLatticeTriple P a)
    (hlate : M8BrokenLatticeLateTriples P) :
    False := by
  classical
  have hcard : M8AtMostOneBrokenLatticeFailure P := by
    simpa [M8AtMostOneBrokenLatticeFailure, M8BrokenLatticeFailures,
      failureSet, lemma10IndexSet] using
      card_le_one_failures_of_turn_hypotheses
        (M8BrokenLatticeGood P) turn hnonneg htotal hseparated hadjacent
  exact contradiction_of_atMostOneFailure_and_lateTriples
    P htriple hcard hlate

/-- Honest-package form of the Lemma 10 pipeline. -/
theorem honestContradiction_of_turn_hypotheses
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G)
    (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hseparated :
      SeparatedFailuresForceTurn (M8BrokenLatticeGood P.data) turn)
    (hadjacent :
      AdjacentFailuresForceTurn (M8BrokenLatticeGood P.data) turn)
    (hlate : P.LateTriples) :
    False :=
  by
    classical
    exact contradiction_of_turn_hypotheses P.data turn hnonneg htotal
      hseparated hadjacent P.tripleEquality_iff_threeComparisons hlate

end

end Lemma10Pipeline
end Swanepoel
end ErdosProblems1066
