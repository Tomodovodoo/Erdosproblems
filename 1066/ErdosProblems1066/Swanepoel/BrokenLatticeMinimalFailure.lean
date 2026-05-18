import ErdosProblems1066.Swanepoel.BrokenLatticeInterface

/-!
# Broken-lattice closure for minimal cleared failures

This file is a conditional closure layer above `MinimalGraphFacts`.  It records
the construction data still needed to turn a minimal cleared failure into the
existing `BrokenLatticeInterface.M8MinimalFailureBrokenLatticeData`, then sends
that package through the already checked broken-lattice contradiction.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticeMinimalFailure

open BrokenLatticeInterface
open GraphBridge
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open MinimalGraphFacts

noncomputable section

/-! ## Missing construction data -/

/-- The honest data still needed for one fixed minimal cleared failure.

This is exactly the data needed to build
`BrokenLatticeInterface.M8MinimalFailureBrokenLatticeData`, except for the
minimal-failure proof itself, which is already an index of the structure. -/
structure M8ConstructionData {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  predicates : M8HonestLocalPredicates (unitDistanceLocalGraph C)
  turn : Nat -> Real
  turn_nonnegative : forall k : Nat, 0 <= turn k
  total_turn_lt_pi_div_three : totalTurn turn < Real.pi / 3
  figure8_E22 : HonestFigure8SeparatedWindowLowerE22 predicates turn
  figure9_E23 : HonestFigure9AdjacentWindowLowerE23 predicates turn
  lateTriples : predicates.LateTriples

namespace M8ConstructionData

/-- Add the indexed minimality proof to obtain the existing interface package. -/
def toInterfaceData {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConstructionData C hmin) :
    M8MinimalFailureBrokenLatticeData C where
  minimalFailure := hmin
  predicates := D.predicates
  turn := D.turn
  turn_nonnegative := D.turn_nonnegative
  total_turn_lt_pi_div_three := D.total_turn_lt_pi_div_three
  figure8_E22 := D.figure8_E22
  figure9_E23 := D.figure9_E23
  lateTriples := D.lateTriples

/-- The construction data for a minimal cleared failure is contradictory. -/
theorem contradiction {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConstructionData C hmin) :
    False := by
  exact D.toInterfaceData.contradiction

end M8ConstructionData

/-! ## Closure from supplied construction data -/

/-- A conditional eliminator saying every minimal cleared failure supplies the
honest `m = 8` broken-lattice construction data. -/
def MinimalFailureM8ConstructionEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (M8ConstructionData C hmin)

/-- A construction-data eliminator gives the existing interface package for
any fixed minimal cleared failure. -/
def interfaceData_of_m8ConstructionEliminator
    (hbuild : MinimalFailureM8ConstructionEliminator)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) :
    M8MinimalFailureBrokenLatticeData C :=
  (Classical.choice (hbuild C hmin)).toInterfaceData

/-- A construction-data eliminator contradicts any fixed minimal cleared
failure. -/
theorem contradiction_of_m8ConstructionEliminator
    (hbuild : MinimalFailureM8ConstructionEliminator)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) :
    False := by
  exact (interfaceData_of_m8ConstructionEliminator hbuild hmin).contradiction

/-- If every minimal cleared failure supplies the honest broken-lattice
construction data, then there are no minimal cleared failures. -/
theorem no_minimalClearedFailure_of_m8ConstructionEliminator
    (hbuild : MinimalFailureM8ConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  intro n C hmin
  exact contradiction_of_m8ConstructionEliminator hbuild hmin

end

end BrokenLatticeMinimalFailure
end Swanepoel
end ErdosProblems1066
