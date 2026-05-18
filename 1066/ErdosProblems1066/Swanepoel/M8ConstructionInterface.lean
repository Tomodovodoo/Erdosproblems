import ErdosProblems1066.Swanepoel.BrokenLatticeMinimalFailure
import ErdosProblems1066.Swanepoel.BrokenLatticePipeline
import ErdosProblems1066.Swanepoel.Lemma10WindowGeometry

/-!
# Clean `m = 8` construction interface

This file is only a repackaging layer.  It separates the still-supplied
minimal-failure construction data into local labels, turn bounds, late triples,
and window geometry, then converts that package to
`BrokenLatticeMinimalFailure.M8ConstructionData`.

No minimal-failure contradiction or final closure theorem is stated here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8ConstructionInterface

open BrokenLatticePipeline
open GraphBridge
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open MinimalGraphFacts

noncomputable section

/-! ## Separated construction fields -/

/-- The honest local label package attached to the unit-distance local graph.

The `M8HonestLocalPredicates` package is the label carrier: it stores the
`p`, `q`, `r`, and `s` labels together with the proofs that the named local
predicates agree with the actual label equalities. -/
structure M8LocalLabels {n : Nat} (C : _root_.UDConfig n) where
  predicates : M8HonestLocalPredicates (unitDistanceLocalGraph C)

namespace M8LocalLabels

/-- The underlying broken-lattice labels. -/
abbrev labels {n : Nat} {C : _root_.UDConfig n}
    (L : M8LocalLabels C) : BrokenLatticeLabels (Fin n) 8 :=
  L.predicates.data.labels

end M8LocalLabels

/-- The turn function together with the global bounds used by Lemma 10. -/
structure M8TurnBounds where
  turn : Nat -> Real
  turn_nonnegative : forall k : Nat, 0 <= turn k
  total_turn_lt_pi_div_three : totalTurn turn < Real.pi / 3

/-- Lemma 9's late-triples content, stated directly on the local labels. -/
structure M8LateTriples {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8LocalLabels C) : Prop where
  labelLateTriples : M8LabelLateTriples localLabels.labels

namespace M8LateTriples

/-- Convert label-level late triples to the predicate-level late-triples
field expected by the existing broken-lattice interface. -/
def toHonestLateTriples {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8LateTriples localLabels) :
    localLabels.predicates.LateTriples :=
  BrokenLatticePipeline.M8HonestLocalPredicates.lateTriples_of_labelLateTriples
    localLabels.predicates H.labelLateTriples

end M8LateTriples

/-- The window-level geometric witnesses that imply the E22 and E23 turn
lower-bound hypotheses. -/
structure M8WindowGeometry {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) : Prop where
  figure8 : HonestFigure8SeparatedWindowGeometry
    localLabels.predicates turnBounds.turn
  figure9_left : HonestFigure9AdjacentLeftWindowGeometry
    localLabels.predicates turnBounds.turn

namespace M8WindowGeometry

/-- Figure 8 window geometry gives the E22 separated-window lower bound. -/
def figure8_E22 {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (W : M8WindowGeometry localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  honestFigure8SeparatedWindowLowerE22_of_windowGeometry W.figure8

/-- Figure 9 left-window geometry gives the E23 adjacent-window lower bound. -/
def figure9_E23 {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (W : M8WindowGeometry localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  honestFigure9AdjacentWindowLowerE23_of_leftWindowGeometry W.figure9_left

end M8WindowGeometry

/-! ## Clean package and conversion -/

/-- The cleaned-up construction package for one fixed minimal cleared failure.

Its fields are grouped by provenance: local labels, turn bounds, label-level
late triples, and window geometry. -/
structure M8ConstructionData {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localLabels : M8LocalLabels C
  turnBounds : M8TurnBounds
  lateTriples : M8LateTriples localLabels
  windowGeometry : M8WindowGeometry localLabels turnBounds

namespace M8ConstructionData

/-- Forget the cleaner grouping and produce the existing minimal-failure
construction data package. -/
def toBrokenLatticeMinimalFailure {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConstructionData C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin where
  predicates := D.localLabels.predicates
  turn := D.turnBounds.turn
  turn_nonnegative := D.turnBounds.turn_nonnegative
  total_turn_lt_pi_div_three := D.turnBounds.total_turn_lt_pi_div_three
  figure8_E22 := D.windowGeometry.figure8_E22
  figure9_E23 := D.windowGeometry.figure9_E23
  lateTriples := D.lateTriples.toHonestLateTriples

end M8ConstructionData

end

end M8ConstructionInterface
end Swanepoel
end ErdosProblems1066
