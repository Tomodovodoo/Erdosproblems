import ErdosProblems1066.Swanepoel.BrokenLatticeMinimalFailure
import ErdosProblems1066.Swanepoel.Lemma10WindowGeometry

set_option autoImplicit false

/-!
# M8 pipeline closure

This file is the strongest checked closure available from the separated
construction fields currently present in the tree.  `Lemma10WindowGeometry`
supplies the route from explicit Figure 8/Figure 9 window geometry to E22/E23;
`BrokenLatticeMinimalFailure` supplies the final contradiction once the
`M8ConstructionData` package is assembled.

The construction of the honest local predicates, the turn bounds, the
window-geometry witnesses, and the late-triple fact remains explicit data.
There is no project-local `M8ConstructionInterface`, `TurnBoundsInterface`, or
`LateTriplesInterface` module in this checkout, so this file does not pretend
those fields have been discharged elsewhere.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8PipelineClosure

open BrokenLatticeMinimalFailure
open GraphBridge
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open MinimalGraphFacts

universe u

noncomputable section

/-! ## Separated construction fields -/

/-- The turn-budget fields used by the broken-lattice contradiction. -/
structure M8TurnBounds (turn : Nat -> Real) : Prop where
  nonnegative : forall k : Nat, 0 <= turn k
  total_lt_pi_div_three : totalTurn turn < Real.pi / 3

/-- The Figure 8/Figure 9 window-geometry fields strong enough to derive the
named E22/E23 hypotheses. -/
structure M8WindowGeometry {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Prop where
  figure8_separated : HonestFigure8SeparatedWindowGeometry P turn
  figure9_adjacent_left : HonestFigure9AdjacentLeftWindowGeometry P turn

/-- The late-triples field, kept separate from the window geometry because it
comes from the Lemma 9 side of the pipeline. -/
structure M8LateTriplesField {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) : Prop where
  lateTriples : P.LateTriples

namespace M8WindowGeometry

variable {V : Type u} {G : LocalGraph V}
variable {P : M8HonestLocalPredicates G} {turn : Nat -> Real}

/-- Figure 8 window geometry gives the E22 lower-bound field. -/
theorem figure8_E22 (W : M8WindowGeometry P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn :=
  honestFigure8SeparatedWindowLowerE22_of_windowGeometry W.figure8_separated

/-- Figure 9 left-window geometry gives the E23 lower-bound field. -/
theorem figure9_E23 (W : M8WindowGeometry P turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  honestFigure9AdjacentWindowLowerE23_of_leftWindowGeometry
    W.figure9_adjacent_left

end M8WindowGeometry

/-- The explicit separated construction data for one fixed minimal cleared
failure.  The minimality proof is an index only; the fields below remain the
actual geometric and combinatorial obligations. -/
structure M8SeparatedConstructionFields {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  predicates : M8HonestLocalPredicates (unitDistanceLocalGraph C)
  turn : Nat -> Real
  turnBounds : M8TurnBounds turn
  windowGeometry : M8WindowGeometry predicates turn
  lateTriples : M8LateTriplesField predicates

namespace M8SeparatedConstructionFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The separated window geometry supplies the E22 field required by
`BrokenLatticeMinimalFailure.M8ConstructionData`. -/
theorem figure8_E22 (D : M8SeparatedConstructionFields C hmin) :
    HonestFigure8SeparatedWindowLowerE22 D.predicates D.turn :=
  D.windowGeometry.figure8_E22

/-- The separated window geometry supplies the E23 field required by
`BrokenLatticeMinimalFailure.M8ConstructionData`. -/
theorem figure9_E23 (D : M8SeparatedConstructionFields C hmin) :
    HonestFigure9AdjacentWindowLowerE23 D.predicates D.turn :=
  D.windowGeometry.figure9_E23

/-- Assemble the separated construction fields into the existing
broken-lattice minimal-failure package. -/
def toConstructionData
    (D : M8SeparatedConstructionFields C hmin) :
    M8ConstructionData C hmin where
  predicates := D.predicates
  turn := D.turn
  turn_nonnegative := D.turnBounds.nonnegative
  total_turn_lt_pi_div_three := D.turnBounds.total_lt_pi_div_three
  figure8_E22 := D.figure8_E22
  figure9_E23 := D.figure9_E23
  lateTriples := D.lateTriples.lateTriples

/-- A fixed minimal cleared failure with the separated M8 fields is
contradictory. -/
theorem contradiction
    (D : M8SeparatedConstructionFields C hmin) :
    False :=
  D.toConstructionData.contradiction

end M8SeparatedConstructionFields

/-! ## Uniform eliminator and final closure -/

/-- A uniform eliminator that supplies the separated construction fields for
every minimal cleared failure. -/
def MinimalFailureM8SeparatedConstructionEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (M8SeparatedConstructionFields C hmin)

/-- The separated-field eliminator is strong enough to supply the existing
`BrokenLatticeMinimalFailure` construction eliminator. -/
theorem m8ConstructionEliminator_of_separatedConstructionEliminator
    (hbuild : MinimalFailureM8SeparatedConstructionEliminator) :
    MinimalFailureM8ConstructionEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D =>
      exact ⟨D.toConstructionData⟩

/-- A uniform separated-field eliminator contradicts every fixed minimal
cleared failure. -/
theorem contradiction_of_separatedConstructionEliminator
    (hbuild : MinimalFailureM8SeparatedConstructionEliminator)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) :
    False := by
  exact contradiction_of_m8ConstructionEliminator
    (m8ConstructionEliminator_of_separatedConstructionEliminator hbuild) hmin

/-- Final closure: if every minimal cleared failure supplies the separated M8
construction fields, then there are no minimal cleared failures. -/
theorem no_minimalClearedFailure_of_separatedConstructionEliminator
    (hbuild : MinimalFailureM8SeparatedConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  exact no_minimalClearedFailure_of_m8ConstructionEliminator
    (m8ConstructionEliminator_of_separatedConstructionEliminator hbuild)

end

end M8PipelineClosure
end Swanepoel
end ErdosProblems1066
