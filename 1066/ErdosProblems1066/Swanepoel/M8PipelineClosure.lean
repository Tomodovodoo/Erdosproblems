import ErdosProblems1066.Swanepoel.BrokenLatticeMinimalFailure
import ErdosProblems1066.Swanepoel.LateTriplesInterface
import ErdosProblems1066.Swanepoel.Lemma10WindowGeometry
import ErdosProblems1066.Swanepoel.M8ConstructionInterface

set_option autoImplicit false

/-!
# M8 pipeline closure

This file is the strongest checked closure available from the construction
fields currently present in the tree.  `Lemma10WindowGeometry` supplies the
route from explicit Figure 8/Figure 9 window geometry to E22/E23;
`LateTriplesInterface` supplies the route from no-early triples to late
triples; and `BrokenLatticeMinimalFailure` supplies the final contradiction
once the `M8ConstructionData` package is assembled.

The construction of the honest local predicates, the turn bounds, the
window-geometry or E22/E23 witnesses, and the no-early/late-triple facts
remains explicit data.  This file only checks the assembly and contradiction
routes.
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

/-! ## Direct E22/E23 plus no-early route -/

/-- Direct analytic/no-early construction data for one fixed minimal cleared
failure.

This is the smallest interface in this file for the final broken-lattice
contradiction: callers provide honest local predicates, turn bounds, the named
E22/E23 turn-window hypotheses, and the no-early-triple fact.  The late-triple
field is derived here by `LateTriplesInterface`.
-/
structure M8E22E23NoEarlyConstructionFields {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  predicates : M8HonestLocalPredicates (unitDistanceLocalGraph C)
  turn : Nat -> Real
  turnBounds : M8TurnBounds turn
  figure8_E22 : HonestFigure8SeparatedWindowLowerE22 predicates turn
  figure9_E23 : HonestFigure9AdjacentWindowLowerE23 predicates turn
  noEarlyTripleEquality :
    LateTriplesInterface.M8NoEarlyTripleEquality predicates.data

namespace M8E22E23NoEarlyConstructionFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The no-early field supplies the honest late-triples predicate. -/
theorem lateTriples
    (D : M8E22E23NoEarlyConstructionFields C hmin) :
    D.predicates.LateTriples :=
  LateTriplesInterface.M8HonestLocalPredicates.lateTriples_of_noEarlyTripleEquality
    D.predicates D.noEarlyTripleEquality

/-- The no-early field packaged in the late-triples field used by the
separated closure. -/
def lateTriplesField
    (D : M8E22E23NoEarlyConstructionFields C hmin) :
    M8LateTriplesField D.predicates where
  lateTriples := D.lateTriples

/-- Assemble direct E22/E23 plus no-early data into the existing
broken-lattice minimal-failure construction package. -/
def toConstructionData
    (D : M8E22E23NoEarlyConstructionFields C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin where
  predicates := D.predicates
  turn := D.turn
  turn_nonnegative := D.turnBounds.nonnegative
  total_turn_lt_pi_div_three := D.turnBounds.total_lt_pi_div_three
  figure8_E22 := D.figure8_E22
  figure9_E23 := D.figure9_E23
  lateTriples := D.lateTriples

/-- A fixed minimal cleared failure with direct E22/E23 and no-early fields is
contradictory. -/
theorem contradiction
    (D : M8E22E23NoEarlyConstructionFields C hmin) :
    False :=
  D.toConstructionData.contradiction

end M8E22E23NoEarlyConstructionFields

/-! ## Window geometry plus no-early route -/

/-- Window-geometry/no-early construction data for one fixed minimal cleared
failure.

This variant keeps the Figure 8/Figure 9 geometric witnesses explicit and
derives both E22/E23 and late triples before entering the final contradiction.
-/
structure M8WindowNoEarlyConstructionFields {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  predicates : M8HonestLocalPredicates (unitDistanceLocalGraph C)
  turn : Nat -> Real
  turnBounds : M8TurnBounds turn
  windowGeometry : M8WindowGeometry predicates turn
  noEarlyTripleEquality :
    LateTriplesInterface.M8NoEarlyTripleEquality predicates.data

namespace M8WindowNoEarlyConstructionFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The no-early field supplies the late-triples field required by
`M8SeparatedConstructionFields`. -/
def lateTriplesField
    (D : M8WindowNoEarlyConstructionFields C hmin) :
    M8LateTriplesField D.predicates where
  lateTriples :=
    LateTriplesInterface.M8HonestLocalPredicates.lateTriples_of_noEarlyTripleEquality
      D.predicates D.noEarlyTripleEquality

/-- Forget window geometry plus no-early fields to the direct E22/E23
no-early interface. -/
def toE22E23NoEarlyConstructionFields
    (D : M8WindowNoEarlyConstructionFields C hmin) :
    M8E22E23NoEarlyConstructionFields C hmin where
  predicates := D.predicates
  turn := D.turn
  turnBounds := D.turnBounds
  figure8_E22 := D.windowGeometry.figure8_E22
  figure9_E23 := D.windowGeometry.figure9_E23
  noEarlyTripleEquality := D.noEarlyTripleEquality

/-- Forget window geometry plus no-early fields to the separated construction
fields used by the existing closure. -/
def toSeparatedConstructionFields
    (D : M8WindowNoEarlyConstructionFields C hmin) :
    M8SeparatedConstructionFields C hmin where
  predicates := D.predicates
  turn := D.turn
  turnBounds := D.turnBounds
  windowGeometry := D.windowGeometry
  lateTriples := D.lateTriplesField

/-- A fixed minimal cleared failure with window geometry and no-early fields
is contradictory. -/
theorem contradiction
    (D : M8WindowNoEarlyConstructionFields C hmin) :
    False :=
  D.toE22E23NoEarlyConstructionFields.contradiction

end M8WindowNoEarlyConstructionFields

/-! ## Clean construction-interface route -/

/-- Repackage the clean construction-interface data as the separated fields
used by this closure. -/
def separatedConstructionFields_of_constructionInterfaceData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConstructionInterface.M8ConstructionData C hmin) :
    M8SeparatedConstructionFields C hmin where
  predicates := D.localLabels.predicates
  turn := D.turnBounds.turn
  turnBounds := {
    nonnegative := D.turnBounds.turn_nonnegative
    total_lt_pi_div_three := D.turnBounds.total_turn_lt_pi_div_three
  }
  windowGeometry := {
    figure8_separated := D.windowGeometry.figure8
    figure9_adjacent_left := D.windowGeometry.figure9_left
  }
  lateTriples := {
    lateTriples := D.lateTriples.toHonestLateTriples
  }

/-- Clean construction-interface data contradicts its indexed minimal cleared
failure. -/
theorem contradiction_of_constructionInterfaceData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConstructionInterface.M8ConstructionData C hmin) :
    False :=
  (separatedConstructionFields_of_constructionInterfaceData D).contradiction

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

/-! ## Alternative uniform eliminators -/

/-- A uniform eliminator that supplies direct E22/E23 plus no-early fields for
every minimal cleared failure. -/
def MinimalFailureM8E22E23NoEarlyConstructionEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (M8E22E23NoEarlyConstructionFields C hmin)

/-- A uniform E22/E23 plus no-early eliminator supplies the existing
`BrokenLatticeMinimalFailure` construction eliminator. -/
theorem m8ConstructionEliminator_of_E22E23NoEarlyConstructionEliminator
    (hbuild : MinimalFailureM8E22E23NoEarlyConstructionEliminator) :
    MinimalFailureM8ConstructionEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D =>
      exact Nonempty.intro D.toConstructionData

/-- Direct E22/E23 plus no-early fields rule out every minimal cleared
failure. -/
theorem no_minimalClearedFailure_of_E22E23NoEarlyConstructionEliminator
    (hbuild : MinimalFailureM8E22E23NoEarlyConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  exact no_minimalClearedFailure_of_m8ConstructionEliminator
    (m8ConstructionEliminator_of_E22E23NoEarlyConstructionEliminator hbuild)

/-- A uniform eliminator that supplies window geometry plus no-early fields
for every minimal cleared failure. -/
def MinimalFailureM8WindowNoEarlyConstructionEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (M8WindowNoEarlyConstructionFields C hmin)

/-- Window geometry plus no-early fields can be viewed as direct E22/E23 plus
no-early fields. -/
theorem E22E23NoEarlyConstructionEliminator_of_windowNoEarlyConstructionEliminator
    (hbuild : MinimalFailureM8WindowNoEarlyConstructionEliminator) :
    MinimalFailureM8E22E23NoEarlyConstructionEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D =>
      exact Nonempty.intro D.toE22E23NoEarlyConstructionFields

/-- Window geometry plus no-early fields can also be viewed as the separated
construction fields used by the original closure. -/
theorem separatedConstructionEliminator_of_windowNoEarlyConstructionEliminator
    (hbuild : MinimalFailureM8WindowNoEarlyConstructionEliminator) :
    MinimalFailureM8SeparatedConstructionEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D =>
      exact Nonempty.intro D.toSeparatedConstructionFields

/-- Window geometry plus no-early fields rule out every minimal cleared
failure. -/
theorem no_minimalClearedFailure_of_windowNoEarlyConstructionEliminator
    (hbuild : MinimalFailureM8WindowNoEarlyConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  exact no_minimalClearedFailure_of_separatedConstructionEliminator
    (separatedConstructionEliminator_of_windowNoEarlyConstructionEliminator hbuild)

/-- A uniform eliminator that supplies the clean construction-interface data
for every minimal cleared failure. -/
def MinimalFailureM8ConstructionInterfaceEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (M8ConstructionInterface.M8ConstructionData C hmin)

/-- A clean construction-interface eliminator supplies the separated-field
eliminator. -/
theorem separatedConstructionEliminator_of_constructionInterfaceEliminator
    (hbuild : MinimalFailureM8ConstructionInterfaceEliminator) :
    MinimalFailureM8SeparatedConstructionEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D =>
      exact
        Nonempty.intro
          (separatedConstructionFields_of_constructionInterfaceData D)

/-- Clean construction-interface data rules out every minimal cleared
failure. -/
theorem no_minimalClearedFailure_of_constructionInterfaceEliminator
    (hbuild : MinimalFailureM8ConstructionInterfaceEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  exact no_minimalClearedFailure_of_separatedConstructionEliminator
    (separatedConstructionEliminator_of_constructionInterfaceEliminator hbuild)

end

end M8PipelineClosure
end Swanepoel
end ErdosProblems1066
