import ErdosProblems1066.Swanepoel.Figure8EuclideanFactsConcrete

set_option autoImplicit false

/-!
# Figure 8 containment angle budget

This file is a small projection layer over the concrete Figure 8 Euclidean
facts.  The metric part proves that the central Figure 8 angle is at least
`pi / 3`; the extra budget input is exactly that this central angle is
contained in the separated turn window.  Together they give the separated
turn lower bounds used as E22.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure8ContainmentAngleBudget

open AngleContainmentInterface
open AngleBridgeFacts
open AngleGeometry
open Figure8ContainmentConcrete
open Figure8EuclideanFactsConcrete
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10EuclideanBridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open M8ConstructionInterface
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Minimal angle-budget arithmetic -/

/-- If a central angle is at least `pi / 3` and is contained in the separated
turn window, then that separated turn window has the E22 lower bound. -/
lemma pi_div_three_le_separatedTurn_of_central_angle_contained
    {turn : Nat -> Real} {i j : Nat} {p qi qj : Point}
    (hangle : Real.pi / 3 <= angleAt qi p qj)
    (hcontained : angleAt qi p qj <= separatedTurn turn i j) :
    Real.pi / 3 <= separatedTurn turn i j :=
  le_trans hangle hcontained

/-- Figure 8 distance data supplies the central-angle lower bound, so central
angle containment is enough to force the separated turn lower bound. -/
lemma separatedTurn_lower_of_distanceData_and_central_containment
    {turn : Nat -> Real} {i j : Nat} {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r)
    (hcontained : angleAt qi p qj <= separatedTurn turn i j) :
    Real.pi / 3 <= separatedTurn turn i j :=
  pi_div_three_le_separatedTurn_of_central_angle_contained
    (Figure8EuclideanFactsConcrete.central_angle_lower D)
    hcontained

/-! ## Pointwise central-angle budget -/

/-- A single separated pair with Figure 8 distance data and the only remaining
turn-budget input: containment of the central angle in the separated turn
window. -/
structure Figure8CentralAngleBudget
    (turn : Nat -> Real) (i j : Nat) where
  p : Point
  qi : Point
  qj : Point
  s : Point
  r : Point
  distanceData : Figure8DistanceData p qi qj s r
  central_angle_le_separatedTurn :
    angleAt qi p qj <= separatedTurn turn i j

namespace Figure8CentralAngleBudget

variable {turn : Nat -> Real} {i j : Nat}

/-- The metric part of a pointwise Figure 8 budget gives the central angle
lower bound. -/
theorem central_angle_lower (B : Figure8CentralAngleBudget turn i j) :
    Real.pi / 3 <= angleAt B.qi B.p B.qj :=
  Figure8EuclideanFactsConcrete.central_angle_lower B.distanceData

/-- A pointwise Figure 8 central-angle budget gives the separated turn lower
bound. -/
theorem separatedTurn_lower (B : Figure8CentralAngleBudget turn i j) :
    Real.pi / 3 <= separatedTurn turn i j :=
  separatedTurn_lower_of_distanceData_and_central_containment
    (p := B.p) (qi := B.qi) (qj := B.qj) (s := B.s) (r := B.r)
    B.distanceData B.central_angle_le_separatedTurn

/-- Forget the pointwise angle budget to the existing contained-data record. -/
def toContainedData (B : Figure8CentralAngleBudget turn i j) :
    Figure8SeparatedContainedData turn i j where
  p := B.p
  qi := B.qi
  qj := B.qj
  s := B.s
  r := B.r
  distanceData := B.distanceData
  central_angle_le_separatedTurn := B.central_angle_le_separatedTurn

end Figure8CentralAngleBudget

/-! ## Uniform separated-window budget -/

/-- Uniform pointwise Figure 8 central-angle budgets for every separated pair
of failed comparisons. -/
structure Figure8SeparatedAngleBudget
    (good : Nat -> Prop) (turn : Nat -> Real) where
  budget :
    forall {i j : Nat},
      1 <= i -> i + 1 < j -> j <= 10 ->
      Not (good i) -> Not (good j) ->
        Figure8CentralAngleBudget turn i j

namespace Figure8SeparatedAngleBudget

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- Select the pointwise budget at one separated bad pair. -/
def data (H : Figure8SeparatedAngleBudget good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Figure8CentralAngleBudget turn i j :=
  H.budget hi hsep hj hbad_i hbad_j

/-- Forget the uniform angle-budget package to the existing Figure 8
contained-window facade. -/
def toWindowContainment
    (H : Figure8SeparatedAngleBudget good turn) :
    Figure8SeparatedWindowContainment good turn where
  containedData := by
    intro i j hi hsep hj hbad_i hbad_j
    exact (H.data hi hsep hj hbad_i hbad_j).toContainedData

/-- Convert an existing selected-containment facade into the pointwise
angle-budget package. -/
def ofWindowContainment
    (H : Figure8SeparatedWindowContainment good turn) :
    Figure8SeparatedAngleBudget good turn where
  budget := by
    intro i j hi hsep hj hbad_i hbad_j
    let D := H.data hi hsep hj hbad_i hbad_j
    exact
      { p := D.p
        qi := D.qi
        qj := D.qj
        s := D.s
        r := D.r
        distanceData := D.distanceData
        central_angle_le_separatedTurn :=
          D.central_angle_le_separatedTurn }

/-- Convert the concrete containment interface into the pointwise
angle-budget package. -/
def ofContainmentInterface
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedAngleBudget good turn :=
  ofWindowContainment
    (Figure8SeparatedWindowContainment.ofContainmentInterface H)

/-- The uniform Figure 8 central-angle budgets give E22. -/
theorem E22 (H : Figure8SeparatedAngleBudget good turn) :
    Figure8SeparatedWindowLowerE22 good turn := by
  intro i j hi hsep hj hbad_i hbad_j
  exact (H.data hi hsep hj hbad_i hbad_j).separatedTurn_lower

/-- Pointwise form of the E22 projection. -/
theorem E22_apply
    (H : Figure8SeparatedAngleBudget good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Real.pi / 3 <= separatedTurn turn i j :=
  H.E22 hi hsep hj hbad_i hbad_j

/-- E22 as the raw separated-failures turn-force interface. -/
theorem separatedFailuresForceTurn
    (H : Figure8SeparatedAngleBudget good turn) :
    SeparatedFailuresForceTurn good turn :=
  separatedFailuresForceTurn_of_E22 H.E22

/-- Existing explicit Euclidean facts from `Figure8EuclideanFactsConcrete`
also give E22 through this budget layer. -/
theorem E22_of_explicitEuclideanFacts
    (H : Figure8ExplicitEuclideanFacts good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  H.E22

/-- Existing explicit Euclidean facts also give the raw separated-failures
turn-force interface. -/
theorem separatedFailuresForceTurn_of_explicitEuclideanFacts
    (H : Figure8ExplicitEuclideanFacts good turn) :
    SeparatedFailuresForceTurn good turn :=
  separatedFailuresForceTurn_of_E22 H.E22

end Figure8SeparatedAngleBudget

/-! ## `m = 8` specializations -/

/-- Uniform Figure 8 angle budgets specialized to the local `m = 8`
predicate package. -/
def M8Figure8SeparatedAngleBudget
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Type :=
  Figure8SeparatedAngleBudget (M8BrokenLatticeGood P) turn

/-- Uniform Figure 8 angle budgets specialized to an honest local `m = 8`
package. -/
def HonestFigure8SeparatedAngleBudget
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Type :=
  M8Figure8SeparatedAngleBudget P.data turn

/-- Local `m = 8` Figure 8 angle budgets give the local E22 hypothesis. -/
theorem m8Figure8SeparatedWindowLowerE22_of_angleBudget
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure8SeparatedAngleBudget P turn) :
    M8Figure8SeparatedWindowLowerE22 P turn :=
  H.E22

/-- Honest Figure 8 angle budgets give the honest E22 hypothesis. -/
theorem honestFigure8SeparatedWindowLowerE22_of_angleBudget
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedAngleBudget P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn :=
  H.E22

/-- Local `m = 8` Figure 8 angle budgets give the raw separated-failures
turn-force interface. -/
theorem m8SeparatedFailuresForceTurn_of_angleBudget
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure8SeparatedAngleBudget P turn) :
    SeparatedFailuresForceTurn (M8BrokenLatticeGood P) turn :=
  H.separatedFailuresForceTurn

/-! ## Strict budget contradiction forms -/

/-- Any legal separated turn window lies strictly below `pi / 3` under the
honest `m = 8` turn budget. -/
theorem separatedTurn_lt_pi_div_three_of_m8TurnBounds
    (T : M8TurnBounds) {i j : Nat} (hi : 1 <= i) (hj : j <= 10) :
    separatedTurn T.turn i j < Real.pi / 3 :=
  lt_of_le_of_lt
    (Lemma10Inequalities.separatedTurn_le_totalTurn hi hj
      T.turn_nonnegative)
    T.total_turn_lt_pi_div_three

/-- A contained Figure 8 central angle contradicts the strict `m = 8` turn
budget for the same separated window. -/
theorem false_of_distanceData_and_central_containment_m8TurnBounds
    (T : M8TurnBounds) {i j : Nat} {p qi qj s r : Point}
    (hi : 1 <= i) (hj : j <= 10)
    (D : Figure8DistanceData p qi qj s r)
    (hcontained : angleAt qi p qj <= separatedTurn T.turn i j) :
    False := by
  have hlower : Real.pi / 3 <= separatedTurn T.turn i j :=
    separatedTurn_lower_of_distanceData_and_central_containment
      (turn := T.turn) (i := i) (j := j) D hcontained
  have hupper : separatedTurn T.turn i j < Real.pi / 3 :=
    separatedTurn_lt_pi_div_three_of_m8TurnBounds T hi hj
  linarith

/-- A pointwise Figure 8 central-angle budget is incompatible with the strict
`m = 8` turn budget on the same legal separated window. -/
theorem false_of_centralAngleBudget_m8TurnBounds
    (T : M8TurnBounds) {i j : Nat}
    (hi : 1 <= i) (hj : j <= 10)
    (B : Figure8CentralAngleBudget T.turn i j) :
    False := by
  have hlower : Real.pi / 3 <= separatedTurn T.turn i j :=
    B.separatedTurn_lower
  have hupper : separatedTurn T.turn i j < Real.pi / 3 :=
    separatedTurn_lt_pi_div_three_of_m8TurnBounds T hi hj
  linarith

/-- Uniform local `m = 8` Figure 8 angle budgets rule out any separated pair
of broken-lattice failures under the strict turn budget. -/
theorem m8_separated_failures_impossible_of_angleBudget
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (T : M8TurnBounds)
    (H : M8Figure8SeparatedAngleBudget P T.turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood P i))
    (hbad_j : Not (M8BrokenLatticeGood P j)) :
    False := by
  have hlower : Real.pi / 3 <= separatedTurn T.turn i j :=
    H.E22 hi hsep hj hbad_i hbad_j
  have hupper : separatedTurn T.turn i j < Real.pi / 3 :=
    separatedTurn_lt_pi_div_three_of_m8TurnBounds T hi hj
  linarith

/-! ## Projections from existing M8 window-containment packages -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- The Figure 8 part of an M8 window-containment package as a uniform
central-angle budget. -/
def honestAngleBudget_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedAngleBudget
      localLabels.predicates turnBounds.turn :=
  Figure8SeparatedAngleBudget.ofWindowContainment
    (Figure8ContainmentConcrete.honestContainment_of_m8WindowContainment W)

/-- Projection to honest E22 through the angle-budget facade. -/
theorem honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  (honestAngleBudget_of_m8WindowContainment W).E22

/-- Projection to the raw separated-failures turn-force interface through the
angle-budget facade. -/
theorem honestSeparatedFailuresForceTurn_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    SeparatedFailuresForceTurn
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  (honestAngleBudget_of_m8WindowContainment W).separatedFailuresForceTurn

/-- Pointwise honest E22 projection from an M8 window-containment package. -/
theorem honestFigure8SeparatedWindowLowerE22_apply_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Real.pi / 3 <= separatedTurn turnBounds.turn i j :=
  honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment W
    hi hsep hj hbad_i hbad_j

/-- The full M8 window-containment package supplies both honest analytic
lower bounds, with the Figure 8 side routed through the angle-budget facade. -/
theorem honestE22_E23_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  And.intro
    (honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment W)
    (M8WindowContainment.figure9_E23 W)

/-- M8 window-containment rules out any separated pair of broken-lattice
failures under the same strict turn budget. -/
theorem honest_separated_failures_impossible_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    False := by
  have hlower : Real.pi / 3 <= separatedTurn turnBounds.turn i j :=
    honestFigure8SeparatedWindowLowerE22_apply_of_m8WindowContainment W
      hi hsep hj hbad_i hbad_j
  have hupper : separatedTurn turnBounds.turn i j < Real.pi / 3 :=
    separatedTurn_lt_pi_div_three_of_m8TurnBounds turnBounds hi hj
  linarith

/-- The M8 window-containment package gives the Lemma 10 at-most-one-failure
conclusion after combining the Figure 8 angle-budget E22 projection with the
existing Figure 9 E23 projection. -/
theorem honestAtMostOneFailure_of_m8WindowContainment
    [DecidablePred
      (M8BrokenLatticeGood localLabels.predicates.data)]
    (W : M8WindowContainment localLabels turnBounds) :
    localLabels.predicates.AtMostOneFailure :=
  m8_atMostOneFailure_of_E22_E23 localLabels.predicates.data
    turnBounds.turn turnBounds.turn_nonnegative
    turnBounds.total_turn_lt_pi_div_three
    (honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment W)
    (M8WindowContainment.figure9_E23 W)

/-- Honest late triples plus M8 window containment close the local finite
contradiction. -/
theorem honestContradiction_of_m8WindowContainment_and_honestLateTriples
    (W : M8WindowContainment localLabels turnBounds)
    (hlate : localLabels.predicates.LateTriples) :
    False :=
  honestContradiction_of_E22_E23 localLabels.predicates turnBounds.turn
    turnBounds.turn_nonnegative turnBounds.total_turn_lt_pi_div_three
    (honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment W)
    (M8WindowContainment.figure9_E23 W) hlate

/-- Label-level late triples plus M8 window containment close the local finite
contradiction through the honest predicate package. -/
theorem honestContradiction_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds)
    (lateTriples : M8LateTriples localLabels) :
    False :=
  honestContradiction_of_m8WindowContainment_and_honestLateTriples W
    lateTriples.toHonestLateTriples

end Figure8ContainmentAngleBudget
end Swanepoel
end ErdosProblems1066

end
