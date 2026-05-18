import ErdosProblems1066.Swanepoel.M8WindowContainmentConcrete

set_option autoImplicit false

/-!
# W12 bridge from Figure containment outputs to E22/E23

This module records the final assumption-reducing adapter for Swanepoel's
Lemma 10 E22/E23 route.  The inputs are not raw analytic E22/E23 hypotheses:
they are the checked Figure 8 and Figure 9 containment interfaces produced by
the Figure workers.  From those containment outputs we build the honest E22
and E23 hypotheses consumed by `Lemma10AnalyticBridge`.

No Figure containment fact is proved here.  If the upstream Figure workers are
not yet available, the interfaces below are exactly the remaining inputs to
provide.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace E22E23BridgeW12

open AngleContainmentInterface
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open LocalConfigurations
open M8ConstructionInterface
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

/-! ## Generic containment outputs -/

/-- The exact Figure-worker outputs needed to derive the E22/E23 turn-window
hypotheses for a predicate `good` and turn budget `turn`. -/
structure ContainmentOutputs (good : Nat -> Prop) (turn : Nat -> Real) where
  figure8 : Figure8SeparatedContainmentInterface good turn
  figure9_left : Figure9AdjacentLeftContainmentInterface good turn

namespace ContainmentOutputs

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- Repackage the two Figure-worker outputs as the combined containment
interface already used by the lower bridge layers. -/
def toAngleContainmentBridges
    (H : ContainmentOutputs good turn) :
    AngleContainmentBridges good turn where
  figure8 := H.figure8
  figure9 := H.figure9_left

/-- Build the named E22/E23 hypotheses from Figure 8/Figure 9 containment
outputs. -/
theorem E22_E23
    (H : ContainmentOutputs good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  H.toAngleContainmentBridges.E22_E23

/-- Projection of the Figure 8/E22 lower-bound hypothesis. -/
theorem E22
    (H : ContainmentOutputs good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  H.E22_E23.1

/-- Projection of the Figure 9/E23 lower-bound hypothesis. -/
theorem E23
    (H : ContainmentOutputs good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  H.E22_E23.2

/-- Generic Lemma 10 cardinal conclusion, with raw E22/E23 assumptions
replaced by the Figure containment outputs. -/
theorem card_le_one_failures
    (H : ContainmentOutputs good turn)
    [DecidablePred good]
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3) :
    ((Finset.Icc 1 10).filter fun i => Not (good i)).card <= 1 :=
  card_le_one_failures_of_E22_E23 good turn hnonneg htotal
    H.E22 H.E23

end ContainmentOutputs

/-- Convenience constructor for the generic Figure-containment outputs. -/
def containmentOutputs_of_interfaces
    {good : Nat -> Prop} {turn : Nat -> Real}
    (figure8 : Figure8SeparatedContainmentInterface good turn)
    (figure9_left : Figure9AdjacentLeftContainmentInterface good turn) :
    ContainmentOutputs good turn where
  figure8 := figure8
  figure9_left := figure9_left

/-- Direct paired E22/E23 projection from separately supplied Figure 8 and
Figure 9 containment interfaces. -/
theorem E22_E23_of_containmentInterfaces
    {good : Nat -> Prop} {turn : Nat -> Real}
    (figure8 : Figure8SeparatedContainmentInterface good turn)
    (figure9_left : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (containmentOutputs_of_interfaces figure8 figure9_left).E22_E23

/-! ## Honest M8 specialization -/

/-- Figure containment outputs specialized to an honest local `m = 8` package. -/
abbrev HonestContainmentOutputs
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Type :=
  ContainmentOutputs (M8BrokenLatticeGood P.data) turn

namespace HonestContainmentOutputs

variable {V : Type u} {G : LocalGraph V}
variable {P : M8HonestLocalPredicates G} {turn : Nat -> Real}

/-- Build the honest E22/E23 hypotheses from the honest Figure containment
outputs. -/
theorem E22_E23
    (H : HonestContainmentOutputs P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn /\
      HonestFigure9AdjacentWindowLowerE23 P turn :=
  ContainmentOutputs.E22_E23 H

/-- Honest Figure containment outputs imply the local Lemma 10 contradiction
once the turn bounds and late-triples input are supplied. -/
theorem contradiction
    (H : HonestContainmentOutputs P turn)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hlate : P.LateTriples) :
    False := by
  exact honestContradiction_of_E22_E23 P turn hnonneg htotal
    (ContainmentOutputs.E22_E23 H).1
    (ContainmentOutputs.E22_E23 H).2 hlate

end HonestContainmentOutputs

/-- Direct honest E22/E23 projection from separately supplied Figure 8 and
Figure 9 containment interfaces. -/
theorem honestE22_E23_of_containmentInterfaces
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood P.data) turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood P.data) turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn /\
      HonestFigure9AdjacentWindowLowerE23 P turn :=
  HonestContainmentOutputs.E22_E23
    (P := P)
    (containmentOutputs_of_interfaces figure8 figure9_left)

/-- Direct honest contradiction from Figure containment outputs, avoiding raw
E22/E23 hypotheses at the call site. -/
theorem honestContradiction_of_containmentInterfaces
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood P.data) turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood P.data) turn)
    (hlate : P.LateTriples) :
    False :=
  HonestContainmentOutputs.contradiction
    (P := P)
    (containmentOutputs_of_interfaces figure8 figure9_left)
    hnonneg htotal hlate

/-! ## Construction-level M8 containment packages -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- The existing M8 window-containment package exposes exactly the Figure
containment outputs needed by this bridge. -/
def containmentOutputs_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestContainmentOutputs localLabels.predicates turnBounds.turn where
  figure8 := W.figure8
  figure9_left := W.figure9_left

/-- M8 window-containment data gives the honest E22/E23 hypotheses. -/
theorem honestE22_E23_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (containmentOutputs_of_m8WindowContainment W).E22_E23

/-- M8 window-containment data gives the honest Lemma 10 contradiction with
turn bounds and predicate-level late triples. -/
theorem honestContradiction_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds)
    (hlate : localLabels.predicates.LateTriples) :
    False :=
  HonestContainmentOutputs.contradiction
    (containmentOutputs_of_m8WindowContainment W)
    turnBounds.turn_nonnegative
    turnBounds.total_turn_lt_pi_div_three
    hlate

/-- Local W12 containment fields give the honest E22/E23 hypotheses. -/
theorem honestE22_E23_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (H.toM8WindowContainment).E22_E23

/-- Local W12 containment fields give the honest Lemma 10 contradiction with
turn bounds and predicate-level late triples. -/
theorem honestContradiction_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    (hlate : localLabels.predicates.LateTriples) :
    False :=
  honestContradiction_of_m8WindowContainment
    H.toM8WindowContainment hlate

/-- Local W12 containment fields give the construction-level contradiction
when paired with the label-level late-triples package. -/
theorem contradiction_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    (hlate : M8LateTriples localLabels) :
    False :=
  honestContradiction_of_localWindowContainmentFields
    H hlate.toHonestLateTriples

/-- A construction-data package from containment contradicts the fixed
minimal failure using the direct E22/E23 route. -/
theorem contradiction_of_constructionDataFromContainment
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConstructionDataFromContainment C hmin) :
    False :=
  honestContradiction_of_m8WindowContainment
    D.windowContainment D.lateTriples.toHonestLateTriples

end E22E23BridgeW12
end Swanepoel
end ErdosProblems1066

end
