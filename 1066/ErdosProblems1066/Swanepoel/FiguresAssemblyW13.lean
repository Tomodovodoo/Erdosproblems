import ErdosProblems1066.Swanepoel.Figure8ContainmentW12
import ErdosProblems1066.Swanepoel.Figure9ContainmentW12
import ErdosProblems1066.Swanepoel.E22E23BridgeW12
import ErdosProblems1066.Swanepoel.Lemma10AnalyticBridge

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W13 assembly of Figure 8 and Figure 9 containment witnesses

This file is the narrow witness-level adapter between the Figure 8/Figure 9
W12 extraction layers and the E22/E23 pair consumed by the honest Lemma 10
contradiction.

No new geometry is proved here.  The Figure 8 worker supplies selected
separated-window data, the Figure 9 worker supplies selected adjacent-window
data, and this module packages their already-checked projections into the
named analytic bridge hypotheses.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FiguresAssemblyW13

open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open LocalConfigurations
open M8ConstructionInterface
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

/-! ## Generic Figure witness assembly -/

/-- The W13 combined witness package: Figure 8 supplies the separated-window
data used for E22, and Figure 9 supplies the adjacent-window data used for
E23. -/
structure FigureContainmentWitnesses
    (good : Nat -> Prop) (turn : Nat -> Real) where
  figure8 :
    Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn
  figure9_left :
    Figure9ContainmentW12.AdjacentWindowWitnesses good turn

namespace FigureContainmentWitnesses

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- The Figure 8 witness component projected to the named E22 hypothesis. -/
theorem E22
    (H : FigureContainmentWitnesses good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  Figure8ContainmentW12.E22_of_dataWitnesses H.figure8

/-- The Figure 9 witness component projected to the named E23 hypothesis. -/
theorem E23
    (H : FigureContainmentWitnesses good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  Figure9ContainmentW12.E23_of_witnesses H.figure9_left

/-- The paired E22/E23 bridge output assembled from the Figure witnesses. -/
theorem E22_E23
    (H : FigureContainmentWitnesses good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  And.intro H.E22 H.E23

/-- The finite Lemma 10 cardinal consequence with Figure witnesses in place
of raw E22/E23 assumptions. -/
theorem card_le_one_failures
    (H : FigureContainmentWitnesses good turn)
    [DecidablePred good]
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3) :
    ((Finset.Icc 1 10).filter fun i => Not (good i)).card <= 1 :=
  card_le_one_failures_of_E22_E23 good turn hnonneg htotal
    H.E22 H.E23

end FigureContainmentWitnesses

/-- Convenience constructor for separately supplied W12 Figure witnesses. -/
def figureContainmentWitnesses_of_components
    {good : Nat -> Prop} {turn : Nat -> Real}
    (figure8 :
      Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn)
    (figure9_left :
      Figure9ContainmentW12.AdjacentWindowWitnesses good turn) :
    FigureContainmentWitnesses good turn where
  figure8 := figure8
  figure9_left := figure9_left

/-- Direct paired E22/E23 output from separately supplied W12 Figure
witnesses. -/
theorem E22_E23_of_components
    {good : Nat -> Prop} {turn : Nat -> Real}
    (figure8 :
      Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn)
    (figure9_left :
      Figure9ContainmentW12.AdjacentWindowWitnesses good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (figureContainmentWitnesses_of_components figure8 figure9_left).E22_E23

/-! ## Relation to the W12 containment bridge -/

/-- Convert the W12 bridge containment outputs into selected W13 witness
components. -/
def witnesses_of_containmentOutputs
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : E22E23BridgeW12.ContainmentOutputs good turn) :
    FigureContainmentWitnesses good turn where
  figure8 :=
    Figure8ContainmentW12.dataWitnesses_of_containmentInterface H.figure8
  figure9_left :=
    Figure9ContainmentW12.witnesses_of_containmentInterface H.figure9_left

/-- The selected-witness assembly agrees with the W12 bridge output type. -/
theorem E22_E23_of_containmentOutputs
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : E22E23BridgeW12.ContainmentOutputs good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (witnesses_of_containmentOutputs H).E22_E23

/-! ## Honest M8 specialization -/

/-- W13 Figure witness assembly specialized to an honest local `m = 8`
predicate package. -/
abbrev HonestFigureContainmentWitnesses
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Type :=
  FigureContainmentWitnesses (M8BrokenLatticeGood P.data) turn

namespace HonestFigureContainmentWitnesses

variable {V : Type u} {G : LocalGraph V}
variable {P : M8HonestLocalPredicates G} {turn : Nat -> Real}

/-- Honest Figure witnesses projected to the paired E22/E23 bridge output. -/
theorem E22_E23
    (H : HonestFigureContainmentWitnesses P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn /\
      HonestFigure9AdjacentWindowLowerE23 P turn :=
  FigureContainmentWitnesses.E22_E23 H

/-- Honest Figure witnesses give the Lemma 10 contradiction once the turn
budget and late-triples input are supplied. -/
theorem contradiction
    (H : HonestFigureContainmentWitnesses P turn)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hlate : P.LateTriples) :
    False :=
  let hpair := H.E22_E23
  honestContradiction_of_E22_E23 P turn hnonneg htotal
    hpair.1 hpair.2 hlate

end HonestFigureContainmentWitnesses

/-- Direct honest paired E22/E23 output from separately supplied W12 Figure
witnesses. -/
theorem honestE22_E23_of_components
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (figure8 :
      Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
        P turn)
    (figure9_left :
      Figure9ContainmentW12.HonestAdjacentWindowWitnesses P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn /\
      HonestFigure9AdjacentWindowLowerE23 P turn :=
  HonestFigureContainmentWitnesses.E22_E23
    (figureContainmentWitnesses_of_components figure8 figure9_left)

/-! ## Construction-level containment fields -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- W13 selected witnesses extracted from an M8 window-containment package. -/
def witnesses_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigureContainmentWitnesses
      localLabels.predicates turnBounds.turn where
  figure8 :=
    Figure8ContainmentW12.dataWitnesses_of_containmentInterface W.figure8
  figure9_left :=
    Figure9ContainmentW12.honestWitnesses_of_m8WindowContainment W

/-- W13 selected witnesses extracted from local W12 containment fields. -/
def witnesses_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigureContainmentWitnesses
      localLabels.predicates turnBounds.turn :=
  witnesses_of_m8WindowContainment H.toM8WindowContainment

/-- M8 window-containment data gives the honest E22/E23 bridge output through
the selected W13 witnesses. -/
theorem honestE22_E23_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (witnesses_of_m8WindowContainment W).E22_E23

/-- Local W12 containment fields give the honest E22/E23 bridge output
through the selected W13 witnesses. -/
theorem honestE22_E23_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (witnesses_of_localWindowContainmentFields H).E22_E23

/-- M8 window-containment data reaches the honest contradiction through the
selected W13 witness assembly. -/
theorem honestContradiction_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds)
    (hlate : localLabels.predicates.LateTriples) :
    False :=
  HonestFigureContainmentWitnesses.contradiction
    (witnesses_of_m8WindowContainment W)
    turnBounds.turn_nonnegative
    turnBounds.total_turn_lt_pi_div_three
    hlate

/-- Local W12 containment fields reach the honest contradiction through the
selected W13 witness assembly. -/
theorem honestContradiction_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    (hlate : localLabels.predicates.LateTriples) :
    False :=
  honestContradiction_of_m8WindowContainment
    H.toM8WindowContainment hlate

end FiguresAssemblyW13
end Swanepoel
end ErdosProblems1066

end
