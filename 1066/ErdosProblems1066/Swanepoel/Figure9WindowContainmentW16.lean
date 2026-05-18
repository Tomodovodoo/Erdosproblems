import ErdosProblems1066.Swanepoel.Lemma89WindowContainmentProofW15
import ErdosProblems1066.Swanepoel.Figure9ContainmentW12
import ErdosProblems1066.Swanepoel.FiguresAssemblyW13
import ErdosProblems1066.Swanepoel.FiguresToRefinedM8W13
import ErdosProblems1066.Swanepoel.E22E23BridgeW12
import ErdosProblems1066.Swanepoel.Lemma8Lemma9AssemblyW13

set_option autoImplicit false
set_option linter.unusedDecidableInType false

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure9WindowContainmentW16

open AngleContainmentInterface
open CutVertexClosure
open Figure9ContainmentW12
open FiguresAssemblyW13
open FiguresToRefinedM8W13
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma89WindowContainmentProofW15
open M8ConstructionInterface
open M8WindowContainmentConcrete
open MinimalGraphFacts

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/--
Pointwise W16 row after the Figure 9 part has been lowered to W12 selected
adjacent-window witnesses.  The Figure 8 side is still the exact interface
carried by the W15 row, while Figure 9 is now the witness shape consumed by
the W13 assembly layer.
-/
structure PointwiseFigure9SelectedWindowContainmentFields
    (B : PointwiseLemma89Base.{u} C hmin) where
  figure8 :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn
  figure9_left :
    Figure9ContainmentW12.HonestAdjacentWindowWitnesses
      B.localLabels.predicates B.turnBounds.turn

namespace PointwiseFigure9SelectedWindowContainmentFields

variable {B : PointwiseLemma89Base.{u} C hmin}
variable (W : PointwiseFigure9SelectedWindowContainmentFields B)

/-- Figure 8 selected data extracted from the retained containment interface. -/
def figure8Witnesses :
    Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
      B.localLabels.predicates B.turnBounds.turn :=
  Figure8ContainmentW12.dataWitnesses_of_containmentInterface W.figure8

/-- Combined W13 Figure witnesses for the localized Lemma 8/Lemma 9 row. -/
def figureWitnesses :
    FiguresAssemblyW13.HonestFigureContainmentWitnesses
      B.localLabels.predicates B.turnBounds.turn where
  figure8 := figure8Witnesses W
  figure9_left := W.figure9_left

/-- The reduced W16 row supplies the same honest E22/E23 pair. -/
theorem E22_E23
    (W : PointwiseFigure9SelectedWindowContainmentFields B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  FiguresAssemblyW13.HonestFigureContainmentWitnesses.E22_E23
    (figureWitnesses W)

/-- The Figure 9 selected witnesses alone provide the E23 side. -/
theorem figure9_E23
    (W : PointwiseFigure9SelectedWindowContainmentFields B) :
    HonestFigure9AdjacentWindowLowerE23
      B.localLabels.predicates B.turnBounds.turn :=
  Figure9ContainmentW12.honestE23_of_witnesses W.figure9_left

/-- The reduced W16 row reaches the local contradiction. -/
theorem contradiction
    (W : PointwiseFigure9SelectedWindowContainmentFields B) :
    False :=
  FiguresAssemblyW13.HonestFigureContainmentWitnesses.contradiction
    (figureWitnesses W)
    B.turnBounds.turn_nonnegative
    B.turnBounds.total_turn_lt_pi_div_three
    B.honestLateTriples

/-- A full W15 missing-window row lowers to the W16 selected Figure 9 row. -/
def ofMissingWindowContainmentFields
    (W15 : PointwiseMissingWindowContainmentFields B) :
    PointwiseFigure9SelectedWindowContainmentFields B where
  figure8 := W15.figure8
  figure9_left :=
    Figure9ContainmentW12.witnesses_of_containmentInterface
      W15.figure9_left

@[simp]
theorem ofMissingWindowContainmentFields_figure8
    (W15 : PointwiseMissingWindowContainmentFields B) :
    (ofMissingWindowContainmentFields W15).figure8 = W15.figure8 :=
  rfl

def ofMissingWindowContainmentFields_figure9_left_apply
    (W15 : PointwiseMissingWindowContainmentFields B) :
    forall {i : Nat}, 1 <= i -> i + 1 <= 10 ->
      Not (M8BrokenLatticeGood B.localLabels.predicates.data i) ->
      Not (M8BrokenLatticeGood B.localLabels.predicates.data (i + 1)) ->
        Figure9ContainmentW12.AdjacentWindowData B.turnBounds.turn i :=
  (ofMissingWindowContainmentFields W15).figure9_left

theorem ofMissingWindowContainmentFields_figure9_left_apply_eq
    (W15 : PointwiseMissingWindowContainmentFields B)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood B.localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood B.localLabels.predicates.data (i + 1))) :
    (ofMissingWindowContainmentFields W15).figure9_left
        hi hi_next hbad_i hbad_next =
      Figure9ContainmentW12.witnesses_of_containmentInterface
        W15.figure9_left hi hi_next hbad_i hbad_next := by
  rfl

end PointwiseFigure9SelectedWindowContainmentFields

/-- The base row plus the W16 reduced Figure 9 selected-witness row. -/
structure PointwiseLemma89Figure9SelectedWindowFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : PointwiseLemma89Base.{u} C hmin
  windowFields : PointwiseFigure9SelectedWindowContainmentFields base

namespace PointwiseLemma89Figure9SelectedWindowFields

variable (R : PointwiseLemma89Figure9SelectedWindowFields.{u} C hmin)

/-- Boundary-derived local labels for the reduced W16 row. -/
def localLabels : M8LocalLabels C :=
  R.base.localLabels

/-- Turn bounds for the reduced W16 row. -/
def turnBounds : M8TurnBounds :=
  R.base.turnBounds

/-- The W13 selected Figure witnesses attached to the reduced W16 row. -/
def figureWitnesses :
    FiguresAssemblyW13.HonestFigureContainmentWitnesses
      R.localLabels.predicates R.turnBounds.turn :=
  PointwiseFigure9SelectedWindowContainmentFields.figureWitnesses
    R.windowFields

/-- The reduced W16 row supplies the honest E22/E23 pair. -/
theorem E22_E23 :
    HonestFigure8SeparatedWindowLowerE22
        R.localLabels.predicates R.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        R.localLabels.predicates R.turnBounds.turn :=
  PointwiseFigure9SelectedWindowContainmentFields.E22_E23
    R.windowFields

/-- The reduced W16 row closes the localized Lemma 8/Lemma 9 contradiction. -/
theorem contradiction
    (R : PointwiseLemma89Figure9SelectedWindowFields.{u} C hmin) :
    False :=
  PointwiseFigure9SelectedWindowContainmentFields.contradiction
    R.windowFields

/-- Full W15 rows lower to the W16 selected-witness row. -/
def ofPointwiseLemma89WindowContainmentFields
    (R15 : PointwiseLemma89WindowContainmentFields.{u} C hmin) :
    PointwiseLemma89Figure9SelectedWindowFields.{u} C hmin where
  base := R15.base
  windowFields :=
    PointwiseFigure9SelectedWindowContainmentFields.ofMissingWindowContainmentFields
      R15.windowFields

@[simp]
theorem ofPointwiseLemma89WindowContainmentFields_base
    (R15 : PointwiseLemma89WindowContainmentFields.{u} C hmin) :
    (ofPointwiseLemma89WindowContainmentFields R15).base = R15.base :=
  rfl

end PointwiseLemma89Figure9SelectedWindowFields

/--
The full W15 missing-window package still routes through the W12 E22/E23
bridge when the original Figure 9 interface is available.
-/
theorem E22_E23_of_full_missing_window_fields
    {B : PointwiseLemma89Base.{u} C hmin}
    (W : PointwiseMissingWindowContainmentFields B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  E22E23BridgeW12.honestE22_E23_of_containmentInterfaces
    W.figure8 W.figure9_left

/--
The existing W13-to-refined route closes any full W15 row; the selected W16
row above records the smaller Figure 9 datum sufficient for the same local
Lemma 10 contradiction.
-/
theorem contradiction_of_full_w15_row
    (R : PointwiseLemma89WindowContainmentFields.{u} C hmin) :
    False :=
  FiguresToRefinedM8W13.M8LateLocalWindowContainmentFields.contradiction
    R.toLateLocalWindowContainmentFields

/-- Projection from the Lemma 8/Lemma 9 assembly row to the bridge pair. -/
theorem lemma8Lemma9Assembly_E22_E23
    {Dplanar : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)}
    {connectedNoCut : PreconnectedNoCutVertexCertificate C}
    (R :
      Lemma8Lemma9AssemblyW13.M8FiniteLemma8NoStartWindowData
        Dplanar connectedNoCut hmin) :
    HonestFigure8SeparatedWindowLowerE22
        R.localLabels.predicates R.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        R.localLabels.predicates R.turnBounds.turn :=
  R.honestE22_E23

end Figure9WindowContainmentW16
end Swanepoel
end ErdosProblems1066

end
