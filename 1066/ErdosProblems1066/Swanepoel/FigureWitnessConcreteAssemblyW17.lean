import ErdosProblems1066.Swanepoel.Figure8WindowContainmentW16
import ErdosProblems1066.Swanepoel.Figure9WindowContainmentW16

set_option autoImplicit false
set_option linter.unusedDecidableInType false

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureWitnessConcreteAssemblyW17

open AngleContainmentInterface
open Figure8WindowContainmentW16
open Figure9WindowContainmentW16
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma89WindowContainmentProofW15
open M8ConstructionInterface
open M8WindowContainmentConcrete
open MinimalGraphFacts

universe u

structure LocalFigureWitnessConcreteFields {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  figure8 :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn
  figure9_left :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn

namespace LocalFigureWitnessConcreteFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}

def toLocalWindowContainmentFields
    (F : LocalFigureWitnessConcreteFields localLabels turnBounds) :
    M8LocalWindowContainmentFields localLabels turnBounds :=
  M8LocalWindowContainmentFields.ofContainmentInterfaces
    F.figure8 F.figure9_left

def figureWitnesses
    (F : LocalFigureWitnessConcreteFields localLabels turnBounds) :
    FiguresAssemblyW13.HonestFigureContainmentWitnesses
      localLabels.predicates turnBounds.turn :=
  FiguresAssemblyW13.witnesses_of_localWindowContainmentFields
    F.toLocalWindowContainmentFields

theorem E22_E23
    (F : LocalFigureWitnessConcreteFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  FiguresAssemblyW13.HonestFigureContainmentWitnesses.E22_E23
    F.figureWitnesses

@[simp]
theorem toLocalWindowContainmentFields_figure8
    (F : LocalFigureWitnessConcreteFields localLabels turnBounds) :
    F.toLocalWindowContainmentFields.figure8 = F.figure8 :=
  rfl

@[simp]
theorem toLocalWindowContainmentFields_figure9_left
    (F : LocalFigureWitnessConcreteFields localLabels turnBounds) :
    F.toLocalWindowContainmentFields.figure9_left = F.figure9_left :=
  rfl

end LocalFigureWitnessConcreteFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}
variable {B : PointwiseLemma89Base.{u} C hmin}

structure PointwiseFigureWitnessConcreteFields
    (B : PointwiseLemma89Base.{u} C hmin) where
  fields : LocalFigureWitnessConcreteFields B.localLabels B.turnBounds

namespace PointwiseFigureWitnessConcreteFields

variable (F : PointwiseFigureWitnessConcreteFields B)

def toFigure8WindowContainmentField :
    PointwiseFigure8WindowContainmentField B where
  figure8 := F.fields.figure8

def toFigure9SelectedWindowContainmentFields :
    PointwiseFigure9SelectedWindowContainmentFields B where
  figure8 := F.fields.figure8
  figure9_left :=
    Figure9ContainmentW12.witnesses_of_containmentInterface
      F.fields.figure9_left

def toPointwiseMissingWindowContainmentFields :
    PointwiseMissingWindowContainmentFields B where
  figure8 := F.fields.figure8
  figure9_left := F.fields.figure9_left

def toLocalWindowContainmentFields :
    M8LocalWindowContainmentFields B.localLabels B.turnBounds :=
  F.fields.toLocalWindowContainmentFields

def figureWitnesses :
    FiguresAssemblyW13.HonestFigureContainmentWitnesses
      B.localLabels.predicates B.turnBounds.turn :=
  F.fields.figureWitnesses

theorem figure8_E22
    (F : PointwiseFigureWitnessConcreteFields B) :
    HonestFigure8SeparatedWindowLowerE22
      B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigure8WindowContainmentField.honestFigure8SeparatedWindowLowerE22
    (toFigure8WindowContainmentField F)

theorem figure9_E23
    (F : PointwiseFigureWitnessConcreteFields B) :
    HonestFigure9AdjacentWindowLowerE23
      B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigure9SelectedWindowContainmentFields.figure9_E23
    (toFigure9SelectedWindowContainmentFields F)

theorem E22_E23
    (F : PointwiseFigureWitnessConcreteFields B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  LocalFigureWitnessConcreteFields.E22_E23 F.fields

theorem missingFields_E22_E23
    (F : PointwiseFigureWitnessConcreteFields B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  PointwiseMissingWindowContainmentFields.E22_E23
    (toPointwiseMissingWindowContainmentFields F)

theorem selectedFields_E22_E23
    (F : PointwiseFigureWitnessConcreteFields B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigure9SelectedWindowContainmentFields.E22_E23
    (toFigure9SelectedWindowContainmentFields F)

@[simp]
theorem toPointwiseMissingWindowContainmentFields_figure8 :
    F.toPointwiseMissingWindowContainmentFields.figure8 =
      F.fields.figure8 :=
  rfl

@[simp]
theorem toPointwiseMissingWindowContainmentFields_figure9_left :
    F.toPointwiseMissingWindowContainmentFields.figure9_left =
      F.fields.figure9_left :=
  rfl

@[simp]
theorem toFigure9SelectedWindowContainmentFields_figure8 :
    F.toFigure9SelectedWindowContainmentFields.figure8 =
      F.fields.figure8 :=
  rfl

def toPointwiseLemma89WindowContainmentFields :
    PointwiseLemma89WindowContainmentFields.{u} C hmin where
  base := B
  windowFields := F.toPointwiseMissingWindowContainmentFields

theorem pointwiseLemma89WindowContainmentFields_E22_E23 :
    HonestFigure8SeparatedWindowLowerE22
        F.toPointwiseLemma89WindowContainmentFields.localLabels.predicates
        F.toPointwiseLemma89WindowContainmentFields.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        F.toPointwiseLemma89WindowContainmentFields.localLabels.predicates
        F.toPointwiseLemma89WindowContainmentFields.turnBounds.turn :=
  PointwiseLemma89WindowContainmentFields.E22_E23
    F.toPointwiseLemma89WindowContainmentFields

end PointwiseFigureWitnessConcreteFields

end FigureWitnessConcreteAssemblyW17
end Swanepoel
end ErdosProblems1066

end
