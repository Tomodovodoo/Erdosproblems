import ErdosProblems1066.Swanepoel.FigureExactAngleSourceW28

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W29 exact Figure angle-data source

This file tightens the W28 exact E22/E23 source boundary around the checked
selected Figure witnesses from W27.  A selected Figure witness row by itself
contains the selected W12 and Euclidean witnesses; adding the local universal
exact angle-containment inequalities reconstructs the W22 local exact angle
data, hence the W28 `ExactE22E23SourceBlocker`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace ExactFigureAngleDataSourceW29

open FigureAngleContainmentConcreteW23
open FigureAngleSourceInhabitationW21
open FigureExactAngleCertificateInhabitationW22
open FigureExactAngleSourceW28
open FigureWitnessConcreteW27
open Lemma10AnalyticBridge
open M8ConstructionInterface
open MinimalGraphFacts

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

abbrev LocalSelectedW12WitnessFields
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  FigureWitnessConcreteW27.LocalSelectedW12WitnessFields
    localLabels turnBounds

abbrev LocalSelectedFigureWitnessFields
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  FigureWitnessConcreteW27.LocalSelectedFigureWitnessFields
    localLabels turnBounds

/-! ## Row constructors from selected witnesses plus exact inequalities -/

/-- Selected W12 witnesses plus the local universal exact inequalities rebuild
the W22 local exact Figure angle data. -/
def localExactAngleData_of_selectedW12WitnessFieldsAndInequalities
    (W : LocalSelectedW12WitnessFields localLabels turnBounds)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds :=
  localExactData_of_w12WitnessesAndInequalities
    W.figure8 W.figure9_left H

/-- Selected W12 witnesses plus local exact inequalities build the W28 exact
Figure witness source. -/
def localExactFigureWitnessSource_of_selectedW12WitnessFieldsAndInequalities
    (W : LocalSelectedW12WitnessFields localLabels turnBounds)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    LocalExactFigureWitnessSource localLabels turnBounds :=
  localExactFigureWitnessSource_of_w12AndInequalities
    W.figure8 W.figure9_left H

/-- A W27 selected Figure witness row plus local exact inequalities rebuilds
the W22 local exact Figure angle data. -/
def localExactAngleData_of_selectedFigureWitnessFieldsAndInequalities
    (W : LocalSelectedFigureWitnessFields localLabels turnBounds)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds :=
  localExactAngleData_of_selectedW12WitnessFieldsAndInequalities
    W.selectedW12 H

/-- A W27 selected Figure witness row plus local exact inequalities builds
the W28 exact Figure witness source. -/
def localExactFigureWitnessSource_of_selectedFigureWitnessFieldsAndInequalities
    (W : LocalSelectedFigureWitnessFields localLabels turnBounds)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    LocalExactFigureWitnessSource localLabels turnBounds :=
  localExactFigureWitnessSource_of_selectedW12WitnessFieldsAndInequalities
    W.selectedW12 H

/-- The selected-witness-plus-inequality row proves E22/E23 through the W28
exact source route. -/
theorem local_E22_E23_of_selectedFigureWitnessFieldsAndInequalities
    (W : LocalSelectedFigureWitnessFields localLabels turnBounds)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (localExactFigureWitnessSource_of_selectedFigureWitnessFieldsAndInequalities
    W H).E22_E23

/-! ## Exact data-source rows -/

/-- A row-level source for W22 exact angle data, factored through the already
checked W27 selected Figure witness package plus the remaining exact universal
angle-containment inequalities. -/
structure LocalExactFigureAngleDataSource
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  selectedFigure :
    LocalSelectedFigureWitnessFields localLabels turnBounds
  exactInequalities :
    LocalExactFigureAngleInequalities localLabels turnBounds

namespace LocalExactFigureAngleDataSource

variable {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}

/-- Reconstruct W22 local exact angle data from the W29 row source. -/
def toLocalExactAngleData
    (S : LocalExactFigureAngleDataSource localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds :=
  localExactAngleData_of_selectedFigureWitnessFieldsAndInequalities
    S.selectedFigure S.exactInequalities

/-- Reconstruct the W28 exact Figure witness source from the W29 row source. -/
def toLocalExactFigureWitnessSource
    (S : LocalExactFigureAngleDataSource localLabels turnBounds) :
    LocalExactFigureWitnessSource localLabels turnBounds :=
  localExactFigureWitnessSource_of_selectedFigureWitnessFieldsAndInequalities
    S.selectedFigure S.exactInequalities

/-- Project the selected W27 witness row carried by the W29 source. -/
def toLocalSelectedFigureWitnessFields
    (S : LocalExactFigureAngleDataSource localLabels turnBounds) :
    LocalSelectedFigureWitnessFields localLabels turnBounds :=
  S.selectedFigure

/-- The W29 row source proves E22/E23 through the W28 exact source route. -/
theorem E22_E23
    (S : LocalExactFigureAngleDataSource localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  S.toLocalExactFigureWitnessSource.E22_E23

theorem E22
    (S : LocalExactFigureAngleDataSource localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn :=
  S.E22_E23.1

theorem E23
    (S : LocalExactFigureAngleDataSource localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  S.E22_E23.2

end LocalExactFigureAngleDataSource

/-- Repackage W22 exact angle data as a W29 selected-witness-plus-inequality
source row. -/
def localExactFigureAngleDataSource_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    LocalExactFigureAngleDataSource localLabels turnBounds where
  selectedFigure :=
    FigureWitnessConcreteW27.localSelectedFigureWitnessFields_of_localExactAngleData
      D
  exactInequalities :=
    { figure8 := D.figure8AngleContainment
      figure9_left := D.figure9AngleContainment }

/-- Pointwise exact data and the W29 row source have the same inhabitance
content. -/
theorem localExactFigureAngleDataSource_nonempty_iff_localExactAngleData :
    Nonempty
        (LocalExactFigureAngleDataSource localLabels turnBounds) <->
      Nonempty (LocalExactAngleData localLabels turnBounds) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toLocalExactAngleData
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro
          (localExactFigureAngleDataSource_of_localExactAngleData D)

/-! ## Family-level exact data sources -/

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

/-- Row-wise local exact Figure angle inequalities over the W21 base rows. -/
abbrev LocalExactFigureAngleInequalitiesFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      LocalExactFigureAngleInequalities
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

/-- A family of W29 exact angle-data sources over the W21 base rows. -/
structure LocalExactFigureAngleDataSourceFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        LocalExactFigureAngleDataSource
          (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

namespace LocalExactFigureAngleDataSourceFamily

/-- Forget the W29 family back to the W22 exact angle-data family. -/
def toLocalExactAngleDataFamily
    (F : LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toLocalExactAngleData

/-- Convert a W29 family to the W28 exact Figure witness source family. -/
def toLocalExactFigureWitnessSourceFamily
    (F : LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toLocalExactFigureWitnessSource

/-- Project the selected W27 Figure witness family carried by the W29 rows. -/
def toSelectedFigureWitnessFieldsFamily
    (F : LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8) :
    FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toLocalSelectedFigureWitnessFields

/-- The W29 source family discharges the W28 exact E22/E23 source blocker. -/
theorem exactE22E23SourceBlocker
    (F : LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  Nonempty.intro F.toLocalExactFigureWitnessSourceFamily

/-- Each W29 source row proves the local E22/E23 consequences through W28. -/
theorem row_E22_E23
    (F : LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  (F.row C hmin).E22_E23

end LocalExactFigureAngleDataSourceFamily

/-- Build the W29 source family from a W22 exact angle-data family. -/
def localExactFigureAngleDataSourceFamily_of_localExactAngleDataFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localExactFigureAngleDataSource_of_localExactAngleData
      (F.row C hmin)

/-- Build the W29 source family from selected W27 Figure witnesses plus
row-wise exact angle inequalities. -/
def localExactFigureAngleDataSourceFamily_of_selectedFigureWitnessFieldsAndInequalitiesFamily
    (W : FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8)
    (H : LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    { selectedFigure := W.row C hmin
      exactInequalities := H C hmin }

/-- Selected W27 Figure witnesses plus row-wise exact inequalities rebuild
the W22 exact angle-data family. -/
def localExactAngleDataFamily_of_selectedFigureWitnessFieldsAndInequalitiesFamily
    (W : FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8)
    (H : LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8 :=
  (localExactFigureAngleDataSourceFamily_of_selectedFigureWitnessFieldsAndInequalitiesFamily
    W H).toLocalExactAngleDataFamily

/-- Selected W27 Figure witnesses plus row-wise exact inequalities discharge
the W28 exact E22/E23 source blocker. -/
theorem exactE22E23SourceBlocker_of_selectedFigureWitnessFieldsAndInequalitiesFamily
    (W : FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8)
    (H : LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  (localExactFigureAngleDataSourceFamily_of_selectedFigureWitnessFieldsAndInequalitiesFamily
    W H).exactE22E23SourceBlocker

/-- Nonempty selected W27 Figure witnesses plus row-wise exact inequalities
inhabit the W22 exact angle-data family. -/
theorem localExactAngleDataFamily_nonempty_of_selectedFigureWitnessFieldsFamily_and_inequalitiesFamily
    (hW : Nonempty
      (FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8))
    (H : LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (LocalExactAngleDataFamily.{u}
        payForCut topologyArc lemma8) := by
  cases hW with
  | intro W =>
      exact Nonempty.intro
        (localExactAngleDataFamily_of_selectedFigureWitnessFieldsAndInequalitiesFamily
          W H)

/-- Nonempty selected W27 Figure witnesses plus row-wise exact inequalities
discharge the W28 exact E22/E23 source blocker. -/
theorem exactE22E23SourceBlocker_of_nonempty_selectedFigureWitnessFieldsFamily_and_inequalitiesFamily
    (hW : Nonempty
      (FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8))
    (H : LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 := by
  cases hW with
  | intro W =>
      exact
        exactE22E23SourceBlocker_of_selectedFigureWitnessFieldsAndInequalitiesFamily
          W H

/-- W29 exact data-source families and W22 local exact angle-data families
have the same family-level inhabitance content. -/
theorem localExactFigureAngleDataSourceFamily_nonempty_iff_localExactAngleDataFamily :
    Nonempty
        (LocalExactFigureAngleDataSourceFamily.{u}
          payForCut topologyArc lemma8) <->
      Nonempty
        (LocalExactAngleDataFamily.{u}
          payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro F.toLocalExactAngleDataFamily
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (localExactFigureAngleDataSourceFamily_of_localExactAngleDataFamily
            F)

/-- The W28 exact E22/E23 blocker is exactly the W29 data-source family. -/
theorem exactE22E23SourceBlocker_iff_localExactFigureAngleDataSourceFamily :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 <->
      Nonempty
        (LocalExactFigureAngleDataSourceFamily.{u}
          payForCut topologyArc lemma8) :=
  exactE22E23SourceBlocker_iff_localExactAngleDataFamily.trans
    localExactFigureAngleDataSourceFamily_nonempty_iff_localExactAngleDataFamily.symm

/-- Missing the W28 exact blocker is exactly missing W22 local exact angle
data. -/
theorem not_exactE22E23SourceBlocker_iff_not_localExactAngleDataFamily :
    Not (ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) <->
      Not
        (Nonempty
          (LocalExactAngleDataFamily.{u}
            payForCut topologyArc lemma8)) := by
  constructor
  case mp =>
    intro hbad hData
    exact hbad
      (exactE22E23SourceBlocker_iff_localExactAngleDataFamily.2 hData)
  case mpr =>
    intro hbad hBlocker
    exact hbad
      (exactE22E23SourceBlocker_iff_localExactAngleDataFamily.1 hBlocker)

/-- Missing the W28 exact blocker is exactly missing the W29 data-source
family. -/
theorem not_exactE22E23SourceBlocker_iff_not_localExactFigureAngleDataSourceFamily :
    Not (ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) <->
      Not
        (Nonempty
          (LocalExactFigureAngleDataSourceFamily.{u}
            payForCut topologyArc lemma8)) := by
  constructor
  case mp =>
    intro hbad hSource
    exact hbad
      (exactE22E23SourceBlocker_iff_localExactFigureAngleDataSourceFamily.2
        hSource)
  case mpr =>
    intro hbad hBlocker
    exact hbad
      (exactE22E23SourceBlocker_iff_localExactFigureAngleDataSourceFamily.1
        hBlocker)

end ExactFigureAngleDataSourceW29
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW29LocalExactFigureAngleDataSource
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : Swanepoel.M8ConstructionInterface.M8LocalLabels C)
    (turnBounds : Swanepoel.M8ConstructionInterface.M8TurnBounds) :=
  Swanepoel.ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSource
    localLabels turnBounds

abbrev SwanepoelW29LocalExactFigureAngleDataSourceFamily :=
  Swanepoel.ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSourceFamily

abbrev SwanepoelW29LocalExactFigureAngleInequalitiesFamily :=
  Swanepoel.ExactFigureAngleDataSourceW29.LocalExactFigureAngleInequalitiesFamily

theorem swanepoelW29_exactE22E23SourceBlocker_iff_dataSourceFamily
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Swanepoel.FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8 <->
      Nonempty
        (SwanepoelW29LocalExactFigureAngleDataSourceFamily.{u}
          payForCut topologyArc lemma8) :=
  Swanepoel.ExactFigureAngleDataSourceW29.exactE22E23SourceBlocker_iff_localExactFigureAngleDataSourceFamily

theorem swanepoelW29_exactE22E23SourceBlocker_of_selectedFigureWitnessFields_and_inequalities
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (hW : Nonempty
      (Swanepoel.FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8))
    (H :
      SwanepoelW29LocalExactFigureAngleInequalitiesFamily.{u}
        payForCut topologyArc lemma8) :
    Swanepoel.FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8 :=
  Swanepoel.ExactFigureAngleDataSourceW29.exactE22E23SourceBlocker_of_nonempty_selectedFigureWitnessFieldsFamily_and_inequalitiesFamily
    hW H

theorem swanepoelW29_missing_exactE22E23SourceBlocker_iff_missing_dataSourceFamily
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Not
        (Swanepoel.FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
          payForCut topologyArc lemma8) <->
      Not
        (Nonempty
          (SwanepoelW29LocalExactFigureAngleDataSourceFamily.{u}
            payForCut topologyArc lemma8)) :=
  Swanepoel.ExactFigureAngleDataSourceW29.not_exactE22E23SourceBlocker_iff_not_localExactFigureAngleDataSourceFamily

end Verified
end ErdosProblems1066

end
