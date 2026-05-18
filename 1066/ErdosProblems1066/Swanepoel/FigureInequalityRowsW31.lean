import ErdosProblems1066.Swanepoel.ExactFigureInequalitiesW30

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W31 exact Figure inequality rows

This file is a source-row layer for the exact Figure 8/Figure 9 E22/E23
route.  A row stores the selected Figure witness data from W27 together with
the exact angle-containment inequalities from W29/W30, then routes all E22/E23
consequences through the checked W28/W29/W30 packages.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureInequalityRowsW31

open ExactFigureAngleDataSourceW29
open ExactFigureInequalitiesW30
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

abbrev LocalSelectedFigureWitnessFields
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  FigureWitnessConcreteW27.LocalSelectedFigureWitnessFields
    localLabels turnBounds

abbrev LocalExactFigureAngleInequalities
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  ExactFigureInequalitiesW30.LocalExactFigureAngleInequalities
    localLabels turnBounds

/-- One exact Figure inequality source row: selected witness data plus the
exact angle-containment inequalities for that same local row. -/
structure LocalExactFigureInequalityRows
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  selectedFigure :
    LocalSelectedFigureWitnessFields localLabels turnBounds
  exactInequalities :
    LocalExactFigureAngleInequalities localLabels turnBounds

namespace LocalExactFigureInequalityRows

variable {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}

/-- Convert the W31 row back to the W29 exact angle-data source row. -/
def toLocalExactFigureAngleDataSource
    (R : LocalExactFigureInequalityRows localLabels turnBounds) :
    ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSource
      localLabels turnBounds where
  selectedFigure := R.selectedFigure
  exactInequalities := R.exactInequalities

/-- Convert the W31 row back to W22 local exact angle data. -/
def toLocalExactAngleData
    (R : LocalExactFigureInequalityRows localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds :=
  R.toLocalExactFigureAngleDataSource.toLocalExactAngleData

/-- Convert the W31 row back to the W28 exact Figure witness source. -/
def toLocalExactFigureWitnessSource
    (R : LocalExactFigureInequalityRows localLabels turnBounds) :
    FigureExactAngleSourceW28.LocalExactFigureWitnessSource
      localLabels turnBounds :=
  R.toLocalExactFigureAngleDataSource.toLocalExactFigureWitnessSource

/-- Project the selected witness row stored in W31. -/
def toLocalSelectedFigureWitnessFields
    (R : LocalExactFigureInequalityRows localLabels turnBounds) :
    LocalSelectedFigureWitnessFields localLabels turnBounds :=
  R.selectedFigure

/-- Project the exact inequality row stored in W31. -/
def toLocalExactFigureAngleInequalities
    (R : LocalExactFigureInequalityRows localLabels turnBounds) :
    LocalExactFigureAngleInequalities localLabels turnBounds :=
  R.exactInequalities

/-- The W31 row proves E22/E23 only by routing through the W29/W28 source
packages. -/
theorem E22_E23
    (R : LocalExactFigureInequalityRows localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  R.toLocalExactFigureAngleDataSource.E22_E23

theorem E22
    (R : LocalExactFigureInequalityRows localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn :=
  R.E22_E23.1

theorem E23
    (R : LocalExactFigureInequalityRows localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  R.E22_E23.2

end LocalExactFigureInequalityRows

/-! ## Family rows -/

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

abbrev LocalSelectedFigureWitnessFieldsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
    payForCut topologyArc lemma8

abbrev LocalExactFigureAngleInequalitiesFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  ExactFigureInequalitiesW30.LocalExactFigureAngleInequalitiesFamily.{u}
    payForCut topologyArc lemma8

abbrev LocalExactFigureAngleDataSourceFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSourceFamily.{u}
    payForCut topologyArc lemma8

abbrev LocalExactFigureWitnessSourceFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  FigureExactAngleSourceW28.LocalExactFigureWitnessSourceFamily.{u}
    payForCut topologyArc lemma8

abbrev ExactE22E23SourceBlocker
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
    payForCut topologyArc lemma8

abbrev ExactE22E23FigureData
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  ExactFigureInequalitiesW30.ExactE22E23FigureData.{u}
    payForCut topologyArc lemma8

/-- W31 family of exact Figure inequality source rows over the W21 base
inputs. -/
structure ExactFigureInequalityRowsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        LocalExactFigureInequalityRows
          (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

namespace ExactFigureInequalityRowsFamily

/-- Forget W31 rows back to the W29 exact angle-data source family. -/
def toLocalExactFigureAngleDataSourceFamily
    (F : ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toLocalExactFigureAngleDataSource

/-- Forget W31 rows back to the W22 exact angle-data family. -/
def toLocalExactAngleDataFamily
    (F : ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8 :=
  F.toLocalExactFigureAngleDataSourceFamily.toLocalExactAngleDataFamily

/-- Forget W31 rows back to the W28 exact Figure witness source family. -/
def toLocalExactFigureWitnessSourceFamily
    (F : ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  F.toLocalExactFigureAngleDataSourceFamily.toLocalExactFigureWitnessSourceFamily

/-- Project the selected Figure witness rows carried by W31. -/
def toSelectedFigureWitnessFieldsFamily
    (F : ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8) :
    LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toLocalSelectedFigureWitnessFields

/-- Project the exact Figure inequality rows carried by W31. -/
def toLocalExactFigureAngleInequalitiesFamily
    (F : ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8 :=
  fun C hmin =>
    (F.row C hmin).toLocalExactFigureAngleInequalities

/-- Repackage W31 rows as the W30 exact E22/E23 Figure data package. -/
def toExactE22E23FigureData
    (F : ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23FigureData.{u} payForCut topologyArc lemma8 :=
  ExactFigureInequalitiesW30.exactE22E23FigureData_of_localExactFigureAngleDataSourceFamily
    F.toLocalExactFigureAngleDataSourceFamily

/-- W31 rows discharge the W28 exact E22/E23 source blocker through W29/W30. -/
theorem exactE22E23SourceBlocker
    (F : ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  F.toLocalExactFigureAngleDataSourceFamily.exactE22E23SourceBlocker

/-- Each W31 row proves the local E22/E23 consequences through W29/W28. -/
theorem row_E22_E23
    (F : ExactFigureInequalityRowsFamily.{u}
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

theorem row_E22
    (F : ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  (F.row_E22_E23 C hmin).1

theorem row_E23
    (F : ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  (F.row_E22_E23 C hmin).2

end ExactFigureInequalityRowsFamily

/-! ## Constructors and exact blockers -/

/-- Build W31 rows from selected witness rows and exact inequality rows. -/
def exactFigureInequalityRowsFamily_of_selectedFigureWitnessFieldsAndInequalities
    (W : LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8)
    (H : LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8) :
    ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    { selectedFigure := W.row C hmin
      exactInequalities := H C hmin }

/-- Repackage a W29 data-source family as W31 rows. -/
def exactFigureInequalityRowsFamily_of_localExactFigureAngleDataSourceFamily
    (F : LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8) :
    ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    { selectedFigure := (F.row C hmin).selectedFigure
      exactInequalities := (F.row C hmin).exactInequalities }

/-- Repackage W30 exact E22/E23 Figure data as W31 rows. -/
def exactFigureInequalityRowsFamily_of_exactE22E23FigureData
    (D : ExactE22E23FigureData.{u} payForCut topologyArc lemma8) :
    ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8 :=
  exactFigureInequalityRowsFamily_of_selectedFigureWitnessFieldsAndInequalities
    D.selectedFigure D.exactInequalities

/-- Repackage an inhabited W28 exact E22/E23 source blocker as W31 rows. -/
def exactFigureInequalityRowsFamily_of_exactE22E23SourceBlocker
    (h : ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) :
    ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8 :=
  exactFigureInequalityRowsFamily_of_exactE22E23FigureData
    (ExactFigureInequalitiesW30.exactE22E23FigureData_of_exactE22E23SourceBlocker
      h)

/-- The W31 row-family blocker. -/
abbrev ExactFigureInequalityRowsBlocker
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  Nonempty
    (ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8)

/-- The exact source components needed to build W31 rows. -/
abbrev ExactFigureInequalityRowComponents
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  Exists fun _ :
      LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8 =>
    LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8

/-- W31 rows are exactly selected Figure witness rows plus exact inequality
rows. -/
theorem exactFigureInequalityRowsBlocker_iff_components :
    ExactFigureInequalityRowsBlocker.{u} payForCut topologyArc lemma8 <->
      ExactFigureInequalityRowComponents.{u}
        payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact
          Exists.intro F.toSelectedFigureWitnessFieldsFamily
            F.toLocalExactFigureAngleInequalitiesFamily
  case mpr =>
    intro h
    cases h with
    | intro W H =>
        exact Nonempty.intro
          (exactFigureInequalityRowsFamily_of_selectedFigureWitnessFieldsAndInequalities
            W H)

/-- W31 row-family blockers are equivalent to W29 data-source families. -/
theorem exactFigureInequalityRowsBlocker_iff_localExactFigureAngleDataSourceFamily :
    ExactFigureInequalityRowsBlocker.{u} payForCut topologyArc lemma8 <->
      Nonempty
        (LocalExactFigureAngleDataSourceFamily.{u}
          payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro F.toLocalExactFigureAngleDataSourceFamily
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (exactFigureInequalityRowsFamily_of_localExactFigureAngleDataSourceFamily
            F)

/-- W31 row-family blockers are equivalent to W30 exact Figure data blockers. -/
theorem exactFigureInequalityRowsBlocker_iff_exactE22E23FigureDataBlocker :
    ExactFigureInequalityRowsBlocker.{u} payForCut topologyArc lemma8 <->
      ExactFigureInequalitiesW30.ExactE22E23FigureDataBlocker.{u}
        payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro F.toExactE22E23FigureData
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro
          (exactFigureInequalityRowsFamily_of_exactE22E23FigureData D)

/-- W31 row-family blockers are equivalent to the W28 exact E22/E23 source
blocker. -/
theorem exactE22E23SourceBlocker_iff_exactFigureInequalityRowsBlocker :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 <->
      ExactFigureInequalityRowsBlocker.{u}
        payForCut topologyArc lemma8 :=
  ExactFigureInequalitiesW30.exactE22E23SourceBlocker_iff_exactE22E23FigureDataBlocker.trans
    exactFigureInequalityRowsBlocker_iff_exactE22E23FigureDataBlocker.symm

/-- The W28 exact blocker is exactly the W31 selected-witness plus exact
inequality component package. -/
theorem exactE22E23SourceBlocker_iff_components :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 <->
      ExactFigureInequalityRowComponents.{u}
        payForCut topologyArc lemma8 :=
  exactE22E23SourceBlocker_iff_exactFigureInequalityRowsBlocker.trans
    exactFigureInequalityRowsBlocker_iff_components

/-- W31 rows discharge the W28 exact E22/E23 source blocker. -/
theorem exactE22E23SourceBlocker_of_exactFigureInequalityRowsBlocker
    (h : ExactFigureInequalityRowsBlocker.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  exactE22E23SourceBlocker_iff_exactFigureInequalityRowsBlocker.2 h

/-- Selected Figure witness rows plus exact inequality rows discharge the W28
exact E22/E23 source blocker. -/
theorem exactE22E23SourceBlocker_of_components
    (h : ExactFigureInequalityRowComponents.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  exactE22E23SourceBlocker_iff_components.2 h

/-- Missing the W28 exact blocker is exactly missing W31 rows. -/
theorem not_exactE22E23SourceBlocker_iff_not_exactFigureInequalityRowsBlocker :
    Not (ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) <->
      Not
        (ExactFigureInequalityRowsBlocker.{u}
          payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro hbad hRows
    exact hbad
      (exactE22E23SourceBlocker_iff_exactFigureInequalityRowsBlocker.2
        hRows)
  case mpr =>
    intro hbad hSource
    exact hbad
      (exactE22E23SourceBlocker_iff_exactFigureInequalityRowsBlocker.1
        hSource)

/-- Missing W31 rows is exactly missing the selected-witness plus exact
inequality component package. -/
theorem not_exactFigureInequalityRowsBlocker_iff_not_components :
    Not
        (ExactFigureInequalityRowsBlocker.{u}
          payForCut topologyArc lemma8) <->
      Not
        (ExactFigureInequalityRowComponents.{u}
          payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro hbad hComponents
    exact hbad
      (exactFigureInequalityRowsBlocker_iff_components.2 hComponents)
  case mpr =>
    intro hbad hRows
    exact hbad
      (exactFigureInequalityRowsBlocker_iff_components.1 hRows)

end FigureInequalityRowsW31
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW31LocalExactFigureInequalityRows
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : Swanepoel.M8ConstructionInterface.M8LocalLabels C)
    (turnBounds : Swanepoel.M8ConstructionInterface.M8TurnBounds) :=
  Swanepoel.FigureInequalityRowsW31.LocalExactFigureInequalityRows
    localLabels turnBounds

abbrev SwanepoelW31ExactFigureInequalityRowsFamily :=
  Swanepoel.FigureInequalityRowsW31.ExactFigureInequalityRowsFamily

abbrev SwanepoelW31ExactFigureInequalityRowsBlocker :=
  Swanepoel.FigureInequalityRowsW31.ExactFigureInequalityRowsBlocker

abbrev SwanepoelW31ExactFigureInequalityRowComponents :=
  Swanepoel.FigureInequalityRowsW31.ExactFigureInequalityRowComponents

theorem swanepoelW31_exactE22E23SourceBlocker_iff_rowsBlocker
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Swanepoel.FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8 <->
      SwanepoelW31ExactFigureInequalityRowsBlocker.{u}
        payForCut topologyArc lemma8 :=
  Swanepoel.FigureInequalityRowsW31.exactE22E23SourceBlocker_iff_exactFigureInequalityRowsBlocker

theorem swanepoelW31_exactE22E23SourceBlocker_iff_components
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Swanepoel.FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8 <->
      SwanepoelW31ExactFigureInequalityRowComponents.{u}
        payForCut topologyArc lemma8 :=
  Swanepoel.FigureInequalityRowsW31.exactE22E23SourceBlocker_iff_components

theorem swanepoelW31_rowsBlocker_iff_dataSourceFamily
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    SwanepoelW31ExactFigureInequalityRowsBlocker.{u}
        payForCut topologyArc lemma8 <->
      Nonempty
        (Swanepoel.ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSourceFamily.{u}
          payForCut topologyArc lemma8) :=
  Swanepoel.FigureInequalityRowsW31.exactFigureInequalityRowsBlocker_iff_localExactFigureAngleDataSourceFamily

end Verified
end ErdosProblems1066

end
