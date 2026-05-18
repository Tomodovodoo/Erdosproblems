import ErdosProblems1066.Swanepoel.ExactFigureAngleDataSourceW29

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W30 exact Figure inequalities

This file keeps the remaining Figure 8/Figure 9 exact angle-containment
inequalities as source data.  The selected Figure witness family supplies the
checked W12/Euclidean witnesses; the inequality family supplies the universal
angle-to-turn containments.  Together they reconstruct the W29 exact
angle-data source family and hence the exact E22/E23 source blocker.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace ExactFigureInequalitiesW30

open ExactFigureAngleDataSourceW29
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

abbrev LocalExactFigureAngleInequalities
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  FigureAngleContainmentConcreteW23.LocalExactFigureAngleInequalities
    localLabels turnBounds

abbrev LocalExactFigureAngleInequalitiesFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  ExactFigureAngleDataSourceW29.LocalExactFigureAngleInequalitiesFamily.{u}
    payForCut topologyArc lemma8

abbrev LocalExactFigureAngleDataSourceFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSourceFamily.{u}
    payForCut topologyArc lemma8

abbrev LocalSelectedFigureWitnessFieldsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
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

/-! ## Row-level inequality projections -/

/-- Project the exact Figure angle inequalities from a W22 exact-data row. -/
def localExactFigureAngleInequalities_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    LocalExactFigureAngleInequalities localLabels turnBounds where
  figure8 := D.figure8AngleContainment
  figure9_left := D.figure9AngleContainment

/-- Project the exact Figure angle inequalities from a W28 exact source row. -/
def localExactFigureAngleInequalities_of_localExactFigureWitnessSource
    (S : FigureExactAngleSourceW28.LocalExactFigureWitnessSource
      localLabels turnBounds) :
    LocalExactFigureAngleInequalities localLabels turnBounds :=
  S.exactInequalities

/-- Project the exact Figure angle inequalities from a W29 data-source row. -/
def localExactFigureAngleInequalities_of_localExactFigureAngleDataSource
    (S : ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSource
      localLabels turnBounds) :
    LocalExactFigureAngleInequalities localLabels turnBounds :=
  S.exactInequalities

/-! ## Family-level inequality constructors -/

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

/-- W22 exact angle-data rows supply the W30 exact-inequality family. -/
def localExactFigureAngleInequalitiesFamily_of_localExactAngleDataFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8 :=
  fun C hmin =>
    localExactFigureAngleInequalities_of_localExactAngleData
      (F.row C hmin)

/-- W28 exact source rows supply the W30 exact-inequality family. -/
def localExactFigureAngleInequalitiesFamily_of_localExactFigureWitnessSourceFamily
    (F : LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8 :=
  fun C hmin =>
    localExactFigureAngleInequalities_of_localExactFigureWitnessSource
      (F.row C hmin)

/-- W29 exact data-source rows supply the W30 exact-inequality family. -/
def localExactFigureAngleInequalitiesFamily_of_localExactFigureAngleDataSourceFamily
    (F : LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8 :=
  fun C hmin =>
    localExactFigureAngleInequalities_of_localExactFigureAngleDataSource
      (F.row C hmin)

/-- An inhabited W28 exact E22/E23 source blocker supplies the W30
exact-inequality family. -/
def localExactFigureAngleInequalitiesFamily_of_exactE22E23SourceBlocker
    (h : ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) :
    LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8 :=
  localExactFigureAngleInequalitiesFamily_of_localExactFigureWitnessSourceFamily
    (Classical.choice h)

/-! ## Exact E22/E23 Figure data -/

/-- Source-only exact Figure data for the E22/E23 route: selected Figure
witnesses plus the row-wise exact angle-containment inequalities. -/
structure ExactE22E23FigureData
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  selectedFigure :
    LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8
  exactInequalities :
    LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8

namespace ExactE22E23FigureData

/-- Rebuild the W29 exact angle-data source family from W30 Figure data. -/
def toLocalExactFigureAngleDataSourceFamily
    (D : ExactE22E23FigureData.{u} payForCut topologyArc lemma8) :
    LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  ExactFigureAngleDataSourceW29.localExactFigureAngleDataSourceFamily_of_selectedFigureWitnessFieldsAndInequalitiesFamily
    D.selectedFigure D.exactInequalities

/-- Rebuild the W22 exact angle-data family from W30 Figure data. -/
def toLocalExactAngleDataFamily
    (D : ExactE22E23FigureData.{u} payForCut topologyArc lemma8) :
    LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8 :=
  D.toLocalExactFigureAngleDataSourceFamily.toLocalExactAngleDataFamily

/-- Rebuild the W28 exact Figure witness source family from W30 Figure data. -/
def toLocalExactFigureWitnessSourceFamily
    (D : ExactE22E23FigureData.{u} payForCut topologyArc lemma8) :
    LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toLocalExactFigureAngleDataSourceFamily.toLocalExactFigureWitnessSourceFamily

/-- Project the selected Figure witness family stored in W30 Figure data. -/
def toSelectedFigureWitnessFieldsFamily
    (D : ExactE22E23FigureData.{u} payForCut topologyArc lemma8) :
    LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  D.selectedFigure

/-- W30 Figure data discharges the W28 exact E22/E23 source blocker. -/
theorem exactE22E23SourceBlocker
    (D : ExactE22E23FigureData.{u} payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  D.toLocalExactFigureAngleDataSourceFamily.exactE22E23SourceBlocker

/-- Each W30 Figure data row proves the local E22/E23 consequences through
the W29 data-source route. -/
theorem row_E22_E23
    (D : ExactE22E23FigureData.{u} payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  D.toLocalExactFigureAngleDataSourceFamily.row_E22_E23 C hmin

theorem row_E22
    (D : ExactE22E23FigureData.{u} payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  (D.row_E22_E23 C hmin).1

theorem row_E23
    (D : ExactE22E23FigureData.{u} payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  (D.row_E22_E23 C hmin).2

end ExactE22E23FigureData

/-! ## Constructors and blockers -/

/-- Repackage a W29 data-source family as W30 exact E22/E23 Figure data. -/
def exactE22E23FigureData_of_localExactFigureAngleDataSourceFamily
    (F : LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23FigureData.{u} payForCut topologyArc lemma8 where
  selectedFigure := F.toSelectedFigureWitnessFieldsFamily
  exactInequalities :=
    localExactFigureAngleInequalitiesFamily_of_localExactFigureAngleDataSourceFamily
      F

/-- Repackage W22 exact angle-data rows as W30 exact E22/E23 Figure data. -/
def exactE22E23FigureData_of_localExactAngleDataFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    ExactE22E23FigureData.{u} payForCut topologyArc lemma8 where
  selectedFigure :=
    FigureWitnessConcreteW27.selectedFigureWitnessFamily_of_localExactAngleDataFamily
      F
  exactInequalities :=
    localExactFigureAngleInequalitiesFamily_of_localExactAngleDataFamily F

/-- Repackage W28 exact source rows as W30 exact E22/E23 Figure data. -/
def exactE22E23FigureData_of_localExactFigureWitnessSourceFamily
    (F : LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23FigureData.{u} payForCut topologyArc lemma8 where
  selectedFigure := F.toSelectedFigureWitnessFieldsFamily
  exactInequalities :=
    localExactFigureAngleInequalitiesFamily_of_localExactFigureWitnessSourceFamily
      F

/-- Repackage an inhabited W28 exact E22/E23 source blocker as W30 exact
Figure data. -/
def exactE22E23FigureData_of_exactE22E23SourceBlocker
    (h : ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) :
    ExactE22E23FigureData.{u} payForCut topologyArc lemma8 :=
  exactE22E23FigureData_of_localExactFigureWitnessSourceFamily
    (Classical.choice h)

/-- Source-only blocker for the W30 exact E22/E23 Figure data package. -/
abbrev ExactE22E23FigureDataBlocker
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  Nonempty
    (ExactE22E23FigureData.{u} payForCut topologyArc lemma8)

/-- W30 Figure data blockers are equivalent to W29 data-source families. -/
theorem exactE22E23FigureDataBlocker_iff_localExactFigureAngleDataSourceFamily :
    ExactE22E23FigureDataBlocker.{u} payForCut topologyArc lemma8 <->
      Nonempty
        (LocalExactFigureAngleDataSourceFamily.{u}
          payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro D.toLocalExactFigureAngleDataSourceFamily
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (exactE22E23FigureData_of_localExactFigureAngleDataSourceFamily F)

/-- W30 Figure data blockers are equivalent to the W28 exact E22/E23 source
blocker. -/
theorem exactE22E23SourceBlocker_iff_exactE22E23FigureDataBlocker :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 <->
      ExactE22E23FigureDataBlocker.{u}
        payForCut topologyArc lemma8 :=
  ExactFigureAngleDataSourceW29.exactE22E23SourceBlocker_iff_localExactFigureAngleDataSourceFamily.trans
    exactE22E23FigureDataBlocker_iff_localExactFigureAngleDataSourceFamily.symm

/-- W30 Figure data discharges the W28 exact E22/E23 source blocker. -/
theorem exactE22E23SourceBlocker_of_exactE22E23FigureDataBlocker
    (h : ExactE22E23FigureDataBlocker.{u} payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  exactE22E23SourceBlocker_iff_exactE22E23FigureDataBlocker.2 h

/-- A W28 exact E22/E23 source blocker inhabits the W30 Figure data blocker. -/
theorem exactE22E23FigureDataBlocker_of_exactE22E23SourceBlocker
    (h : ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) :
    ExactE22E23FigureDataBlocker.{u} payForCut topologyArc lemma8 :=
  exactE22E23SourceBlocker_iff_exactE22E23FigureDataBlocker.1 h

/-- Selected Figure witness rows plus exact inequality rows inhabit the W30
Figure data blocker. -/
theorem exactE22E23FigureDataBlocker_of_selectedFigureWitnessFields_and_inequalities
    (W : LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8)
    (H : LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23FigureDataBlocker.{u}
      payForCut topologyArc lemma8 :=
  Nonempty.intro
    { selectedFigure := W
      exactInequalities := H }

/-- Nonempty selected Figure witness rows plus exact inequality rows discharge
the W28 exact E22/E23 source blocker through W30 Figure data. -/
theorem exactE22E23SourceBlocker_of_nonempty_selectedFigureWitnessFields_and_inequalities
    (hW : Nonempty
      (LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8))
    (H : LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 := by
  cases hW with
  | intro W =>
      exact exactE22E23SourceBlocker_of_exactE22E23FigureDataBlocker
        (exactE22E23FigureDataBlocker_of_selectedFigureWitnessFields_and_inequalities
          W H)

/-- Missing the W28 exact E22/E23 source blocker is exactly missing the W30
exact Figure data blocker. -/
theorem not_exactE22E23SourceBlocker_iff_not_exactE22E23FigureDataBlocker :
    Not (ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) <->
      Not
        (ExactE22E23FigureDataBlocker.{u}
          payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro hbad hData
    exact hbad
      (exactE22E23SourceBlocker_iff_exactE22E23FigureDataBlocker.2 hData)
  case mpr =>
    intro hbad hBlocker
    exact hbad
      (exactE22E23SourceBlocker_iff_exactE22E23FigureDataBlocker.1 hBlocker)

end ExactFigureInequalitiesW30
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW30LocalExactFigureAngleInequalitiesFamily :=
  Swanepoel.ExactFigureInequalitiesW30.LocalExactFigureAngleInequalitiesFamily

abbrev SwanepoelW30ExactE22E23FigureData :=
  Swanepoel.ExactFigureInequalitiesW30.ExactE22E23FigureData

abbrev SwanepoelW30ExactE22E23FigureDataBlocker :=
  Swanepoel.ExactFigureInequalitiesW30.ExactE22E23FigureDataBlocker

theorem swanepoelW30_exactE22E23SourceBlocker_iff_exactFigureDataBlocker
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Swanepoel.FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8 <->
      SwanepoelW30ExactE22E23FigureDataBlocker.{u}
        payForCut topologyArc lemma8 :=
  Swanepoel.ExactFigureInequalitiesW30.exactE22E23SourceBlocker_iff_exactE22E23FigureDataBlocker

theorem swanepoelW30_exactE22E23SourceBlocker_of_selectedFigureWitnessFields_and_inequalities
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
      SwanepoelW30LocalExactFigureAngleInequalitiesFamily.{u}
        payForCut topologyArc lemma8) :
    Swanepoel.FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8 :=
  Swanepoel.ExactFigureInequalitiesW30.exactE22E23SourceBlocker_of_nonempty_selectedFigureWitnessFields_and_inequalities
    hW H

end Verified
end ErdosProblems1066

end
