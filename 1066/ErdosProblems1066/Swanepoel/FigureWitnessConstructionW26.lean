import ErdosProblems1066.Swanepoel.FigureSelectedWitnessInhabitationW25

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W26 Figure witness construction

This file does not introduce a new assumption package.  It records direct
constructions from the existing W19/W22/W23/W25 exact angle-containment data
to the selected W12 witnesses and the W24 selected Euclidean witness fields,
then projects the E22/E23 consequences.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureWitnessConstructionW26

open AngleContainmentBridgeProducerW19
open AngleContainmentInterface
open FigureAngleContainmentConcreteW23
open FigureAngleInequalitiesW24
open FigureExactAngleCertificateInhabitationW22
open FigureSelectedWitnessInhabitationW25
open FigureAngleSourceInhabitationW21
open Lemma10AnalyticBridge
open Lemma10Bridge
open M8ConstructionInterface
open MinimalGraphFacts

universe u

abbrev SelectedW12WitnessFields :=
  FigureSelectedWitnessInhabitationW25.SelectedFigureW12WitnessFields

abbrev SelectedEuclideanWitnessFields :=
  FigureAngleInequalitiesW24.SelectedFigureEuclideanWitnessFields

/-! ## Global selected witnesses -/

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- Exact W19 certificates expose precisely the selected W12 witnesses needed
by the W24 Euclidean selected-witness surface. -/
def selectedW12WitnessFields_of_exactCertificate
    (H : ExactAngleContainmentCertificate good turn) :
    SelectedW12WitnessFields good turn where
  figure8 := H.figure8.witnesses
  figure9_left := H.figure9.witnesses

/-- Existing combined angle-containment bridges expose the same selected W12
witnesses through their W19 exact certificate. -/
def selectedW12WitnessFields_of_angleContainmentBridges
    (A : AngleContainmentBridges good turn) :
    SelectedW12WitnessFields good turn :=
  selectedW12WitnessFields_of_exactCertificate
    (ExactAngleContainmentCertificate.ofAngleContainmentBridges A)

/-- Selected W12 witnesses construct the W24 selected Euclidean witness
surface.  The Euclidean angle lower bounds are rebuilt from the selected
distance packages already present in the W12 witnesses. -/
def selectedEuclideanWitnessFields_of_selectedW12WitnessFields
    (W : SelectedW12WitnessFields good turn) :
    SelectedEuclideanWitnessFields good turn :=
  W.toSelectedFigureEuclideanWitnessFields

/-- Exact W19 certificates construct the W24 selected Euclidean witness
surface without adding any additional hypotheses. -/
def selectedEuclideanWitnessFields_of_exactCertificate
    (H : ExactAngleContainmentCertificate good turn) :
    SelectedEuclideanWitnessFields good turn :=
  selectedFields_of_exactAngleContainmentCertificate H

/-- Existing combined angle-containment bridges construct the W24 selected
Euclidean witness surface. -/
def selectedEuclideanWitnessFields_of_angleContainmentBridges
    (A : AngleContainmentBridges good turn) :
    SelectedEuclideanWitnessFields good turn :=
  selectedFields_of_angleContainmentBridges A

/-- W23 exact inequalities plus selected W12 witnesses construct the W24
selected Euclidean witness surface. -/
def selectedEuclideanWitnessFields_of_exactInequalities
    (H : ExactFigureAngleInequalities good turn)
    (W : SelectedW12WitnessFields good turn) :
    SelectedEuclideanWitnessFields good turn :=
  selectedFields_of_exactFigureAngleInequalities
    H W.figure8 W.figure9_left

/-- Selected W12 witnesses already prove the paired E22/E23 turn-window
lower bounds through the concrete Euclidean files. -/
theorem E22_E23_of_selectedW12WitnessFields
    (W : SelectedW12WitnessFields good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  W.E22_E23

/-- Exact W19 certificates prove the paired E22/E23 turn-window lower bounds
through the selected Euclidean witness route. -/
theorem E22_E23_of_exactCertificate
    (H : ExactAngleContainmentCertificate good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (selectedEuclideanWitnessFields_of_exactCertificate H).E22_E23

/-- Existing combined angle-containment bridges prove the paired E22/E23
turn-window lower bounds through W23/W24 selected witnesses. -/
theorem E22_E23_of_angleContainmentBridges
    (A : AngleContainmentBridges good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (selectedEuclideanWitnessFields_of_angleContainmentBridges A).E22_E23

/-- W23 exact inequalities plus selected W12 witnesses prove E22/E23. -/
theorem E22_E23_of_exactInequalities
    (H : ExactFigureAngleInequalities good turn)
    (W : SelectedW12WitnessFields good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (selectedEuclideanWitnessFields_of_exactInequalities H W).E22_E23

/-- Pointwise E22 extracted from selected W12 witnesses. -/
theorem E22_of_selectedW12WitnessFields
    (W : SelectedW12WitnessFields good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  (E22_E23_of_selectedW12WitnessFields W).1

/-- Pointwise E23 extracted from selected W12 witnesses. -/
theorem E23_of_selectedW12WitnessFields
    (W : SelectedW12WitnessFields good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  (E22_E23_of_selectedW12WitnessFields W).2

/-! ## Local W22 rows -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- A W22 local exact-data row exposes the selected W12 witness fields. -/
def localSelectedW12WitnessFields_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    SelectedW12WitnessFields
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn where
  figure8 := D.figure8Witnesses
  figure9_left := D.figure9Witnesses

/-- A W22 local exact-data row constructs the W24 selected Euclidean witness
fields. -/
def localSelectedEuclideanWitnessFields_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    LocalSelectedFigureEuclideanWitnessFields localLabels turnBounds :=
  localSelectedFields_of_localExactData D

/-- A W22 local exact-data row proves the local E22/E23 obligations. -/
theorem local_E22_E23_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (localSelectedEuclideanWitnessFields_of_localExactAngleData D).E22_E23

/-- A W22 local exact-data row proves the local E22 obligation. -/
theorem local_E22_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn :=
  (local_E22_E23_of_localExactAngleData D).1

/-- A W22 local exact-data row proves the local E23 obligation. -/
theorem local_E23_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (local_E22_E23_of_localExactAngleData D).2

/-- Local W23 exact inequalities plus selected W12 witnesses construct the
W24 selected Euclidean witness fields. -/
def localSelectedEuclideanWitnessFields_of_w12AndInequalities
    (W :
      SelectedW12WitnessFields
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    LocalSelectedFigureEuclideanWitnessFields localLabels turnBounds :=
  localSelectedFields_of_w12WitnessesAndInequalities
    W.figure8 W.figure9_left H

/-- Local W23 exact inequalities plus selected W12 witnesses prove the local
E22/E23 obligations. -/
theorem local_E22_E23_of_w12AndInequalities
    (W :
      SelectedW12WitnessFields
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (localSelectedEuclideanWitnessFields_of_w12AndInequalities W H).E22_E23

/-! ## Family rows -/

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

/-- A W22 exact-data family constructs the W25 selected Euclidean witness
family. -/
def selectedEuclideanWitnessFamily_of_localExactAngleDataFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  LocalSelectedFigureEuclideanWitnessFieldsFamily.ofLocalExactAngleDataFamily
    F

/-- A W20 exact certificate family constructs the W25 selected Euclidean
witness family. -/
def selectedEuclideanWitnessFamily_of_exactSourceFamily
    (F :
      FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
        payForCut topologyArc lemma8) :
    LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  LocalSelectedFigureEuclideanWitnessFieldsFamily.ofBaseExactAngleContainmentCertificateFamily
    F

/-- A W20 bridge-source family constructs the W25 selected Euclidean witness
family. -/
def selectedEuclideanWitnessFamily_of_bridgeSourceFamily
    (F :
      FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8) :
    LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  LocalSelectedFigureEuclideanWitnessFieldsFamily.ofBaseAngleContainmentBridgeProducerFamily
    F

/-- A selected Euclidean witness family proves E22/E23 in every local row. -/
theorem row_E22_E23_of_selectedEuclideanWitnessFamily
    (F :
      LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  F.row_E22_E23 C hmin

/-- A W22 exact-data family proves E22/E23 in every local row. -/
theorem row_E22_E23_of_localExactAngleDataFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  row_E22_E23_of_selectedEuclideanWitnessFamily
    (selectedEuclideanWitnessFamily_of_localExactAngleDataFamily F) C hmin

/-- A W20 exact certificate family proves E22/E23 in every local row. -/
theorem row_E22_E23_of_exactSourceFamily
    (F :
      FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
        payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  row_E22_E23_of_selectedEuclideanWitnessFamily
    (selectedEuclideanWitnessFamily_of_exactSourceFamily F) C hmin

/-- A W20 bridge-source family proves E22/E23 in every local row. -/
theorem row_E22_E23_of_bridgeSourceFamily
    (F :
      FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  row_E22_E23_of_selectedEuclideanWitnessFamily
    (selectedEuclideanWitnessFamily_of_bridgeSourceFamily F) C hmin

end FigureWitnessConstructionW26
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW26SelectedW12WitnessFields :=
  Swanepoel.FigureWitnessConstructionW26.SelectedW12WitnessFields

abbrev SwanepoelW26SelectedEuclideanWitnessFields :=
  Swanepoel.FigureWitnessConstructionW26.SelectedEuclideanWitnessFields

theorem swanepoelW26_E22_E23_of_selectedW12WitnessFields
    {good : Nat -> Prop} {turn : Nat -> Real}
    (W : SwanepoelW26SelectedW12WitnessFields good turn) :
    Swanepoel.Lemma10AnalyticBridge.Figure8SeparatedWindowLowerE22
        good turn /\
      Swanepoel.Lemma10AnalyticBridge.Figure9AdjacentWindowLowerE23
        good turn :=
  Swanepoel.FigureWitnessConstructionW26.E22_E23_of_selectedW12WitnessFields
    W

theorem swanepoelW26_E22_E23_of_exactCertificate
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H :
      Swanepoel.AngleContainmentBridgeProducerW19.ExactAngleContainmentCertificate
        good turn) :
    Swanepoel.Lemma10AnalyticBridge.Figure8SeparatedWindowLowerE22
        good turn /\
      Swanepoel.Lemma10AnalyticBridge.Figure9AdjacentWindowLowerE23
        good turn :=
  Swanepoel.FigureWitnessConstructionW26.E22_E23_of_exactCertificate H

theorem swanepoelW26_row_E22_E23_of_localExactAngleDataFamily
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F :
      Swanepoel.FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
        payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : Swanepoel.MinimalGraphFacts.IsMinimalClearedFailure C) :
    Swanepoel.Lemma10AnalyticBridge.HonestFigure8SeparatedWindowLowerE22
        (Swanepoel.FigureAngleSourceInhabitationW21.BaseInputs
          payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (Swanepoel.FigureAngleSourceInhabitationW21.BaseInputs
          payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      Swanepoel.Lemma10AnalyticBridge.HonestFigure9AdjacentWindowLowerE23
        (Swanepoel.FigureAngleSourceInhabitationW21.BaseInputs
          payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (Swanepoel.FigureAngleSourceInhabitationW21.BaseInputs
          payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  Swanepoel.FigureWitnessConstructionW26.row_E22_E23_of_localExactAngleDataFamily
    F C hmin

end Verified
end ErdosProblems1066

end
