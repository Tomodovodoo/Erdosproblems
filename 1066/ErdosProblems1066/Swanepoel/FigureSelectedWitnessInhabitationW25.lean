import ErdosProblems1066.Swanepoel.FigureAngleInequalitiesW24

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W25 selected Figure witness inhabitation

This file exposes the inhabitance surface for
`FigureAngleInequalitiesW24.SelectedFigureEuclideanWitnessFields`.

The selected Euclidean witness package is equivalent, for inhabitance
purposes, to the W12 selected Figure 8/Figure 9 witnesses.  The concrete
Figure 8/Figure 9 Euclidean files rebuild the metric angle lower bounds from
those W12 distance packages, while the W23/W19 exact angle-containment
interfaces supply the remaining turn-window containments.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureSelectedWitnessInhabitationW25

open AngleContainmentBridgeProducerW19
open AngleContainmentInterface
open FigureAngleContainmentConcreteW23
open FigureAngleInequalitiesW24
open FigureAngleSourceInhabitationW21
open FigureExactAngleCertificateInhabitationW22
open Lemma10AnalyticBridge
open Lemma10Bridge
open M8ConstructionInterface
open MinimalGraphFacts

universe u

/-! ## W12 witness surface -/

/-- The W12 selected Figure witnesses that are exactly needed to inhabit the
W24 selected Euclidean witness fields. -/
structure SelectedFigureW12WitnessFields
    (good : Nat -> Prop) (turn : Nat -> Real) : Type where
  figure8 :
    Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn
  figure9_left :
    Figure9ContainmentW12.AdjacentWindowWitnesses good turn

namespace SelectedFigureW12WitnessFields

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- W12 selected witnesses produce the W24 selected Euclidean witness fields. -/
def toSelectedFigureEuclideanWitnessFields
    (W : SelectedFigureW12WitnessFields good turn) :
    SelectedFigureEuclideanWitnessFields good turn :=
  selectedFields_of_w12Witnesses W.figure8 W.figure9_left

/-- W12 selected witnesses already imply the paired E22/E23 lower bounds
through the W24 selected Euclidean witness route. -/
theorem E22_E23
    (W : SelectedFigureW12WitnessFields good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  W.toSelectedFigureEuclideanWitnessFields.E22_E23

/-- W12 selected witnesses imply E22. -/
theorem E22
    (W : SelectedFigureW12WitnessFields good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  W.E22_E23.1

/-- W12 selected witnesses imply E23. -/
theorem E23
    (W : SelectedFigureW12WitnessFields good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  W.E22_E23.2

end SelectedFigureW12WitnessFields

namespace SelectedFigureEuclideanWitnessFields

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- Forget W24 selected Euclidean witness fields back to the selected W12
witnesses. -/
def toSelectedFigureW12WitnessFields
    (H : SelectedFigureEuclideanWitnessFields good turn) :
    SelectedFigureW12WitnessFields good turn where
  figure8 := H.figure8W12Witnesses
  figure9_left := H.figure9W12Witnesses

end SelectedFigureEuclideanWitnessFields

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- W12 witnesses inhabit the selected Euclidean witness surface. -/
theorem selectedFigureEuclideanWitnessFields_nonempty_of_w12WitnessFields
    (W : SelectedFigureW12WitnessFields good turn) :
    Nonempty (SelectedFigureEuclideanWitnessFields good turn) :=
  Nonempty.intro W.toSelectedFigureEuclideanWitnessFields

/-- Selected Euclidean witness fields and W12 selected witnesses have the
same inhabitance content. -/
theorem selectedFigureEuclideanWitnessFields_nonempty_iff_w12WitnessFields :
    Nonempty (SelectedFigureEuclideanWitnessFields good turn) <->
      Nonempty (SelectedFigureW12WitnessFields good turn) := by
  constructor
  · intro h
    cases h with
    | intro H =>
        exact Nonempty.intro
          (SelectedFigureEuclideanWitnessFields.toSelectedFigureW12WitnessFields
            H)
  · intro h
    cases h with
    | intro W =>
        exact selectedFigureEuclideanWitnessFields_nonempty_of_w12WitnessFields W

/-- Nonempty selected Euclidean witness fields imply E22/E23. -/
theorem E22_E23_of_selectedFigureEuclideanWitnessFields_nonempty
    (h : Nonempty (SelectedFigureEuclideanWitnessFields good turn)) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn := by
  cases h with
  | intro H =>
      exact H.E22_E23

/-- Nonempty selected W12 witness fields imply E22/E23 through the selected
Euclidean witness route. -/
theorem E22_E23_of_w12WitnessFields_nonempty
    (h : Nonempty (SelectedFigureW12WitnessFields good turn)) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn := by
  cases h with
  | intro W =>
      exact W.E22_E23

/-! ## Constructors from exact angle-containment data -/

/-- A W19 exact angle-containment certificate directly inhabits the selected
Euclidean witness fields by combining its W12 selected witnesses with its
exact containment inequalities. -/
def selectedFields_of_exactAngleContainmentCertificate
    (H : ExactAngleContainmentCertificate good turn) :
    SelectedFigureEuclideanWitnessFields good turn :=
  selectedFields_of_exactFigureAngleInequalities
    { figure8 := H.figure8.central_angle_le_separatedTurn
      figure9_left := H.figure9.left_angle_le_adjacentTurn }
    H.figure8.witnesses
    H.figure9.witnesses

/-- A W19 exact angle-containment certificate inhabits the selected Euclidean
witness surface. -/
theorem selectedFigureEuclideanWitnessFields_nonempty_of_exactAngleContainmentCertificate
    (H : ExactAngleContainmentCertificate good turn) :
    Nonempty (SelectedFigureEuclideanWitnessFields good turn) :=
  Nonempty.intro (selectedFields_of_exactAngleContainmentCertificate H)

/-- A combined angle-containment bridge inhabits the selected Euclidean
witness surface. -/
theorem selectedFigureEuclideanWitnessFields_nonempty_of_angleContainmentBridges
    (A : AngleContainmentBridges good turn) :
    Nonempty (SelectedFigureEuclideanWitnessFields good turn) :=
  Nonempty.intro (selectedFields_of_angleContainmentBridges A)

/-- W23 exact Figure inequalities plus selected W12 witnesses inhabit the
selected Euclidean witness surface. -/
theorem selectedFigureEuclideanWitnessFields_nonempty_of_exactFigureAngleInequalities
    (H : ExactFigureAngleInequalities good turn)
    (W : SelectedFigureW12WitnessFields good turn) :
    Nonempty (SelectedFigureEuclideanWitnessFields good turn) :=
  Nonempty.intro
    (selectedFields_of_exactFigureAngleInequalities
      H W.figure8 W.figure9_left)

/-- A W19 exact certificate gives E22/E23 through the selected Euclidean
witness route. -/
theorem E22_E23_of_exactAngleContainmentCertificate
    (H : ExactAngleContainmentCertificate good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (selectedFields_of_exactAngleContainmentCertificate H).E22_E23

/-- A combined angle-containment bridge gives E22/E23 through the selected
Euclidean witness route. -/
theorem E22_E23_of_angleContainmentBridges
    (A : AngleContainmentBridges good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (selectedFields_of_angleContainmentBridges A).E22_E23

/-! ## Local and family-level inhabitation -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- Local W12 selected witness fields. -/
abbrev LocalSelectedFigureW12WitnessFields
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  SelectedFigureW12WitnessFields
    (M8BrokenLatticeGood localLabels.predicates.data)
    turnBounds.turn

/-- Local exact W12/containment data inhabits the local selected Euclidean
witness fields. -/
theorem localSelectedFigureEuclideanWitnessFields_nonempty_of_localExactData
    (D : LocalExactAngleData localLabels turnBounds) :
    Nonempty
      (LocalSelectedFigureEuclideanWitnessFields localLabels turnBounds) :=
  Nonempty.intro (localSelectedFields_of_localExactData D)

/-- Local exact W12/containment data gives the paired local E22/E23 fields
through the selected Euclidean witness route. -/
theorem local_E22_E23_of_localExactData
    (D : LocalExactAngleData localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (localSelectedFields_of_localExactData D).E22_E23

/-- A family of selected Euclidean witness fields over the W21 Figure base
rows. -/
structure LocalSelectedFigureEuclideanWitnessFieldsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        LocalSelectedFigureEuclideanWitnessFields
          (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

namespace LocalSelectedFigureEuclideanWitnessFieldsFamily

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

/-- A W22 local exact-data family inhabits the selected Euclidean witness
family. -/
def ofLocalExactAngleDataFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localSelectedFields_of_localExactData (F.row C hmin)

/-- An exact W20 source family inhabits the selected Euclidean witness
family. -/
def ofBaseExactAngleContainmentCertificateFamily
    (F :
      FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
        payForCut topologyArc lemma8) :
    LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    selectedFields_of_exactAngleContainmentCertificate
      (F.certificate C hmin)

/-- A W20 bridge-source family inhabits the selected Euclidean witness
family. -/
def ofBaseAngleContainmentBridgeProducerFamily
    (F :
      FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8) :
    LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    selectedFields_of_angleContainmentBridges
      (F.row C hmin).angleContainment

/-- Each selected row gives the paired E22/E23 fields. -/
theorem row_E22_E23
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
  (F.row C hmin).E22_E23

end LocalSelectedFigureEuclideanWitnessFieldsFamily

/-- Nonempty W22 local exact-data families are enough to inhabit the selected
Euclidean witness family. -/
theorem selectedFigureEuclideanWitnessFieldsFamily_nonempty_of_localExactAngleDataFamily
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (h : Nonempty
      (LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8)) :
    Nonempty
      (LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | intro F =>
      exact Nonempty.intro
        (LocalSelectedFigureEuclideanWitnessFieldsFamily.ofLocalExactAngleDataFamily
          F)

/-- Nonempty W20 exact source families are enough to inhabit the selected
Euclidean witness family. -/
theorem selectedFigureEuclideanWitnessFieldsFamily_nonempty_of_exactSourceFamily
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (h : Nonempty
      (FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
        payForCut topologyArc lemma8)) :
    Nonempty
      (LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | intro F =>
      exact Nonempty.intro
        (LocalSelectedFigureEuclideanWitnessFieldsFamily.ofBaseExactAngleContainmentCertificateFamily
          F)

/-- Nonempty W20 bridge-source families are enough to inhabit the selected
Euclidean witness family. -/
theorem selectedFigureEuclideanWitnessFieldsFamily_nonempty_of_bridgeSourceFamily
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (h : Nonempty
      (FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8)) :
    Nonempty
      (LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | intro F =>
      exact Nonempty.intro
        (LocalSelectedFigureEuclideanWitnessFieldsFamily.ofBaseAngleContainmentBridgeProducerFamily
          F)

end FigureSelectedWitnessInhabitationW25
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW25SelectedFigureW12WitnessFields :=
  Swanepoel.FigureSelectedWitnessInhabitationW25.SelectedFigureW12WitnessFields

abbrev SwanepoelW25LocalSelectedFigureEuclideanWitnessFieldsFamily :=
  Swanepoel.FigureSelectedWitnessInhabitationW25.LocalSelectedFigureEuclideanWitnessFieldsFamily

theorem swanepoelW25_selectedFigureEuclideanWitnessFields_nonempty_iff_w12WitnessFields
    {good : Nat -> Prop} {turn : Nat -> Real} :
    Nonempty
        (Swanepoel.FigureAngleInequalitiesW24.SelectedFigureEuclideanWitnessFields
          good turn) <->
      Nonempty (SwanepoelW25SelectedFigureW12WitnessFields good turn) :=
  Swanepoel.FigureSelectedWitnessInhabitationW25.selectedFigureEuclideanWitnessFields_nonempty_iff_w12WitnessFields

theorem swanepoelW25_E22_E23_of_selectedFigureEuclideanWitnessFields_nonempty
    {good : Nat -> Prop} {turn : Nat -> Real}
    (h :
      Nonempty
        (Swanepoel.FigureAngleInequalitiesW24.SelectedFigureEuclideanWitnessFields
          good turn)) :
    Swanepoel.Lemma10AnalyticBridge.Figure8SeparatedWindowLowerE22
        good turn /\
      Swanepoel.Lemma10AnalyticBridge.Figure9AdjacentWindowLowerE23
        good turn :=
  Swanepoel.FigureSelectedWitnessInhabitationW25.E22_E23_of_selectedFigureEuclideanWitnessFields_nonempty
    h

theorem swanepoelW25_selectedFigureEuclideanWitnessFieldsFamily_nonempty_of_localExactAngleDataFamily
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (h :
      Nonempty
        (Swanepoel.FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (SwanepoelW25LocalSelectedFigureEuclideanWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.FigureSelectedWitnessInhabitationW25.selectedFigureEuclideanWitnessFieldsFamily_nonempty_of_localExactAngleDataFamily
    h

end Verified
end ErdosProblems1066

end
