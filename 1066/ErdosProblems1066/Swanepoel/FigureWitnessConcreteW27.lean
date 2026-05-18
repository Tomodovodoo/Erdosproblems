import ErdosProblems1066.Swanepoel.FigureWitnessConstructionW26

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W27 concrete Figure witness worker

This file exposes the actual selected Figure 8/Figure 9 witness fields used by
`FigureWitnessConstructionW26`.  The constructors start from local exact angle
data or from containment packages, then build the selected W12 witnesses and
the selected Euclidean witness fields.  The E22/E23 projections at the bottom
therefore pass through concrete witness data instead of assuming E22/E23
directly.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureWitnessConcreteW27

open AngleContainmentInterface
open AngleContainmentBridgeProducerW19
open FigureAngleContainmentConcreteW23
open FigureAngleInequalitiesW24
open FigureExactAngleCertificateInhabitationW22
open FigureSelectedWitnessInhabitationW25
open FigureWitnessConstructionW26
open FigureAngleSourceInhabitationW21
open Lemma10AnalyticBridge
open Lemma10Bridge
open M8ConstructionInterface
open M8WindowContainmentConcrete
open MinimalGraphFacts

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

abbrev LocalGood (localLabels : M8LocalLabels C) : Nat -> Prop :=
  Lemma10Bridge.M8BrokenLatticeGood localLabels.predicates.data

abbrev LocalSelectedW12WitnessFields
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  SelectedW12WitnessFields (LocalGood localLabels) turnBounds.turn

abbrev LocalSelectedEuclideanWitnessFields
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  SelectedEuclideanWitnessFields (LocalGood localLabels) turnBounds.turn

/-! ## Pointwise selected components from local exact data -/

/-- The selected Figure 8 W12 witnesses carried by local exact angle data. -/
def figure8W12Witnesses_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
      localLabels.predicates turnBounds.turn :=
  D.figure8Witnesses

/-- The selected Figure 9 W12 witnesses carried by local exact angle data. -/
def figure9W12Witnesses_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    Figure9ContainmentW12.HonestAdjacentWindowWitnesses
      localLabels.predicates turnBounds.turn :=
  D.figure9Witnesses

/-- The selected W12 Figure 8/Figure 9 fields carried by local exact angle
data, in the shape consumed by W26. -/
def selectedW12WitnessFields_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    LocalSelectedW12WitnessFields localLabels turnBounds :=
  localSelectedW12WitnessFields_of_localExactAngleData D

/-- The selected Figure 8 Euclidean witnesses built from local exact angle
data. -/
def figure8EuclideanWitnesses_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    Figure8EuclideanFactsConcrete.HonestFigure8SeparatedEuclideanFactWitnesses
      localLabels.predicates turnBounds.turn :=
  (localSelectedEuclideanWitnessFields_of_localExactAngleData D).figure8

/-- The selected Figure 9 Euclidean witnesses built from local exact angle
data. -/
def figure9EuclideanWitnesses_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    Figure9EuclideanFactsConcrete.HonestFigure9AdjacentLeftEuclideanFactWitnesses
      localLabels.predicates turnBounds.turn :=
  (localSelectedEuclideanWitnessFields_of_localExactAngleData D).figure9_left

/-- The selected Euclidean Figure 8/Figure 9 fields built from local exact
angle data, in the shape consumed by W26. -/
def selectedEuclideanWitnessFields_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    LocalSelectedEuclideanWitnessFields localLabels turnBounds :=
  localSelectedEuclideanWitnessFields_of_localExactAngleData D

/-! ## Combined selected witness package -/

/-- The concrete selected Figure witness fields for one local row.

The four component fields make the selected Figure 8/Figure 9 W12 and
Euclidean data explicit, while the two aggregate fields are the exact W26
interfaces consumed downstream. -/
structure LocalSelectedFigureWitnessFields
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  figure8W12 :
    Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
      localLabels.predicates turnBounds.turn
  figure9W12 :
    Figure9ContainmentW12.HonestAdjacentWindowWitnesses
      localLabels.predicates turnBounds.turn
  selectedW12 : LocalSelectedW12WitnessFields localLabels turnBounds
  figure8Euclidean :
    Figure8EuclideanFactsConcrete.HonestFigure8SeparatedEuclideanFactWitnesses
      localLabels.predicates turnBounds.turn
  figure9Euclidean :
    Figure9EuclideanFactsConcrete.HonestFigure9AdjacentLeftEuclideanFactWitnesses
      localLabels.predicates turnBounds.turn
  selectedEuclidean :
    LocalSelectedEuclideanWitnessFields localLabels turnBounds

namespace LocalSelectedFigureWitnessFields

variable {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}

/-- Rebuild the W26 selected Euclidean fields from the stored selected W12
fields. -/
def selectedEuclideanFromW12
    (H : LocalSelectedFigureWitnessFields localLabels turnBounds) :
    LocalSelectedEuclideanWitnessFields localLabels turnBounds :=
  selectedEuclideanWitnessFields_of_selectedW12WitnessFields H.selectedW12

/-- The stored selected W12 witnesses prove E22/E23 through W26's selected
Euclidean route. -/
theorem E22_E23_fromW12
    (H : LocalSelectedFigureWitnessFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  E22_E23_of_selectedW12WitnessFields H.selectedW12

/-- The stored selected Euclidean witnesses prove E22/E23 without assuming
either endpoint directly. -/
theorem E22_E23
    (H : LocalSelectedFigureWitnessFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  H.selectedEuclidean.E22_E23

/-- Figure 8/E22 projection from the selected Euclidean witness route. -/
theorem E22
    (H : LocalSelectedFigureWitnessFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn :=
  H.E22_E23.1

/-- Figure 9/E23 projection from the selected Euclidean witness route. -/
theorem E23
    (H : LocalSelectedFigureWitnessFields localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  H.E22_E23.2

end LocalSelectedFigureWitnessFields

/-! ## Constructors from exact data and containment packages -/

/-- Local exact angle data supplies the concrete selected W12 and Euclidean
witness fields. -/
def localSelectedFigureWitnessFields_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    LocalSelectedFigureWitnessFields localLabels turnBounds where
  figure8W12 := figure8W12Witnesses_of_localExactAngleData D
  figure9W12 := figure9W12Witnesses_of_localExactAngleData D
  selectedW12 := selectedW12WitnessFields_of_localExactAngleData D
  figure8Euclidean := figure8EuclideanWitnesses_of_localExactAngleData D
  figure9Euclidean := figure9EuclideanWitnesses_of_localExactAngleData D
  selectedEuclidean := selectedEuclideanWitnessFields_of_localExactAngleData D

/-- W12 witnesses plus local exact containment inequalities supply the same
concrete selected witness fields through local exact angle data. -/
def localSelectedFigureWitnessFields_of_w12AndInequalities
    (figure8 :
      Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
        localLabels.predicates turnBounds.turn)
    (figure9 :
      Figure9ContainmentW12.HonestAdjacentWindowWitnesses
        localLabels.predicates turnBounds.turn)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    LocalSelectedFigureWitnessFields localLabels turnBounds :=
  localSelectedFigureWitnessFields_of_localExactAngleData
    (localExactData_of_w12WitnessesAndInequalities figure8 figure9 H)

/-- A concrete local window-containment package supplies selected W12 and
Euclidean Figure witnesses by first extracting the local exact angle data. -/
def localSelectedFigureWitnessFields_of_localWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    LocalSelectedFigureWitnessFields localLabels turnBounds :=
  localSelectedFigureWitnessFields_of_localExactAngleData
    (LocalExactAngleData.ofLocalWindowContainmentFields W)

/-- A local exact W19 certificate supplies selected W12 and Euclidean Figure
witnesses through the local exact angle data projection. -/
def localSelectedFigureWitnessFields_of_localExactCertificate
    (H : LocalExactAngleContainmentCertificate localLabels turnBounds) :
    LocalSelectedFigureWitnessFields localLabels turnBounds :=
  localSelectedFigureWitnessFields_of_localExactAngleData
    (LocalExactAngleData.ofLocalExactCertificate H)

/-- A local angle-containment bridge package supplies selected W12 and
Euclidean Figure witnesses through the W23 local exact-data constructor. -/
def localSelectedFigureWitnessFields_of_angleContainmentBridges
    (A : AngleContainmentBridges (LocalGood localLabels) turnBounds.turn) :
    LocalSelectedFigureWitnessFields localLabels turnBounds :=
  localSelectedFigureWitnessFields_of_localExactAngleData
    (localExactData_of_angleContainmentBridges A)

/-! ## Selected component projections from containment packages -/

/-- Selected W12 fields obtained from a local window-containment package. -/
def selectedW12WitnessFields_of_localWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    LocalSelectedW12WitnessFields localLabels turnBounds :=
  (localSelectedFigureWitnessFields_of_localWindowContainmentFields W).selectedW12

/-- Selected Euclidean fields obtained from a local window-containment
package. -/
def selectedEuclideanWitnessFields_of_localWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    LocalSelectedEuclideanWitnessFields localLabels turnBounds :=
  (localSelectedFigureWitnessFields_of_localWindowContainmentFields
    W).selectedEuclidean

/-- Selected W12 fields obtained from local angle-containment bridges. -/
def selectedW12WitnessFields_of_angleContainmentBridges
    (A : AngleContainmentBridges (LocalGood localLabels) turnBounds.turn) :
    LocalSelectedW12WitnessFields localLabels turnBounds :=
  (localSelectedFigureWitnessFields_of_angleContainmentBridges A).selectedW12

/-- Selected Euclidean fields obtained from local angle-containment bridges. -/
def selectedEuclideanWitnessFields_of_angleContainmentBridges
    (A : AngleContainmentBridges (LocalGood localLabels) turnBounds.turn) :
    LocalSelectedEuclideanWitnessFields localLabels turnBounds :=
  (localSelectedFigureWitnessFields_of_angleContainmentBridges
    A).selectedEuclidean

/-! ## Consequences through the selected witness route -/

/-- Local exact angle data proves E22/E23 through actual selected Euclidean
witness fields. -/
theorem local_E22_E23_of_selectedFigureWitnessFields
    (D : LocalExactAngleData localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (localSelectedFigureWitnessFields_of_localExactAngleData D).E22_E23

/-- A local window-containment package proves E22/E23 through extracted
selected W12 and Euclidean Figure witnesses. -/
theorem local_E22_E23_of_localWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (localSelectedFigureWitnessFields_of_localWindowContainmentFields W).E22_E23

/-- A local angle-containment bridge package proves E22/E23 through extracted
selected W12 and Euclidean Figure witnesses. -/
theorem local_E22_E23_of_angleContainmentBridges
    (A : AngleContainmentBridges (LocalGood localLabels) turnBounds.turn) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (localSelectedFigureWitnessFields_of_angleContainmentBridges A).E22_E23

/-! ## Family rows -/

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

/-- A family of concrete selected Figure witness rows over the W21 base
inputs. -/
structure LocalSelectedFigureWitnessFieldsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        LocalSelectedFigureWitnessFields
          (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

namespace LocalSelectedFigureWitnessFieldsFamily

/-- Build the selected witness family from a W22 local exact-angle data
family. -/
def ofLocalExactAngleDataFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localSelectedFigureWitnessFields_of_localExactAngleData
      (F.row C hmin)

/-- Build the selected witness family from concrete local window-containment
fields. -/
def ofLocalWindowContainmentFieldsFamily
    (W : LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localSelectedFigureWitnessFields_of_localWindowContainmentFields
      (W C hmin)

/-- Each selected witness row supplies the W26 selected W12 interface. -/
def selectedW12Family
    (F : LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        LocalSelectedW12WitnessFields
          (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds :=
  fun C hmin => (F.row C hmin).selectedW12

/-- Each selected witness row supplies the W26 selected Euclidean interface. -/
def selectedEuclideanFamily
    (F : LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        LocalSelectedEuclideanWitnessFields
          (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds :=
  fun C hmin => (F.row C hmin).selectedEuclidean

/-- Each selected witness row proves the local E22/E23 obligations through
its selected Euclidean fields. -/
theorem row_E22_E23
    (F : LocalSelectedFigureWitnessFieldsFamily.{u}
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

end LocalSelectedFigureWitnessFieldsFamily

/-- W22 local exact-angle data families produce concrete selected witness
families. -/
def selectedFigureWitnessFamily_of_localExactAngleDataFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  LocalSelectedFigureWitnessFieldsFamily.ofLocalExactAngleDataFamily F

/-- Concrete local window-containment field families produce concrete
selected witness families. -/
def selectedFigureWitnessFamily_of_localWindowContainmentFieldsFamily
    (W : LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  LocalSelectedFigureWitnessFieldsFamily.ofLocalWindowContainmentFieldsFamily W

/-- Family-level E22/E23 projection through the selected witness fields. -/
theorem row_E22_E23_of_selectedFigureWitnessFamily
    (F : LocalSelectedFigureWitnessFieldsFamily.{u}
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

/-- W22 local exact-angle data families prove E22/E23 through selected
Figure witness fields. -/
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
  row_E22_E23_of_selectedFigureWitnessFamily
    (selectedFigureWitnessFamily_of_localExactAngleDataFamily F) C hmin

/-- Concrete local window-containment field families prove E22/E23 through
selected Figure witness fields. -/
theorem row_E22_E23_of_localWindowContainmentFieldsFamily
    (W : LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  row_E22_E23_of_selectedFigureWitnessFamily
    (selectedFigureWitnessFamily_of_localWindowContainmentFieldsFamily W)
    C hmin

end FigureWitnessConcreteW27
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW27LocalSelectedFigureWitnessFields
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : Swanepoel.M8ConstructionInterface.M8LocalLabels C)
    (turnBounds : Swanepoel.M8ConstructionInterface.M8TurnBounds) :=
  Swanepoel.FigureWitnessConcreteW27.LocalSelectedFigureWitnessFields
    localLabels turnBounds

abbrev SwanepoelW27LocalSelectedFigureWitnessFieldsFamily :=
  Swanepoel.FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily

theorem swanepoelW27_row_E22_E23_of_localExactAngleDataFamily
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
  Swanepoel.FigureWitnessConcreteW27.row_E22_E23_of_localExactAngleDataFamily
    F C hmin

theorem swanepoelW27_row_E22_E23_of_localWindowContainmentFieldsFamily
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (W :
      Swanepoel.FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
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
  Swanepoel.FigureWitnessConcreteW27.row_E22_E23_of_localWindowContainmentFieldsFamily
    W C hmin

end Verified
end ErdosProblems1066

end
