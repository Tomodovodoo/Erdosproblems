import ErdosProblems1066.Swanepoel.FigureAngleSourceInhabitationW21
import ErdosProblems1066.Swanepoel.Figure8ContainmentConcrete
import ErdosProblems1066.Swanepoel.Figure9ContainmentConcrete
import ErdosProblems1066.Swanepoel.Figure8EuclideanFactsConcrete
import ErdosProblems1066.Swanepoel.Figure9EuclideanFactsConcrete

/-!
# W22 exact Figure angle-certificate inhabitation

This file packages the precise W12/W19 data needed to inhabit the W21 local
exact certificate family.  The local constructor keeps both ingredients
visible: selected Figure 8/Figure 9 W12 witnesses and the universal exact
angle-containment inequalities required by W19.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureExactAngleCertificateInhabitationW22

open AngleContainmentBridgeProducerW19
open FigureAngleSourceInhabitationW21
open FigureWitnessClosureW19
open Lemma10Bridge
open M8ConstructionInterface
open M8WindowContainmentConcrete
open MinimalGraphFacts

universe u

/-! ## Local exact data -/

/-- Local W12 Figure witnesses together with the exact universal angle
containment inequalities required by W19. -/
structure LocalExactAngleData {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  figure8Witnesses :
    Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
      localLabels.predicates turnBounds.turn
  figure8AngleContainment :
    Figure8UniversalAngleContainment
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn
  figure9Witnesses :
    Figure9ContainmentW12.HonestAdjacentWindowWitnesses
      localLabels.predicates turnBounds.turn
  figure9AngleContainment :
    Figure9UniversalLeftAngleContainment
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn

namespace LocalExactAngleData

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}

/-- Build the W19 exact local certificate from the W12 witnesses and exact
angle-containment inequalities. -/
def toLocalExactCertificate
    (D : LocalExactAngleData localLabels turnBounds) :
    LocalExactAngleContainmentCertificate localLabels turnBounds :=
  FigureAngleSourceInhabitationW21.localExactCertificate_of_w12Data
    D.figure8Witnesses D.figure8AngleContainment
    D.figure9Witnesses D.figure9AngleContainment

/-- The same local data in the W19 bridge-input shape consumed by Figure
witness closure. -/
def toLocalBridgeInput
    (D : LocalExactAngleData localLabels turnBounds) :
    LocalAngleContainmentBridgeProducerInput localLabels turnBounds :=
  FigureAngleSourceInhabitationW21.localBridgeInput_of_w12Data
    D.figure8Witnesses D.figure8AngleContainment
    D.figure9Witnesses D.figure9AngleContainment

/-- Extract the W12/exact data from an already-built W19 local certificate. -/
def ofLocalExactCertificate
    (H : LocalExactAngleContainmentCertificate localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds where
  figure8Witnesses := H.figure8.witnesses
  figure8AngleContainment := H.figure8.central_angle_le_separatedTurn
  figure9Witnesses := H.figure9.witnesses
  figure9AngleContainment := H.figure9.left_angle_le_adjacentTurn

/-- Concrete M8 local window-containment fields supply both selected W12
witnesses and the exact universal angle inequalities. -/
def ofLocalWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds where
  figure8Witnesses :=
    Figure8ContainmentW12.dataWitnesses_of_localWindowContainmentFields W
  figure8AngleContainment := by
    intro i j p qi qj s r hi hsep hj hbad_i hbad_j Hdist
    exact
      M8LocalWindowContainmentFields.figure8_central_angle_le_separatedTurn
        W hi hsep hj hbad_i hbad_j Hdist
  figure9Witnesses :=
    Figure9ContainmentW12.witnesses_of_containmentInterface W.figure9_left
  figure9AngleContainment := by
    intro i p qi qj s r hi hi_next hbad_i hbad_next Hdist
    exact
      M8LocalWindowContainmentFields.figure9_left_angle_le_adjacentTurn
        W hi hi_next hbad_i hbad_next Hdist

/-- Local exact certificate built directly from concrete local window fields. -/
def localExactCertificate_of_localWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    LocalExactAngleContainmentCertificate localLabels turnBounds :=
  (ofLocalWindowContainmentFields W).toLocalExactCertificate

/-- Local bridge input built directly from concrete local window fields. -/
def localBridgeInput_of_localWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    LocalAngleContainmentBridgeProducerInput localLabels turnBounds :=
  (ofLocalWindowContainmentFields W).toLocalBridgeInput

/-- The W12 data exposes the paired E22/E23 containment lower bounds. -/
theorem E22_E23
    (D : LocalExactAngleData localLabels turnBounds) :
    Lemma10AnalyticBridge.HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      Lemma10AnalyticBridge.HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  FigureWitnessClosureW19.LocalAngleContainmentBridgeProducerInput.E22_E23
    D.toLocalBridgeInput

/-- Pointwise Figure 8 exact angle containment projected from local data. -/
theorem figure8_central_angle_le_separatedTurn
    (D : LocalExactAngleData localLabels turnBounds)
    {i j : Nat} {p qi qj s r : AngleGeometry.Point}
    (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j))
    (Hdist : AngleBridgeFacts.Figure8DistanceData p qi qj s r) :
    AngleGeometry.angleAt qi p qj <=
      Lemma10Inequalities.separatedTurn turnBounds.turn i j :=
  D.figure8AngleContainment hi hsep hj hbad_i hbad_j Hdist

/-- Pointwise Figure 9 exact left-angle containment projected from local
data. -/
theorem figure9_left_angle_le_adjacentTurn
    (D : LocalExactAngleData localLabels turnBounds)
    {i : Nat} {p qi qj s r : AngleGeometry.Point}
    (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1)))
    (Hdist : AngleBridgeFacts.Figure9DistanceData p qi qj s r) :
    AngleGeometry.angleAt p qi s <=
      Lemma10Inequalities.adjacentTurn turnBounds.turn i :=
  D.figure9AngleContainment hi hi_next hbad_i hbad_next Hdist

end LocalExactAngleData

/-! ## Family-level constructors for W21 -/

/-- A family of concrete local window-containment fields over the W21 base
rows. -/
abbrev LocalWindowContainmentFieldsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      M8LocalWindowContainmentFields
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

/-- Family-level W12/exact data over the W21 base rows. -/
structure LocalExactAngleDataFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        LocalExactAngleData
          (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

namespace LocalExactAngleDataFamily

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

/-- Convert a family of W12/exact rows to the W21 local exact certificate
family. -/
def toLocalExactCertificateFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    LocalExactCertificateFamily.{u} payForCut topologyArc lemma8 :=
  fun {n} C hmin =>
    (F.row (n := n) C hmin).toLocalExactCertificate

/-- Convert a family of W12/exact rows to the W20 exact source family. -/
def toExactSourceFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
      payForCut topologyArc lemma8 :=
  FigureAngleSourceInhabitationW21.exactSourceFamilyOfLocalCertificates
    F.toLocalExactCertificateFamily

/-- Convert a family of W12/exact rows to W19 local bridge inputs. -/
def toLocalBridgeInputFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    LocalBridgeInputFamily.{u} payForCut topologyArc lemma8 :=
  fun {n} C hmin =>
    (F.row (n := n) C hmin).toLocalBridgeInput

/-- Convert a family of W12/exact rows to the W20 bridge source family. -/
def toBridgeSourceFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
      payForCut topologyArc lemma8 :=
  FigureAngleSourceInhabitationW21.bridgeSourceFamilyOfLocalBridgeInputs
    F.toLocalBridgeInputFamily

/-- W12/exact rows produce the W18 Figure witness concrete producer family. -/
def toFigureWitnessConcreteProducerFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    FigureWitnessConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 :=
  F.toExactSourceFamily.toFigureWitnessConcreteProducerFamily

/-- Concrete local window-containment fields inhabit the W12/exact data
family. -/
def ofLocalWindowContainmentFieldsFamily
    (W : LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin =>
    LocalExactAngleData.ofLocalWindowContainmentFields (W C hmin)

/-- Concrete local window-containment fields inhabit the W21 local exact
certificate family. -/
def localExactCertificateFamily_of_localWindowContainmentFieldsFamily
    (W : LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactCertificateFamily.{u} payForCut topologyArc lemma8 :=
  (ofLocalWindowContainmentFieldsFamily W).toLocalExactCertificateFamily

/-- Concrete local window-containment fields inhabit the W20 exact source
family. -/
def exactSourceFamily_of_localWindowContainmentFieldsFamily
    (W : LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
      payForCut topologyArc lemma8 :=
  (ofLocalWindowContainmentFieldsFamily W).toExactSourceFamily

/-- Nonempty W12/exact data rows are enough to inhabit the W21 local exact
certificate family. -/
theorem localExactCertificateFamily_nonempty
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    Nonempty
      (LocalExactCertificateFamily.{u} payForCut topologyArc lemma8) :=
  Nonempty.intro F.toLocalExactCertificateFamily

/-- Nonempty concrete local window-containment rows are enough to inhabit the
W21 local exact certificate family. -/
theorem localExactCertificateFamily_nonempty_of_localWindowContainmentFieldsFamily
    (W : LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (LocalExactCertificateFamily.{u} payForCut topologyArc lemma8) :=
  Nonempty.intro
    (localExactCertificateFamily_of_localWindowContainmentFieldsFamily W)

/-- The inhabited local exact certificate family gives the W18 Figure witness
producer family through the W21/W20 route. -/
theorem figureWitnessConcreteProducerFamily_nonempty
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    Nonempty
      (FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro F.toFigureWitnessConcreteProducerFamily

end LocalExactAngleDataFamily

end FigureExactAngleCertificateInhabitationW22

namespace Verified

universe u

abbrev SwanepoelW22FigureLocalExactAngleDataFamily :=
  Swanepoel.FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily

theorem swanepoelW22FigureLocalExactCertificateFamily_nonempty_of_dataFamily
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F :
      SwanepoelW22FigureLocalExactAngleDataFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (Swanepoel.FigureAngleSourceInhabitationW21.LocalExactCertificateFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.localExactCertificateFamily_nonempty
    F

end Verified
end Swanepoel
end ErdosProblems1066

end
