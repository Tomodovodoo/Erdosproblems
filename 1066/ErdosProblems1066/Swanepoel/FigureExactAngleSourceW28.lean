import ErdosProblems1066.Swanepoel.FigureWitnessConcreteW27

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W28 exact Figure angle source

This file keeps the Figure 8/Figure 9 E22/E23 route tied to its actual source
data.  The source package below stores the selected W12 witnesses together
with the exact universal angle/window containment inequalities.  It then feeds
`FigureWitnessConcreteW27.LocalSelectedFigureWitnessFields` through W22/W24,
rather than wrapping the E22/E23 endpoint statements.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureExactAngleSourceW28

open AngleContainmentBridgeProducerW19
open AngleContainmentInterface
open FigureAngleContainmentConcreteW23
open FigureAngleSourceInhabitationW21
open FigureExactAngleCertificateInhabitationW22
open FigureWitnessConcreteW27
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
  M8BrokenLatticeGood localLabels.predicates.data

/-! ## Pointwise exact sources -/

/-- The exact source needed for the selected Figure 8/Figure 9 E22/E23 route.

The W12 witnesses provide concrete metric data.  The exact inequality package
provides the universal containment of those angles in the turn windows. -/
structure LocalExactFigureWitnessSource
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  figure8Witnesses :
    Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
      localLabels.predicates turnBounds.turn
  figure9Witnesses :
    Figure9ContainmentW12.HonestAdjacentWindowWitnesses
      localLabels.predicates turnBounds.turn
  exactInequalities :
    LocalExactFigureAngleInequalities localLabels turnBounds

namespace LocalExactFigureWitnessSource

variable {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}

/-- Reconstruct the W22 local exact angle data from the W28 source fields. -/
def toLocalExactAngleData
    (S : LocalExactFigureWitnessSource localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds :=
  localExactData_of_w12WitnessesAndInequalities
    S.figure8Witnesses S.figure9Witnesses S.exactInequalities

/-- Reconstruct the W19 exact local certificate from the W28 source fields. -/
def toLocalExactCertificate
    (S : LocalExactFigureWitnessSource localLabels turnBounds) :
    LocalExactAngleContainmentCertificate localLabels turnBounds :=
  S.toLocalExactAngleData.toLocalExactCertificate

/-- Selected W12 witnesses exposed from the exact source, in W26's shape. -/
def toSelectedW12WitnessFields
    (S : LocalExactFigureWitnessSource localLabels turnBounds) :
    FigureWitnessConcreteW27.LocalSelectedW12WitnessFields
      localLabels turnBounds :=
  FigureWitnessConcreteW27.selectedW12WitnessFields_of_localExactAngleData
    S.toLocalExactAngleData

/-- Selected Euclidean witnesses exposed from the exact source, in W26's
shape. -/
def toSelectedEuclideanWitnessFields
    (S : LocalExactFigureWitnessSource localLabels turnBounds) :
    FigureWitnessConcreteW27.LocalSelectedEuclideanWitnessFields
      localLabels turnBounds :=
  FigureWitnessConcreteW27.selectedEuclideanWitnessFields_of_localExactAngleData
    S.toLocalExactAngleData

/-- The W27 selected Figure witness package built from actual W12 plus exact
angle/window containment data. -/
def toLocalSelectedFigureWitnessFields
    (S : LocalExactFigureWitnessSource localLabels turnBounds) :
    FigureWitnessConcreteW27.LocalSelectedFigureWitnessFields
      localLabels turnBounds :=
  FigureWitnessConcreteW27.localSelectedFigureWitnessFields_of_localExactAngleData
    S.toLocalExactAngleData

/-- The exact source proves E22/E23 only after passing through selected
Euclidean Figure witnesses. -/
theorem E22_E23
    (S : LocalExactFigureWitnessSource localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  S.toLocalSelectedFigureWitnessFields.E22_E23

theorem E22
    (S : LocalExactFigureWitnessSource localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn :=
  S.E22_E23.1

theorem E23
    (S : LocalExactFigureWitnessSource localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  S.E22_E23.2

end LocalExactFigureWitnessSource

/-! ## Source constructors -/

/-- Build an exact source directly from selected W12 witnesses and the exact
Figure angle/window containment package. -/
def localExactFigureWitnessSource_of_w12AndInequalities
    (figure8 :
      Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
        localLabels.predicates turnBounds.turn)
    (figure9 :
      Figure9ContainmentW12.HonestAdjacentWindowWitnesses
        localLabels.predicates turnBounds.turn)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    LocalExactFigureWitnessSource localLabels turnBounds where
  figure8Witnesses := figure8
  figure9Witnesses := figure9
  exactInequalities := H

/-- Repackage W22 local exact angle data as the W28 exact source. -/
def localExactFigureWitnessSource_of_localExactAngleData
    (D : LocalExactAngleData localLabels turnBounds) :
    LocalExactFigureWitnessSource localLabels turnBounds :=
  localExactFigureWitnessSource_of_w12AndInequalities
    D.figure8Witnesses D.figure9Witnesses
    { figure8 := D.figure8AngleContainment
      figure9_left := D.figure9AngleContainment }

/-- Concrete local window-containment fields contain exactly the W12 witness
and universal angle/window data needed by the W28 exact source. -/
def localExactFigureWitnessSource_of_localWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    LocalExactFigureWitnessSource localLabels turnBounds :=
  localExactFigureWitnessSource_of_w12AndInequalities
    (Figure8ContainmentW12.dataWitnesses_of_localWindowContainmentFields W)
    (Figure9ContainmentW12.witnesses_of_containmentInterface W.figure9_left)
    (localInequalities_of_localWindowContainmentFields W)

/-- W19 exact local certificates contain the same exact source data. -/
def localExactFigureWitnessSource_of_localExactCertificate
    (H : LocalExactAngleContainmentCertificate localLabels turnBounds) :
    LocalExactFigureWitnessSource localLabels turnBounds :=
  localExactFigureWitnessSource_of_localExactAngleData
    (LocalExactAngleData.ofLocalExactCertificate H)

/-- Combined angle-containment bridges feed the W28 exact source through the
concrete local window-containment fields. -/
def localExactFigureWitnessSource_of_angleContainmentBridges
    (A : AngleContainmentBridges (LocalGood localLabels) turnBounds.turn) :
    LocalExactFigureWitnessSource localLabels turnBounds :=
  localExactFigureWitnessSource_of_localWindowContainmentFields
    (M8LocalWindowContainmentFields.ofAngleContainmentBridges A)

/-- Local exact data and the W28 exact source have the same local inhabitance
content.  This is the pointwise source blocker for E22/E23. -/
theorem localExactFigureWitnessSource_nonempty_iff_localExactAngleData :
    Nonempty (LocalExactFigureWitnessSource localLabels turnBounds) <->
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
          (localExactFigureWitnessSource_of_localExactAngleData D)

/-! ## Family-level exact sources -/

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

/-- A family of exact Figure sources over the W21 base rows. -/
structure LocalExactFigureWitnessSourceFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        LocalExactFigureWitnessSource
          (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

namespace LocalExactFigureWitnessSourceFamily

/-- Forget a W28 source family back to the W22 exact angle-data family. -/
def toLocalExactAngleDataFamily
    (F : LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toLocalExactAngleData

/-- Build the W27 selected Figure witness family from exact source rows. -/
def toSelectedFigureWitnessFieldsFamily
    (F : LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8) :
    FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toLocalSelectedFigureWitnessFields

/-- Build the W20 exact source family from exact source rows. -/
def toExactSourceFamily
    (F : LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8) :
    FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
      payForCut topologyArc lemma8 :=
  F.toLocalExactAngleDataFamily.toExactSourceFamily

/-- Build the W28 source family from a W22 exact angle-data family. -/
def ofLocalExactAngleDataFamily
    (F : LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :
    LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localExactFigureWitnessSource_of_localExactAngleData
      (F.row C hmin)

/-- Build the W28 source family from concrete local window-containment field
rows. -/
def ofLocalWindowContainmentFieldsFamily
    (W : LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localExactFigureWitnessSource_of_localWindowContainmentFields
      (W C hmin)

/-- Build the W28 source family from a W20 exact certificate family. -/
def ofExactSourceFamily
    (F : FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localExactFigureWitnessSource_of_localExactCertificate
      (F.certificate C hmin)

/-- Build the W28 source family from a W20 bridge-source family. -/
def ofBridgeSourceFamily
    (F : FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
      payForCut topologyArc lemma8) :
    LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localExactFigureWitnessSource_of_angleContainmentBridges
      (F.row C hmin).angleContainment

/-- Each exact source row proves E22/E23 through the W27 selected witness
package. -/
theorem row_E22_E23
    (F : LocalExactFigureWitnessSourceFamily.{u}
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

end LocalExactFigureWitnessSourceFamily

/-- The family-level source blocker for the exact E22/E23 route. -/
abbrev ExactE22E23SourceBlocker
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  Nonempty
    (LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8)

/-- The W28 blocker is exactly W22 local exact angle data: selected W12
witnesses plus exact universal angle/window containment rows. -/
theorem exactE22E23SourceBlocker_iff_localExactAngleDataFamily :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 <->
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
          (LocalExactFigureWitnessSourceFamily.ofLocalExactAngleDataFamily F)

/-- Concrete local window-containment families discharge the exact E22/E23
source blocker. -/
theorem exactE22E23SourceBlocker_of_localWindowContainmentFieldsFamily
    (W : LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  Nonempty.intro
    (LocalExactFigureWitnessSourceFamily.ofLocalWindowContainmentFieldsFamily W)

/-- W20 exact source families discharge the exact E22/E23 source blocker. -/
theorem exactE22E23SourceBlocker_of_exactSourceFamily
    (F : FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  Nonempty.intro
    (LocalExactFigureWitnessSourceFamily.ofExactSourceFamily F)

/-- W20 bridge-source families discharge the exact E22/E23 source blocker. -/
theorem exactE22E23SourceBlocker_of_bridgeSourceFamily
    (F : FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
      payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  Nonempty.intro
    (LocalExactFigureWitnessSourceFamily.ofBridgeSourceFamily F)

/-- Once the exact source blocker is discharged, W27 receives an inhabited
selected Figure witness family. -/
theorem selectedFigureWitnessFamily_nonempty_of_exactE22E23SourceBlocker
    (h : ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) :
    Nonempty
      (FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | intro F =>
      exact Nonempty.intro F.toSelectedFigureWitnessFieldsFamily

/-- The exact source blocker yields the row-level E22/E23 consequences via
the W27 selected Figure witness route. -/
theorem row_E22_E23_of_exactE22E23SourceBlocker
    (h : ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn := by
  cases h with
  | intro F =>
      exact F.row_E22_E23 C hmin

end FigureExactAngleSourceW28
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW28LocalExactFigureWitnessSource
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : Swanepoel.M8ConstructionInterface.M8LocalLabels C)
    (turnBounds : Swanepoel.M8ConstructionInterface.M8TurnBounds) :=
  Swanepoel.FigureExactAngleSourceW28.LocalExactFigureWitnessSource
    localLabels turnBounds

abbrev SwanepoelW28ExactE22E23SourceBlocker :=
  Swanepoel.FigureExactAngleSourceW28.ExactE22E23SourceBlocker

theorem swanepoelW28_exactE22E23SourceBlocker_iff_localExactAngleDataFamily
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    SwanepoelW28ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8 <->
      Nonempty
        (Swanepoel.FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
          payForCut topologyArc lemma8) :=
  Swanepoel.FigureExactAngleSourceW28.exactE22E23SourceBlocker_iff_localExactAngleDataFamily

theorem swanepoelW28_selectedFigureWitnessFamily_nonempty_of_exactE22E23SourceBlocker
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (h :
      SwanepoelW28ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (Swanepoel.FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.FigureExactAngleSourceW28.selectedFigureWitnessFamily_nonempty_of_exactE22E23SourceBlocker
    h

end Verified
end ErdosProblems1066

end
