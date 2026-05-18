import ErdosProblems1066.Swanepoel.PointwiseFamilyProducerW18
import ErdosProblems1066.Swanepoel.AngleContainmentBridgeProducerW19
import ErdosProblems1066.Swanepoel.FigureWitnessClosureW19

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W20 Figure producer family

This file is the adapter from the W19 angle-containment bridge surfaces to the
W18 pointwise producer-family field
`PointwiseFamilyProducerW18.FigureWitnessConcreteProducerFamily`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureProducerFamilyW20

open AngleContainmentBridgeProducerW19
open FigureWitnessClosureW19
open MinimalGraphFacts
open PointwiseFamilyProducerW18

universe u

noncomputable section

abbrev W18PayForCutConcreteProducerFamily :=
  PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily

abbrev W18TopologyArcConcreteProducerFamily :=
  PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily

abbrev W18Lemma8ConcreteProducerFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u}) :=
  PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
    payForCut topologyArc

abbrev W18FigureWitnessConcreteProducerFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  PointwiseFamilyProducerW18.FigureWitnessConcreteProducerFamily.{u}
    payForCut topologyArc lemma8

abbrev W18BaseInputs
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  PointwiseFamilyProducerW18.baseInputs
    payForCut topologyArc lemma8 C hmin

/-! ## Source packages at the W18 Figure row boundary -/

/--
Angle-containment bridge rows already specialized to the W18 Figure producer
base.  This is the exact pre-Lemma-9 source shape needed by
`PointwiseFamilyProducerW18.FigureWitnessConcreteProducerFamily`.
-/
structure BaseAngleContainmentBridgeProducerFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        FigureWitnessClosureW19.LocalAngleContainmentBridgeProducerInput
          (W18BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (W18BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

namespace BaseAngleContainmentBridgeProducerFamily

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
variable
  (F :
    BaseAngleContainmentBridgeProducerFamily.{u}
      payForCut topologyArc lemma8)

/-- A W19 bridge-source family is already a W18 Figure witness producer. -/
def toFigureWitnessConcreteProducerFamily :
    W18FigureWitnessConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    FigureWitnessClosureW19.LocalAngleContainmentBridgeProducerInput.toLocalFigureWitnessConcreteFields
      (F.row C hmin)

theorem nonempty_figureWitnessConcreteProducerFamily
    (F :
      BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (W18FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro
    (BaseAngleContainmentBridgeProducerFamily.toFigureWitnessConcreteProducerFamily
      F)

@[simp]
theorem toFigureWitnessConcreteProducerFamily_row
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (BaseAngleContainmentBridgeProducerFamily.toFigureWitnessConcreteProducerFamily
      F).row C hmin =
      FigureWitnessClosureW19.LocalAngleContainmentBridgeProducerInput.toLocalFigureWitnessConcreteFields
        (F.row C hmin) :=
  rfl

end BaseAngleContainmentBridgeProducerFamily

/--
Exact angle-containment certificates specialized to the W18 Figure producer
base.  This exposes the stronger W19 certificate surface while still reducing
to the W18 Figure witness producer.
-/
structure BaseExactAngleContainmentCertificateFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  certificate :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        AngleContainmentBridgeProducerW19.LocalExactAngleContainmentCertificate
          (W18BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (W18BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

namespace BaseExactAngleContainmentCertificateFamily

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
variable
  (F :
    BaseExactAngleContainmentCertificateFamily.{u}
      payForCut topologyArc lemma8)

/-- Forget exact W19 certificates to the bridge-source package used by the
Figure witness closure. -/
def toBaseAngleContainmentBridgeProducerFamily :
    BaseAngleContainmentBridgeProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    { angleContainment := (F.certificate C hmin).toAngleContainmentBridges }

/-- Exact W19 angle-containment certificates produce the W18 Figure witness
producer family. -/
def toFigureWitnessConcreteProducerFamily :
    W18FigureWitnessConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    AngleContainmentBridgeProducerW19.LocalExactAngleContainmentCertificate.toLocalFigureWitnessConcreteFields
      (F.certificate C hmin)

theorem nonempty_figureWitnessConcreteProducerFamily
    (F :
      BaseExactAngleContainmentCertificateFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (W18FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro
    (BaseExactAngleContainmentCertificateFamily.toFigureWitnessConcreteProducerFamily
      F)

@[simp]
theorem toBaseAngleContainmentBridgeProducerFamily_row
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    ((BaseExactAngleContainmentCertificateFamily.toBaseAngleContainmentBridgeProducerFamily
      F).row C hmin).angleContainment =
      (F.certificate C hmin).toAngleContainmentBridges :=
  rfl

@[simp]
theorem toFigureWitnessConcreteProducerFamily_row
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (BaseExactAngleContainmentCertificateFamily.toFigureWitnessConcreteProducerFamily
      F).row C hmin =
      AngleContainmentBridgeProducerW19.LocalExactAngleContainmentCertificate.toLocalFigureWitnessConcreteFields
        (F.certificate C hmin) :=
  rfl

end BaseExactAngleContainmentCertificateFamily

theorem figureWitnessConcreteProducerFamily_nonempty_of_baseBridgeFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (F :
      BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (W18FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  BaseAngleContainmentBridgeProducerFamily.nonempty_figureWitnessConcreteProducerFamily
    F

theorem figureWitnessConcreteProducerFamily_nonempty_of_exactBaseFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (F :
      BaseExactAngleContainmentCertificateFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (W18FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  BaseExactAngleContainmentCertificateFamily.nonempty_figureWitnessConcreteProducerFamily
    F

end

end FigureProducerFamilyW20

namespace Verified

universe u

abbrev SwanepoelW20FigureBridgeSourceFamily :=
  Swanepoel.FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily

abbrev SwanepoelW20FigureExactSourceFamily :=
  Swanepoel.FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily

abbrev SwanepoelW20FigureWitnessConcreteProducerFamily :=
  Swanepoel.FigureProducerFamilyW20.W18FigureWitnessConcreteProducerFamily

theorem swanepoelW20FigureWitnessConcreteProducerFamily_nonempty_of_bridgeSourceFamily
    {payForCut :
      Swanepoel.FigureProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
          payForCut topologyArc}
    (F :
      SwanepoelW20FigureBridgeSourceFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (SwanepoelW20FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.FigureProducerFamilyW20.figureWitnessConcreteProducerFamily_nonempty_of_baseBridgeFamily
    F

theorem swanepoelW20FigureWitnessConcreteProducerFamily_nonempty_of_exactSourceFamily
    {payForCut :
      Swanepoel.FigureProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
          payForCut topologyArc}
    (F :
      SwanepoelW20FigureExactSourceFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (SwanepoelW20FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.FigureProducerFamilyW20.figureWitnessConcreteProducerFamily_nonempty_of_exactBaseFamily
    F

end Verified
end Swanepoel
end ErdosProblems1066
