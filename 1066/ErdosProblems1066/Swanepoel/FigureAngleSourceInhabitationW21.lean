import ErdosProblems1066.Swanepoel.FigureProducerFamilyW20
import ErdosProblems1066.Swanepoel.FigureWitnessClosureW19
import ErdosProblems1066.Swanepoel.AngleContainmentBridgeProducerW19
import ErdosProblems1066.Swanepoel.Figure8ContainmentW12
import ErdosProblems1066.Swanepoel.Figure9ContainmentW12

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W21 Figure angle-source inhabitation

This file records the W21-SW5 attempt to inhabit the W20 Figure
angle-containment source family.

The available W19/W20 adapters close the Figure witness producer once every
local W18 base row carries an exact angle-containment certificate.  The current
imports do not provide such certificates unconditionally; the results below
therefore expose the exact remaining dependency and show how the W12 Figure 8
and Figure 9 containment data feed into it.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureAngleSourceInhabitationW21

open AngleContainmentBridgeProducerW19
open FigureProducerFamilyW20
open MinimalGraphFacts

universe u

noncomputable section

abbrev PayForCutConcreteProducerFamily :=
  FigureProducerFamilyW20.W18PayForCutConcreteProducerFamily

abbrev TopologyArcConcreteProducerFamily :=
  FigureProducerFamilyW20.W18TopologyArcConcreteProducerFamily

abbrev Lemma8ConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :=
  FigureProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
    payForCut topologyArc

abbrev FigureWitnessConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  FigureProducerFamilyW20.W18FigureWitnessConcreteProducerFamily.{u}
    payForCut topologyArc lemma8

abbrev BaseInputs
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  FigureProducerFamilyW20.W18BaseInputs
    payForCut topologyArc lemma8 C hmin

abbrev LocalExactCertificateForBase
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  AngleContainmentBridgeProducerW19.LocalExactAngleContainmentCertificate
    (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
    (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

abbrev LocalExactCertificateFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      LocalExactCertificateForBase payForCut topologyArc lemma8 C hmin

abbrev LocalBridgeInputForBase
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  FigureWitnessClosureW19.LocalAngleContainmentBridgeProducerInput
    (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
    (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

abbrev LocalBridgeInputFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      LocalBridgeInputForBase payForCut topologyArc lemma8 C hmin

/-! ## Local W12 data to W19 exact certificates -/

/-- W12 Figure 8/Figure 9 witnesses plus the two local angle-containment
inequalities are exactly enough to build the W19 local exact certificate. -/
def localExactCertificate_of_w12Data
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    {turnBounds : M8ConstructionInterface.M8TurnBounds}
    (figure8Witnesses :
      Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
        localLabels.predicates turnBounds.turn)
    (figure8AngleContainment :
      AngleContainmentBridgeProducerW19.Figure8UniversalAngleContainment
        (Lemma10Bridge.M8BrokenLatticeGood
          localLabels.predicates.data)
        turnBounds.turn)
    (figure9Witnesses :
      Figure9ContainmentW12.HonestAdjacentWindowWitnesses
        localLabels.predicates turnBounds.turn)
    (figure9AngleContainment :
      AngleContainmentBridgeProducerW19.Figure9UniversalLeftAngleContainment
        (Lemma10Bridge.M8BrokenLatticeGood
          localLabels.predicates.data)
        turnBounds.turn) :
    AngleContainmentBridgeProducerW19.LocalExactAngleContainmentCertificate
      localLabels turnBounds where
  figure8 :=
    { witnesses := figure8Witnesses
      central_angle_le_separatedTurn := figure8AngleContainment }
  figure9 :=
    { witnesses := figure9Witnesses
      left_angle_le_adjacentTurn := figure9AngleContainment }

/-- The certificate built from W12 data exposes the expected bridge input used
by the W19 Figure witness closure. -/
def localBridgeInput_of_w12Data
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    {turnBounds : M8ConstructionInterface.M8TurnBounds}
    (figure8Witnesses :
      Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
        localLabels.predicates turnBounds.turn)
    (figure8AngleContainment :
      AngleContainmentBridgeProducerW19.Figure8UniversalAngleContainment
        (Lemma10Bridge.M8BrokenLatticeGood
          localLabels.predicates.data)
        turnBounds.turn)
    (figure9Witnesses :
      Figure9ContainmentW12.HonestAdjacentWindowWitnesses
        localLabels.predicates turnBounds.turn)
    (figure9AngleContainment :
      AngleContainmentBridgeProducerW19.Figure9UniversalLeftAngleContainment
        (Lemma10Bridge.M8BrokenLatticeGood
          localLabels.predicates.data)
        turnBounds.turn) :
    FigureWitnessClosureW19.LocalAngleContainmentBridgeProducerInput
      localLabels turnBounds where
  angleContainment :=
    (localExactCertificate_of_w12Data
      figure8Witnesses figure8AngleContainment
      figure9Witnesses figure9AngleContainment).toAngleContainmentBridges

theorem localBridgeInput_of_w12Data_E22_E23
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    {turnBounds : M8ConstructionInterface.M8TurnBounds}
    (figure8Witnesses :
      Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
        localLabels.predicates turnBounds.turn)
    (figure8AngleContainment :
      AngleContainmentBridgeProducerW19.Figure8UniversalAngleContainment
        (Lemma10Bridge.M8BrokenLatticeGood
          localLabels.predicates.data)
        turnBounds.turn)
    (figure9Witnesses :
      Figure9ContainmentW12.HonestAdjacentWindowWitnesses
        localLabels.predicates turnBounds.turn)
    (figure9AngleContainment :
      AngleContainmentBridgeProducerW19.Figure9UniversalLeftAngleContainment
        (Lemma10Bridge.M8BrokenLatticeGood
          localLabels.predicates.data)
        turnBounds.turn) :
    Lemma10AnalyticBridge.HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      Lemma10AnalyticBridge.HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  FigureWitnessClosureW19.LocalAngleContainmentBridgeProducerInput.E22_E23
    (localBridgeInput_of_w12Data
      figure8Witnesses figure8AngleContainment
      figure9Witnesses figure9AngleContainment)

/-! ## Exact dependency of the W20 source family -/

def exactSourceFamilyOfLocalCertificates
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (certificates :
      LocalExactCertificateFamily.{u} payForCut topologyArc lemma8) :
    FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
      payForCut topologyArc lemma8 where
  certificate := fun C hmin => certificates C hmin

def localCertificatesOfExactSourceFamily
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (F :
      FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
        payForCut topologyArc lemma8) :
    LocalExactCertificateFamily.{u} payForCut topologyArc lemma8 :=
  fun {n} C hmin => F.certificate (n := n) C hmin

theorem exactSourceFamily_iff_localCertificates
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc} :
    Nonempty
        (FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
          payForCut topologyArc lemma8) <->
      Nonempty
        (LocalExactCertificateFamily.{u} payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro (localCertificatesOfExactSourceFamily F)
  case mpr =>
    intro h
    cases h with
    | intro certificates =>
        exact Nonempty.intro
          (exactSourceFamilyOfLocalCertificates certificates)

theorem exactSourceFamily_nonempty_iff_pointwise_localCertificates
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc} :
    Nonempty
        (FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
          payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Nonempty
            (LocalExactCertificateForBase
              payForCut topologyArc lemma8 C hmin)) := by
  constructor
  case mp =>
    intro h n C hmin
    cases h with
    | intro F =>
        exact Nonempty.intro (F.certificate (n := n) C hmin)
  case mpr =>
    intro h
    refine Nonempty.intro ?_
    exact exactSourceFamilyOfLocalCertificates
      (fun {n} C hmin => Classical.choice (h (n := n) C hmin))

def bridgeSourceFamilyOfLocalBridgeInputs
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (bridges : LocalBridgeInputFamily.{u} payForCut topologyArc lemma8) :
    FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin => bridges C hmin

def localBridgeInputsOfBridgeSourceFamily
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (F :
      FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8) :
    LocalBridgeInputFamily.{u} payForCut topologyArc lemma8 :=
  fun {n} C hmin => F.row (n := n) C hmin

theorem bridgeSourceFamily_nonempty_iff_pointwise_localBridgeInputs
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc} :
    Nonempty
        (FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
          payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Nonempty
            (LocalBridgeInputForBase
              payForCut topologyArc lemma8 C hmin)) := by
  constructor
  case mp =>
    intro h n C hmin
    cases h with
    | intro F =>
        exact Nonempty.intro (F.row (n := n) C hmin)
  case mpr =>
    intro h
    refine Nonempty.intro ?_
    exact bridgeSourceFamilyOfLocalBridgeInputs
      (fun {n} C hmin => Classical.choice (h (n := n) C hmin))

theorem figureWitnessProducer_nonempty_of_pointwise_localCertificates
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (h :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Nonempty
            (LocalExactCertificateForBase
              payForCut topologyArc lemma8 C hmin)) :
    Nonempty
      (FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) := by
  cases
    (exactSourceFamily_nonempty_iff_pointwise_localCertificates
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8)).2 h
    with
  | intro F =>
      exact
        FigureProducerFamilyW20.figureWitnessConcreteProducerFamily_nonempty_of_exactBaseFamily
          F

theorem figureWitnessProducer_nonempty_of_pointwise_localBridgeInputs
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (h :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Nonempty
            (LocalBridgeInputForBase
              payForCut topologyArc lemma8 C hmin)) :
    Nonempty
      (FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) := by
  cases
    (bridgeSourceFamily_nonempty_iff_pointwise_localBridgeInputs
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8)).2 h
    with
  | intro F =>
      exact
        FigureProducerFamilyW20.figureWitnessConcreteProducerFamily_nonempty_of_baseBridgeFamily
          F

end

end FigureAngleSourceInhabitationW21
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW21FigureLocalExactCertificateFamily :=
  Swanepoel.FigureAngleSourceInhabitationW21.LocalExactCertificateFamily

theorem swanepoelW21FigureExactSourceFamily_nonempty_iff_localCertificates
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Nonempty
        (Swanepoel.FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
          payForCut topologyArc lemma8) <->
      Nonempty
        (SwanepoelW21FigureLocalExactCertificateFamily.{u}
          payForCut topologyArc lemma8) :=
  Swanepoel.FigureAngleSourceInhabitationW21.exactSourceFamily_iff_localCertificates

theorem swanepoelW21FigureWitnessProducer_nonempty_of_localCertificates
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (h :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : Swanepoel.MinimalGraphFacts.IsMinimalClearedFailure C),
          Nonempty
            (Swanepoel.FigureAngleSourceInhabitationW21.LocalExactCertificateForBase
              payForCut topologyArc lemma8 C hmin)) :
    Nonempty
      (Swanepoel.FigureAngleSourceInhabitationW21.FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.FigureAngleSourceInhabitationW21.figureWitnessProducer_nonempty_of_pointwise_localCertificates
    h

end Verified
end ErdosProblems1066
