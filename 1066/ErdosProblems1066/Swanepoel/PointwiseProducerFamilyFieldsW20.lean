import ErdosProblems1066.Swanepoel.PointwiseAssemblyClosureW19
import ErdosProblems1066.Swanepoel.NoCutMinimalityClosureW19
import ErdosProblems1066.Swanepoel.TopologyArcClosureW19
import ErdosProblems1066.Swanepoel.Lemma8ConcreteGeometryProducerW19
import ErdosProblems1066.Swanepoel.Lemma9NatLateTripleProducerW19
import ErdosProblems1066.Swanepoel.FigureWitnessClosureW19

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W20 pointwise producer-family fields

This file assembles the W19 pointwise producer package from the weakest source
families currently exposed by the W19 source modules.  The resulting package is
conditional, but each condition is named at the lowest available interface:

* pay-for-cut: the W19 minimality/no-cut field family;
* topology arc: actual topology-arc inputs, with a constructor from the W19
  topology source family;
* Lemma 8: W19 finite pointwise geometry rows;
* Lemma 9: W19 natural late-triple coverage rows;
* figures: W19 local angle-containment bridge rows.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseProducerFamilyFieldsW20

open FigureWitnessConcreteAssemblyW17
open Lemma9NatLateTripleProducerW19
open MinimalGraphFacts
open PointwiseAssemblyClosureW19
open PointwiseFamilyProducerW18
open PointwiseRemainingRowAssemblyW17

universe u

noncomputable section

abbrev W19PointwiseProducerFamilyFields :=
  PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields

abbrev PayForCutConcreteProducerFamily :=
  PointwiseAssemblyClosureW19.PayForCutConcreteProducerFamily

abbrev TopologyArcConcreteProducerFamily :=
  PointwiseAssemblyClosureW19.TopologyArcConcreteProducerFamily

abbrev Lemma8ConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :=
  PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
    payForCut topologyArc

abbrev Lemma9CoverageConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  PointwiseAssemblyClosureW19.Lemma9CoverageConcreteProducerFamily.{u}
    payForCut topologyArc lemma8

abbrev FigureWitnessConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  PointwiseAssemblyClosureW19.FigureWitnessConcreteProducerFamily.{u}
    payForCut topologyArc lemma8

abbrev PointwiseW16AssemblyFamily :=
  PointwiseAssemblyClosureW19.PointwiseW16AssemblyFamily

abbrev ConcreteBlockerInputFamily :=
  PointwiseAssemblyClosureW19.ConcreteBlockerInputFamily

/-! ## Weak source assumptions and adapters -/

abbrev PayForCutNoCutFieldFamily : Prop :=
  NoCutMinimalityClosureW19.PayForCutNoCutFieldFamily

def payForCutConcreteProducerFamilyOfNoCutFieldFamily
    (H : PayForCutNoCutFieldFamily) :
    PayForCutConcreteProducerFamily where
  row := by
    intro n C hmin
    exact
      (NoCutPayForCutProducerW18.pointwiseBasePayForCutInput_iff_concreteSideCardInequalityAll
        (C := C) hmin).1 (H C hmin)

abbrev ActualTopologyArcInputsFamily :=
  TopologyArcClosureW19.MinimalFailureActualTopologyArcInputsFamily

abbrev TopologyArcSourceFamily :=
  TopologyArcClosureW19.MinimalFailureTopologyArcSourceFamily

def topologyArcConcreteProducerFamilyOfActualInputsFamily
    (F : ActualTopologyArcInputsFamily.{u}) :
    TopologyArcConcreteProducerFamily.{u} where
  row := fun C hmin => F.inputsFor C hmin

def topologyArcConcreteProducerFamilyOfSourceFamily
    (F : TopologyArcSourceFamily.{u}) :
    TopologyArcConcreteProducerFamily.{u} :=
  topologyArcConcreteProducerFamilyOfActualInputsFamily
    F.toActualTopologyArcInputsFamily

def topologyArcConcreteProducerFamilyOfW18SourceFamily
    (F : TopologyArcClosureW19.W18TopologyArcSourceFamily.{u}) :
    TopologyArcConcreteProducerFamily.{u} :=
  topologyArcConcreteProducerFamilyOfActualInputsFamily
    (TopologyArcClosureW19.actualTopologyArcInputsFamilyOfW18SourceFamily F)

abbrev Lemma8GeometrySourceFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :=
  Lemma8ConcreteGeometryProducerW19.PointwiseLemma8GeometryFieldFamily.{u}
    payForCut topologyArc

def preLateBase
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    Lemma9LateTriplesW16.PointwiseLemma89PreLateBase.{u} C hmin :=
  (PointwiseFamilyProducerW18.baseInputs
    payForCut topologyArc lemma8 C hmin).toPreLateBase

def lemma8ConcreteProducerFamilyOfGeometrySourceFamily
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    (F : Lemma8GeometrySourceFamily.{u} payForCut topologyArc) :
    Lemma8ConcreteProducerFamily.{u} payForCut topologyArc :=
  F.toLemma8ConcreteProducerFamily

structure Lemma9NatCoverageSourceFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Lemma9NatLateTripleProducerW19.M8NatLateTripleCoverageInputs
          (preLateBase payForCut topologyArc lemma8 C hmin)

namespace Lemma9NatCoverageSourceFamily

variable
  {payForCut : PayForCutConcreteProducerFamily}
  {topologyArc : TopologyArcConcreteProducerFamily.{u}}
  {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

def toLemma9CoverageConcreteProducerFamily
    (F :
      Lemma9NatCoverageSourceFamily.{u}
        payForCut topologyArc lemma8) :
    Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin => (F.row C hmin).toCoverageConcreteRow

theorem row_iff_exists_coverage_and_nat
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    Nonempty
        (Lemma9NatLateTripleProducerW19.M8NatLateTripleCoverageInputs
          (preLateBase payForCut topologyArc lemma8 C hmin)) <->
      exists longArcCount : Nat,
        Nonempty
          (Lemma6Lemma7AssemblyW13.GapNegativeCoverageData
            ((preLateBase payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary)
            longArcCount) /\
          Nonempty
            (LateTriplesInterface.M8NatLateTripleInputs
              ((preLateBase payForCut topologyArc lemma8 C hmin).localLabels.predicates.data)) :=
  Lemma9NatLateTripleProducerW19.nonempty_natCoverageInputs_iff_exists_coverage_and_nat
    (B :=
      preLateBase payForCut topologyArc lemma8 C hmin)

end Lemma9NatCoverageSourceFamily

structure FigureLocalAngleContainmentSourceFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        FigureWitnessClosureW19.LocalAngleContainmentBridgeProducerInput
          (PointwiseFamilyProducerW18.baseInputs
            payForCut topologyArc lemma8 C hmin).localLabels
          (PointwiseFamilyProducerW18.baseInputs
            payForCut topologyArc lemma8 C hmin).turnBounds

namespace FigureLocalAngleContainmentSourceFamily

variable
  {payForCut : PayForCutConcreteProducerFamily}
  {topologyArc : TopologyArcConcreteProducerFamily.{u}}
  {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

def toFigureWitnessConcreteProducerFamily
    (F :
      FigureLocalAngleContainmentSourceFamily.{u}
        payForCut topologyArc lemma8) :
    FigureWitnessConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toLocalFigureWitnessConcreteFields

theorem row_E22_E23
    (F :
      FigureLocalAngleContainmentSourceFamily.{u}
        payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    Lemma10AnalyticBridge.HonestFigure8SeparatedWindowLowerE22
        (PointwiseFamilyProducerW18.baseInputs
          payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (PointwiseFamilyProducerW18.baseInputs
          payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      Lemma10AnalyticBridge.HonestFigure9AdjacentWindowLowerE23
        (PointwiseFamilyProducerW18.baseInputs
          payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (PointwiseFamilyProducerW18.baseInputs
          payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  FigureWitnessClosureW19.LocalAngleContainmentBridgeProducerInput.E22_E23
    (F.row C hmin)

end FigureLocalAngleContainmentSourceFamily

/-! ## W20 conditional package -/

structure PointwiseSourceFamilyFields : Type (u + 1) where
  payForCut : PayForCutNoCutFieldFamily
  topologyArc : ActualTopologyArcInputsFamily.{u}
  lemma8 :
    Lemma8GeometrySourceFamily.{u}
      (payForCutConcreteProducerFamilyOfNoCutFieldFamily payForCut)
      (topologyArcConcreteProducerFamilyOfActualInputsFamily topologyArc)
  lemma9 :
    Lemma9NatCoverageSourceFamily.{u}
      (payForCutConcreteProducerFamilyOfNoCutFieldFamily payForCut)
      (topologyArcConcreteProducerFamilyOfActualInputsFamily topologyArc)
      (lemma8ConcreteProducerFamilyOfGeometrySourceFamily lemma8)
  figures :
    FigureLocalAngleContainmentSourceFamily.{u}
      (payForCutConcreteProducerFamilyOfNoCutFieldFamily payForCut)
      (topologyArcConcreteProducerFamilyOfActualInputsFamily topologyArc)
      (lemma8ConcreteProducerFamilyOfGeometrySourceFamily lemma8)

namespace PointwiseSourceFamilyFields

def payForCutConcrete
    (P : PointwiseSourceFamilyFields.{u}) :
    PayForCutConcreteProducerFamily :=
  payForCutConcreteProducerFamilyOfNoCutFieldFamily P.payForCut

def topologyArcConcrete
    (P : PointwiseSourceFamilyFields.{u}) :
    TopologyArcConcreteProducerFamily.{u} :=
  topologyArcConcreteProducerFamilyOfActualInputsFamily P.topologyArc

def lemma8Concrete
    (P : PointwiseSourceFamilyFields.{u}) :
    Lemma8ConcreteProducerFamily.{u}
      P.payForCutConcrete P.topologyArcConcrete :=
  lemma8ConcreteProducerFamilyOfGeometrySourceFamily P.lemma8

def lemma9Concrete
    (P : PointwiseSourceFamilyFields.{u}) :
    Lemma9CoverageConcreteProducerFamily.{u}
      P.payForCutConcrete P.topologyArcConcrete P.lemma8Concrete :=
  P.lemma9.toLemma9CoverageConcreteProducerFamily

def figuresConcrete
    (P : PointwiseSourceFamilyFields.{u}) :
    FigureWitnessConcreteProducerFamily.{u}
      P.payForCutConcrete P.topologyArcConcrete P.lemma8Concrete :=
  P.figures.toFigureWitnessConcreteProducerFamily

def toW19PointwiseProducerFamilyFields
    (P : PointwiseSourceFamilyFields.{u}) :
    W19PointwiseProducerFamilyFields.{u} where
  payForCut := P.payForCutConcrete
  topologyArc := P.topologyArcConcrete
  lemma8 := P.lemma8Concrete
  lemma9 := P.lemma9Concrete
  figures := P.figuresConcrete

def toPointwiseW16AssemblyFamily
    (P : PointwiseSourceFamilyFields.{u}) :
    PointwiseW16AssemblyFamily.{u} :=
  P.toW19PointwiseProducerFamilyFields.toPointwiseW16AssemblyFamily

theorem toPointwiseW16AssemblyFamily_nonempty
    (P : PointwiseSourceFamilyFields.{u}) :
    Nonempty PointwiseW16AssemblyFamily.{u} :=
  P.toW19PointwiseProducerFamilyFields.toPointwiseW16AssemblyFamily_nonempty

def toConcreteBlockerInputFamily
    (P : PointwiseSourceFamilyFields.{0}) :
    ConcreteBlockerInputFamily.{0} :=
  P.toW19PointwiseProducerFamilyFields.toConcreteBlockerInputFamily

theorem no_minimalClearedFailure
    (P : PointwiseSourceFamilyFields.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (MinimalGraphFacts.IsMinimalClearedFailure C) :=
  P.toW19PointwiseProducerFamilyFields.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (P : PointwiseSourceFamilyFields.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  P.toW19PointwiseProducerFamilyFields.targetLowerBoundEightThirtyOne

@[simp]
theorem toW19PointwiseProducerFamilyFields_payForCut
    (P : PointwiseSourceFamilyFields.{u}) :
    P.toW19PointwiseProducerFamilyFields.payForCut =
      P.payForCutConcrete :=
  rfl

@[simp]
theorem toW19PointwiseProducerFamilyFields_topologyArc
    (P : PointwiseSourceFamilyFields.{u}) :
    P.toW19PointwiseProducerFamilyFields.topologyArc =
      P.topologyArcConcrete :=
  rfl

@[simp]
theorem toW19PointwiseProducerFamilyFields_lemma8
    (P : PointwiseSourceFamilyFields.{u}) :
    P.toW19PointwiseProducerFamilyFields.lemma8 =
      P.lemma8Concrete :=
  rfl

@[simp]
theorem toW19PointwiseProducerFamilyFields_lemma9
    (P : PointwiseSourceFamilyFields.{u}) :
    P.toW19PointwiseProducerFamilyFields.lemma9 =
      P.lemma9Concrete :=
  rfl

@[simp]
theorem toW19PointwiseProducerFamilyFields_figures
    (P : PointwiseSourceFamilyFields.{u}) :
    P.toW19PointwiseProducerFamilyFields.figures =
      P.figuresConcrete :=
  rfl

end PointwiseSourceFamilyFields

def pointwiseW16AssemblyFamilyOfSourceFamilies
    (payForCut : PayForCutNoCutFieldFamily)
    (topologyArc : ActualTopologyArcInputsFamily.{u})
    (lemma8 :
      Lemma8GeometrySourceFamily.{u}
        (payForCutConcreteProducerFamilyOfNoCutFieldFamily payForCut)
        (topologyArcConcreteProducerFamilyOfActualInputsFamily topologyArc))
    (lemma9 :
      Lemma9NatCoverageSourceFamily.{u}
        (payForCutConcreteProducerFamilyOfNoCutFieldFamily payForCut)
        (topologyArcConcreteProducerFamilyOfActualInputsFamily topologyArc)
        (lemma8ConcreteProducerFamilyOfGeometrySourceFamily lemma8))
    (figures :
      FigureLocalAngleContainmentSourceFamily.{u}
        (payForCutConcreteProducerFamilyOfNoCutFieldFamily payForCut)
        (topologyArcConcreteProducerFamilyOfActualInputsFamily topologyArc)
        (lemma8ConcreteProducerFamilyOfGeometrySourceFamily lemma8)) :
    PointwiseW16AssemblyFamily.{u} :=
  (PointwiseSourceFamilyFields.mk
    payForCut topologyArc lemma8 lemma9 figures)
      |>.toPointwiseW16AssemblyFamily

theorem targetLowerBoundEightThirtyOne_of_sourceFamilies
    (payForCut : PayForCutNoCutFieldFamily)
    (topologyArc : ActualTopologyArcInputsFamily.{0})
    (lemma8 :
      Lemma8GeometrySourceFamily.{0}
        (payForCutConcreteProducerFamilyOfNoCutFieldFamily payForCut)
        (topologyArcConcreteProducerFamilyOfActualInputsFamily topologyArc))
    (lemma9 :
      Lemma9NatCoverageSourceFamily.{0}
        (payForCutConcreteProducerFamilyOfNoCutFieldFamily payForCut)
        (topologyArcConcreteProducerFamilyOfActualInputsFamily topologyArc)
        (lemma8ConcreteProducerFamilyOfGeometrySourceFamily lemma8))
    (figures :
      FigureLocalAngleContainmentSourceFamily.{0}
        (payForCutConcreteProducerFamilyOfNoCutFieldFamily payForCut)
        (topologyArcConcreteProducerFamilyOfActualInputsFamily topologyArc)
        (lemma8ConcreteProducerFamilyOfGeometrySourceFamily lemma8)) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  (PointwiseSourceFamilyFields.mk
    payForCut topologyArc lemma8 lemma9 figures)
      |>.targetLowerBoundEightThirtyOne

end

end PointwiseProducerFamilyFieldsW20

namespace Verified

abbrev SwanepoelW20PointwiseSourceFamilyFields :=
  Swanepoel.PointwiseProducerFamilyFieldsW20.PointwiseSourceFamilyFields

theorem targetLowerBoundEightThirtyOne_of_swanepoel_w20_pointwiseSourceFamilyFields
    (P : SwanepoelW20PointwiseSourceFamilyFields.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  P.targetLowerBoundEightThirtyOne

end Verified
end Swanepoel
end ErdosProblems1066
