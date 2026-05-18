import ErdosProblems1066.Swanepoel.NoCutPayForCutProducerW18
import ErdosProblems1066.Swanepoel.ActualTopologyArcInputsProducerW18
import ErdosProblems1066.Swanepoel.BoundaryFrameCoreProducerW19
import ErdosProblems1066.Swanepoel.PositiveCyclicOrderProducerW19
import ErdosProblems1066.Swanepoel.Lemma8ConcreteGeometryProducerW19
import ErdosProblems1066.Swanepoel.Lemma9NatLateTripleProducerW19
import ErdosProblems1066.Swanepoel.AngleContainmentBridgeProducerW19
import ErdosProblems1066.Swanepoel.PointwiseAssemblyClosureW19

set_option autoImplicit false
set_option linter.unusedDecidableInType false

namespace ErdosProblems1066
namespace Swanepoel
namespace RemainingObligationLedgerW20

open ActualTopologyArcInputsProducerW18
open AngleContainmentBridgeProducerW19
open BoundaryFrameCoreProducerW19
open Lemma8ConcreteGeometryProducerW19
open Lemma8GeometryFieldsW18
open Lemma9NatLateTripleProducerW19
open MinimalGraphFacts
open NoCutPayForCutProducerW18
open PointwiseAssemblyClosureW19
open PointwiseFamilyProducerW18
open PointwiseRemainingRowAssemblyW17
open PositiveCyclicOrderProducerW19

universe u

noncomputable section

/-! ## Pay-for-cut / no-cut -/

abbrev PayForCutProducerFamily : Type 1 :=
  PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily

abbrev NoCutFamily : Prop :=
  NoCutPayForCutProducerW18.MinimalFailureNoCutFamily

abbrev ConcreteSideCardFamily : Prop :=
  NoCutPayForCutProducerW18.MinimalFailureConcreteSideCardFamily

def payForCutProducerFamilyOfNoCutFamily
    (H : NoCutFamily) :
    PayForCutProducerFamily where
  row := fun C hmin =>
    (NoCutPayForCutProducerW18.noCutFamily_iff_concreteSideCardFamily).1
      H C hmin

def noCutFamilyOfPayForCutProducerFamily
    (F : PayForCutProducerFamily) :
    NoCutFamily :=
  fun C hmin =>
    PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily.noCutVertex
      F C hmin

theorem payForCutProducerFamily_nonempty_iff_noCutFamily :
    Nonempty PayForCutProducerFamily <-> NoCutFamily := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact noCutFamilyOfPayForCutProducerFamily F
  case mpr =>
    intro H
    exact Nonempty.intro (payForCutProducerFamilyOfNoCutFamily H)

theorem noCutFamily_iff_concreteSideCardFamily :
    NoCutFamily <-> ConcreteSideCardFamily :=
  NoCutPayForCutProducerW18.noCutFamily_iff_concreteSideCardFamily

/-! ## Topology source -/

abbrev TopologySourceFamily : Type (u + 1) :=
  ActualTopologyArcInputsProducerW18.MinimalFailureActualTopologyArcSourceFamily.{u}

abbrev TopologyArcProducerFamily : Type (u + 1) :=
  PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}

def topologyArcProducerFamilyOfSource
    (F : TopologySourceFamily.{u}) :
    TopologyArcProducerFamily.{u} where
  row := fun C hmin =>
    F.inputsFor C hmin

@[simp]
theorem topologyArcProducerFamilyOfSource_row
    (F : TopologySourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (topologyArcProducerFamilyOfSource F).row C hmin =
      F.inputsFor C hmin :=
  rfl

/-! ## Lemma 8 frame / order -/

abbrev Lemma8FrameCardinalitySources
    {n : Nat} {C : _root_.UDConfig n}
    {H : M8LabelsFromBoundaryInterface.M8BoundaryCutDegreeContext C}
    (S : M8LabelsFromBoundaryInterface.M8BoundarySpine H) : Prop :=
  BoundaryFrameCoreProducerW19.M8FrameCoreCardinalitySources S

abbrev Lemma8PositiveOrderCertificate
    {n : Nat} {C : _root_.UDConfig n}
    {H : M8LabelsFromBoundaryInterface.M8BoundaryCutDegreeContext C}
    {S : M8LabelsFromBoundaryInterface.M8BoundarySpine H}
    (R : Lemma8FrameCardinalitySources S) : Type :=
  PositiveCyclicOrderProducerW19.M8PositiveCyclicOrderCertificate
    R.extraNeighborData

def lemma8GeometryFieldSourcesOfFrameAndOrder
    {n : Nat} {C : _root_.UDConfig n}
    {H : M8LabelsFromBoundaryInterface.M8BoundaryCutDegreeContext C}
    {S : M8LabelsFromBoundaryInterface.M8BoundarySpine H}
    (R : Lemma8FrameCardinalitySources S)
    (O : Lemma8PositiveOrderCertificate R) :
    Lemma8GeometryFieldsW18.M8GeometryFieldSources S :=
  R.toGeometryFieldSources
    O.positiveCyclicOrderAt O.positiveCyclicOrder

abbrev Lemma8GeometryFieldFamily
    (payForCut : PayForCutProducerFamily)
    (topologyArc : TopologyArcProducerFamily.{u}) : Type (u + 1) :=
  Lemma8ConcreteGeometryProducerW19.PointwiseLemma8GeometryFieldFamily.{u}
    payForCut topologyArc

def lemma8ProducerFamilyOfGeometryFamily
    {payForCut : PayForCutProducerFamily}
    {topologyArc : TopologyArcProducerFamily.{u}}
    (F : Lemma8GeometryFieldFamily.{u} payForCut topologyArc) :
    PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc :=
  F.toLemma8ConcreteProducerFamily

/-! ## Lemma 9 natural late triples -/

abbrev PointwiseBaseInputs
    (payForCut : PayForCutProducerFamily)
    (topologyArc : TopologyArcProducerFamily.{u})
    (lemma8 :
      PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    PointwiseRemainingRowAssemblyW17.PointwiseW16BaseInputs.{u} C hmin :=
  PointwiseFamilyProducerW18.baseInputs
    payForCut topologyArc lemma8 C hmin

abbrev PointwisePreLateBase
    (payForCut : PayForCutProducerFamily)
    (topologyArc : TopologyArcProducerFamily.{u})
    (lemma8 :
      PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  (PointwiseBaseInputs payForCut topologyArc lemma8 C hmin).toPreLateBase

structure Lemma9NatLateTripleCoverageFamily
    (payForCut : PayForCutProducerFamily)
    (topologyArc : TopologyArcProducerFamily.{u})
    (lemma8 :
      PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Lemma9NatLateTripleProducerW19.M8NatLateTripleCoverageInputs
          (PointwisePreLateBase payForCut topologyArc lemma8 C hmin)

namespace Lemma9NatLateTripleCoverageFamily

variable {payForCut : PayForCutProducerFamily}
variable {topologyArc : TopologyArcProducerFamily.{u}}
variable
  {lemma8 :
    PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc}

def toLemma9CoverageConcreteProducerFamily
    (F :
      Lemma9NatLateTripleCoverageFamily.{u}
        payForCut topologyArc lemma8) :
    PointwiseAssemblyClosureW19.Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toCoverageConcreteRow

@[simp]
theorem toLemma9CoverageConcreteProducerFamily_row
    (F :
      Lemma9NatLateTripleCoverageFamily.{u}
        payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (F.toLemma9CoverageConcreteProducerFamily.row C hmin) =
      (F.row C hmin).toCoverageConcreteRow :=
  rfl

end Lemma9NatLateTripleCoverageFamily

/-! ## Figure angle bridges -/

structure FigureAngleBridgeFamily
    (payForCut : PayForCutProducerFamily)
    (topologyArc : TopologyArcProducerFamily.{u})
    (lemma8 :
      PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        AngleContainmentBridgeProducerW19.LocalExactAngleContainmentCertificate
          (PointwiseBaseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (PointwiseBaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

namespace FigureAngleBridgeFamily

variable {payForCut : PayForCutProducerFamily}
variable {topologyArc : TopologyArcProducerFamily.{u}}
variable
  {lemma8 :
    PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc}

def toFigureWitnessConcreteProducerFamily
    (F : FigureAngleBridgeFamily.{u} payForCut topologyArc lemma8) :
    PointwiseAssemblyClosureW19.FigureWitnessConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toLocalFigureWitnessConcreteFields

@[simp]
theorem toFigureWitnessConcreteProducerFamily_row
    (F : FigureAngleBridgeFamily.{u} payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (F.toFigureWitnessConcreteProducerFamily.row C hmin) =
      (F.row C hmin).toLocalFigureWitnessConcreteFields :=
  rfl

end FigureAngleBridgeFamily

/-! ## Final pointwise producer family fields -/

structure RemainingObligationFields : Type (u + 1) where
  noCut : NoCutFamily
  topologySource : TopologySourceFamily.{u}
  lemma8 :
    Lemma8GeometryFieldFamily.{u}
      (payForCutProducerFamilyOfNoCutFamily noCut)
      (topologyArcProducerFamilyOfSource topologySource)
  lemma9 :
    Lemma9NatLateTripleCoverageFamily.{u}
      (payForCutProducerFamilyOfNoCutFamily noCut)
      (topologyArcProducerFamilyOfSource topologySource)
      (lemma8ProducerFamilyOfGeometryFamily lemma8)
  figures :
    FigureAngleBridgeFamily.{u}
      (payForCutProducerFamilyOfNoCutFamily noCut)
      (topologyArcProducerFamilyOfSource topologySource)
      (lemma8ProducerFamilyOfGeometryFamily lemma8)

namespace RemainingObligationFields

variable (P : RemainingObligationFields.{u})

def payForCut : PayForCutProducerFamily :=
  payForCutProducerFamilyOfNoCutFamily P.noCut

def topologyArc : TopologyArcProducerFamily.{u} :=
  topologyArcProducerFamilyOfSource P.topologySource

def lemma8Producer :
    PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
      P.payForCut P.topologyArc :=
  lemma8ProducerFamilyOfGeometryFamily P.lemma8

def lemma9Producer :
    PointwiseAssemblyClosureW19.Lemma9CoverageConcreteProducerFamily.{u}
      P.payForCut P.topologyArc P.lemma8Producer :=
  P.lemma9.toLemma9CoverageConcreteProducerFamily

def figureProducer :
    PointwiseAssemblyClosureW19.FigureWitnessConcreteProducerFamily.{u}
      P.payForCut P.topologyArc P.lemma8Producer :=
  P.figures.toFigureWitnessConcreteProducerFamily

def toPointwiseProducerFamilyFields :
    PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields.{u} where
  payForCut := P.payForCut
  topologyArc := P.topologyArc
  lemma8 := P.lemma8Producer
  lemma9 := P.lemma9Producer
  figures := P.figureProducer

def toPointwiseW16AssemblyFamily :
    PointwiseAssemblyClosureW19.PointwiseW16AssemblyFamily.{u} :=
  P.toPointwiseProducerFamilyFields.toPointwiseW16AssemblyFamily

theorem pointwiseW16AssemblyFamily_nonempty
    (P : RemainingObligationFields.{u}) :
    Nonempty PointwiseAssemblyClosureW19.PointwiseW16AssemblyFamily.{u} :=
  Nonempty.intro (toPointwiseW16AssemblyFamily P)

theorem no_minimalClearedFailure
    (P : RemainingObligationFields.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields.no_minimalClearedFailure
    (toPointwiseProducerFamilyFields P)

theorem targetLowerBoundEightThirtyOne
    (P : RemainingObligationFields.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields.targetLowerBoundEightThirtyOne
    (toPointwiseProducerFamilyFields P)

@[simp]
theorem toPointwiseProducerFamilyFields_payForCut :
    P.toPointwiseProducerFamilyFields.payForCut = P.payForCut :=
  rfl

@[simp]
theorem toPointwiseProducerFamilyFields_topologyArc :
    P.toPointwiseProducerFamilyFields.topologyArc = P.topologyArc :=
  rfl

@[simp]
theorem toPointwiseProducerFamilyFields_lemma8 :
    P.toPointwiseProducerFamilyFields.lemma8 = P.lemma8Producer :=
  rfl

end RemainingObligationFields

theorem targetLowerBoundEightThirtyOne_of_remainingObligationFields
    (P : RemainingObligationFields.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  RemainingObligationFields.targetLowerBoundEightThirtyOne P

end

end RemainingObligationLedgerW20
end Swanepoel

namespace Verified

abbrev SwanepoelW20RemainingObligationFields :=
  Swanepoel.RemainingObligationLedgerW20.RemainingObligationFields

theorem targetLowerBoundEightThirtyOne_of_swanepoel_w20_remainingObligationFields
    (P : SwanepoelW20RemainingObligationFields.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  Swanepoel.RemainingObligationLedgerW20.targetLowerBoundEightThirtyOne_of_remainingObligationFields
    P

end Verified
end ErdosProblems1066
