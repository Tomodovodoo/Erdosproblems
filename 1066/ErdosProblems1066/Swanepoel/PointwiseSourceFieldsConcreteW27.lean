import ErdosProblems1066.Swanepoel.PointwiseSourceFieldsInhabitationW25
import ErdosProblems1066.Swanepoel.NoCutConcreteEliminationW26
import ErdosProblems1066.Swanepoel.BoundaryWitnessRemainingFieldsW26
import ErdosProblems1066.Swanepoel.Lemma8FrameRowsConstructionW26
import ErdosProblems1066.Swanepoel.Lemma9NoEarlyConstructionW26
import ErdosProblems1066.Swanepoel.FigureWitnessConstructionW26

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W27 pointwise source-field concrete assembler

This file is the W27 SW8 boundary for the W25 pointwise source fields.  The
currently checked W26 workers do not expose unconditional inhabitants of all
five W20 fields.  What they do expose is enough to assemble the actual W25
`PointwiseSourceFamilyFields` from one explicit product of remaining concrete
components:

* the W26 partition-scoped no-cut deletion eliminator;
* the W26 selected-boundary remaining component family, which supplies the
  actual topology-arc inputs;
* W26 Lemma 8 frame-positive rows;
* the exact W25/W26 Lemma 9 no-early source family;
* W22/W26 local exact figure-angle data.

Thus this module has no endpoint alias or hidden inhabitance claim: the
`PointwiseSourceFieldsW26Product` below is the precise product still needed,
and `pointwiseSourceFamilyFieldsOfW26Product` is the actual W25 record obtained
from it.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseSourceFieldsConcreteW27

universe u

noncomputable section

open MinimalGraphFacts

def payForCutNoCutFieldFamilyOfCutPartitionDegreeDeletionEliminator
    (H : NoCutConcreteEliminationW26.CutPartitionDegreeDeletionEliminator) :
    PointwiseProducerFamilyFieldsW20.PayForCutNoCutFieldFamily :=
  NoCutConcreteEliminationW26.pointwisePayForCutFamily_of_cutPartitionDegreeDeletionEliminator
    H

def payForCutConcreteProducerFamilyOfCutPartitionDegreeDeletionEliminator
    (H : NoCutConcreteEliminationW26.CutPartitionDegreeDeletionEliminator) :
    PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily :=
  PointwiseProducerFamilyFieldsW20.payForCutConcreteProducerFamilyOfNoCutFieldFamily
    (payForCutNoCutFieldFamilyOfCutPartitionDegreeDeletionEliminator H)

def topologyArcSourceFieldsOfSelectedFaceRemainingComponentRow
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (R :
      BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentRow.{u}
        C hmin) :
    TopologyArcClosureW19.MinimalFailureTopologyArcSourceFields.{u}
      C hmin where
  topology :=
    MinimalBoundaryTopologyWitnessInhabitationW25.topologyFactsOfSelectedFace
      R.selectedFace R.enclosure
  outerAngleBounds := R.remaining.angleField.outerAngleBounds
  Subpolygon := R.remaining.subpolygonField.Subpolygon
  subpolygonData := R.remaining.subpolygonField.subpolygonData
  longArc := R.remaining.longArcField.longArc
  triangleRun := R.remaining.triangleRunField.triangleRun

def actualTopologyArcInputsFamilyOfBoundaryComponentFamily
    (F :
      BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentFamily.{u}) :
    PointwiseProducerFamilyFieldsW20.ActualTopologyArcInputsFamily.{u} where
  inputs := fun C hmin =>
    (topologyArcSourceFieldsOfSelectedFaceRemainingComponentRow
      (F.row C hmin)).toActualTopologyArcInputs

def topologyArcConcreteProducerFamilyOfBoundaryComponentFamily
    (F :
      BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentFamily.{u}) :
    PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u} :=
  PointwiseProducerFamilyFieldsW20.topologyArcConcreteProducerFamilyOfActualInputsFamily
    (actualTopologyArcInputsFamilyOfBoundaryComponentFamily F)

def lemma8GeometrySourceFamilyOfFramePositiveOrderRows
    {payForCut : PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc : PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}}
    (F :
      Lemma8FrameRowsConstructionW26.FramePositiveOrderRows.{u}
        payForCut topologyArc) :
    PointwiseProducerFamilyFieldsW20.Lemma8GeometrySourceFamily.{u}
      payForCut topologyArc :=
  Lemma8FrameRowsConstructionW26.geometryFieldFamilyOfFramePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc) F

def lemma8ConcreteProducerFamilyOfFramePositiveOrderRows
    {payForCut : PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc : PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}}
    (F :
      Lemma8FrameRowsConstructionW26.FramePositiveOrderRows.{u}
        payForCut topologyArc) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc :=
  PointwiseProducerFamilyFieldsW20.lemma8ConcreteProducerFamilyOfGeometrySourceFamily
    (lemma8GeometrySourceFamilyOfFramePositiveOrderRows F)

def lemma9NatCoverageSourceFamilyOfNoEarlySourceFamily
    {payForCut : PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc : PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F :
      Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :
    PointwiseProducerFamilyFieldsW20.Lemma9NatCoverageSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    ((F.toSourceFamily).row C hmin).toNatLateTripleCoverageInputs

def figureLocalAngleContainmentSourceFamilyOfLocalExactAngleDataFamily
    {payForCut : PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc : PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F :
      FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
        payForCut topologyArc lemma8) :
    PointwiseProducerFamilyFieldsW20.FigureLocalAngleContainmentSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin => (F.row C hmin).toLocalBridgeInput

structure PointwiseSourceFieldsW26Product : Type (u + 1) where
  noCut :
    NoCutConcreteEliminationW26.CutPartitionDegreeDeletionEliminator
  boundary :
    BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentFamily.{u}
  lemma8 :
    Lemma8FrameRowsConstructionW26.FramePositiveOrderRows.{u}
      (payForCutConcreteProducerFamilyOfCutPartitionDegreeDeletionEliminator
        noCut)
      (topologyArcConcreteProducerFamilyOfBoundaryComponentFamily boundary)
  lemma9 :
    Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{u}
      (payForCutConcreteProducerFamilyOfCutPartitionDegreeDeletionEliminator
        noCut)
      (topologyArcConcreteProducerFamilyOfBoundaryComponentFamily boundary)
      (lemma8ConcreteProducerFamilyOfFramePositiveOrderRows lemma8)
  figures :
    FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
      (payForCutConcreteProducerFamilyOfCutPartitionDegreeDeletionEliminator
        noCut)
      (topologyArcConcreteProducerFamilyOfBoundaryComponentFamily boundary)
      (lemma8ConcreteProducerFamilyOfFramePositiveOrderRows lemma8)

namespace PointwiseSourceFieldsW26Product

def payForCutNoCutFieldFamily
    (P : PointwiseSourceFieldsW26Product.{u}) :
    PointwiseProducerFamilyFieldsW20.PayForCutNoCutFieldFamily :=
  payForCutNoCutFieldFamilyOfCutPartitionDegreeDeletionEliminator P.noCut

def payForCutConcrete
    (P : PointwiseSourceFieldsW26Product.{u}) :
    PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily :=
  payForCutConcreteProducerFamilyOfCutPartitionDegreeDeletionEliminator
    P.noCut

def topologyArcInputs
    (P : PointwiseSourceFieldsW26Product.{u}) :
    PointwiseProducerFamilyFieldsW20.ActualTopologyArcInputsFamily.{u} :=
  actualTopologyArcInputsFamilyOfBoundaryComponentFamily P.boundary

def topologyArcConcrete
    (P : PointwiseSourceFieldsW26Product.{u}) :
    PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u} :=
  topologyArcConcreteProducerFamilyOfBoundaryComponentFamily P.boundary

def lemma8Geometry
    (P : PointwiseSourceFieldsW26Product.{u}) :
    PointwiseProducerFamilyFieldsW20.Lemma8GeometrySourceFamily.{u}
      P.payForCutConcrete P.topologyArcConcrete :=
  lemma8GeometrySourceFamilyOfFramePositiveOrderRows P.lemma8

def lemma8Concrete
    (P : PointwiseSourceFieldsW26Product.{u}) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
      P.payForCutConcrete P.topologyArcConcrete :=
  lemma8ConcreteProducerFamilyOfFramePositiveOrderRows P.lemma8

def lemma9NatCoverage
    (P : PointwiseSourceFieldsW26Product.{u}) :
    PointwiseProducerFamilyFieldsW20.Lemma9NatCoverageSourceFamily.{u}
      P.payForCutConcrete P.topologyArcConcrete P.lemma8Concrete :=
  lemma9NatCoverageSourceFamilyOfNoEarlySourceFamily P.lemma9

def figureAngleContainment
    (P : PointwiseSourceFieldsW26Product.{u}) :
    PointwiseProducerFamilyFieldsW20.FigureLocalAngleContainmentSourceFamily.{u}
      P.payForCutConcrete P.topologyArcConcrete P.lemma8Concrete :=
  figureLocalAngleContainmentSourceFamilyOfLocalExactAngleDataFamily P.figures

def toPointwiseSourceFamilyFields
    (P : PointwiseSourceFieldsW26Product.{u}) :
    PointwiseSourceFieldsInhabitationW25.PointwiseSourceFamilyFields.{u} where
  payForCut := P.payForCutNoCutFieldFamily
  topologyArc := P.topologyArcInputs
  lemma8 := P.lemma8Geometry
  lemma9 := P.lemma9NatCoverage
  figures := P.figureAngleContainment

end PointwiseSourceFieldsW26Product

def pointwiseSourceFamilyFieldsOfW26Product
    (P : PointwiseSourceFieldsW26Product.{u}) :
    PointwiseSourceFieldsInhabitationW25.PointwiseSourceFamilyFields.{u} :=
  P.toPointwiseSourceFamilyFields

theorem pointwiseSourceFamilyFields_nonempty_of_w26Product
    (P : PointwiseSourceFieldsW26Product.{u}) :
    Nonempty
      (PointwiseSourceFieldsInhabitationW25.PointwiseSourceFamilyFields.{u}) :=
  Nonempty.intro (pointwiseSourceFamilyFieldsOfW26Product P)

theorem pointwiseSourceFamilyFields_nonempty_of_nonempty_w26Product
    (h : Nonempty PointwiseSourceFieldsW26Product.{u}) :
    Nonempty
      (PointwiseSourceFieldsInhabitationW25.PointwiseSourceFamilyFields.{u}) := by
  cases h with
  | intro P =>
      exact pointwiseSourceFamilyFields_nonempty_of_w26Product P

end

end PointwiseSourceFieldsConcreteW27
end Swanepoel
end ErdosProblems1066
