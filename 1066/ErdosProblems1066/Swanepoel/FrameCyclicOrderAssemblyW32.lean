import ErdosProblems1066.Swanepoel.FrameRowsInhabitationW31
import ErdosProblems1066.Swanepoel.CyclicOrderRowsInhabitationW31
import ErdosProblems1066.Swanepoel.PointwiseLaneProductInhabitationW31
import ErdosProblems1066.Swanepoel.ExtractedComponentsConcreteClosureW32
import ErdosProblems1066.Swanepoel.BoundaryArcExtractionProofW15
import ErdosProblems1066.Swanepoel.BoundaryArcFiniteWalkConstructionW16
import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate
import ErdosProblems1066.Swanepoel.Lemma8ConcreteGeometryProducerW19
import ErdosProblems1066.Swanepoel.DegreeBound
import ErdosProblems1066.Swanepoel.GraphBridge

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W32 frame/cyclic-order source assembly

This file assembles the W31 frame-row and cyclic-order-row surfaces into a
single source package.  It keeps the degree-six route honest by naming the
exact generated cyclic-row blocker: degree-six/non-cyclic rows plus cyclic
rows keyed to the frame rows generated from those degree-six rows.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FrameCyclicOrderAssemblyW32

open MinimalGraphFacts
open BoundarySpineFiniteCertificate
open BoundaryArcExtractionProofW15
open Lemma8ForbiddenDistinctConcrete
open M8LabelsFromBoundaryInterface
open PointwiseFamilyProducerW18

universe u

noncomputable section

variable
  (payForCut : PayForCutConcreteProducerFamily)
  (topologyArc : TopologyArcConcreteProducerFamily.{u})

abbrev UniformFiniteGeometryRows : Type (u + 1) :=
  FrameRowsInhabitationW31.UniformFiniteGeometryRows.{u}
    payForCut topologyArc

abbrev UniformFrameCyclicOrderRows : Type (u + 1) :=
  FrameRowsInhabitationW31.UniformFrameCyclicOrderRows.{u}
    payForCut topologyArc

abbrev FrameRows : Prop :=
  FrameRowsInhabitationW31.FrameRows.{u}
    payForCut topologyArc

abbrev FiniteGeometryRows
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Type :=
  FrameRowsInhabitationW31.FiniteGeometryRows.{u}
    payForCut topologyArc C hmin

abbrev FrameCardinalityRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Prop :=
  FrameRowsInhabitationW31.FrameCardinalityRow.{u}
    payForCut topologyArc C hmin

abbrev UniformFrameRowsSource : Type (u + 1) :=
  FrameRowsInhabitationW31.UniformFrameRowsSource.{u}
    payForCut topologyArc

abbrev NeighborCyclicOrderRowsForFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :=
  FrameRowsInhabitationW31.NeighborCyclicOrderRowsForFrameRows.{u}
    payForCut topologyArc frameRows

abbrev SeparatedFrameCyclicOrderRows : Type (u + 1) :=
  FrameRowsInhabitationW31.SeparatedFrameCyclicOrderRows.{u}
    payForCut topologyArc

abbrev NeighborCyclicOrderSourceRows : Type (u + 1) :=
  CyclicOrderRowsInhabitationW31.NeighborCyclicOrderSourceRows.{u}
    payForCut topologyArc

abbrev FrameCyclicRowsBlocker : Prop :=
  CyclicOrderRowsInhabitationW31.FrameCyclicRowsBlocker.{u}
    payForCut topologyArc

abbrev ExactRemainingPackage : Type (u + 1) :=
  FrameRowsInhabitationW31.ExactRemainingPackage.{u}
    payForCut topologyArc

abbrev GeometryFieldFamily : Type (u + 1) :=
  FrameRowsInhabitationW31.GeometryFieldFamily.{u}
    payForCut topologyArc

abbrev ConcreteFrameOrderFamily : Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.ConcreteFrameOrderFamily.{u}
    payForCut topologyArc

abbrev FramePositiveOrderRows : Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.FramePositiveOrderRows.{u}
    payForCut topologyArc

abbrev DegreeSixNoncyclicRows : Prop :=
  FrameRowsInhabitationW31.DegreeSixNoncyclicRows.{u}
    payForCut topologyArc

abbrev DegreeSixNeighborCyclicOrderRows : Type (u + 1) :=
  FrameRowsInhabitationW31.DegreeSixNeighborCyclicOrderRows.{u}
    payForCut topologyArc

abbrev W31DegreeSixGeneratedFrameCyclicRowsBlocker : Prop :=
  CyclicOrderRowsInhabitationW31.DegreeSixGeneratedFrameCyclicRowsBlocker.{u}
    payForCut topologyArc

/-! ## Frame plus cyclic-order source package -/

/-- The exact W32 source package: frame rows together with cyclic-order rows
keyed to those same frame rows. -/
structure FrameCyclicOrderSourcePackage : Type (u + 1) where
  frameRows : FrameRows.{u} payForCut topologyArc
  cyclicRows :
    NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc frameRows

def frameCyclicOrderSourcePackageOfRows
    (frameRows : FrameRows.{u} payForCut topologyArc)
    (cyclicRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc where
  frameRows := frameRows
  cyclicRows := cyclicRows

namespace FrameCyclicOrderSourcePackage

def toUniformFrameRowsSource
    (P : FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :
    UniformFrameRowsSource.{u} payForCut topologyArc :=
  FrameRowsInhabitationW31.uniformFrameRowsSourceOfFrameRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.frameRows

def toSeparatedRows
    (P : FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :
    SeparatedFrameCyclicOrderRows.{u} payForCut topologyArc where
  frameSource := P.toUniformFrameRowsSource
  cyclicOrderRows := P.cyclicRows

def toNeighborCyclicOrderSourceRows
    (P : FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :
    NeighborCyclicOrderSourceRows.{u} payForCut topologyArc where
  frameRows := P.frameRows
  neighborCyclicOrderRows := P.cyclicRows

def toUniformFrameCyclicOrderRows
    (P : FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :
    UniformFrameCyclicOrderRows.{u} payForCut topologyArc :=
  FrameRowsInhabitationW31.uniformFrameCyclicOrderRowsOfSeparatedRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.toSeparatedRows

def toUniformFiniteGeometryRows
    (P : FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  FrameRowsInhabitationW31.uniformFiniteGeometryRowsOfSeparatedRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.toSeparatedRows

def toExactRemainingPackage
    (P : FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :
    ExactRemainingPackage.{u} payForCut topologyArc :=
  Lemma8FiniteGeometryRowsW28.exactRemainingPackageOfUniformRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.toUniformFiniteGeometryRows

def toGeometryFieldFamily
    (P : FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :
    GeometryFieldFamily.{u} payForCut topologyArc :=
  FrameRowsInhabitationW31.geometryFieldFamilyOfUniformFiniteGeometryRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.toUniformFiniteGeometryRows

end FrameCyclicOrderSourcePackage

def frameCyclicOrderSourcePackageOfSeparatedRows
    (P : SeparatedFrameCyclicOrderRows.{u} payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc where
  frameRows := P.frameSource.frameRows
  cyclicRows := P.cyclicOrderRows

def frameCyclicOrderSourcePackageOfNeighborCyclicOrderSourceRows
    (P : NeighborCyclicOrderSourceRows.{u} payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc where
  frameRows := P.frameRows
  cyclicRows := P.neighborCyclicOrderRows

def frameCyclicOrderSourcePackageOfUniformFrameCyclicOrderRows
    (P : UniformFrameCyclicOrderRows.{u} payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc where
  frameRows :=
    FrameCyclicOrderRowsW30.frameRowsOfUniformFrameCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P
  cyclicRows :=
    FrameCyclicOrderRowsW30.neighborCyclicOrderRowsOfUniformFrameCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P

def frameCyclicOrderSourcePackageOfUniformFiniteGeometryRows
    (P : UniformFiniteGeometryRows.{u} payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc :=
  frameCyclicOrderSourcePackageOfSeparatedRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (FrameRowsInhabitationW31.separatedRowsOfUniformFiniteGeometryRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem sourcePackage_nonempty_iff_separatedRows :
    Nonempty
        (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) <->
      Nonempty
        (SeparatedFrameCyclicOrderRows.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toSeparatedRows
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (frameCyclicOrderSourcePackageOfSeparatedRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem sourcePackage_nonempty_iff_neighborCyclicOrderSourceRows :
    Nonempty
        (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) <->
      Nonempty
        (NeighborCyclicOrderSourceRows.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toNeighborCyclicOrderSourceRows
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (frameCyclicOrderSourcePackageOfNeighborCyclicOrderSourceRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem uniformFrameCyclicOrderRows_nonempty_iff_sourcePackage :
    Nonempty
        (UniformFrameCyclicOrderRows.{u} payForCut topologyArc) <->
      Nonempty
        (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :=
  (CyclicOrderRowsInhabitationW31.uniformFrameCyclicOrderRows_nonempty_iff_neighborCyclicOrderSourceRows
    (payForCut := payForCut) (topologyArc := topologyArc)).trans
    (sourcePackage_nonempty_iff_neighborCyclicOrderSourceRows
      (payForCut := payForCut) (topologyArc := topologyArc)).symm

theorem uniformFiniteGeometryRows_nonempty_iff_sourcePackage :
    Nonempty
        (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      Nonempty
        (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :=
  (FrameRowsInhabitationW31.uniformFiniteGeometryRows_nonempty_iff_separatedRows
    (payForCut := payForCut) (topologyArc := topologyArc)).trans
    (sourcePackage_nonempty_iff_separatedRows
      (payForCut := payForCut) (topologyArc := topologyArc)).symm

theorem sourcePackage_nonempty_iff_frameCyclicRowsBlocker :
    Nonempty
        (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) <->
      FrameCyclicRowsBlocker.{u} payForCut topologyArc :=
  (sourcePackage_nonempty_iff_neighborCyclicOrderSourceRows
    (payForCut := payForCut) (topologyArc := topologyArc)).trans
    (CyclicOrderRowsInhabitationW31.neighborCyclicOrderSourceRows_nonempty_iff_frameCyclicRowsBlocker
      (payForCut := payForCut) (topologyArc := topologyArc))

theorem sourcePackage_nonempty_iff_exactRemainingPackage :
    Nonempty
        (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) <->
      Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) :=
  (uniformFiniteGeometryRows_nonempty_iff_sourcePackage
    (payForCut := payForCut) (topologyArc := topologyArc)).symm.trans
    (FrameRowsInhabitationW31.exactRemainingPackage_nonempty_iff_uniformFiniteGeometryRows
      (payForCut := payForCut) (topologyArc := topologyArc)).symm

theorem sourcePackage_nonempty_iff_geometryFieldFamily :
    Nonempty
        (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) <->
      Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) :=
  (uniformFiniteGeometryRows_nonempty_iff_sourcePackage
    (payForCut := payForCut) (topologyArc := topologyArc)).symm.trans
    (FrameRowsInhabitationW31.geometryFieldFamily_nonempty_iff_uniformFiniteGeometryRows
      (payForCut := payForCut) (topologyArc := topologyArc)).symm

theorem exactRemainingPackage_nonempty_of_sourcePackage
    (P : FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :
    Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) :=
  Nonempty.intro P.toExactRemainingPackage

theorem geometryFieldFamily_nonempty_of_sourcePackage
    (P : FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :
    Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) :=
  Nonempty.intro P.toGeometryFieldFamily

/-! ## Real constructors from existing Lemma 8 frame/order producers -/

def frameCyclicOrderSourcePackageOfFramePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc where
  frameRows := P.frameRows
  cyclicRows :=
    UniformFiniteGeometryRowsSourceW29.neighborCyclicOrderRowsOfPositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRows := P.frameRows)
      P.positiveOrderRows

def uniformFiniteGeometryRowsOfFramePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  (frameCyclicOrderSourcePackageOfFramePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc) P).toUniformFiniteGeometryRows

def frameCyclicOrderSourcePackageOfConcreteFrameOrderFamily
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc :=
  frameCyclicOrderSourcePackageOfFramePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (Lemma8FrameRowsConstructionW26.framePositiveOrderRowsOfConcreteFrameOrderFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

def frameCyclicOrderSourcePackageOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc :=
  frameCyclicOrderSourcePackageOfFramePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (Lemma8FrameRowsConstructionW26.framePositiveOrderRowsOfGeometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

def frameCyclicOrderSourcePackageOfExactRemainingPackage
    (P : ExactRemainingPackage.{u} payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc :=
  frameCyclicOrderSourcePackageOfFramePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (Lemma8GeometryFamilyConcreteW27.framePositiveOrderRowsOfExactRemainingPackage
      (payForCut := payForCut) (topologyArc := topologyArc) P)

def frameCyclicOrderSourcePackageOfRemainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    FrameCyclicOrderSourcePackage.{u} P.payForCut P.topologyArc :=
  frameCyclicOrderSourcePackageOfFramePositiveOrderRows
    (payForCut := P.payForCut) (topologyArc := P.topologyArc)
    (Lemma8GeometryFamilyConcreteW27.framePositiveOrderRowsOfRemainingLaneProduct P)

def frameCyclicOrderSourcePackageOfConcreteComponentLanes
    (P : M8ComponentLanesConcreteW23.ConcreteComponentLanes.{u}) :
    FrameCyclicOrderSourcePackage.{u}
      (M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
      (M8ComponentLanesConcreteW23.topologyArcProducerOfLane P.topology) :=
  frameCyclicOrderSourcePackageOfConcreteFrameOrderFamily
    (payForCut := M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
    (topologyArc :=
      M8ComponentLanesConcreteW23.topologyArcProducerOfLane P.topology)
    (Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamilyOfConcreteComponentLanes
      P)

def frameCyclicOrderSourcePackageOfNamedConcreteComponentLanes
    (P : M8ComponentLanesConcreteW23.NamedConcreteComponentLanes.{u}) :
    FrameCyclicOrderSourcePackage.{u}
      (M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
      (M8ComponentLanesConcreteW23.topologyArcProducerOfLane
        (M8ComponentLanesConcreteW23.topologyLaneOfNamedTopology P.topology)) :=
  frameCyclicOrderSourcePackageOfConcreteComponentLanes
    (M8ComponentLanesConcreteW23.NamedConcreteComponentLanes.toConcreteComponentLanes P)

theorem sourcePackage_nonempty_of_framePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    Nonempty (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (frameCyclicOrderSourcePackageOfFramePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem uniformFiniteGeometryRows_nonempty_of_framePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (uniformFiniteGeometryRowsOfFramePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem sourcePackage_nonempty_of_concreteFrameOrderFamily
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    Nonempty (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (frameCyclicOrderSourcePackageOfConcreteFrameOrderFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

theorem sourcePackage_nonempty_of_geometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    Nonempty (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (frameCyclicOrderSourcePackageOfGeometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

theorem sourcePackage_nonempty_of_exactRemainingPackage
    (P : ExactRemainingPackage.{u} payForCut topologyArc) :
    Nonempty (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (frameCyclicOrderSourcePackageOfExactRemainingPackage
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem sourcePackage_nonempty_of_remainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    Nonempty
      (FrameCyclicOrderSourcePackage.{u} P.payForCut P.topologyArc) :=
  Nonempty.intro (frameCyclicOrderSourcePackageOfRemainingLaneProduct P)

theorem sourcePackage_nonempty_of_concreteComponentLanes
    (P : M8ComponentLanesConcreteW23.ConcreteComponentLanes.{u}) :
    Nonempty
      (FrameCyclicOrderSourcePackage.{u}
        (M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
        (M8ComponentLanesConcreteW23.topologyArcProducerOfLane P.topology)) :=
  Nonempty.intro (frameCyclicOrderSourcePackageOfConcreteComponentLanes P)

theorem sourcePackage_nonempty_of_namedConcreteComponentLanes
    (P : M8ComponentLanesConcreteW23.NamedConcreteComponentLanes.{u}) :
    Nonempty
      (FrameCyclicOrderSourcePackage.{u}
        (M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
        (M8ComponentLanesConcreteW23.topologyArcProducerOfLane
          (M8ComponentLanesConcreteW23.topologyLaneOfNamedTopology P.topology))) :=
  Nonempty.intro (frameCyclicOrderSourcePackageOfNamedConcreteComponentLanes P)

theorem sourcePackage_nonempty_iff_framePositiveOrderRows :
    Nonempty
        (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) <->
      Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) :=
  (sourcePackage_nonempty_iff_geometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc)).trans
    (Lemma8FrameRowsConstructionW26.framePositiveOrderRows_nonempty_iff_geometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc)).symm

theorem sourcePackage_nonempty_iff_concreteFrameOrderFamily :
    Nonempty
        (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) <->
      Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) :=
  (sourcePackage_nonempty_iff_framePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)).trans
    (Lemma8FrameRowsInhabitationW25.concreteFrameOrderFamily_nonempty_iff_framePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)).symm

/-! ## Frame-core/Lemma 8 combinatorics route -/

abbrev PointwiseSpine {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  Lemma8ConcreteGeometryProducerW19.pointwiseSpine
    payForCut topologyArc C hmin

abbrev PointwiseFinitePQSpineCertificate {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    M8FinitePQSpineCertificate
      (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary :=
  (topologyArc.row C hmin).boundaryArc.toFinitePQSpineCertificate

def pointwiseFinitePQSpineCyclicSuccessorRows
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows
      (PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin) :=
  BoundaryArcFiniteWalkData.cyclicSuccessorRowsOfBoundaryArcCertificate
    (topologyArc.row C hmin).boundaryArc

def pointwiseFinitePQSpineCyclicSuccessorRowsSource
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows
          K } :=
  Nonempty.intro
    (Subtype.mk
      (PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin)
      (pointwiseFinitePQSpineCyclicSuccessorRows
        (topologyArc := topologyArc) C hmin))

def pointwiseFinitePQSpineCyclicSuccessorRowsFamily :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Nonempty
          { K :
              M8FinitePQSpineCertificate
                (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary //
            BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows
              K } :=
  fun C hmin =>
    pointwiseFinitePQSpineCyclicSuccessorRowsSource
      (topologyArc := topologyArc) C hmin

def pointwiseFinitePQSpineCyclicSuccessorRowsFamilyOfFinitePQTheorem
    (H :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Nonempty
          { K :
              M8FinitePQSpineCertificate
                (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary //
            BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows
              K } :=
  fun C hmin =>
    H C
      (topologyArc.row C hmin).topology
      (topologyArc.row C hmin).outerAngleBounds
      (topologyArc.row C hmin).Subpolygon
      (topologyArc.row C hmin).subpolygonData
      (topologyArc.row C hmin).longArc

abbrev PointwiseConnectedNoCutCertificate {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  (MinimalFailureClosureW13.cutVertexOfNoCut hmin
    (payForCut.noCutVertex C hmin)).preconnectedNoCut

/-- The real non-cyclic Lemma 8 source row for the W32 route: the named
Lemma 8 combinatorics and the actual finite-spine fields that generate the
four-forbidden frame core.  The center-degree six field is deliberately
absent; it is derived from these rows. -/
structure FrameCoreLemma8CombinatoricsRows : Type (u + 1) where
  frameCoreFields :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8FinitePQSpineFrameCoreFields
          (PointwiseFinitePQSpineCertificate
            (topologyArc := topologyArc) C hmin)
          (PointwiseConnectedNoCutCertificate
            (payForCut := payForCut) C hmin)
          hmin
  lemma8 :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8Lemma8Combinatorics
          (PointwiseSpine (payForCut := payForCut)
            (topologyArc := topologyArc) C hmin)

namespace FrameCoreLemma8CombinatoricsRows

/-- The four-forbidden frame core generated from the actual finite-spine
frame-core fields. -/
def frameCore
    (P : FrameCoreLemma8CombinatoricsRows.{u} payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    M8FourForbiddenFrameCore
      (PointwiseSpine (payForCut := payForCut)
        (topologyArc := topologyArc) C hmin) :=
  { core := fun i =>
      { prev_adj := (P.frameCoreFields C hmin).prev_adj i
        next_adj := (P.frameCoreFields C hmin).next_adj i
        left_ne_next := (P.frameCoreFields C hmin).left_ne_next i
        right_ne_prev := (P.frameCoreFields C hmin).right_ne_prev i
        prev_ne_next := (P.frameCoreFields C hmin).prev_ne_next i } }

/-- The center degree-six field is a consequence of Lemma 8 combinatorics
and the frame core, not a source premise. -/
theorem centerDegreeSix
    (P : FrameCoreLemma8CombinatoricsRows.{u} payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    forall i : M8ExtraIndex,
      Lemma8ExistenceConcrete.centerDegree
        (PointwiseSpine (payForCut := payForCut)
          (topologyArc := topologyArc) C hmin) i = 6 :=
  Lemma8ForbiddenDistinctConcrete.centerDegreeSix_of_lemma8Combinatorics_and_frameCore
    (S :=
      PointwiseSpine (payForCut := payForCut)
        (topologyArc := topologyArc) C hmin)
    (FrameCoreLemma8CombinatoricsRows.lemma8
      (payForCut := payForCut) (topologyArc := topologyArc) P C hmin)
    (FrameCoreLemma8CombinatoricsRows.frameCore
      (payForCut := payForCut) (topologyArc := topologyArc) P C hmin)

/-- The remaining finite no-collision family is also closed from the same
real source rows. -/
theorem remaining_three_noCollision
    (P : FrameCoreLemma8CombinatoricsRows.{u} payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    forall i : M8ExtraIndex,
      Not
        ((PointwiseSpine (payForCut := payForCut)
          (topologyArc := topologyArc) C hmin).leftP i =
            (PointwiseSpine (payForCut := payForCut)
              (topologyArc := topologyArc) C hmin).nextQ i) /\
      Not
        ((PointwiseSpine (payForCut := payForCut)
          (topologyArc := topologyArc) C hmin).rightP i =
            (PointwiseSpine (payForCut := payForCut)
              (topologyArc := topologyArc) C hmin).prevQ i) /\
      Not
        ((PointwiseSpine (payForCut := payForCut)
          (topologyArc := topologyArc) C hmin).prevQ i =
            (PointwiseSpine (payForCut := payForCut)
              (topologyArc := topologyArc) C hmin).nextQ i) :=
  Lemma8ForbiddenDistinctConcrete.remaining_three_noCollision_of_lemma8Combinatorics_and_frameCore
    (S :=
      PointwiseSpine (payForCut := payForCut)
        (topologyArc := topologyArc) C hmin)
    (FrameCoreLemma8CombinatoricsRows.lemma8
      (payForCut := payForCut) (topologyArc := topologyArc) P C hmin)
    (FrameCoreLemma8CombinatoricsRows.frameCore
      (payForCut := payForCut) (topologyArc := topologyArc) P C hmin)

/-- Convert the frame-core/Lemma 8 row into the W19 frame-row surface used by
the existing frame/cyclic-order assembly. -/
def toFrameRows
    (P : FrameCoreLemma8CombinatoricsRows.{u} payForCut topologyArc) :
    FrameRows.{u} payForCut topologyArc := fun C hmin =>
  { frameCore :=
      FrameCoreLemma8CombinatoricsRows.frameCore
        (payForCut := payForCut) (topologyArc := topologyArc) P C hmin
    extraNeighborCardTwo := fun i =>
      Lemma8ForbiddenDistinctConcrete.extraNeighborFinset_card_eq_two_of_lemma8Combinatorics
        (S :=
          PointwiseSpine (payForCut := payForCut)
            (topologyArc := topologyArc) C hmin)
        (FrameCoreLemma8CombinatoricsRows.lemma8
          (payForCut := payForCut) (topologyArc := topologyArc)
          P C hmin) i }

end FrameCoreLemma8CombinatoricsRows

abbrev GeneratedFrameRowsOfFrameCoreLemma8CombinatoricsRows
    (P : FrameCoreLemma8CombinatoricsRows.{u} payForCut topologyArc) :
    FrameRows.{u} payForCut topologyArc :=
  P.toFrameRows

/-! ## Actual finite-spine row source -/

/--
The finite `p_i/q_i` boundary-spine source rows for the selected
`topologyArc` boundary, with the actual finite frame core and Lemma 8
combinatorics on that same generated spine.
-/
structure FinitePQSpineFrameCoreLemma8Rows : Type (u + 1) where
  frameCoreFields :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8FinitePQSpineFrameCoreFields
          (PointwiseFinitePQSpineCertificate
            (topologyArc := topologyArc) C hmin)
          (PointwiseConnectedNoCutCertificate
            (payForCut := payForCut) C hmin)
          hmin
  lemma8 :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8Lemma8Combinatorics
          ((PointwiseFinitePQSpineCertificate
            (topologyArc := topologyArc) C hmin).toM8BoundarySpine
              (PointwiseConnectedNoCutCertificate
                (payForCut := payForCut) C hmin)
              hmin)

def finitePQSpineFrameCoreOfFields
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        (PointwiseFinitePQSpineCertificate
          (topologyArc := topologyArc) C hmin)
        (PointwiseConnectedNoCutCertificate
          (payForCut := payForCut) C hmin)
        hmin) :
    M8FourForbiddenFrameCore
      (PointwiseSpine (payForCut := payForCut)
        (topologyArc := topologyArc) C hmin) :=
  { core := fun i =>
      { prev_adj := frameCoreFields.prev_adj i
        next_adj := frameCoreFields.next_adj i
        left_ne_next := frameCoreFields.left_ne_next i
        right_ne_prev := frameCoreFields.right_ne_prev i
        prev_ne_next := frameCoreFields.prev_ne_next i } }

namespace FinitePQSpineFrameCoreLemma8Rows

variable (P : FinitePQSpineFrameCoreLemma8Rows.{u} payForCut topologyArc)

/-- The four-forbidden frame core generated directly from the finite
`p_i/q_i` spine fields. -/
def toFrameCore
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    M8FourForbiddenFrameCore
      (PointwiseSpine (payForCut := payForCut)
        (topologyArc := topologyArc) C hmin) :=
  finitePQSpineFrameCoreOfFields
    (payForCut := payForCut) (topologyArc := topologyArc)
    C hmin (P.frameCoreFields C hmin)

/-- Forget the actual finite-spine source rows to the W32 frame-core/Lemma 8
row surface keyed to `PointwiseSpine`. -/
def toFrameCoreLemma8CombinatoricsRows :
    FrameCoreLemma8CombinatoricsRows.{u} payForCut topologyArc where
  frameCoreFields := fun C hmin => P.frameCoreFields C hmin
  lemma8 := fun C hmin => P.lemma8 C hmin

def generatedFrameRows :
    FrameRows.{u} payForCut topologyArc :=
  (FinitePQSpineFrameCoreLemma8Rows.toFrameCoreLemma8CombinatoricsRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P).toFrameRows

end FinitePQSpineFrameCoreLemma8Rows

/-! ## Reduction to generated finite-spine cyclic order -/

def finitePQSpineGeneratedExtraNeighborData
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        (PointwiseFinitePQSpineCertificate
          (topologyArc := topologyArc) C hmin)
        (PointwiseConnectedNoCutCertificate
          (payForCut := payForCut) C hmin)
        hmin)
    (extraNeighborCardTwo :
      forall i : M8ExtraIndex,
        (Lemma8ExistenceConcrete.extraNeighborFinset
          (PointwiseSpine (payForCut := payForCut)
            (topologyArc := topologyArc) C hmin) i).card = 2) :
    Lemma8NeighborExtractionConcrete.M8ExtraNeighborData
      (PointwiseSpine (payForCut := payForCut)
        (topologyArc := topologyArc) C hmin) :=
  Lemma8GeometryFieldsW18.extraNeighborDataOfFrameCoreAndExtraCardTwo
    (finitePQSpineFrameCoreOfFields
      (payForCut := payForCut) (topologyArc := topologyArc)
      C hmin frameCoreFields)
    extraNeighborCardTwo

def finitePQSpineGeneratedCyclicOrderTransport
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        (PointwiseFinitePQSpineCertificate
          (topologyArc := topologyArc) C hmin)
        (PointwiseConnectedNoCutCertificate
          (payForCut := payForCut) C hmin)
        hmin}
    {extraNeighborCardTwo extraNeighborCardTwo' :
      forall i : M8ExtraIndex,
        (Lemma8ExistenceConcrete.extraNeighborFinset
          (PointwiseSpine (payForCut := payForCut)
            (topologyArc := topologyArc) C hmin) i).card = 2}
    (cyclicRows :
      Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
        (finitePQSpineGeneratedExtraNeighborData
          (payForCut := payForCut) (topologyArc := topologyArc)
          C hmin frameCoreFields extraNeighborCardTwo)) :
    Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
      (finitePQSpineGeneratedExtraNeighborData
        (payForCut := payForCut) (topologyArc := topologyArc)
        C hmin frameCoreFields extraNeighborCardTwo') := by
  have hcard : extraNeighborCardTwo = extraNeighborCardTwo' := by
    funext i
    exact Subsingleton.elim _ _
  cases hcard
  exact cyclicRows

def finitePQSpineGeneratedCyclicOrderTransportFrameCoreFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {frameCoreFields frameCoreFields' :
      M8FinitePQSpineFrameCoreFields
        (PointwiseFinitePQSpineCertificate
          (topologyArc := topologyArc) C hmin)
        (PointwiseConnectedNoCutCertificate
          (payForCut := payForCut) C hmin)
        hmin}
    {extraNeighborCardTwo extraNeighborCardTwo' :
      forall i : M8ExtraIndex,
        (Lemma8ExistenceConcrete.extraNeighborFinset
          (PointwiseSpine (payForCut := payForCut)
            (topologyArc := topologyArc) C hmin) i).card = 2}
    (cyclicRows :
      Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
        (finitePQSpineGeneratedExtraNeighborData
          (payForCut := payForCut) (topologyArc := topologyArc)
          C hmin frameCoreFields extraNeighborCardTwo)) :
    Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
      (finitePQSpineGeneratedExtraNeighborData
        (payForCut := payForCut) (topologyArc := topologyArc)
        C hmin frameCoreFields' extraNeighborCardTwo') := by
  have hfields : frameCoreFields = frameCoreFields' :=
    Subsingleton.elim _ _
  have hcard : extraNeighborCardTwo = extraNeighborCardTwo' := by
    funext i
    exact Subsingleton.elim _ _
  cases hfields
  cases hcard
  exact cyclicRows

abbrev PointwiseFinitePQSpineRawFrameCoreFacts
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Prop :=
  (forall i : M8ExtraIndex,
    (GraphBridge.unitDistanceLocalGraph C).Adj
      ((PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin).q
          (m8TriangleIndexOfExtra i))
      ((PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin).q
          (m8TriangleIndexPrevOfExtra i))) /\
  (forall i : M8ExtraIndex,
    (GraphBridge.unitDistanceLocalGraph C).Adj
      ((PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin).q
          (m8TriangleIndexOfExtra i))
      ((PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin).q
          (m8TriangleIndexNextOfExtra i))) /\
  (forall i : M8ExtraIndex,
    Not
      ((PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin).p
          (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
        (PointwiseFinitePQSpineCertificate
          (topologyArc := topologyArc) C hmin).q
            (m8TriangleIndexNextOfExtra i))) /\
  (forall i : M8ExtraIndex,
    Not
      ((PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin).p
          (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
        (PointwiseFinitePQSpineCertificate
          (topologyArc := topologyArc) C hmin).q
            (m8TriangleIndexPrevOfExtra i))) /\
  (forall i : M8ExtraIndex,
    Not
      ((PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin).q
          (m8TriangleIndexPrevOfExtra i) =
        (PointwiseFinitePQSpineCertificate
          (topologyArc := topologyArc) C hmin).q
            (m8TriangleIndexNextOfExtra i)))

theorem finitePQSpineFrameCoreFields_iff_rawFacts
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    M8FinitePQSpineFrameCoreFields
        (PointwiseFinitePQSpineCertificate
          (topologyArc := topologyArc) C hmin)
        (PointwiseConnectedNoCutCertificate
          (payForCut := payForCut) C hmin)
        hmin <->
      PointwiseFinitePQSpineRawFrameCoreFacts
        (topologyArc := topologyArc) C hmin :=
  M8FinitePQSpineFrameCoreFields.fields_iff_rawFinitePQFacts
    (K :=
      PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin)
    (connectedNoCut :=
      PointwiseConnectedNoCutCertificate
        (payForCut := payForCut) C hmin)
    (hmin := hmin)

def finitePQSpineFrameCoreFieldsOfRawFacts
    (rawFacts :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseFinitePQSpineRawFrameCoreFacts
            (topologyArc := topologyArc) C hmin) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8FinitePQSpineFrameCoreFields
          (PointwiseFinitePQSpineCertificate
            (topologyArc := topologyArc) C hmin)
          (PointwiseConnectedNoCutCertificate
            (payForCut := payForCut) C hmin)
          hmin := by
  intro n C hmin
  exact
    (finitePQSpineFrameCoreFields_iff_rawFacts
      (payForCut := payForCut) (topologyArc := topologyArc)
      C hmin).2 (rawFacts C hmin)

theorem rawFactsOfFinitePQSpineFrameCoreFields
    (frameCoreFields :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineFrameCoreFields
            (PointwiseFinitePQSpineCertificate
              (topologyArc := topologyArc) C hmin)
            (PointwiseConnectedNoCutCertificate
              (payForCut := payForCut) C hmin)
            hmin) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseFinitePQSpineRawFrameCoreFacts
          (topologyArc := topologyArc) C hmin := by
  intro n C hmin
  exact
    (finitePQSpineFrameCoreFields_iff_rawFacts
      (payForCut := payForCut) (topologyArc := topologyArc)
      C hmin).1 (frameCoreFields C hmin)

/--
Finite-spine source rows where the Lemma 8 combinatorics and selected cyclic
rows are both generated from the same raw finite `p_i/q_i` spine.
-/
structure FinitePQSpineGeneratedOrderRows : Type (u + 1) where
  frameCoreFields :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8FinitePQSpineFrameCoreFields
          (PointwiseFinitePQSpineCertificate
            (topologyArc := topologyArc) C hmin)
          (PointwiseConnectedNoCutCertificate
            (payForCut := payForCut) C hmin)
          hmin
  extraNeighborCardTwo :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        forall i : M8ExtraIndex,
          (Lemma8ExistenceConcrete.extraNeighborFinset
            (PointwiseSpine (payForCut := payForCut)
              (topologyArc := topologyArc) C hmin) i).card = 2
  generatedCyclicRows :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
          (finitePQSpineGeneratedExtraNeighborData
            (payForCut := payForCut) (topologyArc := topologyArc)
            C hmin (frameCoreFields C hmin)
            (extraNeighborCardTwo C hmin))

namespace FinitePQSpineGeneratedOrderRows

variable (P : FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc)

def lemma8
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    M8Lemma8Combinatorics
      ((PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin).toM8BoundarySpine
          (PointwiseConnectedNoCutCertificate
            (payForCut := payForCut) C hmin)
          hmin) :=
  (finitePQSpineGeneratedExtraNeighborData
    (payForCut := payForCut) (topologyArc := topologyArc)
    C hmin (P.frameCoreFields C hmin)
    (P.extraNeighborCardTwo C hmin)).toLemma8Combinatorics
      (P.generatedCyclicRows C hmin)

def toFinitePQSpineFrameCoreLemma8Rows :
    FinitePQSpineFrameCoreLemma8Rows.{u} payForCut topologyArc where
  frameCoreFields := fun C hmin => P.frameCoreFields C hmin
  lemma8 := fun C hmin =>
    FinitePQSpineGeneratedOrderRows.lemma8
      (payForCut := payForCut) (topologyArc := topologyArc) P C hmin

def toGeneratedCyclicRows :
    NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc
      (FinitePQSpineFrameCoreLemma8Rows.generatedFrameRows
        (payForCut := payForCut) (topologyArc := topologyArc)
        P.toFinitePQSpineFrameCoreLemma8Rows) := by
  intro n C hmin
  exact
    finitePQSpineGeneratedCyclicOrderTransport
      (payForCut := payForCut) (topologyArc := topologyArc)
      (C := C) (hmin := hmin)
      (frameCoreFields := P.frameCoreFields C hmin)
      (extraNeighborCardTwo := P.extraNeighborCardTwo C hmin)
      (P.generatedCyclicRows C hmin)

end FinitePQSpineGeneratedOrderRows

theorem finitePQSpineGeneratedOrderRows_rawFacts
    (P : FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseFinitePQSpineRawFrameCoreFacts
          (topologyArc := topologyArc) C hmin :=
  rawFactsOfFinitePQSpineFrameCoreFields
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.frameCoreFields

def finitePQSpineGeneratedOrderRowsOfRawFacts
    (rawFacts :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseFinitePQSpineRawFrameCoreFacts
            (topologyArc := topologyArc) C hmin)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine (payForCut := payForCut)
                (topologyArc := topologyArc) C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut := payForCut) (topologyArc := topologyArc)
              C hmin
              (finitePQSpineFrameCoreFieldsOfRawFacts
                (payForCut := payForCut) (topologyArc := topologyArc)
                rawFacts C hmin)
              (extraNeighborCardTwo C hmin))) :
    FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc where
  frameCoreFields :=
    finitePQSpineFrameCoreFieldsOfRawFacts
      (payForCut := payForCut) (topologyArc := topologyArc)
      rawFacts
  extraNeighborCardTwo := extraNeighborCardTwo
  generatedCyclicRows := generatedCyclicRows

theorem finitePQSpineGeneratedOrderRows_nonempty_of_rawFacts
    (rawFacts :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseFinitePQSpineRawFrameCoreFacts
            (topologyArc := topologyArc) C hmin)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine (payForCut := payForCut)
                (topologyArc := topologyArc) C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut := payForCut) (topologyArc := topologyArc)
              C hmin
              (finitePQSpineFrameCoreFieldsOfRawFacts
                (payForCut := payForCut) (topologyArc := topologyArc)
                rawFacts C hmin)
              (extraNeighborCardTwo C hmin))) :
    Nonempty (FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (finitePQSpineGeneratedOrderRowsOfRawFacts
      (payForCut := payForCut) (topologyArc := topologyArc)
      rawFacts extraNeighborCardTwo generatedCyclicRows)

theorem finitePQSpineFrameCoreLemma8Rows_nonempty_of_generatedOrderRows
    (P : FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :
    Nonempty
      (FinitePQSpineFrameCoreLemma8Rows.{u} payForCut topologyArc) :=
  Nonempty.intro P.toFinitePQSpineFrameCoreLemma8Rows

theorem finitePQSpineGeneratedCyclicRows_nonempty_of_generatedOrderRows
    (P : FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :
    Nonempty
      (NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc
        (FinitePQSpineFrameCoreLemma8Rows.generatedFrameRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          P.toFinitePQSpineFrameCoreLemma8Rows)) :=
  Nonempty.intro P.toGeneratedCyclicRows

/--
Instantiate the W32 finite-spine rows from the actual selected finite boundary
walk carrying frame-core facts.  The equality premise records that the
selected `topologyArc` boundary arc is precisely the honest finite walk's
boundary certificate.
-/
def finitePQSpineFrameCoreLemma8RowsOfFiniteWalkFrameCoreData
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D := (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut := payForCut) C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            (topologyArc.row C hmin).boundaryArc)
    (lemma8 :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8Lemma8Combinatorics
            (((finiteWalkFrameCore C hmin).toFinitePQSpineCertificate)
              |>.toM8BoundarySpine
                (PointwiseConnectedNoCutCertificate
                  (payForCut := payForCut) C hmin)
                hmin)) :
    FinitePQSpineFrameCoreLemma8Rows.{u} payForCut topologyArc where
  frameCoreFields := by
    intro n C hmin
    let W := finiteWalkFrameCore C hmin
    have hW :
        M8FinitePQSpineFrameCoreFields
          W.toFinitePQSpineCertificate
          (PointwiseConnectedNoCutCertificate
            (payForCut := payForCut) C hmin)
          hmin :=
      W.frameCoreFields_holds
    have hcert :
        W.toFinitePQSpineCertificate =
          (topologyArc.row C hmin).boundaryArc.toFinitePQSpineCertificate := by
      exact
        congrArg
          BoundaryArcW12.M8BoundaryArcCertificate.toFinitePQSpineCertificate
          (boundaryArc_eq C hmin)
    change
      M8FinitePQSpineFrameCoreFields
        ((topologyArc.row C hmin).boundaryArc.toFinitePQSpineCertificate)
        (PointwiseConnectedNoCutCertificate
          (payForCut := payForCut) C hmin)
        hmin
    rw [← hcert]
    exact hW
  lemma8 := by
    intro n C hmin
    let W := finiteWalkFrameCore C hmin
    have hcert :
        W.toFinitePQSpineCertificate =
          (topologyArc.row C hmin).boundaryArc.toFinitePQSpineCertificate := by
      exact
        congrArg
          BoundaryArcW12.M8BoundaryArcCertificate.toFinitePQSpineCertificate
          (boundaryArc_eq C hmin)
    change
      M8Lemma8Combinatorics
        (((topologyArc.row C hmin).boundaryArc.toFinitePQSpineCertificate)
          |>.toM8BoundarySpine
            (PointwiseConnectedNoCutCertificate
              (payForCut := payForCut) C hmin)
            hmin)
    rw [← hcert]
    exact lemma8 C hmin

theorem finitePQSpineFrameCoreLemma8Rows_nonempty_of_finiteWalkFrameCoreData
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D := (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut := payForCut) C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            (topologyArc.row C hmin).boundaryArc)
    (lemma8 :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8Lemma8Combinatorics
            (((finiteWalkFrameCore C hmin).toFinitePQSpineCertificate)
              |>.toM8BoundarySpine
                (PointwiseConnectedNoCutCertificate
                  (payForCut := payForCut) C hmin)
                hmin)) :
    Nonempty
      (FinitePQSpineFrameCoreLemma8Rows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (finitePQSpineFrameCoreLemma8RowsOfFiniteWalkFrameCoreData
      (payForCut := payForCut) (topologyArc := topologyArc)
      finiteWalkFrameCore boundaryArc_eq lemma8)

def finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D := (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut := payForCut) C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            (topologyArc.row C hmin).boundaryArc) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8FinitePQSpineFrameCoreFields
          (PointwiseFinitePQSpineCertificate
            (topologyArc := topologyArc) C hmin)
          (PointwiseConnectedNoCutCertificate
            (payForCut := payForCut) C hmin)
          hmin := by
  intro n C hmin
  let W := finiteWalkFrameCore C hmin
  have hW :
      M8FinitePQSpineFrameCoreFields
        W.toFinitePQSpineCertificate
        (PointwiseConnectedNoCutCertificate
          (payForCut := payForCut) C hmin)
        hmin :=
    W.frameCoreFields_holds
  have hcert :
      W.toFinitePQSpineCertificate =
        (topologyArc.row C hmin).boundaryArc.toFinitePQSpineCertificate := by
    exact
      congrArg
        BoundaryArcW12.M8BoundaryArcCertificate.toFinitePQSpineCertificate
        (boundaryArc_eq C hmin)
  change
    M8FinitePQSpineFrameCoreFields
      ((topologyArc.row C hmin).boundaryArc.toFinitePQSpineCertificate)
      (PointwiseConnectedNoCutCertificate
        (payForCut := payForCut) C hmin)
      hmin
  rw [hcert.symm]
  exact hW

/-- The exact non-cyclic finite-walk source still needed after
`BoundaryArcFiniteWalkFrameCoreData`: center-degree six on the same generated
finite-walk spine supplies cardinality two for the generated extra-neighbor
finset.  The `boundaryArc_eq` premise transports the result back to the
selected topology arc. -/
def finiteWalkFrameCoreExtraNeighborCardTwoOfCenterDegreeSix
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D := (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut := payForCut) C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            (topologyArc.row C hmin).boundaryArc)
    (centerDegreeSix :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            Lemma8ExistenceConcrete.centerDegree
              (((finiteWalkFrameCore C hmin).toFinitePQSpineCertificate)
                |>.toM8BoundarySpine
                  (PointwiseConnectedNoCutCertificate
                    (payForCut := payForCut) C hmin)
                  hmin) i = 6) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        forall i : M8ExtraIndex,
          (Lemma8ExistenceConcrete.extraNeighborFinset
            (PointwiseSpine (payForCut := payForCut)
              (topologyArc := topologyArc) C hmin) i).card = 2 := by
  intro n C hmin i
  let W := finiteWalkFrameCore C hmin
  let connectedNoCut :=
    PointwiseConnectedNoCutCertificate
      (payForCut := payForCut) C hmin
  have hcore :
      M8FourForbiddenFrameCore
        (W.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin) := by
    let fields := W.frameCoreFields_holds
    exact
      { core := fun j =>
          { prev_adj := fields.prev_adj j
            next_adj := fields.next_adj j
            left_ne_next := fields.left_ne_next j
            right_ne_prev := fields.right_ne_prev j
            prev_ne_next := fields.prev_ne_next j } }
  have hcard :
      (Lemma8ExistenceConcrete.extraNeighborFinset
        (W.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin) i).card = 2 :=
    (Lemma8GeometryFieldsW18.centerDegreeSix_iff_extraNeighborCardTwo
      (S :=
        W.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin) hcore).1
      (centerDegreeSix C hmin) i
  have hcert :
      W.toFinitePQSpineCertificate =
        (topologyArc.row C hmin).boundaryArc.toFinitePQSpineCertificate := by
    exact
      congrArg
        BoundaryArcW12.M8BoundaryArcCertificate.toFinitePQSpineCertificate
        (boundaryArc_eq C hmin)
  change
    (Lemma8ExistenceConcrete.extraNeighborFinset
      (((topologyArc.row C hmin).boundaryArc.toFinitePQSpineCertificate)
        |>.toM8BoundarySpine connectedNoCut hmin) i).card = 2
  rw [← hcert]
  exact hcard

def finitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreData
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D := (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut := payForCut) C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            (topologyArc.row C hmin).boundaryArc)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine (payForCut := payForCut)
                (topologyArc := topologyArc) C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut := payForCut) (topologyArc := topologyArc)
              C hmin
              (finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
                (payForCut := payForCut) (topologyArc := topologyArc)
                finiteWalkFrameCore boundaryArc_eq C hmin)
              (extraNeighborCardTwo C hmin))) :
    FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc where
  frameCoreFields :=
    finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
      (payForCut := payForCut) (topologyArc := topologyArc)
      finiteWalkFrameCore boundaryArc_eq
  extraNeighborCardTwo := extraNeighborCardTwo
  generatedCyclicRows := generatedCyclicRows

def finitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSix
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D := (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut := payForCut) C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            (topologyArc.row C hmin).boundaryArc)
    (centerDegreeSix :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            Lemma8ExistenceConcrete.centerDegree
              (((finiteWalkFrameCore C hmin).toFinitePQSpineCertificate)
                |>.toM8BoundarySpine
                  (PointwiseConnectedNoCutCertificate
                    (payForCut := payForCut) C hmin)
                  hmin) i = 6)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut := payForCut) (topologyArc := topologyArc)
              C hmin
              (finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
                (payForCut := payForCut) (topologyArc := topologyArc)
                finiteWalkFrameCore boundaryArc_eq C hmin)
              (finiteWalkFrameCoreExtraNeighborCardTwoOfCenterDegreeSix
                (payForCut := payForCut) (topologyArc := topologyArc)
                finiteWalkFrameCore boundaryArc_eq centerDegreeSix
                C hmin))) :
    FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc :=
  finitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreData
    (payForCut := payForCut) (topologyArc := topologyArc)
    finiteWalkFrameCore boundaryArc_eq
    (finiteWalkFrameCoreExtraNeighborCardTwoOfCenterDegreeSix
      (payForCut := payForCut) (topologyArc := topologyArc)
      finiteWalkFrameCore boundaryArc_eq centerDegreeSix)
    generatedCyclicRows

theorem finitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreData
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D := (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut := payForCut) C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            (topologyArc.row C hmin).boundaryArc)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine (payForCut := payForCut)
                (topologyArc := topologyArc) C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut := payForCut) (topologyArc := topologyArc)
              C hmin
              (finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
                (payForCut := payForCut) (topologyArc := topologyArc)
                finiteWalkFrameCore boundaryArc_eq C hmin)
              (extraNeighborCardTwo C hmin))) :
    Nonempty (FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (finitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreData
      (payForCut := payForCut) (topologyArc := topologyArc)
      finiteWalkFrameCore boundaryArc_eq extraNeighborCardTwo
      generatedCyclicRows)

theorem finitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreCenterDegreeSix
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D := (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut := payForCut) C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            (topologyArc.row C hmin).boundaryArc)
    (centerDegreeSix :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            Lemma8ExistenceConcrete.centerDegree
              (((finiteWalkFrameCore C hmin).toFinitePQSpineCertificate)
                |>.toM8BoundarySpine
                  (PointwiseConnectedNoCutCertificate
                    (payForCut := payForCut) C hmin)
                  hmin) i = 6)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut := payForCut) (topologyArc := topologyArc)
              C hmin
              (finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
                (payForCut := payForCut) (topologyArc := topologyArc)
                finiteWalkFrameCore boundaryArc_eq C hmin)
              (finiteWalkFrameCoreExtraNeighborCardTwoOfCenterDegreeSix
                (payForCut := payForCut) (topologyArc := topologyArc)
                finiteWalkFrameCore boundaryArc_eq centerDegreeSix
                C hmin))) :
    Nonempty (FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (finitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSix
      (payForCut := payForCut) (topologyArc := topologyArc)
      finiteWalkFrameCore boundaryArc_eq centerDegreeSix
      generatedCyclicRows)

/-! ## Generated-order rows from finite geometry rows -/

def finitePQSpineFrameCoreFieldsOfFrameCardinalityRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (R : FrameCardinalityRow.{u} payForCut topologyArc C hmin) :
    M8FinitePQSpineFrameCoreFields
      (PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin)
      (PointwiseConnectedNoCutCertificate
        (payForCut := payForCut) C hmin)
      hmin :=
  Lemma8ForbiddenDistinctConcrete.FinitePQSpineRoute.toFinitePQSpineFrameCoreFields
    (K :=
      PointwiseFinitePQSpineCertificate
        (topologyArc := topologyArc) C hmin)
    (connectedNoCut :=
      PointwiseConnectedNoCutCertificate
        (payForCut := payForCut) C hmin)
    (hmin := hmin)
    R.frameCore

def finitePQSpineGeneratedExtraNeighborDataOfFrameCardinalityRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (R : FrameCardinalityRow.{u} payForCut topologyArc C hmin) :
    Lemma8NeighborExtractionConcrete.M8ExtraNeighborData
      (PointwiseSpine (payForCut := payForCut)
        (topologyArc := topologyArc) C hmin) :=
  finitePQSpineGeneratedExtraNeighborData
    (payForCut := payForCut) (topologyArc := topologyArc)
    C hmin
    (finitePQSpineFrameCoreFieldsOfFrameCardinalityRow
      (payForCut := payForCut) (topologyArc := topologyArc)
      C hmin R)
    R.extraNeighborCardTwo

theorem finitePQSpineGeneratedExtraNeighborDataOfFrameCardinalityRow_eq
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (R : FrameCardinalityRow.{u} payForCut topologyArc C hmin) :
    finitePQSpineGeneratedExtraNeighborDataOfFrameCardinalityRow
      (payForCut := payForCut) (topologyArc := topologyArc)
      C hmin R = R.extraNeighborData := by
  cases R with
  | mk frameCore extraNeighborCardTwo =>
      cases frameCore with
      | mk core =>
          rfl

def finitePQSpineGeneratedCyclicRowsOfFiniteGeometryRows
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (R : FiniteGeometryRows.{u} payForCut topologyArc C hmin) :
    Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
      (finitePQSpineGeneratedExtraNeighborDataOfFrameCardinalityRow
        (payForCut := payForCut) (topologyArc := topologyArc)
        C hmin R.frameCardinality) :=
  (finitePQSpineGeneratedExtraNeighborDataOfFrameCardinalityRow_eq
    (payForCut := payForCut) (topologyArc := topologyArc)
    C hmin R.frameCardinality).symm ▸
      R.positiveOrder.toNeighborCyclicOrder

def finitePQSpineGeneratedOrderRowsOfUniformFiniteGeometryRows
    (rows : UniformFiniteGeometryRows.{u} payForCut topologyArc) :
    FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc where
  frameCoreFields := fun C hmin =>
    finitePQSpineFrameCoreFieldsOfFrameCardinalityRow
      (payForCut := payForCut) (topologyArc := topologyArc)
      C hmin (rows.row C hmin).frameCardinality
  extraNeighborCardTwo := fun C hmin =>
    (rows.row C hmin).frameCardinality.extraNeighborCardTwo
  generatedCyclicRows := fun C hmin =>
    finitePQSpineGeneratedCyclicRowsOfFiniteGeometryRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      C hmin (rows.row C hmin)

theorem finitePQSpineGeneratedOrderRows_nonempty_of_uniformFiniteGeometryRows
    (rows : UniformFiniteGeometryRows.{u} payForCut topologyArc) :
    Nonempty (FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (finitePQSpineGeneratedOrderRowsOfUniformFiniteGeometryRows
      (payForCut := payForCut) (topologyArc := topologyArc) rows)

/-- W32 frame/cyclic source package generated from the real frame-core plus
Lemma 8 combinatorics rows.  Cyclic rows are keyed to the frame rows derived
from those data. -/
structure FrameCoreLemma8GeneratedCyclicRowPackage : Type (u + 1) where
  rows : FrameCoreLemma8CombinatoricsRows.{u} payForCut topologyArc
  generatedCyclicRows :
    NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc
      (GeneratedFrameRowsOfFrameCoreLemma8CombinatoricsRows
        (payForCut := payForCut) (topologyArc := topologyArc) rows)

namespace FrameCoreLemma8GeneratedCyclicRowPackage

def generatedFrameRows
    (P : FrameCoreLemma8GeneratedCyclicRowPackage.{u}
      payForCut topologyArc) :
    FrameRows.{u} payForCut topologyArc :=
  GeneratedFrameRowsOfFrameCoreLemma8CombinatoricsRows
    (payForCut := payForCut) (topologyArc := topologyArc) P.rows

def toFrameCyclicOrderSourcePackage
    (P : FrameCoreLemma8GeneratedCyclicRowPackage.{u}
      payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc where
  frameRows := P.generatedFrameRows
  cyclicRows := P.generatedCyclicRows

def toUniformFrameCyclicOrderRows
    (P : FrameCoreLemma8GeneratedCyclicRowPackage.{u}
      payForCut topologyArc) :
    UniformFrameCyclicOrderRows.{u} payForCut topologyArc :=
  P.toFrameCyclicOrderSourcePackage.toUniformFrameCyclicOrderRows

def toUniformFiniteGeometryRows
    (P : FrameCoreLemma8GeneratedCyclicRowPackage.{u}
      payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  P.toFrameCyclicOrderSourcePackage.toUniformFiniteGeometryRows

def toExactRemainingPackage
    (P : FrameCoreLemma8GeneratedCyclicRowPackage.{u}
      payForCut topologyArc) :
    ExactRemainingPackage.{u} payForCut topologyArc :=
  P.toFrameCyclicOrderSourcePackage.toExactRemainingPackage

def toGeometryFieldFamily
    (P : FrameCoreLemma8GeneratedCyclicRowPackage.{u}
      payForCut topologyArc) :
    GeometryFieldFamily.{u} payForCut topologyArc :=
  P.toFrameCyclicOrderSourcePackage.toGeometryFieldFamily

end FrameCoreLemma8GeneratedCyclicRowPackage

theorem sourcePackage_nonempty_of_frameCoreLemma8GeneratedCyclicRows
    (P : FrameCoreLemma8GeneratedCyclicRowPackage.{u}
      payForCut topologyArc) :
    Nonempty (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :=
  Nonempty.intro P.toFrameCyclicOrderSourcePackage

theorem uniformFiniteGeometryRows_nonempty_of_frameCoreLemma8GeneratedCyclicRows
    (P : FrameCoreLemma8GeneratedCyclicRowPackage.{u}
      payForCut topologyArc) :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
  Nonempty.intro P.toUniformFiniteGeometryRows

theorem exactRemainingPackage_nonempty_of_frameCoreLemma8GeneratedCyclicRows
    (P : FrameCoreLemma8GeneratedCyclicRowPackage.{u}
      payForCut topologyArc) :
    Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) :=
  Nonempty.intro P.toExactRemainingPackage

def frameCoreLemma8GeneratedCyclicRowPackageOfFinitePQSpineRows
    (finiteRows :
      FinitePQSpineFrameCoreLemma8Rows.{u} payForCut topologyArc)
    (generatedCyclicRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc
        (FinitePQSpineFrameCoreLemma8Rows.generatedFrameRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          finiteRows)) :
    FrameCoreLemma8GeneratedCyclicRowPackage.{u} payForCut topologyArc where
  rows := finiteRows.toFrameCoreLemma8CombinatoricsRows
  generatedCyclicRows := generatedCyclicRows

/-- Actual W32 frame/cyclic source package from the finite `p_i/q_i`
boundary spine, its frame-core/Lemma 8 rows, and cyclic rows keyed to the
generated frame rows. -/
def frameCyclicOrderSourcePackageOfFinitePQSpineRows
    (finiteRows :
      FinitePQSpineFrameCoreLemma8Rows.{u} payForCut topologyArc)
    (generatedCyclicRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc
        (FinitePQSpineFrameCoreLemma8Rows.generatedFrameRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          finiteRows)) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc :=
  (frameCoreLemma8GeneratedCyclicRowPackageOfFinitePQSpineRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    finiteRows generatedCyclicRows).toFrameCyclicOrderSourcePackage

/-- Generated-order finite-spine rows are already the compatible pair of
finite frame-core rows and cyclic rows keyed to the generated frame. -/
def frameCoreLemma8GeneratedCyclicRowPackageOfFinitePQSpineGeneratedOrderRows
    (rows : FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :
    FrameCoreLemma8GeneratedCyclicRowPackage.{u} payForCut topologyArc :=
  frameCoreLemma8GeneratedCyclicRowPackageOfFinitePQSpineRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    rows.toFinitePQSpineFrameCoreLemma8Rows rows.toGeneratedCyclicRows

/-- Direct W32 frame/cyclic source package from finite `p_i/q_i` rows whose
cyclic order was generated from the same finite spine. -/
def frameCyclicOrderSourcePackageOfFinitePQSpineGeneratedOrderRows
    (rows : FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc :=
  (frameCoreLemma8GeneratedCyclicRowPackageOfFinitePQSpineGeneratedOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    rows).toFrameCyclicOrderSourcePackage

theorem sourcePackage_nonempty_of_finitePQSpineRows
    (finiteRows :
      FinitePQSpineFrameCoreLemma8Rows.{u} payForCut topologyArc)
    (generatedCyclicRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc
        (FinitePQSpineFrameCoreLemma8Rows.generatedFrameRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          finiteRows)) :
    Nonempty (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (frameCyclicOrderSourcePackageOfFinitePQSpineRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      finiteRows generatedCyclicRows)

theorem sourcePackage_nonempty_of_finitePQSpineGeneratedOrderRows
    (rows : FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :
    Nonempty (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (frameCyclicOrderSourcePackageOfFinitePQSpineGeneratedOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      rows)

theorem uniformFiniteGeometryRows_nonempty_of_finitePQSpineRows
    (finiteRows :
      FinitePQSpineFrameCoreLemma8Rows.{u} payForCut topologyArc)
    (generatedCyclicRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc
        (FinitePQSpineFrameCoreLemma8Rows.generatedFrameRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          finiteRows)) :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    ((frameCyclicOrderSourcePackageOfFinitePQSpineRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      finiteRows generatedCyclicRows).toUniformFiniteGeometryRows)

theorem uniformFiniteGeometryRows_nonempty_of_finitePQSpineGeneratedOrderRows
    (rows : FinitePQSpineGeneratedOrderRows.{u} payForCut topologyArc) :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    ((frameCyclicOrderSourcePackageOfFinitePQSpineGeneratedOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      rows).toUniformFiniteGeometryRows)

/-! ## Exact degree-six generated cyclic-row blocker -/

abbrev GeneratedFrameRowsOfDegreeSixRows
    (degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc) :
    FrameRows.{u} payForCut topologyArc :=
  FrameCyclicOrderRowsW30.frameRowsOfDegreeSixNoncyclicRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    degreeRows

/-- The exact degree-six generated cyclic-row route: cyclic rows are keyed to
the frame rows generated from the degree-six/non-cyclic rows. -/
structure DegreeSixGeneratedCyclicRowPackage : Type (u + 1) where
  degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc
  generatedCyclicRows :
    NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc
      (GeneratedFrameRowsOfDegreeSixRows.{u}
        payForCut topologyArc degreeRows)

abbrev ExactDegreeSixGeneratedCyclicRowsBlocker : Prop :=
  exists degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc,
    Nonempty
      (NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc
        (GeneratedFrameRowsOfDegreeSixRows.{u}
          payForCut topologyArc degreeRows))

namespace DegreeSixGeneratedCyclicRowPackage

def generatedFrameRows
    (P : DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) :
    FrameRows.{u} payForCut topologyArc :=
  GeneratedFrameRowsOfDegreeSixRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.degreeRows

def toFrameCyclicOrderSourcePackage
    (P : DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) :
    FrameCyclicOrderSourcePackage.{u} payForCut topologyArc where
  frameRows := P.generatedFrameRows
  cyclicRows := P.generatedCyclicRows

def toDegreeSixNeighborCyclicOrderRows
    (P : DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) :
    DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc :=
  FrameCyclicOrderRowsW30.degreeSixNeighborCyclicOrderRowsOfGeneratedFrameCyclicRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.degreeRows P.generatedCyclicRows

def toGeneratedFrameCyclicSourceRows
    (P : DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) :
    CyclicOrderRowsInhabitationW31.GeneratedFrameCyclicSourceRows.{u}
      payForCut topologyArc where
  degreeRows := P.degreeRows
  neighborCyclicOrderRows := P.generatedCyclicRows

def toUniformFrameCyclicOrderRows
    (P : DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) :
    UniformFrameCyclicOrderRows.{u} payForCut topologyArc :=
  P.toFrameCyclicOrderSourcePackage.toUniformFrameCyclicOrderRows

def toUniformFiniteGeometryRows
    (P : DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  P.toFrameCyclicOrderSourcePackage.toUniformFiniteGeometryRows

def toExactRemainingPackage
    (P : DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) :
    ExactRemainingPackage.{u} payForCut topologyArc :=
  P.toFrameCyclicOrderSourcePackage.toExactRemainingPackage

def toGeometryFieldFamily
    (P : DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) :
    GeometryFieldFamily.{u} payForCut topologyArc :=
  P.toFrameCyclicOrderSourcePackage.toGeometryFieldFamily

end DegreeSixGeneratedCyclicRowPackage

def degreeSixGeneratedCyclicRowPackageOfDegreeSixNeighborRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc :=
  { degreeRows := P.degreeRows
    generatedCyclicRows := P.neighborCyclicOrderRows }

def degreeSixNeighborRowsOfDegreeSixGeneratedCyclicRowPackage
    (P : DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) :
    DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc :=
  P.toDegreeSixNeighborCyclicOrderRows

theorem degreeSixGeneratedCyclicRowPackage_nonempty_iff_exactBlocker :
    Nonempty
        (DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) <->
      ExactDegreeSixGeneratedCyclicRowsBlocker.{u}
        payForCut topologyArc := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro P.degreeRows
            (Nonempty.intro P.generatedCyclicRows)
  case mpr =>
    intro h
    cases h with
    | intro degreeRows hRows =>
        cases hRows with
        | intro generatedCyclicRows =>
            exact
              Nonempty.intro
                { degreeRows := degreeRows
                  generatedCyclicRows := generatedCyclicRows }

theorem exactDegreeSixGeneratedCyclicRowsBlocker_iff_w31Blocker :
    ExactDegreeSixGeneratedCyclicRowsBlocker.{u}
        payForCut topologyArc <->
      W31DegreeSixGeneratedFrameCyclicRowsBlocker.{u}
        payForCut topologyArc :=
  Iff.rfl

theorem degreeSixGeneratedCyclicRowPackage_nonempty_iff_w31Blocker :
    Nonempty
        (DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) <->
      W31DegreeSixGeneratedFrameCyclicRowsBlocker.{u}
        payForCut topologyArc :=
  (degreeSixGeneratedCyclicRowPackage_nonempty_iff_exactBlocker
    (payForCut := payForCut) (topologyArc := topologyArc)).trans
    (exactDegreeSixGeneratedCyclicRowsBlocker_iff_w31Blocker
      (payForCut := payForCut) (topologyArc := topologyArc))

theorem degreeSixGeneratedCyclicRowPackage_nonempty_iff_degreeSixNeighborRows :
    Nonempty
        (DegreeSixGeneratedCyclicRowPackage.{u} payForCut topologyArc) <->
      Nonempty
        (DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toDegreeSixNeighborCyclicOrderRows
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (degreeSixGeneratedCyclicRowPackageOfDegreeSixNeighborRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem sourcePackage_nonempty_of_degreeSixGeneratedCyclicRowsBlocker
    (h :
      ExactDegreeSixGeneratedCyclicRowsBlocker.{u}
        payForCut topologyArc) :
    Nonempty
      (FrameCyclicOrderSourcePackage.{u} payForCut topologyArc) := by
  have hpkg :
      Nonempty
        (DegreeSixGeneratedCyclicRowPackage.{u}
          payForCut topologyArc) :=
    (degreeSixGeneratedCyclicRowPackage_nonempty_iff_exactBlocker
      (payForCut := payForCut) (topologyArc := topologyArc)).2 h
  cases hpkg with
  | intro P =>
      exact Nonempty.intro P.toFrameCyclicOrderSourcePackage

theorem uniformFiniteGeometryRows_nonempty_of_degreeSixGeneratedCyclicRowsBlocker
    (h :
      ExactDegreeSixGeneratedCyclicRowsBlocker.{u}
        payForCut topologyArc) :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
  (uniformFiniteGeometryRows_nonempty_iff_sourcePackage
    (payForCut := payForCut) (topologyArc := topologyArc)).2
    (sourcePackage_nonempty_of_degreeSixGeneratedCyclicRowsBlocker
      (payForCut := payForCut) (topologyArc := topologyArc) h)

theorem exactRemainingPackage_nonempty_of_degreeSixGeneratedCyclicRowsBlocker
    (h :
      ExactDegreeSixGeneratedCyclicRowsBlocker.{u}
        payForCut topologyArc) :
    Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) :=
  (sourcePackage_nonempty_iff_exactRemainingPackage
    (payForCut := payForCut) (topologyArc := topologyArc)).1
    (sourcePackage_nonempty_of_degreeSixGeneratedCyclicRowsBlocker
      (payForCut := payForCut) (topologyArc := topologyArc) h)

/-! ## No-cut component frame/cyclic source package -/

abbrev NoCutDependency : Prop :=
  PointwiseLaneProductInhabitationW31.NoCutDependency

abbrev ComponentFamily : Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.ExtractedWitnessComponentFamily.{u}

abbrev ActualTopologyComponentClosurePackage : Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.ActualTopologyExtractedComponentClosurePackage.{u}

abbrev MinimalFailureActualSelectedTopologyRows : Type 1 :=
  ExtractedComponentsConcreteClosureW32.MinimalFailureActualSelectedTopologyRows

abbrev ActualTopologyRemainingComponentRows
    (topology : MinimalFailureActualSelectedTopologyRows) :
    Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.ActualTopologyRemainingComponentRows.{u}
    topology

def componentFamilyOfActualTopologyClosurePackage
    (P : ActualTopologyComponentClosurePackage.{u}) :
    ComponentFamily.{u} :=
  P.toExtractedWitnessComponentFamily

def actualTopologyClosurePackageOfActualTopologyRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (components : ActualTopologyRemainingComponentRows.{u} topology) :
    ActualTopologyComponentClosurePackage.{u} :=
  ExtractedComponentsConcreteClosureW32.actualTopologyClosurePackageOfActualTopologyRows
    topology components

abbrev FrameCyclicRows
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) :
    Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.UniformFrameCyclicOrderRows.{u}
    noCut components

abbrev FrameCyclicSourcePackage
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) :
    Type (u + 1) :=
  FrameCyclicOrderSourcePackage.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)

abbrev ActualTopologyClosureFrameCyclicRows
    (noCut : NoCutDependency)
    (topology : MinimalFailureActualSelectedTopologyRows)
    (components : ActualTopologyRemainingComponentRows.{u} topology) :
    Type (u + 1) :=
  FrameCyclicRows.{u} noCut
    (componentFamilyOfActualTopologyClosurePackage
      (actualTopologyClosurePackageOfActualTopologyRows topology
        components))

abbrev ActualTopologyClosureFrameSource
    (noCut : NoCutDependency)
    (topology : MinimalFailureActualSelectedTopologyRows)
    (components : ActualTopologyRemainingComponentRows.{u} topology) :
    Type (u + 1) :=
  FrameCyclicSourcePackage.{u} noCut
    (componentFamilyOfActualTopologyClosurePackage
      (actualTopologyClosurePackageOfActualTopologyRows topology
        components))

def frameCyclicRowsOfFrameCyclicSourcePackage
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (P : FrameCyclicSourcePackage.{u} noCut components) :
    FrameCyclicRows.{u} noCut components :=
  P.toUniformFrameCyclicOrderRows

def frameCyclicSourcePackageOfFrameCyclicRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    FrameCyclicSourcePackage.{u} noCut components :=
  frameCyclicOrderSourcePackageOfUniformFrameCyclicOrderRows
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    rows

/-! ## Selected finite-spine frame source package -/

abbrev SelectedFinitePQSpineFrameCoreLemma8Rows
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) :
    Type (u + 1) :=
  FinitePQSpineFrameCoreLemma8Rows.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)

abbrev SelectedFinitePQSpineGeneratedCyclicRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components) :=
  NeighborCyclicOrderRowsForFrameRows.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)
    (FinitePQSpineFrameCoreLemma8Rows.generatedFrameRows
      (payForCut :=
        PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
      (topologyArc :=
        PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
      finiteRows)

/--
Pointwise generated cyclic-order rows obtained from the explicit finite
`p_i/q_i` boundary-spine successor rows.
-/
def finitePQSpineGeneratedCyclicRowsOfExplicitCyclicOrderRows
    (finiteRows :
      FinitePQSpineFrameCoreLemma8Rows.{u} payForCut topologyArc)
    (explicitCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineCertificate.ExplicitCyclicOrderRows
            (PointwiseFinitePQSpineCertificate
              (topologyArc := topologyArc) C hmin)) :
    NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc
      (FinitePQSpineFrameCoreLemma8Rows.generatedFrameRows
        (payForCut := payForCut) (topologyArc := topologyArc)
        finiteRows) := by
  intro n C hmin
  exact
    { positiveCyclicOrderAt := fun _i _s _r _prev _left _right _next =>
        M8FinitePQSpineCertificate.ExplicitCyclicOrderRows
          (PointwiseFinitePQSpineCertificate
            (topologyArc := topologyArc) C hmin)
      positiveCyclicOrder := fun _i => explicitCyclicRows C hmin }

/-- Selected version of
`finitePQSpineGeneratedCyclicRowsOfExplicitCyclicOrderRows`. -/
def selectedFinitePQSpineGeneratedCyclicRowsOfExplicitCyclicOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (explicitCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineCertificate.ExplicitCyclicOrderRows
            (PointwiseFinitePQSpineCertificate
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin)) :
    SelectedFinitePQSpineGeneratedCyclicRows
      (noCut := noCut) (components := components)
      finiteRows :=
  finitePQSpineGeneratedCyclicRowsOfExplicitCyclicOrderRows
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    finiteRows explicitCyclicRows

theorem selectedFinitePQSpineGeneratedCyclicRows_nonempty_of_explicitCyclicOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (explicitCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineCertificate.ExplicitCyclicOrderRows
            (PointwiseFinitePQSpineCertificate
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin)) :
    Nonempty
      (SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := noCut) (components := components)
        finiteRows) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedCyclicRowsOfExplicitCyclicOrderRows
      (noCut := noCut) (components := components)
      finiteRows explicitCyclicRows)

abbrev SelectedFinitePQSpineGeneratedOrderRows
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) :
    Type (u + 1) :=
  FinitePQSpineGeneratedOrderRows.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)

def selectedFinitePQSpineGeneratedOrderRowsOfUniformFiniteGeometryRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      UniformFiniteGeometryRows.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)) :
    SelectedFinitePQSpineGeneratedOrderRows.{u} noCut components :=
  finitePQSpineGeneratedOrderRowsOfUniformFiniteGeometryRows
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    rows

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_uniformFiniteGeometryRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      UniformFiniteGeometryRows.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedOrderRowsOfUniformFiniteGeometryRows
      (noCut := noCut) (components := components) rows)

/-- Selected finite-spine generated-order rows keyed to the component family
extracted from an actual-topology closure package. -/
abbrev SelectedFinitePQSpineGeneratedOrderRowsForActualTopologyClosure
    (noCut : NoCutDependency)
    (componentClosure : ActualTopologyComponentClosurePackage.{u}) :
    Type (u + 1) :=
  SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
    (componentFamilyOfActualTopologyClosurePackage componentClosure)

def selectedFinitePQSpineGeneratedOrderRowsForActualTopologyClosureOfUniformFiniteGeometryRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      UniformFiniteGeometryRows.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          (componentFamilyOfActualTopologyClosurePackage
            componentClosure))) :
    SelectedFinitePQSpineGeneratedOrderRowsForActualTopologyClosure.{u}
      noCut componentClosure :=
  selectedFinitePQSpineGeneratedOrderRowsOfUniformFiniteGeometryRows
    (noCut := noCut)
    (components :=
      componentFamilyOfActualTopologyClosurePackage componentClosure)
    rows

theorem selectedFinitePQSpineGeneratedOrderRowsForActualTopologyClosure_nonempty_of_uniformFiniteGeometryRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      UniformFiniteGeometryRows.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          (componentFamilyOfActualTopologyClosurePackage
            componentClosure))) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRowsForActualTopologyClosure.{u}
        noCut componentClosure) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedOrderRowsForActualTopologyClosureOfUniformFiniteGeometryRows
      (noCut := noCut) componentClosure rows)

def selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D :=
              ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components).row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components).row C hmin).boundaryArc)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin
              (finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                finiteWalkFrameCore boundaryArc_eq C hmin)
              (extraNeighborCardTwo C hmin))) :
    SelectedFinitePQSpineGeneratedOrderRows.{u} noCut components :=
  finitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreData
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    finiteWalkFrameCore boundaryArc_eq extraNeighborCardTwo
    generatedCyclicRows

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D :=
              ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components).row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components).row C hmin).boundaryArc)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin
              (finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                finiteWalkFrameCore boundaryArc_eq C hmin)
              (extraNeighborCardTwo C hmin))) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreData
      (noCut := noCut) (components := components)
      finiteWalkFrameCore boundaryArc_eq extraNeighborCardTwo
      generatedCyclicRows)

def selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSix
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D :=
              ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components).row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components).row C hmin).boundaryArc)
    (centerDegreeSix :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            Lemma8ExistenceConcrete.centerDegree
              (((finiteWalkFrameCore C hmin).toFinitePQSpineCertificate)
                |>.toM8BoundarySpine
                  (PointwiseConnectedNoCutCertificate
                    (payForCut :=
                      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                        noCut)
                    C hmin)
                  hmin) i = 6)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin
              (finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                finiteWalkFrameCore boundaryArc_eq C hmin)
              (finiteWalkFrameCoreExtraNeighborCardTwoOfCenterDegreeSix
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                finiteWalkFrameCore boundaryArc_eq centerDegreeSix
                C hmin))) :
    SelectedFinitePQSpineGeneratedOrderRows.{u} noCut components :=
  finitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSix
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents components)
    finiteWalkFrameCore boundaryArc_eq centerDegreeSix
    generatedCyclicRows

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreCenterDegreeSix
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteWalkFrameCore :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkFrameCoreData
            (D :=
              ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components).row C hmin).arcBoundaryBudget.planarBoundary)
            (PointwiseConnectedNoCutCertificate
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              C hmin)
            hmin)
    (boundaryArc_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
            ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components).row C hmin).boundaryArc)
    (centerDegreeSix :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            Lemma8ExistenceConcrete.centerDegree
              (((finiteWalkFrameCore C hmin).toFinitePQSpineCertificate)
                |>.toM8BoundarySpine
                  (PointwiseConnectedNoCutCertificate
                    (payForCut :=
                      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                        noCut)
                    C hmin)
                  hmin) i = 6)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin
              (finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                finiteWalkFrameCore boundaryArc_eq C hmin)
              (finiteWalkFrameCoreExtraNeighborCardTwoOfCenterDegreeSix
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                finiteWalkFrameCore boundaryArc_eq centerDegreeSix
                C hmin))) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSix
      (noCut := noCut) (components := components)
      finiteWalkFrameCore boundaryArc_eq centerDegreeSix
      generatedCyclicRows)

def selectedFinitePQSpineGeneratedOrderRowsOfRawFacts
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rawFacts :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseFinitePQSpineRawFrameCoreFacts
            (topologyArc :=
              PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
            C hmin)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin
              (finitePQSpineFrameCoreFieldsOfRawFacts
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                rawFacts C hmin)
              (extraNeighborCardTwo C hmin))) :
    SelectedFinitePQSpineGeneratedOrderRows.{u} noCut components :=
  finitePQSpineGeneratedOrderRowsOfRawFacts
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    rawFacts extraNeighborCardTwo generatedCyclicRows

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_rawFacts
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rawFacts :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseFinitePQSpineRawFrameCoreFacts
            (topologyArc :=
              PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
            C hmin)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin
              (finitePQSpineFrameCoreFieldsOfRawFacts
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                rawFacts C hmin)
              (extraNeighborCardTwo C hmin))) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedOrderRowsOfRawFacts
      (noCut := noCut) (components := components)
      rawFacts extraNeighborCardTwo generatedCyclicRows)

/-- Minimal selected source rows for the finite-walk route to generated
finite-spine order.  The selected boundary arc already carries the finite
`p/q` successor rows, so the source field retained here is the matching
frame-core payload together with the generated neighbor cyclic order used by
the W32 frame rows. -/
structure SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) : Type (u + 1) where
  frameCoreFields :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8FinitePQSpineFrameCoreFields
          (PointwiseFinitePQSpineCertificate
            (topologyArc :=
              PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
            C hmin)
          (PointwiseConnectedNoCutCertificate
            (payForCut :=
              PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                noCut)
            C hmin)
          hmin
  extraNeighborCardTwo :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        forall i : M8ExtraIndex,
          (Lemma8ExistenceConcrete.extraNeighborFinset
            (PointwiseSpine
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin) i).card = 2
  generatedCyclicRows :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
          (finitePQSpineGeneratedExtraNeighborData
            (payForCut :=
              PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                noCut)
            (topologyArc :=
              PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
            C hmin
            (frameCoreFields C hmin)
            (extraNeighborCardTwo C hmin))

namespace SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows

variable {noCut : NoCutDependency}
variable {components : ComponentFamily.{u}}

def finiteWalkFrameCore
    (rows :
      SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BoundaryArcFiniteWalkFrameCoreData
          (D :=
            ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components).row C hmin).arcBoundaryBudget.planarBoundary)
          (PointwiseConnectedNoCutCertificate
            (payForCut :=
              PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                noCut)
            C hmin)
          hmin :=
  fun {_n} C hmin =>
    BoundaryArcFiniteWalkFrameCoreData.ofBoundaryArcCertificateAndFrameCoreFields
      (D :=
        ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components).row C hmin).arcBoundaryBudget.planarBoundary)
      (connectedNoCut :=
        PointwiseConnectedNoCutCertificate
          (payForCut :=
            PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
              noCut)
          C hmin)
      (hmin := hmin)
      ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components).row C hmin).boundaryArc
      (rows.frameCoreFields C hmin)

theorem boundaryArc_eq
    (rows :
      SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        (rows.finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
          ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components).row C hmin).boundaryArc := by
  intro n C hmin
  rfl

def boundaryArcFrameCoreFields
    (rows :
      SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8FinitePQSpineBoundaryArcFrameCoreFields
          (PointwiseFinitePQSpineCertificate
            (topologyArc :=
              PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
            C hmin)
          (PointwiseConnectedNoCutCertificate
            (payForCut :=
              PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                noCut)
            C hmin)
          hmin := by
  intro n C hmin
  exact
    M8FinitePQSpineBoundaryArcFrameCoreFields.ofCyclicOrderAndFrameCoreFields
      (K :=
        PointwiseFinitePQSpineCertificate
          (topologyArc :=
            PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components)
          C hmin)
      (connectedNoCut :=
        PointwiseConnectedNoCutCertificate
          (payForCut :=
            PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
              noCut)
          C hmin)
      (hmin := hmin)
      (fun i =>
        ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components).row C hmin).boundaryArc.toFinitePQSpineCertificate_cyclicOrder i)
      (rows.frameCoreFields C hmin)

theorem rawFacts
    (rows :
      SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseFinitePQSpineRawFrameCoreFacts
          (topologyArc :=
            PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components)
          C hmin :=
  rawFactsOfFinitePQSpineFrameCoreFields
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    rows.frameCoreFields

end SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows

def selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFrameCoreFields
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (frameCoreFields :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineFrameCoreFields
            (PointwiseFinitePQSpineCertificate
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin)
            (PointwiseConnectedNoCutCertificate
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              C hmin)
            hmin)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin (frameCoreFields C hmin)
              (extraNeighborCardTwo C hmin))) :
    SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
      noCut components where
  frameCoreFields := frameCoreFields
  extraNeighborCardTwo := extraNeighborCardTwo
  generatedCyclicRows := generatedCyclicRows

def selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfBoundaryArcFrameCoreFields
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (frameCoreFields :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineFrameCoreFields
            (PointwiseFinitePQSpineCertificate
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin)
            (PointwiseConnectedNoCutCertificate
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              C hmin)
            hmin)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin (frameCoreFields C hmin)
              (extraNeighborCardTwo C hmin))) :
    SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
      noCut components :=
  selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFrameCoreFields
    (noCut := noCut) (components := components)
    frameCoreFields extraNeighborCardTwo generatedCyclicRows

def selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFinitePQSpineBoundaryArcFrameCoreFields
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (boundaryArcFrameCoreFields :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineBoundaryArcFrameCoreFields
            (PointwiseFinitePQSpineCertificate
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin)
            (PointwiseConnectedNoCutCertificate
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              C hmin)
            hmin)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin
              (boundaryArcFrameCoreFields C hmin).frameCoreFields
              (extraNeighborCardTwo C hmin))) :
    SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
      noCut components where
  frameCoreFields := fun C hmin =>
    (boundaryArcFrameCoreFields C hmin).frameCoreFields
  extraNeighborCardTwo := extraNeighborCardTwo
  generatedCyclicRows := generatedCyclicRows

theorem selectedFiniteWalkFrameCoreGeneratedOrderSourceRows_nonempty_of_boundaryArcFrameCoreFields
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (boundaryArcFrameCoreFields :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineBoundaryArcFrameCoreFields
            (PointwiseFinitePQSpineCertificate
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin)
            (PointwiseConnectedNoCutCertificate
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              C hmin)
            hmin)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin
              (boundaryArcFrameCoreFields C hmin).frameCoreFields
              (extraNeighborCardTwo C hmin))) :
    Nonempty
      (SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :=
  Nonempty.intro
    (selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFinitePQSpineBoundaryArcFrameCoreFields
      (noCut := noCut) (components := components)
      boundaryArcFrameCoreFields extraNeighborCardTwo generatedCyclicRows)

def selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfRawFacts
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rawFacts :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseFinitePQSpineRawFrameCoreFacts
            (topologyArc :=
              PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
            C hmin)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin
              (finitePQSpineFrameCoreFieldsOfRawFacts
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                rawFacts C hmin)
              (extraNeighborCardTwo C hmin))) :
    SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
      noCut components :=
  selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfBoundaryArcFrameCoreFields
    (noCut := noCut) (components := components)
    (finitePQSpineFrameCoreFieldsOfRawFacts
      (payForCut :=
        PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
      (topologyArc :=
        PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
      rawFacts)
    extraNeighborCardTwo generatedCyclicRows

theorem selectedFiniteWalkFrameCoreGeneratedOrderSourceRows_nonempty_of_rawFacts
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rawFacts :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseFinitePQSpineRawFrameCoreFacts
            (topologyArc :=
              PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
            C hmin)
    (extraNeighborCardTwo :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          forall i : M8ExtraIndex,
            (Lemma8ExistenceConcrete.extraNeighborFinset
              (PointwiseSpine
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                C hmin) i).card = 2)
    (generatedCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
            (finitePQSpineGeneratedExtraNeighborData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin
              (finitePQSpineFrameCoreFieldsOfRawFacts
                (payForCut :=
                  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    noCut)
                (topologyArc :=
                  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components)
                rawFacts C hmin)
              (extraNeighborCardTwo C hmin))) :
    Nonempty
      (SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :=
  Nonempty.intro
    (selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfRawFacts
      (noCut := noCut) (components := components)
      rawFacts extraNeighborCardTwo generatedCyclicRows)

def selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFinitePQSpineFrameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (generatedCyclicRows :
      SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := noCut) (components := components)
        finiteRows) :
    SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
      noCut components where
  frameCoreFields := finiteRows.frameCoreFields
  extraNeighborCardTwo := fun C hmin i =>
    Lemma8ForbiddenDistinctConcrete.extraNeighborFinset_card_eq_two_of_lemma8Combinatorics
      (finiteRows.lemma8 C hmin) i
  generatedCyclicRows := by
    intro n C hmin
    exact generatedCyclicRows C hmin

theorem selectedFiniteWalkFrameCoreGeneratedOrderSourceRows_nonempty_of_finitePQSpineFrameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (generatedCyclicRows :
      SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := noCut) (components := components)
        finiteRows) :
    Nonempty
      (SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :=
  Nonempty.intro
    (selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFinitePQSpineFrameCoreLemma8Rows
      (noCut := noCut) (components := components)
      finiteRows generatedCyclicRows)

def selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :
    SelectedFinitePQSpineGeneratedOrderRows.{u} noCut components :=
  { frameCoreFields := rows.frameCoreFields
    extraNeighborCardTwo := rows.extraNeighborCardTwo
    generatedCyclicRows := rows.generatedCyclicRows }

def selectedFinitePQSpineFrameCoreLemma8RowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :
    SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut components :=
  (selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
    (noCut := noCut) (components := components) rows).toFinitePQSpineFrameCoreLemma8Rows

def selectedFinitePQSpineGeneratedCyclicRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :
    SelectedFinitePQSpineGeneratedCyclicRows
      (noCut := noCut) (components := components)
      (selectedFinitePQSpineFrameCoreLemma8RowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
        (noCut := noCut) (components := components) rows) :=
  (selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
    (noCut := noCut) (components := components) rows).toGeneratedCyclicRows

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
      (noCut := noCut) (components := components) rows)

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_nonempty_finiteWalkFrameCoreGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      Nonempty
        (SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
          noCut components)) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) := by
  cases rows with
  | intro rows =>
      exact
        selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreGeneratedOrderSourceRows
          (noCut := noCut) (components := components) rows

/-! ## Selected finite-PQ generated-order source rows -/

/--
Selected generated-order source rows built directly from the finite
`p_i/q_i` boundary-spine certificate: the frame-core/Lemma 8 rows supply the
generated frame core, while the named explicit cyclic-successor rows generate
the selected cyclic rows keyed to that same frame core.
-/
structure SelectedFinitePQSpineGeneratedOrderSourceRows
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) : Type (u + 1) where
  finiteRows :
    SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut components
  explicitCyclicRows :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8FinitePQSpineCertificate.ExplicitCyclicOrderRows
          (PointwiseFinitePQSpineCertificate
            (topologyArc :=
              PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
            C hmin)

namespace SelectedFinitePQSpineGeneratedOrderSourceRows

variable {noCut : NoCutDependency}
variable {components : ComponentFamily.{u}}

def generatedCyclicRows
    (rows :
      SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
        noCut components) :
    SelectedFinitePQSpineGeneratedCyclicRows
      (noCut := noCut) (components := components)
      rows.finiteRows :=
  selectedFinitePQSpineGeneratedCyclicRowsOfExplicitCyclicOrderRows
    (noCut := noCut) (components := components)
    rows.finiteRows rows.explicitCyclicRows

def toFrameCoreGeneratedOrderSourceRows
    (rows :
      SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
        noCut components) :
    SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
      noCut components :=
  selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFinitePQSpineFrameCoreLemma8Rows
    (noCut := noCut) (components := components)
    rows.finiteRows rows.generatedCyclicRows

def toGeneratedOrderRows
    (rows :
      SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
        noCut components) :
    SelectedFinitePQSpineGeneratedOrderRows.{u} noCut components :=
  selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
    (noCut := noCut) (components := components)
    rows.toFrameCoreGeneratedOrderSourceRows

theorem generatedOrderRows_eq_frameCoreSourceRows
    (rows :
      SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
        noCut components) :
    rows.toGeneratedOrderRows =
      selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
        (noCut := noCut) (components := components)
        rows.toFrameCoreGeneratedOrderSourceRows := rfl

end SelectedFinitePQSpineGeneratedOrderSourceRows

def selectedFinitePQSpineGeneratedOrderSourceRowsOfFinitePQSpineFrameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (explicitCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineCertificate.ExplicitCyclicOrderRows
            (PointwiseFinitePQSpineCertificate
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin)) :
    SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
      noCut components where
  finiteRows := finiteRows
  explicitCyclicRows := explicitCyclicRows

theorem selectedFinitePQSpineGeneratedOrderSourceRows_nonempty_of_finitePQSpineFrameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (explicitCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineCertificate.ExplicitCyclicOrderRows
            (PointwiseFinitePQSpineCertificate
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin)) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
        noCut components) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedOrderSourceRowsOfFinitePQSpineFrameCoreLemma8Rows
      (noCut := noCut) (components := components)
      finiteRows explicitCyclicRows)

def selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFinitePQSpineGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
        noCut components) :
    SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
      noCut components :=
  rows.toFrameCoreGeneratedOrderSourceRows

theorem selectedFiniteWalkFrameCoreGeneratedOrderSourceRows_nonempty_of_finitePQSpineGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
        noCut components) :
    Nonempty
      (SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :=
  Nonempty.intro
    (selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFinitePQSpineGeneratedOrderSourceRows
      (noCut := noCut) (components := components) rows)

def selectedFinitePQSpineGeneratedOrderRowsOfFinitePQSpineGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
        noCut components) :
    SelectedFinitePQSpineGeneratedOrderRows.{u} noCut components :=
  rows.toGeneratedOrderRows

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finitePQSpineGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
        noCut components) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedOrderRowsOfFinitePQSpineGeneratedOrderSourceRows
      (noCut := noCut) (components := components) rows)

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finitePQSpineFrameCoreLemma8Rows_explicitCyclicOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (explicitCyclicRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8FinitePQSpineCertificate.ExplicitCyclicOrderRows
            (PointwiseFinitePQSpineCertificate
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              C hmin)) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :=
  selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finitePQSpineGeneratedOrderSourceRows
    (noCut := noCut) (components := components)
    (selectedFinitePQSpineGeneratedOrderSourceRowsOfFinitePQSpineFrameCoreLemma8Rows
      (noCut := noCut) (components := components)
      finiteRows explicitCyclicRows)

/--
The selected finite boundary-spine certificate carries the cyclic-successor
rows needed to build the named explicit positive cyclic-order rows for the
same `p_i/q_i` spine.
-/
def selectedFinitePQSpineExplicitCyclicOrderRowsOfBoundarySpineCertificate
    {components : ComponentFamily.{u}} :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8FinitePQSpineCertificate.ExplicitCyclicOrderRows
          (PointwiseFinitePQSpineCertificate
            (topologyArc :=
              PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
            C hmin) := by
  intro n C hmin
  exact
    (PointwiseFinitePQSpineCertificate
      (topologyArc :=
        PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
      C hmin).toExplicitCyclicOrderRows
      (fun i =>
        ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components).row C hmin).boundaryArc.toFinitePQSpineCertificate_cyclicOrder i)

def selectedFinitePQSpineGeneratedOrderSourceRowsOfBoundarySpineCertificateFrameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components) :
    SelectedFinitePQSpineGeneratedOrderSourceRows.{u}
      noCut components :=
  selectedFinitePQSpineGeneratedOrderSourceRowsOfFinitePQSpineFrameCoreLemma8Rows
    (noCut := noCut) (components := components)
    finiteRows
    (selectedFinitePQSpineExplicitCyclicOrderRowsOfBoundarySpineCertificate
      (components := components))

def selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfBoundarySpineCertificateFrameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components) :
    SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
      noCut components :=
  selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFinitePQSpineGeneratedOrderSourceRows
    (noCut := noCut) (components := components)
    (selectedFinitePQSpineGeneratedOrderSourceRowsOfBoundarySpineCertificateFrameCoreLemma8Rows
      (noCut := noCut) (components := components) finiteRows)

theorem selectedFiniteWalkFrameCoreGeneratedOrderSourceRows_nonempty_of_boundarySpineCertificate_frameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components) :
    Nonempty
      (SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :=
  Nonempty.intro
    (selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfBoundarySpineCertificateFrameCoreLemma8Rows
      (noCut := noCut) (components := components) finiteRows)

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_boundarySpineCertificate_frameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :=
  selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finitePQSpineGeneratedOrderSourceRows
    (noCut := noCut) (components := components)
    (selectedFinitePQSpineGeneratedOrderSourceRowsOfBoundarySpineCertificateFrameCoreLemma8Rows
      (noCut := noCut) (components := components) finiteRows)

theorem selectedFiniteWalkFrameCoreGeneratedOrderSourceRows_nonempty_of_nonempty_boundarySpineCertificate_frameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      Nonempty
        (SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
          components)) :
    Nonempty
      (SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) := by
  cases finiteRows with
  | intro finiteRows =>
      exact
        selectedFiniteWalkFrameCoreGeneratedOrderSourceRows_nonempty_of_boundarySpineCertificate_frameCoreLemma8Rows
          (noCut := noCut) (components := components) finiteRows

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_nonempty_boundarySpineCertificate_frameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      Nonempty
        (SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
          components)) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) := by
  cases finiteRows with
  | intro finiteRows =>
      exact
        selectedFinitePQSpineGeneratedOrderRows_nonempty_of_boundarySpineCertificate_frameCoreLemma8Rows
          (noCut := noCut) (components := components) finiteRows

def selectedFinitePQSpineGeneratedOrderRowsOfBoundarySpineCertificateFrameCoreLemma8Rows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components) :
    SelectedFinitePQSpineGeneratedOrderRows.{u} noCut components :=
  selectedFinitePQSpineGeneratedOrderRowsOfFinitePQSpineGeneratedOrderSourceRows
    (noCut := noCut) (components := components)
    (selectedFinitePQSpineGeneratedOrderSourceRowsOfBoundarySpineCertificateFrameCoreLemma8Rows
      (noCut := noCut) (components := components) finiteRows)

/-- Variant of the selected finite-walk generated-order source where the
extra-neighbor cardinality-two row is derived from center-degree six on the
same finite-walk spine. -/
structure SelectedFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) : Type (u + 1) where
  finiteWalkFrameCore :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BoundaryArcFiniteWalkFrameCoreData
          (D :=
            ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components).row C hmin).arcBoundaryBudget.planarBoundary)
          (PointwiseConnectedNoCutCertificate
            (payForCut :=
              PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                noCut)
            C hmin)
          hmin
  boundaryArc_eq :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        (finiteWalkFrameCore C hmin).finiteWalk.toBoundaryArcCertificate =
          ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components).row C hmin).boundaryArc
  centerDegreeSix :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        forall i : M8ExtraIndex,
          Lemma8ExistenceConcrete.centerDegree
            (((finiteWalkFrameCore C hmin).toFinitePQSpineCertificate)
              |>.toM8BoundarySpine
                (PointwiseConnectedNoCutCertificate
                  (payForCut :=
                    PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                      noCut)
                  C hmin)
                hmin) i = 6
  generatedCyclicRows :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
          (finitePQSpineGeneratedExtraNeighborData
            (payForCut :=
              PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                noCut)
            (topologyArc :=
              PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
            C hmin
            (finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              finiteWalkFrameCore boundaryArc_eq C hmin)
            (finiteWalkFrameCoreExtraNeighborCardTwoOfCenterDegreeSix
              (payForCut :=
                PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
              (topologyArc :=
                PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
              finiteWalkFrameCore boundaryArc_eq centerDegreeSix
              C hmin))

def selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfCenterDegreeSix
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows.{u}
        noCut components) :
    SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
      noCut components where
  frameCoreFields :=
    finitePQSpineFrameCoreFieldsOfFiniteWalkFrameCoreData
      (payForCut :=
        PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
          noCut)
      (topologyArc :=
        PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
      rows.finiteWalkFrameCore rows.boundaryArc_eq
  extraNeighborCardTwo :=
    finiteWalkFrameCoreExtraNeighborCardTwoOfCenterDegreeSix
      (payForCut :=
        PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
          noCut)
      (topologyArc :=
        PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
      rows.finiteWalkFrameCore rows.boundaryArc_eq rows.centerDegreeSix
  generatedCyclicRows := rows.generatedCyclicRows

theorem selectedFiniteWalkFrameCoreGeneratedOrderSourceRows_nonempty_of_centerDegreeSixGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows.{u}
        noCut components) :
    Nonempty
      (SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{u}
        noCut components) :=
  Nonempty.intro
    (selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfCenterDegreeSix
      (noCut := noCut) (components := components) rows)

def selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows.{u}
        noCut components) :
    SelectedFinitePQSpineGeneratedOrderRows.{u} noCut components :=
  selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
    (noCut := noCut) (components := components)
    (selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfCenterDegreeSix
      (noCut := noCut) (components := components) rows)

theorem selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows_eq_extraCard
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows.{u}
        noCut components) :
    selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows
      (noCut := noCut) (components := components) rows =
    selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
      (noCut := noCut) (components := components)
      (selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfCenterDegreeSix
        (noCut := noCut) (components := components) rows) :=
  rfl

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows.{u}
        noCut components) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows
      (noCut := noCut) (components := components) rows)

theorem selectedFinitePQSpineGeneratedOrderRows_nonempty_of_nonempty_finiteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      Nonempty
        (SelectedFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows.{u}
          noCut components)) :
    Nonempty
      (SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) := by
  cases rows with
  | intro rows =>
      exact
        selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows
          (noCut := noCut) (components := components) rows

def selectedFinitePQSpineCyclicSuccessorRowsSourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}} :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Nonempty
          { K :
              M8FinitePQSpineCertificate
                ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components).row C hmin).arcBoundaryBudget.planarBoundary //
            BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows
              K } :=
  by
    let _selectedNoCut : NoCutDependency := noCut
    intro n C hmin
    exact
      pointwiseFinitePQSpineCyclicSuccessorRowsFamily
        (topologyArc :=
          PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
        C hmin

def selectedFinitePQSpineCyclicSuccessorRowsSourceFamilyOfGeneratedOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (_rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Nonempty
          { K :
              M8FinitePQSpineCertificate
                ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components).row C hmin).arcBoundaryBudget.planarBoundary //
            BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows
              K } :=
  selectedFinitePQSpineCyclicSuccessorRowsSourceFamily
    (noCut := noCut) (components := components)

def selectedFinitePQSpineCyclicSuccessorRowsSourceFamilyOfFinitePQTheorem
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (H :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Nonempty
          { K :
              M8FinitePQSpineCertificate
                ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    components).row C hmin).arcBoundaryBudget.planarBoundary //
            BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows
              K } :=
  by
    let _selectedNoCut : NoCutDependency := noCut
    intro n C hmin
    exact
      pointwiseFinitePQSpineCyclicSuccessorRowsFamilyOfFinitePQTheorem
        (topologyArc :=
          PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
        H C hmin

def selectedFinitePQSpineFrameCoreLemma8RowsOfGeneratedOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :
    SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut components :=
  rows.toFinitePQSpineFrameCoreLemma8Rows

def selectedFinitePQSpineGeneratedCyclicRowsOfGeneratedOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :
    SelectedFinitePQSpineGeneratedCyclicRows
      (noCut := noCut) (components := components)
      (selectedFinitePQSpineFrameCoreLemma8RowsOfGeneratedOrderRows
        (noCut := noCut) (components := components) rows) :=
  rows.toGeneratedCyclicRows

theorem selectedFinitePQSpineFrameCoreLemma8Rows_nonempty_of_generatedOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :
    Nonempty
      (SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components) :=
  Nonempty.intro
    (selectedFinitePQSpineFrameCoreLemma8RowsOfGeneratedOrderRows
      (noCut := noCut) (components := components) rows)

theorem selectedFinitePQSpineGeneratedCyclicRows_nonempty_of_generatedOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :
    Nonempty
      (SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := noCut) (components := components)
        (selectedFinitePQSpineFrameCoreLemma8RowsOfGeneratedOrderRows
          (noCut := noCut) (components := components) rows)) :=
  Nonempty.intro
    (selectedFinitePQSpineGeneratedCyclicRowsOfGeneratedOrderRows
      (noCut := noCut) (components := components) rows)

def selectedFinitePQSpineFrameCoreLemma8RowsOfActualTopologyClosureGeneratedOrderRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
      (componentFamilyOfActualTopologyClosurePackage
        componentClosure) :=
  selectedFinitePQSpineFrameCoreLemma8RowsOfGeneratedOrderRows
    (noCut := noCut)
    (components :=
      componentFamilyOfActualTopologyClosurePackage componentClosure)
    rows

def selectedFinitePQSpineGeneratedCyclicRowsOfActualTopologyClosureGeneratedOrderRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    SelectedFinitePQSpineGeneratedCyclicRows
      (noCut := noCut)
      (components :=
        componentFamilyOfActualTopologyClosurePackage componentClosure)
      (selectedFinitePQSpineFrameCoreLemma8RowsOfActualTopologyClosureGeneratedOrderRows
        (noCut := noCut) componentClosure rows) :=
  selectedFinitePQSpineGeneratedCyclicRowsOfGeneratedOrderRows
    (noCut := noCut)
    (components :=
      componentFamilyOfActualTopologyClosurePackage componentClosure)
    rows

def selectedFinitePQSpineCyclicSuccessorRowsSourceFamilyOfActualTopologyClosureGeneratedOrderRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (_rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Nonempty
          { K :
              M8FinitePQSpineCertificate
                ((PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    (componentFamilyOfActualTopologyClosurePackage
                      componentClosure)).row C hmin).arcBoundaryBudget.planarBoundary //
            BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows
              K } :=
  selectedFinitePQSpineCyclicSuccessorRowsSourceFamily
    (noCut := noCut)
    (components :=
      componentFamilyOfActualTopologyClosurePackage componentClosure)

def selectedFinitePQSpineFrameCoreLemma8RowsOfActualTopologyClosureEqGeneratedOrderRows
    {noCut : NoCutDependency}
    {componentClosure actualClosure :
      ActualTopologyComponentClosurePackage.{u}}
    (componentClosure_eq : componentClosure = actualClosure)
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          actualClosure)) :
    SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
      (componentFamilyOfActualTopologyClosurePackage
        componentClosure) := by
  cases componentClosure_eq
  exact
    selectedFinitePQSpineFrameCoreLemma8RowsOfActualTopologyClosureGeneratedOrderRows
      (noCut := noCut) componentClosure rows

def selectedFinitePQSpineGeneratedCyclicRowsOfActualTopologyClosureEqGeneratedOrderRows
    {noCut : NoCutDependency}
    {componentClosure actualClosure :
      ActualTopologyComponentClosurePackage.{u}}
    (componentClosure_eq : componentClosure = actualClosure)
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          actualClosure)) :
    SelectedFinitePQSpineGeneratedCyclicRows
      (noCut := noCut)
      (components :=
        componentFamilyOfActualTopologyClosurePackage componentClosure)
      (selectedFinitePQSpineFrameCoreLemma8RowsOfActualTopologyClosureEqGeneratedOrderRows
        (noCut := noCut) componentClosure_eq rows) := by
  cases componentClosure_eq
  exact
    selectedFinitePQSpineGeneratedCyclicRowsOfActualTopologyClosureGeneratedOrderRows
      (noCut := noCut) componentClosure rows

/-- Selected-frame source package generated from finite `p_i/q_i` spine
rows and cyclic rows keyed to the generated frame rows. -/
def frameCyclicSourcePackageOfFinitePQSpineRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (generatedCyclicRows :
      SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := noCut) (components := components)
        finiteRows) :
    FrameCyclicSourcePackage.{u} noCut components :=
  frameCyclicOrderSourcePackageOfFinitePQSpineRows
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    finiteRows generatedCyclicRows

def frameCyclicSourcePackageOfFinitePQSpineGeneratedOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :
    FrameCyclicSourcePackage.{u} noCut components :=
  frameCyclicSourcePackageOfFinitePQSpineRows
    (noCut := noCut) (components := components)
    (selectedFinitePQSpineFrameCoreLemma8RowsOfGeneratedOrderRows
      (noCut := noCut) (components := components) rows)
    (selectedFinitePQSpineGeneratedCyclicRowsOfGeneratedOrderRows
      (noCut := noCut) (components := components) rows)

def frameCyclicRowsOfFinitePQSpineRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (generatedCyclicRows :
      SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := noCut) (components := components)
        finiteRows) :
    FrameCyclicRows.{u} noCut components :=
  frameCyclicRowsOfFrameCyclicSourcePackage
    (frameCyclicSourcePackageOfFinitePQSpineRows
      (noCut := noCut) (components := components)
      finiteRows generatedCyclicRows)

def frameCyclicRowsOfFinitePQSpineGeneratedOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :
    FrameCyclicRows.{u} noCut components :=
  frameCyclicRowsOfFrameCyclicSourcePackage
    (frameCyclicSourcePackageOfFinitePQSpineGeneratedOrderRows
      (noCut := noCut) (components := components) rows)

theorem frameCyclicSourcePackage_nonempty_of_finitePQSpineRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (generatedCyclicRows :
      SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := noCut) (components := components)
        finiteRows) :
    Nonempty (FrameCyclicSourcePackage.{u} noCut components) :=
  Nonempty.intro
    (frameCyclicSourcePackageOfFinitePQSpineRows
      (noCut := noCut) (components := components)
      finiteRows generatedCyclicRows)

theorem frameCyclicSourcePackage_nonempty_of_finitePQSpineGeneratedOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :
    Nonempty (FrameCyclicSourcePackage.{u} noCut components) :=
  Nonempty.intro
    (frameCyclicSourcePackageOfFinitePQSpineGeneratedOrderRows
      (noCut := noCut) (components := components) rows)

theorem frameCyclicRows_nonempty_of_finitePQSpineRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        components)
    (generatedCyclicRows :
      SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := noCut) (components := components)
        finiteRows) :
    Nonempty (FrameCyclicRows.{u} noCut components) :=
  Nonempty.intro
    (frameCyclicRowsOfFinitePQSpineRows
      (noCut := noCut) (components := components)
      finiteRows generatedCyclicRows)

theorem frameCyclicRows_nonempty_of_finitePQSpineGeneratedOrderRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        components) :
    Nonempty (FrameCyclicRows.{u} noCut components) :=
  Nonempty.intro
    (frameCyclicRowsOfFinitePQSpineGeneratedOrderRows
      (noCut := noCut) (components := components) rows)

theorem frameCyclicRows_nonempty_iff_sourcePackage
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) :
    Nonempty (FrameCyclicRows.{u} noCut components) <->
      Nonempty (FrameCyclicSourcePackage.{u} noCut components) :=
  uniformFrameCyclicOrderRows_nonempty_iff_sourcePackage
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)

theorem frameCyclicSourcePackage_nonempty_iff_frameCyclicRows
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) :
    Nonempty (FrameCyclicSourcePackage.{u} noCut components) <->
      Nonempty (FrameCyclicRows.{u} noCut components) :=
  (frameCyclicRows_nonempty_iff_sourcePackage
    (noCut := noCut) (components := components)).symm

def frameCyclicRowsOfActualTopologyClosureFrameSource
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    FrameCyclicRows.{u} noCut
      (componentFamilyOfActualTopologyClosurePackage componentClosure) :=
  frameCyclicRowsOfFrameCyclicSourcePackage frameSource

theorem frameCyclicRows_nonempty_of_actualTopologyClosureFrameSource
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    Nonempty
      (FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :=
  Nonempty.intro
    (frameCyclicRowsOfActualTopologyClosureFrameSource
      componentClosure frameSource)

def frameCyclicRowsOfActualTopologyRowsFrameSource
    {noCut : NoCutDependency}
    {topology : MinimalFailureActualSelectedTopologyRows}
    {components : ActualTopologyRemainingComponentRows.{u} topology}
    (frameSource :
      ActualTopologyClosureFrameSource.{u} noCut topology
        components) :
    ActualTopologyClosureFrameCyclicRows.{u} noCut topology
      components :=
  frameCyclicRowsOfFrameCyclicSourcePackage frameSource

theorem frameCyclicRows_nonempty_of_actualTopologyRowsFrameSource
    {noCut : NoCutDependency}
    {topology : MinimalFailureActualSelectedTopologyRows}
    {components : ActualTopologyRemainingComponentRows.{u} topology}
    (frameSource :
      ActualTopologyClosureFrameSource.{u} noCut topology
        components) :
    Nonempty
      (ActualTopologyClosureFrameCyclicRows.{u} noCut topology
        components) :=
  Nonempty.intro
    (frameCyclicRowsOfActualTopologyRowsFrameSource frameSource)

theorem actualTopologyClosureFrameSource_nonempty_iff_frameCyclicRows
    (noCut : NoCutDependency)
    (topology : MinimalFailureActualSelectedTopologyRows)
    (components : ActualTopologyRemainingComponentRows.{u} topology) :
    Nonempty
        (ActualTopologyClosureFrameSource.{u} noCut topology
          components) <->
      Nonempty
        (ActualTopologyClosureFrameCyclicRows.{u} noCut topology
          components) :=
  frameCyclicSourcePackage_nonempty_iff_frameCyclicRows
    (noCut := noCut)
    (components :=
      componentFamilyOfActualTopologyClosurePackage
        (actualTopologyClosurePackageOfActualTopologyRows topology
          components))

/-- Frame/cyclic source data keyed to an actual-topology component closure. -/
structure ActualTopologyFrameCyclicSourcePackage : Type (u + 1) where
  noCut : NoCutDependency
  componentClosure : ActualTopologyComponentClosurePackage.{u}
  frameSource :
    FrameCyclicSourcePackage.{u} noCut
      (componentFamilyOfActualTopologyClosurePackage componentClosure)

namespace ActualTopologyFrameCyclicSourcePackage

def components
    (P : ActualTopologyFrameCyclicSourcePackage.{u}) :
    ComponentFamily.{u} :=
  componentFamilyOfActualTopologyClosurePackage P.componentClosure

def frameCyclicRows
    (P : ActualTopologyFrameCyclicSourcePackage.{u}) :
    FrameCyclicRows.{u} P.noCut P.components :=
  frameCyclicRowsOfFrameCyclicSourcePackage P.frameSource

theorem frameSource_nonempty
    (P : ActualTopologyFrameCyclicSourcePackage.{u}) :
    Nonempty (FrameCyclicSourcePackage.{u} P.noCut P.components) :=
  Nonempty.intro P.frameSource

theorem frameCyclicRows_nonempty
    (P : ActualTopologyFrameCyclicSourcePackage.{u}) :
    Nonempty (FrameCyclicRows.{u} P.noCut P.components) :=
  Nonempty.intro P.frameCyclicRows

end ActualTopologyFrameCyclicSourcePackage

def actualTopologyFrameCyclicSourcePackageOfFrameSource
    (noCut : NoCutDependency)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    ActualTopologyFrameCyclicSourcePackage.{u} where
  noCut := noCut
  componentClosure := componentClosure
  frameSource := frameSource

/-- Actual-topology selected frame source generated from the finite
`p_i/q_i` spine rows.  This is the shape quantified over by the K23 route
coverage and W32 final assembly surfaces. -/
def actualTopologyClosureFrameSourceOfFinitePQSpineRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := noCut)
        (components :=
          componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows) :
    FrameCyclicSourcePackage.{u} noCut
      (componentFamilyOfActualTopologyClosurePackage
        componentClosure) :=
  frameCyclicSourcePackageOfFinitePQSpineRows
    (noCut := noCut)
    (components :=
      componentFamilyOfActualTopologyClosurePackage
        componentClosure)
    finiteRows generatedCyclicRows

def actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    FrameCyclicSourcePackage.{u} noCut
      (componentFamilyOfActualTopologyClosurePackage
        componentClosure) :=
  frameCyclicSourcePackageOfFinitePQSpineGeneratedOrderRows
    (noCut := noCut)
    (components :=
      componentFamilyOfActualTopologyClosurePackage
        componentClosure)
    rows

def actualTopologyFrameCyclicSourcePackageOfFinitePQSpineRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (finiteRows :
      SelectedFinitePQSpineFrameCoreLemma8Rows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := noCut)
        (components :=
          componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows) :
    ActualTopologyFrameCyclicSourcePackage.{u} :=
  actualTopologyFrameCyclicSourcePackageOfFrameSource
    noCut componentClosure
    (actualTopologyClosureFrameSourceOfFinitePQSpineRows
      (noCut := noCut) componentClosure finiteRows
      generatedCyclicRows)

def actualTopologyFrameCyclicSourcePackageOfFinitePQSpineGeneratedOrderRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    ActualTopologyFrameCyclicSourcePackage.{u} :=
  actualTopologyFrameCyclicSourcePackageOfFrameSource
    noCut componentClosure
    (actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
      (noCut := noCut) componentClosure rows)

theorem actualTopologyClosureFrameSource_nonempty_of_finitePQSpineGeneratedOrderRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    Nonempty
      (FrameCyclicSourcePackage.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :=
  Nonempty.intro
    (actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
      (noCut := noCut) componentClosure rows)

theorem actualTopologyFrameCyclicSourcePackage_nonempty_of_finitePQSpineGeneratedOrderRows
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      SelectedFinitePQSpineGeneratedOrderRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    Nonempty ActualTopologyFrameCyclicSourcePackage.{u} :=
  Nonempty.intro
    (actualTopologyFrameCyclicSourcePackageOfFinitePQSpineGeneratedOrderRows
      (noCut := noCut) componentClosure rows)

def actualTopologyFrameCyclicSourcePackageOfFrameCyclicRows
    (noCut : NoCutDependency)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    ActualTopologyFrameCyclicSourcePackage.{u} :=
  actualTopologyFrameCyclicSourcePackageOfFrameSource
    noCut componentClosure
    (frameCyclicSourcePackageOfFrameCyclicRows rows)

def actualTopologyFrameCyclicSourcePackageOfActualTopologyRowsFrameSource
    (noCut : NoCutDependency)
    (topology : MinimalFailureActualSelectedTopologyRows)
    (components : ActualTopologyRemainingComponentRows.{u} topology)
    (frameSource :
      ActualTopologyClosureFrameSource.{u} noCut topology
        components) :
    ActualTopologyFrameCyclicSourcePackage.{u} :=
  actualTopologyFrameCyclicSourcePackageOfFrameSource
    noCut
    (actualTopologyClosurePackageOfActualTopologyRows topology components)
    frameSource

def actualTopologyFrameCyclicSourcePackageOfActualTopologyRows
    (noCut : NoCutDependency)
    (topology : MinimalFailureActualSelectedTopologyRows)
    (components : ActualTopologyRemainingComponentRows.{u} topology)
    (rows :
      ActualTopologyClosureFrameCyclicRows.{u} noCut topology
        components) :
    ActualTopologyFrameCyclicSourcePackage.{u} :=
  actualTopologyFrameCyclicSourcePackageOfActualTopologyRowsFrameSource
    noCut topology components
    (frameCyclicSourcePackageOfFrameCyclicRows rows)

theorem actualTopologyFrameCyclicSourcePackage_nonempty_iff_sourcePackage :
    Nonempty ActualTopologyFrameCyclicSourcePackage.{u} <->
      Exists fun noCut : NoCutDependency =>
      Exists fun componentClosure :
          ActualTopologyComponentClosurePackage.{u} =>
        Nonempty
          (FrameCyclicSourcePackage.{u} noCut
            (componentFamilyOfActualTopologyClosurePackage
              componentClosure)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro P.noCut
            (Exists.intro P.componentClosure P.frameSource_nonempty)
  case mpr =>
    intro h
    cases h with
    | intro noCut hClosure =>
        cases hClosure with
        | intro componentClosure hSource =>
            cases hSource with
            | intro frameSource =>
                exact
                  Nonempty.intro
                    (actualTopologyFrameCyclicSourcePackageOfFrameSource
                      noCut componentClosure frameSource)

theorem actualTopologyFrameCyclicSourcePackage_nonempty_iff_frameCyclicRows :
    Nonempty ActualTopologyFrameCyclicSourcePackage.{u} <->
      Exists fun noCut : NoCutDependency =>
      Exists fun componentClosure :
          ActualTopologyComponentClosurePackage.{u} =>
        Nonempty
          (FrameCyclicRows.{u} noCut
            (componentFamilyOfActualTopologyClosurePackage
              componentClosure)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro P.noCut
            (Exists.intro P.componentClosure P.frameCyclicRows_nonempty)
  case mpr =>
    intro h
    cases h with
    | intro noCut hClosure =>
        cases hClosure with
        | intro componentClosure hRows =>
            cases hRows with
            | intro rows =>
                exact
                  Nonempty.intro
                    (actualTopologyFrameCyclicSourcePackageOfFrameCyclicRows
                      noCut componentClosure rows)

/-! ## Degree-bound and graph bridge names used by the degree-six route -/

namespace DegreeGraphBridge

abbrev UnitDistanceNeighborCardBound {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n) : Prop :=
  ((Finset.univ : Finset (Fin n)).filter
    (fun j =>
      Not (j = center) /\
        _root_.eucDist (C.pts j) (C.pts center) = 1)).card <= 6

theorem unitDistanceNeighborCardBound {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n) :
    UnitDistanceNeighborCardBound C center := by
  simpa [UnitDistanceNeighborCardBound] using
    DegreeBound.UDConfig.unitDistanceNeighborSet_card_le_six C center

theorem unitDistanceAdj_iff {n : Nat}
    (C : _root_.UDConfig n) (i j : Fin n) :
    GraphBridge.UnitDistanceAdj C i j <->
      _root_.eucDist (C.pts i) (C.pts j) = 1 :=
  GraphBridge.unitDistanceAdj_iff C i j

theorem simpleGraph_adj_iff_localGraph_adj {n : Nat}
    (C : _root_.UDConfig n) (i j : Fin n) :
    (GraphBridge.unitDistanceSimpleGraph C).Adj i j <->
      (GraphBridge.unitDistanceLocalGraph C).Adj i j :=
  GraphBridge.unitDistanceSimpleGraph_adj_iff_localGraph_adj C i j

end DegreeGraphBridge

end

end FrameCyclicOrderAssemblyW32
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW32FrameCyclicOrderSourcePackage
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.FrameCyclicOrderSourcePackage.{u}
    payForCut topologyArc

abbrev SwanepoelW32ExactDegreeSixGeneratedCyclicRowsBlocker
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Prop :=
  Swanepoel.FrameCyclicOrderAssemblyW32.ExactDegreeSixGeneratedCyclicRowsBlocker.{u}
    payForCut topologyArc

abbrev SwanepoelW32DegreeSixGeneratedCyclicRowPackage
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.DegreeSixGeneratedCyclicRowPackage.{u}
    payForCut topologyArc

abbrev SwanepoelW32FrameCyclicRows
    (noCut :
      Swanepoel.FrameCyclicOrderAssemblyW32.NoCutDependency)
    (components :
      Swanepoel.FrameCyclicOrderAssemblyW32.ComponentFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.FrameCyclicRows.{u}
    noCut components

abbrev SwanepoelW32FrameCyclicSourcePackage
    (noCut :
      Swanepoel.FrameCyclicOrderAssemblyW32.NoCutDependency)
    (components :
      Swanepoel.FrameCyclicOrderAssemblyW32.ComponentFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.FrameCyclicSourcePackage.{u}
    noCut components

abbrev SwanepoelW32ActualTopologyClosureFrameCyclicRows
    (noCut :
      Swanepoel.FrameCyclicOrderAssemblyW32.NoCutDependency)
    (topology :
      Swanepoel.FrameCyclicOrderAssemblyW32.MinimalFailureActualSelectedTopologyRows)
    (components :
      Swanepoel.FrameCyclicOrderAssemblyW32.ActualTopologyRemainingComponentRows.{u}
        topology) :
    Type (u + 1) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.ActualTopologyClosureFrameCyclicRows.{u}
    noCut topology components

abbrev SwanepoelW32ActualTopologyClosureFrameSource
    (noCut :
      Swanepoel.FrameCyclicOrderAssemblyW32.NoCutDependency)
    (topology :
      Swanepoel.FrameCyclicOrderAssemblyW32.MinimalFailureActualSelectedTopologyRows)
    (components :
      Swanepoel.FrameCyclicOrderAssemblyW32.ActualTopologyRemainingComponentRows.{u}
        topology) :
    Type (u + 1) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.ActualTopologyClosureFrameSource.{u}
    noCut topology components

abbrev SwanepoelW32ActualTopologyFrameCyclicSourcePackage :
    Type (u + 1) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.ActualTopologyFrameCyclicSourcePackage.{u}

theorem swanepoel_w32_sourcePackage_nonempty_iff_uniformFiniteRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (SwanepoelW32FrameCyclicOrderSourcePackage.{u}
          payForCut topologyArc) <->
      Nonempty
        (Swanepoel.FrameCyclicOrderAssemblyW32.UniformFiniteGeometryRows.{u}
          payForCut topologyArc) :=
  (Swanepoel.FrameCyclicOrderAssemblyW32.uniformFiniteGeometryRows_nonempty_iff_sourcePackage
    (payForCut := payForCut) (topologyArc := topologyArc)).symm

theorem swanepoel_w32_sourcePackage_nonempty_iff_exactRemainingPackage
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (SwanepoelW32FrameCyclicOrderSourcePackage.{u}
          payForCut topologyArc) <->
      Nonempty
        (Swanepoel.FrameCyclicOrderAssemblyW32.ExactRemainingPackage.{u}
          payForCut topologyArc) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.sourcePackage_nonempty_iff_exactRemainingPackage
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w32_degreeSixGeneratedPackage_nonempty_iff_exactBlocker
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (SwanepoelW32DegreeSixGeneratedCyclicRowPackage.{u}
          payForCut topologyArc) <->
      SwanepoelW32ExactDegreeSixGeneratedCyclicRowsBlocker.{u}
        payForCut topologyArc :=
  Swanepoel.FrameCyclicOrderAssemblyW32.degreeSixGeneratedCyclicRowPackage_nonempty_iff_exactBlocker
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w32_frameCyclicSourcePackage_nonempty_iff_frameCyclicRows
    (noCut :
      Swanepoel.FrameCyclicOrderAssemblyW32.NoCutDependency)
    (components :
      Swanepoel.FrameCyclicOrderAssemblyW32.ComponentFamily.{u}) :
    Nonempty
        (SwanepoelW32FrameCyclicSourcePackage.{u}
          noCut components) <->
      Nonempty
        (SwanepoelW32FrameCyclicRows.{u}
          noCut components) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.frameCyclicSourcePackage_nonempty_iff_frameCyclicRows
    (noCut := noCut) (components := components)

theorem swanepoel_w32_actualTopologyClosureFrameSource_nonempty_iff_frameCyclicRows
    (noCut :
      Swanepoel.FrameCyclicOrderAssemblyW32.NoCutDependency)
    (topology :
      Swanepoel.FrameCyclicOrderAssemblyW32.MinimalFailureActualSelectedTopologyRows)
    (components :
      Swanepoel.FrameCyclicOrderAssemblyW32.ActualTopologyRemainingComponentRows.{u}
        topology) :
    Nonempty
        (SwanepoelW32ActualTopologyClosureFrameSource.{u}
          noCut topology components) <->
      Nonempty
        (SwanepoelW32ActualTopologyClosureFrameCyclicRows.{u}
          noCut topology components) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSource_nonempty_iff_frameCyclicRows
    noCut topology components

theorem swanepoel_w32_actualTopologyFrameCyclicSourcePackage_nonempty_iff_frameCyclicRows :
    Nonempty SwanepoelW32ActualTopologyFrameCyclicSourcePackage.{u} <->
      Exists fun noCut :
          Swanepoel.FrameCyclicOrderAssemblyW32.NoCutDependency =>
      Exists fun componentClosure :
          Swanepoel.FrameCyclicOrderAssemblyW32.ActualTopologyComponentClosurePackage.{u} =>
        Nonempty
          (SwanepoelW32FrameCyclicRows.{u} noCut
            (Swanepoel.FrameCyclicOrderAssemblyW32.componentFamilyOfActualTopologyClosurePackage
              componentClosure)) :=
  Swanepoel.FrameCyclicOrderAssemblyW32.actualTopologyFrameCyclicSourcePackage_nonempty_iff_frameCyclicRows

theorem swanepoel_w32_exactDegreeSixGeneratedCyclicRows_iff_w31Blocker
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    SwanepoelW32ExactDegreeSixGeneratedCyclicRowsBlocker.{u}
        payForCut topologyArc <->
      Swanepoel.CyclicOrderRowsInhabitationW31.DegreeSixGeneratedFrameCyclicRowsBlocker.{u}
        payForCut topologyArc :=
  Swanepoel.FrameCyclicOrderAssemblyW32.exactDegreeSixGeneratedCyclicRowsBlocker_iff_w31Blocker
    (payForCut := payForCut) (topologyArc := topologyArc)

end Verified
end ErdosProblems1066
