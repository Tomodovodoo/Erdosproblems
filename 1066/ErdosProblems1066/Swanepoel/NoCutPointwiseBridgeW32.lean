import ErdosProblems1066.Swanepoel.PointwiseLaneProductInhabitationW31
import ErdosProblems1066.Swanepoel.NoCutBlockerEliminationW30
import ErdosProblems1066.Swanepoel.PointwiseProductDataClosureW30
import ErdosProblems1066.Swanepoel.LaneProductFinalClosureW30
import ErdosProblems1066.Swanepoel.NoEarlyRouteCoverageClosureW32
import ErdosProblems1066.Swanepoel.ExactFigureRowsAssemblyW32
import ErdosProblems1066.Swanepoel.ExtractedComponentsConcreteClosureW32

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W32 no-cut to pointwise/lane-product bridge

This file is a conditional bridge from the exact W30 no-cut blocker
elimination sources into the W31 pointwise component source package and the
W30 pointwise/lane-product source packages.

It does not introduce a root import, known-bound statement, or final target
route.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutPointwiseBridgeW32

universe u

noncomputable section

abbrev MinimalCutVertexBlockerExists : Prop :=
  NoCutBlockerEliminationW30.MinimalCutVertexBlockerExists

abbrev BlockerDegreeDeletionSource : Prop :=
  NoCutBlockerEliminationW30.BlockerDegreeDeletionSource

abbrev BlockerClosedDeletionReinsertionSource : Prop :=
  NoCutBlockerEliminationW30.BlockerClosedDeletionReinsertionSource

abbrev BlockerDirectDeletionReinsertionSource : Prop :=
  NoCutBlockerEliminationW30.BlockerDirectDeletionReinsertionSource

abbrev BlockerDeficientDeletionSource : Prop :=
  NoCutBlockerEliminationW30.BlockerDeficientDeletionSource

abbrev TupledBlockerEliminationSource : Prop :=
  NoCutBlockerEliminationW30.TupledBlockerEliminationSource

abbrev DeletionReinsertionEliminationSource : Prop :=
  NoCutBlockerEliminationW30.DeletionReinsertionEliminationSource

abbrev CanonicalBlockerEliminationSource : Prop :=
  NoCutBlockerEliminationW30.CanonicalBlockerEliminationSource

abbrev NoCutDependency : Prop :=
  PointwiseLaneProductInhabitationW31.NoCutDependency

abbrev MinimalFailureNoCutVertexFamily : Prop :=
  NoCutBlockerEliminationW24.MinimalFailureNoCutVertexFamily

abbrev NoCutVertexFamily : Prop :=
  MinimalFailureNoCutVertexFamily

abbrev MinimalClearedFailureEliminator : Prop :=
  MinimalGraphFacts.MinimalClearedFailureEliminator

abbrev MinimalFailureExclusion : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    Not (MinimalGraphFacts.IsMinimalClearedFailure C)

abbrev SmallestExactLocalDeletionDependency : Prop :=
  NoCutLocalDeletionConcreteW27.SmallestExactLocalDeletionDependency

abbrev CutPartitionLocalClosedNeighborhoodDeletionEliminator : Prop :=
  NoCutConcreteEliminationW26.CutPartitionLocalClosedNeighborhoodDeletionEliminator

abbrev CutPartitionDirectCardBoundCertificateEliminator : Prop :=
  NoCutConcreteEliminationW26.CutPartitionDirectCardBoundCertificateEliminator

abbrev CutPartitionTupledClosedNeighborhoodDeletionData : Prop :=
  NoCutLocalDeletionConcreteW27.CutPartitionTupledClosedNeighborhoodDeletionData

abbrev CutPartitionTupledDirectCardBoundDeletionData : Prop :=
  NoCutLocalDeletionConcreteW27.CutPartitionTupledDirectCardBoundDeletionData

abbrev CutPartitionDeficientNeighborhoodDeletionData : Prop :=
  NoCutLocalDeletionConcreteW27.CutPartitionDeficientNeighborhoodDeletionData

abbrev LiveCutPartitionDeletionPayloadSource : Prop :=
  NoCutLocalDeletionConcreteW27.LiveCutPartitionDeletionPayloadSource

abbrev CutPartitionPlusSideAvoidsCutDataSource : Prop :=
  NoCutBlockerEliminationW30.CutPartitionPlusSideAvoidsCutDataSource

abbrev CutPartitionPlusSideMinimalityWitnessAvoidsCutSource : Prop :=
  NoCutBlockerEliminationW30.CutPartitionPlusSideMinimalityWitnessAvoidsCutSource

abbrev NoBothPlusSidesCutForcedDataSource : Prop :=
  NoCutBlockerEliminationW30.NoBothPlusSidesCutForcedDataSource

abbrev CutPartitionCrossPairSideNeighborCardBound : Prop :=
  NoCutBlockerEliminationW30.CutPartitionCrossPairSideNeighborCardBound

abbrev CutPartitionCrossPairSideNeighborCardLowerBound : Prop :=
  NoCutBlockerEliminationW30.CutPartitionCrossPairSideNeighborCardLowerBound

abbrev ExtractedWitnessComponentFamily : Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.ExtractedWitnessComponentFamily.{u}

abbrev ActualTopologyExtractedComponentClosurePackage : Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.ActualTopologyExtractedComponentClosurePackage.{u}

def extractedWitnessComponentFamilyOfActualTopologyClosurePackage
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    ExtractedWitnessComponentFamily.{u} :=
  P.toExtractedWitnessComponentFamily

abbrev UniformFrameCyclicOrderRows
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u}) :
    Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.UniformFrameCyclicOrderRows.{u}
    noCut components

abbrev UniformFiniteGeometryRows
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u}) :
    Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.UniformFiniteGeometryRows.{u}
    noCut components

abbrev GeometrySourceFamily
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u}) :
    Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.GeometrySourceFamily.{u}
    noCut components

abbrev PayForCutOfNoCut
    (noCut : NoCutDependency) :
    PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily :=
  PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut

abbrev TopologyArcOfComponents
    (components : ExtractedWitnessComponentFamily.{u}) :
    PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u} :=
  PointwiseLaneProductInhabitationW31.TopologyArcOfComponents components

abbrev Lemma8ConcreteOfGeometrySource
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
      (PayForCutOfNoCut noCut) (TopologyArcOfComponents components) :=
  PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
    geometry

abbrev ConcreteNoEarlyRouteData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.ConcreteNoEarlyRouteData
    geometry

abbrev ExactFigureData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  ExactFigureRowsAssemblyW32.ExactFigureRowsAssemblyFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfComponents components)
    (Lemma8ConcreteOfGeometrySource geometry)

abbrev W31ExactFigureData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.ExactFigureData geometry

abbrev W31ComponentFrameNoEarlyFigureSourceData : Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.ComponentFrameNoEarlyFigureSourceData.{u}

abbrev PointwiseSourceData : Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.SourceData.{u}

abbrev PointwiseProductBlocker : Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.PointwiseProductBlocker.{u}

abbrev W26Product : Type (u + 1) :=
  PointwiseLaneProductInhabitationW31.W26Product.{u}

abbrev PointwiseUniformRouteFigureSourceData : Type (u + 1) :=
  PointwiseProductDataClosureW30.UniformRouteFigureSourceData.{u}

abbrev LaneProductSourceAlternatives : Prop :=
  LaneProductFinalClosureW30.LaneProductSourceAlternatives

abbrev W29FinalSourceGate : Prop :=
  LaneProductFinalClosureW30.W29FinalSourceGate

def geometrySourceFamilyOfFrameCyclicOrderRows
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    GeometrySourceFamily.{u} noCut components :=
  PointwiseLaneProductInhabitationW31.geometrySourceFamilyOfFrameCyclicOrderRows
    rows

abbrev RouteCoverageAvailable
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Prop :=
  NoEarlyRouteCoverageClosureW32.NoEarlyRouteCoverageAvailable.{u}
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

abbrev NoEarlyCoverageFamily
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Type (u + 1) :=
  NoEarlyRouteCoverageClosureW32.NoEarlyCoverageFamily.{u}
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

abbrev K23ObstructionFamily
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Type (u + 1) :=
  NoEarlyRouteCoverageClosureW32.K23ObstructionFamily.{u}
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

abbrev ThreeCommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Type (u + 1) :=
  NoEarlyRouteCoverageClosureW32.ThreeCommonNeighborObstructionFamily.{u}
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

abbrev CommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Type (u + 1) :=
  NoEarlyRouteCoverageClosureW32.CommonNeighborObstructionFamily.{u}
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

abbrev LocalExclusionObstructionFamily
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Type (u + 1) :=
  NoEarlyRouteCoverageClosureW32.LocalExclusionObstructionFamily.{u}
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

abbrev K23RouteCoverageData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Type (u + 1) :=
  NoEarlyRouteCoverageClosureW32.K23RouteCoverageData.{u}
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

abbrev ThreeCommonNeighborRouteCoverageData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Type (u + 1) :=
  NoEarlyRouteCoverageClosureW32.ThreeCommonNeighborRouteCoverageData.{u}
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

abbrev CommonNeighborRouteCoverageData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Type (u + 1) :=
  NoEarlyRouteCoverageClosureW32.CommonNeighborRouteCoverageData.{u}
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

abbrev LocalExclusionRouteCoverageData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Type (u + 1) :=
  NoEarlyRouteCoverageClosureW32.LocalExclusionRouteCoverageData.{u}
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

abbrev ConcreteNoEarlySourceFamily
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Type (u + 1) :=
  Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfComponents components)
    (Lemma8ConcreteOfGeometrySource
      (geometrySourceFamilyOfFrameCyclicOrderRows rows))

theorem routeData_nonempty_iff_routeCoverageAvailable
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)) <->
      RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeData_nonempty_iff_routeCoverage
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))

def routeDataOfRouteCoverageAvailable
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (h : RouteCoverageAvailable rows) :
    ConcreteNoEarlyRouteData
      (geometrySourceFamilyOfFrameCyclicOrderRows rows) :=
  Classical.choice
    ((routeData_nonempty_iff_routeCoverageAvailable rows).2 h)

theorem routeCoverageAvailable_of_concreteNoEarlySourceFamily
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (h : Nonempty (ConcreteNoEarlySourceFamily rows)) :
    RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeCoverage_of_concreteNoEarlySourceFamily
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    h

theorem routeCoverageAvailable_of_coverage_and_k23Obstruction
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (hobstruction : Nonempty (K23ObstructionFamily rows)) :
    RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeCoverage_of_coverage_and_k23Obstruction
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    hcoverage hobstruction

theorem routeCoverageAvailable_of_coverage_and_threeCommonNeighborObstruction
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (hobstruction :
      Nonempty (ThreeCommonNeighborObstructionFamily rows)) :
    RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeCoverage_of_coverage_and_threeCommonNeighborObstruction
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    hcoverage hobstruction

theorem routeCoverageAvailable_of_coverage_and_commonNeighborObstruction
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (hobstruction : Nonempty (CommonNeighborObstructionFamily rows)) :
    RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeCoverage_of_coverage_and_commonNeighborObstruction
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    hcoverage hobstruction

theorem routeCoverageAvailable_of_coverage_and_localExclusionObstruction
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (hobstruction : Nonempty (LocalExclusionObstructionFamily rows)) :
    RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeCoverage_of_coverage_and_localExclusionObstruction
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    hcoverage hobstruction

theorem routeCoverageAvailable_of_k23RouteCoverageData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (h : Nonempty (K23RouteCoverageData rows)) :
    RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeCoverage_of_k23RouteCoverageData
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    h

theorem routeCoverageAvailable_of_threeCommonNeighborRouteCoverageData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (h : Nonempty (ThreeCommonNeighborRouteCoverageData rows)) :
    RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeCoverage_of_threeCommonNeighborRouteCoverageData
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    h

theorem routeCoverageAvailable_of_commonNeighborRouteCoverageData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (h : Nonempty (CommonNeighborRouteCoverageData rows)) :
    RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeCoverage_of_commonNeighborRouteCoverageData
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    h

theorem routeCoverageAvailable_of_localExclusionRouteCoverageData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (h : Nonempty (LocalExclusionRouteCoverageData rows)) :
    RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeCoverage_of_localExclusionRouteCoverageData
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    h

def concreteNoEarlySourceFamilyOfRouteCoverageAvailable
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (h : RouteCoverageAvailable rows) :
    ConcreteNoEarlySourceFamily rows :=
  NoEarlyRouteCoverageClosureW32.concreteNoEarlySourceFamilyOfRouteCoverageAvailable
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    h

theorem concreteNoEarlySourceFamily_nonempty_of_routeCoverageAvailable
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {rows : UniformFrameCyclicOrderRows.{u} noCut components}
    (h : RouteCoverageAvailable rows) :
    Nonempty (ConcreteNoEarlySourceFamily rows) :=
  Nonempty.intro
    (concreteNoEarlySourceFamilyOfRouteCoverageAvailable h)

def w31ExactFigureDataOfExactFigureData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut components}
    (figures : ExactFigureData geometry) :
    W31ExactFigureData geometry :=
  figures.toExactFigureInequalityRowsFamily.toExactE22E23FigureData

structure ComponentFrameNoEarlyFigureSourceData : Type (u + 1) where
  noCut : NoCutDependency
  components : ExtractedWitnessComponentFamily.{u}
  frameCyclicRows :
    UniformFrameCyclicOrderRows.{u} noCut components
  routeData :
    ConcreteNoEarlyRouteData
      (geometrySourceFamilyOfFrameCyclicOrderRows frameCyclicRows)
  figureData :
    ExactFigureData
      (geometrySourceFamilyOfFrameCyclicOrderRows frameCyclicRows)

namespace ComponentFrameNoEarlyFigureSourceData

def boundary
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseLaneProductInhabitationW31.BoundaryFamily.{u} :=
  PointwiseLaneProductInhabitationW31.boundaryFamilyOfComponentFamily
    S.components

def topologySource
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseLaneProductInhabitationW31.BoundaryWitnessSourceFamily.{u} :=
  PointwiseLaneProductInhabitationW31.boundaryWitnessSourceFamilyOfComponentFamily
    S.components

def extractedTopology
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseLaneProductInhabitationW31.ExtractedWitnessFamily.{u} :=
  PointwiseLaneProductInhabitationW31.extractedWitnessFamilyOfComponentFamily
    S.components

def uniformRows
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    UniformFiniteGeometryRows.{u} S.noCut S.components :=
  PointwiseLaneProductInhabitationW31.uniformRowsOfFrameCyclicOrderRows
    S.frameCyclicRows

def geometry
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    GeometrySourceFamily.{u} S.noCut S.components :=
  geometrySourceFamilyOfFrameCyclicOrderRows S.frameCyclicRows

def w31ExactFigureData
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    W31ExactFigureData S.geometry :=
  w31ExactFigureDataOfExactFigureData S.figureData

def figureAngleData
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseLaneProductInhabitationW31.FigureAngleDataSourceFamily
      S.geometry :=
  PointwiseLaneProductInhabitationW31.figureAngleDataSourceFamilyOfExactFigureData
    S.w31ExactFigureData

def toW31ComponentFrameNoEarlyFigureSourceData
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    W31ComponentFrameNoEarlyFigureSourceData.{u} where
  noCut := S.noCut
  components := S.components
  frameCyclicRows := S.frameCyclicRows
  routeData := S.routeData
  figureData := S.w31ExactFigureData

def toSourceData
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseSourceData.{u} :=
  S.toW31ComponentFrameNoEarlyFigureSourceData.toSourceData

def toPointwiseProductBlocker
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseProductBlocker.{u} :=
  S.toW31ComponentFrameNoEarlyFigureSourceData.toPointwiseProductBlocker

def toW26Product
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    W26Product.{u} :=
  S.toW31ComponentFrameNoEarlyFigureSourceData.toW26Product

theorem sourceData_nonempty
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseSourceData.{u} :=
  Nonempty.intro S.toSourceData

theorem pointwiseProductBlocker_nonempty
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseProductBlocker.{u} :=
  Nonempty.intro S.toPointwiseProductBlocker

theorem w26Product_nonempty
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty W26Product.{u} :=
  Nonempty.intro S.toW26Product

end ComponentFrameNoEarlyFigureSourceData

/-! ## Exact no-cut blocker bridges -/

theorem noCutDependency_iff_not_minimalCutVertexBlockerExists :
    NoCutDependency <-> Not MinimalCutVertexBlockerExists :=
  PointwiseLaneProductInhabitationW31.noCutDependency_iff_not_minimalCutVertexBlocker

theorem noCutDependency_iff_noCutVertexFamily :
    NoCutDependency <-> NoCutVertexFamily :=
  noCutDependency_iff_not_minimalCutVertexBlockerExists.trans
    NoCutBlockerEliminationW24.not_blocker_iff_noCutVertexFamily

theorem noCutVertexFamily_iff_noCutDependency :
    NoCutVertexFamily <-> NoCutDependency :=
  noCutDependency_iff_noCutVertexFamily.symm

theorem noCutVertexFamily_iff_minimalFailureNoCutVertexFamily :
    NoCutVertexFamily <-> MinimalFailureNoCutVertexFamily :=
  Iff.rfl

theorem minimalFailureNoCutVertexFamily_iff_noCutVertexFamily :
    MinimalFailureNoCutVertexFamily <-> NoCutVertexFamily :=
  noCutVertexFamily_iff_minimalFailureNoCutVertexFamily.symm

theorem noCutDependency_iff_minimalFailureNoCutVertexFamily :
    NoCutDependency <-> MinimalFailureNoCutVertexFamily :=
  noCutDependency_iff_noCutVertexFamily.trans
    noCutVertexFamily_iff_minimalFailureNoCutVertexFamily

theorem minimalFailureNoCutVertexFamily_iff_noCutDependency :
    MinimalFailureNoCutVertexFamily <-> NoCutDependency :=
  noCutDependency_iff_minimalFailureNoCutVertexFamily.symm

theorem not_minimalCutVertexBlockerExists_iff_noCutVertexFamily :
    Not MinimalCutVertexBlockerExists <-> NoCutVertexFamily :=
  noCutDependency_iff_not_minimalCutVertexBlockerExists.symm.trans
    noCutDependency_iff_noCutVertexFamily

theorem noCutVertexFamily_iff_not_minimalCutVertexBlockerExists :
    NoCutVertexFamily <-> Not MinimalCutVertexBlockerExists :=
  not_minimalCutVertexBlockerExists_iff_noCutVertexFamily.symm

theorem noCutDependency_of_plusSideAvoidsCutDataSource
    (H : CutPartitionPlusSideAvoidsCutDataSource) :
    NoCutDependency :=
  noCutDependency_iff_not_minimalCutVertexBlockerExists.2
    (NoCutBlockerEliminationW30.not_minimalCutVertexBlockerExists_of_plusSideAvoidsCutDataSource
      H)

theorem cutPartitionPlusSideAvoidsCutDataSource_of_minimalityWitnessAvoidsCutSource
    (H : CutPartitionPlusSideMinimalityWitnessAvoidsCutSource) :
    CutPartitionPlusSideAvoidsCutDataSource :=
  NoCutBlockerEliminationW30.cutPartitionPlusSideAvoidsCutDataSource_of_minimalityWitnessAvoidsCutSource
    H

theorem noCutDependency_of_plusSideMinimalityWitnessAvoidsCutSource
    (H : CutPartitionPlusSideMinimalityWitnessAvoidsCutSource) :
    NoCutDependency :=
  noCutDependency_iff_not_minimalCutVertexBlockerExists.2
    (NoCutBlockerEliminationW30.not_minimalCutVertexBlockerExists_of_plusSideMinimalityWitnessAvoidsCutSource
      H)

theorem noBothPlusSidesCutForcedDataSource :
    NoBothPlusSidesCutForcedDataSource :=
  NoCutBlockerEliminationW30.noBothPlusSidesCutForcedDataSource

theorem cutPartitionPlusSideAvoidsCutDataSource_of_noBothPlusSidesCutForcedDataSource
    (H : NoBothPlusSidesCutForcedDataSource) :
    CutPartitionPlusSideAvoidsCutDataSource :=
  NoCutBlockerEliminationW30.cutPartitionPlusSideAvoidsCutDataSource_of_noBothPlusSidesCutForcedDataSource
    H

theorem cutPartitionPlusSideAvoidsCutDataSource_of_refuting_bothPlusSidesCutForced :
    CutPartitionPlusSideAvoidsCutDataSource :=
  NoCutBlockerEliminationW30.cutPartitionPlusSideAvoidsCutDataSource_of_refuting_bothPlusSidesCutForced

theorem noCutDependency_of_noBothPlusSidesCutForcedDataSource
    (H : NoBothPlusSidesCutForcedDataSource) :
    NoCutDependency :=
  noCutDependency_iff_not_minimalCutVertexBlockerExists.2
    (NoCutBlockerEliminationW30.not_minimalCutVertexBlockerExists_of_noBothPlusSidesCutForcedDataSource
      H)

theorem noCutDependency_of_refuting_bothPlusSidesCutForced :
    NoCutDependency :=
  noCutDependency_of_noBothPlusSidesCutForcedDataSource
    noBothPlusSidesCutForcedDataSource

theorem minimalFailureNoCutVertexFamily_of_plusSideAvoidsCutDataSource
    (H : CutPartitionPlusSideAvoidsCutDataSource) :
    MinimalFailureNoCutVertexFamily :=
  noCutDependency_iff_minimalFailureNoCutVertexFamily.1
    (noCutDependency_of_plusSideAvoidsCutDataSource H)

theorem minimalFailureNoCutVertexFamily_of_plusSideMinimalityWitnessAvoidsCutSource
    (H : CutPartitionPlusSideMinimalityWitnessAvoidsCutSource) :
    MinimalFailureNoCutVertexFamily :=
  noCutDependency_iff_minimalFailureNoCutVertexFamily.1
    (noCutDependency_of_plusSideMinimalityWitnessAvoidsCutSource H)

theorem minimalFailureNoCutVertexFamily_of_noBothPlusSidesCutForcedDataSource
    (H : NoBothPlusSidesCutForcedDataSource) :
    MinimalFailureNoCutVertexFamily :=
  noCutDependency_iff_minimalFailureNoCutVertexFamily.1
    (noCutDependency_of_noBothPlusSidesCutForcedDataSource H)

theorem minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced :
    MinimalFailureNoCutVertexFamily :=
  minimalFailureNoCutVertexFamily_of_noBothPlusSidesCutForcedDataSource
    noBothPlusSidesCutForcedDataSource

theorem plusSideAvoidsCutDataSource_iff_noCutDependency :
    CutPartitionPlusSideAvoidsCutDataSource <-> NoCutDependency :=
  NoCutBlockerEliminationW30.cutPartitionPlusSideAvoidsCutDataSource_iff_not_minimalCutVertexBlockerExists.trans
    noCutDependency_iff_not_minimalCutVertexBlockerExists.symm

theorem plusSideAvoidsCutDataSource_iff_minimalFailureNoCutVertexFamily :
    CutPartitionPlusSideAvoidsCutDataSource <->
      MinimalFailureNoCutVertexFamily :=
  plusSideAvoidsCutDataSource_iff_noCutDependency.trans
    noCutDependency_iff_minimalFailureNoCutVertexFamily

theorem plusSideAvoidsCutDataSource_of_minimalFailureNoCutVertexFamily
    (H : MinimalFailureNoCutVertexFamily) :
    CutPartitionPlusSideAvoidsCutDataSource :=
  plusSideAvoidsCutDataSource_iff_minimalFailureNoCutVertexFamily.2 H

theorem cutPartitionCrossPairSideNeighborCardLowerBound_of_minimalFailure :
    CutPartitionCrossPairSideNeighborCardLowerBound :=
  NoCutBlockerEliminationW30.cutPartitionCrossPairSideNeighborCardLowerBound_of_minimalFailure

theorem noCutDependency_of_sideNeighborCardBound
    (H : CutPartitionCrossPairSideNeighborCardBound) :
    NoCutDependency :=
  noCutDependency_iff_not_minimalCutVertexBlockerExists.2
    (NoCutBlockerEliminationW30.not_minimalCutVertexBlockerExists_of_sideNeighborCardBound
      H)

theorem tupledClosedNeighborhoodDeletionData_iff_noCutDependency :
    CutPartitionTupledClosedNeighborhoodDeletionData <->
      NoCutDependency :=
  NoCutLocalDeletionConcreteW27.cutPartitionTupledClosedNeighborhoodDeletionData_iff_noCutVertexFamily.trans
    noCutVertexFamily_iff_noCutDependency

theorem tupledClosedNeighborhoodDeletionData_iff_minimalFailureNoCutVertexFamily :
    CutPartitionTupledClosedNeighborhoodDeletionData <->
      MinimalFailureNoCutVertexFamily :=
  NoCutLocalDeletionConcreteW27.cutPartitionTupledClosedNeighborhoodDeletionData_iff_noCutVertexFamily.trans
    noCutVertexFamily_iff_minimalFailureNoCutVertexFamily

theorem degreeDeletionSource_iff_noCutDependency :
    BlockerDegreeDeletionSource <-> NoCutDependency :=
  Iff.trans
    NoCutBlockerEliminationW30.degreeDeletionSource_iff_not_minimalCutVertexBlockerExists
    noCutDependency_iff_not_minimalCutVertexBlockerExists.symm

theorem closedDeletionReinsertionSource_iff_noCutDependency :
    BlockerClosedDeletionReinsertionSource <-> NoCutDependency :=
  Iff.trans
    NoCutBlockerEliminationW30.closedDeletionReinsertionSource_iff_not_minimalCutVertexBlockerExists
    noCutDependency_iff_not_minimalCutVertexBlockerExists.symm

theorem directDeletionReinsertionSource_iff_noCutDependency :
    BlockerDirectDeletionReinsertionSource <-> NoCutDependency :=
  Iff.trans
    NoCutBlockerEliminationW30.directDeletionReinsertionSource_iff_not_minimalCutVertexBlockerExists
    noCutDependency_iff_not_minimalCutVertexBlockerExists.symm

theorem deficientDeletionSource_iff_noCutDependency :
    BlockerDeficientDeletionSource <-> NoCutDependency :=
  Iff.trans
    NoCutBlockerEliminationW30.deficientDeletionSource_iff_not_minimalCutVertexBlockerExists
    noCutDependency_iff_not_minimalCutVertexBlockerExists.symm

theorem tupledBlockerEliminationSource_iff_noCutDependency :
    TupledBlockerEliminationSource <-> NoCutDependency :=
  Iff.trans
    NoCutBlockerEliminationW30.tupledEliminationSource_iff_not_minimalCutVertexBlockerExists
    noCutDependency_iff_not_minimalCutVertexBlockerExists.symm

theorem deletionReinsertionEliminationSource_iff_noCutDependency :
    DeletionReinsertionEliminationSource <-> NoCutDependency :=
  Iff.trans
    NoCutBlockerEliminationW30.deletionReinsertionEliminationSource_iff_not_minimalCutVertexBlockerExists
    noCutDependency_iff_not_minimalCutVertexBlockerExists.symm

theorem canonicalBlockerEliminationSource_iff_noCutDependency :
    CanonicalBlockerEliminationSource <-> NoCutDependency :=
  Iff.trans
    NoCutBlockerEliminationW30.canonicalEliminationSource_iff_not_minimalCutVertexBlockerExists
    noCutDependency_iff_not_minimalCutVertexBlockerExists.symm

def noCutDependencyOfNotMinimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    NoCutDependency :=
  noCutDependency_iff_not_minimalCutVertexBlockerExists.2 hno

def noCutDependencyOfNoCutVertexFamily
    (H : NoCutVertexFamily) :
    NoCutDependency :=
  noCutVertexFamily_iff_noCutDependency.1 H

def noCutDependencyOfMinimalFailureNoCutVertexFamily
    (H : MinimalFailureNoCutVertexFamily) :
    NoCutDependency :=
  minimalFailureNoCutVertexFamily_iff_noCutDependency.1 H

def noCutDependencyOfCutPartitionPlusSideAvoidsCutDataSource
    (H : CutPartitionPlusSideAvoidsCutDataSource) :
    NoCutDependency :=
  noCutDependency_of_plusSideAvoidsCutDataSource H

def minimalFailureNoCutVertexFamilyOfNoCutDependency
    (noCut : NoCutDependency) :
    MinimalFailureNoCutVertexFamily :=
  noCutDependency_iff_minimalFailureNoCutVertexFamily.1 noCut

def noCutVertexFamilyOfNoCutDependency
    (noCut : NoCutDependency) :
    NoCutVertexFamily :=
  noCutDependency_iff_noCutVertexFamily.1 noCut

theorem noCutDependency_of_minimalFailureNoCutVertexFamily
    (H : MinimalFailureNoCutVertexFamily) :
    NoCutDependency :=
  noCutDependencyOfMinimalFailureNoCutVertexFamily H

theorem noCutDependency_of_cutPartitionPlusSideAvoidsCutDataSource
    (H : CutPartitionPlusSideAvoidsCutDataSource) :
    NoCutDependency :=
  noCutDependencyOfCutPartitionPlusSideAvoidsCutDataSource H

theorem minimalFailureNoCutVertexFamily_of_noCutDependency
    (noCut : NoCutDependency) :
    MinimalFailureNoCutVertexFamily :=
  minimalFailureNoCutVertexFamilyOfNoCutDependency noCut

def noCutVertexFamilyOfNotMinimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    NoCutVertexFamily :=
  not_minimalCutVertexBlockerExists_iff_noCutVertexFamily.1 hno

theorem noCutVertexFamily_of_not_minimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    NoCutVertexFamily :=
  noCutVertexFamilyOfNotMinimalCutVertexBlockerExists hno

def noCutDependencyOfDegreeDeletionSource
    (H : BlockerDegreeDeletionSource) :
    NoCutDependency :=
  degreeDeletionSource_iff_noCutDependency.1 H

def noCutDependencyOfClosedDeletionReinsertionSource
    (H : BlockerClosedDeletionReinsertionSource) :
    NoCutDependency :=
  closedDeletionReinsertionSource_iff_noCutDependency.1 H

def noCutDependencyOfDirectDeletionReinsertionSource
    (H : BlockerDirectDeletionReinsertionSource) :
    NoCutDependency :=
  directDeletionReinsertionSource_iff_noCutDependency.1 H

def noCutDependencyOfDeficientDeletionSource
    (H : BlockerDeficientDeletionSource) :
    NoCutDependency :=
  deficientDeletionSource_iff_noCutDependency.1 H

def noCutDependencyOfTupledBlockerEliminationSource
    (H : TupledBlockerEliminationSource) :
    NoCutDependency :=
  tupledBlockerEliminationSource_iff_noCutDependency.1 H

def noCutDependencyOfDeletionReinsertionEliminationSource
    (H : DeletionReinsertionEliminationSource) :
    NoCutDependency :=
  deletionReinsertionEliminationSource_iff_noCutDependency.1 H

def noCutDependencyOfCanonicalBlockerEliminationSource
    (H : CanonicalBlockerEliminationSource) :
    NoCutDependency :=
  canonicalBlockerEliminationSource_iff_noCutDependency.1 H

def canonicalBlockerEliminationSourceOfNoCutDependency
    (noCut : NoCutDependency) :
    CanonicalBlockerEliminationSource :=
  canonicalBlockerEliminationSource_iff_noCutDependency.2 noCut

/-! ## Minimality/local-deletion lifts to no-cut source evidence -/

theorem not_minimalCutVertexBlockerExists_of_minimalClearedFailureEliminator
    (H : MinimalClearedFailureEliminator) :
    Not MinimalCutVertexBlockerExists :=
  NoCutSourceConcreteW23.not_blocker_of_minimalClearedFailureEliminator H

theorem not_minimalCutVertexBlockerExists_of_no_minimalClearedFailure
    (H : MinimalFailureExclusion) :
    Not MinimalCutVertexBlockerExists := by
  intro hBlocker
  cases hBlocker with
  | intro B =>
      exact H B.C B.minimal

theorem noCutVertexFamily_of_no_minimalClearedFailure
    (H : MinimalFailureExclusion) :
    NoCutVertexFamily := by
  intro n C hmin
  exact False.elim (H C hmin)

theorem not_minimalCutVertexBlockerExists_of_smallestExactLocalDeletionDependency
    (H : SmallestExactLocalDeletionDependency) :
    Not MinimalCutVertexBlockerExists :=
  NoCutLocalDeletionConcreteW27.smallestExactLocalDeletionDependency_iff_not_minimalCutVertexBlocker.1
    H

theorem not_minimalCutVertexBlockerExists_of_localClosedNeighborhoodDeletion
    (H : CutPartitionLocalClosedNeighborhoodDeletionEliminator) :
    Not MinimalCutVertexBlockerExists :=
  NoCutLocalDeletionConcreteW27.cutPartitionLocalClosedNeighborhoodDeletionEliminator_iff_not_minimalCutVertexBlocker.1
    H

theorem not_minimalCutVertexBlockerExists_of_directCardBoundCertificate
    (H : CutPartitionDirectCardBoundCertificateEliminator) :
    Not MinimalCutVertexBlockerExists :=
  NoCutLocalDeletionConcreteW27.cutPartitionDirectCardBoundCertificateEliminator_iff_not_minimalCutVertexBlocker.1
    H

theorem not_minimalCutVertexBlockerExists_of_tupledClosedNeighborhoodDeletionData
    (H : CutPartitionTupledClosedNeighborhoodDeletionData) :
    Not MinimalCutVertexBlockerExists :=
  NoCutLocalDeletionConcreteW27.not_nonempty_minimalCutVertexBlocker_of_tupledClosedNeighborhood
    H

theorem not_minimalCutVertexBlockerExists_of_tupledDirectCardBoundDeletionData
    (H : CutPartitionTupledDirectCardBoundDeletionData) :
    Not MinimalCutVertexBlockerExists :=
  NoCutLocalDeletionConcreteW27.not_nonempty_minimalCutVertexBlocker_of_tupledDirectCardBound
    H

theorem not_minimalCutVertexBlockerExists_of_deficientNeighborhoodDeletionData
    (H : CutPartitionDeficientNeighborhoodDeletionData) :
    Not MinimalCutVertexBlockerExists :=
  NoCutLocalDeletionConcreteW27.not_nonempty_minimalCutVertexBlocker_of_deficientNeighborhood
    H

theorem not_minimalCutVertexBlockerExists_of_liveCutPartitionDeletionPayloadSource
    (H : LiveCutPartitionDeletionPayloadSource) :
    Not MinimalCutVertexBlockerExists :=
  not_minimalCutVertexBlockerExists_iff_noCutVertexFamily.2
    (NoCutLocalDeletionConcreteW27.noCutVertexFamily_of_liveCutPartitionDeletionPayloadSource
      H)

theorem liveCutPartitionDeletionPayloadSource_iff_not_minimalCutVertexBlockerExists :
    LiveCutPartitionDeletionPayloadSource <->
      Not MinimalCutVertexBlockerExists :=
  Iff.intro
    not_minimalCutVertexBlockerExists_of_liveCutPartitionDeletionPayloadSource
    (fun hno n C hmin P =>
      False.elim (hno
        (Nonempty.intro
          { n := n
            C := C
            minimal := hmin
            cut := P })))

def noCutDependencyOfMinimalClearedFailureEliminator
    (H : MinimalClearedFailureEliminator) :
    NoCutDependency :=
  noCutDependencyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_minimalClearedFailureEliminator H)

def noCutDependencyOfNoMinimalClearedFailure
    (H : MinimalFailureExclusion) :
    NoCutDependency :=
  noCutDependencyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_no_minimalClearedFailure H)

def noCutVertexFamilyOfMinimalClearedFailureEliminator
    (H : MinimalClearedFailureEliminator) :
    NoCutVertexFamily :=
  noCutVertexFamilyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_minimalClearedFailureEliminator H)

def noCutVertexFamilyOfNoMinimalClearedFailure
    (H : MinimalFailureExclusion) :
    NoCutVertexFamily :=
  noCutVertexFamilyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_no_minimalClearedFailure H)

theorem noCutVertexFamily_of_minimalClearedFailureEliminator
    (H : MinimalClearedFailureEliminator) :
    NoCutVertexFamily :=
  noCutVertexFamilyOfMinimalClearedFailureEliminator H

theorem noCutDependency_of_no_minimalClearedFailure
    (H : MinimalFailureExclusion) :
    NoCutDependency :=
  noCutDependencyOfNoMinimalClearedFailure H

theorem minimalFailureNoCutVertexFamily_of_no_minimalClearedFailure
    (H : MinimalFailureExclusion) :
    MinimalFailureNoCutVertexFamily :=
  noCutVertexFamilyOfNoMinimalClearedFailure H

def canonicalBlockerEliminationSourceOfMinimalClearedFailureEliminator
    (H : MinimalClearedFailureEliminator) :
    CanonicalBlockerEliminationSource :=
  canonicalBlockerEliminationSourceOfNoCutDependency
    (noCutDependencyOfMinimalClearedFailureEliminator H)

def canonicalBlockerEliminationSourceOfNoMinimalClearedFailure
    (H : MinimalFailureExclusion) :
    CanonicalBlockerEliminationSource :=
  canonicalBlockerEliminationSourceOfNoCutDependency
    (noCutDependencyOfNoMinimalClearedFailure H)

def noCutDependencyOfSmallestExactLocalDeletionDependency
    (H : SmallestExactLocalDeletionDependency) :
    NoCutDependency :=
  noCutDependencyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_smallestExactLocalDeletionDependency H)

def noCutVertexFamilyOfSmallestExactLocalDeletionDependency
    (H : SmallestExactLocalDeletionDependency) :
    NoCutVertexFamily :=
  noCutVertexFamilyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_smallestExactLocalDeletionDependency H)

theorem noCutVertexFamily_of_smallestExactLocalDeletionDependency
    (H : SmallestExactLocalDeletionDependency) :
    NoCutVertexFamily :=
  noCutVertexFamilyOfSmallestExactLocalDeletionDependency H

def canonicalBlockerEliminationSourceOfSmallestExactLocalDeletionDependency
    (H : SmallestExactLocalDeletionDependency) :
    CanonicalBlockerEliminationSource :=
  canonicalBlockerEliminationSourceOfNoCutDependency
    (noCutDependencyOfSmallestExactLocalDeletionDependency H)

def noCutDependencyOfLocalClosedNeighborhoodDeletion
    (H : CutPartitionLocalClosedNeighborhoodDeletionEliminator) :
    NoCutDependency :=
  noCutDependencyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_localClosedNeighborhoodDeletion H)

def canonicalBlockerEliminationSourceOfLocalClosedNeighborhoodDeletion
    (H : CutPartitionLocalClosedNeighborhoodDeletionEliminator) :
    CanonicalBlockerEliminationSource :=
  canonicalBlockerEliminationSourceOfNoCutDependency
    (noCutDependencyOfLocalClosedNeighborhoodDeletion H)

def noCutDependencyOfDirectCardBoundCertificate
    (H : CutPartitionDirectCardBoundCertificateEliminator) :
    NoCutDependency :=
  noCutDependencyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_directCardBoundCertificate H)

def canonicalBlockerEliminationSourceOfDirectCardBoundCertificate
    (H : CutPartitionDirectCardBoundCertificateEliminator) :
    CanonicalBlockerEliminationSource :=
  canonicalBlockerEliminationSourceOfNoCutDependency
    (noCutDependencyOfDirectCardBoundCertificate H)

def noCutDependencyOfTupledClosedNeighborhoodDeletionData
    (H : CutPartitionTupledClosedNeighborhoodDeletionData) :
    NoCutDependency :=
  noCutDependencyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_tupledClosedNeighborhoodDeletionData H)

def canonicalBlockerEliminationSourceOfTupledClosedNeighborhoodDeletionData
    (H : CutPartitionTupledClosedNeighborhoodDeletionData) :
    CanonicalBlockerEliminationSource :=
  canonicalBlockerEliminationSourceOfNoCutDependency
    (noCutDependencyOfTupledClosedNeighborhoodDeletionData H)

def noCutDependencyOfTupledDirectCardBoundDeletionData
    (H : CutPartitionTupledDirectCardBoundDeletionData) :
    NoCutDependency :=
  noCutDependencyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_tupledDirectCardBoundDeletionData H)

def canonicalBlockerEliminationSourceOfTupledDirectCardBoundDeletionData
    (H : CutPartitionTupledDirectCardBoundDeletionData) :
    CanonicalBlockerEliminationSource :=
  canonicalBlockerEliminationSourceOfNoCutDependency
    (noCutDependencyOfTupledDirectCardBoundDeletionData H)

def noCutDependencyOfDeficientNeighborhoodDeletionData
    (H : CutPartitionDeficientNeighborhoodDeletionData) :
    NoCutDependency :=
  noCutDependencyOfNotMinimalCutVertexBlockerExists
    (not_minimalCutVertexBlockerExists_of_deficientNeighborhoodDeletionData H)

def canonicalBlockerEliminationSourceOfDeficientNeighborhoodDeletionData
    (H : CutPartitionDeficientNeighborhoodDeletionData) :
    CanonicalBlockerEliminationSource :=
  canonicalBlockerEliminationSourceOfNoCutDependency
    (noCutDependencyOfDeficientNeighborhoodDeletionData H)

def noCutDependencyOfLiveCutPartitionDeletionPayloadSource
    (H : LiveCutPartitionDeletionPayloadSource) :
    NoCutDependency :=
  noCutDependencyOfNoCutVertexFamily
    (NoCutLocalDeletionConcreteW27.noCutVertexFamily_of_liveCutPartitionDeletionPayloadSource
      H)

def noCutVertexFamilyOfLiveCutPartitionDeletionPayloadSource
    (H : LiveCutPartitionDeletionPayloadSource) :
    NoCutVertexFamily :=
  NoCutLocalDeletionConcreteW27.noCutVertexFamily_of_liveCutPartitionDeletionPayloadSource
    H

theorem noCutVertexFamily_of_liveCutPartitionDeletionPayloadSource
    (H : LiveCutPartitionDeletionPayloadSource) :
    NoCutVertexFamily :=
  noCutVertexFamilyOfLiveCutPartitionDeletionPayloadSource H

def canonicalBlockerEliminationSourceOfLiveCutPartitionDeletionPayloadSource
    (H : LiveCutPartitionDeletionPayloadSource) :
    CanonicalBlockerEliminationSource :=
  canonicalBlockerEliminationSourceOfNoCutDependency
    (noCutDependencyOfLiveCutPartitionDeletionPayloadSource H)

/-! ## Component source constructors -/

def componentFrameNoEarlyFigureSourceDataOfNoCut
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows : UniformFrameCyclicOrderRows.{u} noCut components)
    (routeData :
      ConcreteNoEarlyRouteData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    (figureData :
      ExactFigureData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows)) :
    ComponentFrameNoEarlyFigureSourceData.{u} where
  noCut := noCut
  components := components
  frameCyclicRows := rows
  routeData := routeData
  figureData := figureData

def componentFrameNoEarlyFigureSourceDataOfNotMinimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfNotMinimalCutVertexBlockerExists hno)
        components)
    (routeData :
      ConcreteNoEarlyRouteData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    (figureData :
      ExactFigureData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows)) :
    ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceDataOfNoCut
    (noCutDependencyOfNotMinimalCutVertexBlockerExists hno)
    components rows routeData figureData

def componentFrameNoEarlyFigureSourceDataOfCanonicalBlockerEliminationSource
    (H : CanonicalBlockerEliminationSource)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        components)
    (routeData :
      ConcreteNoEarlyRouteData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    (figureData :
      ExactFigureData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows)) :
    ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceDataOfNoCut
    (noCutDependencyOfCanonicalBlockerEliminationSource H)
    components rows routeData figureData

def componentFrameNoEarlyFigureSourceDataOfActualTopologyClosurePackage
    (noCut : NoCutDependency)
    (componentClosure : ActualTopologyExtractedComponentClosurePackage.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u} noCut
        (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (routeData :
      ConcreteNoEarlyRouteData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    (figureData :
      ExactFigureData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows)) :
    ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceDataOfNoCut
    noCut
    (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
      componentClosure)
    rows routeData figureData

def componentFrameNoEarlyFigureSourceDataOfCanonicalBlockerEliminationAndActualTopologyClosurePackage
    (H : CanonicalBlockerEliminationSource)
    (componentClosure : ActualTopologyExtractedComponentClosurePackage.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (routeData :
      ConcreteNoEarlyRouteData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    (figureData :
      ExactFigureData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows)) :
    ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceDataOfActualTopologyClosurePackage
    (noCutDependencyOfCanonicalBlockerEliminationSource H)
    componentClosure rows routeData figureData

def componentFrameNoEarlyFigureSourceDataOfNoCutRouteCoverage
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows : UniformFrameCyclicOrderRows.{u} noCut components)
    (routeCoverage : RouteCoverageAvailable rows)
    (figureData :
      ExactFigureData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows)) :
    ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceDataOfNoCut
    noCut components rows
    (routeDataOfRouteCoverageAvailable routeCoverage)
    figureData

def componentFrameNoEarlyFigureSourceDataOfCanonicalBlockerEliminationRouteCoverage
    (H : CanonicalBlockerEliminationSource)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        components)
    (routeCoverage : RouteCoverageAvailable rows)
    (figureData :
      ExactFigureData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows)) :
    ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceDataOfNoCutRouteCoverage
    (noCutDependencyOfCanonicalBlockerEliminationSource H)
    components rows routeCoverage figureData

def componentFrameNoEarlyFigureSourceDataOfActualTopologyRouteCoverage
    (noCut : NoCutDependency)
    (componentClosure : ActualTopologyExtractedComponentClosurePackage.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u} noCut
        (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (routeCoverage : RouteCoverageAvailable rows)
    (figureData :
      ExactFigureData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows)) :
    ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceDataOfNoCutRouteCoverage
    noCut
    (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
      componentClosure)
    rows routeCoverage figureData

def pointwiseUniformRouteFigureSourceDataOfComponentSource
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseUniformRouteFigureSourceData.{u} where
  noCut := S.noCut
  boundary := S.boundary
  uniformRows := S.uniformRows
  routeData := S.routeData
  figureData := S.figureAngleData

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_noCut
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows : UniformFrameCyclicOrderRows.{u} noCut components)
    (hRoute :
      Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} := by
  cases hRoute with
  | intro routeData =>
      cases hFigure with
      | intro figureData =>
          exact
            Nonempty.intro
              (componentFrameNoEarlyFigureSourceDataOfNoCut
                noCut components rows routeData figureData)

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_canonicalBlockerEliminationSource
    (H : CanonicalBlockerEliminationSource)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        components)
    (hRoute :
      Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceData_nonempty_of_noCut
    (noCutDependencyOfCanonicalBlockerEliminationSource H)
    components rows hRoute hFigure

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_actualTopologyClosurePackage
    (noCut : NoCutDependency)
    (componentClosure : ActualTopologyExtractedComponentClosurePackage.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u} noCut
        (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceData_nonempty_of_noCut
    noCut
    (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
      componentClosure)
    rows hRoute hFigure

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_canonicalBlockerEliminationAndActualTopologyClosurePackage
    (H : CanonicalBlockerEliminationSource)
    (componentClosure : ActualTopologyExtractedComponentClosurePackage.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceData_nonempty_of_actualTopologyClosurePackage
    (noCutDependencyOfCanonicalBlockerEliminationSource H)
    componentClosure rows hRoute hFigure

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_noCut_routeCoverage
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows : UniformFrameCyclicOrderRows.{u} noCut components)
    (hRoute : RouteCoverageAvailable rows)
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceData_nonempty_of_noCut
    noCut components rows
    ((routeData_nonempty_iff_routeCoverageAvailable rows).2 hRoute)
    hFigure

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_canonicalBlockerEliminationRouteCoverage
    (H : CanonicalBlockerEliminationSource)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        components)
    (hRoute : RouteCoverageAvailable rows)
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceData_nonempty_of_noCut_routeCoverage
    (noCutDependencyOfCanonicalBlockerEliminationSource H)
    components rows hRoute hFigure

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_actualTopologyRouteCoverage
    (noCut : NoCutDependency)
    (componentClosure : ActualTopologyExtractedComponentClosurePackage.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u} noCut
        (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute : RouteCoverageAvailable rows)
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceData_nonempty_of_noCut_routeCoverage
    noCut
    (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
      componentClosure)
    rows hRoute hFigure

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_noCut_concreteNoEarlySourceFamily
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows : UniformFrameCyclicOrderRows.{u} noCut components)
    (hRoute : Nonempty (ConcreteNoEarlySourceFamily rows))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceData_nonempty_of_noCut_routeCoverage
    noCut components rows
    (routeCoverageAvailable_of_concreteNoEarlySourceFamily hRoute)
    hFigure

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_actualTopologyConcreteNoEarlySourceFamily
    (noCut : NoCutDependency)
    (componentClosure : ActualTopologyExtractedComponentClosurePackage.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u} noCut
        (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute : Nonempty (ConcreteNoEarlySourceFamily rows))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceData_nonempty_of_actualTopologyRouteCoverage
    noCut componentClosure rows
    (routeCoverageAvailable_of_concreteNoEarlySourceFamily hRoute)
    hFigure

theorem pointwiseSourceData_nonempty_of_componentSource
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseSourceData.{u} := by
  cases h with
  | intro S =>
      exact S.sourceData_nonempty

theorem pointwiseProductBlocker_nonempty_of_componentSource
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseProductBlocker.{u} := by
  cases h with
  | intro S =>
      exact S.pointwiseProductBlocker_nonempty

theorem w26Product_nonempty_of_componentSource
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty W26Product.{u} := by
  cases h with
  | intro S =>
      exact S.w26Product_nonempty

theorem pointwiseProductDataClosure_sourceData_nonempty_of_componentSource
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseProductDataClosureW30.SourceData.{u} := by
  cases h with
  | intro S =>
      exact
        Nonempty.intro
            (pointwiseUniformRouteFigureSourceDataOfComponentSource S).toSourceData

theorem componentFrameNoEarlyFigureSourceData_nonempty_iff :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} <->
      Exists fun noCut : NoCutDependency =>
        Exists fun components : ExtractedWitnessComponentFamily.{u} =>
          Exists fun rows :
              UniformFrameCyclicOrderRows.{u} noCut components =>
            Nonempty
                (ConcreteNoEarlyRouteData
                  (geometrySourceFamilyOfFrameCyclicOrderRows rows)) /\
              Nonempty
                (ExactFigureData
                  (geometrySourceFamilyOfFrameCyclicOrderRows rows)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.noCut
            (Exists.intro S.components
              (Exists.intro S.frameCyclicRows
                (And.intro
                  (Nonempty.intro S.routeData)
                  (Nonempty.intro S.figureData))))
  case mpr =>
    intro h
    cases h with
    | intro noCut hComponents =>
        cases hComponents with
        | intro components hRows =>
            cases hRows with
            | intro rows hData =>
                cases hData.1 with
                | intro routeData =>
                    cases hData.2 with
                    | intro figureData =>
                        exact
                          Nonempty.intro
                            { noCut := noCut
                              components := components
                              frameCyclicRows := rows
                              routeData := routeData
                              figureData := figureData }

theorem not_componentFrameNoEarlyFigureSourceData_iff :
    Not (Nonempty ComponentFrameNoEarlyFigureSourceData.{u}) <->
      Not
        (Exists fun noCut : NoCutDependency =>
          Exists fun components : ExtractedWitnessComponentFamily.{u} =>
            Exists fun rows :
                UniformFrameCyclicOrderRows.{u} noCut components =>
              Nonempty
                  (ConcreteNoEarlyRouteData
                    (geometrySourceFamilyOfFrameCyclicOrderRows rows)) /\
                Nonempty
                  (ExactFigureData
                    (geometrySourceFamilyOfFrameCyclicOrderRows rows))) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad (componentFrameNoEarlyFigureSourceData_nonempty_iff.2 h)
  case mpr =>
    intro hbad h
    exact hbad (componentFrameNoEarlyFigureSourceData_nonempty_iff.1 h)

theorem pointwiseSourceData_nonempty_of_canonicalBlockerEliminationSource
    (H : CanonicalBlockerEliminationSource)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        components)
    (hRoute :
      Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty PointwiseSourceData.{u} :=
  pointwiseSourceData_nonempty_of_componentSource
    (componentFrameNoEarlyFigureSourceData_nonempty_of_canonicalBlockerEliminationSource
      H components rows hRoute hFigure)

theorem pointwiseProductBlocker_nonempty_of_canonicalBlockerEliminationSource
    (H : CanonicalBlockerEliminationSource)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        components)
    (hRoute :
      Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty PointwiseProductBlocker.{u} :=
  pointwiseProductBlocker_nonempty_of_componentSource
    (componentFrameNoEarlyFigureSourceData_nonempty_of_canonicalBlockerEliminationSource
      H components rows hRoute hFigure)

theorem w26Product_nonempty_of_canonicalBlockerEliminationSource
    (H : CanonicalBlockerEliminationSource)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        components)
    (hRoute :
      Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty W26Product.{u} :=
  w26Product_nonempty_of_componentSource
    (componentFrameNoEarlyFigureSourceData_nonempty_of_canonicalBlockerEliminationSource
      H components rows hRoute hFigure)

theorem pointwiseProductDataClosure_sourceData_nonempty_of_canonicalBlockerEliminationSource
    (H : CanonicalBlockerEliminationSource)
    (components : ExtractedWitnessComponentFamily.{u})
    (rows :
      UniformFrameCyclicOrderRows.{u}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        components)
    (hRoute :
      Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    Nonempty PointwiseProductDataClosureW30.SourceData.{u} :=
  pointwiseProductDataClosure_sourceData_nonempty_of_componentSource
    (componentFrameNoEarlyFigureSourceData_nonempty_of_canonicalBlockerEliminationSource
      H components rows hRoute hFigure)

theorem laneProductSourceAlternatives_of_componentSource
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{0}) :
    LaneProductSourceAlternatives :=
  LaneProductFinalClosureW30.laneProductSourceAlternatives_of_pointwiseProductSourceData
    (pointwiseProductDataClosure_sourceData_nonempty_of_componentSource h)

theorem w29FinalSourceGate_of_componentSource
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{0}) :
    W29FinalSourceGate :=
  LaneProductFinalClosureW30.finalSourceGate_of_pointwiseProductSourceData
    (pointwiseProductDataClosure_sourceData_nonempty_of_componentSource h)

theorem laneProductSourceAlternatives_of_canonicalBlockerEliminationSource
    (H : CanonicalBlockerEliminationSource)
    (components : ExtractedWitnessComponentFamily.{0})
    (rows :
      UniformFrameCyclicOrderRows.{0}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        components)
    (hRoute :
      Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    LaneProductSourceAlternatives :=
  laneProductSourceAlternatives_of_componentSource
    (componentFrameNoEarlyFigureSourceData_nonempty_of_canonicalBlockerEliminationSource
      H components rows hRoute hFigure)

theorem w29FinalSourceGate_of_canonicalBlockerEliminationSource
    (H : CanonicalBlockerEliminationSource)
    (components : ExtractedWitnessComponentFamily.{0})
    (rows :
      UniformFrameCyclicOrderRows.{0}
        (noCutDependencyOfCanonicalBlockerEliminationSource H)
        components)
    (hRoute :
      Nonempty
        (ConcreteNoEarlyRouteData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows)))
    (hFigure :
      Nonempty
        (ExactFigureData
          (geometrySourceFamilyOfFrameCyclicOrderRows rows))) :
    W29FinalSourceGate :=
  w29FinalSourceGate_of_componentSource
    (componentFrameNoEarlyFigureSourceData_nonempty_of_canonicalBlockerEliminationSource
      H components rows hRoute hFigure)

/-! ## Actual topology component source package -/

structure ActualTopologyComponentFrameNoEarlyFigureSourceData :
    Type (u + 1) where
  noCut : NoCutDependency
  componentClosure : ActualTopologyExtractedComponentClosurePackage.{u}
  frameCyclicRows :
    UniformFrameCyclicOrderRows.{u} noCut
      (extractedWitnessComponentFamilyOfActualTopologyClosurePackage
        componentClosure)
  routeData :
    ConcreteNoEarlyRouteData
      (geometrySourceFamilyOfFrameCyclicOrderRows frameCyclicRows)
  figureData :
    ExactFigureData
      (geometrySourceFamilyOfFrameCyclicOrderRows frameCyclicRows)

namespace ActualTopologyComponentFrameNoEarlyFigureSourceData

def components
    (S : ActualTopologyComponentFrameNoEarlyFigureSourceData.{u}) :
    ExtractedWitnessComponentFamily.{u} :=
  extractedWitnessComponentFamilyOfActualTopologyClosurePackage
    S.componentClosure

def toComponentFrameNoEarlyFigureSourceData
    (S : ActualTopologyComponentFrameNoEarlyFigureSourceData.{u}) :
    ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceDataOfActualTopologyClosurePackage
    S.noCut S.componentClosure S.frameCyclicRows S.routeData S.figureData

def toPointwiseUniformRouteFigureSourceData
    (S : ActualTopologyComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseUniformRouteFigureSourceData.{u} :=
  pointwiseUniformRouteFigureSourceDataOfComponentSource
    S.toComponentFrameNoEarlyFigureSourceData

def toPointwiseSourceData
    (S : ActualTopologyComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseSourceData.{u} :=
  S.toComponentFrameNoEarlyFigureSourceData.toSourceData

theorem componentSource_nonempty
    (S : ActualTopologyComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} :=
  Nonempty.intro S.toComponentFrameNoEarlyFigureSourceData

theorem pointwiseSourceData_nonempty
    (S : ActualTopologyComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseSourceData.{u} :=
  Nonempty.intro S.toPointwiseSourceData

theorem pointwiseProductDataClosure_sourceData_nonempty
    (S : ActualTopologyComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseProductDataClosureW30.SourceData.{u} :=
  Nonempty.intro S.toPointwiseUniformRouteFigureSourceData.toSourceData

theorem laneProductSourceAlternatives
    (S : ActualTopologyComponentFrameNoEarlyFigureSourceData.{0}) :
    LaneProductSourceAlternatives :=
  LaneProductFinalClosureW30.laneProductSourceAlternatives_of_pointwiseProductSourceData
    S.pointwiseProductDataClosure_sourceData_nonempty

theorem w29FinalSourceGate
    (S : ActualTopologyComponentFrameNoEarlyFigureSourceData.{0}) :
    W29FinalSourceGate :=
  LaneProductFinalClosureW30.finalSourceGate_of_pointwiseProductSourceData
    S.pointwiseProductDataClosure_sourceData_nonempty

end ActualTopologyComponentFrameNoEarlyFigureSourceData

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_actualTopologySourceData
    (h :
      Nonempty
        ActualTopologyComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} := by
  cases h with
  | intro S =>
      exact S.componentSource_nonempty

/-! ## Exact canonical source package blocker -/

structure CanonicalNoCutComponentFrameNoEarlyFigureSourceData :
    Type (u + 1) where
  blockerElimination : CanonicalBlockerEliminationSource
  components : ExtractedWitnessComponentFamily.{u}
  frameCyclicRows :
    UniformFrameCyclicOrderRows.{u}
      (noCutDependencyOfCanonicalBlockerEliminationSource blockerElimination)
      components
  routeData :
    ConcreteNoEarlyRouteData
      (geometrySourceFamilyOfFrameCyclicOrderRows frameCyclicRows)
  figureData :
    ExactFigureData
      (geometrySourceFamilyOfFrameCyclicOrderRows frameCyclicRows)

namespace CanonicalNoCutComponentFrameNoEarlyFigureSourceData

def noCut
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    NoCutDependency :=
  noCutDependencyOfCanonicalBlockerEliminationSource S.blockerElimination

def toComponentFrameNoEarlyFigureSourceData
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    ComponentFrameNoEarlyFigureSourceData.{u} :=
  componentFrameNoEarlyFigureSourceDataOfCanonicalBlockerEliminationSource
    S.blockerElimination S.components S.frameCyclicRows S.routeData
    S.figureData

def toPointwiseUniformRouteFigureSourceData
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseUniformRouteFigureSourceData.{u} :=
  pointwiseUniformRouteFigureSourceDataOfComponentSource
    S.toComponentFrameNoEarlyFigureSourceData

def toPointwiseSourceData
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseSourceData.{u} :=
  S.toComponentFrameNoEarlyFigureSourceData.toSourceData

def toPointwiseProductBlocker
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseProductBlocker.{u} :=
  S.toComponentFrameNoEarlyFigureSourceData.toPointwiseProductBlocker

def toW26Product
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    W26Product.{u} :=
  S.toComponentFrameNoEarlyFigureSourceData.toW26Product

theorem componentSource_nonempty
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} :=
  Nonempty.intro S.toComponentFrameNoEarlyFigureSourceData

theorem pointwiseSourceData_nonempty
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseSourceData.{u} :=
  Nonempty.intro S.toPointwiseSourceData

theorem pointwiseProductBlocker_nonempty
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseProductBlocker.{u} :=
  Nonempty.intro S.toPointwiseProductBlocker

theorem w26Product_nonempty
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty W26Product.{u} :=
  Nonempty.intro S.toW26Product

theorem pointwiseProductDataClosure_sourceData_nonempty
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseProductDataClosureW30.SourceData.{u} :=
  Nonempty.intro S.toPointwiseUniformRouteFigureSourceData.toSourceData

theorem laneProductSourceAlternatives
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{0}) :
    LaneProductSourceAlternatives :=
  LaneProductFinalClosureW30.laneProductSourceAlternatives_of_pointwiseProductSourceData
    S.pointwiseProductDataClosure_sourceData_nonempty

theorem w29FinalSourceGate
    (S : CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{0}) :
    W29FinalSourceGate :=
  LaneProductFinalClosureW30.finalSourceGate_of_pointwiseProductSourceData
    S.pointwiseProductDataClosure_sourceData_nonempty

end CanonicalNoCutComponentFrameNoEarlyFigureSourceData

theorem canonicalNoCutComponentFrameNoEarlyFigureSourceData_nonempty_iff :
    Nonempty
        CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u} <->
      Exists fun blockerElimination : CanonicalBlockerEliminationSource =>
        Exists fun components : ExtractedWitnessComponentFamily.{u} =>
          Exists fun rows :
              UniformFrameCyclicOrderRows.{u}
                (noCutDependencyOfCanonicalBlockerEliminationSource
                  blockerElimination)
                components =>
            Nonempty
                (ConcreteNoEarlyRouteData
                  (geometrySourceFamilyOfFrameCyclicOrderRows rows)) /\
              Nonempty
                (ExactFigureData
                  (geometrySourceFamilyOfFrameCyclicOrderRows rows)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.blockerElimination
            (Exists.intro S.components
              (Exists.intro S.frameCyclicRows
                (And.intro
                  (Nonempty.intro S.routeData)
                  (Nonempty.intro S.figureData))))
  case mpr =>
    intro h
    cases h with
    | intro blockerElimination hComponents =>
        cases hComponents with
        | intro components hRows =>
            cases hRows with
            | intro rows hData =>
                cases hData.1 with
                | intro routeData =>
                    cases hData.2 with
                    | intro figureData =>
                        exact
                          Nonempty.intro
                            { blockerElimination := blockerElimination
                              components := components
                              frameCyclicRows := rows
                              routeData := routeData
                              figureData := figureData }

theorem componentSource_nonempty_of_canonicalSourceData
    (h :
      Nonempty
        CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} := by
  cases h with
  | intro S =>
      exact S.componentSource_nonempty

theorem pointwiseSourceData_nonempty_of_canonicalSourceData
    (h :
      Nonempty
        CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseSourceData.{u} := by
  cases h with
  | intro S =>
      exact S.pointwiseSourceData_nonempty

theorem pointwiseProductBlocker_nonempty_of_canonicalSourceData
    (h :
      Nonempty
        CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseProductBlocker.{u} := by
  cases h with
  | intro S =>
      exact S.pointwiseProductBlocker_nonempty

theorem w26Product_nonempty_of_canonicalSourceData
    (h :
      Nonempty
        CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty W26Product.{u} := by
  cases h with
  | intro S =>
      exact S.w26Product_nonempty

theorem pointwiseProductDataClosure_sourceData_nonempty_of_canonicalSourceData
    (h :
      Nonempty
        CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseProductDataClosureW30.SourceData.{u} := by
  cases h with
  | intro S =>
      exact S.pointwiseProductDataClosure_sourceData_nonempty

theorem laneProductSourceAlternatives_of_canonicalSourceData
    (h :
      Nonempty
        CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{0}) :
    LaneProductSourceAlternatives := by
  cases h with
  | intro S =>
      exact S.laneProductSourceAlternatives

theorem w29FinalSourceGate_of_canonicalSourceData
    (h :
      Nonempty
        CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{0}) :
    W29FinalSourceGate := by
  cases h with
  | intro S =>
      exact S.w29FinalSourceGate

end

end NoCutPointwiseBridgeW32
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW32NoCutDependency : Prop :=
  Swanepoel.NoCutPointwiseBridgeW32.NoCutDependency

abbrev SwanepoelW32NoCutVertexFamily : Prop :=
  Swanepoel.NoCutPointwiseBridgeW32.NoCutVertexFamily

abbrev SwanepoelW32MinimalFailureNoCutVertexFamily : Prop :=
  Swanepoel.NoCutPointwiseBridgeW32.MinimalFailureNoCutVertexFamily

abbrev SwanepoelW32CanonicalBlockerEliminationSource : Prop :=
  Swanepoel.NoCutPointwiseBridgeW32.CanonicalBlockerEliminationSource

abbrev SwanepoelW32MinimalCutVertexBlockerExists : Prop :=
  Swanepoel.NoCutPointwiseBridgeW32.MinimalCutVertexBlockerExists

abbrev SwanepoelW32MinimalClearedFailureEliminator : Prop :=
  Swanepoel.NoCutPointwiseBridgeW32.MinimalClearedFailureEliminator

abbrev SwanepoelW32MinimalFailureExclusion : Prop :=
  Swanepoel.NoCutPointwiseBridgeW32.MinimalFailureExclusion

abbrev SwanepoelW32SmallestExactLocalDeletionDependency : Prop :=
  Swanepoel.NoCutPointwiseBridgeW32.SmallestExactLocalDeletionDependency

abbrev SwanepoelW32CanonicalNoCutComponentSourceData : Type (u + 1) :=
  Swanepoel.NoCutPointwiseBridgeW32.CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}

abbrev SwanepoelW32ActualTopologyComponentSourceData : Type (u + 1) :=
  Swanepoel.NoCutPointwiseBridgeW32.ActualTopologyComponentFrameNoEarlyFigureSourceData.{u}

abbrev SwanepoelW32NoCutComponentFrameNoEarlyFigureSourceData :
    Type (u + 1) :=
  Swanepoel.NoCutPointwiseBridgeW32.ComponentFrameNoEarlyFigureSourceData.{u}

abbrev SwanepoelW32PointwiseSourceData : Type (u + 1) :=
  Swanepoel.NoCutPointwiseBridgeW32.PointwiseSourceData.{u}

theorem swanepoelW32_canonicalBlockerEliminationSource_exactly_noCutDependency :
    SwanepoelW32CanonicalBlockerEliminationSource <->
      SwanepoelW32NoCutDependency :=
  Swanepoel.NoCutPointwiseBridgeW32.canonicalBlockerEliminationSource_iff_noCutDependency

theorem swanepoelW32_noCutDependency_iff_minimalFailureNoCutVertexFamily :
    SwanepoelW32NoCutDependency <->
      SwanepoelW32MinimalFailureNoCutVertexFamily :=
  Swanepoel.NoCutPointwiseBridgeW32.noCutDependency_iff_minimalFailureNoCutVertexFamily

theorem swanepoelW32_noCutDependency_of_minimalFailureNoCutVertexFamily
    (H : SwanepoelW32MinimalFailureNoCutVertexFamily) :
    SwanepoelW32NoCutDependency :=
  Swanepoel.NoCutPointwiseBridgeW32.noCutDependencyOfMinimalFailureNoCutVertexFamily
    H

theorem swanepoelW32_noCutVertexFamily_of_no_minimalClearedFailure
    (H : SwanepoelW32MinimalFailureExclusion) :
    SwanepoelW32NoCutVertexFamily :=
  Swanepoel.NoCutPointwiseBridgeW32.noCutVertexFamily_of_no_minimalClearedFailure
    H

theorem swanepoelW32_not_minimalCutVertexBlockerExists_of_no_minimalClearedFailure
    (H : SwanepoelW32MinimalFailureExclusion) :
    Not SwanepoelW32MinimalCutVertexBlockerExists :=
  Swanepoel.NoCutPointwiseBridgeW32.not_minimalCutVertexBlockerExists_of_no_minimalClearedFailure
    H

theorem swanepoelW32_noCutDependency_of_no_minimalClearedFailure
    (H : SwanepoelW32MinimalFailureExclusion) :
    SwanepoelW32NoCutDependency :=
  Swanepoel.NoCutPointwiseBridgeW32.noCutDependencyOfNoMinimalClearedFailure
    H

theorem swanepoelW32_minimalFailureNoCutVertexFamily_of_no_minimalClearedFailure
    (H : SwanepoelW32MinimalFailureExclusion) :
    SwanepoelW32MinimalFailureNoCutVertexFamily :=
  Swanepoel.NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_no_minimalClearedFailure
    H

theorem swanepoelW32_noCutDependency_of_minimalClearedFailureEliminator
    (H : SwanepoelW32MinimalClearedFailureEliminator) :
    SwanepoelW32NoCutDependency :=
  Swanepoel.NoCutPointwiseBridgeW32.noCutDependencyOfMinimalClearedFailureEliminator
    H

theorem swanepoelW32_noCutVertexFamily_of_minimalClearedFailureEliminator
    (H : SwanepoelW32MinimalClearedFailureEliminator) :
    SwanepoelW32NoCutVertexFamily :=
  Swanepoel.NoCutPointwiseBridgeW32.noCutVertexFamilyOfMinimalClearedFailureEliminator
    H

theorem swanepoelW32_canonicalBlockerEliminationSource_of_minimalClearedFailureEliminator
    (H : SwanepoelW32MinimalClearedFailureEliminator) :
    SwanepoelW32CanonicalBlockerEliminationSource :=
  Swanepoel.NoCutPointwiseBridgeW32.canonicalBlockerEliminationSourceOfMinimalClearedFailureEliminator
    H

theorem swanepoelW32_noCutDependency_of_smallestExactLocalDeletionDependency
    (H : SwanepoelW32SmallestExactLocalDeletionDependency) :
    SwanepoelW32NoCutDependency :=
  Swanepoel.NoCutPointwiseBridgeW32.noCutDependencyOfSmallestExactLocalDeletionDependency
    H

theorem swanepoelW32_noCutVertexFamily_of_smallestExactLocalDeletionDependency
    (H : SwanepoelW32SmallestExactLocalDeletionDependency) :
    SwanepoelW32NoCutVertexFamily :=
  Swanepoel.NoCutPointwiseBridgeW32.noCutVertexFamilyOfSmallestExactLocalDeletionDependency
    H

theorem swanepoelW32_canonicalBlockerEliminationSource_of_smallestExactLocalDeletionDependency
    (H : SwanepoelW32SmallestExactLocalDeletionDependency) :
    SwanepoelW32CanonicalBlockerEliminationSource :=
  Swanepoel.NoCutPointwiseBridgeW32.canonicalBlockerEliminationSourceOfSmallestExactLocalDeletionDependency
    H

theorem swanepoelW32_pointwiseSourceData_of_canonicalNoCutComponents
    (h : Nonempty SwanepoelW32CanonicalNoCutComponentSourceData.{u}) :
    Nonempty SwanepoelW32PointwiseSourceData.{u} :=
  Swanepoel.NoCutPointwiseBridgeW32.pointwiseSourceData_nonempty_of_canonicalSourceData
    h

theorem swanepoelW32_componentSourceData_of_actualTopologyComponentSource
    (h : Nonempty SwanepoelW32ActualTopologyComponentSourceData.{u}) :
    Nonempty SwanepoelW32NoCutComponentFrameNoEarlyFigureSourceData.{u} :=
  open Swanepoel.NoCutPointwiseBridgeW32 in
    componentFrameNoEarlyFigureSourceData_nonempty_of_actualTopologySourceData h

theorem swanepoelW32_pointwiseSourceData_of_actualTopologyComponentSource
    (h : Nonempty SwanepoelW32ActualTopologyComponentSourceData.{u}) :
    Nonempty SwanepoelW32PointwiseSourceData.{u} :=
  Swanepoel.NoCutPointwiseBridgeW32.pointwiseSourceData_nonempty_of_componentSource
    (swanepoelW32_componentSourceData_of_actualTopologyComponentSource h)

theorem swanepoelW32_laneProductSourceAlternatives_of_canonicalNoCutComponents
    (h : Nonempty SwanepoelW32CanonicalNoCutComponentSourceData.{0}) :
    Swanepoel.NoCutPointwiseBridgeW32.LaneProductSourceAlternatives :=
  Swanepoel.NoCutPointwiseBridgeW32.laneProductSourceAlternatives_of_canonicalSourceData
    h

end Verified
end ErdosProblems1066
