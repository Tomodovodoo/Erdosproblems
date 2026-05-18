import ErdosProblems1066.Swanepoel.PointwiseProductDataClosureW30
import ErdosProblems1066.Swanepoel.LaneProductFinalClosureW30
import ErdosProblems1066.Swanepoel.FrameCyclicOrderRowsW30
import ErdosProblems1066.Swanepoel.NoEarlyRouteDataClosureW30
import ErdosProblems1066.Swanepoel.ExactFigureInequalitiesW30
import ErdosProblems1066.Swanepoel.ExtractedWitnessComponentsW30
import ErdosProblems1066.Swanepoel.NoCutBlockerEliminationW30

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W31 pointwise/lane-product source inhabitation

This file is a source-only assembly layer.  It packages the exact W30
component surfaces -- extracted topology components, no-cut, frame/cyclic
rows, no-early route data, and exact Figure data -- and forgets them through
the W30 pointwise-product and lane-product closures.

No root imports, known bounds, lower-bound endpoint, or final theorem is
introduced here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseLaneProductInhabitationW31

universe u

noncomputable section

abbrev SourceData : Type (u + 1) :=
  PointwiseProductDataClosureW30.SourceData.{u}

abbrev PointwiseProductBlocker : Type (u + 1) :=
  PointwiseProductDataClosureW30.W28PointwiseProductBlocker.{u}

abbrev W26Product : Type (u + 1) :=
  PointwiseProductDataClosureW30.W28W26Product.{u}

abbrev NoCutDependency : Prop :=
  PointwiseProductDataClosureW30.NoCutDependency

abbrev BoundaryFamily : Type (u + 1) :=
  PointwiseProductDataClosureW30.BoundaryFamily.{u}

abbrev ExtractedWitnessComponentFamily : Type (u + 1) :=
  ExtractedWitnessComponentsW30.ExtractedWitnessComponentFamily.{u}

abbrev ExtractedWitnessFamily : Type (u + 1) :=
  ExtractedWitnessComponentsW30.ExtractedWitnessFamily.{u}

abbrev BoundaryWitnessSourceFamily : Type (u + 1) :=
  ExtractedWitnessComponentsW30.BoundaryWitnessSourceFamily.{u}

def extractedWitnessFamilyOfComponentFamily
    (components : ExtractedWitnessComponentFamily.{u}) :
    ExtractedWitnessFamily.{u} :=
  components.toExtractedWitnessFamily

def boundaryWitnessSourceFamilyOfComponentFamily
    (components : ExtractedWitnessComponentFamily.{u}) :
    BoundaryWitnessSourceFamily.{u} :=
  components.toBoundaryWitnessSourceFamily

def selectedFaceWitnessFamilyOfComponentFamily
    (components : ExtractedWitnessComponentFamily.{u}) :
    SelectedFaceWitnessConstructionW28.SelectedFaceWitnessFamily.{u} :=
  SelectedFaceWitnessConstructionW28.selectedFaceWitnessFamilyOfExtracted
    (extractedWitnessFamilyOfComponentFamily components)

def boundaryFamilyOfComponentFamily
    (components : ExtractedWitnessComponentFamily.{u}) :
    BoundaryFamily.{u} :=
  PointwiseProductSourceW28.boundaryFamilyOfSelectedFaceWitnessFamily
    (selectedFaceWitnessFamilyOfComponentFamily components)

abbrev PayForCutOfNoCut
    (noCut : NoCutDependency) :
    PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily :=
  PointwiseProductDataClosureW30.PayForCutOfNoCut noCut

abbrev TopologyArcOfComponents
    (components : ExtractedWitnessComponentFamily.{u}) :
    PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u} :=
  PointwiseProductDataClosureW30.TopologyArcOfBoundary
    (boundaryFamilyOfComponentFamily components)

abbrev UniformFrameCyclicOrderRows
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u}) :
    Type (u + 1) :=
  FrameCyclicOrderRowsW30.UniformFrameCyclicOrderRows.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfComponents components)

abbrev UniformFiniteGeometryRows
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u}) :
    Type (u + 1) :=
  PointwiseProductDataClosureW30.UniformFiniteGeometryRows.{u}
    noCut (boundaryFamilyOfComponentFamily components)

def uniformRowsOfFrameCyclicOrderRows
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    UniformFiniteGeometryRows.{u} noCut components :=
  FrameCyclicOrderRowsW30.uniformRowsOfUniformFrameCyclicOrderRows
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    rows

abbrev GeometrySourceFamily
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u}) :
    Type (u + 1) :=
  PointwiseProductDataClosureW30.GeometrySourceFamily.{u}
    noCut (boundaryFamilyOfComponentFamily components)

def geometrySourceFamilyOfFrameCyclicOrderRows
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (rows : UniformFrameCyclicOrderRows.{u} noCut components) :
    GeometrySourceFamily.{u} noCut components :=
  PointwiseProductDataClosureW30.geometrySourceFamilyOfUniformRows
    (uniformRowsOfFrameCyclicOrderRows rows)

abbrev Lemma8ConcreteOfGeometrySource
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
      (PayForCutOfNoCut noCut) (TopologyArcOfComponents components) :=
  PointwiseProductDataClosureW30.Lemma8ConcreteOfGeometrySource geometry

abbrev ConcreteNoEarlyRouteData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  PointwiseProductDataClosureW30.ConcreteNoEarlyRouteData geometry

abbrev NoEarlyCoverageData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8Lemma9NoEarlyCoverageFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfComponents components)
    (Lemma8ConcreteOfGeometrySource geometry)

abbrev K23ObstructionData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8K23ObstructionRowFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfComponents components)
    (Lemma8ConcreteOfGeometrySource geometry)

abbrev ThreeCommonNeighborObstructionData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8ThreeCommonNeighborObstructionRowFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfComponents components)
    (Lemma8ConcreteOfGeometrySource geometry)

abbrev CommonNeighborObstructionData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8CommonNeighborCardObstructionRowFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfComponents components)
    (Lemma8ConcreteOfGeometrySource geometry)

abbrev LocalExclusionObstructionData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8LocalExclusionObstructionPackageFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfComponents components)
    (Lemma8ConcreteOfGeometrySource geometry)

def routeDataOfCoverageAndK23Obstruction
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut components}
    (coverage : NoEarlyCoverageData geometry)
    (obstruction : K23ObstructionData geometry) :
    ConcreteNoEarlyRouteData geometry :=
  NoEarlyRouteDataClosureW30.routeDataOfCoverageAndK23Obstruction
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 := Lemma8ConcreteOfGeometrySource geometry)
    coverage obstruction

def routeDataOfCoverageAndThreeCommonNeighborObstruction
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut components}
    (coverage : NoEarlyCoverageData geometry)
    (obstruction : ThreeCommonNeighborObstructionData geometry) :
    ConcreteNoEarlyRouteData geometry :=
  NoEarlyRouteDataClosureW30.routeDataOfCoverageAndThreeCommonNeighborObstruction
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 := Lemma8ConcreteOfGeometrySource geometry)
    coverage obstruction

def routeDataOfCoverageAndCommonNeighborObstruction
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut components}
    (coverage : NoEarlyCoverageData geometry)
    (obstruction : CommonNeighborObstructionData geometry) :
    ConcreteNoEarlyRouteData geometry :=
  NoEarlyRouteDataClosureW30.routeDataOfCoverageAndCommonNeighborObstruction
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 := Lemma8ConcreteOfGeometrySource geometry)
    coverage obstruction

def routeDataOfCoverageAndLocalExclusionObstruction
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut components}
    (coverage : NoEarlyCoverageData geometry)
    (obstruction : LocalExclusionObstructionData geometry) :
    ConcreteNoEarlyRouteData geometry :=
  NoEarlyRouteDataClosureW30.routeDataOfCoverageAndLocalExclusionObstruction
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 := Lemma8ConcreteOfGeometrySource geometry)
    coverage obstruction

abbrev ExactFigureData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  ExactFigureInequalitiesW30.ExactE22E23FigureData.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfComponents components)
    (Lemma8ConcreteOfGeometrySource geometry)

abbrev FigureAngleDataSourceFamily
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Type (u + 1) :=
  PointwiseProductDataClosureW30.FigureAngleDataSourceFamily geometry

def figureAngleDataSourceFamilyOfExactFigureData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut components}
    (figures : ExactFigureData geometry) :
    FigureAngleDataSourceFamily geometry :=
  figures.toLocalExactFigureAngleDataSourceFamily

/-- All W31 source components needed to build the pointwise product. -/
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
    BoundaryFamily.{u} :=
  boundaryFamilyOfComponentFamily S.components

def topologySource
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    BoundaryWitnessSourceFamily.{u} :=
  boundaryWitnessSourceFamilyOfComponentFamily S.components

def extractedTopology
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    ExtractedWitnessFamily.{u} :=
  extractedWitnessFamilyOfComponentFamily S.components

def uniformRows
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    UniformFiniteGeometryRows.{u} S.noCut S.components :=
  uniformRowsOfFrameCyclicOrderRows S.frameCyclicRows

def geometry
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    GeometrySourceFamily.{u} S.noCut S.components :=
  geometrySourceFamilyOfFrameCyclicOrderRows S.frameCyclicRows

def figureAngleData
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    FigureAngleDataSourceFamily S.geometry :=
  figureAngleDataSourceFamilyOfExactFigureData S.figureData

def toSourceData
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    SourceData.{u} :=
  PointwiseProductDataClosureW30.sourceDataOfUniformRowsRouteFigureData
    S.noCut S.boundary S.uniformRows S.routeData S.figureAngleData

def toPointwiseProductBlocker
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseProductBlocker.{u} :=
  S.toSourceData.toPointwiseProductBlocker

def toW26Product
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    W26Product.{u} :=
  S.toSourceData.toW26Product

theorem sourceData_nonempty
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty SourceData.{u} :=
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

def sourceDataOfComponentFrameNoEarlyFigureSourceData
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    SourceData.{u} :=
  S.toSourceData

theorem sourceData_nonempty_of_componentFrameNoEarlyFigureSourceData
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty SourceData.{u} := by
  cases h with
  | intro S =>
      exact S.sourceData_nonempty

theorem pointwiseProductBlocker_nonempty_of_componentFrameNoEarlyFigureSourceData
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty PointwiseProductBlocker.{u} := by
  cases h with
  | intro S =>
      exact S.pointwiseProductBlocker_nonempty

theorem w26Product_nonempty_of_componentFrameNoEarlyFigureSourceData
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty W26Product.{u} := by
  cases h with
  | intro S =>
      exact S.w26Product_nonempty

/-- Exact W31 component blocker: all component families must be present. -/
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

/-! ## Lane-product source alternatives in the W29/W30 final-source surface -/

abbrev LaneProductSourceAlternatives : Prop :=
  LaneProductFinalClosureW30.LaneProductSourceAlternatives

abbrev W29FinalSourceGate : Prop :=
  LaneProductFinalClosureW30.W29FinalSourceGate

def laneProductSourceAlternativesOfComponentFrameNoEarlyFigureSourceData
    (S : ComponentFrameNoEarlyFigureSourceData.{0}) :
    LaneProductSourceAlternatives :=
  LaneProductFinalClosureW30.laneProductSourceAlternatives_of_pointwiseProductSourceData
    (Nonempty.intro S.toSourceData)

def finalSourceGateOfComponentFrameNoEarlyFigureSourceData
    (S : ComponentFrameNoEarlyFigureSourceData.{0}) :
    W29FinalSourceGate :=
  LaneProductFinalClosureW30.finalSourceGate_of_pointwiseProductSourceData
    (Nonempty.intro S.toSourceData)

theorem laneProductSourceAlternatives_of_componentFrameNoEarlyFigureSourceData
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{0}) :
    LaneProductSourceAlternatives := by
  cases h with
  | intro S =>
      exact laneProductSourceAlternativesOfComponentFrameNoEarlyFigureSourceData S

theorem finalSourceGate_of_componentFrameNoEarlyFigureSourceData
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData.{0}) :
    W29FinalSourceGate := by
  cases h with
  | intro S =>
      exact finalSourceGateOfComponentFrameNoEarlyFigureSourceData S

/-! ## Exact component blockers inherited from W30 surfaces -/

theorem noCutDependency_iff_not_minimalCutVertexBlocker :
    NoCutDependency <->
      Not
        (Nonempty
          NoCutLocalDeletionConcreteW27.MinimalCutVertexBlocker) :=
  PointwiseProductSourceW28.noCutDependency_iff_not_minimalCutVertexBlocker

theorem extractedWitnessFamily_nonempty_iff_componentFamily :
    Nonempty ExtractedWitnessFamily.{u} <->
      Nonempty ExtractedWitnessComponentFamily.{u} :=
  ExtractedWitnessComponentsW30.extractedWitnessFamily_nonempty_iff_componentFamily

theorem boundaryWitnessSourceFamily_nonempty_iff_componentFamily :
    Nonempty BoundaryWitnessSourceFamily.{u} <->
      Nonempty ExtractedWitnessComponentFamily.{u} :=
  ExtractedWitnessComponentsW30.sourceFamily_nonempty_iff_componentFamily

theorem uniformFiniteGeometryRows_nonempty_iff_frameCyclicOrderRows
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily.{u}) :
    Nonempty (UniformFiniteGeometryRows.{u} noCut components) <->
      Nonempty
        (UniformFrameCyclicOrderRows.{u} noCut components) :=
  FrameCyclicOrderRowsW30.uniformFiniteGeometryRows_nonempty_iff_uniformFrameCyclicOrderRows
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)

theorem routeData_nonempty_iff_coverage_and_obstruction
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Nonempty (ConcreteNoEarlyRouteData geometry) <->
      Nonempty (NoEarlyCoverageData geometry) /\
        (Nonempty (K23ObstructionData geometry) \/
          Nonempty (ThreeCommonNeighborObstructionData geometry) \/
            Nonempty (CommonNeighborObstructionData geometry) \/
              Nonempty (LocalExclusionObstructionData geometry)) :=
  NoEarlyRouteDataClosureW30.nonempty_routeData_iff_coverage_and_obstruction
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 := Lemma8ConcreteOfGeometrySource geometry)

theorem exactFigureData_nonempty_iff_angleDataSourceFamily
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Nonempty (ExactFigureData geometry) <->
      Nonempty (FigureAngleDataSourceFamily geometry) :=
  ExactFigureInequalitiesW30.exactE22E23FigureDataBlocker_iff_localExactFigureAngleDataSourceFamily
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 := Lemma8ConcreteOfGeometrySource geometry)

theorem not_exactFigureData_iff_not_angleDataSourceFamily
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut components) :
    Not (Nonempty (ExactFigureData geometry)) <->
      Not (Nonempty (FigureAngleDataSourceFamily geometry)) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad ((exactFigureData_nonempty_iff_angleDataSourceFamily geometry).2 h)
  case mpr =>
    intro hbad h
    exact hbad ((exactFigureData_nonempty_iff_angleDataSourceFamily geometry).1 h)

end

end PointwiseLaneProductInhabitationW31
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW31ComponentFrameNoEarlyFigureSourceData :
    Type (u + 1) :=
  Swanepoel.PointwiseLaneProductInhabitationW31.ComponentFrameNoEarlyFigureSourceData.{u}

abbrev SwanepoelW31PointwiseProductSourceData : Type (u + 1) :=
  Swanepoel.PointwiseLaneProductInhabitationW31.SourceData.{u}

theorem swanepoelW31_pointwiseProductSourceData_of_componentSources
    (h :
      Nonempty
        SwanepoelW31ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty SwanepoelW31PointwiseProductSourceData.{u} :=
  Swanepoel.PointwiseLaneProductInhabitationW31.sourceData_nonempty_of_componentFrameNoEarlyFigureSourceData
    h

theorem swanepoelW31_pointwiseProductBlocker_of_componentSources
    (h :
      Nonempty
        SwanepoelW31ComponentFrameNoEarlyFigureSourceData.{u}) :
    Nonempty
      Swanepoel.PointwiseLaneProductInhabitationW31.PointwiseProductBlocker.{u} :=
  Swanepoel.PointwiseLaneProductInhabitationW31.pointwiseProductBlocker_nonempty_of_componentFrameNoEarlyFigureSourceData
    h

theorem swanepoelW31_laneProductSourceAlternatives_of_componentSources
    (h :
      Nonempty
        SwanepoelW31ComponentFrameNoEarlyFigureSourceData.{0}) :
    Swanepoel.PointwiseLaneProductInhabitationW31.LaneProductSourceAlternatives :=
  Swanepoel.PointwiseLaneProductInhabitationW31.laneProductSourceAlternatives_of_componentFrameNoEarlyFigureSourceData
    h

theorem swanepoelW31_componentSources_exactly_all_componentSources :
    Nonempty SwanepoelW31ComponentFrameNoEarlyFigureSourceData.{u} <->
      Exists fun noCut :
          Swanepoel.PointwiseLaneProductInhabitationW31.NoCutDependency =>
        Exists fun components :
            Swanepoel.PointwiseLaneProductInhabitationW31.ExtractedWitnessComponentFamily.{u} =>
          Exists fun rows :
              Swanepoel.PointwiseLaneProductInhabitationW31.UniformFrameCyclicOrderRows.{u}
                noCut components =>
            Nonempty
                (Swanepoel.PointwiseLaneProductInhabitationW31.ConcreteNoEarlyRouteData
                  (Swanepoel.PointwiseLaneProductInhabitationW31.geometrySourceFamilyOfFrameCyclicOrderRows
                    rows)) /\
              Nonempty
                (Swanepoel.PointwiseLaneProductInhabitationW31.ExactFigureData
                  (Swanepoel.PointwiseLaneProductInhabitationW31.geometrySourceFamilyOfFrameCyclicOrderRows
                    rows)) :=
  Swanepoel.PointwiseLaneProductInhabitationW31.componentFrameNoEarlyFigureSourceData_nonempty_iff

end Verified
end ErdosProblems1066
