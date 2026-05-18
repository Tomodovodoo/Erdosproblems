import ErdosProblems1066.Swanepoel.LaneProductSourceAlternativesW29
import ErdosProblems1066.Swanepoel.SwanepoelW29FinalAssembly
import ErdosProblems1066.Swanepoel.PointwiseProductBlockerSourceW29
import ErdosProblems1066.Swanepoel.ExtractedBoundaryWitnessSourceW29
import ErdosProblems1066.Swanepoel.ExactFigureAngleDataSourceW29

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W30 lane-product final-source closure

This file closes the honest source-data routes into the W29 lane-product
alternatives and the W29 final source gate.  The direction is always
source-to-gate: pointwise product data first gives a W28 pointwise product
blocker, the sharper W29 lane-product alternative then turns that blocker into
the older remaining lane-product blocker required by the W29 final assembly.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LaneProductFinalClosureW30

noncomputable section

abbrev LaneProductSourceAlternatives : Prop :=
  LaneProductSourceAlternativesW29.LaneProductSourceAlternatives

abbrev W29RemainingLaneProductSourceAlternatives : Prop :=
  SwanepoelW29FinalAssembly.LaneProductSourceAlternatives

abbrev W29FinalSourceGate : Prop :=
  SwanepoelW29FinalAssembly.FinalSourceGate

abbrev PointwiseProductBlocker : Type 1 :=
  LaneProductSourceAlternativesW29.PointwiseProductBlocker

abbrev PointwiseProductSourceData : Type 1 :=
  PointwiseProductBlockerSourceW29.PointwiseProductSourceData.{0}

abbrev NoCutDependency : Prop :=
  PointwiseProductBlockerSourceW29.NoCutDependency

abbrev BoundaryFamily : Type 1 :=
  PointwiseProductBlockerSourceW29.BoundaryFamily.{0}

abbrev GeometrySourceFamily
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily) : Type 1 :=
  PointwiseProductBlockerSourceW29.GeometrySourceFamily.{0} noCut boundary

abbrev Lemma8UniformFiniteRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily) : Type 1 :=
  PointwiseProductBlockerSourceW29.Lemma8UniformFiniteRows.{0}
    noCut boundary

abbrev FramePositiveRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily) : Type 1 :=
  PointwiseProductBlockerSourceW29.FramePositiveRows.{0}
    noCut boundary

abbrev Lemma9RouteData
    {noCut : NoCutDependency} {boundary : BoundaryFamily}
    (geometry : GeometrySourceFamily noCut boundary) : Type 1 :=
  PointwiseProductBlockerSourceW29.Lemma9RouteData.{0} geometry

abbrev FigureExactSourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily}
    (geometry : GeometrySourceFamily noCut boundary) : Type 1 :=
  PointwiseProductBlockerSourceW29.FigureExactSourceFamily.{0} geometry

abbrev ExtractedBoundaryWitnessSourceFamily : Type 1 :=
  ExtractedBoundaryWitnessSourceW29.ExtractedBoundaryWitnessSourceFamily.{0}

abbrev ExtractedWitnessFamily : Type 1 :=
  ExtractedBoundaryWitnessSourceW29.ExtractedWitnessFamily.{0}

abbrev PayForCutOfNoCut
    (noCut : NoCutDependency) :
    PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily :=
  PointwiseProductBlockerSourceW29.PayForCutOfNoCut noCut

abbrev TopologyArcOfBoundary
    (boundary : BoundaryFamily) :
    PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{0} :=
  PointwiseProductBlockerSourceW29.TopologyArcOfBoundary boundary

abbrev Lemma8ConcreteOfGeometrySource
    {noCut : NoCutDependency} {boundary : BoundaryFamily}
    (geometry : GeometrySourceFamily noCut boundary) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{0}
      (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary) :=
  PointwiseProductBlockerSourceW29.Lemma8ConcreteOfGeometrySource geometry

abbrev ExactFigureAngleDataSourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily}
    (geometry : GeometrySourceFamily noCut boundary) : Type 1 :=
  ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSourceFamily.{0}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfGeometrySource geometry)

/-! ## Pointwise product data into the lane-product and final W29 gates -/

def laneProductSourceAlternativesOfPointwiseProductBlocker
    (h : Nonempty PointwiseProductBlocker) :
    LaneProductSourceAlternatives :=
  Or.inr (Or.inr h)

def remainingLaneProductSourceAlternativesOfLaneProductSourceAlternatives
    (h : LaneProductSourceAlternatives) :
    W29RemainingLaneProductSourceAlternatives :=
  LaneProductSourceAlternativesW29.laneProductSourceAlternatives_to_remainingBlocker
    h

def finalSourceGateOfLaneProductSourceAlternatives
    (h : LaneProductSourceAlternatives) :
    W29FinalSourceGate :=
  Or.inr
    (Or.inl
      (remainingLaneProductSourceAlternativesOfLaneProductSourceAlternatives
        h))

theorem pointwiseProductBlocker_nonempty_of_sourceData
    (h : Nonempty PointwiseProductSourceData) :
    Nonempty PointwiseProductBlocker :=
  PointwiseProductBlockerSourceW29.pointwiseProductBlocker_nonempty_of_sourceData
    h

theorem laneProductSourceAlternatives_of_pointwiseProductSourceData
    (h : Nonempty PointwiseProductSourceData) :
    LaneProductSourceAlternatives :=
  laneProductSourceAlternativesOfPointwiseProductBlocker
    (pointwiseProductBlocker_nonempty_of_sourceData h)

theorem finalSourceGate_of_pointwiseProductSourceData
    (h : Nonempty PointwiseProductSourceData) :
    W29FinalSourceGate :=
  finalSourceGateOfLaneProductSourceAlternatives
    (laneProductSourceAlternatives_of_pointwiseProductSourceData h)

/-! ## Existing W29 extracted topology and Figure source composites -/

def laneProductSourceAlternativesOfExtractedTopologyGeometryRouteFigureSources
    (S :
      LaneProductSourceAlternativesW29.ExtractedTopologyGeometryRouteFigureSources) :
    LaneProductSourceAlternatives :=
  laneProductSourceAlternativesOfPointwiseProductBlocker
    (Nonempty.intro S.toPointwiseProductBlocker)

def finalSourceGateOfExtractedTopologyGeometryRouteFigureSources
    (S :
      LaneProductSourceAlternativesW29.ExtractedTopologyGeometryRouteFigureSources) :
    W29FinalSourceGate :=
  finalSourceGateOfLaneProductSourceAlternatives
    (laneProductSourceAlternativesOfExtractedTopologyGeometryRouteFigureSources
      S)

theorem finalSourceGate_of_extractedTopologyGeometryRouteFigureSources
    (h :
      Nonempty
        LaneProductSourceAlternativesW29.ExtractedTopologyGeometryRouteFigureSources) :
    W29FinalSourceGate := by
  cases h with
  | intro S =>
      exact finalSourceGateOfExtractedTopologyGeometryRouteFigureSources S

/-! ## W29 extracted boundary and exact Figure data as pointwise data -/

def extractedWitnessFamilyOfBoundarySource
    (F : ExtractedBoundaryWitnessSourceFamily) :
    ExtractedWitnessFamily :=
  F.toExtractedWitnessFamily

def boundaryFamilyOfExtractedBoundarySource
    (F : ExtractedBoundaryWitnessSourceFamily) :
    BoundaryFamily :=
  LaneProductSourceAlternativesW29.boundaryFamilyOfExtractedWitnessFamily
    (extractedWitnessFamilyOfBoundarySource F)

structure ExtractedTopologyFigurePointwiseSources : Type 1 where
  noCut : NoCutDependency
  topology : ExtractedBoundaryWitnessSourceFamily
  lemma8Geometry :
    GeometrySourceFamily noCut
      (boundaryFamilyOfExtractedBoundarySource topology)
  lemma9Route : Lemma9RouteData lemma8Geometry
  figures : ExactFigureAngleDataSourceFamily lemma8Geometry

namespace ExtractedTopologyFigurePointwiseSources

def extractedWitnessFamily
    (S : ExtractedTopologyFigurePointwiseSources) :
    ExtractedWitnessFamily :=
  extractedWitnessFamilyOfBoundarySource S.topology

def boundary
    (S : ExtractedTopologyFigurePointwiseSources) :
    BoundaryFamily :=
  boundaryFamilyOfExtractedBoundarySource S.topology

def figureExactSourceFamily
    (S : ExtractedTopologyFigurePointwiseSources) :
    FigureExactSourceFamily S.lemma8Geometry :=
  S.figures.toLocalExactFigureWitnessSourceFamily

def toPointwiseProductSourceData
    (S : ExtractedTopologyFigurePointwiseSources) :
    PointwiseProductSourceData where
  noCut := S.noCut
  boundary := S.boundary
  lemma8Geometry := S.lemma8Geometry
  lemma9Route := S.lemma9Route
  figures := S.figureExactSourceFamily

def toW29ExtractedTopologyGeometryRouteFigureSources
    (S : ExtractedTopologyFigurePointwiseSources) :
    LaneProductSourceAlternativesW29.ExtractedTopologyGeometryRouteFigureSources where
  noCut := S.noCut
  topology := S.extractedWitnessFamily
  lemma8Geometry := S.lemma8Geometry
  lemma9Route := S.lemma9Route
  figures := Nonempty.intro S.figureExactSourceFamily

def toPointwiseProductBlocker
    (S : ExtractedTopologyFigurePointwiseSources) :
    PointwiseProductBlocker :=
  S.toPointwiseProductSourceData.toPointwiseProductBlocker

def laneProductSourceAlternatives
    (S : ExtractedTopologyFigurePointwiseSources) :
    LaneProductSourceAlternatives :=
  laneProductSourceAlternativesOfPointwiseProductBlocker
    (Nonempty.intro S.toPointwiseProductBlocker)

def finalSourceGate
    (S : ExtractedTopologyFigurePointwiseSources) :
    W29FinalSourceGate :=
  finalSourceGateOfLaneProductSourceAlternatives
    S.laneProductSourceAlternatives

end ExtractedTopologyFigurePointwiseSources

theorem laneProductSourceAlternatives_of_extractedTopologyFigureSources
    (h : Nonempty ExtractedTopologyFigurePointwiseSources) :
    LaneProductSourceAlternatives := by
  cases h with
  | intro S =>
      exact S.laneProductSourceAlternatives

theorem finalSourceGate_of_extractedTopologyFigureSources
    (h : Nonempty ExtractedTopologyFigurePointwiseSources) :
    W29FinalSourceGate := by
  cases h with
  | intro S =>
      exact S.finalSourceGate

/-! ## Uniform finite geometry rows plus extracted topology/Figure data -/

structure ExtractedTopologyUniformRowsRouteFigureSources : Type 1 where
  noCut : NoCutDependency
  topology : ExtractedBoundaryWitnessSourceFamily
  lemma8Rows :
    Lemma8UniformFiniteRows noCut
      (boundaryFamilyOfExtractedBoundarySource topology)
  lemma9Route :
    Lemma9RouteData
      (PointwiseProductBlockerSourceW29.geometrySourceFamilyOfUniformFiniteRows
        lemma8Rows)
  figures :
    ExactFigureAngleDataSourceFamily
      (PointwiseProductBlockerSourceW29.geometrySourceFamilyOfUniformFiniteRows
        lemma8Rows)

namespace ExtractedTopologyUniformRowsRouteFigureSources

def boundary
    (S : ExtractedTopologyUniformRowsRouteFigureSources) :
    BoundaryFamily :=
  boundaryFamilyOfExtractedBoundarySource S.topology

def lemma8Geometry
    (S : ExtractedTopologyUniformRowsRouteFigureSources) :
    GeometrySourceFamily S.noCut S.boundary :=
  PointwiseProductBlockerSourceW29.geometrySourceFamilyOfUniformFiniteRows
    S.lemma8Rows

def figureExactSourceFamily
    (S : ExtractedTopologyUniformRowsRouteFigureSources) :
    FigureExactSourceFamily S.lemma8Geometry :=
  S.figures.toLocalExactFigureWitnessSourceFamily

def toPointwiseProductSourceData
    (S : ExtractedTopologyUniformRowsRouteFigureSources) :
    PointwiseProductSourceData :=
  PointwiseProductBlockerSourceW29.sourceDataOfUniformRowsRouteFigureSources
    S.noCut S.boundary S.lemma8Rows S.lemma9Route
    S.figureExactSourceFamily

def toExtractedTopologyFigurePointwiseSources
    (S : ExtractedTopologyUniformRowsRouteFigureSources) :
    ExtractedTopologyFigurePointwiseSources where
  noCut := S.noCut
  topology := S.topology
  lemma8Geometry := S.lemma8Geometry
  lemma9Route := S.lemma9Route
  figures := S.figures

def laneProductSourceAlternatives
    (S : ExtractedTopologyUniformRowsRouteFigureSources) :
    LaneProductSourceAlternatives :=
  laneProductSourceAlternatives_of_pointwiseProductSourceData
    (Nonempty.intro S.toPointwiseProductSourceData)

def finalSourceGate
    (S : ExtractedTopologyUniformRowsRouteFigureSources) :
    W29FinalSourceGate :=
  finalSourceGateOfLaneProductSourceAlternatives
    S.laneProductSourceAlternatives

end ExtractedTopologyUniformRowsRouteFigureSources

theorem laneProductSourceAlternatives_of_extractedTopologyUniformRowsRouteFigureSources
    (h : Nonempty ExtractedTopologyUniformRowsRouteFigureSources) :
    LaneProductSourceAlternatives := by
  cases h with
  | intro S =>
      exact S.laneProductSourceAlternatives

theorem finalSourceGate_of_extractedTopologyUniformRowsRouteFigureSources
    (h : Nonempty ExtractedTopologyUniformRowsRouteFigureSources) :
    W29FinalSourceGate := by
  cases h with
  | intro S =>
      exact S.finalSourceGate

end

end LaneProductFinalClosureW30
end Swanepoel
end ErdosProblems1066
