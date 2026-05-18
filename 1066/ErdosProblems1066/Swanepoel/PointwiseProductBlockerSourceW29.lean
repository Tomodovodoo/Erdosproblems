import ErdosProblems1066.Swanepoel.PointwiseProductSourceW28
import ErdosProblems1066.Swanepoel.Lemma8FiniteGeometryRowsW28
import ErdosProblems1066.Swanepoel.Lemma9NoEarlySourceRowsW28
import ErdosProblems1066.Swanepoel.FigureExactAngleSourceW28

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W29 pointwise product blocker source data

This file strengthens the W28 pointwise product blocker by exposing a source
package assembled from the currently available W28/W27 source data:

* Lemma 8 geometry source families, with a constructor from W28 uniform finite
  geometry rows;
* Lemma 9 route data, carrying one of the checked K23/common-neighbor/local
  exclusion no-early source routes;
* exact Figure 8/Figure 9 witness sources, carrying selected W12 witnesses and
  angle-window inequalities.

The only direction proved here is from these source packages to the W28
`PointwiseProductBlocker` and then to the W26 product.  No final lower-bound
target is used.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseProductBlockerSourceW29

universe u

noncomputable section

abbrev W28PointwiseProductBlocker : Type (u + 1) :=
  PointwiseProductSourceW28.PointwiseProductBlocker.{u}

abbrev W28W26Product : Type (u + 1) :=
  PointwiseProductSourceW28.W26Product.{u}

abbrev W28PointwiseSourceFamilyFields : Type (u + 1) :=
  PointwiseProductSourceW28.PointwiseSourceFamilyFields.{u}

abbrev NoCutDependency : Prop :=
  PointwiseProductSourceW28.NoCutDependency

abbrev BoundaryFamily : Type (u + 1) :=
  PointwiseProductSourceW28.BoundaryFamily.{u}

abbrev PayForCutOfNoCut
    (noCut : NoCutDependency) :
    PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily :=
  PointwiseProductSourceW28.PayForCutOfNoCut noCut

abbrev TopologyArcOfBoundary
    (boundary : BoundaryFamily.{u}) :
    PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u} :=
  PointwiseProductSourceW28.TopologyArcOfBoundary boundary

abbrev FramePositiveRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) :
    Type (u + 1) :=
  PointwiseProductSourceW28.FramePositiveRows.{u} noCut boundary

abbrev Lemma8ConcreteOfRows
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
      (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary) :=
  PointwiseProductSourceW28.Lemma8ConcreteOfRows lemma8

abbrev GeometrySourceFamily
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) :
    Type (u + 1) :=
  PointwiseProductSourceW28.GeometrySourceFamily.{u} noCut boundary

abbrev NoEarlySourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    Type (u + 1) :=
  PointwiseProductSourceW28.NoEarlySourceFamily lemma8

abbrev FigureExactDataFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    Type (u + 1) :=
  PointwiseProductSourceW28.FigureExactDataFamily lemma8

abbrev Lemma8UniformFiniteRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) :
    Type (u + 1) :=
  Lemma8FiniteGeometryRowsW28.UniformFiniteGeometryRows.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)

def geometrySourceFamilyOfUniformFiniteRows
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (rows : Lemma8UniformFiniteRows.{u} noCut boundary) :
    GeometrySourceFamily.{u} noCut boundary :=
  Lemma8FiniteGeometryRowsW28.geometryFieldFamilyOfUniformRows
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfBoundary boundary)
    rows

abbrev FramePositiveRowsOfGeometrySource
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    FramePositiveRows.{u} noCut boundary :=
  PointwiseProductSourceW28.lemma8RowsOfGeometrySourceFamily geometry

abbrev Lemma8ConcreteOfGeometrySource
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
      (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary) :=
  Lemma8ConcreteOfRows (FramePositiveRowsOfGeometrySource geometry)

abbrev Lemma9RouteData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    Type (u + 1) :=
  Lemma9NoEarlySourceRowsW28.M8NoEarlyRouteFamilyData.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfGeometrySource geometry)

abbrev FigureExactSourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    Type (u + 1) :=
  FigureExactAngleSourceW28.LocalExactFigureWitnessSourceFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfGeometrySource geometry)

theorem geometrySourceFamily_nonempty_iff_uniformFiniteRows
    (noCut : NoCutDependency) (boundary : BoundaryFamily.{u}) :
    Nonempty (GeometrySourceFamily.{u} noCut boundary) <->
      Nonempty (Lemma8UniformFiniteRows.{u} noCut boundary) :=
  Lemma8FiniteGeometryRowsW28.geometryFieldFamily_nonempty_iff_uniformFiniteGeometryRows
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfBoundary boundary)

theorem noEarlySourceFamily_nonempty_of_routeData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut boundary}
    (h : Nonempty (Lemma9RouteData geometry)) :
    Nonempty
      (NoEarlySourceFamily
        (FramePositiveRowsOfGeometrySource geometry)) := by
  cases h with
  | intro route =>
      exact Nonempty.intro route.toW25SourceFamily

theorem figureExactSourceFamily_nonempty_iff_figureExactDataFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    Nonempty (FigureExactSourceFamily geometry) <->
      Nonempty
        (FigureExactDataFamily
          (FramePositiveRowsOfGeometrySource geometry)) :=
  FigureExactAngleSourceW28.exactE22E23SourceBlocker_iff_localExactAngleDataFamily
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfBoundary boundary)
    (lemma8 := Lemma8ConcreteOfGeometrySource geometry)

/-! ## Actual source-data product -/

structure PointwiseProductSourceData : Type (u + 1) where
  noCut : NoCutDependency
  boundary : BoundaryFamily.{u}
  lemma8Geometry : GeometrySourceFamily.{u} noCut boundary
  lemma9Route : Lemma9RouteData lemma8Geometry
  figures : FigureExactSourceFamily lemma8Geometry

namespace PointwiseProductSourceData

def lemma8Rows
    (S : PointwiseProductSourceData.{u}) :
    FramePositiveRows.{u} S.noCut S.boundary :=
  FramePositiveRowsOfGeometrySource S.lemma8Geometry

def lemma8Concrete
    (S : PointwiseProductSourceData.{u}) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
      (PayForCutOfNoCut S.noCut) (TopologyArcOfBoundary S.boundary) :=
  Lemma8ConcreteOfRows S.lemma8Rows

def lemma9SourceFamily
    (S : PointwiseProductSourceData.{u}) :
    NoEarlySourceFamily S.lemma8Rows :=
  S.lemma9Route.toW25SourceFamily

def figureExactDataFamily
    (S : PointwiseProductSourceData.{u}) :
    FigureExactDataFamily S.lemma8Rows :=
  S.figures.toLocalExactAngleDataFamily

def toPointwiseProductBlocker
    (S : PointwiseProductSourceData.{u}) :
    W28PointwiseProductBlocker.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8 := S.lemma8Rows
  lemma9 := S.lemma9SourceFamily
  figures := S.figureExactDataFamily

def toW26Product
    (S : PointwiseProductSourceData.{u}) :
    W28W26Product.{u} :=
  S.toPointwiseProductBlocker.toW26Product

def toPointwiseSourceFamilyFields
    (S : PointwiseProductSourceData.{u}) :
    W28PointwiseSourceFamilyFields.{u} :=
  S.toPointwiseProductBlocker.toPointwiseSourceFamilyFields

theorem pointwiseProductBlocker_nonempty
    (S : PointwiseProductSourceData.{u}) :
    Nonempty W28PointwiseProductBlocker.{u} :=
  Nonempty.intro S.toPointwiseProductBlocker

theorem w26Product_nonempty
    (S : PointwiseProductSourceData.{u}) :
    Nonempty W28W26Product.{u} :=
  Nonempty.intro S.toW26Product

theorem pointwiseSourceFamilyFields_nonempty
    (S : PointwiseProductSourceData.{u}) :
    Nonempty W28PointwiseSourceFamilyFields.{u} :=
  Nonempty.intro S.toPointwiseSourceFamilyFields

end PointwiseProductSourceData

theorem pointwiseProductBlocker_nonempty_of_sourceData
    (h : Nonempty PointwiseProductSourceData.{u}) :
    Nonempty W28PointwiseProductBlocker.{u} := by
  cases h with
  | intro S =>
      exact S.pointwiseProductBlocker_nonempty

theorem w26Product_nonempty_of_sourceData
    (h : Nonempty PointwiseProductSourceData.{u}) :
    Nonempty W28W26Product.{u} := by
  cases h with
  | intro S =>
      exact S.w26Product_nonempty

theorem pointwiseSourceFamilyFields_nonempty_of_sourceData
    (h : Nonempty PointwiseProductSourceData.{u}) :
    Nonempty W28PointwiseSourceFamilyFields.{u} := by
  cases h with
  | intro S =>
      exact S.pointwiseSourceFamilyFields_nonempty

theorem sourceData_nonempty_iff_components :
    Nonempty PointwiseProductSourceData.{u} <->
      Exists fun noCut : NoCutDependency =>
        Exists fun boundary : BoundaryFamily.{u} =>
          Exists fun lemma8Geometry :
              GeometrySourceFamily.{u} noCut boundary =>
            Nonempty (Lemma9RouteData lemma8Geometry) /\
              Nonempty (FigureExactSourceFamily lemma8Geometry) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.noCut
            (Exists.intro S.boundary
              (Exists.intro S.lemma8Geometry
                (And.intro
                  (Nonempty.intro S.lemma9Route)
                  (Nonempty.intro S.figures))))
  case mpr =>
    intro h
    cases h with
    | intro noCut hBoundary =>
        cases hBoundary with
        | intro boundary hGeometry =>
            cases hGeometry with
            | intro lemma8Geometry hRest =>
                cases hRest.1 with
                | intro lemma9Route =>
                    cases hRest.2 with
                    | intro figures =>
                        exact
                          Nonempty.intro
                            { noCut := noCut
                              boundary := boundary
                              lemma8Geometry := lemma8Geometry
                              lemma9Route := lemma9Route
                              figures := figures }

/-! ## Constructors from W28/W27 source packages -/

def sourceDataOfGeometryRouteFigureSources
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u})
    (lemma8Geometry : GeometrySourceFamily.{u} noCut boundary)
    (lemma9Route : Lemma9RouteData lemma8Geometry)
    (figures : FigureExactSourceFamily lemma8Geometry) :
    PointwiseProductSourceData.{u} where
  noCut := noCut
  boundary := boundary
  lemma8Geometry := lemma8Geometry
  lemma9Route := lemma9Route
  figures := figures

def sourceDataOfUniformRowsRouteFigureSources
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u})
    (lemma8Rows : Lemma8UniformFiniteRows.{u} noCut boundary)
    (lemma9Route :
      Lemma9RouteData
        (geometrySourceFamilyOfUniformFiniteRows lemma8Rows))
    (figures :
      FigureExactSourceFamily
        (geometrySourceFamilyOfUniformFiniteRows lemma8Rows)) :
    PointwiseProductSourceData.{u} :=
  sourceDataOfGeometryRouteFigureSources
    noCut boundary
    (geometrySourceFamilyOfUniformFiniteRows lemma8Rows)
    lemma9Route figures

def sourceDataOfGeometryLocalExclusionWindowSources
    (S : PointwiseProductSourceW28.GeometryLocalExclusionWindowSources.{u}) :
    PointwiseProductSourceData.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8Geometry := S.lemma8Geometry
  lemma9Route :=
    Lemma9NoEarlySourceRowsW28.routeFamilyDataOfLocalExclusion
      S.lemma9Data
  figures :=
    FigureExactAngleSourceW28.LocalExactFigureWitnessSourceFamily.ofLocalWindowContainmentFieldsFamily
      S.figureWindows

def sourceDataOfGeometryK23WindowSources
    (S : PointwiseProductSourceW28.GeometryK23WindowSources.{u}) :
    PointwiseProductSourceData.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8Geometry := S.lemma8Geometry
  lemma9Route :=
    Lemma9NoEarlySourceRowsW28.routeFamilyDataOfK23
      S.lemma9Data
  figures :=
    FigureExactAngleSourceW28.LocalExactFigureWitnessSourceFamily.ofLocalWindowContainmentFieldsFamily
      S.figureWindows

def sourceDataOfGeometryCommonNeighborWindowSources
    (S :
      PointwiseProductSourceW28.GeometryCommonNeighborWindowSources.{u}) :
    PointwiseProductSourceData.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8Geometry := S.lemma8Geometry
  lemma9Route :=
    Lemma9NoEarlySourceRowsW28.routeFamilyDataOfCommonNeighbor
      S.lemma9Data
  figures :=
    FigureExactAngleSourceW28.LocalExactFigureWitnessSourceFamily.ofLocalWindowContainmentFieldsFamily
      S.figureWindows

def sourceDataOfGeometryThreeCommonNeighborWindowSources
    (S :
      PointwiseProductSourceW28.GeometryThreeCommonNeighborWindowSources.{u}) :
    PointwiseProductSourceData.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8Geometry := S.lemma8Geometry
  lemma9Route :=
    Lemma9NoEarlySourceRowsW28.routeFamilyDataOfThreeCommonNeighbor
      S.lemma9Data
  figures :=
    FigureExactAngleSourceW28.LocalExactFigureWitnessSourceFamily.ofLocalWindowContainmentFieldsFamily
      S.figureWindows

theorem sourceData_nonempty_of_geometryLocalExclusionWindowSources
    (h :
      Nonempty
        PointwiseProductSourceW28.GeometryLocalExclusionWindowSources.{u}) :
    Nonempty PointwiseProductSourceData.{u} := by
  cases h with
  | intro S =>
      exact Nonempty.intro (sourceDataOfGeometryLocalExclusionWindowSources S)

theorem sourceData_nonempty_of_geometryK23WindowSources
    (h : Nonempty PointwiseProductSourceW28.GeometryK23WindowSources.{u}) :
    Nonempty PointwiseProductSourceData.{u} := by
  cases h with
  | intro S =>
      exact Nonempty.intro (sourceDataOfGeometryK23WindowSources S)

theorem sourceData_nonempty_of_geometryCommonNeighborWindowSources
    (h :
      Nonempty
        PointwiseProductSourceW28.GeometryCommonNeighborWindowSources.{u}) :
    Nonempty PointwiseProductSourceData.{u} := by
  cases h with
  | intro S =>
      exact Nonempty.intro (sourceDataOfGeometryCommonNeighborWindowSources S)

theorem sourceData_nonempty_of_geometryThreeCommonNeighborWindowSources
    (h :
      Nonempty
        PointwiseProductSourceW28.GeometryThreeCommonNeighborWindowSources.{u}) :
    Nonempty PointwiseProductSourceData.{u} := by
  cases h with
  | intro S =>
      exact Nonempty.intro
        (sourceDataOfGeometryThreeCommonNeighborWindowSources S)

/-! ## Exact forward blockers -/

theorem pointwiseProductBlocker_nonempty_of_geometryLocalExclusionWindowSources
    (h :
      Nonempty
        PointwiseProductSourceW28.GeometryLocalExclusionWindowSources.{u}) :
    Nonempty W28PointwiseProductBlocker.{u} :=
  pointwiseProductBlocker_nonempty_of_sourceData
    (sourceData_nonempty_of_geometryLocalExclusionWindowSources h)

theorem pointwiseProductBlocker_nonempty_of_geometryK23WindowSources
    (h : Nonempty PointwiseProductSourceW28.GeometryK23WindowSources.{u}) :
    Nonempty W28PointwiseProductBlocker.{u} :=
  pointwiseProductBlocker_nonempty_of_sourceData
    (sourceData_nonempty_of_geometryK23WindowSources h)

theorem pointwiseProductBlocker_nonempty_of_geometryCommonNeighborWindowSources
    (h :
      Nonempty
        PointwiseProductSourceW28.GeometryCommonNeighborWindowSources.{u}) :
    Nonempty W28PointwiseProductBlocker.{u} :=
  pointwiseProductBlocker_nonempty_of_sourceData
    (sourceData_nonempty_of_geometryCommonNeighborWindowSources h)

theorem pointwiseProductBlocker_nonempty_of_geometryThreeCommonNeighborWindowSources
    (h :
      Nonempty
        PointwiseProductSourceW28.GeometryThreeCommonNeighborWindowSources.{u}) :
    Nonempty W28PointwiseProductBlocker.{u} :=
  pointwiseProductBlocker_nonempty_of_sourceData
    (sourceData_nonempty_of_geometryThreeCommonNeighborWindowSources h)

end

end PointwiseProductBlockerSourceW29
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW29PointwiseProductSourceData : Type (u + 1) :=
  Swanepoel.PointwiseProductBlockerSourceW29.PointwiseProductSourceData.{u}

abbrev SwanepoelW29PointwiseProductBlocker : Type (u + 1) :=
  Swanepoel.PointwiseProductBlockerSourceW29.W28PointwiseProductBlocker.{u}

theorem swanepoelW29_pointwiseProductBlocker_nonempty_of_sourceData
    (h : Nonempty SwanepoelW29PointwiseProductSourceData.{u}) :
    Nonempty SwanepoelW29PointwiseProductBlocker.{u} :=
  Swanepoel.PointwiseProductBlockerSourceW29.pointwiseProductBlocker_nonempty_of_sourceData
    h

theorem swanepoelW29_w26Product_nonempty_of_sourceData
    (h : Nonempty SwanepoelW29PointwiseProductSourceData.{u}) :
    Nonempty
      Swanepoel.PointwiseProductBlockerSourceW29.W28W26Product.{u} :=
  Swanepoel.PointwiseProductBlockerSourceW29.w26Product_nonempty_of_sourceData
    h

theorem swanepoelW29_pointwiseSourceFamilyFields_nonempty_of_sourceData
    (h : Nonempty SwanepoelW29PointwiseProductSourceData.{u}) :
    Nonempty
      Swanepoel.PointwiseProductBlockerSourceW29.W28PointwiseSourceFamilyFields.{u} :=
  Swanepoel.PointwiseProductBlockerSourceW29.pointwiseSourceFamilyFields_nonempty_of_sourceData
    h

end Verified
end ErdosProblems1066
