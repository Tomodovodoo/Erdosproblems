import ErdosProblems1066.Swanepoel.PointwiseProductBlockerSourceW29
import ErdosProblems1066.Swanepoel.UniformFiniteGeometryRowsSourceW29
import ErdosProblems1066.Swanepoel.NoEarlyConcreteSourceFamilyW29
import ErdosProblems1066.Swanepoel.ExactFigureAngleDataSourceW29

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W30 pointwise product data closure

This file is the source-only W30 handoff into
`PointwiseProductBlockerSourceW29.PointwiseProductSourceData`.  It combines
the W29 frame-row surface, the W29 no-early route-data surface, and the W29
exact Figure angle-data source surface, then forgets them to the W29 pointwise
product source data.

No final target or known-bound endpoint is used here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseProductDataClosureW30

universe u

noncomputable section

abbrev SourceData : Type (u + 1) :=
  PointwiseProductBlockerSourceW29.PointwiseProductSourceData.{u}

abbrev W28PointwiseProductBlocker : Type (u + 1) :=
  PointwiseProductBlockerSourceW29.W28PointwiseProductBlocker.{u}

abbrev W28W26Product : Type (u + 1) :=
  PointwiseProductBlockerSourceW29.W28W26Product.{u}

abbrev W28PointwiseSourceFamilyFields : Type (u + 1) :=
  PointwiseProductBlockerSourceW29.W28PointwiseSourceFamilyFields.{u}

abbrev NoCutDependency : Prop :=
  PointwiseProductBlockerSourceW29.NoCutDependency

abbrev BoundaryFamily : Type (u + 1) :=
  PointwiseProductBlockerSourceW29.BoundaryFamily.{u}

abbrev PayForCutOfNoCut
    (noCut : NoCutDependency) :
    PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily :=
  PointwiseProductBlockerSourceW29.PayForCutOfNoCut noCut

abbrev TopologyArcOfBoundary
    (boundary : BoundaryFamily.{u}) :
    PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u} :=
  PointwiseProductBlockerSourceW29.TopologyArcOfBoundary boundary

abbrev GeometrySourceFamily
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) :
    Type (u + 1) :=
  PointwiseProductBlockerSourceW29.GeometrySourceFamily.{u}
    noCut boundary

abbrev Lemma8ConcreteOfGeometrySource
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
      (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary) :=
  PointwiseProductBlockerSourceW29.Lemma8ConcreteOfGeometrySource
    geometry

abbrev UniformFiniteGeometryRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) :
    Type (u + 1) :=
  UniformFiniteGeometryRowsSourceW29.UniformFiniteGeometryRows.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)

abbrev FrameRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) :
    Prop :=
  UniformFiniteGeometryRowsSourceW29.FrameRows.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)

abbrev NeighborCyclicOrderRowsForFrameRows
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (frameRows : FrameRows.{u} noCut boundary) :
    Type :=
  UniformFiniteGeometryRowsSourceW29.NeighborCyclicOrderRowsForFrameRows.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary) frameRows

abbrev DegreeSixNeighborCyclicOrderRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) :
    Type (u + 1) :=
  UniformFiniteGeometryRowsSourceW29.DegreeSixNeighborCyclicOrderRows.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)

def uniformRowsOfFrameRowsNeighborCyclicOrderRows
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (frameRows : FrameRows.{u} noCut boundary)
    (orderRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        (noCut := noCut) (boundary := boundary) frameRows) :
    UniformFiniteGeometryRows.{u} noCut boundary :=
  UniformFiniteGeometryRowsSourceW29.uniformRowsOfFrameRowsNeighborCyclicOrderRows
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfBoundary boundary)
    frameRows orderRows

def uniformRowsOfDegreeSixNeighborCyclicOrderRows
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (rows : DegreeSixNeighborCyclicOrderRows.{u} noCut boundary) :
    UniformFiniteGeometryRows.{u} noCut boundary :=
  UniformFiniteGeometryRowsSourceW29.uniformRowsOfDegreeSixNeighborCyclicOrderRows
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfBoundary boundary)
    rows

def geometrySourceFamilyOfUniformRows
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (rows : UniformFiniteGeometryRows.{u} noCut boundary) :
    GeometrySourceFamily.{u} noCut boundary :=
  PointwiseProductBlockerSourceW29.geometrySourceFamilyOfUniformFiniteRows
    rows

def geometrySourceFamilyOfFrameRowsNeighborCyclicOrderRows
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (frameRows : FrameRows.{u} noCut boundary)
    (orderRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        (noCut := noCut) (boundary := boundary) frameRows) :
    GeometrySourceFamily.{u} noCut boundary :=
  geometrySourceFamilyOfUniformRows
    (uniformRowsOfFrameRowsNeighborCyclicOrderRows frameRows orderRows)

def geometrySourceFamilyOfDegreeSixNeighborCyclicOrderRows
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (rows : DegreeSixNeighborCyclicOrderRows.{u} noCut boundary) :
    GeometrySourceFamily.{u} noCut boundary :=
  geometrySourceFamilyOfUniformRows
    (uniformRowsOfDegreeSixNeighborCyclicOrderRows rows)

abbrev Lemma9RouteData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    Type (u + 1) :=
  PointwiseProductBlockerSourceW29.Lemma9RouteData geometry

abbrev ConcreteNoEarlyRouteData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    Type (u + 1) :=
  NoEarlyConcreteSourceFamilyW29.M8ConcreteNoEarlySourceRouteData.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfGeometrySource geometry)

def lemma9RouteDataOfConcreteNoEarlyRouteData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut boundary}
    (route : ConcreteNoEarlyRouteData geometry) :
    Lemma9RouteData geometry :=
  match route with
  | NoEarlyConcreteSourceFamilyW29.M8ConcreteNoEarlySourceRouteData.k23 data =>
      Lemma9NoEarlySourceRowsW28.routeFamilyDataOfK23 data
  | NoEarlyConcreteSourceFamilyW29.M8ConcreteNoEarlySourceRouteData.threeCommonNeighbor data =>
      Lemma9NoEarlySourceRowsW28.routeFamilyDataOfThreeCommonNeighbor data
  | NoEarlyConcreteSourceFamilyW29.M8ConcreteNoEarlySourceRouteData.commonNeighbor data =>
      Lemma9NoEarlySourceRowsW28.routeFamilyDataOfCommonNeighbor data
  | NoEarlyConcreteSourceFamilyW29.M8ConcreteNoEarlySourceRouteData.localExclusion data =>
      Lemma9NoEarlySourceRowsW28.routeFamilyDataOfLocalExclusion data

def concreteNoEarlyRouteDataOfLemma9RouteData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut boundary}
    (route : Lemma9RouteData geometry) :
    ConcreteNoEarlyRouteData geometry :=
  match route with
  | Lemma9NoEarlySourceRowsW28.M8NoEarlyRouteFamilyData.k23 data =>
      NoEarlyConcreteSourceFamilyW29.routeDataOfK23Data data
  | Lemma9NoEarlySourceRowsW28.M8NoEarlyRouteFamilyData.threeCommonNeighbor data =>
      NoEarlyConcreteSourceFamilyW29.routeDataOfThreeCommonNeighborData data
  | Lemma9NoEarlySourceRowsW28.M8NoEarlyRouteFamilyData.commonNeighbor data =>
      NoEarlyConcreteSourceFamilyW29.routeDataOfCommonNeighborData data
  | Lemma9NoEarlySourceRowsW28.M8NoEarlyRouteFamilyData.localExclusion data =>
      NoEarlyConcreteSourceFamilyW29.routeDataOfLocalExclusionData data

def concreteNoEarlyRouteDataEquivLemma9RouteData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    Equiv (ConcreteNoEarlyRouteData geometry) (Lemma9RouteData geometry) where
  toFun := lemma9RouteDataOfConcreteNoEarlyRouteData
  invFun := concreteNoEarlyRouteDataOfLemma9RouteData
  left_inv := by
    intro route
    cases route <;> rfl
  right_inv := by
    intro route
    cases route <;> rfl

theorem concreteNoEarlyRouteData_nonempty_iff_lemma9RouteData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    Nonempty (ConcreteNoEarlyRouteData geometry) <->
      Nonempty (Lemma9RouteData geometry) :=
  (concreteNoEarlyRouteDataEquivLemma9RouteData geometry).nonempty_congr

abbrev FigureExactSourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    Type (u + 1) :=
  PointwiseProductBlockerSourceW29.FigureExactSourceFamily geometry

abbrev FigureAngleDataSourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    Type (u + 1) :=
  ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSourceFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfGeometrySource geometry)

def figureExactSourceFamilyOfAngleDataSourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut boundary}
    (figures : FigureAngleDataSourceFamily geometry) :
    FigureExactSourceFamily geometry :=
  figures.toLocalExactFigureWitnessSourceFamily

def figureAngleDataSourceFamilyOfFigureExactSourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {geometry : GeometrySourceFamily.{u} noCut boundary}
    (figures : FigureExactSourceFamily geometry) :
    FigureAngleDataSourceFamily geometry :=
  ExactFigureAngleDataSourceW29.localExactFigureAngleDataSourceFamily_of_localExactAngleDataFamily
    figures.toLocalExactAngleDataFamily

theorem figureExactSourceFamily_nonempty_iff_angleDataSourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (geometry : GeometrySourceFamily.{u} noCut boundary) :
    Nonempty (FigureExactSourceFamily geometry) <->
      Nonempty (FigureAngleDataSourceFamily geometry) :=
  ExactFigureAngleDataSourceW29.exactE22E23SourceBlocker_iff_localExactFigureAngleDataSourceFamily
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfBoundary boundary)
    (lemma8 := Lemma8ConcreteOfGeometrySource geometry)

/-! ## Combined source packages -/

structure UniformRouteFigureSourceData : Type (u + 1) where
  noCut : NoCutDependency
  boundary : BoundaryFamily.{u}
  uniformRows : UniformFiniteGeometryRows.{u} noCut boundary
  routeData :
    ConcreteNoEarlyRouteData
      (geometrySourceFamilyOfUniformRows uniformRows)
  figureData :
    FigureAngleDataSourceFamily
      (geometrySourceFamilyOfUniformRows uniformRows)

namespace UniformRouteFigureSourceData

def geometry
    (S : UniformRouteFigureSourceData.{u}) :
    GeometrySourceFamily.{u} S.noCut S.boundary :=
  geometrySourceFamilyOfUniformRows S.uniformRows

def toSourceData
    (S : UniformRouteFigureSourceData.{u}) :
    SourceData.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8Geometry := S.geometry
  lemma9Route := lemma9RouteDataOfConcreteNoEarlyRouteData S.routeData
  figures := figureExactSourceFamilyOfAngleDataSourceFamily S.figureData

theorem sourceData_nonempty
    (S : UniformRouteFigureSourceData.{u}) :
    Nonempty SourceData.{u} :=
  Nonempty.intro S.toSourceData

end UniformRouteFigureSourceData

structure FrameRouteFigureSourceData : Type (u + 1) where
  noCut : NoCutDependency
  boundary : BoundaryFamily.{u}
  frameRows : FrameRows.{u} noCut boundary
  orderRows :
    NeighborCyclicOrderRowsForFrameRows.{u}
      (noCut := noCut) (boundary := boundary) frameRows
  routeData :
    ConcreteNoEarlyRouteData
      (geometrySourceFamilyOfFrameRowsNeighborCyclicOrderRows
        (noCut := noCut) (boundary := boundary)
        frameRows orderRows)
  figureData :
    FigureAngleDataSourceFamily
      (geometrySourceFamilyOfFrameRowsNeighborCyclicOrderRows
        (noCut := noCut) (boundary := boundary)
        frameRows orderRows)

namespace FrameRouteFigureSourceData

def uniformRows
    (S : FrameRouteFigureSourceData.{u}) :
    UniformFiniteGeometryRows.{u} S.noCut S.boundary :=
  uniformRowsOfFrameRowsNeighborCyclicOrderRows S.frameRows S.orderRows

def geometry
    (S : FrameRouteFigureSourceData.{u}) :
    GeometrySourceFamily.{u} S.noCut S.boundary :=
  geometrySourceFamilyOfFrameRowsNeighborCyclicOrderRows
    (noCut := S.noCut) (boundary := S.boundary)
    S.frameRows S.orderRows

def toUniformRouteFigureSourceData
    (S : FrameRouteFigureSourceData.{u}) :
    UniformRouteFigureSourceData.{u} where
  noCut := S.noCut
  boundary := S.boundary
  uniformRows := S.uniformRows
  routeData := S.routeData
  figureData := S.figureData

def toSourceData
    (S : FrameRouteFigureSourceData.{u}) :
    SourceData.{u} :=
  S.toUniformRouteFigureSourceData.toSourceData

theorem sourceData_nonempty
    (S : FrameRouteFigureSourceData.{u}) :
    Nonempty SourceData.{u} :=
  Nonempty.intro S.toSourceData

end FrameRouteFigureSourceData

structure DegreeSixRouteFigureSourceData : Type (u + 1) where
  noCut : NoCutDependency
  boundary : BoundaryFamily.{u}
  degreeRows : DegreeSixNeighborCyclicOrderRows.{u} noCut boundary
  routeData :
    ConcreteNoEarlyRouteData
      (geometrySourceFamilyOfDegreeSixNeighborCyclicOrderRows degreeRows)
  figureData :
    FigureAngleDataSourceFamily
      (geometrySourceFamilyOfDegreeSixNeighborCyclicOrderRows degreeRows)

namespace DegreeSixRouteFigureSourceData

def uniformRows
    (S : DegreeSixRouteFigureSourceData.{u}) :
    UniformFiniteGeometryRows.{u} S.noCut S.boundary :=
  uniformRowsOfDegreeSixNeighborCyclicOrderRows S.degreeRows

def geometry
    (S : DegreeSixRouteFigureSourceData.{u}) :
    GeometrySourceFamily.{u} S.noCut S.boundary :=
  geometrySourceFamilyOfDegreeSixNeighborCyclicOrderRows S.degreeRows

def toUniformRouteFigureSourceData
    (S : DegreeSixRouteFigureSourceData.{u}) :
    UniformRouteFigureSourceData.{u} where
  noCut := S.noCut
  boundary := S.boundary
  uniformRows := S.uniformRows
  routeData := S.routeData
  figureData := S.figureData

def toSourceData
    (S : DegreeSixRouteFigureSourceData.{u}) :
    SourceData.{u} :=
  S.toUniformRouteFigureSourceData.toSourceData

theorem sourceData_nonempty
    (S : DegreeSixRouteFigureSourceData.{u}) :
    Nonempty SourceData.{u} :=
  Nonempty.intro S.toSourceData

end DegreeSixRouteFigureSourceData

def sourceDataOfUniformRowsRouteFigureData
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u})
    (uniformRows : UniformFiniteGeometryRows.{u} noCut boundary)
    (routeData :
      ConcreteNoEarlyRouteData
        (geometrySourceFamilyOfUniformRows uniformRows))
    (figureData :
      FigureAngleDataSourceFamily
        (geometrySourceFamilyOfUniformRows uniformRows)) :
    SourceData.{u} :=
  (UniformRouteFigureSourceData.mk
    noCut boundary uniformRows routeData figureData).toSourceData

def sourceDataOfFrameRowsRouteFigureData
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u})
    (frameRows : FrameRows.{u} noCut boundary)
    (orderRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        (noCut := noCut) (boundary := boundary) frameRows)
    (routeData :
      ConcreteNoEarlyRouteData
        (geometrySourceFamilyOfFrameRowsNeighborCyclicOrderRows
          (noCut := noCut) (boundary := boundary)
          frameRows orderRows))
    (figureData :
      FigureAngleDataSourceFamily
        (geometrySourceFamilyOfFrameRowsNeighborCyclicOrderRows
          (noCut := noCut) (boundary := boundary)
          frameRows orderRows)) :
    SourceData.{u} :=
  (FrameRouteFigureSourceData.mk
    noCut boundary frameRows orderRows routeData figureData).toSourceData

def sourceDataOfDegreeSixRouteFigureData
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u})
    (degreeRows : DegreeSixNeighborCyclicOrderRows.{u} noCut boundary)
    (routeData :
      ConcreteNoEarlyRouteData
        (geometrySourceFamilyOfDegreeSixNeighborCyclicOrderRows
          degreeRows))
    (figureData :
      FigureAngleDataSourceFamily
        (geometrySourceFamilyOfDegreeSixNeighborCyclicOrderRows
          degreeRows)) :
    SourceData.{u} :=
  (DegreeSixRouteFigureSourceData.mk
    noCut boundary degreeRows routeData figureData).toSourceData

theorem sourceData_nonempty_of_uniformRouteFigureSourceData
    (h : Nonempty UniformRouteFigureSourceData.{u}) :
    Nonempty SourceData.{u} := by
  cases h with
  | intro S =>
      exact S.sourceData_nonempty

theorem sourceData_nonempty_of_frameRouteFigureSourceData
    (h : Nonempty FrameRouteFigureSourceData.{u}) :
    Nonempty SourceData.{u} := by
  cases h with
  | intro S =>
      exact S.sourceData_nonempty

theorem sourceData_nonempty_of_degreeSixRouteFigureSourceData
    (h : Nonempty DegreeSixRouteFigureSourceData.{u}) :
    Nonempty SourceData.{u} := by
  cases h with
  | intro S =>
      exact S.sourceData_nonempty

theorem pointwiseProductBlocker_nonempty_of_uniformRouteFigureSourceData
    (h : Nonempty UniformRouteFigureSourceData.{u}) :
    Nonempty W28PointwiseProductBlocker.{u} :=
  PointwiseProductBlockerSourceW29.pointwiseProductBlocker_nonempty_of_sourceData
    (sourceData_nonempty_of_uniformRouteFigureSourceData h)

theorem pointwiseProductBlocker_nonempty_of_frameRouteFigureSourceData
    (h : Nonempty FrameRouteFigureSourceData.{u}) :
    Nonempty W28PointwiseProductBlocker.{u} :=
  PointwiseProductBlockerSourceW29.pointwiseProductBlocker_nonempty_of_sourceData
    (sourceData_nonempty_of_frameRouteFigureSourceData h)

theorem pointwiseProductBlocker_nonempty_of_degreeSixRouteFigureSourceData
    (h : Nonempty DegreeSixRouteFigureSourceData.{u}) :
    Nonempty W28PointwiseProductBlocker.{u} :=
  PointwiseProductBlockerSourceW29.pointwiseProductBlocker_nonempty_of_sourceData
    (sourceData_nonempty_of_degreeSixRouteFigureSourceData h)

theorem w26Product_nonempty_of_uniformRouteFigureSourceData
    (h : Nonempty UniformRouteFigureSourceData.{u}) :
    Nonempty W28W26Product.{u} :=
  PointwiseProductBlockerSourceW29.w26Product_nonempty_of_sourceData
    (sourceData_nonempty_of_uniformRouteFigureSourceData h)

theorem w26Product_nonempty_of_frameRouteFigureSourceData
    (h : Nonempty FrameRouteFigureSourceData.{u}) :
    Nonempty W28W26Product.{u} :=
  PointwiseProductBlockerSourceW29.w26Product_nonempty_of_sourceData
    (sourceData_nonempty_of_frameRouteFigureSourceData h)

theorem w26Product_nonempty_of_degreeSixRouteFigureSourceData
    (h : Nonempty DegreeSixRouteFigureSourceData.{u}) :
    Nonempty W28W26Product.{u} :=
  PointwiseProductBlockerSourceW29.w26Product_nonempty_of_sourceData
    (sourceData_nonempty_of_degreeSixRouteFigureSourceData h)

/-! ## Source-package inhabitance equivalences -/

theorem uniformRouteFigureSourceData_nonempty_iff :
    Nonempty UniformRouteFigureSourceData.{u} <->
      Exists fun noCut : NoCutDependency =>
        Exists fun boundary : BoundaryFamily.{u} =>
          Exists fun uniformRows :
              UniformFiniteGeometryRows.{u} noCut boundary =>
            Nonempty
                (ConcreteNoEarlyRouteData
                  (geometrySourceFamilyOfUniformRows uniformRows)) /\
              Nonempty
                (FigureAngleDataSourceFamily
                  (geometrySourceFamilyOfUniformRows uniformRows)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.noCut
            (Exists.intro S.boundary
              (Exists.intro S.uniformRows
                (And.intro
                  (Nonempty.intro S.routeData)
                  (Nonempty.intro S.figureData))))
  case mpr =>
    intro h
    cases h with
    | intro noCut hBoundary =>
        cases hBoundary with
        | intro boundary hRows =>
            cases hRows with
            | intro uniformRows hData =>
                cases hData.1 with
                | intro routeData =>
                    cases hData.2 with
                    | intro figureData =>
                        exact
                          Nonempty.intro
                            { noCut := noCut
                              boundary := boundary
                              uniformRows := uniformRows
                              routeData := routeData
                              figureData := figureData }

theorem frameRouteFigureSourceData_nonempty_iff :
    Nonempty FrameRouteFigureSourceData.{u} <->
      Exists fun noCut : NoCutDependency =>
        Exists fun boundary : BoundaryFamily.{u} =>
          Exists fun frameRows : FrameRows.{u} noCut boundary =>
            Exists fun orderRows :
                NeighborCyclicOrderRowsForFrameRows.{u}
                  (noCut := noCut) (boundary := boundary) frameRows =>
              Nonempty
                  (ConcreteNoEarlyRouteData
                    (geometrySourceFamilyOfFrameRowsNeighborCyclicOrderRows
                      (noCut := noCut) (boundary := boundary)
                      frameRows orderRows)) /\
                Nonempty
                  (FigureAngleDataSourceFamily
                    (geometrySourceFamilyOfFrameRowsNeighborCyclicOrderRows
                      (noCut := noCut) (boundary := boundary)
                      frameRows orderRows)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.noCut
            (Exists.intro S.boundary
              (Exists.intro S.frameRows
                (Exists.intro S.orderRows
                  (And.intro
                    (Nonempty.intro S.routeData)
                    (Nonempty.intro S.figureData)))))
  case mpr =>
    intro h
    cases h with
    | intro noCut hBoundary =>
        cases hBoundary with
        | intro boundary hFrame =>
            cases hFrame with
            | intro frameRows hOrder =>
                cases hOrder with
                | intro orderRows hData =>
                    cases hData.1 with
                    | intro routeData =>
                        cases hData.2 with
                        | intro figureData =>
                            exact
                              Nonempty.intro
                                { noCut := noCut
                                  boundary := boundary
                                  frameRows := frameRows
                                  orderRows := orderRows
                                  routeData := routeData
                                  figureData := figureData }

theorem degreeSixRouteFigureSourceData_nonempty_iff :
    Nonempty DegreeSixRouteFigureSourceData.{u} <->
      Exists fun noCut : NoCutDependency =>
        Exists fun boundary : BoundaryFamily.{u} =>
          Exists fun degreeRows :
              DegreeSixNeighborCyclicOrderRows.{u} noCut boundary =>
            Nonempty
                (ConcreteNoEarlyRouteData
                  (geometrySourceFamilyOfDegreeSixNeighborCyclicOrderRows
                    degreeRows)) /\
              Nonempty
                (FigureAngleDataSourceFamily
                  (geometrySourceFamilyOfDegreeSixNeighborCyclicOrderRows
                    degreeRows)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.noCut
            (Exists.intro S.boundary
              (Exists.intro S.degreeRows
                (And.intro
                  (Nonempty.intro S.routeData)
                  (Nonempty.intro S.figureData))))
  case mpr =>
    intro h
    cases h with
    | intro noCut hBoundary =>
        cases hBoundary with
        | intro boundary hRows =>
            cases hRows with
            | intro degreeRows hData =>
                cases hData.1 with
                | intro routeData =>
                    cases hData.2 with
                    | intro figureData =>
                        exact
                          Nonempty.intro
                            { noCut := noCut
                              boundary := boundary
                              degreeRows := degreeRows
                              routeData := routeData
                              figureData := figureData }

end

end PointwiseProductDataClosureW30
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW30PointwiseProductSourceData : Type (u + 1) :=
  Swanepoel.PointwiseProductDataClosureW30.SourceData.{u}

abbrev SwanepoelW30PointwiseProductUniformRouteFigureSourceData :
    Type (u + 1) :=
  Swanepoel.PointwiseProductDataClosureW30.UniformRouteFigureSourceData.{u}

abbrev SwanepoelW30PointwiseProductFrameRouteFigureSourceData :
    Type (u + 1) :=
  Swanepoel.PointwiseProductDataClosureW30.FrameRouteFigureSourceData.{u}

abbrev SwanepoelW30PointwiseProductDegreeSixRouteFigureSourceData :
    Type (u + 1) :=
  Swanepoel.PointwiseProductDataClosureW30.DegreeSixRouteFigureSourceData.{u}

theorem swanepoelW30_pointwiseProductSourceData_of_uniformRouteFigureSourceData
    (h :
      Nonempty SwanepoelW30PointwiseProductUniformRouteFigureSourceData.{u}) :
    Nonempty SwanepoelW30PointwiseProductSourceData.{u} :=
  Swanepoel.PointwiseProductDataClosureW30.sourceData_nonempty_of_uniformRouteFigureSourceData
    h

theorem swanepoelW30_pointwiseProductSourceData_of_frameRouteFigureSourceData
    (h :
      Nonempty SwanepoelW30PointwiseProductFrameRouteFigureSourceData.{u}) :
    Nonempty SwanepoelW30PointwiseProductSourceData.{u} :=
  Swanepoel.PointwiseProductDataClosureW30.sourceData_nonempty_of_frameRouteFigureSourceData
    h

theorem swanepoelW30_pointwiseProductSourceData_of_degreeSixRouteFigureSourceData
    (h :
      Nonempty SwanepoelW30PointwiseProductDegreeSixRouteFigureSourceData.{u}) :
    Nonempty SwanepoelW30PointwiseProductSourceData.{u} :=
  Swanepoel.PointwiseProductDataClosureW30.sourceData_nonempty_of_degreeSixRouteFigureSourceData
    h

theorem swanepoelW30_pointwiseProductBlocker_of_frameRouteFigureSourceData
    (h :
      Nonempty SwanepoelW30PointwiseProductFrameRouteFigureSourceData.{u}) :
    Nonempty
      Swanepoel.PointwiseProductDataClosureW30.W28PointwiseProductBlocker.{u} :=
  Swanepoel.PointwiseProductDataClosureW30.pointwiseProductBlocker_nonempty_of_frameRouteFigureSourceData
    h

theorem swanepoelW30_w26Product_of_frameRouteFigureSourceData
    (h :
      Nonempty SwanepoelW30PointwiseProductFrameRouteFigureSourceData.{u}) :
    Nonempty
      Swanepoel.PointwiseProductDataClosureW30.W28W26Product.{u} :=
  Swanepoel.PointwiseProductDataClosureW30.w26Product_nonempty_of_frameRouteFigureSourceData
    h

end Verified
end ErdosProblems1066
