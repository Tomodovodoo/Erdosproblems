import ErdosProblems1066.Swanepoel.PointwiseSourceFieldsConcreteW27
import ErdosProblems1066.Swanepoel.NoCutLocalDeletionConcreteW27
import ErdosProblems1066.Swanepoel.BoundaryRemainingComponentsConcreteW27
import ErdosProblems1066.Swanepoel.Lemma8GeometryFamilyConcreteW27
import ErdosProblems1066.Swanepoel.Lemma9SourceFamilyConcreteW27
import ErdosProblems1066.Swanepoel.FigureWitnessConcreteW27

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W28 pointwise product-source assembly

This file isolates the exact pointwise product still needed by the W27
Swanepoel path.  It assembles
`PointwiseSourceFieldsConcreteW27.PointwiseSourceFieldsW26Product` only from
component-level source packages: no-cut deletion, selected boundary
components, Lemma 8 rows, Lemma 9 rows, and local exact Figure data.

The final lower-bound endpoint is deliberately not re-exported here.  The main
checked result is the exact blocker equivalence
`Nonempty W26Product <-> Nonempty PointwiseProductBlocker`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseProductSourceW28

universe u

noncomputable section

abbrev W26Product : Type (u + 1) :=
  PointwiseSourceFieldsConcreteW27.PointwiseSourceFieldsW26Product.{u}

abbrev PointwiseSourceFamilyFields : Type (u + 1) :=
  PointwiseSourceFieldsInhabitationW25.PointwiseSourceFamilyFields.{u}

abbrev NoCutDependency : Prop :=
  NoCutConcreteEliminationW26.CutPartitionDegreeDeletionEliminator

abbrev BoundaryFamily : Type (u + 1) :=
  BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentFamily.{u}

abbrev PayForCutOfNoCut
    (noCut : NoCutDependency) :
    PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily :=
  PointwiseSourceFieldsConcreteW27.payForCutConcreteProducerFamilyOfCutPartitionDegreeDeletionEliminator
    noCut

abbrev TopologyArcOfBoundary
    (boundary : BoundaryFamily.{u}) :
    PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u} :=
  PointwiseSourceFieldsConcreteW27.topologyArcConcreteProducerFamilyOfBoundaryComponentFamily
    boundary

abbrev FramePositiveRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) :
    Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.FramePositiveOrderRows.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)

abbrev Lemma8ConcreteOfRows
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
      (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary) :=
  PointwiseSourceFieldsConcreteW27.lemma8ConcreteProducerFamilyOfFramePositiveOrderRows
    lemma8

abbrev NoEarlySourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    Type (u + 1) :=
  Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfRows lemma8)

abbrev FigureExactDataFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    Type (u + 1) :=
  FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfRows lemma8)

abbrev GeometrySourceFamily
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) :
    Type (u + 1) :=
  Lemma8GeometryFamilyConcreteW27.GeometryFieldFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)

abbrev LocalWindowContainmentFieldsFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    Type :=
  FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfRows lemma8)

abbrev K23NoEarlySourceData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8K23NoEarlySourceFamilyData.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfRows lemma8)

abbrev ThreeCommonNeighborNoEarlySourceData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfRows lemma8)

abbrev CommonNeighborNoEarlySourceData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8CommonNeighborNoEarlySourceFamilyData.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfRows lemma8)

abbrev LocalExclusionNoEarlySourceData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8LocalExclusionNoEarlySourceFamilyData.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
    (Lemma8ConcreteOfRows lemma8)

/-! ## Exact product blocker -/

structure PointwiseProductBlocker : Type (u + 1) where
  noCut : NoCutDependency
  boundary : BoundaryFamily.{u}
  lemma8 : FramePositiveRows.{u} noCut boundary
  lemma9 : NoEarlySourceFamily lemma8
  figures : FigureExactDataFamily lemma8

namespace PointwiseProductBlocker

def toW26Product
    (P : PointwiseProductBlocker.{u}) :
    W26Product.{u} where
  noCut := P.noCut
  boundary := P.boundary
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

def toPointwiseSourceFamilyFields
    (P : PointwiseProductBlocker.{u}) :
    PointwiseSourceFamilyFields.{u} :=
  PointwiseSourceFieldsConcreteW27.pointwiseSourceFamilyFieldsOfW26Product
    P.toW26Product

theorem pointwiseSourceFamilyFields_nonempty
    (P : PointwiseProductBlocker.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} :=
  Nonempty.intro P.toPointwiseSourceFamilyFields

end PointwiseProductBlocker

def blockerOfW26Product
    (P : W26Product.{u}) :
    PointwiseProductBlocker.{u} where
  noCut := P.noCut
  boundary := P.boundary
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

@[simp]
theorem blockerOfW26Product_toW26Product
    (P : W26Product.{u}) :
    (blockerOfW26Product P).toW26Product = P := by
  cases P
  rfl

@[simp]
theorem toW26Product_blockerOfW26Product
    (P : PointwiseProductBlocker.{u}) :
    blockerOfW26Product P.toW26Product = P := by
  cases P
  rfl

def pointwiseProductBlockerEquiv :
    Equiv PointwiseProductBlocker.{u} W26Product.{u} where
  toFun := PointwiseProductBlocker.toW26Product
  invFun := blockerOfW26Product
  left_inv := by
    intro P
    exact toW26Product_blockerOfW26Product P
  right_inv := by
    intro P
    exact blockerOfW26Product_toW26Product P

theorem nonempty_w26Product_iff_pointwiseProductBlocker :
    Nonempty W26Product.{u} <-> Nonempty PointwiseProductBlocker.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (blockerOfW26Product P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toW26Product

theorem not_w26Product_iff_not_pointwiseProductBlocker :
    Not (Nonempty W26Product.{u}) <->
      Not (Nonempty PointwiseProductBlocker.{u}) := by
  constructor
  case mp =>
    intro hbad hblocker
    exact hbad (nonempty_w26Product_iff_pointwiseProductBlocker.2 hblocker)
  case mpr =>
    intro hbad hproduct
    exact hbad (nonempty_w26Product_iff_pointwiseProductBlocker.1 hproduct)

/-! ## Component constructors from W27/W26 source packages -/

def noCutDependencyOfBlockerEliminated
    (h :
      Not
        (Nonempty
          NoCutLocalDeletionConcreteW27.MinimalCutVertexBlocker)) :
    NoCutDependency :=
  NoCutLocalDeletionConcreteW27.smallestExactLocalDeletionDependency_of_not_minimalCutVertexBlocker
    h

theorem noCutDependency_iff_not_minimalCutVertexBlocker :
    NoCutDependency <->
      Not
        (Nonempty
          NoCutLocalDeletionConcreteW27.MinimalCutVertexBlocker) :=
  NoCutLocalDeletionConcreteW27.smallestExactLocalDeletionDependency_iff_not_minimalCutVertexBlocker

def boundaryFamilyOfSelectedFaceWitnessFamily
    (F :
      BoundaryRemainingComponentsConcreteW27.W25SelectedFaceWitnessFamily.{u}) :
    BoundaryFamily.{u} :=
  BoundaryRemainingComponentsConcreteW27.boundaryRemainingComponentFamilyOfSelectedFaceWitnessFamily
    F

theorem boundaryFamily_nonempty_iff_selectedFaceWitnessFamily :
    Nonempty BoundaryFamily.{u} <->
      Nonempty
        BoundaryRemainingComponentsConcreteW27.W25SelectedFaceWitnessFamily.{u} :=
  BoundaryRemainingComponentsConcreteW27.boundaryRemainingComponentFamily_nonempty_iff_selectedFaceWitnessFamily

def lemma8RowsOfGeometrySourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (G : GeometrySourceFamily.{u} noCut boundary) :
    FramePositiveRows.{u} noCut boundary :=
  Lemma8GeometryFamilyConcreteW27.framePositiveOrderRowsOfGeometryFieldFamily
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfBoundary boundary) G

theorem framePositiveRows_nonempty_iff_geometrySourceFamily
    (noCut : NoCutDependency) (boundary : BoundaryFamily.{u}) :
    Nonempty (FramePositiveRows.{u} noCut boundary) <->
      Nonempty (GeometrySourceFamily.{u} noCut boundary) :=
  Lemma8GeometryFamilyConcreteW27.framePositiveOrderRows_nonempty_iff_geometryFieldFamily
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfBoundary boundary)

def noEarlySourceFamilyOfK23Data
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {lemma8 : FramePositiveRows.{u} noCut boundary}
    (D : K23NoEarlySourceData lemma8) :
    NoEarlySourceFamily lemma8 :=
  (Lemma9SourceFamilyConcreteW27.M8K23NoEarlySourceFamilyData.toW26SourceFamily
    D).toW25SourceFamily

def noEarlySourceFamilyOfThreeCommonNeighborData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {lemma8 : FramePositiveRows.{u} noCut boundary}
    (D : ThreeCommonNeighborNoEarlySourceData lemma8) :
    NoEarlySourceFamily lemma8 :=
  (Lemma9SourceFamilyConcreteW27.M8ThreeCommonNeighborNoEarlySourceFamilyData.toW26SourceFamily
    D).toW25SourceFamily

def noEarlySourceFamilyOfCommonNeighborData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {lemma8 : FramePositiveRows.{u} noCut boundary}
    (D : CommonNeighborNoEarlySourceData lemma8) :
    NoEarlySourceFamily lemma8 :=
  (Lemma9SourceFamilyConcreteW27.M8CommonNeighborNoEarlySourceFamilyData.toW26SourceFamily
    D).toW25SourceFamily

def noEarlySourceFamilyOfLocalExclusionData
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {lemma8 : FramePositiveRows.{u} noCut boundary}
    (D : LocalExclusionNoEarlySourceData lemma8) :
    NoEarlySourceFamily lemma8 :=
  Lemma9SourceFamilyConcreteW27.M8LocalExclusionNoEarlySourceFamilyData.toW25SourceFamily
    D

theorem noEarlySourceFamily_nonempty_iff_w20SourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    (lemma8 : FramePositiveRows.{u} noCut boundary) :
    Nonempty (NoEarlySourceFamily lemma8) <->
      Nonempty
        (Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
          (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)
          (Lemma8ConcreteOfRows lemma8)) :=
  (Lemma9NoEarlyConstructionW26.nonempty_sourceFamily_iff_w25NoEarlySourceFamily
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfBoundary boundary)
    (lemma8 := Lemma8ConcreteOfRows lemma8)).symm

def figureExactDataFamilyOfLocalWindowContainmentFieldsFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {lemma8 : FramePositiveRows.{u} noCut boundary}
    (W : LocalWindowContainmentFieldsFamily lemma8) :
    FigureExactDataFamily lemma8 :=
  FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.ofLocalWindowContainmentFieldsFamily
    W

theorem figureExactDataFamily_nonempty_of_localWindowContainmentFieldsFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily.{u}}
    {lemma8 : FramePositiveRows.{u} noCut boundary}
    (h : Nonempty (LocalWindowContainmentFieldsFamily lemma8)) :
    Nonempty (FigureExactDataFamily lemma8) := by
  cases h with
  | intro W =>
      exact
        Nonempty.intro
          (figureExactDataFamilyOfLocalWindowContainmentFieldsFamily W)

def pointwiseProductBlockerOfComponents
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u})
    (lemma8 : FramePositiveRows.{u} noCut boundary)
    (lemma9 : NoEarlySourceFamily lemma8)
    (figures : FigureExactDataFamily lemma8) :
    PointwiseProductBlocker.{u} where
  noCut := noCut
  boundary := boundary
  lemma8 := lemma8
  lemma9 := lemma9
  figures := figures

def w26ProductOfComponents
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u})
    (lemma8 : FramePositiveRows.{u} noCut boundary)
    (lemma9 : NoEarlySourceFamily lemma8)
    (figures : FigureExactDataFamily lemma8) :
    W26Product.{u} :=
  (pointwiseProductBlockerOfComponents
    noCut boundary lemma8 lemma9 figures).toW26Product

/-! ## Source packages that genuinely assemble the product -/

structure GeometryLocalExclusionWindowSources : Type (u + 1) where
  noCut : NoCutDependency
  boundary : BoundaryFamily.{u}
  lemma8Geometry : GeometrySourceFamily.{u} noCut boundary
  lemma9Data :
    LocalExclusionNoEarlySourceData
      (lemma8RowsOfGeometrySourceFamily lemma8Geometry)
  figureWindows :
    LocalWindowContainmentFieldsFamily
      (lemma8RowsOfGeometrySourceFamily lemma8Geometry)

namespace GeometryLocalExclusionWindowSources

def lemma8Rows
    (S : GeometryLocalExclusionWindowSources.{u}) :
    FramePositiveRows.{u} S.noCut S.boundary :=
  lemma8RowsOfGeometrySourceFamily S.lemma8Geometry

def toPointwiseProductBlocker
    (S : GeometryLocalExclusionWindowSources.{u}) :
    PointwiseProductBlocker.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8 := S.lemma8Rows
  lemma9 := noEarlySourceFamilyOfLocalExclusionData S.lemma9Data
  figures :=
    figureExactDataFamilyOfLocalWindowContainmentFieldsFamily
      S.figureWindows

def toW26Product
    (S : GeometryLocalExclusionWindowSources.{u}) :
    W26Product.{u} :=
  S.toPointwiseProductBlocker.toW26Product

theorem nonempty_w26Product
    (S : GeometryLocalExclusionWindowSources.{u}) :
    Nonempty W26Product.{u} :=
  Nonempty.intro S.toW26Product

end GeometryLocalExclusionWindowSources

structure GeometryK23WindowSources : Type (u + 1) where
  noCut : NoCutDependency
  boundary : BoundaryFamily.{u}
  lemma8Geometry : GeometrySourceFamily.{u} noCut boundary
  lemma9Data :
    K23NoEarlySourceData
      (lemma8RowsOfGeometrySourceFamily lemma8Geometry)
  figureWindows :
    LocalWindowContainmentFieldsFamily
      (lemma8RowsOfGeometrySourceFamily lemma8Geometry)

namespace GeometryK23WindowSources

def lemma8Rows
    (S : GeometryK23WindowSources.{u}) :
    FramePositiveRows.{u} S.noCut S.boundary :=
  lemma8RowsOfGeometrySourceFamily S.lemma8Geometry

def toPointwiseProductBlocker
    (S : GeometryK23WindowSources.{u}) :
    PointwiseProductBlocker.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8 := S.lemma8Rows
  lemma9 := noEarlySourceFamilyOfK23Data S.lemma9Data
  figures :=
    figureExactDataFamilyOfLocalWindowContainmentFieldsFamily
      S.figureWindows

def toW26Product
    (S : GeometryK23WindowSources.{u}) :
    W26Product.{u} :=
  S.toPointwiseProductBlocker.toW26Product

theorem nonempty_w26Product
    (S : GeometryK23WindowSources.{u}) :
    Nonempty W26Product.{u} :=
  Nonempty.intro S.toW26Product

end GeometryK23WindowSources

structure GeometryCommonNeighborWindowSources : Type (u + 1) where
  noCut : NoCutDependency
  boundary : BoundaryFamily.{u}
  lemma8Geometry : GeometrySourceFamily.{u} noCut boundary
  lemma9Data :
    CommonNeighborNoEarlySourceData
      (lemma8RowsOfGeometrySourceFamily lemma8Geometry)
  figureWindows :
    LocalWindowContainmentFieldsFamily
      (lemma8RowsOfGeometrySourceFamily lemma8Geometry)

namespace GeometryCommonNeighborWindowSources

def lemma8Rows
    (S : GeometryCommonNeighborWindowSources.{u}) :
    FramePositiveRows.{u} S.noCut S.boundary :=
  lemma8RowsOfGeometrySourceFamily S.lemma8Geometry

def toPointwiseProductBlocker
    (S : GeometryCommonNeighborWindowSources.{u}) :
    PointwiseProductBlocker.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8 := S.lemma8Rows
  lemma9 := noEarlySourceFamilyOfCommonNeighborData S.lemma9Data
  figures :=
    figureExactDataFamilyOfLocalWindowContainmentFieldsFamily
      S.figureWindows

def toW26Product
    (S : GeometryCommonNeighborWindowSources.{u}) :
    W26Product.{u} :=
  S.toPointwiseProductBlocker.toW26Product

theorem nonempty_w26Product
    (S : GeometryCommonNeighborWindowSources.{u}) :
    Nonempty W26Product.{u} :=
  Nonempty.intro S.toW26Product

end GeometryCommonNeighborWindowSources

structure GeometryThreeCommonNeighborWindowSources : Type (u + 1) where
  noCut : NoCutDependency
  boundary : BoundaryFamily.{u}
  lemma8Geometry : GeometrySourceFamily.{u} noCut boundary
  lemma9Data :
    ThreeCommonNeighborNoEarlySourceData
      (lemma8RowsOfGeometrySourceFamily lemma8Geometry)
  figureWindows :
    LocalWindowContainmentFieldsFamily
      (lemma8RowsOfGeometrySourceFamily lemma8Geometry)

namespace GeometryThreeCommonNeighborWindowSources

def lemma8Rows
    (S : GeometryThreeCommonNeighborWindowSources.{u}) :
    FramePositiveRows.{u} S.noCut S.boundary :=
  lemma8RowsOfGeometrySourceFamily S.lemma8Geometry

def toPointwiseProductBlocker
    (S : GeometryThreeCommonNeighborWindowSources.{u}) :
    PointwiseProductBlocker.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8 := S.lemma8Rows
  lemma9 := noEarlySourceFamilyOfThreeCommonNeighborData S.lemma9Data
  figures :=
    figureExactDataFamilyOfLocalWindowContainmentFieldsFamily
      S.figureWindows

def toW26Product
    (S : GeometryThreeCommonNeighborWindowSources.{u}) :
    W26Product.{u} :=
  S.toPointwiseProductBlocker.toW26Product

theorem nonempty_w26Product
    (S : GeometryThreeCommonNeighborWindowSources.{u}) :
    Nonempty W26Product.{u} :=
  Nonempty.intro S.toW26Product

end GeometryThreeCommonNeighborWindowSources

/-! ## Exact blocker aliases for downstream workers -/

theorem pointwiseSourceFamilyFields_nonempty_of_w26Product
    (h : Nonempty W26Product.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} := by
  cases h with
  | intro P =>
      exact
        PointwiseSourceFieldsConcreteW27.pointwiseSourceFamilyFields_nonempty_of_w26Product
          P

theorem pointwiseSourceFamilyFields_nonempty_of_pointwiseProductBlocker
    (h : Nonempty PointwiseProductBlocker.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} := by
  cases h with
  | intro P =>
      exact P.pointwiseSourceFamilyFields_nonempty

end

end PointwiseProductSourceW28
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW28PointwiseProductBlocker : Type (u + 1) :=
  Swanepoel.PointwiseProductSourceW28.PointwiseProductBlocker.{u}

abbrev SwanepoelW28PointwiseW26Product : Type (u + 1) :=
  Swanepoel.PointwiseProductSourceW28.W26Product.{u}

theorem swanepoelW28_pointwiseProduct_exact_blocker :
    Nonempty SwanepoelW28PointwiseW26Product.{u} <->
      Nonempty SwanepoelW28PointwiseProductBlocker.{u} :=
  Swanepoel.PointwiseProductSourceW28.nonempty_w26Product_iff_pointwiseProductBlocker

theorem swanepoelW28_pointwiseProduct_missing_exactly_blocker_missing :
    Not (Nonempty SwanepoelW28PointwiseW26Product.{u}) <->
      Not (Nonempty SwanepoelW28PointwiseProductBlocker.{u}) :=
  Swanepoel.PointwiseProductSourceW28.not_w26Product_iff_not_pointwiseProductBlocker

end Verified
end ErdosProblems1066
