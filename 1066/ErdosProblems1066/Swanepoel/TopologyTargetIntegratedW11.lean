import ErdosProblems1066.Swanepoel.TopologyIntegratedW11
import ErdosProblems1066.Swanepoel.TopologyClosureW11
import ErdosProblems1066.Swanepoel.SubpolygonTargetIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryAngleIntegratedW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Target-facing W11 topology aggregate

This module is a thin aggregate over the checked W11 topology, boundary-angle,
subpolygon, and target ledgers.  It keeps extraction and geometry inputs
visible, while every Swanepoel target route below remains a projection from an
explicit source matrix.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyTargetIntegratedW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  TopologyIntegratedW11.CanonicalGraph C

abbrev CheckedTopologyPackage (C : _root_.UDConfig n) :=
  TopologyIntegratedW11.CheckedTopologyPackage C

abbrev TopologyFrontierPackage (C : _root_.UDConfig n) :=
  TopologyIntegratedW11.TopologyFrontierPackage C

abbrev BoundaryInput (C : _root_.UDConfig n) :=
  TopologyIntegratedW11.BoundaryInput.{u} C

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

/-! ## Explicit topology, boundary, and subpolygon aggregate -/

abbrev TopologyExtractionFields (C : _root_.UDConfig n) :=
  TopologyIntegratedW11.TopologyExtractionFields C

abbrev BoundarySubpolygonPackage (C : _root_.UDConfig n) :=
  TopologyIntegratedW11.BoundarySubpolygonPackage.{u} C

/-- Topology extraction together with explicit boundary and subpolygon data. -/
structure BoundarySubpolygonAggregate
    (C : _root_.UDConfig n) : Type (u + 3) where
  topologyExtraction : TopologyExtractionFields C
  boundarySubpolygon : BoundarySubpolygonPackage.{u} C

namespace BoundarySubpolygonAggregate

variable {C : _root_.UDConfig n}

/-- The checked topology package underlying the displayed extraction data. -/
def checkedTopology
    (A : BoundarySubpolygonAggregate.{u} C) :
    CheckedTopologyPackage C :=
  A.topologyExtraction.checkedTopology

/-- The W10 topology component fields exposed by the extraction row. -/
def topologyComponentFields
    (A : BoundarySubpolygonAggregate.{u} C) :
    MinimalFailureDirectMatrixW10.TopologyComponentFields C :=
  A.topologyExtraction.topologyComponentFields

/-- The explicit selected outer-face and subpolygon data. -/
def explicitFaceData
    (A : BoundarySubpolygonAggregate.{u} C) :
    SubpolygonInstantiation.ExplicitOuterBoundaryFaceData.{u}
      (CanonicalGraph C) :=
  A.boundarySubpolygon.explicitFaceData

/-- The selected family of subpolygons. -/
def subpolygons
    (A : BoundarySubpolygonAggregate.{u} C) :
    SubpolygonFamilyW11.SubpolygonFamilyPackage.{u}
      A.explicitFaceData :=
  A.boundarySubpolygon.subpolygons

/-- The displayed subpolygon index type. -/
abbrev Subpolygon
    (A : BoundarySubpolygonAggregate.{u} C) :
    Type u :=
  A.boundarySubpolygon.Subpolygon

/-- The displayed subpolygon cycle/count/angle datum. -/
def subpolygonData
    (A : BoundarySubpolygonAggregate.{u} C)
    (S : A.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C) :=
  A.boundarySubpolygon.subpolygonData S

/-- The topology/angle/subpolygon row selected by the boundary package. -/
def topologyAngleSubpolygonRow
    (A : BoundarySubpolygonAggregate.{u} C) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  A.boundarySubpolygon.topologyAngleSubpolygonRow

/-- The topology/angle/long-arc fields selected by the boundary package. -/
def geometryTopologyAngleLongArcFields
    (A : BoundarySubpolygonAggregate.{u} C) :
    GeometryRemainingFieldsW10.TopologyAngleLongArcFields.{u} C :=
  A.boundarySubpolygon.geometryTopologyAngleLongArcFields

/-- The partition and angle fields selected by the boundary package. -/
def partitionAngleComponentFields
    (A : BoundarySubpolygonAggregate.{u} C) :
    MinimalFailureDirectMatrixW10.PartitionAngleComponentFields.{u}
      C A.boundarySubpolygon.w10TopologyComponentFields :=
  A.boundarySubpolygon.w10PartitionAngleComponentFields

/-- Extracted exact topology fields give the W10 exact-field target row. -/
theorem exactFieldTarget
    (A : BoundarySubpolygonAggregate.{u} C) :
    TopologyClosureW11.W10ExactFieldTarget C :=
  A.topologyExtraction.exactFieldTarget

/-- Extracted exact topology fields give the W10 noncrossing frontier. -/
theorem noncrossingToExactFrontier
    (A : BoundarySubpolygonAggregate.{u} C) :
    TopologyClosureW11.W10NoncrossingToExactFrontier C :=
  A.topologyExtraction.noncrossingToExactFrontier

/-- The extracted topology fields discharge the remaining core row. -/
theorem remainingCoreTopologyRequirements
    (A : BoundarySubpolygonAggregate.{u} C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  A.topologyExtraction.remainingCoreTopologyRequirements

/-- The selected subpolygon family supplies the face-counting theorems. -/
theorem faceCountingTheorems
    (A : BoundarySubpolygonAggregate.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      A.subpolygons.toPlanarBoundaryData :=
  A.boundarySubpolygon.faceCountingTheorems

/-- Boundary-angle count inequality retained from the aggregate input. -/
theorem boundaryAngleCountInequality
    (A : BoundarySubpolygonAggregate.{u} C) :
    A.boundarySubpolygon.boundary.classification.counts.d5 +
        2 * A.boundarySubpolygon.boundary.classification.counts.d6 +
        A.boundarySubpolygon.boundary.classification.counts.b +
        A.boundarySubpolygon.boundary.classification.counts.B + 6 <=
      A.boundarySubpolygon.boundary.classification.counts.d3 :=
  A.boundarySubpolygon.boundaryAngleCountInequality

/-- Negative boundary count inequality retained from the aggregate input. -/
theorem boundaryNegativeCountInequality
    (A : BoundarySubpolygonAggregate.{u} C) :
    A.boundarySubpolygon.boundary.classification.counts.negativeCount +
        A.boundarySubpolygon.boundary.classification.counts.B + 6 <=
      A.boundarySubpolygon.boundary.classification.counts.d3 :=
  A.boundarySubpolygon.boundaryNegativeCountInequality

/-- Low-degree conclusion for each displayed subpolygon. -/
theorem subpolygonLowDegree
    (A : BoundarySubpolygonAggregate.{u} C)
    (S : A.Subpolygon) :
    6 <= 2 * (A.subpolygonData S).counts.D2 +
      (A.subpolygonData S).counts.D3 :=
  A.boundarySubpolygon.subpolygonLowDegree S

end BoundarySubpolygonAggregate

/-- Aggregate a frontier row with an explicit boundary/subpolygon input. -/
def aggregateOfFrontierAndBoundaryInput
    {C : _root_.UDConfig n}
    (T : TopologyFrontierPackage C)
    (B : BoundaryInput.{u} C) :
    BoundarySubpolygonAggregate.{u} C where
  topologyExtraction := TopologyIntegratedW11.TopologyExtractionFields.ofFrontier T
  boundarySubpolygon := TopologyIntegratedW11.boundarySubpolygonPackageOfInput B

/-- Aggregate a universe-zero boundary input with its induced topology row. -/
def aggregateOfBoundaryInput
    {C : _root_.UDConfig n}
    (B : BoundaryInput.{0} C) :
    BoundarySubpolygonAggregate.{0} C :=
  let P : BoundarySubpolygonPackage.{0} C :=
    TopologyIntegratedW11.boundarySubpolygonPackageOfInput B
  { topologyExtraction := P.topologyExtraction
    boundarySubpolygon := P }

/-! ## Explicit pointwise geometry fields -/

abbrev DirectSubpolygonGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  SubpolygonTargetIntegratedW11.DirectRow.{u} C hmin

abbrev K23SubpolygonGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  SubpolygonTargetIntegratedW11.K23Row.{u} C hmin

abbrev CommonNeighborSubpolygonGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  SubpolygonTargetIntegratedW11.CommonNeighborRow.{u} C hmin

namespace DirectSubpolygonGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def source
    (R : DirectSubpolygonGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  R.labelPrefix.toGeometrySourceFields

def containment
    (R : DirectSubpolygonGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.ContainmentFields
      R.labelPrefix.toGeometrySourceFields :=
  R.window

def noStartNoEarlyFields
    (R : DirectSubpolygonGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.NoStartNoEarlyFields
      R.labelPrefix.toGeometrySourceFields :=
  R.noStartNoEarly

def geometryClosureRow
    (R : DirectSubpolygonGeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.toGeometryClosureRow

end DirectSubpolygonGeometryFields

namespace K23SubpolygonGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def source
    (R : K23SubpolygonGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  R.labelPrefix.toGeometrySourceFields

def containment
    (R : K23SubpolygonGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.ContainmentFields
      R.labelPrefix.toGeometrySourceFields :=
  R.window

def k23NoEarlyFields
    (R : K23SubpolygonGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.K23NoEarlyFields
      R.labelPrefix.toGeometrySourceFields :=
  R.k23NoEarly

def geometryClosureRow
    (R : K23SubpolygonGeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.toGeometryClosureRow

end K23SubpolygonGeometryFields

namespace CommonNeighborSubpolygonGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def source
    (R : CommonNeighborSubpolygonGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  R.labelPrefix.toGeometrySourceFields

def containment
    (R : CommonNeighborSubpolygonGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.ContainmentFields
      R.labelPrefix.toGeometrySourceFields :=
  R.window

def commonNeighborNoEarlyFields
    (R : CommonNeighborSubpolygonGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
      R.labelPrefix.toGeometrySourceFields :=
  R.commonNeighborNoEarly

def geometryClosureRow
    (R : CommonNeighborSubpolygonGeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.toGeometryClosureRow

end CommonNeighborSubpolygonGeometryFields

abbrev DirectBoundaryAngleGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryAngleIntegratedW11.DirectGeometryRow.{u} C hmin

abbrev K23BoundaryAngleGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryAngleIntegratedW11.K23GeometryRow.{u} C hmin

abbrev CommonNeighborBoundaryAngleGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryAngleIntegratedW11.CommonNeighborGeometryRow.{u} C hmin

namespace DirectBoundaryAngleGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def source
    (R : DirectBoundaryAngleGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  R.boundaryPrefix.toGeometrySourceFields

def containment
    (R : DirectBoundaryAngleGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.ContainmentFields
      R.boundaryPrefix.toGeometrySourceFields :=
  R.window

def noStartNoEarlyFields
    (R : DirectBoundaryAngleGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.NoStartNoEarlyFields
      R.boundaryPrefix.toGeometrySourceFields :=
  R.noStartNoEarly

def geometryIntegratedFields
    (R : DirectBoundaryAngleGeometryFields.{u} C hmin) :
    GeometryIntegratedW11.DirectGeometryFields.{u} C hmin :=
  R.toGeometryIntegratedFields

def geometryClosureRow
    (R : DirectBoundaryAngleGeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.toGeometryClosureRow

end DirectBoundaryAngleGeometryFields

namespace K23BoundaryAngleGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def source
    (R : K23BoundaryAngleGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  R.boundaryPrefix.toGeometrySourceFields

def containment
    (R : K23BoundaryAngleGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.ContainmentFields
      R.boundaryPrefix.toGeometrySourceFields :=
  R.window

def k23NoEarlyFields
    (R : K23BoundaryAngleGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.K23NoEarlyFields
      R.boundaryPrefix.toGeometrySourceFields :=
  R.k23NoEarly

def geometryIntegratedFields
    (R : K23BoundaryAngleGeometryFields.{u} C hmin) :
    GeometryIntegratedW11.K23GeometryFields.{u} C hmin :=
  R.toGeometryIntegratedFields

def geometryClosureRow
    (R : K23BoundaryAngleGeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.toGeometryClosureRow

end K23BoundaryAngleGeometryFields

namespace CommonNeighborBoundaryAngleGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def source
    (R : CommonNeighborBoundaryAngleGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  R.boundaryPrefix.toGeometrySourceFields

def containment
    (R : CommonNeighborBoundaryAngleGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.ContainmentFields
      R.boundaryPrefix.toGeometrySourceFields :=
  R.window

def commonNeighborNoEarlyFields
    (R : CommonNeighborBoundaryAngleGeometryFields.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
      R.boundaryPrefix.toGeometrySourceFields :=
  R.commonNeighborNoEarly

def geometryIntegratedFields
    (R : CommonNeighborBoundaryAngleGeometryFields.{u} C hmin) :
    GeometryIntegratedW11.CommonNeighborGeometryFields.{u} C hmin :=
  R.toGeometryIntegratedFields

def geometryClosureRow
    (R : CommonNeighborBoundaryAngleGeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.toGeometryClosureRow

end CommonNeighborBoundaryAngleGeometryFields

/-! ## Conditional Swanepoel target routes -/

/-- Target projections from explicit source matrices only. -/
structure ConditionalTargetRoutes : Type (u + 3) where
  subpolygonDirect :
    SubpolygonTargetIntegratedW11.DirectMatrix.{u} -> Target
  subpolygonK23 :
    SubpolygonTargetIntegratedW11.K23Matrix.{u} -> Target
  subpolygonCommonNeighbor :
    SubpolygonTargetIntegratedW11.CommonNeighborMatrix.{u} -> Target
  boundaryDirect :
    SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u} -> Target
  boundaryK23 :
    SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u} -> Target
  boundaryCommonNeighbor :
    SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u} ->
      Target
  boundaryAngleDirect :
    BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u} -> Target
  boundaryAngleK23 :
    BoundaryAngleIntegratedW11.K23GeometryMatrix.{u} -> Target
  boundaryAngleCommonNeighbor :
    BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u} -> Target
  sourceDirect :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u} -> Target
  sourceK23 :
    BrokenLatticeIntegratedW11.K23FieldMatrix.{u} -> Target
  sourceCommonNeighbor :
    BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u} -> Target
  noEarly :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u} -> Target
  noStart :
    WindowNoEarlyRowsW11.NoStartMatrix.{u, u} -> Target

/-- The checked target routes assembled from the imported W11 ledgers. -/
def conditionalTargetRoutes : ConditionalTargetRoutes.{u} where
  subpolygonDirect :=
    SubpolygonTargetIntegratedW11.targetClosure_of_directMatrix
  subpolygonK23 :=
    SubpolygonTargetIntegratedW11.targetClosure_of_k23Matrix
  subpolygonCommonNeighbor :=
    SubpolygonTargetIntegratedW11.targetClosure_of_commonNeighborMatrix
  boundaryDirect :=
    TopologyIntegratedW11.targetFacadeOfDirectBoundaryGeometryMatrix
  boundaryK23 :=
    TopologyIntegratedW11.targetFacadeOfK23BoundaryGeometryMatrix
  boundaryCommonNeighbor :=
    TopologyIntegratedW11.targetFacadeOfCommonNeighborBoundaryGeometryMatrix
  boundaryAngleDirect := fun M =>
    TargetClosureMatrixW11.directGeometryW10Row.target
      M.toW10DirectGeometryMatrix
  boundaryAngleK23 := fun M =>
    TargetClosureMatrixW11.k23GeometryW10Row.target
      M.toW10K23GeometryMatrix
  boundaryAngleCommonNeighbor := fun M =>
    TargetClosureMatrixW11.commonNeighborGeometryW10Row.target
      M.toW10CommonNeighborGeometryMatrix
  sourceDirect :=
    TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix
  sourceK23 :=
    TargetIntegratedMatrixW11.targetClosure_of_k23FieldMatrix
  sourceCommonNeighbor :=
    TargetIntegratedMatrixW11.targetClosure_of_commonNeighborFieldMatrix
  noEarly :=
    TargetIntegratedMatrixW11.targetClosure_of_noEarlyMatrix
  noStart :=
    TargetIntegratedMatrixW11.targetClosure_of_noStartMatrix

/-! ## Aggregate matrix -/

/-- Target-facing aggregate over the checked W11 topology and target ledgers. -/
structure Matrix : Type (u + 3) where
  topologyIntegrated : TopologyIntegratedW11.Matrix.{u}
  topologyClosure : TopologyClosureW11.Matrix.{u}
  subpolygonTarget : SubpolygonTargetIntegratedW11.Matrix.{u}
  boundaryAngleIntegrated : BoundaryAngleIntegratedW11.Matrix.{u}
  targetIntegrated : TargetIntegratedMatrixW11.Matrix.{u}
  targetRoutes : ConditionalTargetRoutes.{u}

/-- The checked aggregate matrix assembled from the present W11 modules. -/
def matrix : Matrix.{u} where
  topologyIntegrated := TopologyIntegratedW11.matrix
  topologyClosure := TopologyClosureW11.matrix
  subpolygonTarget := SubpolygonTargetIntegratedW11.matrix
  boundaryAngleIntegrated := BoundaryAngleIntegratedW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  targetRoutes := conditionalTargetRoutes

/-! ## Public extraction projections -/

def topologyExtractionOfCheckedPackage
    {C : _root_.UDConfig n}
    (T : CheckedTopologyPackage C) :
    TopologyExtractionFields C :=
  TopologyIntegratedW11.topologyExtractionFieldsOfCheckedPackage T

def topologyExtractionOfFrontier
    {C : _root_.UDConfig n}
    (T : TopologyFrontierPackage C) :
    TopologyExtractionFields C :=
  TopologyIntegratedW11.topologyExtractionFieldsOfFrontier T

def boundarySubpolygonAggregateOfInput
    {C : _root_.UDConfig n}
    (T : TopologyFrontierPackage C)
    (B : BoundaryInput.{u} C) :
    BoundarySubpolygonAggregate.{u} C :=
  aggregateOfFrontierAndBoundaryInput T B

theorem exactFieldTargetOfAggregate
    {C : _root_.UDConfig n}
    (A : BoundarySubpolygonAggregate.{u} C) :
    TopologyClosureW11.W10ExactFieldTarget C :=
  A.exactFieldTarget

theorem faceCountingTheoremsOfAggregate
    {C : _root_.UDConfig n}
    (A : BoundarySubpolygonAggregate.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      A.subpolygons.toPlanarBoundaryData :=
  A.faceCountingTheorems

/-! ## Public conditional target projections -/

theorem targetOfSubpolygonDirectMatrix
    (M : SubpolygonTargetIntegratedW11.DirectMatrix.{u}) :
    Target :=
  SubpolygonTargetIntegratedW11.targetClosure_of_directMatrix M

theorem targetOfSubpolygonK23Matrix
    (M : SubpolygonTargetIntegratedW11.K23Matrix.{u}) :
    Target :=
  SubpolygonTargetIntegratedW11.targetClosure_of_k23Matrix M

theorem targetOfSubpolygonCommonNeighborMatrix
    (M : SubpolygonTargetIntegratedW11.CommonNeighborMatrix.{u}) :
    Target :=
  SubpolygonTargetIntegratedW11.targetClosure_of_commonNeighborMatrix M

theorem targetOfBoundaryDirectMatrix
    (M : SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u}) :
    Target :=
  TopologyIntegratedW11.targetFacadeOfDirectBoundaryGeometryMatrix M

theorem targetOfBoundaryK23Matrix
    (M : SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u}) :
    Target :=
  TopologyIntegratedW11.targetFacadeOfK23BoundaryGeometryMatrix M

theorem targetOfBoundaryCommonNeighborMatrix
    (M : SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u}) :
    Target :=
  TopologyIntegratedW11.targetFacadeOfCommonNeighborBoundaryGeometryMatrix M

theorem targetOfBoundaryAngleDirectMatrix
    (M : BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.directGeometryW10Row.target
    M.toW10DirectGeometryMatrix

theorem targetOfBoundaryAngleK23Matrix
    (M : BoundaryAngleIntegratedW11.K23GeometryMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.k23GeometryW10Row.target
    M.toW10K23GeometryMatrix

theorem targetOfBoundaryAngleCommonNeighborMatrix
    (M : BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.commonNeighborGeometryW10Row.target
    M.toW10CommonNeighborGeometryMatrix

theorem targetOfSourceDirectMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix M

theorem targetOfSourceK23Matrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_k23FieldMatrix M

theorem targetOfSourceCommonNeighborMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_commonNeighborFieldMatrix M

theorem targetOfNoEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noEarlyMatrix M

theorem targetOfNoStartMatrix
    (M : WindowNoEarlyRowsW11.NoStartMatrix.{u, u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noStartMatrix M

end

end TopologyTargetIntegratedW11
end Swanepoel
end ErdosProblems1066
