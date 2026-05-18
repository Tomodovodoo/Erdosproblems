import ErdosProblems1066.Swanepoel.TopologyTargetFinalW11
import ErdosProblems1066.Swanepoel.BoundaryLabelTargetFinalW11
import ErdosProblems1066.Swanepoel.BoundaryAngleTargetFinalW11
import ErdosProblems1066.Swanepoel.SubpolygonTargetFinalW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 topology/boundary route summary

This leaf summary records the checked topology, boundary-label,
boundary-angle, and subpolygon target ledgers.  It also displays the explicit
matrix surfaces that still have to be supplied by a caller, and exposes only
target projections from those supplied matrices.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyBoundaryRouteSummaryFinalW11

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev CheckedTopologyPackage (C : _root_.UDConfig n) :=
  TopologyTargetFinalW11.CheckedTopologyPackage C

abbrev TopologyFrontierPackage (C : _root_.UDConfig n) :=
  TopologyTargetFinalW11.TopologyFrontierPackage C

abbrev BoundaryInput (C : _root_.UDConfig n) :=
  TopologyTargetFinalW11.BoundaryInput.{u} C

abbrev TopologyExtractionFields (C : _root_.UDConfig n) :=
  TopologyTargetFinalW11.TopologyExtractionFields C

abbrev BoundarySubpolygonAggregate (C : _root_.UDConfig n) :=
  TopologyTargetFinalW11.BoundarySubpolygonAggregate.{u} C

/-! ## Checked ledgers -/

/-- Checked W11 topology and boundary target ledgers used by this summary. -/
structure CheckedLedgers : Type (u + 5) where
  topologyTarget :
    TopologyTargetFinalW11.Matrix.{u}
  boundaryLabelTarget :
    BoundaryLabelTargetFinalW11.Matrix.{u}
  boundaryAngleTarget :
    BoundaryAngleTargetFinalW11.Matrix.{u}
  subpolygonTarget :
    SubpolygonTargetFinalW11.Matrix.{u}

/-- Imported checked target ledgers. -/
def checkedLedgers : CheckedLedgers.{u} where
  topologyTarget := TopologyTargetFinalW11.matrix
  boundaryLabelTarget := BoundaryLabelTargetFinalW11.matrix
  boundaryAngleTarget := BoundaryAngleTargetFinalW11.matrix
  subpolygonTarget := SubpolygonTargetFinalW11.matrix

/-! ## Explicit matrix surfaces -/

/-- The caller-supplied matrix package for the topology/boundary routes. -/
structure ExplicitMatrices : Type (u + 5) where
  topology :
    TopologyTargetFinalW11.ExplicitFinalGeometryMatrices.{u}
  boundaryLabel :
    BoundaryLabelTargetFinalW11.FinalMatrixInput.{u}
  boundaryAngle :
    BoundaryAngleTargetFinalW11.FinalMatrixInput.{u}
  subpolygon :
    SubpolygonTargetFinalW11.FinalMatrixInput.{u}

namespace ExplicitMatrices

/-- Boundary-angle matrix selected by the topology package. -/
def topologyBoundaryAngle
    (M : ExplicitMatrices.{u}) :
    BoundaryAngleTargetFinalW11.FinalMatrixInput.{u} :=
  M.topology.boundaryAngleFinal

/-- Final subpolygon matrix selected by the topology package. -/
def topologySubpolygon
    (M : ExplicitMatrices.{u}) :
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u} :=
  M.topology.subpolygonFinal

@[simp]
theorem topologyBoundaryAngle_eq
    (M : ExplicitMatrices.{u}) :
    M.topologyBoundaryAngle = M.topology.boundaryAngleFinal := by
  rfl

@[simp]
theorem topologySubpolygon_eq
    (M : ExplicitMatrices.{u}) :
    M.topologySubpolygon = M.topology.subpolygonFinal := by
  rfl

end ExplicitMatrices

/-! ## Topology extraction projections -/

/-- Checked topology extraction and boundary/subpolygon projections. -/
def extractionMatrix :
    TopologyTargetFinalW11.ExplicitExtractionMatrix.{u} :=
  TopologyTargetFinalW11.explicitExtractionMatrix

def topologyExtractionOfCheckedPackage
    {C : _root_.UDConfig n}
    (T : CheckedTopologyPackage C) :
    TopologyExtractionFields C :=
  TopologyTargetFinalW11.topologyExtractionOfCheckedPackage T

def topologyExtractionOfFrontier
    {C : _root_.UDConfig n}
    (T : TopologyFrontierPackage C) :
    TopologyExtractionFields C :=
  TopologyTargetFinalW11.topologyExtractionOfFrontier T

def boundarySubpolygonAggregateOfInput
    {C : _root_.UDConfig n}
    (T : TopologyFrontierPackage C)
    (B : BoundaryInput.{u} C) :
    BoundarySubpolygonAggregate.{u} C :=
  TopologyTargetFinalW11.boundarySubpolygonAggregateOfInput T B

theorem exactTopologyOfBoundarySubpolygonAggregate
    {C : _root_.UDConfig n}
    (A : BoundarySubpolygonAggregate.{u} C) :
    TopologyClosureW11.W10ExactFieldTarget C :=
  TopologyTargetFinalW11.exactTopologyOfBoundarySubpolygonAggregate A

theorem faceCountingOfBoundarySubpolygonAggregate
    {C : _root_.UDConfig n}
    (A : BoundarySubpolygonAggregate.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      A.subpolygons.toPlanarBoundaryData :=
  TopologyTargetFinalW11.faceCountingOfBoundarySubpolygonAggregate A

/-! ## Conditional target projections -/

/-- Conditional target projections from the supplied explicit matrices. -/
structure ConditionalTargetProjections : Type (u + 5) where
  topologyBoundaryDirect :
    ExplicitMatrices.{u} -> Target
  topologyBoundaryK23 :
    ExplicitMatrices.{u} -> Target
  topologyBoundaryCommonNeighbor :
    ExplicitMatrices.{u} -> Target
  topologyBoundaryAngleDirect :
    ExplicitMatrices.{u} -> Target
  topologyBoundaryAngleK23 :
    ExplicitMatrices.{u} -> Target
  topologyBoundaryAngleCommonNeighbor :
    ExplicitMatrices.{u} -> Target
  topologySubpolygonDirect :
    ExplicitMatrices.{u} -> Target
  topologySubpolygonK23 :
    ExplicitMatrices.{u} -> Target
  topologySubpolygonCommonNeighbor :
    ExplicitMatrices.{u} -> Target
  boundaryLabel :
    ExplicitMatrices.{u} -> Target
  boundaryLabelNoEarly :
    ExplicitMatrices.{u} -> Target
  boundaryLabelNoStart :
    ExplicitMatrices.{u} -> Target
  boundaryLabelGeometryTarget :
    ExplicitMatrices.{u} -> Target
  boundaryAngleDirect :
    ExplicitMatrices.{u} -> Target
  boundaryAngleK23 :
    ExplicitMatrices.{u} -> Target
  boundaryAngleCommonNeighbor :
    ExplicitMatrices.{u} -> Target
  subpolygonDirect :
    ExplicitMatrices.{u} -> Target
  subpolygonTopologyDirect :
    ExplicitMatrices.{u} -> Target
  subpolygonTopologyK23 :
    ExplicitMatrices.{u} -> Target
  subpolygonTopologyCommonNeighbor :
    ExplicitMatrices.{u} -> Target

/-- Checked conditional target projections assembled from the target ledgers. -/
def conditionalTargetProjections :
    ConditionalTargetProjections.{u} where
  topologyBoundaryDirect := fun M =>
    TopologyTargetFinalW11.swanepoelTarget_via_topologyBoundaryDirect
      M.topology
  topologyBoundaryK23 := fun M =>
    TopologyTargetFinalW11.swanepoelTarget_via_topologyBoundaryK23
      M.topology
  topologyBoundaryCommonNeighbor := fun M =>
    TopologyTargetFinalW11.swanepoelTarget_via_topologyBoundaryCommonNeighbor
      M.topology
  topologyBoundaryAngleDirect := fun M =>
    TopologyTargetFinalW11.swanepoelTarget_via_topologyBoundaryAngleDirect
      M.topology
  topologyBoundaryAngleK23 := fun M =>
    TopologyTargetFinalW11.swanepoelTarget_via_topologyBoundaryAngleK23
      M.topology
  topologyBoundaryAngleCommonNeighbor := fun M =>
    TopologyTargetFinalW11.swanepoelTarget_via_topologyBoundaryAngleCommonNeighbor
      M.topology
  topologySubpolygonDirect := fun M =>
    TopologyTargetFinalW11.swanepoelTarget_via_topologySubpolygonDirect
      M.topology
  topologySubpolygonK23 := fun M =>
    TopologyTargetFinalW11.swanepoelTarget_via_topologySubpolygonK23
      M.topology
  topologySubpolygonCommonNeighbor := fun M =>
    TopologyTargetFinalW11.swanepoelTarget_via_topologySubpolygonCommonNeighbor
      M.topology
  boundaryLabel := fun M =>
    BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_boundaryLabel
      M.boundaryLabel
  boundaryLabelNoEarly := fun M =>
    BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_explicitNoEarly
      M.boundaryLabel
  boundaryLabelNoStart := fun M =>
    BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_explicitNoStart
      M.boundaryLabel
  boundaryLabelGeometryTarget := fun M =>
    BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_geometryTarget
      M.boundaryLabel
  boundaryAngleDirect := fun M =>
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_direct
      M.boundaryAngle
  boundaryAngleK23 := fun M =>
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_k23
      M.boundaryAngle
  boundaryAngleCommonNeighbor := fun M =>
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_commonNeighbor
      M.boundaryAngle
  subpolygonDirect := fun M =>
    SubpolygonTargetFinalW11.target_of_finalMatrix_via_subpolygon_direct
      M.subpolygon
  subpolygonTopologyDirect := fun M =>
    SubpolygonTargetFinalW11.target_of_finalMatrix_via_topology_direct
      M.subpolygon
  subpolygonTopologyK23 := fun M =>
    SubpolygonTargetFinalW11.target_of_finalMatrix_via_topology_k23
      M.subpolygon
  subpolygonTopologyCommonNeighbor := fun M =>
    SubpolygonTargetFinalW11.target_of_finalMatrix_via_topology_commonNeighbor
      M.subpolygon

/-! ## Final summary matrix -/

/-- Concise checked topology/boundary route summary matrix. -/
structure Matrix : Type (u + 7) where
  checked :
    CheckedLedgers.{u}
  extraction :
    TopologyTargetFinalW11.ExplicitExtractionMatrix.{u}
  explicit :
    Type (u + 5)
  projections :
    ConditionalTargetProjections.{u}

/-- The checked final W11 topology/boundary route summary matrix. -/
def matrix :
    Matrix.{u} where
  checked := checkedLedgers
  extraction := extractionMatrix
  explicit := ExplicitMatrices.{u}
  projections := conditionalTargetProjections

theorem matrix_nonempty :
    Nonempty Matrix.{u} :=
  Nonempty.intro matrix

theorem checked_topologyTarget :
    matrix.checked.topologyTarget = TopologyTargetFinalW11.matrix := by
  rfl

theorem checked_boundaryLabelTarget :
    matrix.checked.boundaryLabelTarget =
      BoundaryLabelTargetFinalW11.matrix := by
  rfl

theorem checked_boundaryAngleTarget :
    matrix.checked.boundaryAngleTarget =
      BoundaryAngleTargetFinalW11.matrix := by
  rfl

theorem checked_subpolygonTarget :
    matrix.checked.subpolygonTarget = SubpolygonTargetFinalW11.matrix := by
  rfl

/-! ## Public conditional target projections -/

theorem target_of_explicitMatrices_via_topologyBoundaryDirect
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.topologyBoundaryDirect M

theorem target_of_explicitMatrices_via_topologyBoundaryK23
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.topologyBoundaryK23 M

theorem target_of_explicitMatrices_via_topologyBoundaryCommonNeighbor
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.topologyBoundaryCommonNeighbor M

theorem target_of_explicitMatrices_via_topologyBoundaryAngleDirect
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.topologyBoundaryAngleDirect M

theorem target_of_explicitMatrices_via_topologyBoundaryAngleK23
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.topologyBoundaryAngleK23 M

theorem target_of_explicitMatrices_via_topologyBoundaryAngleCommonNeighbor
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.topologyBoundaryAngleCommonNeighbor M

theorem target_of_explicitMatrices_via_topologySubpolygonDirect
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.topologySubpolygonDirect M

theorem target_of_explicitMatrices_via_topologySubpolygonK23
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.topologySubpolygonK23 M

theorem target_of_explicitMatrices_via_topologySubpolygonCommonNeighbor
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.topologySubpolygonCommonNeighbor M

theorem target_of_explicitMatrices_via_boundaryLabel
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.boundaryLabel M

theorem target_of_explicitMatrices_via_boundaryLabelNoEarly
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.boundaryLabelNoEarly M

theorem target_of_explicitMatrices_via_boundaryLabelNoStart
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.boundaryLabelNoStart M

theorem target_of_explicitMatrices_via_boundaryLabelGeometryTarget
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.boundaryLabelGeometryTarget M

theorem target_of_explicitMatrices_via_boundaryAngleDirect
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.boundaryAngleDirect M

theorem target_of_explicitMatrices_via_boundaryAngleK23
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.boundaryAngleK23 M

theorem target_of_explicitMatrices_via_boundaryAngleCommonNeighbor
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.boundaryAngleCommonNeighbor M

theorem target_of_explicitMatrices_via_subpolygonDirect
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.subpolygonDirect M

theorem target_of_explicitMatrices_via_subpolygonTopologyDirect
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.subpolygonTopologyDirect M

theorem target_of_explicitMatrices_via_subpolygonTopologyK23
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.subpolygonTopologyK23 M

theorem target_of_explicitMatrices_via_subpolygonTopologyCommonNeighbor
    (M : ExplicitMatrices.{u}) :
    Target :=
  conditionalTargetProjections.subpolygonTopologyCommonNeighbor M

end

end TopologyBoundaryRouteSummaryFinalW11
end Swanepoel
end ErdosProblems1066
