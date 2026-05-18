import ErdosProblems1066.Swanepoel.SwanepoelTargetFinalAggregateW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency
import ErdosProblems1066.Swanepoel.TargetConsistencyFinalW11
import ErdosProblems1066.Swanepoel.GeometryFinalIntegratedW11
import ErdosProblems1066.Swanepoel.K23FinalIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryAngleFinalIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryLabelFinalIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyTargetFinalW11
import ErdosProblems1066.Swanepoel.SubpolygonFinalIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 Swanepoel route summary

This file is a compact terminal summary for the checked W11 Swanepoel route
ledgers.  It records the imported matrices, displays the remaining input
matrix surfaces, and exposes only conditional target projections from supplied
input matrices.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelRouteSummaryFinalW11

universe u

noncomputable section

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

/-! ## Imported checked matrices -/

/-- Checked final W11 ledgers summarized by this file. -/
structure CheckedMatrices where
  targetFinalAggregate :
    SwanepoelTargetFinalAggregateW11.Matrix.{u}
  finalConsistency :
    SwanepoelW11FinalConsistency.Matrix.{u}
  targetConsistency :
    TargetConsistencyFinalW11.Matrix.{u}
  geometryFinal :
    GeometryFinalIntegratedW11.Matrix.{u}
  k23Final :
    K23FinalIntegratedW11.Matrix.{u}
  boundaryAngleFinal :
    BoundaryAngleFinalIntegratedW11.Matrix.{u}
  boundaryLabelFinal :
    BoundaryLabelFinalIntegratedW11.Matrix.{u}
  noEarlyTargetFinal :
    NoEarlyTargetFinalW11.Matrix.{u}
  subpolygonFinal :
    SubpolygonFinalIntegratedW11.Matrix.{u}

/-- Imported checked W11 matrices. -/
def checkedMatrices : CheckedMatrices where
  targetFinalAggregate := SwanepoelTargetFinalAggregateW11.matrix
  finalConsistency := SwanepoelW11FinalConsistency.matrix
  targetConsistency := TargetConsistencyFinalW11.matrix
  geometryFinal := GeometryFinalIntegratedW11.matrix
  k23Final := K23FinalIntegratedW11.matrix
  boundaryAngleFinal := BoundaryAngleFinalIntegratedW11.matrix
  boundaryLabelFinal := BoundaryLabelFinalIntegratedW11.matrix
  noEarlyTargetFinal := NoEarlyTargetFinalW11.matrix
  subpolygonFinal := SubpolygonFinalIntegratedW11.matrix

/-! ## Explicit input matrix surfaces -/

/-- All input matrix surfaces named by the final route summary. -/
structure ExplicitInputMatrices where
  targetAggregateTypes :
    SwanepoelTargetFinalAggregateW11.ExplicitInputMatrixTypes
  targetAggregateCore :
    Type _
  targetAggregateFinalBranches :
    Type _
  targetAggregateAll :
    Type _
  targetConsistency :
    TargetConsistencyFinalW11.RequiredInputMatrices.{u}
  finalConsistencyPackages :
    SwanepoelW11FinalConsistency.ExplicitPackageRouteLedger.{u}
  geometryFinal :
    GeometryFinalIntegratedW11.ExplicitGeometryFieldLedger.{u}
  geometryDirect :
    Type (u + 1)
  geometryK23 :
    Type (u + 1)
  geometryCommonNeighbor :
    Type (u + 1)
  geometryAllBranches :
    Type (u + 1)
  k23Final :
    Type (u + 1)
  boundaryAngleFinal :
    Type (u + 1)
  boundaryLabelFinal :
    BoundaryLabelFinalIntegratedW11.ExplicitBoundaryLabelInputLedger.{u}
  boundaryLabelUniform :
    Type (u + 1)
  noEarlyTargetFinal :
    NoEarlyTargetFinalW11.ExplicitInputLedger.{u}
  noEarlyTargetUniform :
    Type (u + 1)
  subpolygonFinal :
    Type (u + 1)

/-- Displayed input matrix surfaces for every conditional route below. -/
def explicitInputMatrices : ExplicitInputMatrices where
  targetAggregateTypes :=
    SwanepoelTargetFinalAggregateW11.explicitInputMatrixTypes
  targetAggregateCore :=
    SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}
  targetAggregateFinalBranches :=
    SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}
  targetAggregateAll :=
    SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices.{u}
  targetConsistency := TargetConsistencyFinalW11.requiredInputMatrices
  finalConsistencyPackages :=
    SwanepoelW11FinalConsistency.explicitPackageRouteLedger
  geometryFinal := GeometryFinalIntegratedW11.explicitGeometryFieldLedger
  geometryDirect := GeometryFinalIntegratedW11.DirectFinalGeometryMatrix.{u}
  geometryK23 := GeometryFinalIntegratedW11.K23FinalGeometryMatrix.{u}
  geometryCommonNeighbor :=
    GeometryFinalIntegratedW11.CommonNeighborFinalGeometryMatrix.{u}
  geometryAllBranches := GeometryFinalIntegratedW11.ExplicitGeometryMatrices.{u}
  k23Final := K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u}
  boundaryAngleFinal := BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.{u}
  boundaryLabelFinal :=
    BoundaryLabelFinalIntegratedW11.explicitBoundaryLabelInputLedger
  boundaryLabelUniform :=
    BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}
  noEarlyTargetFinal := NoEarlyTargetFinalW11.explicitInputLedger
  noEarlyTargetUniform := NoEarlyTargetFinalW11.FinalMatrixInput.{u}
  subpolygonFinal := SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}

/-! ## Conditional route ledgers -/

/-- Conditional K23/common-neighbor projections from the final K23 matrix. -/
structure K23FinalProjectionRoutes : Type (u + 1) where
  k23 :
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u} -> Target
  commonNeighbor :
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u} -> Target
  k23TargetClosure :
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u} -> Target
  commonNeighborTargetClosure :
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u} -> Target
  k23Geometry :
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u} -> Target
  commonNeighborGeometry :
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u} -> Target

/-- Checked conditional projections from the final K23 ledger. -/
def k23FinalProjectionRoutes : K23FinalProjectionRoutes.{u} where
  k23 := K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix_via_k23
  commonNeighbor := K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix
  k23TargetClosure :=
    K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix_via_k23TargetClosure
  commonNeighborTargetClosure :=
    K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix_via_commonNeighborTargetClosure
  k23Geometry :=
    K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix_via_k23Geometry
  commonNeighborGeometry :=
    K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix_via_commonNeighborGeometry

/-- Conditional subpolygon projections from the final subpolygon matrix. -/
structure SubpolygonFinalProjectionRoutes : Type (u + 1) where
  direct :
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u} -> Target
  k23 :
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u} -> Target
  commonNeighbor :
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u} -> Target
  directGeometry :
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u} -> Target
  k23Geometry :
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u} -> Target
  commonNeighborGeometry :
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u} -> Target

/-- Checked conditional projections from the final subpolygon ledger. -/
def subpolygonFinalProjectionRoutes :
    SubpolygonFinalProjectionRoutes.{u} where
  direct :=
    SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_direct
  k23 := SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_k23
  commonNeighbor :=
    SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_commonNeighbor
  directGeometry :=
    SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_directGeometry
  k23Geometry :=
    SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_k23Geometry
  commonNeighborGeometry :=
    SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_commonNeighborGeometry

/-- Main conditional route ledgers retained by the final summary. -/
structure ConditionalRouteLedgers where
  targetFinalAggregate :
    SwanepoelTargetFinalAggregateW11.CheckedConditionalRoutes.{u}
  finalConsistency :
    SwanepoelW11FinalConsistency.ExplicitPackageRouteLedger.{u}
  targetConsistency :
    TargetConsistencyFinalW11.RequiredInputMatrices.{u}
  geometryFinal :
    GeometryFinalIntegratedW11.ConditionalSwanepoelTargetRoutes.{u}
  k23Final :
    K23FinalProjectionRoutes.{u}
  boundaryAngleFinal :
    BoundaryAngleFinalIntegratedW11.ConditionalSwanepoelTargetRoutes.{u}
  boundaryLabelFinal :
    BoundaryLabelFinalIntegratedW11.ConditionalSwanepoelTargetRoutes.{u}
  noEarlyTargetFinal :
    NoEarlyTargetFinalW11.ConditionalRoutes.{u}
  subpolygonFinal :
    SubpolygonFinalProjectionRoutes.{u}

/-- Checked route ledgers gathered by the final summary. -/
def conditionalRouteLedgers : ConditionalRouteLedgers where
  targetFinalAggregate :=
    SwanepoelTargetFinalAggregateW11.checkedConditionalRoutes
  finalConsistency := SwanepoelW11FinalConsistency.explicitPackageRouteLedger
  targetConsistency := TargetConsistencyFinalW11.requiredInputMatrices
  geometryFinal := GeometryFinalIntegratedW11.conditionalSwanepoelTargetRoutes
  k23Final := k23FinalProjectionRoutes
  boundaryAngleFinal :=
    BoundaryAngleFinalIntegratedW11.conditionalSwanepoelTargetRoutes
  boundaryLabelFinal :=
    BoundaryLabelFinalIntegratedW11.conditionalSwanepoelTargetRoutes
  noEarlyTargetFinal := NoEarlyTargetFinalW11.conditionalRoutes
  subpolygonFinal := subpolygonFinalProjectionRoutes

/-! ## Final summary matrix -/

/-- Final W11 Swanepoel route summary.

The matrix stores checked ledgers and explicit input surfaces.  It supplies no
target proof without one of those input matrices.
-/
structure Matrix where
  checked : CheckedMatrices
  inputs : ExplicitInputMatrices
  routes : ConditionalRouteLedgers

/-- The checked final W11 Swanepoel route summary matrix. -/
def matrix : Matrix where
  checked := checkedMatrices
  inputs := explicitInputMatrices
  routes := conditionalRouteLedgers

/-! ## Public conditional target projections -/

theorem target_of_targetAggregate_core_direct
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_directFields M

theorem target_of_targetAggregate_core_k23
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_k23Fields M

theorem target_of_targetAggregate_core_commonNeighbor
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborFields M

theorem target_of_targetAggregate_final_boundaryLabel
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryLabel M

theorem target_of_targetAggregate_final_boundaryAngleDirect
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_direct M

theorem target_of_targetAggregate_final_boundaryAngleK23
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_k23 M

theorem target_of_targetAggregate_final_boundaryAngleCommonNeighbor
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_commonNeighbor M

theorem target_of_geometryDirectFinalMatrix
    (M : GeometryFinalIntegratedW11.DirectFinalGeometryMatrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix
    M

theorem target_of_geometryK23FinalMatrix
    (M : GeometryFinalIntegratedW11.K23FinalGeometryMatrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix
    M

theorem target_of_geometryCommonNeighborFinalMatrix
    (M : GeometryFinalIntegratedW11.CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix
    M

theorem target_of_k23FinalMatrix_via_k23
    (M : K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix_via_k23
    M

theorem target_of_k23FinalMatrix_via_commonNeighbor
    (M : K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix M

theorem target_of_boundaryAngleFinalMatrix_via_direct
    (M : BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.{u}) :
    Target :=
  BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_direct M

theorem target_of_boundaryAngleFinalMatrix_via_k23
    (M : BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.{u}) :
    Target :=
  BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_k23 M

theorem target_of_boundaryAngleFinalMatrix_via_commonNeighbor
    (M : BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.{u}) :
    Target :=
  BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_commonNeighbor M

theorem target_of_boundaryLabelFinalMatrix
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix M

theorem target_of_boundaryLabelFinalMatrix_via_noEarlyFinal
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_noEarlyFinal
    M

theorem target_of_boundaryLabelFinalMatrix_via_geometryTarget
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_geometryTarget
    M

theorem target_of_noEarlyTargetFinalMatrix_via_noEarly
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_noEarly M

theorem target_of_noEarlyTargetFinalMatrix_via_noStart
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_noStart M

theorem target_of_noEarlyTargetFinalMatrix_via_explicitNoEarly
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_explicitNoEarly M

theorem target_of_noEarlyTargetFinalMatrix_via_explicitNoStart
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_explicitNoStart M

theorem target_of_subpolygonFinalMatrix_via_direct
    (M : SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_direct M

theorem target_of_subpolygonFinalMatrix_via_k23
    (M : SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_k23 M

theorem target_of_subpolygonFinalMatrix_via_commonNeighbor
    (M : SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_commonNeighbor
    M

theorem target_of_targetConsistency_boundaryLabelIntegratedMatrix
    (M : BoundaryLabelIntegratedW11.Matrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_boundaryLabelIntegratedMatrix M

theorem target_of_targetConsistency_explicitNoEarlyMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_explicitNoEarlyMatrix M

theorem target_of_targetConsistency_geometryDirectTargetMatrix
    (M : GeometryTargetIntegratedW11.DirectTargetMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_geometryDirectTargetMatrix M

theorem target_of_targetConsistency_k23ExplicitTargetMatrix
    (M : K23TargetIntegratedW11.K23TargetMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_k23ExplicitTargetMatrix M

end

end SwanepoelRouteSummaryFinalW11
end Swanepoel
end ErdosProblems1066
