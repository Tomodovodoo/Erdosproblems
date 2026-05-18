import ErdosProblems1066.Swanepoel.SwanepoelW11FinalAggregate
import ErdosProblems1066.Swanepoel.SwanepoelTargetFinalAggregateW11
import ErdosProblems1066.Swanepoel.TargetConsistencyFinalW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 Swanepoel route ledger

This terminal ledger records checked final W11 Swanepoel route data, the
explicit input-matrix ledgers still visible at this layer, and only
matrix-indexed target projections.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelRouteLedgerFinalW11

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

/-! ## Explicit input matrices -/

abbrev TargetAggregateCoreInputMatrices :=
  SwanepoelTargetFinalAggregateW11.CoreInputMatrices

abbrev TargetAggregateFinalBranchInputMatrices :=
  SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices

abbrev TargetAggregateExplicitInputMatrices :=
  SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices

/-- Stable explicit input ledgers from the final W11 Swanepoel files. -/
structure ExplicitInputMatrixLedger : Type (u + 3) where
  swanepoelAggregate :
    SwanepoelW11FinalAggregate.ExplicitInputMatrices.{u}
  targetConsistency :
    TargetConsistencyFinalW11.RequiredInputMatrices.{u}
  finalConsistencyOmissions :
    SwanepoelW11FinalConsistency.KnownImportOmissions

/-- The checked explicit input ledger. -/
def explicitInputMatrixLedger :
    ExplicitInputMatrixLedger.{u} where
  swanepoelAggregate := SwanepoelW11FinalAggregate.explicitInputMatrices
  targetConsistency := TargetConsistencyFinalW11.requiredInputMatrices
  finalConsistencyOmissions := SwanepoelW11FinalConsistency.knownImportOmissions

/-! ## Checked final route ledger -/

/-- Stable checked final matrices and input ledgers. -/
structure Matrix : Type (u + 3) where
  swanepoelAggregate :
    SwanepoelW11FinalAggregate.Matrix.{u}
  targetConsistency :
    TargetConsistencyFinalW11.Matrix.{u}
  inputs :
    ExplicitInputMatrixLedger.{u}
  omissions :
    SwanepoelW11FinalConsistency.KnownImportOmissions

/-- The final checked Swanepoel route ledger. -/
def matrix : Matrix.{u} where
  swanepoelAggregate := SwanepoelW11FinalAggregate.matrix
  targetConsistency := TargetConsistencyFinalW11.matrix
  inputs := explicitInputMatrixLedger
  omissions := SwanepoelW11FinalConsistency.knownImportOmissions

theorem checked_swanepoelAggregate :
    matrix.swanepoelAggregate = SwanepoelW11FinalAggregate.matrix := by
  rfl

theorem checked_targetConsistency :
    matrix.targetConsistency = TargetConsistencyFinalW11.matrix := by
  rfl

theorem checked_topologyIntegratedW11_omission :
    matrix.omissions.topologyIntegratedW11 =
      SwanepoelW11FinalConsistency.knownImportOmissions.topologyIntegratedW11 := by
  rfl

/-! ## Target-aggregate conditional projections -/

theorem target_of_core_directFields
    (M : TargetAggregateCoreInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_directFields M

theorem target_of_core_k23Fields
    (M : TargetAggregateCoreInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_k23Fields M

theorem target_of_core_commonNeighborFields
    (M : TargetAggregateCoreInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborFields M

theorem target_of_core_noEarlyRows
    (M : TargetAggregateCoreInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_noEarlyRows M

theorem target_of_core_noStartRows
    (M : TargetAggregateCoreInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_noStartRows M

theorem target_of_core_directGeometry
    (M : TargetAggregateCoreInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_directGeometry M

theorem target_of_core_k23Geometry
    (M : TargetAggregateCoreInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_k23Geometry M

theorem target_of_core_commonNeighborGeometry
    (M : TargetAggregateCoreInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborGeometry M

theorem target_of_core_k23Integrated
    (M : TargetAggregateCoreInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_k23Integrated M

theorem target_of_core_commonNeighborIntegrated
    (M : TargetAggregateCoreInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborIntegrated M

theorem target_of_finalBranches_k23Final
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_k23Final M

theorem target_of_finalBranches_commonNeighborFinal
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_k23Final_commonNeighbor M

theorem target_of_finalBranches_noEarlyFinal
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_noEarlyFinal M

theorem target_of_finalBranches_noStartFinal
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_noStartFinal M

theorem target_of_finalBranches_boundaryLabel
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryLabel M

theorem target_of_finalBranches_boundaryLabelNoEarlyTarget
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryLabel_noEarlyTarget M

theorem target_of_finalBranches_boundaryLabelGeometry
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryLabel_geometry M

theorem target_of_finalBranches_boundaryLabelGeometryTarget
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryLabel_geometryTarget M

theorem target_of_finalBranches_geometryTargetDirect
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_geometryTarget_direct M

theorem target_of_finalBranches_geometryTargetK23
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_geometryTarget_k23 M

theorem target_of_finalBranches_geometryTargetCommonNeighbor
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_geometryTarget_commonNeighbor M

theorem target_of_finalBranches_boundaryAngleDirect
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_direct M

theorem target_of_finalBranches_boundaryAngleK23
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_k23 M

theorem target_of_finalBranches_boundaryAngleCommonNeighbor
    (M : TargetAggregateFinalBranchInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_commonNeighbor M

theorem target_of_all_core_directFields
    (M : TargetAggregateExplicitInputMatrices) :
    Target :=
  target_of_core_directFields M.core

theorem target_of_all_k23Final
    (M : TargetAggregateExplicitInputMatrices) :
    Target :=
  target_of_finalBranches_k23Final M.finalBranches

theorem target_of_all_boundaryLabel
    (M : TargetAggregateExplicitInputMatrices) :
    Target :=
  target_of_finalBranches_boundaryLabel M.finalBranches

/-! ## Swanepoel-aggregate conditional projections -/

theorem target_of_boundaryLabelFinalMatrix
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_boundaryLabelFinalMatrix M

theorem target_of_boundaryLabelFinalMatrix_via_noEarlyFinal
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_boundaryLabelFinalMatrix_via_noEarlyFinal
    M

theorem target_of_boundaryLabelFinalMatrix_via_geometryTarget
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_boundaryLabelFinalMatrix_via_geometryTarget
    M

theorem target_of_noEarlyTargetFinalMatrix_via_noEarly
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_noEarlyTargetFinalMatrix_via_noEarly
    M

theorem target_of_noEarlyTargetFinalMatrix_via_noStart
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_noEarlyTargetFinalMatrix_via_noStart
    M

theorem target_of_noEarlyTargetFinalMatrix_via_explicitNoEarly
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_noEarlyTargetFinalMatrix_via_explicitNoEarly
    M

theorem target_of_geometryDirectFinalMatrix
    (M : GeometryFinalIntegratedW11.DirectFinalGeometryMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_geometryDirectFinalMatrix M

theorem target_of_geometryK23FinalMatrix
    (M : GeometryFinalIntegratedW11.K23FinalGeometryMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_geometryK23FinalMatrix M

theorem target_of_geometryCommonNeighborFinalMatrix
    (M : GeometryFinalIntegratedW11.CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_geometryCommonNeighborFinalMatrix M

theorem target_of_brokenLatticeDirectFieldMatrix
    (M : BrokenLatticeFinalIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_brokenLatticeDirectFieldMatrix M

theorem target_of_brokenLatticeK23FieldMatrix
    (M : BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_brokenLatticeK23FieldMatrix M

theorem target_of_brokenLatticeCommonNeighborFieldMatrix
    (M : BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_brokenLatticeCommonNeighborFieldMatrix
    M

theorem target_of_k23BrokenLatticeFields_via_direct
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_direct M

theorem target_of_k23BrokenLatticeFields_via_k23Final
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_k23Final
    M

theorem target_of_k23BrokenLatticeFields_via_commonNeighborFinal
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_commonNeighborFinal
    M

/-! ## Target-consistency conditional projections -/

theorem target_of_targetConsistency_boundaryLabelIntegratedMatrix
    (M : BoundaryLabelIntegratedW11.Matrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_boundaryLabelIntegratedMatrix M

theorem target_of_targetConsistency_explicitNoEarlyMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_explicitNoEarlyMatrix M

theorem target_of_targetConsistency_explicitNoStartMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_explicitNoStartMatrix M

theorem target_of_targetConsistency_noStartNoEarlyMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_noStartNoEarlyTargetMatrix M

theorem target_of_targetConsistency_geometryDirectTargetMatrix
    (M : GeometryTargetIntegratedW11.DirectTargetMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_geometryDirectTargetMatrix M

theorem target_of_targetConsistency_k23ExplicitTargetMatrix
    (M : K23TargetIntegratedW11.K23TargetMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_k23ExplicitTargetMatrix M

end

end SwanepoelRouteLedgerFinalW11
end Swanepoel
end ErdosProblems1066
