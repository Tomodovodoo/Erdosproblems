import ErdosProblems1066.Swanepoel.SwanepoelRouteSummaryFinalW11
import ErdosProblems1066.Swanepoel.SwanepoelFinalRouteSummaryW11
import ErdosProblems1066.Swanepoel.SwanepoelRouteLedgerFinalW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalAggregate
import ErdosProblems1066.Swanepoel.SwanepoelTargetFinalAggregateW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 Swanepoel checked summary

This terminal ledger gathers the final W11 Swanepoel summaries present in this
tree.  It records the remaining input matrix types and exports only projections
whose matrix inputs are explicit arguments.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelFinalCheckedSummaryW11

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

/-! ## Checked summary sources -/

/-- Names of the checked summaries imported by this file. -/
structure CheckedSummarySources where
  routeSummaryFinalW11 : True
  finalRouteSummaryW11 : True
  routeLedgerFinalW11 : True
  w11FinalAggregate : True
  targetFinalAggregateW11 : True

/-- The available final W11 summaries used by this ledger. -/
def checkedSummarySources : CheckedSummarySources where
  routeSummaryFinalW11 := True.intro
  finalRouteSummaryW11 := True.intro
  routeLedgerFinalW11 := True.intro
  w11FinalAggregate := True.intro
  targetFinalAggregateW11 := True.intro

/-! ## Explicit input matrix types -/

/-- Type-level ledger of all input matrices named by the final checked
summary. -/
structure ExplicitInputMatrixTypes where
  targetAggregateCore : Type _
  targetAggregateFinalBranches : Type _
  targetAggregateAll : Type _
  geometryDirectFinal : Type _
  geometryK23Final : Type _
  geometryCommonNeighborFinal : Type _
  k23Final : Type _
  boundaryAngleFinal : Type _
  boundaryLabelFinal : Type _
  noEarlyTargetFinal : Type _
  subpolygonFinal : Type _
  targetBoundaryLabelIntegrated : Type _
  targetExplicitNoEarly : Type _
  targetGeometryDirect : Type _
  targetK23Explicit : Type _
  brokenLatticeDirect : Type _
  brokenLatticeK23 : Type _
  brokenLatticeCommonNeighbor : Type _
  k23BrokenLatticeFields : Type _
  finalRouteSummaryRequired : Type _
  finalRouteSummaryAggregate : Type _
  routeLedgerExplicit : Type _

/-- The explicit input matrix surfaces for the projections below. -/
def explicitInputMatrixTypes : ExplicitInputMatrixTypes where
  targetAggregateCore :=
    SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}
  targetAggregateFinalBranches :=
    SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}
  targetAggregateAll :=
    SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices.{u}
  geometryDirectFinal :=
    GeometryFinalIntegratedW11.DirectFinalGeometryMatrix.{u}
  geometryK23Final :=
    GeometryFinalIntegratedW11.K23FinalGeometryMatrix.{u}
  geometryCommonNeighborFinal :=
    GeometryFinalIntegratedW11.CommonNeighborFinalGeometryMatrix.{u}
  k23Final :=
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u}
  boundaryAngleFinal :=
    BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.{u}
  boundaryLabelFinal :=
    BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}
  noEarlyTargetFinal :=
    NoEarlyTargetFinalW11.FinalMatrixInput.{u}
  subpolygonFinal :=
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}
  targetBoundaryLabelIntegrated :=
    BoundaryLabelIntegratedW11.Matrix.{u}
  targetExplicitNoEarly :=
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}
  targetGeometryDirect :=
    GeometryTargetIntegratedW11.DirectTargetMatrix.{u}
  targetK23Explicit :=
    K23TargetIntegratedW11.K23TargetMatrix.{u}
  brokenLatticeDirect :=
    BrokenLatticeFinalIntegratedW11.DirectFieldMatrix.{u}
  brokenLatticeK23 :=
    BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u}
  brokenLatticeCommonNeighbor :=
    BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u}
  k23BrokenLatticeFields :=
    K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}
  finalRouteSummaryRequired :=
    SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}
  finalRouteSummaryAggregate :=
    SwanepoelFinalRouteSummaryW11.FinalAggregateMatrices.{u}
  routeLedgerExplicit :=
    SwanepoelRouteLedgerFinalW11.ExplicitInputMatrixLedger.{u}

/-- Compact top-level ledger: checked sources plus explicit input matrix
types. -/
structure Matrix where
  sources : CheckedSummarySources
  inputTypes : ExplicitInputMatrixTypes

/-- The final checked W11 summary ledger. -/
def matrix : Matrix where
  sources := checkedSummarySources
  inputTypes := explicitInputMatrixTypes

/-! ## Target aggregate projections -/

theorem target_of_targetAggregate_core_direct
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetAggregate_core_direct M

theorem target_of_targetAggregate_core_k23
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetAggregate_core_k23 M

theorem target_of_targetAggregate_core_commonNeighbor
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetAggregate_core_commonNeighbor
    M

theorem target_of_targetAggregate_core_noEarlyRows
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_noEarlyRows M

theorem target_of_targetAggregate_core_noStartRows
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_noStartRows M

theorem target_of_targetAggregate_core_directGeometry
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_directGeometry M

theorem target_of_targetAggregate_core_k23Geometry
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_k23Geometry M

theorem target_of_targetAggregate_core_commonNeighborGeometry
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborGeometry M

theorem target_of_targetAggregate_core_k23Integrated
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_k23Integrated M

theorem target_of_targetAggregate_core_commonNeighborIntegrated
    (M : SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborIntegrated
    M

theorem target_of_targetAggregate_final_k23
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_k23Final M

theorem target_of_targetAggregate_final_commonNeighbor
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_k23Final_commonNeighbor M

theorem target_of_targetAggregate_final_noEarly
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_noEarlyFinal M

theorem target_of_targetAggregate_final_noStart
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_noStartFinal M

theorem target_of_targetAggregate_final_boundaryLabel
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetAggregate_final_boundaryLabel
    M

theorem target_of_targetAggregate_final_boundaryAngleDirect
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetAggregate_final_boundaryAngleDirect
    M

theorem target_of_targetAggregate_final_boundaryAngleK23
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetAggregate_final_boundaryAngleK23
    M

theorem target_of_targetAggregate_final_boundaryAngleCommonNeighbor
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetAggregate_final_boundaryAngleCommonNeighbor
    M

theorem target_of_targetAggregate_all_coreDirect
    (M : SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_all_core_direct M

theorem target_of_targetAggregate_all_k23Final
    (M : SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_all_k23Final M

theorem target_of_targetAggregate_all_boundaryLabel
    (M : SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_all_boundaryLabel M

/-! ## Final route-summary projections -/

theorem target_of_finalRouteSummary_verifiedDirectField
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_verified_directField M

theorem target_of_finalRouteSummary_verifiedNoEarlyFinal
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_verified_noEarlyFinal M

theorem target_of_finalRouteSummary_finalAggregateBoundaryLabel
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_finalAggregate_boundaryLabel
    M

theorem target_of_finalRouteSummary_finalAggregateNoEarly
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_finalAggregate_noEarly M

theorem target_of_finalRouteSummary_finalAggregateGeometryDirect
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_finalAggregate_geometryDirect
    M

theorem target_of_finalRouteSummary_finalAggregateBrokenLatticeDirect
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_finalAggregate_brokenLatticeDirect
    M

theorem target_of_finalRouteSummary_targetAggregateCoreDirect
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_targetAggregate_coreDirect M

theorem target_of_finalRouteSummary_targetAggregateK23Final
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_targetAggregate_k23Final M

theorem target_of_finalRouteSummary_targetAggregateBoundaryAngleDirect
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_targetAggregate_boundaryAngleDirect
    M

theorem target_of_finalRouteSummary_targetAggregateAllCoreDirect
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_targetAggregate_allCoreDirect
    M

theorem target_of_finalRouteSummary_boundaryAngleDirect
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_boundaryAngle_direct M

theorem target_of_finalRouteSummary_boundaryAngleTargetConsistencyDirect
    (M : SwanepoelFinalRouteSummaryW11.RequiredMatrices.{u}) :
    Target :=
  SwanepoelFinalRouteSummaryW11.target_via_boundaryAngle_targetConsistencyDirect
    M

/-! ## Final route-ledger projections -/

theorem target_of_routeLedger_coreDirectFields
    (M : SwanepoelRouteLedgerFinalW11.TargetAggregateCoreInputMatrices.{u}) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_core_directFields M

theorem target_of_routeLedger_finalBranchesBoundaryLabel
    (M :
      SwanepoelRouteLedgerFinalW11.TargetAggregateFinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_finalBranches_boundaryLabel M

theorem target_of_routeLedger_allCoreDirectFields
    (M : SwanepoelRouteLedgerFinalW11.TargetAggregateExplicitInputMatrices.{u}) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_all_core_directFields M

theorem target_of_routeLedger_allK23Final
    (M : SwanepoelRouteLedgerFinalW11.TargetAggregateExplicitInputMatrices.{u}) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_all_k23Final M

theorem target_of_routeLedger_targetConsistencyExplicitNoStart
    (M : NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_targetConsistency_explicitNoStartMatrix
    M

theorem target_of_routeLedger_targetConsistencyNoStartNoEarly
    (M : NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u}) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_targetConsistency_noStartNoEarlyMatrix
    M

/-! ## Final route-summary projections -/

theorem target_of_geometryDirectFinalMatrix
    (M : GeometryFinalIntegratedW11.DirectFinalGeometryMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_geometryDirectFinalMatrix M

theorem target_of_geometryK23FinalMatrix
    (M : GeometryFinalIntegratedW11.K23FinalGeometryMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_geometryK23FinalMatrix M

theorem target_of_geometryCommonNeighborFinalMatrix
    (M : GeometryFinalIntegratedW11.CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_geometryCommonNeighborFinalMatrix
    M

theorem target_of_k23FinalMatrix
    (M : K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_k23FinalMatrix_via_k23 M

theorem target_of_commonNeighborFinalMatrix
    (M : K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_k23FinalMatrix_via_commonNeighbor
    M

theorem target_of_boundaryAngleFinalMatrix_direct
    (M : BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_boundaryAngleFinalMatrix_via_direct
    M

theorem target_of_boundaryAngleFinalMatrix_k23
    (M : BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_boundaryAngleFinalMatrix_via_k23
    M

theorem target_of_boundaryAngleFinalMatrix_commonNeighbor
    (M : BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_boundaryAngleFinalMatrix_via_commonNeighbor
    M

theorem target_of_boundaryLabelFinalMatrix
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_boundaryLabelFinalMatrix M

theorem target_of_boundaryLabelFinalMatrix_noEarly
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_boundaryLabelFinalMatrix_via_noEarlyFinal
    M

theorem target_of_boundaryLabelFinalMatrix_geometry
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_boundaryLabelFinalMatrix_via_geometryTarget
    M

theorem target_of_noEarlyTargetFinalMatrix_noEarly
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_noEarlyTargetFinalMatrix_via_noEarly
    M

theorem target_of_noEarlyTargetFinalMatrix_noStart
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_noEarlyTargetFinalMatrix_via_noStart
    M

theorem target_of_noEarlyTargetFinalMatrix_explicitNoEarly
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_noEarlyTargetFinalMatrix_via_explicitNoEarly
    M

theorem target_of_noEarlyTargetFinalMatrix_explicitNoStart
    (M : NoEarlyTargetFinalW11.FinalMatrixInput.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_noEarlyTargetFinalMatrix_via_explicitNoStart
    M

theorem target_of_subpolygonFinalMatrix_direct
    (M : SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_subpolygonFinalMatrix_via_direct
    M

theorem target_of_subpolygonFinalMatrix_k23
    (M : SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_subpolygonFinalMatrix_via_k23
    M

theorem target_of_subpolygonFinalMatrix_commonNeighbor
    (M : SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_subpolygonFinalMatrix_via_commonNeighbor
    M

theorem target_of_targetConsistency_boundaryLabelIntegratedMatrix
    (M : BoundaryLabelIntegratedW11.Matrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetConsistency_boundaryLabelIntegratedMatrix
    M

theorem target_of_targetConsistency_explicitNoEarlyMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetConsistency_explicitNoEarlyMatrix
    M

theorem target_of_targetConsistency_geometryDirectTargetMatrix
    (M : GeometryTargetIntegratedW11.DirectTargetMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetConsistency_geometryDirectTargetMatrix
    M

theorem target_of_targetConsistency_k23ExplicitTargetMatrix
    (M : K23TargetIntegratedW11.K23TargetMatrix.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_targetConsistency_k23ExplicitTargetMatrix
    M

/-! ## Final aggregate projections -/

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

theorem target_of_k23BrokenLatticeFields_direct
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_direct M

theorem target_of_k23BrokenLatticeFields_k23Final
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_k23Final
    M

theorem target_of_k23BrokenLatticeFields_commonNeighborFinal
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_commonNeighborFinal
    M

theorem target_of_k23BrokenLatticeFields_k23BrokenLattice
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_k23BrokenLattice
    M

theorem target_of_k23BrokenLatticeFields_commonNeighborBrokenLattice
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_commonNeighborBrokenLattice
    M

theorem target_of_k23BrokenLatticeFields_k23TargetClosure
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_k23TargetClosure
    M

theorem target_of_k23BrokenLatticeFields_commonNeighborTargetClosure
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_commonNeighborTargetClosure
    M

theorem target_of_k23BrokenLatticeFields_k23Geometry
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_k23Geometry
    M

theorem target_of_k23BrokenLatticeFields_commonNeighborGeometry
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_commonNeighborGeometry
    M

end

end SwanepoelFinalCheckedSummaryW11
end Swanepoel
end ErdosProblems1066
