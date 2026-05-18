import ErdosProblems1066.Swanepoel.BrokenLatticeFinalIntegratedW11
import ErdosProblems1066.Swanepoel.K23FinalIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyFinalIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryLabelTargetIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryAngleIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryTargetIntegratedW11
import ErdosProblems1066.Swanepoel.TargetLedgerConsistencyW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# Final W11 Swanepoel target aggregate

This module is a terminal ledger for the checked W11 conditional target
routes.  It gathers the final branch ledgers, records the remaining input
matrix surfaces as fields, and exposes only conditional target projections.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelTargetFinalAggregateW11

universe u v

noncomputable section

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

abbrev TargetRoute (alpha : Sort v) : Sort (max 1 v) :=
  TargetIntegratedMatrixW11.TargetRoute alpha

abbrev EliminatorTargetRoute (alpha : Type v) : Type v :=
  TargetIntegratedMatrixW11.EliminatorTargetRoute alpha

/-! ## Explicit input matrix surfaces -/

/-- Source-facing matrices used by the checked target routes. -/
structure CoreInputMatrices where
  directFields :
    BrokenLatticeFinalIntegratedW11.DirectFieldMatrix.{u}
  k23Fields :
    BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u}
  commonNeighborFields :
    BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u}
  noEarlyRows :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}
  noStartRows :
    WindowNoEarlyRowsW11.NoStartMatrix.{u, u}
  directGeometry :
    GeometryIntegratedW11.DirectGeometryMatrix.{u}
  k23Geometry :
    GeometryIntegratedW11.K23GeometryMatrix.{u}
  commonNeighborGeometry :
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u}
  k23Integrated :
    K23IntegratedMatrixW11.K23IntegratedMatrix.{u}
  commonNeighborIntegrated :
    K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u}
  prefixNoEarly :
    NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}
  prefixNoStart :
    NoEarlyIntegratedW11.PrefixNoStartMatrix.{u}

/-- Final branch matrices whose rows keep all branch-specific inputs visible. -/
structure FinalBranchInputMatrices where
  k23Final :
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u}
  noStartNoEarlyFinal :
    NoEarlyFinalIntegratedW11.FinalNoStartNoEarlyMatrix.{u, u}
  boundaryLabelTarget :
    BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetMatrix.{u}
  geometryTargetDirect :
    GeometryTargetIntegratedW11.DirectTargetMatrix.{u}
  geometryTargetK23 :
    GeometryTargetIntegratedW11.K23TargetMatrix.{u}
  geometryTargetCommonNeighbor :
    GeometryTargetIntegratedW11.CommonNeighborTargetMatrix.{u}
  boundaryAngleDirect :
    BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u}
  boundaryAngleK23 :
    BoundaryAngleIntegratedW11.K23GeometryMatrix.{u}
  boundaryAngleCommonNeighbor :
    BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u}

/-- All input matrix surfaces named by the final aggregate. -/
structure ExplicitInputMatrices where
  core : CoreInputMatrices
  finalBranches : FinalBranchInputMatrices

/-- The types of all matrix surfaces, recorded without constructing rows. -/
structure ExplicitInputMatrixTypes where
  core : Type _
  finalBranches : Type _
  all : Type _

/-- Type-level ledger for the still-external inputs. -/
def explicitInputMatrixTypes : ExplicitInputMatrixTypes where
  core := CoreInputMatrices
  finalBranches := FinalBranchInputMatrices
  all := ExplicitInputMatrices

/-! ## Boundary-angle target routes -/

/-- Boundary-angle direct rows routed through the integrated geometry target. -/
def boundaryAngleDirectTargetRoute :
    TargetRoute
      (BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u}) where
  noMinimal :=
    BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_directGeometryMatrix
  pipeline :=
    BoundaryAngleIntegratedW11.pipelineCleared_of_directGeometryMatrix
  target := fun M =>
    GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
      M.toGeometryIntegratedMatrix

/-- Boundary-angle K23 rows routed through the integrated geometry target. -/
def boundaryAngleK23TargetRoute :
    TargetRoute
      (BoundaryAngleIntegratedW11.K23GeometryMatrix.{u}) where
  noMinimal :=
    BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_k23GeometryMatrix
  pipeline :=
    BoundaryAngleIntegratedW11.pipelineCleared_of_k23GeometryMatrix
  target := fun M =>
    GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
      M.toGeometryIntegratedMatrix

/-- Boundary-angle common-neighbor rows routed through the integrated geometry
target. -/
def boundaryAngleCommonNeighborTargetRoute :
    TargetRoute
      (BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u}) where
  noMinimal :=
    BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_commonNeighborGeometryMatrix
  pipeline :=
    BoundaryAngleIntegratedW11.pipelineCleared_of_commonNeighborGeometryMatrix
  target := fun M =>
    GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
      M.toGeometryIntegratedMatrix

/-! ## Imported final ledgers -/

/-- Checked ledgers gathered by this terminal aggregate. -/
structure ImportedFinalLedgers where
  brokenLatticeFinal :
    BrokenLatticeFinalIntegratedW11.Matrix.{u}
  k23Final :
    K23FinalIntegratedW11.Matrix.{u}
  noEarlyFinal :
    NoEarlyFinalIntegratedW11.Matrix.{u}
  boundaryLabelTarget :
    BoundaryLabelTargetIntegratedW11.Matrix.{u}
  boundaryAngleIntegrated :
    BoundaryAngleIntegratedW11.Matrix.{u}
  geometryIntegrated :
    GeometryIntegratedW11.Matrix.{u}
  geometryTargetIntegrated :
    GeometryTargetIntegratedW11.Matrix.{u}
  targetLedgerConsistency :
    TargetLedgerConsistencyW11.Matrix.{u}

/-- Imported checked ledgers, with absent final wrappers replaced by the
checked integrated ledgers present in this tree. -/
def importedFinalLedgers : ImportedFinalLedgers where
  brokenLatticeFinal := BrokenLatticeFinalIntegratedW11.matrix
  k23Final := K23FinalIntegratedW11.matrix
  noEarlyFinal := NoEarlyFinalIntegratedW11.matrix
  boundaryLabelTarget := BoundaryLabelTargetIntegratedW11.matrix
  boundaryAngleIntegrated := BoundaryAngleIntegratedW11.matrix
  geometryIntegrated := GeometryIntegratedW11.matrix
  geometryTargetIntegrated := GeometryTargetIntegratedW11.matrix
  targetLedgerConsistency := TargetLedgerConsistencyW11.matrix

/-! ## Route ledger -/

/-- Final K23/common-neighbor route rows. -/
structure K23FinalRoutes where
  k23Integrated :
    EliminatorTargetRoute
      (K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u})
  commonNeighborIntegrated :
    EliminatorTargetRoute
      (K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u})
  k23TargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u})
  commonNeighborTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u})
  k23Geometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u})
  commonNeighborGeometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u})

/-- Checked K23/common-neighbor rows from the final K23 ledger. -/
def k23FinalRoutes : K23FinalRoutes where
  k23Integrated := K23FinalIntegratedW11.k23FinalIntegratedRoute
  commonNeighborIntegrated :=
    K23FinalIntegratedW11.commonNeighborFinalIntegratedRoute
  k23TargetClosure := K23FinalIntegratedW11.k23FinalTargetClosureRow
  commonNeighborTargetClosure :=
    K23FinalIntegratedW11.commonNeighborFinalTargetClosureRow
  k23Geometry := K23FinalIntegratedW11.k23FinalGeometryProjectionRow
  commonNeighborGeometry :=
    K23FinalIntegratedW11.commonNeighborFinalGeometryProjectionRow

/-- Final no-start/no-early route rows. -/
structure NoEarlyFinalRoutes where
  targetNoEarly :
    TargetRoute
      (NoEarlyFinalIntegratedW11.FinalNoStartNoEarlyMatrix.{u})
  targetNoStart :
    TargetRoute
      (NoEarlyFinalIntegratedW11.FinalNoStartNoEarlyMatrix.{u})
  swanepoelNoEarly :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (NoEarlyFinalIntegratedW11.FinalNoStartNoEarlyMatrix.{u})
  swanepoelNoStart :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (NoEarlyFinalIntegratedW11.FinalNoStartNoEarlyMatrix.{u})

/-- Checked no-start/no-early rows from the final no-early ledger. -/
def noEarlyFinalRoutes : NoEarlyFinalRoutes where
  targetNoEarly := NoEarlyFinalIntegratedW11.targetIntegratedNoEarlyRoute
  targetNoStart := NoEarlyFinalIntegratedW11.targetIntegratedNoStartRoute
  swanepoelNoEarly := NoEarlyFinalIntegratedW11.swanepoelNoEarlyRoute
  swanepoelNoStart := NoEarlyFinalIntegratedW11.swanepoelNoStartRoute

/-- Final boundary-label target route rows. -/
structure BoundaryLabelFinalRoutes where
  targetIntegrated :
    EliminatorTargetRoute
      (BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetMatrix.{u})
  targetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetMatrix.{u})
  noEarlyTarget :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetMatrix.{u})
  geometryTarget :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetMatrix.{u})
  w11NoEarly :
    TargetRoute
      (BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetMatrix.{u})
  geometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetMatrix.{u})

/-- Checked boundary-label rows from the target-facing boundary-label ledger. -/
def boundaryLabelFinalRoutes : BoundaryLabelFinalRoutes where
  targetIntegrated :=
    BoundaryLabelTargetIntegratedW11.boundaryLabelTargetIntegratedRoute
  targetClosure :=
    BoundaryLabelTargetIntegratedW11.boundaryLabelTargetClosureRow
  noEarlyTarget :=
    BoundaryLabelTargetIntegratedW11.boundaryLabelNoEarlyTargetRow
  geometryTarget :=
    BoundaryLabelTargetIntegratedW11.boundaryLabelGeometryTargetRow
  w11NoEarly :=
    BoundaryLabelTargetIntegratedW11.boundaryLabelW11NoEarlyRow
  geometry :=
    BoundaryLabelTargetIntegratedW11.boundaryLabelGeometryProjectionRow

/-- Target-facing geometry route rows. -/
structure GeometryTargetFinalRoutes where
  direct :
    EliminatorTargetRoute
      (GeometryTargetIntegratedW11.DirectTargetMatrix.{u})
  k23 :
    EliminatorTargetRoute
      (GeometryTargetIntegratedW11.K23TargetMatrix.{u})
  commonNeighbor :
    EliminatorTargetRoute
      (GeometryTargetIntegratedW11.CommonNeighborTargetMatrix.{u})

/-- Checked target-facing geometry rows. -/
def geometryTargetFinalRoutes : GeometryTargetFinalRoutes where
  direct := GeometryTargetIntegratedW11.directTargetIntegratedRoute
  k23 := GeometryTargetIntegratedW11.k23TargetIntegratedRoute
  commonNeighbor :=
    GeometryTargetIntegratedW11.commonNeighborTargetIntegratedRoute

/-- Boundary-angle rows after routing through the integrated geometry layer. -/
structure BoundaryAngleFinalRoutes where
  direct :
    TargetRoute
      (BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u})
  k23 :
    TargetRoute
      (BoundaryAngleIntegratedW11.K23GeometryMatrix.{u})
  commonNeighbor :
    TargetRoute
      (BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u})

/-- Checked boundary-angle rows available through the integrated geometry
ledger. -/
def boundaryAngleFinalRoutes : BoundaryAngleFinalRoutes where
  direct := boundaryAngleDirectTargetRoute
  k23 := boundaryAngleK23TargetRoute
  commonNeighbor := boundaryAngleCommonNeighborTargetRoute

/-- All checked conditional target routes gathered by the aggregate. -/
structure CheckedConditionalRoutes where
  brokenLattice :
    BrokenLatticeFinalIntegratedW11.ConditionalSwanepoelTargetRoutes.{u}
  k23Final : K23FinalRoutes.{u}
  noEarlyFinal : NoEarlyFinalRoutes.{u}
  boundaryLabel : BoundaryLabelFinalRoutes.{u}
  geometryTarget : GeometryTargetFinalRoutes.{u}
  boundaryAngle : BoundaryAngleFinalRoutes.{u}
  targetConsistency :
    TargetLedgerConsistencyW11.CheckedTargetRoutes.{u}

/-- The checked conditional target-route ledger. -/
def checkedConditionalRoutes : CheckedConditionalRoutes where
  brokenLattice :=
    BrokenLatticeFinalIntegratedW11.conditionalSwanepoelTargetRoutes
  k23Final := k23FinalRoutes
  noEarlyFinal := noEarlyFinalRoutes
  boundaryLabel := boundaryLabelFinalRoutes
  geometryTarget := geometryTargetFinalRoutes
  boundaryAngle := boundaryAngleFinalRoutes
  targetConsistency := TargetLedgerConsistencyW11.checkedTargetRoutes

/-! ## Final aggregate matrix -/

/-- Final aggregate ledger of checked conditional Swanepoel target routes.

The aggregate stores checked routes and the names of the matrix inputs.  It
does not provide any input matrix inhabitants. -/
structure Matrix where
  imported : ImportedFinalLedgers
  inputTypes : ExplicitInputMatrixTypes
  routes : CheckedConditionalRoutes

/-- The checked final aggregate route ledger. -/
def matrix : Matrix where
  imported := importedFinalLedgers
  inputTypes := explicitInputMatrixTypes
  routes := checkedConditionalRoutes

/-! ## Public conditional projections from explicit matrices -/

theorem target_via_core_directFields
    (M : CoreInputMatrices) :
    Target :=
  BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_directFieldMatrix
    M.directFields

theorem target_via_core_k23Fields
    (M : CoreInputMatrices) :
    Target :=
  BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_k23FieldMatrix
    M.k23Fields

theorem target_via_core_commonNeighborFields
    (M : CoreInputMatrices) :
    Target :=
  BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix
    M.commonNeighborFields

theorem target_via_core_noEarlyRows
    (M : CoreInputMatrices) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noEarlyMatrix M.noEarlyRows

theorem target_via_core_noStartRows
    (M : CoreInputMatrices) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noStartMatrix M.noStartRows

theorem target_via_core_directGeometry
    (M : CoreInputMatrices) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    M.directGeometry

theorem target_via_core_k23Geometry
    (M : CoreInputMatrices) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    M.k23Geometry

theorem target_via_core_commonNeighborGeometry
    (M : CoreInputMatrices) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    M.commonNeighborGeometry

theorem target_via_core_k23Integrated
    (M : CoreInputMatrices) :
    Target :=
  K23IntegratedMatrixW11.targetLowerBoundEightThirtyOne_of_k23IntegratedMatrix
    M.k23Integrated

theorem target_via_core_commonNeighborIntegrated
    (M : CoreInputMatrices) :
    Target :=
  K23IntegratedMatrixW11.targetLowerBoundEightThirtyOne_of_commonNeighborIntegratedMatrix
    M.commonNeighborIntegrated

theorem target_via_k23Final
    (M : FinalBranchInputMatrices) :
    Target :=
  K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix_via_k23
    M.k23Final

theorem target_via_k23Final_commonNeighbor
    (M : FinalBranchInputMatrices) :
    Target :=
  K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix
    M.k23Final

theorem target_via_noEarlyFinal
    (M : FinalBranchInputMatrices) :
    Target :=
  NoEarlyFinalIntegratedW11.swanepoelTarget_of_finalNoEarlyMatrix
    M.noStartNoEarlyFinal

theorem target_via_noStartFinal
    (M : FinalBranchInputMatrices) :
    Target :=
  NoEarlyFinalIntegratedW11.swanepoelTarget_of_finalNoStartMatrix
    M.noStartNoEarlyFinal

theorem target_via_boundaryLabel
    (M : FinalBranchInputMatrices) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix
    M.boundaryLabelTarget

theorem target_via_boundaryLabel_noEarlyTarget
    (M : FinalBranchInputMatrices) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix_via_noEarlyTarget
    M.boundaryLabelTarget

theorem target_via_boundaryLabel_geometry
    (M : FinalBranchInputMatrices) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix_via_geometry
    M.boundaryLabelTarget

theorem target_via_boundaryLabel_geometryTarget
    (M : FinalBranchInputMatrices) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix_via_geometryTarget
    M.boundaryLabelTarget

theorem target_via_geometryTarget_direct
    (M : FinalBranchInputMatrices) :
    Target :=
  GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_directTargetMatrix
    M.geometryTargetDirect

theorem target_via_geometryTarget_k23
    (M : FinalBranchInputMatrices) :
    Target :=
  GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_k23TargetMatrix
    M.geometryTargetK23

theorem target_via_geometryTarget_commonNeighbor
    (M : FinalBranchInputMatrices) :
    Target :=
  GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
    M.geometryTargetCommonNeighbor

theorem target_via_boundaryAngle_direct
    (M : FinalBranchInputMatrices) :
    Target :=
  boundaryAngleDirectTargetRoute.target M.boundaryAngleDirect

theorem target_via_boundaryAngle_k23
    (M : FinalBranchInputMatrices) :
    Target :=
  boundaryAngleK23TargetRoute.target M.boundaryAngleK23

theorem target_via_boundaryAngle_commonNeighbor
    (M : FinalBranchInputMatrices) :
    Target :=
  boundaryAngleCommonNeighborTargetRoute.target M.boundaryAngleCommonNeighbor

theorem target_via_all_core_direct
    (M : ExplicitInputMatrices) :
    Target :=
  target_via_core_directFields M.core

theorem target_via_all_k23Final
    (M : ExplicitInputMatrices) :
    Target :=
  target_via_k23Final M.finalBranches

theorem target_via_all_boundaryLabel
    (M : ExplicitInputMatrices) :
    Target :=
  target_via_boundaryLabel M.finalBranches

end

end SwanepoelTargetFinalAggregateW11
end Swanepoel
end ErdosProblems1066
