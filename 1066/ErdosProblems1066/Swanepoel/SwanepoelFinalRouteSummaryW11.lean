import ErdosProblems1066.Swanepoel.TargetConsistencyVerifiedFinalW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalAggregate
import ErdosProblems1066.Swanepoel.SwanepoelTargetFinalAggregateW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency
import ErdosProblems1066.Swanepoel.BoundaryAngleTargetFinalW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# W11 Swanepoel final route summary

This module is a compact terminal summary of the checked W11 Swanepoel route
facades.  It records the imported matrices, displays the remaining matrix
inputs as explicit caller-supplied packages, and exposes only conditional
target projections from those packages.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelFinalRouteSummaryW11

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

/-! ## Imported checked matrices -/

/-- The final W11 Swanepoel imports summarized by this file. -/
structure CheckedMatrices : Type where
  verifiedTargetConsistencyChecked :
    True
  finalAggregateChecked :
    True
  targetFinalAggregateChecked :
    True
  finalConsistencyChecked :
    True
  boundaryAngleTargetChecked :
    True

/-- Imported checked W11 ledgers. -/
def checkedMatrices :
    CheckedMatrices where
  verifiedTargetConsistencyChecked := True.intro
  finalAggregateChecked := True.intro
  targetFinalAggregateChecked := True.intro
  finalConsistencyChecked := True.intro
  boundaryAngleTargetChecked := True.intro

/-! ## Caller-supplied matrices -/

/-- Matrix package used by the final aggregate projections. -/
structure FinalAggregateMatrices : Type (u + 1) where
  boundaryLabelFinal :
    BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}
  noEarlyTargetFinal :
    NoEarlyTargetFinalW11.FinalMatrixInput.{u}
  geometryDirectFinal :
    GeometryFinalIntegratedW11.DirectFinalGeometryMatrix.{u}
  geometryK23Final :
    GeometryFinalIntegratedW11.K23FinalGeometryMatrix.{u}
  geometryCommonNeighborFinal :
    GeometryFinalIntegratedW11.CommonNeighborFinalGeometryMatrix.{u}
  brokenLatticeDirect :
    BrokenLatticeFinalIntegratedW11.DirectFieldMatrix.{u}
  brokenLatticeK23 :
    BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u}
  brokenLatticeCommonNeighbor :
    BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u}
  k23BrokenFields :
    K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}
  boundaryLabelIntegrated :
    BoundaryLabelIntegratedW11.Matrix.{u}
  explicitNoEarly :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}
  geometryDirectTarget :
    GeometryTargetIntegratedW11.DirectTargetMatrix.{u}
  k23ExplicitTarget :
    K23TargetIntegratedW11.K23TargetMatrix.{u}

/-- All explicit matrix packages displayed by this final summary. -/
structure RequiredMatrices : Type (u + 1) where
  verifiedTargetConsistency :
    TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u}
  finalAggregate :
    FinalAggregateMatrices.{u}
  targetAggregateCore :
    SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u}
  targetAggregateBranches :
    SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}
  targetAggregateAll :
    SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices.{u}
  boundaryAngleFinal :
    BoundaryAngleTargetFinalW11.FinalMatrixInput.{u}

namespace RequiredMatrices

/-- Core target-aggregate rows carried by the combined target-aggregate
package. -/
def coreFromAll
    (M : RequiredMatrices.{u}) :
    SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u} :=
  M.targetAggregateAll.core

/-- Final branch rows carried by the combined target-aggregate package. -/
def branchesFromAll
    (M : RequiredMatrices.{u}) :
    SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u} :=
  M.targetAggregateAll.finalBranches

@[simp]
theorem coreFromAll_eq
    (M : RequiredMatrices.{u}) :
    M.coreFromAll = M.targetAggregateAll.core :=
  rfl

@[simp]
theorem branchesFromAll_eq
    (M : RequiredMatrices.{u}) :
    M.branchesFromAll = M.targetAggregateAll.finalBranches :=
  rfl

end RequiredMatrices

/-! ## Explicit required matrix ledgers -/

/-- Type-level ledgers for the explicit matrix surfaces kept open. -/
structure RequiredMatrixLedgers : Type (u + 2) where
  all :
    Type (u + 1)

/-- Checked type-level ledgers for all open matrix inputs. -/
def requiredMatrixLedgers :
    RequiredMatrixLedgers.{u} where
  all := RequiredMatrices.{u}

/-! ## Conditional target rows -/

/-- A target projection that remains indexed by explicit caller data. -/
structure ConditionalTargetProjection (alpha : Sort v) : Sort (max 1 v) where
  target : alpha -> Target

/-- Target projections from the verified target-consistency package. -/
structure VerifiedTargetConsistencyRoutes : Type (u + 1) where
  directField :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  k23Field :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  commonNeighborField :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  noEarlyRows :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  noStartRows :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  geometryDirect :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  geometryK23 :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  geometryCommonNeighbor :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  k23 :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  commonNeighbor :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  explicitNoEarly :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  explicitNoStart :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  explicitNoStartNoEarly :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  noEarlyFinal :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  noStartFinal :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})
  boundaryLabelIntegrated :
    ConditionalTargetProjection
      (TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u})

/-- Checked target-consistency routes. -/
def verifiedTargetConsistencyRoutes :
    VerifiedTargetConsistencyRoutes.{u} where
  directField := {
    target := TargetConsistencyVerifiedFinalW11.target_of_directField
  }
  k23Field := {
    target := TargetConsistencyVerifiedFinalW11.target_of_k23Field
  }
  commonNeighborField := {
    target := TargetConsistencyVerifiedFinalW11.target_of_commonNeighborField
  }
  noEarlyRows := {
    target := TargetConsistencyVerifiedFinalW11.target_of_noEarlyRows
  }
  noStartRows := {
    target := TargetConsistencyVerifiedFinalW11.target_of_noStartRows
  }
  geometryDirect := {
    target := TargetConsistencyVerifiedFinalW11.target_of_geometryDirect
  }
  geometryK23 := {
    target := TargetConsistencyVerifiedFinalW11.target_of_geometryK23
  }
  geometryCommonNeighbor := {
    target :=
      TargetConsistencyVerifiedFinalW11.target_of_geometryCommonNeighbor
  }
  k23 := {
    target := TargetConsistencyVerifiedFinalW11.target_of_k23
  }
  commonNeighbor := {
    target := TargetConsistencyVerifiedFinalW11.target_of_commonNeighbor
  }
  explicitNoEarly := {
    target := TargetConsistencyVerifiedFinalW11.target_of_explicitNoEarly
  }
  explicitNoStart := {
    target := TargetConsistencyVerifiedFinalW11.target_of_explicitNoStart
  }
  explicitNoStartNoEarly := {
    target :=
      TargetConsistencyVerifiedFinalW11.target_of_explicitNoStartNoEarly
  }
  noEarlyFinal := {
    target := TargetConsistencyVerifiedFinalW11.target_of_noEarlyFinal
  }
  noStartFinal := {
    target := TargetConsistencyVerifiedFinalW11.target_of_noStartFinal
  }
  boundaryLabelIntegrated := {
    target :=
      TargetConsistencyVerifiedFinalW11.target_of_boundaryLabelIntegrated
  }

/-- Target projections from the final aggregate package. -/
structure FinalAggregateRoutes : Type (u + 1) where
  boundaryLabelFinal :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  boundaryLabelFinalViaNoEarly :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  boundaryLabelFinalViaGeometry :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  noEarlyTargetFinal :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  noStartTargetFinal :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  explicitNoEarlyTargetFinal :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  geometryDirectFinal :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  geometryK23Final :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  geometryCommonNeighborFinal :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  brokenLatticeDirect :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  brokenLatticeK23 :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  brokenLatticeCommonNeighbor :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  k23BrokenFieldsViaDirect :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  k23BrokenFieldsViaK23 :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  k23BrokenFieldsViaCommonNeighbor :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  targetConsistencyBoundaryLabel :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  targetConsistencyExplicitNoEarly :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  targetConsistencyGeometryDirect :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})
  targetConsistencyK23 :
    ConditionalTargetProjection (FinalAggregateMatrices.{u})

/-- Checked final aggregate routes. -/
def finalAggregateRoutes :
    FinalAggregateRoutes.{u} where
  boundaryLabelFinal := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_boundaryLabelFinalMatrix
        M.boundaryLabelFinal
  }
  boundaryLabelFinalViaNoEarly := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_boundaryLabelFinalMatrix_via_noEarlyFinal
        M.boundaryLabelFinal
  }
  boundaryLabelFinalViaGeometry := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_boundaryLabelFinalMatrix_via_geometryTarget
        M.boundaryLabelFinal
  }
  noEarlyTargetFinal := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_noEarlyTargetFinalMatrix_via_noEarly
        M.noEarlyTargetFinal
  }
  noStartTargetFinal := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_noEarlyTargetFinalMatrix_via_noStart
        M.noEarlyTargetFinal
  }
  explicitNoEarlyTargetFinal := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_noEarlyTargetFinalMatrix_via_explicitNoEarly
        M.noEarlyTargetFinal
  }
  geometryDirectFinal := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_geometryDirectFinalMatrix
        M.geometryDirectFinal
  }
  geometryK23Final := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_geometryK23FinalMatrix
        M.geometryK23Final
  }
  geometryCommonNeighborFinal := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_geometryCommonNeighborFinalMatrix
        M.geometryCommonNeighborFinal
  }
  brokenLatticeDirect := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_brokenLatticeDirectFieldMatrix
        M.brokenLatticeDirect
  }
  brokenLatticeK23 := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_brokenLatticeK23FieldMatrix
        M.brokenLatticeK23
  }
  brokenLatticeCommonNeighbor := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_brokenLatticeCommonNeighborFieldMatrix
        M.brokenLatticeCommonNeighbor
  }
  k23BrokenFieldsViaDirect := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_direct
        M.k23BrokenFields
  }
  k23BrokenFieldsViaK23 := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_k23Final
        M.k23BrokenFields
  }
  k23BrokenFieldsViaCommonNeighbor := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_k23BrokenLatticeFields_via_commonNeighborFinal
        M.k23BrokenFields
  }
  targetConsistencyBoundaryLabel := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_targetConsistency_boundaryLabelIntegratedMatrix
        M.boundaryLabelIntegrated
  }
  targetConsistencyExplicitNoEarly := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_targetConsistency_explicitNoEarlyMatrix
        M.explicitNoEarly
  }
  targetConsistencyGeometryDirect := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_targetConsistency_geometryDirectTargetMatrix
        M.geometryDirectTarget
  }
  targetConsistencyK23 := {
    target := fun M =>
      SwanepoelW11FinalAggregate.target_of_targetConsistency_k23ExplicitTargetMatrix
        M.k23ExplicitTarget
  }

/-- Core route projections from the terminal target aggregate. -/
structure TargetAggregateCoreRoutes : Type (u + 1) where
  directFields :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u})
  k23Fields :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u})
  commonNeighborFields :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u})
  noEarlyRows :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u})
  noStartRows :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u})
  directGeometry :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u})
  k23Geometry :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u})
  commonNeighborGeometry :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u})
  k23Integrated :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u})
  commonNeighborIntegrated :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.CoreInputMatrices.{u})

/-- Checked core routes from the target aggregate. -/
def targetAggregateCoreRoutes :
    TargetAggregateCoreRoutes.{u} where
  directFields := {
    target := SwanepoelTargetFinalAggregateW11.target_via_core_directFields
  }
  k23Fields := {
    target := SwanepoelTargetFinalAggregateW11.target_via_core_k23Fields
  }
  commonNeighborFields := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborFields
  }
  noEarlyRows := {
    target := SwanepoelTargetFinalAggregateW11.target_via_core_noEarlyRows
  }
  noStartRows := {
    target := SwanepoelTargetFinalAggregateW11.target_via_core_noStartRows
  }
  directGeometry := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_core_directGeometry
  }
  k23Geometry := {
    target := SwanepoelTargetFinalAggregateW11.target_via_core_k23Geometry
  }
  commonNeighborGeometry := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborGeometry
  }
  k23Integrated := {
    target := SwanepoelTargetFinalAggregateW11.target_via_core_k23Integrated
  }
  commonNeighborIntegrated := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborIntegrated
  }

/-- Final-branch route projections from the terminal target aggregate. -/
structure TargetAggregateBranchRoutes : Type (u + 1) where
  k23Final :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  k23FinalCommonNeighbor :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  noEarlyFinal :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  noStartFinal :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  boundaryLabel :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  boundaryLabelNoEarly :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  boundaryLabelGeometry :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  geometryDirect :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  geometryK23 :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  geometryCommonNeighbor :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  boundaryAngleDirect :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  boundaryAngleK23 :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})
  boundaryAngleCommonNeighbor :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u})

/-- Checked final-branch routes from the target aggregate. -/
def targetAggregateBranchRoutes :
    TargetAggregateBranchRoutes.{u} where
  k23Final := {
    target := SwanepoelTargetFinalAggregateW11.target_via_k23Final
  }
  k23FinalCommonNeighbor := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_k23Final_commonNeighbor
  }
  noEarlyFinal := {
    target := SwanepoelTargetFinalAggregateW11.target_via_noEarlyFinal
  }
  noStartFinal := {
    target := SwanepoelTargetFinalAggregateW11.target_via_noStartFinal
  }
  boundaryLabel := {
    target := SwanepoelTargetFinalAggregateW11.target_via_boundaryLabel
  }
  boundaryLabelNoEarly := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_boundaryLabel_noEarlyTarget
  }
  boundaryLabelGeometry := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_boundaryLabel_geometryTarget
  }
  geometryDirect := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_geometryTarget_direct
  }
  geometryK23 := {
    target := SwanepoelTargetFinalAggregateW11.target_via_geometryTarget_k23
  }
  geometryCommonNeighbor := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_geometryTarget_commonNeighbor
  }
  boundaryAngleDirect := {
    target := SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_direct
  }
  boundaryAngleK23 := {
    target := SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_k23
  }
  boundaryAngleCommonNeighbor := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_commonNeighbor
  }

/-- Combined target-aggregate route projections. -/
structure TargetAggregateAllRoutes : Type (u + 1) where
  coreDirect :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices.{u})
  k23Final :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices.{u})
  boundaryLabel :
    ConditionalTargetProjection
      (SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices.{u})

/-- Checked combined target-aggregate routes. -/
def targetAggregateAllRoutes :
    TargetAggregateAllRoutes.{u} where
  coreDirect := {
    target := SwanepoelTargetFinalAggregateW11.target_via_all_core_direct
  }
  k23Final := {
    target := SwanepoelTargetFinalAggregateW11.target_via_all_k23Final
  }
  boundaryLabel := {
    target := SwanepoelTargetFinalAggregateW11.target_via_all_boundaryLabel
  }

/-- Boundary-angle final route projections. -/
structure BoundaryAngleRoutes : Type (u + 1) where
  direct :
    ConditionalTargetProjection
      (BoundaryAngleTargetFinalW11.FinalMatrixInput.{u})
  k23 :
    ConditionalTargetProjection
      (BoundaryAngleTargetFinalW11.FinalMatrixInput.{u})
  commonNeighbor :
    ConditionalTargetProjection
      (BoundaryAngleTargetFinalW11.FinalMatrixInput.{u})
  brokenLatticeDirect :
    ConditionalTargetProjection
      (BoundaryAngleTargetFinalW11.FinalMatrixInput.{u})
  brokenLatticeK23 :
    ConditionalTargetProjection
      (BoundaryAngleTargetFinalW11.FinalMatrixInput.{u})
  brokenLatticeCommonNeighbor :
    ConditionalTargetProjection
      (BoundaryAngleTargetFinalW11.FinalMatrixInput.{u})
  targetConsistencyDirect :
    ConditionalTargetProjection
      (BoundaryAngleTargetFinalW11.FinalMatrixInput.{u})
  targetConsistencyK23 :
    ConditionalTargetProjection
      (BoundaryAngleTargetFinalW11.FinalMatrixInput.{u})
  targetConsistencyCommonNeighbor :
    ConditionalTargetProjection
      (BoundaryAngleTargetFinalW11.FinalMatrixInput.{u})

/-- Checked boundary-angle final routes. -/
def boundaryAngleRoutes :
    BoundaryAngleRoutes.{u} where
  direct := {
    target := BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_direct
  }
  k23 := {
    target := BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_k23
  }
  commonNeighbor := {
    target :=
      BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_commonNeighbor
  }
  brokenLatticeDirect := {
    target :=
      BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_brokenLatticeDirect
  }
  brokenLatticeK23 := {
    target :=
      BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_brokenLatticeK23
  }
  brokenLatticeCommonNeighbor := {
    target :=
      BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_brokenLatticeCommonNeighbor
  }
  targetConsistencyDirect := {
    target :=
      BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_targetConsistencyDirect
  }
  targetConsistencyK23 := {
    target :=
      BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_targetConsistencyK23
  }
  targetConsistencyCommonNeighbor := {
    target :=
      BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_targetConsistencyCommonNeighbor
  }

/-- All conditional route rows exposed by the final summary. -/
structure ConditionalRouteSummary : Type (u + 1) where
  verifiedTargetConsistency :
    VerifiedTargetConsistencyRoutes.{u}
  finalAggregate :
    FinalAggregateRoutes.{u}
  targetAggregateCore :
    TargetAggregateCoreRoutes.{u}
  targetAggregateBranches :
    TargetAggregateBranchRoutes.{u}
  targetAggregateAll :
    TargetAggregateAllRoutes.{u}
  boundaryAngle :
    BoundaryAngleRoutes.{u}

/-- Checked conditional route rows. -/
def conditionalRouteSummary :
    ConditionalRouteSummary.{u} where
  verifiedTargetConsistency := verifiedTargetConsistencyRoutes
  finalAggregate := finalAggregateRoutes
  targetAggregateCore := targetAggregateCoreRoutes
  targetAggregateBranches := targetAggregateBranchRoutes
  targetAggregateAll := targetAggregateAllRoutes
  boundaryAngle := boundaryAngleRoutes

/-! ## Final summary matrix -/

/-- Final W11 Swanepoel conditional route summary.

The summary stores checked ledgers, explicit required-matrix ledgers, and
conditional target rows only.  It supplies no inhabitant of the required
matrix packages. -/
structure Matrix : Type (u + 4) where
  checked :
    CheckedMatrices
  required :
    RequiredMatrixLedgers.{u}
  routes :
    ConditionalRouteSummary.{u}
  omissions :
    SwanepoelW11FinalConsistency.KnownImportOmissions

/-- The checked final conditional route summary. -/
def matrix :
    Matrix.{u} where
  checked := checkedMatrices
  required := requiredMatrixLedgers
  routes := conditionalRouteSummary
  omissions := SwanepoelW11FinalConsistency.knownImportOmissions

theorem matrix_nonempty :
    Nonempty Matrix.{u} :=
  Nonempty.intro matrix

theorem checked_verifiedTargetConsistency :
    matrix.checked.verifiedTargetConsistencyChecked =
      True.intro := by
  rfl

theorem checked_finalAggregate :
    matrix.checked.finalAggregateChecked =
      True.intro := by
  rfl

theorem checked_targetFinalAggregate :
    matrix.checked.targetFinalAggregateChecked =
      True.intro := by
  rfl

theorem checked_finalConsistency :
    matrix.checked.finalConsistencyChecked =
      True.intro := by
  rfl

theorem checked_boundaryAngleTarget :
    matrix.checked.boundaryAngleTargetChecked =
      True.intro := by
  rfl

/-! ## Public conditional projections from the displayed packages -/

theorem target_via_verified_directField
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.verifiedTargetConsistency.directField.target
    M.verifiedTargetConsistency

theorem target_via_verified_noEarlyFinal
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.verifiedTargetConsistency.noEarlyFinal.target
    M.verifiedTargetConsistency

theorem target_via_finalAggregate_boundaryLabel
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.finalAggregate.boundaryLabelFinal.target M.finalAggregate

theorem target_via_finalAggregate_noEarly
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.finalAggregate.noEarlyTargetFinal.target M.finalAggregate

theorem target_via_finalAggregate_geometryDirect
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.finalAggregate.geometryDirectFinal.target M.finalAggregate

theorem target_via_finalAggregate_brokenLatticeDirect
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.finalAggregate.brokenLatticeDirect.target M.finalAggregate

theorem target_via_targetAggregate_coreDirect
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.targetAggregateCore.directFields.target
    M.targetAggregateCore

theorem target_via_targetAggregate_k23Final
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.targetAggregateBranches.k23Final.target
    M.targetAggregateBranches

theorem target_via_targetAggregate_boundaryAngleDirect
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.targetAggregateBranches.boundaryAngleDirect.target
    M.targetAggregateBranches

theorem target_via_targetAggregate_allCoreDirect
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.targetAggregateAll.coreDirect.target
    M.targetAggregateAll

theorem target_via_boundaryAngle_direct
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.boundaryAngle.direct.target M.boundaryAngleFinal

theorem target_via_boundaryAngle_targetConsistencyDirect
    (M : RequiredMatrices.{u}) :
    Target :=
  matrix.routes.boundaryAngle.targetConsistencyDirect.target
    M.boundaryAngleFinal

end

end SwanepoelFinalRouteSummaryW11
end Swanepoel
end ErdosProblems1066
