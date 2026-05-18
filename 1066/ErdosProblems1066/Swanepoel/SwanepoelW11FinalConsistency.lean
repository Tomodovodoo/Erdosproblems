import ErdosProblems1066.Swanepoel.SwanepoelW11ConsistencyMatrix
import ErdosProblems1066.Swanepoel.TargetLedgerConsistencyW11
import ErdosProblems1066.Swanepoel.BoundaryAngleIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryLabelIntegratedW11
import ErdosProblems1066.Swanepoel.K23TargetIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryTargetIntegratedW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Swanepoel W11 final consistency ledger

This file is a final import-and-package check for the W11 Swanepoel ledgers.
It records only checked coexistence data and source-facing package routes.  It
does not assert the Swanepoel target proposition without an explicit package.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW11FinalConsistency

universe u v

noncomputable section

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

/-! ## Checked module package -/

/-- Canonical ledgers from the requested W11 modules, checked in one import
environment. -/
structure CheckedModuleLedger where
  swanepoelConsistency :
    SwanepoelW11ConsistencyMatrix.Matrix.{u}
  targetLedgerConsistency :
    TargetLedgerConsistencyW11.Matrix.{u}
  boundaryAngleIntegrated :
    BoundaryAngleIntegratedW11.Matrix.{u}
  boundaryLabelIntegrated :
    BoundaryLabelIntegratedW11.RouteMatrix.{u}
  k23TargetIntegrated :
    K23TargetIntegratedW11.Matrix.{u}
  geometryTargetIntegrated :
    GeometryTargetIntegratedW11.Matrix.{u}
  targetIntegrated :
    TargetIntegratedMatrixW11.Matrix.{u}

/-- The checked module ledger for the W11 final consistency pass. -/
def checkedModuleLedger : CheckedModuleLedger where
  swanepoelConsistency :=
    SwanepoelW11ConsistencyMatrix.matrix
  targetLedgerConsistency :=
    TargetLedgerConsistencyW11.matrix
  boundaryAngleIntegrated :=
    BoundaryAngleIntegratedW11.matrix
  boundaryLabelIntegrated :=
    BoundaryLabelIntegratedW11.routeMatrix
  k23TargetIntegrated :=
    K23TargetIntegratedW11.matrix
  geometryTargetIntegrated :=
    GeometryTargetIntegratedW11.matrix
  targetIntegrated :=
    TargetIntegratedMatrixW11.matrix

/-! ## Explicit package routes -/

/-- A source-facing route to the common cleared-pipeline propositions, without
asserting the target proposition itself. -/
structure ClearedPackageRoute (alpha : Sort v) : Sort (max 1 v) where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared

/-- Explicit source packages whose checked routes coexist in the final W11
environment. -/
structure ExplicitPackageRouteLedger where
  boundaryAngleDirect :
    ClearedPackageRoute
      (BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u})
  boundaryAngleK23 :
    ClearedPackageRoute
      (BoundaryAngleIntegratedW11.K23GeometryMatrix.{u})
  boundaryAngleCommonNeighbor :
    ClearedPackageRoute
      (BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u})
  boundaryLabelIntegrated :
    ClearedPackageRoute
      (BoundaryLabelIntegratedW11.Matrix.{u})
  k23TargetIntegrated :
    ClearedPackageRoute
      (K23TargetIntegratedW11.K23TargetMatrix.{u})
  commonNeighborTargetIntegrated :
    ClearedPackageRoute
      (K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u})
  geometryDirectTarget :
    ClearedPackageRoute
      (GeometryTargetIntegratedW11.DirectTargetMatrix.{u})
  geometryK23Target :
    ClearedPackageRoute
      (GeometryTargetIntegratedW11.K23TargetMatrix.{u})
  geometryCommonNeighborTarget :
    ClearedPackageRoute
      (GeometryTargetIntegratedW11.CommonNeighborTargetMatrix.{u})
  targetIntegratedDirectField :
    ClearedPackageRoute
      (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u})
  targetIntegratedK23Field :
    ClearedPackageRoute
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u})
  targetIntegratedCommonNeighborField :
    ClearedPackageRoute
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u})
  prefixNoEarly :
    ClearedPackageRoute
      (NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u})
  prefixNoStart :
    ClearedPackageRoute
      (NoEarlyIntegratedW11.PrefixNoStartMatrix.{u})

/-- Checked routes from explicit W11 source packages to the common
cleared-pipeline propositions. -/
def explicitPackageRouteLedger : ExplicitPackageRouteLedger where
  boundaryAngleDirect := {
    noMinimal :=
      BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_directGeometryMatrix
    pipeline :=
      BoundaryAngleIntegratedW11.pipelineCleared_of_directGeometryMatrix
  }
  boundaryAngleK23 := {
    noMinimal :=
      BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_k23GeometryMatrix
    pipeline :=
      BoundaryAngleIntegratedW11.pipelineCleared_of_k23GeometryMatrix
  }
  boundaryAngleCommonNeighbor := {
    noMinimal :=
      BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_commonNeighborGeometryMatrix
    pipeline :=
      BoundaryAngleIntegratedW11.pipelineCleared_of_commonNeighborGeometryMatrix
  }
  boundaryLabelIntegrated := {
    noMinimal :=
      BoundaryLabelIntegratedW11.no_minimalClearedFailure_of_matrix
    pipeline :=
      BoundaryLabelIntegratedW11.pipelineCleared_of_matrix
  }
  k23TargetIntegrated := {
    noMinimal :=
      K23TargetIntegratedW11.no_minimalClearedFailure_of_k23TargetMatrix
    pipeline :=
      K23TargetIntegratedW11.pipelineCleared_of_k23TargetMatrix
  }
  commonNeighborTargetIntegrated := {
    noMinimal :=
      K23TargetIntegratedW11.no_minimalClearedFailure_of_commonNeighborTargetMatrix
    pipeline :=
      K23TargetIntegratedW11.pipelineCleared_of_commonNeighborTargetMatrix
  }
  geometryDirectTarget := {
    noMinimal :=
      GeometryTargetIntegratedW11.no_minimalClearedFailure_of_directTargetMatrix
    pipeline :=
      GeometryTargetIntegratedW11.pipelineCleared_of_directTargetMatrix
  }
  geometryK23Target := {
    noMinimal :=
      GeometryTargetIntegratedW11.no_minimalClearedFailure_of_k23TargetMatrix
    pipeline :=
      GeometryTargetIntegratedW11.pipelineCleared_of_k23TargetMatrix
  }
  geometryCommonNeighborTarget := {
    noMinimal :=
      GeometryTargetIntegratedW11.no_minimalClearedFailure_of_commonNeighborTargetMatrix
    pipeline :=
      GeometryTargetIntegratedW11.pipelineCleared_of_commonNeighborTargetMatrix
  }
  targetIntegratedDirectField := {
    noMinimal :=
      TargetIntegratedMatrixW11.no_minimalClearedFailure_of_directFieldMatrix
    pipeline :=
      TargetIntegratedMatrixW11.pipelineCleared_of_directFieldMatrix
  }
  targetIntegratedK23Field := {
    noMinimal :=
      TargetIntegratedMatrixW11.no_minimalClearedFailure_of_k23FieldMatrix
    pipeline :=
      TargetIntegratedMatrixW11.pipelineCleared_of_k23FieldMatrix
  }
  targetIntegratedCommonNeighborField := {
    noMinimal :=
      TargetIntegratedMatrixW11.no_minimalClearedFailure_of_commonNeighborFieldMatrix
    pipeline :=
      TargetIntegratedMatrixW11.pipelineCleared_of_commonNeighborFieldMatrix
  }
  prefixNoEarly := {
    noMinimal :=
      TargetLedgerConsistencyW11.no_minimalClearedFailure_of_prefixNoEarlyMatrix
    pipeline :=
      TargetLedgerConsistencyW11.pipelineCleared_of_prefixNoEarlyMatrix
  }
  prefixNoStart := {
    noMinimal :=
      TargetLedgerConsistencyW11.no_minimalClearedFailure_of_prefixNoStartMatrix
    pipeline :=
      TargetLedgerConsistencyW11.pipelineCleared_of_prefixNoStartMatrix
  }

/-! ## Checked omissions -/

/-- Real import omissions carried into the final ledger as checked fields. -/
structure KnownImportOmissions : Type where
  topologyIntegratedW11 :
    "ErdosProblems1066.Swanepoel.TopologyIntegratedW11 import blocked: topology fact universe mismatch; unresolved boundary-geometry route names; matrix universe mismatch" =
    "ErdosProblems1066.Swanepoel.TopologyIntegratedW11 import blocked: topology fact universe mismatch; unresolved boundary-geometry route names; matrix universe mismatch"

/-- Current checked import omissions inherited from the W11 consistency
matrix. -/
def knownImportOmissions : KnownImportOmissions where
  topologyIntegratedW11 :=
    SwanepoelW11ConsistencyMatrix.importBlockers.topologyIntegratedW11

/-! ## Final consistency ledger -/

/-- Final W11 consistency ledger: requested checked modules, explicit package
routes, and checked omissions. -/
structure Matrix where
  checkedModules : CheckedModuleLedger
  explicitPackages : ExplicitPackageRouteLedger
  omissions : KnownImportOmissions

/-- The checked final W11 consistency ledger. -/
def matrix : Matrix where
  checkedModules :=
    checkedModuleLedger
  explicitPackages :=
    explicitPackageRouteLedger
  omissions :=
    knownImportOmissions

theorem checked_swanepoelConsistency :
    matrix.checkedModules.swanepoelConsistency =
      SwanepoelW11ConsistencyMatrix.matrix := by
  rfl

theorem checked_targetLedgerConsistency :
    matrix.checkedModules.targetLedgerConsistency =
      TargetLedgerConsistencyW11.matrix := by
  rfl

theorem checked_boundaryAngleIntegrated :
    matrix.checkedModules.boundaryAngleIntegrated =
      BoundaryAngleIntegratedW11.matrix := by
  rfl

theorem checked_boundaryLabelIntegrated :
    matrix.checkedModules.boundaryLabelIntegrated =
      BoundaryLabelIntegratedW11.routeMatrix := by
  rfl

theorem checked_k23TargetIntegrated :
    matrix.checkedModules.k23TargetIntegrated =
      K23TargetIntegratedW11.matrix := by
  rfl

theorem checked_geometryTargetIntegrated :
    matrix.checkedModules.geometryTargetIntegrated =
      GeometryTargetIntegratedW11.matrix := by
  rfl

theorem checked_targetIntegrated :
    matrix.checkedModules.targetIntegrated =
      TargetIntegratedMatrixW11.matrix := by
  rfl

theorem checked_topologyIntegratedW11_omission :
    matrix.omissions.topologyIntegratedW11 =
      SwanepoelW11ConsistencyMatrix.importBlockers.topologyIntegratedW11 := by
  rfl

end

end SwanepoelW11FinalConsistency
end Swanepoel
end ErdosProblems1066
