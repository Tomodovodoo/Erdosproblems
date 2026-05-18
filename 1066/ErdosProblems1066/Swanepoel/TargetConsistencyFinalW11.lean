import ErdosProblems1066.Swanepoel.TargetLedgerConsistencyW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11
import ErdosProblems1066.Swanepoel.SwanepoelW11ConsistencyMatrix
import ErdosProblems1066.Swanepoel.GeometryTargetIntegratedW11
import ErdosProblems1066.Swanepoel.K23TargetIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyTargetIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 Swanepoel target-route consistency ledger

This module gathers the checked target-facing W11 ledgers into one typed
record.  It records imported matrices and the matrix shapes still required by
the checked conditional target projections below.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TargetConsistencyFinalW11

universe u

noncomputable section

abbrev Target : Prop :=
  TargetLedgerConsistencyW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetLedgerConsistencyW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetLedgerConsistencyW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  TargetLedgerConsistencyW11.MinimalFailureEliminator

/-! ## Explicit input ledgers -/

/-- Input matrix shapes consumed by the broad W11 consistency projections.
These are requirements, not constructed values. -/
structure BroadConsistencyInputMatrices : Type (u + 2) where
  boundaryAngleClosureDirect : Type (u + 1)
  boundaryAngleClosureK23 : Type (u + 1)
  boundaryAngleClosureCommonNeighbor : Type (u + 1)
  boundaryLabelClosure : Type (u + 1)
  boundaryLabelIntegrated : Type (u + 1)
  prefixNoEarly : Type (u + 1)
  explicitNoEarly : Type (u + 1)
  explicitNoStart : Type (u + 1)
  geometryDirect : Type (u + 1)
  geometryK23 : Type (u + 1)
  geometryCommonNeighbor : Type (u + 1)
  brokenLatticeDirect : Type (u + 1)
  k23Integrated : Type (u + 1)
  commonNeighborIntegrated : Type (u + 1)
  k23Target : Type (u + 1)
  commonNeighborTarget : Type (u + 1)
  subpolygonDirect : Type (u + 1)
  targetIntegratedDirect : Type (u + 1)

/-- All input matrix shapes used by `SwanepoelW11ConsistencyMatrix`. -/
def broadConsistencyInputMatrices : BroadConsistencyInputMatrices.{u} where
  boundaryAngleClosureDirect :=
    BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.{u}
  boundaryAngleClosureK23 :=
    BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.{u}
  boundaryAngleClosureCommonNeighbor :=
    BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.{u}
  boundaryLabelClosure := BoundaryLabelClosureW11.Matrix.{u}
  boundaryLabelIntegrated := BoundaryLabelIntegratedW11.Matrix.{u}
  prefixNoEarly := NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}
  explicitNoEarly := NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}
  explicitNoStart := NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}
  geometryDirect := GeometryIntegratedW11.DirectGeometryMatrix.{u}
  geometryK23 := GeometryIntegratedW11.K23GeometryMatrix.{u}
  geometryCommonNeighbor :=
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u}
  brokenLatticeDirect := BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}
  k23Integrated := K23IntegratedMatrixW11.K23IntegratedMatrix.{u}
  commonNeighborIntegrated :=
    K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u}
  k23Target := K23TargetIntegratedW11.K23TargetMatrix.{u}
  commonNeighborTarget :=
    K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u}
  subpolygonDirect :=
    SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u}
  targetIntegratedDirect := BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}

/-- Input matrix shapes consumed by the target-facing wrapper projections. -/
structure TargetFacingInputMatrices : Type (u + 2) where
  geometryDirectTarget : Type (u + 1)
  geometryK23Target : Type (u + 1)
  geometryCommonNeighborTarget : Type (u + 1)
  k23Target : Type (u + 1)
  commonNeighborTarget : Type (u + 1)
  explicitNoEarly : Type (u + 1)
  explicitNoStart : Type (u + 1)
  explicitNoStartNoEarly : Type (u + 1)

/-- All input matrix shapes used by the target-facing wrapper ledgers. -/
def targetFacingInputMatrices : TargetFacingInputMatrices.{u} where
  geometryDirectTarget := GeometryTargetIntegratedW11.DirectTargetMatrix.{u}
  geometryK23Target := GeometryTargetIntegratedW11.K23TargetMatrix.{u}
  geometryCommonNeighborTarget :=
    GeometryTargetIntegratedW11.CommonNeighborTargetMatrix.{u}
  k23Target := K23TargetIntegratedW11.K23TargetMatrix.{u}
  commonNeighborTarget :=
    K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u}
  explicitNoEarly := NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}
  explicitNoStart := NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}
  explicitNoStartNoEarly :=
    NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u}

/-- All missing input matrices for the checked target routes. -/
structure RequiredInputMatrices : Type (u + 2) where
  targetLedger : TargetLedgerConsistencyW11.OpenInputLedger.{u}
  broadConsistency : BroadConsistencyInputMatrices.{u}
  targetFacing : TargetFacingInputMatrices.{u}

/-- The explicit input matrix ledger for the final consistency record. -/
def requiredInputMatrices : RequiredInputMatrices.{u} where
  targetLedger := TargetLedgerConsistencyW11.openInputLedger
  broadConsistency := broadConsistencyInputMatrices
  targetFacing := targetFacingInputMatrices

/-! ## Checked imports -/

/-- Imported checked W11 target-route matrices. -/
structure ImportedTargetMatrices : Type (u + 2) where
  targetLedgerConsistency : TargetLedgerConsistencyW11.Matrix.{u}
  targetIntegrated : TargetIntegratedMatrixW11.Matrix.{u}
  targetClosure : TargetClosureMatrixW11.Matrix.{u}
  geometryTarget : GeometryTargetIntegratedW11.Matrix.{u}
  k23Target : K23TargetIntegratedW11.Matrix.{u}
  noEarlyTarget : NoEarlyTargetIntegratedW11.Matrix.{u}

/-- The imported matrices that currently typecheck together. -/
def importedTargetMatrices : ImportedTargetMatrices.{u} where
  targetLedgerConsistency := TargetLedgerConsistencyW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  targetClosure := TargetClosureMatrixW11.matrix
  geometryTarget := GeometryTargetIntegratedW11.matrix
  k23Target := K23TargetIntegratedW11.matrix
  noEarlyTarget := NoEarlyTargetIntegratedW11.matrix

/-! ## Final consistency matrix -/

/-- Final consistency matrix for checked W11 Swanepoel target routes.

The matrix stores imported checked matrices, visible missing input matrices,
and the known import blocker ledger from the broad consistency matrix. -/
structure Matrix : Type (u + 2) where
  imports : ImportedTargetMatrices.{u}
  missingInputs : RequiredInputMatrices.{u}
  importBlockers : SwanepoelW11ConsistencyMatrix.ImportBlockers

/-- The checked final target-route consistency ledger. -/
def matrix : Matrix.{u} where
  imports := importedTargetMatrices
  missingInputs := requiredInputMatrices
  importBlockers := SwanepoelW11ConsistencyMatrix.importBlockers

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

/-! ## Public conditional projections from the final ledger -/

theorem target_from_ledger_directFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_directFieldMatrix M

theorem target_from_ledger_k23FieldMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_k23FieldMatrix M

theorem target_from_ledger_commonNeighborFieldMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_commonNeighborFieldMatrix M

theorem target_from_ledger_noEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_noEarlyMatrix M

theorem target_from_ledger_noStartMatrix
    (M : WindowNoEarlyRowsW11.NoStartMatrix.{u, u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_noStartMatrix M

theorem target_from_ledger_directGeometryMatrix
    (M : GeometryIntegratedW11.DirectGeometryMatrix.{u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_directGeometryMatrix M

theorem target_from_ledger_k23GeometryMatrix
    (M : GeometryIntegratedW11.K23GeometryMatrix.{u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_k23GeometryMatrix M

theorem target_from_ledger_commonNeighborGeometryMatrix
    (M : GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_commonNeighborGeometryMatrix M

theorem target_from_ledger_k23IntegratedMatrix
    (M : K23IntegratedMatrixW11.K23IntegratedMatrix.{u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_k23IntegratedMatrix M

theorem target_from_ledger_commonNeighborIntegratedMatrix
    (M : K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_commonNeighborIntegratedMatrix M

theorem target_of_boundaryAngleClosureDirectMatrix
    (M : BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_boundaryAngleClosureDirectMatrix M

theorem target_of_boundaryAngleClosureK23Matrix
    (M : BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.boundaryAngleClosureK23Route.target M

theorem target_of_boundaryAngleClosureCommonNeighborMatrix
    (M : BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.boundaryAngleClosureCommonNeighborRoute.target M

theorem target_of_boundaryLabelClosureMatrix
    (M : BoundaryLabelClosureW11.Matrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_boundaryLabelClosureMatrix M

theorem target_of_boundaryLabelIntegratedMatrix
    (M : BoundaryLabelIntegratedW11.Matrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_boundaryLabelIntegratedMatrix M

theorem target_of_prefixNoEarlyMatrix
    (M : NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_prefixNoEarlyMatrix M

theorem target_of_explicitNoEarlyMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_explicitNoEarlyMatrix M

theorem target_of_explicitNoStartMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoStartMatrix M

theorem target_of_geometryDirectMatrix
    (M : GeometryIntegratedW11.DirectGeometryMatrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_geometryDirectMatrix M

theorem target_of_geometryK23Matrix
    (M : GeometryIntegratedW11.K23GeometryMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix M

theorem target_of_geometryCommonNeighborMatrix
    (M : GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    M

theorem target_of_brokenLatticeDirectFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_brokenLatticeDirectFieldMatrix M

theorem target_of_k23IntegratedMatrix
    (M : K23IntegratedMatrixW11.K23IntegratedMatrix.{u}) :
    Target :=
  K23IntegratedMatrixW11.targetLowerBoundEightThirtyOne_of_k23IntegratedMatrix
    M

theorem target_of_commonNeighborIntegratedMatrix
    (M : K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u}) :
    Target :=
  K23IntegratedMatrixW11.targetLowerBoundEightThirtyOne_of_commonNeighborIntegratedMatrix
    M

theorem target_of_k23TargetMatrix
    (M : K23TargetIntegratedW11.K23TargetMatrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_k23TargetMatrix M

theorem target_of_commonNeighborTargetMatrix
    (M : K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
    M

theorem target_of_subpolygonDirectBoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_subpolygonDirectBoundaryGeometryMatrix
    M

theorem target_of_targetIntegratedDirectFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_targetIntegratedDirectFieldMatrix M

theorem target_of_geometryDirectTargetMatrix
    (M : GeometryTargetIntegratedW11.DirectTargetMatrix.{u}) :
    Target :=
  GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_directTargetMatrix
    M

theorem target_of_geometryK23TargetMatrix
    (M : GeometryTargetIntegratedW11.K23TargetMatrix.{u}) :
    Target :=
  GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_k23TargetMatrix
    M

theorem target_of_geometryCommonNeighborTargetMatrix
    (M : GeometryTargetIntegratedW11.CommonNeighborTargetMatrix.{u}) :
    Target :=
  GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
    M

theorem target_of_k23ExplicitTargetMatrix
    (M : K23TargetIntegratedW11.K23TargetMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.targetLowerBoundEightThirtyOne_of_k23TargetMatrix M

theorem target_of_commonNeighborExplicitTargetMatrix
    (M : K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
    M

theorem target_of_noEarlyTargetMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoEarlyMatrix M

theorem target_of_noStartTargetMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoStartMatrix M

theorem target_of_noStartNoEarlyTargetMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoStartNoEarlyMatrix M

end

end TargetConsistencyFinalW11
end Swanepoel
end ErdosProblems1066
