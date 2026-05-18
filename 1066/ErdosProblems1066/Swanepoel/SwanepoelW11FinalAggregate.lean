import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency
import ErdosProblems1066.Swanepoel.TargetConsistencyFinalW11
import ErdosProblems1066.Swanepoel.K23BrokenLatticeFinalW11
import ErdosProblems1066.Swanepoel.BoundaryLabelFinalIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyTargetFinalW11
import ErdosProblems1066.Swanepoel.GeometryFinalIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 Swanepoel aggregate ledger

This file gathers the checked final W11 Swanepoel route ledgers into one
additive record.  It records imported ledgers, explicit input matrices, and
conditional target routes only.  Every target projection below has a visible
caller-supplied input matrix.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW11FinalAggregate

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

/-- Explicit input matrix surfaces consumed by the gathered final ledgers. -/
structure ExplicitInputMatrices : Type (u + 3) where
  targetConsistency :
    TargetConsistencyFinalW11.RequiredInputMatrices.{u}
  geometryFinal :
    GeometryFinalIntegratedW11.ExplicitGeometryFieldLedger.{u}
  geometryAllBranches :
    Type (u + 1)
  boundaryLabelFinal :
    BoundaryLabelFinalIntegratedW11.ExplicitBoundaryLabelInputLedger.{u}
  noEarlyTargetFinal :
    NoEarlyTargetFinalW11.ExplicitInputLedger.{u}
  k23BrokenLatticeSurface :
    K23BrokenLatticeFinalW11.ExplicitFieldMatrixSurface.{u}
  k23BrokenLatticeFields :
    Type (u + 1)
  brokenLatticeFinal :
    BrokenLatticeFinalIntegratedW11.ExplicitFieldPackageLedger.{u}

/-- The complete explicit input matrix ledger exposed by the aggregate. -/
def explicitInputMatrices : ExplicitInputMatrices.{u} where
  targetConsistency := TargetConsistencyFinalW11.requiredInputMatrices
  geometryFinal := GeometryFinalIntegratedW11.explicitGeometryFieldLedger
  geometryAllBranches := GeometryFinalIntegratedW11.ExplicitGeometryMatrices.{u}
  boundaryLabelFinal :=
    BoundaryLabelFinalIntegratedW11.explicitBoundaryLabelInputLedger
  noEarlyTargetFinal := NoEarlyTargetFinalW11.explicitInputLedger
  k23BrokenLatticeSurface :=
    K23BrokenLatticeFinalW11.explicitFieldMatrixSurface
  k23BrokenLatticeFields :=
    K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}
  brokenLatticeFinal := BrokenLatticeFinalIntegratedW11.explicitFieldPackageLedger

/-! ## Target-consistency projections -/

/-- Target projections exported by the final target-consistency layer. -/
structure TargetConsistencyProjectionRoutes : Type (u + 2) where
  directField :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u} -> Target
  k23Field :
    BrokenLatticeIntegratedW11.K23FieldMatrix.{u} -> Target
  commonNeighborField :
    BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u} -> Target
  noEarly :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u} -> Target
  noStart :
    WindowNoEarlyRowsW11.NoStartMatrix.{u, u} -> Target
  directGeometry :
    GeometryIntegratedW11.DirectGeometryMatrix.{u} -> Target
  k23Geometry :
    GeometryIntegratedW11.K23GeometryMatrix.{u} -> Target
  commonNeighborGeometry :
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u} -> Target
  k23Integrated :
    K23IntegratedMatrixW11.K23IntegratedMatrix.{u} -> Target
  commonNeighborIntegrated :
    K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u} -> Target
  boundaryAngleClosureDirect :
    BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.{u} -> Target
  boundaryAngleClosureK23 :
    BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.{u} -> Target
  boundaryAngleClosureCommonNeighbor :
    BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.{u} ->
      Target
  boundaryLabelClosure :
    BoundaryLabelClosureW11.Matrix.{u} -> Target
  boundaryLabelIntegrated :
    BoundaryLabelIntegratedW11.Matrix.{u} -> Target
  prefixNoEarly :
    NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u} -> Target
  explicitNoEarly :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u} -> Target
  explicitNoStart :
    NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u} -> Target
  geometryDirect :
    GeometryIntegratedW11.DirectGeometryMatrix.{u} -> Target
  geometryK23 :
    GeometryIntegratedW11.K23GeometryMatrix.{u} -> Target
  geometryCommonNeighbor :
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u} -> Target
  brokenLatticeDirect :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u} -> Target
  k23IntegratedBroad :
    K23IntegratedMatrixW11.K23IntegratedMatrix.{u} -> Target
  commonNeighborIntegratedBroad :
    K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u} -> Target
  k23Target :
    K23TargetIntegratedW11.K23TargetMatrix.{u} -> Target
  commonNeighborTarget :
    K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u} -> Target
  subpolygonDirect :
    SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u} -> Target
  targetIntegratedDirect :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u} -> Target
  geometryDirectTarget :
    GeometryTargetIntegratedW11.DirectTargetMatrix.{u} -> Target
  geometryK23Target :
    GeometryTargetIntegratedW11.K23TargetMatrix.{u} -> Target
  geometryCommonNeighborTarget :
    GeometryTargetIntegratedW11.CommonNeighborTargetMatrix.{u} -> Target
  k23ExplicitTarget :
    K23TargetIntegratedW11.K23TargetMatrix.{u} -> Target
  commonNeighborExplicitTarget :
    K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u} -> Target
  noEarlyTarget :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u} -> Target
  noStartTarget :
    NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u} -> Target
  noStartNoEarlyTarget :
    NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u} -> Target

/-- The checked target-consistency projections with their input matrices. -/
def targetConsistencyProjectionRoutes :
    TargetConsistencyProjectionRoutes.{u} where
  directField := TargetConsistencyFinalW11.target_from_ledger_directFieldMatrix
  k23Field := TargetConsistencyFinalW11.target_from_ledger_k23FieldMatrix
  commonNeighborField :=
    TargetConsistencyFinalW11.target_from_ledger_commonNeighborFieldMatrix
  noEarly := TargetConsistencyFinalW11.target_from_ledger_noEarlyMatrix
  noStart := TargetConsistencyFinalW11.target_from_ledger_noStartMatrix
  directGeometry :=
    TargetConsistencyFinalW11.target_from_ledger_directGeometryMatrix
  k23Geometry :=
    TargetConsistencyFinalW11.target_from_ledger_k23GeometryMatrix
  commonNeighborGeometry :=
    TargetConsistencyFinalW11.target_from_ledger_commonNeighborGeometryMatrix
  k23Integrated :=
    TargetConsistencyFinalW11.target_from_ledger_k23IntegratedMatrix
  commonNeighborIntegrated :=
    TargetConsistencyFinalW11.target_from_ledger_commonNeighborIntegratedMatrix
  boundaryAngleClosureDirect :=
    TargetConsistencyFinalW11.target_of_boundaryAngleClosureDirectMatrix
  boundaryAngleClosureK23 :=
    TargetConsistencyFinalW11.target_of_boundaryAngleClosureK23Matrix
  boundaryAngleClosureCommonNeighbor :=
    TargetConsistencyFinalW11.target_of_boundaryAngleClosureCommonNeighborMatrix
  boundaryLabelClosure :=
    TargetConsistencyFinalW11.target_of_boundaryLabelClosureMatrix
  boundaryLabelIntegrated :=
    TargetConsistencyFinalW11.target_of_boundaryLabelIntegratedMatrix
  prefixNoEarly := TargetConsistencyFinalW11.target_of_prefixNoEarlyMatrix
  explicitNoEarly :=
    TargetConsistencyFinalW11.target_of_explicitNoEarlyMatrix
  explicitNoStart :=
    TargetConsistencyFinalW11.target_of_explicitNoStartMatrix
  geometryDirect := TargetConsistencyFinalW11.target_of_geometryDirectMatrix
  geometryK23 := TargetConsistencyFinalW11.target_of_geometryK23Matrix
  geometryCommonNeighbor :=
    TargetConsistencyFinalW11.target_of_geometryCommonNeighborMatrix
  brokenLatticeDirect :=
    TargetConsistencyFinalW11.target_of_brokenLatticeDirectFieldMatrix
  k23IntegratedBroad :=
    TargetConsistencyFinalW11.target_of_k23IntegratedMatrix
  commonNeighborIntegratedBroad :=
    TargetConsistencyFinalW11.target_of_commonNeighborIntegratedMatrix
  k23Target := TargetConsistencyFinalW11.target_of_k23TargetMatrix
  commonNeighborTarget :=
    TargetConsistencyFinalW11.target_of_commonNeighborTargetMatrix
  subpolygonDirect :=
    TargetConsistencyFinalW11.target_of_subpolygonDirectBoundaryGeometryMatrix
  targetIntegratedDirect :=
    TargetConsistencyFinalW11.target_of_targetIntegratedDirectFieldMatrix
  geometryDirectTarget :=
    TargetConsistencyFinalW11.target_of_geometryDirectTargetMatrix
  geometryK23Target :=
    TargetConsistencyFinalW11.target_of_geometryK23TargetMatrix
  geometryCommonNeighborTarget :=
    TargetConsistencyFinalW11.target_of_geometryCommonNeighborTargetMatrix
  k23ExplicitTarget :=
    TargetConsistencyFinalW11.target_of_k23ExplicitTargetMatrix
  commonNeighborExplicitTarget :=
    TargetConsistencyFinalW11.target_of_commonNeighborExplicitTargetMatrix
  noEarlyTarget := TargetConsistencyFinalW11.target_of_noEarlyTargetMatrix
  noStartTarget := TargetConsistencyFinalW11.target_of_noStartTargetMatrix
  noStartNoEarlyTarget :=
    TargetConsistencyFinalW11.target_of_noStartNoEarlyTargetMatrix

/-! ## Checked conditional route ledgers -/

/-- Route ledgers collected from all checked final W11 modules. -/
structure CheckedConditionalRouteLedgers : Type (u + 3) where
  targetConsistency :
    TargetConsistencyProjectionRoutes.{u}
  geometryFinal :
    GeometryFinalIntegratedW11.ConditionalSwanepoelTargetRoutes.{u}
  brokenLatticeFinal :
    BrokenLatticeFinalIntegratedW11.ConditionalSwanepoelTargetRoutes.{u}
  k23BrokenLatticeAggregate :
    K23BrokenLatticeFinalW11.K23CommonNeighborRoutes.{u}
  k23BrokenLatticeExplicit :
    K23BrokenLatticeFinalW11.ExplicitFieldRoutes.{u}
  boundaryLabelFinal :
    BoundaryLabelFinalIntegratedW11.ConditionalSwanepoelTargetRoutes.{u}
  noEarlyTargetFinal :
    NoEarlyTargetFinalW11.ConditionalRoutes.{u}

/-- All checked conditional route rows gathered by the aggregate. -/
def checkedConditionalRouteLedgers :
    CheckedConditionalRouteLedgers.{u} where
  targetConsistency := targetConsistencyProjectionRoutes
  geometryFinal := GeometryFinalIntegratedW11.conditionalSwanepoelTargetRoutes
  brokenLatticeFinal :=
    BrokenLatticeFinalIntegratedW11.conditionalSwanepoelTargetRoutes
  k23BrokenLatticeAggregate := K23BrokenLatticeFinalW11.k23CommonNeighborRoutes
  k23BrokenLatticeExplicit := K23BrokenLatticeFinalW11.explicitFieldRoutes
  boundaryLabelFinal :=
    BoundaryLabelFinalIntegratedW11.conditionalSwanepoelTargetRoutes
  noEarlyTargetFinal := NoEarlyTargetFinalW11.conditionalRoutes

/-! ## Aggregate matrix -/

/-- Final W11 aggregate ledger.

The record stores only ledgers, input matrix surfaces, and conditional route
rows.  It does not provide a target proof without one of the explicit input
matrices listed above.
-/
structure Matrix : Type (u + 3) where
  inputs : ExplicitInputMatrices.{u}
  routes : CheckedConditionalRouteLedgers.{u}

/-- The checked final W11 aggregate ledger. -/
def matrix : Matrix.{u} where
  inputs := explicitInputMatrices
  routes := checkedConditionalRouteLedgers

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

/-! ## Public conditional projections -/

theorem target_of_boundaryLabelFinalMatrix
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix M

theorem target_of_boundaryLabelFinalMatrix_via_noEarlyFinal
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_noEarlyFinal M

theorem target_of_boundaryLabelFinalMatrix_via_geometryTarget
    (M : BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_geometryTarget M

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

theorem target_of_brokenLatticeDirectFieldMatrix
    (M : BrokenLatticeFinalIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_directFieldMatrix
    M

theorem target_of_brokenLatticeK23FieldMatrix
    (M : BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_k23FieldMatrix
    M

theorem target_of_brokenLatticeCommonNeighborFieldMatrix
    (M : BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix
    M

theorem target_of_k23BrokenLatticeFields_via_direct
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  K23BrokenLatticeFinalW11.target_of_fields_via_direct M

theorem target_of_k23BrokenLatticeFields_via_k23Final
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  K23BrokenLatticeFinalW11.target_of_fields_via_k23Final M

theorem target_of_k23BrokenLatticeFields_via_commonNeighborFinal
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  K23BrokenLatticeFinalW11.target_of_fields_via_commonNeighborFinal M

theorem target_of_k23BrokenLatticeFields_via_k23BrokenLattice
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  K23BrokenLatticeFinalW11.target_of_fields_via_k23BrokenLattice M

theorem target_of_k23BrokenLatticeFields_via_commonNeighborBrokenLattice
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  K23BrokenLatticeFinalW11.target_of_fields_via_commonNeighborBrokenLattice M

theorem target_of_k23BrokenLatticeFields_via_k23TargetClosure
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  K23BrokenLatticeFinalW11.target_of_fields_via_k23TargetClosure M

theorem target_of_k23BrokenLatticeFields_via_commonNeighborTargetClosure
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  K23BrokenLatticeFinalW11.target_of_fields_via_commonNeighborTargetClosure M

theorem target_of_k23BrokenLatticeFields_via_k23Geometry
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  K23BrokenLatticeFinalW11.target_of_fields_via_k23Geometry M

theorem target_of_k23BrokenLatticeFields_via_commonNeighborGeometry
    (M : K23BrokenLatticeFinalW11.ExplicitFieldMatrices.{u}) :
    Target :=
  K23BrokenLatticeFinalW11.target_of_fields_via_commonNeighborGeometry M

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

end SwanepoelW11FinalAggregate
end Swanepoel
end ErdosProblems1066
