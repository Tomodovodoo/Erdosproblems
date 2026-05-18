import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11
import ErdosProblems1066.Swanepoel.SwanepoelW11IntegratedMatrix
import ErdosProblems1066.Swanepoel.GeometryIntegratedW11
import ErdosProblems1066.Swanepoel.K23IntegratedMatrixW11
import ErdosProblems1066.Swanepoel.NoEarlyIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 target ledger consistency

This file is a typed ledger for the W11 Swanepoel target-route layers.  It
assembles only checked conditional routes and keeps the source matrices needed
to use those routes as explicit data.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TargetLedgerConsistencyW11

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

/-! ## Import and source-status ledger -/

/-- Status for an integration layer.  The checked constructor stores the
imported ledger; the blocked constructor is available for future ledgers whose
integration cannot yet be imported. -/
inductive IntegrationStatus (alpha : Type u) : Type u where
  | checked (value : alpha) : IntegrationStatus alpha
  | blocked (routeName : String) (detail : String) : IntegrationStatus alpha

/-- Imported W11 layers used by this consistency ledger. -/
structure CheckedModuleStatus : Type (u + 1) where
  targetClosure :
    IntegrationStatus (TargetClosureMatrixW11.Matrix.{u})
  targetIntegrated :
    IntegrationStatus (TargetIntegratedMatrixW11.Matrix.{u})
  swanepoelIntegrated :
    IntegrationStatus (SwanepoelW11IntegratedMatrix.Matrix.{u})
  geometryIntegrated :
    IntegrationStatus (GeometryIntegratedW11.Matrix.{u})
  k23Integrated :
    IntegrationStatus (K23IntegratedMatrixW11.Matrix.{u})
  noEarlyIntegrated :
    IntegrationStatus (NoEarlyIntegratedW11.Matrix.{u})

/-- All optional W11 layers requested by the ledger check in this tree. -/
def checkedModuleStatus : CheckedModuleStatus.{u} where
  targetClosure :=
    IntegrationStatus.checked TargetClosureMatrixW11.matrix
  targetIntegrated :=
    IntegrationStatus.checked TargetIntegratedMatrixW11.matrix
  swanepoelIntegrated :=
    IntegrationStatus.checked SwanepoelW11IntegratedMatrix.matrix
  geometryIntegrated :=
    IntegrationStatus.checked GeometryIntegratedW11.matrix
  k23Integrated :=
    IntegrationStatus.checked K23IntegratedMatrixW11.matrix
  noEarlyIntegrated :=
    IntegrationStatus.checked NoEarlyIntegratedW11.matrix

/-- Source packages that remain external inputs to the checked route rows. -/
structure OpenInputLedger : Type (u + 2) where
  directFieldMatrix : Type (u + 1)
  k23FieldMatrix : Type (u + 1)
  commonNeighborFieldMatrix : Type (u + 1)
  noEarlyRows : Type (u + 1)
  noStartRows : Type (u + 1)
  directGeometryMatrix : Type (u + 1)
  k23GeometryMatrix : Type (u + 1)
  commonNeighborGeometryMatrix : Type (u + 1)
  k23IntegratedMatrix : Type (u + 1)
  commonNeighborIntegratedMatrix : Type (u + 1)
  prefixNoEarlyMatrix : Type (u + 1)
  prefixNoStartMatrix : Type (u + 1)

/-- The still-open input packages, recorded as fields rather than prose. -/
def openInputLedger : OpenInputLedger.{u} where
  directFieldMatrix :=
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}
  k23FieldMatrix :=
    BrokenLatticeIntegratedW11.K23FieldMatrix.{u}
  commonNeighborFieldMatrix :=
    BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}
  noEarlyRows :=
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u}
  noStartRows :=
    WindowNoEarlyRowsW11.NoStartMatrix.{u}
  directGeometryMatrix :=
    GeometryIntegratedW11.DirectGeometryMatrix.{u}
  k23GeometryMatrix :=
    GeometryIntegratedW11.K23GeometryMatrix.{u}
  commonNeighborGeometryMatrix :=
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u}
  k23IntegratedMatrix :=
    K23IntegratedMatrixW11.K23IntegratedMatrix.{u}
  commonNeighborIntegratedMatrix :=
    K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u}
  prefixNoEarlyMatrix :=
    NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}
  prefixNoStartMatrix :=
    NoEarlyIntegratedW11.PrefixNoStartMatrix.{u}

/-! ## Checked target-route ledger -/

/-- Flat list of checked target-route records imported by the W11 ledgers. -/
structure CheckedTargetRoutes : Type (u + 1) where
  targetClosure :
    TargetClosureMatrixW11.Matrix.{u}
  swanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.TargetRouteLedger.{u}
  targetIntegrated :
    TargetIntegratedMatrixW11.SourceFacingTargetRoutes.{u}
  directGeometry :
    GeometryIntegratedW11.GeometryProjectionRow
      (GeometryIntegratedW11.DirectGeometryMatrix.{u})
  k23Geometry :
    GeometryIntegratedW11.GeometryProjectionRow
      (GeometryIntegratedW11.K23GeometryMatrix.{u})
  commonNeighborGeometry :
    GeometryIntegratedW11.GeometryProjectionRow
      (GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u})
  k23Integrated :
    SwanepoelW11ClosureMatrix.TargetProjectionRow
      (K23IntegratedMatrixW11.K23IntegratedMatrix.{u})
  commonNeighborIntegrated :
    SwanepoelW11ClosureMatrix.TargetProjectionRow
      (K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u})

/-- The checked target routes available after importing the W11 layers. -/
def checkedTargetRoutes : CheckedTargetRoutes.{u} where
  targetClosure :=
    TargetClosureMatrixW11.matrix
  swanepoelIntegrated :=
    SwanepoelW11IntegratedMatrix.targetRouteLedger
  targetIntegrated :=
    TargetIntegratedMatrixW11.sourceFacingTargetRoutes
  directGeometry :=
    GeometryIntegratedW11.directGeometryProjectionRow
  k23Geometry :=
    GeometryIntegratedW11.k23GeometryProjectionRow
  commonNeighborGeometry :=
    GeometryIntegratedW11.commonNeighborGeometryProjectionRow
  k23Integrated :=
    K23IntegratedMatrixW11.k23IntegratedMatrixRow
  commonNeighborIntegrated :=
    K23IntegratedMatrixW11.commonNeighborIntegratedMatrixRow

/-! ## Checked non-target adapters -/

/-- No-early prefix integrations that check but are recorded here only through
their non-target projections and adapters. -/
structure PrefixAdapterLedger : Type (u + 1) where
  noEarlyIntegrated :
    NoEarlyIntegratedW11.Matrix.{u}
  prefixNoEarlyNoMinimal :
    NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u} ->
      MinimalFailureExclusion
  prefixNoEarlyPipeline :
    NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u} ->
      PipelineCleared
  prefixNoStartNoMinimal :
    NoEarlyIntegratedW11.PrefixNoStartMatrix.{u} ->
      MinimalFailureExclusion
  prefixNoStartPipeline :
    NoEarlyIntegratedW11.PrefixNoStartMatrix.{u} ->
      PipelineCleared
  prefixNoEarlyToRows :
    NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u} ->
      WindowNoEarlyRowsW11.NoEarlyMatrix.{u}
  prefixNoStartToRows :
    NoEarlyIntegratedW11.PrefixNoStartMatrix.{u} ->
      WindowNoEarlyRowsW11.NoStartMatrix.{u}

/-- Checked prefix adapters from `NoEarlyIntegratedW11`. -/
def prefixAdapterLedger : PrefixAdapterLedger.{u} where
  noEarlyIntegrated :=
    NoEarlyIntegratedW11.matrix
  prefixNoEarlyNoMinimal :=
    fun M =>
      NoEarlyIntegratedW11.no_minimalClearedFailure_of_prefixNoEarlyMatrix M
  prefixNoEarlyPipeline :=
    fun M =>
      NoEarlyIntegratedW11.pipelineCleared_of_prefixNoEarlyMatrix M
  prefixNoStartNoMinimal :=
    fun M =>
      NoEarlyIntegratedW11.no_minimalClearedFailure_of_prefixNoStartMatrix M
  prefixNoStartPipeline :=
    fun M =>
      NoEarlyIntegratedW11.pipelineCleared_of_prefixNoStartMatrix M
  prefixNoEarlyToRows :=
    fun M =>
      NoEarlyIntegratedW11.PrefixNoEarlyMatrix.toW11NoEarlyMatrix M
  prefixNoStartToRows :=
    fun M =>
      NoEarlyIntegratedW11.PrefixNoStartMatrix.toW11NoStartMatrix M

/-! ## Consistency matrix -/

/-- Consistency matrix for the W11 target ledgers.

It records checked imports, checked target routes, non-target prefix adapters,
and the external source packages still needed to instantiate those routes. -/
structure Matrix : Type (u + 2) where
  modules : CheckedModuleStatus.{u}
  routes : CheckedTargetRoutes.{u}
  prefixAdapters : PrefixAdapterLedger.{u}
  openInputs : OpenInputLedger.{u}

/-- The checked W11 target-ledger consistency matrix. -/
def matrix : Matrix.{u} where
  modules := checkedModuleStatus
  routes := checkedTargetRoutes
  prefixAdapters := prefixAdapterLedger
  openInputs := openInputLedger

/-! ## Public conditional projections -/

theorem target_of_directFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix M

theorem target_of_k23FieldMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_k23FieldMatrix M

theorem target_of_commonNeighborFieldMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_commonNeighborFieldMatrix M

theorem target_of_noEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noEarlyMatrix M

theorem target_of_noStartMatrix
    (M : WindowNoEarlyRowsW11.NoStartMatrix.{u, u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noStartMatrix M

theorem target_of_directGeometryMatrix
    (M : GeometryIntegratedW11.DirectGeometryMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    M

theorem target_of_k23GeometryMatrix
    (M : GeometryIntegratedW11.K23GeometryMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    M

theorem target_of_commonNeighborGeometryMatrix
    (M : GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    M

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

theorem no_minimalClearedFailure_of_prefixNoEarlyMatrix
    (M : NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}) :
    MinimalFailureExclusion :=
  NoEarlyIntegratedW11.no_minimalClearedFailure_of_prefixNoEarlyMatrix
    M

theorem pipelineCleared_of_prefixNoEarlyMatrix
    (M : NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}) :
    PipelineCleared :=
  NoEarlyIntegratedW11.pipelineCleared_of_prefixNoEarlyMatrix M

theorem no_minimalClearedFailure_of_prefixNoStartMatrix
    (M : NoEarlyIntegratedW11.PrefixNoStartMatrix.{u}) :
    MinimalFailureExclusion :=
  NoEarlyIntegratedW11.no_minimalClearedFailure_of_prefixNoStartMatrix
    M

theorem pipelineCleared_of_prefixNoStartMatrix
    (M : NoEarlyIntegratedW11.PrefixNoStartMatrix.{u}) :
    PipelineCleared :=
  NoEarlyIntegratedW11.pipelineCleared_of_prefixNoStartMatrix M

end

end TargetLedgerConsistencyW11
end Swanepoel
end ErdosProblems1066
