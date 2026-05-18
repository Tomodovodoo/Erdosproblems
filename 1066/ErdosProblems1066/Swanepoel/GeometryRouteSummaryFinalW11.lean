import ErdosProblems1066.Swanepoel.GeometryTargetFinalW11
import ErdosProblems1066.Swanepoel.GeometryFinalIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelTargetFinalAggregateW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalAggregate
import ErdosProblems1066.Swanepoel.SwanepoelRouteSummaryFinalW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 geometry route summary

This module is a compact geometry-only facade over the checked W11 route
ledgers.  The direct, K23, and common-neighbor inputs remain explicit, and all
target projections below require a caller-supplied matrix.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace GeometryRouteSummaryFinalW11

universe u

noncomputable section

abbrev Target : Prop :=
  GeometryTargetFinalW11.Target

abbrev MinimalFailureExclusion : Prop :=
  GeometryTargetFinalW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  GeometryTargetFinalW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  GeometryTargetFinalW11.MinimalFailureEliminator

abbrev DirectMatrix : Type (u + 1) :=
  GeometryTargetFinalW11.DirectMatrix.{u}

abbrev K23Matrix : Type (u + 1) :=
  GeometryTargetFinalW11.K23Matrix.{u}

abbrev CommonNeighborMatrix : Type (u + 1) :=
  GeometryTargetFinalW11.CommonNeighborMatrix.{u}

abbrev GeometryMatrixBundle : Type (u + 1) :=
  GeometryTargetFinalW11.ExplicitGeometryMatrices.{u}

/-! ## Explicit geometry matrices -/

/-- Explicit geometry matrix surfaces retained by this final summary. -/
structure ExplicitMatrices : Type (u + 3) where
  geometryTargetTypes :
    GeometryTargetFinalW11.ExplicitMatrixTypes.{u}
  geometryFinalFields :
    GeometryFinalIntegratedW11.ExplicitGeometryFieldLedger.{u}
  direct : Type (u + 1)
  k23 : Type (u + 1)
  commonNeighbor : Type (u + 1)
  allBranches : Type (u + 1)

/-- The displayed direct, K23, common-neighbor, and bundled matrix surfaces. -/
def explicitMatrices : ExplicitMatrices.{u} where
  geometryTargetTypes := GeometryTargetFinalW11.explicitMatrixTypes
  geometryFinalFields := GeometryFinalIntegratedW11.explicitGeometryFieldLedger
  direct := DirectMatrix.{u}
  k23 := K23Matrix.{u}
  commonNeighbor := CommonNeighborMatrix.{u}
  allBranches := GeometryMatrixBundle.{u}

/-! ## Conditional projection ledgers -/

/-- Conditional direct-geometry projections from a supplied matrix. -/
structure DirectProjections : Type (u + 1) where
  noMinimal : DirectMatrix.{u} -> MinimalFailureExclusion
  pipeline : DirectMatrix.{u} -> PipelineCleared
  geometryTargetFinal : DirectMatrix.{u} -> Target
  geometryTargetRoute : DirectMatrix.{u} -> Target
  brokenLatticeFinal : DirectMatrix.{u} -> Target
  targetConsistency : DirectMatrix.{u} -> Target
  geometryFinalIntegrated : DirectMatrix.{u} -> Target
  swanepoelFinalAggregate : DirectMatrix.{u} -> Target
  swanepoelRouteSummary : DirectMatrix.{u} -> Target

/-- Conditional K23-geometry projections from a supplied matrix. -/
structure K23Projections : Type (u + 1) where
  noMinimal : K23Matrix.{u} -> MinimalFailureExclusion
  pipeline : K23Matrix.{u} -> PipelineCleared
  geometryTargetFinal : K23Matrix.{u} -> Target
  geometryTargetRoute : K23Matrix.{u} -> Target
  brokenLatticeFinal : K23Matrix.{u} -> Target
  targetConsistency : K23Matrix.{u} -> Target
  explicitTargetConsistency : K23Matrix.{u} -> Target
  geometryFinalIntegrated : K23Matrix.{u} -> Target
  swanepoelFinalAggregate : K23Matrix.{u} -> Target
  swanepoelRouteSummary : K23Matrix.{u} -> Target

/-- Conditional common-neighbor geometry projections from a supplied matrix. -/
structure CommonNeighborProjections : Type (u + 1) where
  noMinimal : CommonNeighborMatrix.{u} -> MinimalFailureExclusion
  pipeline : CommonNeighborMatrix.{u} -> PipelineCleared
  geometryTargetFinal : CommonNeighborMatrix.{u} -> Target
  geometryTargetRoute : CommonNeighborMatrix.{u} -> Target
  brokenLatticeFinal : CommonNeighborMatrix.{u} -> Target
  targetConsistency : CommonNeighborMatrix.{u} -> Target
  explicitTargetConsistency : CommonNeighborMatrix.{u} -> Target
  geometryFinalIntegrated : CommonNeighborMatrix.{u} -> Target
  swanepoelFinalAggregate : CommonNeighborMatrix.{u} -> Target
  swanepoelRouteSummary : CommonNeighborMatrix.{u} -> Target

/-- Conditional projections from a bundle containing all geometry branches. -/
structure BundleProjections : Type (u + 1) where
  direct : GeometryMatrixBundle.{u} -> Target
  k23 : GeometryMatrixBundle.{u} -> Target
  commonNeighbor : GeometryMatrixBundle.{u} -> Target

/-- Checked direct route projections. -/
def directProjections : DirectProjections.{u} where
  noMinimal := GeometryTargetFinalW11.no_minimalClearedFailure_of_directMatrix
  pipeline := GeometryTargetFinalW11.pipelineCleared_of_directMatrix
  geometryTargetFinal := GeometryTargetFinalW11.target_of_directMatrix
  geometryTargetRoute :=
    GeometryTargetFinalW11.target_of_directMatrix_via_geometryTarget
  brokenLatticeFinal :=
    GeometryTargetFinalW11.target_of_directMatrix_via_brokenLatticeFinal
  targetConsistency :=
    GeometryTargetFinalW11.target_of_directMatrix_via_targetConsistency
  geometryFinalIntegrated :=
    GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix
  swanepoelFinalAggregate :=
    SwanepoelW11FinalAggregate.target_of_geometryDirectFinalMatrix
  swanepoelRouteSummary :=
    SwanepoelRouteSummaryFinalW11.target_of_geometryDirectFinalMatrix

/-- Checked K23 route projections. -/
def k23Projections : K23Projections.{u} where
  noMinimal := GeometryTargetFinalW11.no_minimalClearedFailure_of_k23Matrix
  pipeline := GeometryTargetFinalW11.pipelineCleared_of_k23Matrix
  geometryTargetFinal := GeometryTargetFinalW11.target_of_k23Matrix
  geometryTargetRoute :=
    GeometryTargetFinalW11.target_of_k23Matrix_via_geometryTarget
  brokenLatticeFinal :=
    GeometryTargetFinalW11.target_of_k23Matrix_via_brokenLatticeFinal
  targetConsistency :=
    GeometryTargetFinalW11.target_of_k23Matrix_via_targetConsistency
  explicitTargetConsistency :=
    GeometryTargetFinalW11.target_of_k23Matrix_via_explicitTargetConsistency
  geometryFinalIntegrated :=
    GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix
  swanepoelFinalAggregate :=
    SwanepoelW11FinalAggregate.target_of_geometryK23FinalMatrix
  swanepoelRouteSummary :=
    SwanepoelRouteSummaryFinalW11.target_of_geometryK23FinalMatrix

/-- Checked common-neighbor route projections. -/
def commonNeighborProjections : CommonNeighborProjections.{u} where
  noMinimal :=
    GeometryTargetFinalW11.no_minimalClearedFailure_of_commonNeighborMatrix
  pipeline := GeometryTargetFinalW11.pipelineCleared_of_commonNeighborMatrix
  geometryTargetFinal := GeometryTargetFinalW11.target_of_commonNeighborMatrix
  geometryTargetRoute :=
    GeometryTargetFinalW11.target_of_commonNeighborMatrix_via_geometryTarget
  brokenLatticeFinal :=
    GeometryTargetFinalW11.target_of_commonNeighborMatrix_via_brokenLatticeFinal
  targetConsistency :=
    GeometryTargetFinalW11.target_of_commonNeighborMatrix_via_targetConsistency
  explicitTargetConsistency :=
    GeometryTargetFinalW11.target_of_commonNeighborMatrix_via_explicitTargetConsistency
  geometryFinalIntegrated :=
    GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix
  swanepoelFinalAggregate :=
    SwanepoelW11FinalAggregate.target_of_geometryCommonNeighborFinalMatrix
  swanepoelRouteSummary :=
    SwanepoelRouteSummaryFinalW11.target_of_geometryCommonNeighborFinalMatrix

/-- Checked projections from a supplied three-branch geometry bundle. -/
def bundleProjections : BundleProjections.{u} where
  direct := GeometryTargetFinalW11.target_of_explicitGeometryMatrices_via_direct
  k23 := GeometryTargetFinalW11.target_of_explicitGeometryMatrices_via_k23
  commonNeighbor :=
    GeometryTargetFinalW11.target_of_explicitGeometryMatrices_via_commonNeighbor

/-- Geometry projections summarized by branch. -/
structure ConditionalProjections : Type (u + 1) where
  direct : DirectProjections.{u}
  k23 : K23Projections.{u}
  commonNeighbor : CommonNeighborProjections.{u}
  bundle : BundleProjections.{u}

/-- Checked conditional projections summarized by branch. -/
def conditionalProjections : ConditionalProjections.{u} where
  direct := directProjections
  k23 := k23Projections
  commonNeighbor := commonNeighborProjections
  bundle := bundleProjections

/-! ## Final summary matrix -/

/-- Final W11 geometry route summary matrix. -/
structure Matrix : Type (u + 3) where
  explicit : ExplicitMatrices.{u}
  projections : ConditionalProjections.{u}

/-- The checked final W11 geometry route summary. -/
def matrix : Matrix.{u} where
  explicit := explicitMatrices
  projections := conditionalProjections

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

/-! ## Public conditional projections -/

theorem no_minimalClearedFailure_of_directMatrix
    (M : DirectMatrix.{u}) :
    MinimalFailureExclusion :=
  directProjections.noMinimal M

theorem pipelineCleared_of_directMatrix
    (M : DirectMatrix.{u}) :
    PipelineCleared :=
  directProjections.pipeline M

theorem target_of_directMatrix
    (M : DirectMatrix.{u}) :
    Target :=
  directProjections.geometryTargetFinal M

theorem target_of_directMatrix_via_geometryTarget
    (M : DirectMatrix.{u}) :
    Target :=
  directProjections.geometryTargetRoute M

theorem target_of_directMatrix_via_brokenLatticeFinal
    (M : DirectMatrix.{u}) :
    Target :=
  directProjections.brokenLatticeFinal M

theorem target_of_directMatrix_via_targetConsistency
    (M : DirectMatrix.{u}) :
    Target :=
  directProjections.targetConsistency M

theorem target_of_directMatrix_via_geometryFinalIntegrated
    (M : DirectMatrix.{u}) :
    Target :=
  directProjections.geometryFinalIntegrated M

theorem target_of_directMatrix_via_swanepoelFinalAggregate
    (M : DirectMatrix.{u}) :
    Target :=
  directProjections.swanepoelFinalAggregate M

theorem target_of_directMatrix_via_swanepoelRouteSummary
    (M : DirectMatrix.{u}) :
    Target :=
  directProjections.swanepoelRouteSummary M

theorem no_minimalClearedFailure_of_k23Matrix
    (M : K23Matrix.{u}) :
    MinimalFailureExclusion :=
  k23Projections.noMinimal M

theorem pipelineCleared_of_k23Matrix
    (M : K23Matrix.{u}) :
    PipelineCleared :=
  k23Projections.pipeline M

theorem target_of_k23Matrix
    (M : K23Matrix.{u}) :
    Target :=
  k23Projections.geometryTargetFinal M

theorem target_of_k23Matrix_via_geometryTarget
    (M : K23Matrix.{u}) :
    Target :=
  k23Projections.geometryTargetRoute M

theorem target_of_k23Matrix_via_brokenLatticeFinal
    (M : K23Matrix.{u}) :
    Target :=
  k23Projections.brokenLatticeFinal M

theorem target_of_k23Matrix_via_targetConsistency
    (M : K23Matrix.{u}) :
    Target :=
  k23Projections.targetConsistency M

theorem target_of_k23Matrix_via_explicitTargetConsistency
    (M : K23Matrix.{u}) :
    Target :=
  k23Projections.explicitTargetConsistency M

theorem target_of_k23Matrix_via_geometryFinalIntegrated
    (M : K23Matrix.{u}) :
    Target :=
  k23Projections.geometryFinalIntegrated M

theorem target_of_k23Matrix_via_swanepoelFinalAggregate
    (M : K23Matrix.{u}) :
    Target :=
  k23Projections.swanepoelFinalAggregate M

theorem target_of_k23Matrix_via_swanepoelRouteSummary
    (M : K23Matrix.{u}) :
    Target :=
  k23Projections.swanepoelRouteSummary M

theorem no_minimalClearedFailure_of_commonNeighborMatrix
    (M : CommonNeighborMatrix.{u}) :
    MinimalFailureExclusion :=
  commonNeighborProjections.noMinimal M

theorem pipelineCleared_of_commonNeighborMatrix
    (M : CommonNeighborMatrix.{u}) :
    PipelineCleared :=
  commonNeighborProjections.pipeline M

theorem target_of_commonNeighborMatrix
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  commonNeighborProjections.geometryTargetFinal M

theorem target_of_commonNeighborMatrix_via_geometryTarget
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  commonNeighborProjections.geometryTargetRoute M

theorem target_of_commonNeighborMatrix_via_brokenLatticeFinal
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  commonNeighborProjections.brokenLatticeFinal M

theorem target_of_commonNeighborMatrix_via_targetConsistency
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  commonNeighborProjections.targetConsistency M

theorem target_of_commonNeighborMatrix_via_explicitTargetConsistency
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  commonNeighborProjections.explicitTargetConsistency M

theorem target_of_commonNeighborMatrix_via_geometryFinalIntegrated
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  commonNeighborProjections.geometryFinalIntegrated M

theorem target_of_commonNeighborMatrix_via_swanepoelFinalAggregate
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  commonNeighborProjections.swanepoelFinalAggregate M

theorem target_of_commonNeighborMatrix_via_swanepoelRouteSummary
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  commonNeighborProjections.swanepoelRouteSummary M

theorem target_of_geometryBundle_via_direct
    (M : GeometryMatrixBundle.{u}) :
    Target :=
  bundleProjections.direct M

theorem target_of_geometryBundle_via_k23
    (M : GeometryMatrixBundle.{u}) :
    Target :=
  bundleProjections.k23 M

theorem target_of_geometryBundle_via_commonNeighbor
    (M : GeometryMatrixBundle.{u}) :
    Target :=
  bundleProjections.commonNeighbor M

theorem target_of_targetAggregateFinalBranches_via_geometryDirect
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_geometryTarget_direct M

theorem target_of_targetAggregateFinalBranches_via_geometryK23
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_geometryTarget_k23 M

theorem target_of_targetAggregateFinalBranches_via_geometryCommonNeighbor
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_geometryTarget_commonNeighbor M

end

end GeometryRouteSummaryFinalW11
end Swanepoel
end ErdosProblems1066
