import ErdosProblems1066.Swanepoel.GeometryFinalIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryTargetIntegratedW11
import ErdosProblems1066.Swanepoel.BrokenLatticeFinalIntegratedW11
import ErdosProblems1066.Swanepoel.K23FinalIntegratedW11
import ErdosProblems1066.Swanepoel.TargetConsistencyFinalW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalAggregate

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 geometry target consistency layer

This module is a final read-only facade over the checked W11 geometry,
broken-lattice, K23/common-neighbor, and target-consistency ledgers.

The direct, K23, and common-neighbor matrices stay explicit throughout.  Every
target route below is conditional on one of those caller-supplied matrices.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace GeometryTargetFinalW11

universe u v

noncomputable section

abbrev Target : Prop :=
  TargetConsistencyFinalW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetConsistencyFinalW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetConsistencyFinalW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  TargetConsistencyFinalW11.MinimalFailureEliminator

abbrev DirectMatrix :=
  GeometryFinalIntegratedW11.DirectFinalGeometryMatrix

abbrev K23Matrix :=
  GeometryFinalIntegratedW11.K23FinalGeometryMatrix

abbrev CommonNeighborMatrix :=
  GeometryFinalIntegratedW11.CommonNeighborFinalGeometryMatrix

abbrev K23CommonNeighborMatrix :=
  K23FinalIntegratedW11.K23CommonNeighborFinalMatrix

/-! ## Shared route shapes -/

/-- A checked conditional route from an explicit matrix to the target. -/
structure TargetRoute (alpha : Type v) : Type v where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

/-- A checked conditional route that also exposes the eliminator. -/
structure EliminatorTargetRoute (alpha : Type v) : Type v where
  eliminator : alpha -> MinimalFailureEliminator
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace EliminatorTargetRoute

/-- Forget the eliminator and keep the target-facing route. -/
def toTargetRoute
    {alpha : Type v}
    (R : EliminatorTargetRoute alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end EliminatorTargetRoute

/-! ## Explicit matrix surfaces -/

/-- Explicit matrix types displayed by the final geometry target layer. -/
structure ExplicitMatrixTypes : Type (u + 2) where
  direct : Type (u + 1)
  k23 : Type (u + 1)
  commonNeighbor : Type (u + 1)
  geometryTargetDirect : Type (u + 1)
  geometryTargetK23 : Type (u + 1)
  geometryTargetCommonNeighbor : Type (u + 1)
  brokenLatticeDirect : Type (u + 1)
  brokenLatticeK23 : Type (u + 1)
  brokenLatticeCommonNeighbor : Type (u + 1)
  k23CommonNeighbor : Type (u + 1)

/-- The concrete explicit matrix types used by this facade. -/
def explicitMatrixTypes : ExplicitMatrixTypes.{u} where
  direct := DirectMatrix.{u}
  k23 := K23Matrix.{u}
  commonNeighbor := CommonNeighborMatrix.{u}
  geometryTargetDirect := GeometryTargetIntegratedW11.DirectTargetMatrix.{u}
  geometryTargetK23 := GeometryTargetIntegratedW11.K23TargetMatrix.{u}
  geometryTargetCommonNeighbor :=
    GeometryTargetIntegratedW11.CommonNeighborTargetMatrix.{u}
  brokenLatticeDirect := BrokenLatticeFinalIntegratedW11.DirectFieldMatrix.{u}
  brokenLatticeK23 := BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u}
  brokenLatticeCommonNeighbor :=
    BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u}
  k23CommonNeighbor := K23CommonNeighborMatrix.{u}

/-- A caller-supplied bundle of the three geometry alternatives. -/
structure ExplicitGeometryMatrices : Type (u + 1) where
  direct : DirectMatrix.{u}
  k23 : K23Matrix.{u}
  commonNeighbor : CommonNeighborMatrix.{u}

/-! ## Direct routes -/

def directFinalRoute :
    EliminatorTargetRoute (DirectMatrix.{u}) where
  eliminator :=
    GeometryFinalIntegratedW11.minimalClearedFailureEliminator_of_directFinalGeometryMatrix
  noMinimal :=
    GeometryFinalIntegratedW11.no_minimalClearedFailure_of_directFinalGeometryMatrix
  pipeline :=
    GeometryFinalIntegratedW11.pipelineCleared_of_directFinalGeometryMatrix
  target :=
    GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix

def directGeometryTargetRoute :
    EliminatorTargetRoute (DirectMatrix.{u}) where
  eliminator := fun M =>
    GeometryTargetIntegratedW11.minimalClearedFailureEliminator_of_directTargetMatrix
      M.toGeometryTargetMatrix
  noMinimal := fun M =>
    GeometryTargetIntegratedW11.no_minimalClearedFailure_of_directTargetMatrix
      M.toGeometryTargetMatrix
  pipeline := fun M =>
    GeometryTargetIntegratedW11.pipelineCleared_of_directTargetMatrix
      M.toGeometryTargetMatrix
  target := fun M =>
    GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_directTargetMatrix
      M.toGeometryTargetMatrix

def directBrokenLatticeFinalRoute :
    EliminatorTargetRoute (DirectMatrix.{u}) where
  eliminator := fun M =>
    BrokenLatticeFinalIntegratedW11.minimalClearedFailureEliminator_of_directFieldMatrix
      M.toBrokenLatticeFieldMatrix
  noMinimal := fun M =>
    BrokenLatticeFinalIntegratedW11.no_minimalClearedFailure_of_directFieldMatrix
      M.toBrokenLatticeFieldMatrix
  pipeline := fun M =>
    BrokenLatticeFinalIntegratedW11.pipelineCleared_of_directFieldMatrix
      M.toBrokenLatticeFieldMatrix
  target := fun M =>
    BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_directFieldMatrix
      M.toBrokenLatticeFieldMatrix

def directTargetConsistencyRoute :
    TargetRoute (DirectMatrix.{u}) where
  noMinimal := fun M =>
    GeometryTargetIntegratedW11.no_minimalClearedFailure_of_directTargetMatrix
      M.toGeometryTargetMatrix
  pipeline := fun M =>
    GeometryTargetIntegratedW11.pipelineCleared_of_directTargetMatrix
      M.toGeometryTargetMatrix
  target := fun M =>
    TargetConsistencyFinalW11.target_of_geometryDirectTargetMatrix
      M.toGeometryTargetMatrix

def directFinalAggregateRoute :
    TargetRoute (DirectMatrix.{u}) where
  noMinimal :=
    GeometryFinalIntegratedW11.no_minimalClearedFailure_of_directFinalGeometryMatrix
  pipeline :=
    GeometryFinalIntegratedW11.pipelineCleared_of_directFinalGeometryMatrix
  target :=
    SwanepoelW11FinalAggregate.target_of_geometryDirectFinalMatrix

/-! ## K23 routes -/

def k23FinalRoute :
    EliminatorTargetRoute (K23Matrix.{u}) where
  eliminator :=
    GeometryFinalIntegratedW11.minimalClearedFailureEliminator_of_k23FinalGeometryMatrix
  noMinimal :=
    GeometryFinalIntegratedW11.no_minimalClearedFailure_of_k23FinalGeometryMatrix
  pipeline :=
    GeometryFinalIntegratedW11.pipelineCleared_of_k23FinalGeometryMatrix
  target :=
    GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix

def k23GeometryTargetRoute :
    EliminatorTargetRoute (K23Matrix.{u}) where
  eliminator := fun M =>
    GeometryTargetIntegratedW11.minimalClearedFailureEliminator_of_k23TargetMatrix
      M.toGeometryTargetMatrix
  noMinimal := fun M =>
    GeometryTargetIntegratedW11.no_minimalClearedFailure_of_k23TargetMatrix
      M.toGeometryTargetMatrix
  pipeline := fun M =>
    GeometryTargetIntegratedW11.pipelineCleared_of_k23TargetMatrix
      M.toGeometryTargetMatrix
  target := fun M =>
    GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_k23TargetMatrix
      M.toGeometryTargetMatrix

def k23BrokenLatticeFinalRoute :
    EliminatorTargetRoute (K23Matrix.{u}) where
  eliminator := fun M =>
    BrokenLatticeFinalIntegratedW11.minimalClearedFailureEliminator_of_k23FieldMatrix
      M.toBrokenLatticeFieldMatrix
  noMinimal := fun M =>
    BrokenLatticeFinalIntegratedW11.no_minimalClearedFailure_of_k23FieldMatrix
      M.toBrokenLatticeFieldMatrix
  pipeline := fun M =>
    BrokenLatticeFinalIntegratedW11.pipelineCleared_of_k23FieldMatrix
      M.toBrokenLatticeFieldMatrix
  target := fun M =>
    BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_k23FieldMatrix
      M.toBrokenLatticeFieldMatrix

def k23TargetConsistencyRoute :
    TargetRoute (K23Matrix.{u}) where
  noMinimal := fun M =>
    GeometryTargetIntegratedW11.no_minimalClearedFailure_of_k23TargetMatrix
      M.toGeometryTargetMatrix
  pipeline := fun M =>
    GeometryTargetIntegratedW11.pipelineCleared_of_k23TargetMatrix
      M.toGeometryTargetMatrix
  target := fun M =>
    TargetConsistencyFinalW11.target_of_geometryK23TargetMatrix
      M.toGeometryTargetMatrix

def k23ExplicitTargetConsistencyRoute :
    EliminatorTargetRoute (K23Matrix.{u}) where
  eliminator := fun M =>
    K23TargetIntegratedW11.minimalClearedFailureEliminator_of_k23TargetMatrix
      M.toK23TargetMatrix
  noMinimal := fun M =>
    K23TargetIntegratedW11.no_minimalClearedFailure_of_k23TargetMatrix
      M.toK23TargetMatrix
  pipeline := fun M =>
    K23TargetIntegratedW11.pipelineCleared_of_k23TargetMatrix
      M.toK23TargetMatrix
  target := fun M =>
    TargetConsistencyFinalW11.target_of_k23ExplicitTargetMatrix
      M.toK23TargetMatrix

def k23FinalAggregateRoute :
    TargetRoute (K23Matrix.{u}) where
  noMinimal :=
    GeometryFinalIntegratedW11.no_minimalClearedFailure_of_k23FinalGeometryMatrix
  pipeline :=
    GeometryFinalIntegratedW11.pipelineCleared_of_k23FinalGeometryMatrix
  target :=
    SwanepoelW11FinalAggregate.target_of_geometryK23FinalMatrix

/-! ## Common-neighbor routes -/

def commonNeighborFinalRoute :
    EliminatorTargetRoute (CommonNeighborMatrix.{u}) where
  eliminator :=
    GeometryFinalIntegratedW11.minimalClearedFailureEliminator_of_commonNeighborFinalGeometryMatrix
  noMinimal :=
    GeometryFinalIntegratedW11.no_minimalClearedFailure_of_commonNeighborFinalGeometryMatrix
  pipeline :=
    GeometryFinalIntegratedW11.pipelineCleared_of_commonNeighborFinalGeometryMatrix
  target :=
    GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix

def commonNeighborGeometryTargetRoute :
    EliminatorTargetRoute (CommonNeighborMatrix.{u}) where
  eliminator := fun M =>
    GeometryTargetIntegratedW11.minimalClearedFailureEliminator_of_commonNeighborTargetMatrix
      M.toGeometryTargetMatrix
  noMinimal := fun M =>
    GeometryTargetIntegratedW11.no_minimalClearedFailure_of_commonNeighborTargetMatrix
      M.toGeometryTargetMatrix
  pipeline := fun M =>
    GeometryTargetIntegratedW11.pipelineCleared_of_commonNeighborTargetMatrix
      M.toGeometryTargetMatrix
  target := fun M =>
    GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
      M.toGeometryTargetMatrix

def commonNeighborBrokenLatticeFinalRoute :
    EliminatorTargetRoute (CommonNeighborMatrix.{u}) where
  eliminator := fun M =>
    BrokenLatticeFinalIntegratedW11.minimalClearedFailureEliminator_of_commonNeighborFieldMatrix
      M.toBrokenLatticeFieldMatrix
  noMinimal := fun M =>
    BrokenLatticeFinalIntegratedW11.no_minimalClearedFailure_of_commonNeighborFieldMatrix
      M.toBrokenLatticeFieldMatrix
  pipeline := fun M =>
    BrokenLatticeFinalIntegratedW11.pipelineCleared_of_commonNeighborFieldMatrix
      M.toBrokenLatticeFieldMatrix
  target := fun M =>
    BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix
      M.toBrokenLatticeFieldMatrix

def commonNeighborTargetConsistencyRoute :
    TargetRoute (CommonNeighborMatrix.{u}) where
  noMinimal := fun M =>
    GeometryTargetIntegratedW11.no_minimalClearedFailure_of_commonNeighborTargetMatrix
      M.toGeometryTargetMatrix
  pipeline := fun M =>
    GeometryTargetIntegratedW11.pipelineCleared_of_commonNeighborTargetMatrix
      M.toGeometryTargetMatrix
  target := fun M =>
    TargetConsistencyFinalW11.target_of_geometryCommonNeighborTargetMatrix
      M.toGeometryTargetMatrix

def commonNeighborExplicitTargetConsistencyRoute :
    EliminatorTargetRoute (CommonNeighborMatrix.{u}) where
  eliminator := fun M =>
    K23TargetIntegratedW11.minimalClearedFailureEliminator_of_commonNeighborTargetMatrix
      M.toK23TargetMatrix
  noMinimal := fun M =>
    K23TargetIntegratedW11.no_minimalClearedFailure_of_commonNeighborTargetMatrix
      M.toK23TargetMatrix
  pipeline := fun M =>
    K23TargetIntegratedW11.pipelineCleared_of_commonNeighborTargetMatrix
      M.toK23TargetMatrix
  target := fun M =>
    TargetConsistencyFinalW11.target_of_commonNeighborExplicitTargetMatrix
      M.toK23TargetMatrix

def commonNeighborFinalAggregateRoute :
    TargetRoute (CommonNeighborMatrix.{u}) where
  noMinimal :=
    GeometryFinalIntegratedW11.no_minimalClearedFailure_of_commonNeighborFinalGeometryMatrix
  pipeline :=
    GeometryFinalIntegratedW11.pipelineCleared_of_commonNeighborFinalGeometryMatrix
  target :=
    SwanepoelW11FinalAggregate.target_of_geometryCommonNeighborFinalMatrix

/-! ## K23/common-neighbor aggregate routes -/

def k23CommonNeighborViaK23Route :
    EliminatorTargetRoute (K23CommonNeighborMatrix.{u}) where
  eliminator :=
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.minimalClearedFailureEliminator_via_k23
  noMinimal :=
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.no_minimalClearedFailure_via_k23
  pipeline :=
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.pipelineCleared_via_k23
  target :=
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.targetLowerBoundEightThirtyOne_via_k23

def k23CommonNeighborViaCommonNeighborRoute :
    EliminatorTargetRoute (K23CommonNeighborMatrix.{u}) where
  eliminator :=
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.minimalClearedFailureEliminator_via_commonNeighbor
  noMinimal :=
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.no_minimalClearedFailure_via_commonNeighbor
  pipeline :=
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.pipelineCleared_via_commonNeighbor
  target :=
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.targetLowerBoundEightThirtyOne_via_commonNeighbor

/-! ## Final route ledgers -/

structure DirectRoutes : Type (u + 1) where
  finalGeometry : EliminatorTargetRoute (DirectMatrix.{u})
  geometryTarget : EliminatorTargetRoute (DirectMatrix.{u})
  brokenLatticeFinal : EliminatorTargetRoute (DirectMatrix.{u})
  targetConsistency : TargetRoute (DirectMatrix.{u})
  finalAggregate : TargetRoute (DirectMatrix.{u})

def directRoutes : DirectRoutes.{u} where
  finalGeometry := directFinalRoute
  geometryTarget := directGeometryTargetRoute
  brokenLatticeFinal := directBrokenLatticeFinalRoute
  targetConsistency := directTargetConsistencyRoute
  finalAggregate := directFinalAggregateRoute

structure K23Routes : Type (u + 1) where
  finalGeometry : EliminatorTargetRoute (K23Matrix.{u})
  geometryTarget : EliminatorTargetRoute (K23Matrix.{u})
  brokenLatticeFinal : EliminatorTargetRoute (K23Matrix.{u})
  targetConsistency : TargetRoute (K23Matrix.{u})
  explicitTargetConsistency : EliminatorTargetRoute (K23Matrix.{u})
  finalAggregate : TargetRoute (K23Matrix.{u})

def k23Routes : K23Routes.{u} where
  finalGeometry := k23FinalRoute
  geometryTarget := k23GeometryTargetRoute
  brokenLatticeFinal := k23BrokenLatticeFinalRoute
  targetConsistency := k23TargetConsistencyRoute
  explicitTargetConsistency := k23ExplicitTargetConsistencyRoute
  finalAggregate := k23FinalAggregateRoute

structure CommonNeighborRoutes : Type (u + 1) where
  finalGeometry : EliminatorTargetRoute (CommonNeighborMatrix.{u})
  geometryTarget : EliminatorTargetRoute (CommonNeighborMatrix.{u})
  brokenLatticeFinal : EliminatorTargetRoute (CommonNeighborMatrix.{u})
  targetConsistency : TargetRoute (CommonNeighborMatrix.{u})
  explicitTargetConsistency :
    EliminatorTargetRoute (CommonNeighborMatrix.{u})
  finalAggregate : TargetRoute (CommonNeighborMatrix.{u})

def commonNeighborRoutes : CommonNeighborRoutes.{u} where
  finalGeometry := commonNeighborFinalRoute
  geometryTarget := commonNeighborGeometryTargetRoute
  brokenLatticeFinal := commonNeighborBrokenLatticeFinalRoute
  targetConsistency := commonNeighborTargetConsistencyRoute
  explicitTargetConsistency := commonNeighborExplicitTargetConsistencyRoute
  finalAggregate := commonNeighborFinalAggregateRoute

structure K23CommonNeighborRoutes : Type (u + 1) where
  viaK23 : EliminatorTargetRoute (K23CommonNeighborMatrix.{u})
  viaCommonNeighbor : EliminatorTargetRoute (K23CommonNeighborMatrix.{u})

def k23CommonNeighborRoutes : K23CommonNeighborRoutes.{u} where
  viaK23 := k23CommonNeighborViaK23Route
  viaCommonNeighbor := k23CommonNeighborViaCommonNeighborRoute

/-- All conditional target routes exposed by this final layer. -/
structure ConditionalSwanepoelTargetRoutes : Type (u + 1) where
  direct : DirectRoutes.{u}
  k23 : K23Routes.{u}
  commonNeighbor : CommonNeighborRoutes.{u}
  k23CommonNeighbor : K23CommonNeighborRoutes.{u}

def conditionalSwanepoelTargetRoutes :
    ConditionalSwanepoelTargetRoutes.{u} where
  direct := directRoutes
  k23 := k23Routes
  commonNeighbor := commonNeighborRoutes
  k23CommonNeighbor := k23CommonNeighborRoutes

/-- Checked ledgers imported by the final consistency layer. -/
structure ImportedLedgers : Type (u + 4) where
  geometryFinal : GeometryFinalIntegratedW11.Matrix.{u}
  geometryTarget : GeometryTargetIntegratedW11.Matrix.{u}
  brokenLatticeFinal : BrokenLatticeFinalIntegratedW11.Matrix.{u}
  k23Final : K23FinalIntegratedW11.Matrix.{u}
  targetConsistency : TargetConsistencyFinalW11.Matrix.{u}
  swanepoelFinalAggregate : SwanepoelW11FinalAggregate.Matrix.{u}

def importedLedgers : ImportedLedgers.{u} where
  geometryFinal := GeometryFinalIntegratedW11.matrix
  geometryTarget := GeometryTargetIntegratedW11.matrix
  brokenLatticeFinal := BrokenLatticeFinalIntegratedW11.matrix
  k23Final := K23FinalIntegratedW11.matrix
  targetConsistency := TargetConsistencyFinalW11.matrix
  swanepoelFinalAggregate := SwanepoelW11FinalAggregate.matrix

/-- Final geometry target consistency matrix.

The matrix records checked imports, visible input-matrix types, and conditional
routes.  It does not provide any direct, K23, or common-neighbor matrix. -/
structure Matrix : Type (u + 4) where
  matrixTypes : ExplicitMatrixTypes.{u}
  imports : ImportedLedgers.{u}
  routes : ConditionalSwanepoelTargetRoutes.{u}

/-- The checked final geometry target consistency layer. -/
def matrix : Matrix.{u} where
  matrixTypes := explicitMatrixTypes
  imports := importedLedgers
  routes := conditionalSwanepoelTargetRoutes

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

/-! ## Public conditional projections -/

theorem target_of_directMatrix
    (M : DirectMatrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix
    M

theorem target_of_directMatrix_via_geometryTarget
    (M : DirectMatrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix_via_geometryTarget
    M

theorem target_of_directMatrix_via_brokenLatticeFinal
    (M : DirectMatrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix_via_brokenLatticeFinal
    M

theorem target_of_directMatrix_via_targetConsistency
    (M : DirectMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_geometryDirectTargetMatrix
    M.toGeometryTargetMatrix

theorem target_of_directMatrix_via_finalAggregate
    (M : DirectMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_geometryDirectFinalMatrix M

theorem no_minimalClearedFailure_of_directMatrix
    (M : DirectMatrix.{u}) :
    MinimalFailureExclusion :=
  GeometryFinalIntegratedW11.no_minimalClearedFailure_of_directFinalGeometryMatrix
    M

theorem pipelineCleared_of_directMatrix
    (M : DirectMatrix.{u}) :
    PipelineCleared :=
  GeometryFinalIntegratedW11.pipelineCleared_of_directFinalGeometryMatrix M

theorem target_of_k23Matrix
    (M : K23Matrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix
    M

theorem target_of_k23Matrix_via_geometryTarget
    (M : K23Matrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix_via_geometryTarget
    M

theorem target_of_k23Matrix_via_brokenLatticeFinal
    (M : K23Matrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix_via_brokenLatticeFinal
    M

theorem target_of_k23Matrix_via_targetConsistency
    (M : K23Matrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_geometryK23TargetMatrix
    M.toGeometryTargetMatrix

theorem target_of_k23Matrix_via_explicitTargetConsistency
    (M : K23Matrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_k23ExplicitTargetMatrix
    M.toK23TargetMatrix

theorem target_of_k23Matrix_via_finalAggregate
    (M : K23Matrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_geometryK23FinalMatrix M

theorem no_minimalClearedFailure_of_k23Matrix
    (M : K23Matrix.{u}) :
    MinimalFailureExclusion :=
  GeometryFinalIntegratedW11.no_minimalClearedFailure_of_k23FinalGeometryMatrix
    M

theorem pipelineCleared_of_k23Matrix
    (M : K23Matrix.{u}) :
    PipelineCleared :=
  GeometryFinalIntegratedW11.pipelineCleared_of_k23FinalGeometryMatrix M

theorem target_of_commonNeighborMatrix
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix
    M

theorem target_of_commonNeighborMatrix_via_geometryTarget
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix_via_geometryTarget
    M

theorem target_of_commonNeighborMatrix_via_brokenLatticeFinal
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  GeometryFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix_via_brokenLatticeFinal
    M

theorem target_of_commonNeighborMatrix_via_targetConsistency
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_geometryCommonNeighborTargetMatrix
    M.toGeometryTargetMatrix

theorem target_of_commonNeighborMatrix_via_explicitTargetConsistency
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_commonNeighborExplicitTargetMatrix
    M.toK23TargetMatrix

theorem target_of_commonNeighborMatrix_via_finalAggregate
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_geometryCommonNeighborFinalMatrix M

theorem no_minimalClearedFailure_of_commonNeighborMatrix
    (M : CommonNeighborMatrix.{u}) :
    MinimalFailureExclusion :=
  GeometryFinalIntegratedW11.no_minimalClearedFailure_of_commonNeighborFinalGeometryMatrix
    M

theorem pipelineCleared_of_commonNeighborMatrix
    (M : CommonNeighborMatrix.{u}) :
    PipelineCleared :=
  GeometryFinalIntegratedW11.pipelineCleared_of_commonNeighborFinalGeometryMatrix
    M

theorem target_of_k23CommonNeighborMatrix_via_k23
    (M : K23CommonNeighborMatrix.{u}) :
    Target :=
  K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix_via_k23
    M

theorem target_of_k23CommonNeighborMatrix_via_commonNeighbor
    (M : K23CommonNeighborMatrix.{u}) :
    Target :=
  K23FinalIntegratedW11.targetLowerBoundEightThirtyOne_of_finalMatrix
    M

theorem target_of_explicitGeometryMatrices_via_direct
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  target_of_directMatrix M.direct

theorem target_of_explicitGeometryMatrices_via_k23
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  target_of_k23Matrix M.k23

theorem target_of_explicitGeometryMatrices_via_commonNeighbor
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  target_of_commonNeighborMatrix M.commonNeighbor

end

end GeometryTargetFinalW11
end Swanepoel
end ErdosProblems1066
