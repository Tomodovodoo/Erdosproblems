import ErdosProblems1066.Swanepoel.BoundaryAngleFinalIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryAngleIntegratedW11
import ErdosProblems1066.Swanepoel.BrokenLatticeFinalIntegratedW11
import ErdosProblems1066.Swanepoel.TargetConsistencyFinalW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# Final W11 boundary-angle target consistency

This module is a target-facing wrapper for the final W11 boundary-angle
aggregate.  It records the explicit `BoundaryAngleFinalMatrix` input surface,
adapters to the checked boundary-angle and broken-lattice matrices, and
conditional Swanepoel target routes.  Every target projection below consumes a
caller-supplied final matrix.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleTargetFinalW11

open MinimalGraphFacts

universe u v

noncomputable section

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

abbrev FinalMatrixInput : Type (u + 1) :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.{u}

abbrev FinalRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Type (u + 1) :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalRow.{u} C hmin

abbrev BoundaryAngleDirectMatrix : Type (u + 1) :=
  BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u}

abbrev BoundaryAngleK23Matrix : Type (u + 1) :=
  BoundaryAngleIntegratedW11.K23GeometryMatrix.{u}

abbrev BoundaryAngleCommonNeighborMatrix : Type (u + 1) :=
  BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u}

abbrev DirectFieldMatrix : Type (u + 1) :=
  BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}

abbrev K23FieldMatrix : Type (u + 1) :=
  BrokenLatticeIntegratedW11.K23FieldMatrix.{u}

abbrev CommonNeighborFieldMatrix : Type (u + 1) :=
  BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}

/-! ## Shared route records -/

/-- A checked route to the common cleared-pipeline propositions. -/
structure ClearedRoute (alpha : Type v) : Type v where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared

/-- A checked conditional route to the Swanepoel target proposition. -/
structure TargetRoute (alpha : Type v) : Type v where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

/-! ## Explicit final matrix input -/

namespace FinalMatrixInput

/-- Project final boundary-angle rows to integrated direct boundary-angle
rows. -/
def toBoundaryAngleDirectMatrix
    (M : FinalMatrixInput.{u}) :
    BoundaryAngleDirectMatrix.{u} :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.toBoundaryAngleDirectGeometryMatrix
    M

/-- Project final boundary-angle rows to integrated K23 boundary-angle rows. -/
def toBoundaryAngleK23Matrix
    (M : FinalMatrixInput.{u}) :
    BoundaryAngleK23Matrix.{u} :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.toBoundaryAngleK23GeometryMatrix
    M

/-- Project final boundary-angle rows to integrated common-neighbor
boundary-angle rows. -/
def toBoundaryAngleCommonNeighborMatrix
    (M : FinalMatrixInput.{u}) :
    BoundaryAngleCommonNeighborMatrix.{u} :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.toBoundaryAngleCommonNeighborGeometryMatrix
    M

/-- Project final boundary-angle rows to direct broken-lattice fields. -/
def toDirectFieldMatrix
    (M : FinalMatrixInput.{u}) :
    DirectFieldMatrix.{u} :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.toDirectFieldMatrix
    M

/-- Project final boundary-angle rows to K23 broken-lattice fields. -/
def toK23FieldMatrix
    (M : FinalMatrixInput.{u}) :
    K23FieldMatrix.{u} :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.toK23FieldMatrix
    M

/-- Project final boundary-angle rows to common-neighbor broken-lattice
fields. -/
def toCommonNeighborFieldMatrix
    (M : FinalMatrixInput.{u}) :
    CommonNeighborFieldMatrix.{u} :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.toCommonNeighborFieldMatrix
    M

/-- Boundary-angle direct rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure_via_boundaryAngleDirect
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_directGeometryMatrix
    M.toBoundaryAngleDirectMatrix

/-- Boundary-angle K23 rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure_via_boundaryAngleK23
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_k23GeometryMatrix
    M.toBoundaryAngleK23Matrix

/-- Boundary-angle common-neighbor rows rule out every minimal cleared
failure. -/
theorem no_minimalClearedFailure_via_boundaryAngleCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_commonNeighborGeometryMatrix
    M.toBoundaryAngleCommonNeighborMatrix

/-- Boundary-angle direct rows supply the cleared-pipeline predicate. -/
theorem pipelineCleared_via_boundaryAngleDirect
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  BoundaryAngleIntegratedW11.pipelineCleared_of_directGeometryMatrix
    M.toBoundaryAngleDirectMatrix

/-- Boundary-angle K23 rows supply the cleared-pipeline predicate. -/
theorem pipelineCleared_via_boundaryAngleK23
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  BoundaryAngleIntegratedW11.pipelineCleared_of_k23GeometryMatrix
    M.toBoundaryAngleK23Matrix

/-- Boundary-angle common-neighbor rows supply the cleared-pipeline
predicate. -/
theorem pipelineCleared_via_boundaryAngleCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  BoundaryAngleIntegratedW11.pipelineCleared_of_commonNeighborGeometryMatrix
    M.toBoundaryAngleCommonNeighborMatrix

/-- Direct final fields give the pointwise minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator_via_direct
    (M : FinalMatrixInput.{u}) :
    MinimalFailureEliminator :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.minimalClearedFailureEliminator_via_direct
    M

/-- K23 final fields give the pointwise minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator_via_k23
    (M : FinalMatrixInput.{u}) :
    MinimalFailureEliminator :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.minimalClearedFailureEliminator_via_k23
    M

/-- Common-neighbor final fields give the pointwise minimal-failure
eliminator. -/
theorem minimalClearedFailureEliminator_via_commonNeighbor
    (M : FinalMatrixInput.{u}) :
    MinimalFailureEliminator :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.minimalClearedFailureEliminator_via_commonNeighbor
    M

/-- Direct final fields rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure_via_direct
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.no_minimalClearedFailure_via_direct
    M

/-- K23 final fields rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure_via_k23
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.no_minimalClearedFailure_via_k23
    M

/-- Common-neighbor final fields rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure_via_commonNeighbor
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.no_minimalClearedFailure_via_commonNeighbor
    M

/-- Direct final fields supply the cleared-pipeline predicate. -/
theorem pipelineCleared_via_direct
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.pipelineCleared_via_direct
    M

/-- K23 final fields supply the cleared-pipeline predicate. -/
theorem pipelineCleared_via_k23
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.pipelineCleared_via_k23
    M

/-- Common-neighbor final fields supply the cleared-pipeline predicate. -/
theorem pipelineCleared_via_commonNeighbor
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  BoundaryAngleFinalIntegratedW11.BoundaryAngleFinalMatrix.pipelineCleared_via_commonNeighbor
    M

/-- Conditional target projection through direct final fields. -/
theorem swanepoelTarget_via_direct
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_direct M

/-- Conditional target projection through K23 final fields. -/
theorem swanepoelTarget_via_k23
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_k23 M

/-- Conditional target projection through common-neighbor final fields. -/
theorem swanepoelTarget_via_commonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_commonNeighbor
    M

/-- Conditional target projection through the final broken-lattice direct
route. -/
theorem swanepoelTarget_via_brokenLatticeDirect
    (M : FinalMatrixInput.{u}) :
    Target :=
  BrokenLatticeFinalIntegratedW11.directTargetIntegratedRoute.target
    M.toDirectFieldMatrix

/-- Conditional target projection through the final broken-lattice K23
route. -/
theorem swanepoelTarget_via_brokenLatticeK23
    (M : FinalMatrixInput.{u}) :
    Target :=
  BrokenLatticeFinalIntegratedW11.k23TargetIntegratedRoute.target
    M.toK23FieldMatrix

/-- Conditional target projection through the final broken-lattice
common-neighbor route. -/
theorem swanepoelTarget_via_brokenLatticeCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  BrokenLatticeFinalIntegratedW11.commonNeighborTargetIntegratedRoute.target
    M.toCommonNeighborFieldMatrix

/-- Conditional target projection through the final target-consistency direct
ledger. -/
theorem swanepoelTarget_via_targetConsistencyDirect
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_from_ledger_directFieldMatrix
    M.toDirectFieldMatrix

/-- Conditional target projection through the final target-consistency K23
ledger. -/
theorem swanepoelTarget_via_targetConsistencyK23
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_from_ledger_k23FieldMatrix
    M.toK23FieldMatrix

/-- Conditional target projection through the final target-consistency
common-neighbor ledger. -/
theorem swanepoelTarget_via_targetConsistencyCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_from_ledger_commonNeighborFieldMatrix
    M.toCommonNeighborFieldMatrix

end FinalMatrixInput

/-! ## Input and import ledgers -/

/-- Explicit input shapes owned by this target-facing boundary-angle layer. -/
structure ExplicitInputLedger : Type (u + 2) where
  pointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C), Type (u + 1)
  finalUniform : Type (u + 1)
  boundaryAngleDirectUniform : Type (u + 1)
  boundaryAngleK23Uniform : Type (u + 1)
  boundaryAngleCommonNeighborUniform : Type (u + 1)
  directFieldUniform : Type (u + 1)
  k23FieldUniform : Type (u + 1)
  commonNeighborFieldUniform : Type (u + 1)

/-- The explicit final input surface and its checked projections. -/
def explicitInputLedger : ExplicitInputLedger.{u} where
  pointwise := fun C hmin => FinalRow.{u} C hmin
  finalUniform := FinalMatrixInput.{u}
  boundaryAngleDirectUniform := BoundaryAngleDirectMatrix.{u}
  boundaryAngleK23Uniform := BoundaryAngleK23Matrix.{u}
  boundaryAngleCommonNeighborUniform :=
    BoundaryAngleCommonNeighborMatrix.{u}
  directFieldUniform := DirectFieldMatrix.{u}
  k23FieldUniform := K23FieldMatrix.{u}
  commonNeighborFieldUniform := CommonNeighborFieldMatrix.{u}

/-- Checked ledgers imported by this target-facing wrapper. -/
structure ImportedLedgers : Type (u + 4) where
  boundaryAngleFinal : BoundaryAngleFinalIntegratedW11.Matrix.{u}
  boundaryAngleIntegrated : BoundaryAngleIntegratedW11.Matrix.{u}
  brokenLatticeFinal : BrokenLatticeFinalIntegratedW11.Matrix.{u}
  targetConsistencyFinal : TargetConsistencyFinalW11.Matrix.{u}

/-- The imported ledgers checked together for this file. -/
def importedLedgers : ImportedLedgers.{u} where
  boundaryAngleFinal := BoundaryAngleFinalIntegratedW11.matrix
  boundaryAngleIntegrated := BoundaryAngleIntegratedW11.matrix
  brokenLatticeFinal := BrokenLatticeFinalIntegratedW11.matrix
  targetConsistencyFinal := TargetConsistencyFinalW11.matrix

/-! ## Conditional route rows -/

/-- Boundary-angle projections from final rows to checked cleared routes. -/
structure BoundaryAngleClearedRoutes : Type (u + 1) where
  direct : ClearedRoute (FinalMatrixInput.{u})
  k23 : ClearedRoute (FinalMatrixInput.{u})
  commonNeighbor : ClearedRoute (FinalMatrixInput.{u})

/-- The checked boundary-angle cleared routes from the final matrix input. -/
def boundaryAngleClearedRoutes :
    BoundaryAngleClearedRoutes.{u} where
  direct := {
    noMinimal := FinalMatrixInput.no_minimalClearedFailure_via_boundaryAngleDirect
    pipeline := FinalMatrixInput.pipelineCleared_via_boundaryAngleDirect
  }
  k23 := {
    noMinimal := FinalMatrixInput.no_minimalClearedFailure_via_boundaryAngleK23
    pipeline := FinalMatrixInput.pipelineCleared_via_boundaryAngleK23
  }
  commonNeighbor := {
    noMinimal :=
      FinalMatrixInput.no_minimalClearedFailure_via_boundaryAngleCommonNeighbor
    pipeline :=
      FinalMatrixInput.pipelineCleared_via_boundaryAngleCommonNeighbor
  }

/-- Final boundary-angle routes through the target-integrated ledger. -/
structure FinalIntegratedTargetRoutes : Type (u + 1) where
  direct :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalMatrixInput.{u})
  k23 :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalMatrixInput.{u})
  commonNeighbor :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalMatrixInput.{u})

/-- Checked final boundary-angle routes through target-integrated fields. -/
def finalIntegratedTargetRoutes :
    FinalIntegratedTargetRoutes.{u} where
  direct := BoundaryAngleFinalIntegratedW11.directFinalRoute
  k23 := BoundaryAngleFinalIntegratedW11.k23FinalRoute
  commonNeighbor := BoundaryAngleFinalIntegratedW11.commonNeighborFinalRoute

/-- Final boundary-angle routes routed through the broken-lattice final
ledger. -/
structure BrokenLatticeFinalTargetRoutes : Type (u + 1) where
  direct : TargetRoute (FinalMatrixInput.{u})
  k23 : TargetRoute (FinalMatrixInput.{u})
  commonNeighbor : TargetRoute (FinalMatrixInput.{u})

/-- Checked routes from final boundary-angle rows through broken-lattice
final fields. -/
def brokenLatticeFinalTargetRoutes :
    BrokenLatticeFinalTargetRoutes.{u} where
  direct := {
    noMinimal := fun M =>
      BrokenLatticeFinalIntegratedW11.directTargetIntegratedRoute.noMinimal
        M.toDirectFieldMatrix
    pipeline := fun M =>
      BrokenLatticeFinalIntegratedW11.directTargetIntegratedRoute.pipeline
        M.toDirectFieldMatrix
    target := FinalMatrixInput.swanepoelTarget_via_brokenLatticeDirect
  }
  k23 := {
    noMinimal := fun M =>
      BrokenLatticeFinalIntegratedW11.k23TargetIntegratedRoute.noMinimal
        M.toK23FieldMatrix
    pipeline := fun M =>
      BrokenLatticeFinalIntegratedW11.k23TargetIntegratedRoute.pipeline
        M.toK23FieldMatrix
    target := FinalMatrixInput.swanepoelTarget_via_brokenLatticeK23
  }
  commonNeighbor := {
    noMinimal := fun M =>
      BrokenLatticeFinalIntegratedW11.commonNeighborTargetIntegratedRoute.noMinimal
        M.toCommonNeighborFieldMatrix
    pipeline := fun M =>
      BrokenLatticeFinalIntegratedW11.commonNeighborTargetIntegratedRoute.pipeline
        M.toCommonNeighborFieldMatrix
    target :=
      FinalMatrixInput.swanepoelTarget_via_brokenLatticeCommonNeighbor
  }

/-- Final boundary-angle routes routed through the final target-consistency
ledger. -/
structure TargetConsistencyRoutes : Type (u + 1) where
  direct : TargetRoute (FinalMatrixInput.{u})
  k23 : TargetRoute (FinalMatrixInput.{u})
  commonNeighbor : TargetRoute (FinalMatrixInput.{u})

/-- Checked routes from final boundary-angle rows through the final
target-consistency ledger. -/
def targetConsistencyRoutes :
    TargetConsistencyRoutes.{u} where
  direct := {
    noMinimal := FinalMatrixInput.no_minimalClearedFailure_via_direct
    pipeline := FinalMatrixInput.pipelineCleared_via_direct
    target := FinalMatrixInput.swanepoelTarget_via_targetConsistencyDirect
  }
  k23 := {
    noMinimal := FinalMatrixInput.no_minimalClearedFailure_via_k23
    pipeline := FinalMatrixInput.pipelineCleared_via_k23
    target := FinalMatrixInput.swanepoelTarget_via_targetConsistencyK23
  }
  commonNeighbor := {
    noMinimal := FinalMatrixInput.no_minimalClearedFailure_via_commonNeighbor
    pipeline := FinalMatrixInput.pipelineCleared_via_commonNeighbor
    target :=
      FinalMatrixInput.swanepoelTarget_via_targetConsistencyCommonNeighbor
  }

/-- All checked conditional routes exposed by this final target layer. -/
structure ConditionalSwanepoelTargetRoutes : Type (u + 1) where
  boundaryAngleCleared : BoundaryAngleClearedRoutes.{u}
  finalIntegrated : FinalIntegratedTargetRoutes.{u}
  brokenLatticeFinal : BrokenLatticeFinalTargetRoutes.{u}
  targetConsistency : TargetConsistencyRoutes.{u}

/-- Checked conditional routes from explicit final boundary-angle matrices. -/
def conditionalSwanepoelTargetRoutes :
    ConditionalSwanepoelTargetRoutes.{u} where
  boundaryAngleCleared := boundaryAngleClearedRoutes
  finalIntegrated := finalIntegratedTargetRoutes
  brokenLatticeFinal := brokenLatticeFinalTargetRoutes
  targetConsistency := targetConsistencyRoutes

/-! ## Final matrix -/

/-- Final target-facing boundary-angle consistency matrix.

The matrix stores input shapes, checked imports, and conditional routes.  It
does not provide a final boundary-angle input family.
-/
structure Matrix : Type (u + 4) where
  inputs : ExplicitInputLedger.{u}
  imported : ImportedLedgers.{u}
  routes : ConditionalSwanepoelTargetRoutes.{u}

/-- The checked final target-facing boundary-angle consistency matrix. -/
def matrix : Matrix.{u} where
  inputs := explicitInputLedger
  imported := importedLedgers
  routes := conditionalSwanepoelTargetRoutes

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

/-! ## Public conditional projections -/

/-- Minimal-failure exclusion from a supplied final input family. -/
theorem no_minimalClearedFailure_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  FinalMatrixInput.no_minimalClearedFailure_via_direct M

/-- Cleared-pipeline projection from a supplied final input family. -/
theorem pipelineCleared_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  FinalMatrixInput.pipelineCleared_via_direct M

/-- Pointwise minimal-failure eliminator from a supplied final input family. -/
theorem minimalClearedFailureEliminator_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    MinimalFailureEliminator :=
  FinalMatrixInput.minimalClearedFailureEliminator_via_direct M

/-- Boundary-angle direct projection from a supplied final input family. -/
theorem no_minimalClearedFailure_of_finalMatrix_via_boundaryAngleDirect
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  FinalMatrixInput.no_minimalClearedFailure_via_boundaryAngleDirect M

/-- Boundary-angle K23 projection from a supplied final input family. -/
theorem no_minimalClearedFailure_of_finalMatrix_via_boundaryAngleK23
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  FinalMatrixInput.no_minimalClearedFailure_via_boundaryAngleK23 M

/-- Boundary-angle common-neighbor projection from a supplied final input
family. -/
theorem no_minimalClearedFailure_of_finalMatrix_via_boundaryAngleCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  FinalMatrixInput.no_minimalClearedFailure_via_boundaryAngleCommonNeighbor M

/-- Conditional Swanepoel target projection through direct final fields. -/
theorem swanepoelTarget_of_finalMatrix_via_direct
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.swanepoelTarget_via_direct M

/-- Conditional Swanepoel target projection through K23 final fields. -/
theorem swanepoelTarget_of_finalMatrix_via_k23
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.swanepoelTarget_via_k23 M

/-- Conditional Swanepoel target projection through common-neighbor final
fields. -/
theorem swanepoelTarget_of_finalMatrix_via_commonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.swanepoelTarget_via_commonNeighbor M

/-- Conditional Swanepoel target projection through broken-lattice direct
fields. -/
theorem swanepoelTarget_of_finalMatrix_via_brokenLatticeDirect
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.swanepoelTarget_via_brokenLatticeDirect M

/-- Conditional Swanepoel target projection through broken-lattice K23
fields. -/
theorem swanepoelTarget_of_finalMatrix_via_brokenLatticeK23
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.swanepoelTarget_via_brokenLatticeK23 M

/-- Conditional Swanepoel target projection through broken-lattice
common-neighbor fields. -/
theorem swanepoelTarget_of_finalMatrix_via_brokenLatticeCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.swanepoelTarget_via_brokenLatticeCommonNeighbor M

/-- Conditional Swanepoel target projection through the final
target-consistency direct route. -/
theorem swanepoelTarget_of_finalMatrix_via_targetConsistencyDirect
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.swanepoelTarget_via_targetConsistencyDirect M

/-- Conditional Swanepoel target projection through the final
target-consistency K23 route. -/
theorem swanepoelTarget_of_finalMatrix_via_targetConsistencyK23
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.swanepoelTarget_via_targetConsistencyK23 M

/-- Conditional Swanepoel target projection through the final
target-consistency common-neighbor route. -/
theorem swanepoelTarget_of_finalMatrix_via_targetConsistencyCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.swanepoelTarget_via_targetConsistencyCommonNeighbor M

end

end BoundaryAngleTargetFinalW11
end Swanepoel
end ErdosProblems1066
