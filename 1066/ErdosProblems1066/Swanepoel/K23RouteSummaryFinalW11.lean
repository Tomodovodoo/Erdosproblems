import ErdosProblems1066.Swanepoel.K23BrokenTargetFinalW11
import ErdosProblems1066.Swanepoel.K23BrokenLatticeFinalW11
import ErdosProblems1066.Swanepoel.K23FinalIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelTargetFinalAggregateW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 K23/common-neighbor route summary

This file is a compact checked summary of the final W11 K23 and
common-neighbor route ledgers.  It records the imported matrices, keeps the
explicit matrix packages visible, and exposes only conditional Swanepoel target
projections indexed by caller-supplied data.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace K23RouteSummaryFinalW11

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

abbrev K23CommonNeighborFinalMatrix :=
  K23FinalIntegratedW11.K23CommonNeighborFinalMatrix

abbrev K23BrokenFieldMatrices :=
  K23BrokenLatticeFinalW11.ExplicitFieldMatrices

abbrev K23BrokenTargetMatrices :=
  K23BrokenTargetFinalW11.ExplicitMatrices

abbrev FinalBranchInputMatrices :=
  SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices

/-! ## Imported checked matrices -/

/-- Final W11 matrices summarized by this route ledger. -/
structure CheckedMatrices : Type (u + 3) where
  k23Final :
    K23FinalIntegratedW11.Matrix.{u}
  k23BrokenLattice :
    K23BrokenLatticeFinalW11.Matrix.{u}
  k23BrokenTarget :
    K23BrokenTargetFinalW11.Matrix.{u}
  swanepoelTargetAggregateChecked :
    True
  swanepoelFinalConsistencyChecked :
    True

/-- Imported checked W11 matrices. -/
def checkedMatrices :
    CheckedMatrices.{u} where
  k23Final := K23FinalIntegratedW11.matrix
  k23BrokenLattice := K23BrokenLatticeFinalW11.matrix
  k23BrokenTarget := K23BrokenTargetFinalW11.matrix
  swanepoelTargetAggregateChecked := True.intro
  swanepoelFinalConsistencyChecked := True.intro

/-! ## Explicit matrix surfaces -/

/-- Caller-supplied K23/common-neighbor matrix packages displayed by the
summary.

The fields deliberately name several already-checked package shapes rather
than manufacturing any rows. -/
structure ExplicitMatrices : Type (u + 1) where
  final :
    K23CommonNeighborFinalMatrix.{u}
  brokenFields :
    K23BrokenFieldMatrices.{u}
  brokenTarget :
    K23BrokenTargetMatrices.{u}
  finalBranches :
    FinalBranchInputMatrices.{u}

namespace ExplicitMatrices

/-- The aggregate final matrix carried by the broken-lattice package. -/
def finalFromBrokenFields
    (M : ExplicitMatrices.{u}) :
    K23CommonNeighborFinalMatrix.{u} :=
  M.brokenFields.k23CommonNeighbor

/-- The aggregate final matrix carried by the K23/broken-target package. -/
def finalFromBrokenTarget
    (M : ExplicitMatrices.{u}) :
    K23CommonNeighborFinalMatrix.{u} :=
  M.brokenTarget.k23Broken.k23CommonNeighbor

/-- The aggregate final matrix carried by the terminal Swanepoel target
aggregate branch package. -/
def finalFromAggregateBranch
    (M : ExplicitMatrices.{u}) :
    K23CommonNeighborFinalMatrix.{u} :=
  M.finalBranches.k23Final

/-- The K23 broken-lattice matrix selected from the direct broken-fields
package. -/
def k23BrokenLattice
    (M : ExplicitMatrices.{u}) :
    BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u} :=
  M.brokenFields.k23BrokenLattice

/-- The common-neighbor broken-lattice matrix selected from the direct
broken-fields package. -/
def commonNeighborBrokenLattice
    (M : ExplicitMatrices.{u}) :
    BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u} :=
  M.brokenFields.commonNeighborBrokenLattice

@[simp]
theorem finalFromBrokenFields_eq
    (M : ExplicitMatrices.{u}) :
    M.finalFromBrokenFields = M.brokenFields.k23CommonNeighbor :=
  rfl

@[simp]
theorem finalFromBrokenTarget_eq
    (M : ExplicitMatrices.{u}) :
    M.finalFromBrokenTarget =
      M.brokenTarget.k23Broken.k23CommonNeighbor :=
  rfl

@[simp]
theorem finalFromAggregateBranch_eq
    (M : ExplicitMatrices.{u}) :
    M.finalFromAggregateBranch = M.finalBranches.k23Final :=
  rfl

end ExplicitMatrices

/-- Projection functions naming every explicit matrix surface used by the
summary. -/
structure ExplicitMatrixSurface : Type (u + 1) where
  final :
    ExplicitMatrices.{u} -> K23CommonNeighborFinalMatrix.{u}
  brokenFields :
    ExplicitMatrices.{u} -> K23BrokenFieldMatrices.{u}
  brokenTarget :
    ExplicitMatrices.{u} -> K23BrokenTargetMatrices.{u}
  finalBranches :
    ExplicitMatrices.{u} -> FinalBranchInputMatrices.{u}
  finalFromBrokenFields :
    ExplicitMatrices.{u} -> K23CommonNeighborFinalMatrix.{u}
  finalFromBrokenTarget :
    ExplicitMatrices.{u} -> K23CommonNeighborFinalMatrix.{u}
  finalFromAggregateBranch :
    ExplicitMatrices.{u} -> K23CommonNeighborFinalMatrix.{u}
  k23BrokenLattice :
    ExplicitMatrices.{u} ->
      BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u}
  commonNeighborBrokenLattice :
    ExplicitMatrices.{u} ->
      BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u}

/-- The displayed explicit matrix projections. -/
def explicitMatrixSurface :
    ExplicitMatrixSurface.{u} where
  final := ExplicitMatrices.final
  brokenFields := ExplicitMatrices.brokenFields
  brokenTarget := ExplicitMatrices.brokenTarget
  finalBranches := ExplicitMatrices.finalBranches
  finalFromBrokenFields := ExplicitMatrices.finalFromBrokenFields
  finalFromBrokenTarget := ExplicitMatrices.finalFromBrokenTarget
  finalFromAggregateBranch := ExplicitMatrices.finalFromAggregateBranch
  k23BrokenLattice := ExplicitMatrices.k23BrokenLattice
  commonNeighborBrokenLattice :=
    ExplicitMatrices.commonNeighborBrokenLattice

/-! ## Conditional projection rows -/

/-- A conditional route to the Swanepoel target from an explicit input
package. -/
structure ConditionalTargetProjection (alpha : Type v) : Type v where
  eliminator : alpha -> MinimalFailureEliminator
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace ConditionalTargetProjection

/-- Reuse a target-integrated route row. -/
def ofTargetIntegratedRoute
    {alpha : Type v}
    (R : TargetIntegratedMatrixW11.EliminatorTargetRoute alpha) :
    ConditionalTargetProjection alpha where
  eliminator := R.eliminator
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse a K23/broken-lattice final route row. -/
def ofK23BrokenLatticeRoute
    {alpha : Type v}
    (R : K23BrokenLatticeFinalW11.EliminatorTargetRoute alpha) :
    ConditionalTargetProjection alpha where
  eliminator := R.eliminator
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse a K23/broken-target final route row. -/
def ofK23BrokenTargetRoute
    {alpha : Type v}
    (R : K23BrokenTargetFinalW11.EliminatorTargetRoute alpha) :
    ConditionalTargetProjection alpha where
  eliminator := R.eliminator
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end ConditionalTargetProjection

/-- K23 route through the final aggregate matrix. -/
def k23FinalProjection :
    ConditionalTargetProjection
      (K23CommonNeighborFinalMatrix.{u}) :=
  ConditionalTargetProjection.ofTargetIntegratedRoute
    K23FinalIntegratedW11.k23FinalIntegratedRoute

/-- Common-neighbor route through the final aggregate matrix. -/
def commonNeighborFinalProjection :
    ConditionalTargetProjection
      (K23CommonNeighborFinalMatrix.{u}) :=
  ConditionalTargetProjection.ofTargetIntegratedRoute
    K23FinalIntegratedW11.commonNeighborFinalIntegratedRoute

/-- K23 route from the explicit broken-lattice field package. -/
def k23BrokenFieldProjection :
    ConditionalTargetProjection
      (K23BrokenFieldMatrices.{u}) :=
  ConditionalTargetProjection.ofK23BrokenLatticeRoute
    K23BrokenLatticeFinalW11.explicitK23FinalRoute

/-- Common-neighbor route from the explicit broken-lattice field package. -/
def commonNeighborBrokenFieldProjection :
    ConditionalTargetProjection
      (K23BrokenFieldMatrices.{u}) :=
  ConditionalTargetProjection.ofK23BrokenLatticeRoute
    K23BrokenLatticeFinalW11.explicitCommonNeighborFinalRoute

/-- K23 route from the explicit K23/broken-target package. -/
def k23BrokenTargetProjection :
    ConditionalTargetProjection
      (K23BrokenTargetMatrices.{u}) :=
  ConditionalTargetProjection.ofK23BrokenTargetRoute
    K23BrokenTargetFinalW11.route_via_k23Broken_k23Final

/-- Common-neighbor route from the explicit K23/broken-target package. -/
def commonNeighborBrokenTargetProjection :
    ConditionalTargetProjection
      (K23BrokenTargetMatrices.{u}) :=
  ConditionalTargetProjection.ofK23BrokenTargetRoute
    K23BrokenTargetFinalW11.route_via_k23Broken_commonNeighborFinal

/-- K23 route from the terminal Swanepoel aggregate branch package. -/
def aggregateBranchK23Projection :
    ConditionalTargetProjection
      (FinalBranchInputMatrices.{u}) where
  eliminator := fun M =>
    K23FinalIntegratedW11.k23FinalIntegratedRoute.eliminator M.k23Final
  noMinimal := fun M =>
    K23FinalIntegratedW11.k23FinalIntegratedRoute.noMinimal M.k23Final
  pipeline := fun M =>
    K23FinalIntegratedW11.k23FinalIntegratedRoute.pipeline M.k23Final
  target := fun M =>
    K23FinalIntegratedW11.k23FinalIntegratedRoute.target M.k23Final

/-- Common-neighbor route from the terminal Swanepoel aggregate branch
package. -/
def aggregateBranchCommonNeighborProjection :
    ConditionalTargetProjection
      (FinalBranchInputMatrices.{u}) where
  eliminator := fun M =>
    K23FinalIntegratedW11.commonNeighborFinalIntegratedRoute.eliminator
      M.k23Final
  noMinimal := fun M =>
    K23FinalIntegratedW11.commonNeighborFinalIntegratedRoute.noMinimal
      M.k23Final
  pipeline := fun M =>
    K23FinalIntegratedW11.commonNeighborFinalIntegratedRoute.pipeline
      M.k23Final
  target := fun M =>
    K23FinalIntegratedW11.commonNeighborFinalIntegratedRoute.target
      M.k23Final

/-- Conditional target rows for the K23/common-neighbor summary. -/
structure ConditionalProjectionMatrix : Type (u + 1) where
  k23Final :
    ConditionalTargetProjection (K23CommonNeighborFinalMatrix.{u})
  commonNeighborFinal :
    ConditionalTargetProjection (K23CommonNeighborFinalMatrix.{u})
  k23BrokenFields :
    ConditionalTargetProjection (K23BrokenFieldMatrices.{u})
  commonNeighborBrokenFields :
    ConditionalTargetProjection (K23BrokenFieldMatrices.{u})
  k23BrokenTarget :
    ConditionalTargetProjection (K23BrokenTargetMatrices.{u})
  commonNeighborBrokenTarget :
    ConditionalTargetProjection (K23BrokenTargetMatrices.{u})
  aggregateBranchK23 :
    ConditionalTargetProjection (FinalBranchInputMatrices.{u})
  aggregateBranchCommonNeighbor :
    ConditionalTargetProjection (FinalBranchInputMatrices.{u})

/-- Checked conditional target rows for the K23/common-neighbor summary. -/
def conditionalProjectionMatrix :
    ConditionalProjectionMatrix.{u} where
  k23Final := k23FinalProjection
  commonNeighborFinal := commonNeighborFinalProjection
  k23BrokenFields := k23BrokenFieldProjection
  commonNeighborBrokenFields := commonNeighborBrokenFieldProjection
  k23BrokenTarget := k23BrokenTargetProjection
  commonNeighborBrokenTarget := commonNeighborBrokenTargetProjection
  aggregateBranchK23 := aggregateBranchK23Projection
  aggregateBranchCommonNeighbor := aggregateBranchCommonNeighborProjection

/-! ## Blocker/omission ledger -/

/-- Checked omissions carried through the final W11 consistency ledger. -/
def finalConsistencyOmissions :
    SwanepoelW11FinalConsistency.KnownImportOmissions :=
  SwanepoelW11FinalConsistency.knownImportOmissions

/-! ## Final summary matrix -/

/-- Concise checked W11 K23/common-neighbor route summary matrix.

The summary records checked ledgers and conditional route rows only; it does
not supply an inhabitant of any explicit matrix package. -/
structure Matrix : Type (u + 3) where
  checked :
    CheckedMatrices.{u}
  explicit :
    ExplicitMatrixSurface.{u}
  projections :
    ConditionalProjectionMatrix.{u}
  omissions :
    SwanepoelW11FinalConsistency.KnownImportOmissions

/-- The final checked K23/common-neighbor route summary matrix. -/
def matrix :
    Matrix.{u} where
  checked := checkedMatrices
  explicit := explicitMatrixSurface
  projections := conditionalProjectionMatrix
  omissions := finalConsistencyOmissions

theorem matrix_nonempty :
    Nonempty Matrix.{u} :=
  Nonempty.intro matrix

theorem checked_k23Final :
    matrix.checked.k23Final = K23FinalIntegratedW11.matrix := by
  rfl

theorem checked_k23BrokenLattice :
    matrix.checked.k23BrokenLattice = K23BrokenLatticeFinalW11.matrix := by
  rfl

theorem checked_k23BrokenTarget :
    matrix.checked.k23BrokenTarget = K23BrokenTargetFinalW11.matrix := by
  rfl

theorem checked_swanepoelTargetAggregate :
    matrix.checked.swanepoelTargetAggregateChecked =
      True.intro := by
  rfl

theorem checked_swanepoelFinalConsistency :
    matrix.checked.swanepoelFinalConsistencyChecked =
      True.intro := by
  rfl

/-! ## Public conditional target projections -/

theorem target_of_finalMatrix_via_k23
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  matrix.projections.k23Final.target M

theorem target_of_finalMatrix_via_commonNeighbor
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  matrix.projections.commonNeighborFinal.target M

theorem target_of_brokenFields_via_k23
    (M : K23BrokenFieldMatrices.{u}) :
    Target :=
  matrix.projections.k23BrokenFields.target M

theorem target_of_brokenFields_via_commonNeighbor
    (M : K23BrokenFieldMatrices.{u}) :
    Target :=
  matrix.projections.commonNeighborBrokenFields.target M

theorem target_of_brokenTarget_via_k23
    (M : K23BrokenTargetMatrices.{u}) :
    Target :=
  matrix.projections.k23BrokenTarget.target M

theorem target_of_brokenTarget_via_commonNeighbor
    (M : K23BrokenTargetMatrices.{u}) :
    Target :=
  matrix.projections.commonNeighborBrokenTarget.target M

theorem target_of_finalBranch_via_k23
    (M : FinalBranchInputMatrices.{u}) :
    Target :=
  matrix.projections.aggregateBranchK23.target M

theorem target_of_finalBranch_via_commonNeighbor
    (M : FinalBranchInputMatrices.{u}) :
    Target :=
  matrix.projections.aggregateBranchCommonNeighbor.target M

theorem target_of_explicitMatrices_via_k23Final
    (M : ExplicitMatrices.{u}) :
    Target :=
  target_of_finalMatrix_via_k23 M.final

theorem target_of_explicitMatrices_via_commonNeighborFinal
    (M : ExplicitMatrices.{u}) :
    Target :=
  target_of_finalMatrix_via_commonNeighbor M.final

theorem target_of_explicitMatrices_via_brokenFields_k23
    (M : ExplicitMatrices.{u}) :
    Target :=
  target_of_brokenFields_via_k23 M.brokenFields

theorem target_of_explicitMatrices_via_brokenFields_commonNeighbor
    (M : ExplicitMatrices.{u}) :
    Target :=
  target_of_brokenFields_via_commonNeighbor M.brokenFields

theorem target_of_explicitMatrices_via_brokenTarget_k23
    (M : ExplicitMatrices.{u}) :
    Target :=
  target_of_brokenTarget_via_k23 M.brokenTarget

theorem target_of_explicitMatrices_via_brokenTarget_commonNeighbor
    (M : ExplicitMatrices.{u}) :
    Target :=
  target_of_brokenTarget_via_commonNeighbor M.brokenTarget

theorem target_of_explicitMatrices_via_finalBranch_k23
    (M : ExplicitMatrices.{u}) :
    Target :=
  target_of_finalBranch_via_k23 M.finalBranches

theorem target_of_explicitMatrices_via_finalBranch_commonNeighbor
    (M : ExplicitMatrices.{u}) :
    Target :=
  target_of_finalBranch_via_commonNeighbor M.finalBranches

end

end K23RouteSummaryFinalW11
end Swanepoel
end ErdosProblems1066
