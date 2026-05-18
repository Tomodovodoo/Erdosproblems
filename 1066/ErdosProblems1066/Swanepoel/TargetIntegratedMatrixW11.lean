import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11
import ErdosProblems1066.Swanepoel.SwanepoelW11IntegratedMatrix
import ErdosProblems1066.Swanepoel.BrokenLatticeIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Integrated W11 Swanepoel target matrix

This module records the checked W11 target routes currently present in the
Swanepoel tree.  It is a conditional ledger: every route still takes one of
the displayed source packages as input, and the topology, boundary, geometry,
containment, K23, common-neighbor, no-early, and no-start fields stay visible
in the checked input packages.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TargetIntegratedMatrixW11

universe u v

noncomputable section

abbrev Target : Prop :=
  TargetClosureMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetClosureMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetClosureMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  BrokenLatticeIntegratedW11.MinimalFailureEliminator

/-! ## Target route records -/

/-- A checked conditional route from an explicit input package to the
Swanepoel target proposition. -/
structure TargetRoute (alpha : Sort v) : Sort (max 1 v) where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace TargetRoute

/-- Reuse a route row from the target-closure matrix. -/
def ofTargetClosureRow
    {alpha : Sort v}
    (R : TargetClosureMatrixW11.TargetProjectionRow alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse a route row from the broader W11 integrated matrix. -/
def ofSwanepoelIntegratedRow
    {alpha : Sort v}
    (R : SwanepoelW11IntegratedMatrix.TargetProjectionRow alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end TargetRoute

/-- A target route that also exposes the minimal-failure eliminator delivered
by the source package. -/
structure EliminatorTargetRoute (alpha : Type v) : Type v where
  eliminator : alpha -> MinimalFailureEliminator
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace EliminatorTargetRoute

/-- Forget the eliminator field and retain the target route. -/
def toTargetRoute
    {alpha : Type v}
    (R : EliminatorTargetRoute alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse a source-facing route row from the integrated broken-lattice
matrix. -/
def ofBrokenLatticeRow
    {alpha : Type v}
    (R : BrokenLatticeIntegratedW11.ProjectionRow alpha) :
    EliminatorTargetRoute alpha where
  eliminator := R.eliminator
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end EliminatorTargetRoute

/-! ## Source-facing broken-lattice routes -/

/-- Conditional target route from direct source geometry plus containment and
five-start no-early fields. -/
def directFieldMatrixRoute :
    EliminatorTargetRoute
      (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :=
  EliminatorTargetRoute.ofBrokenLatticeRow
    BrokenLatticeIntegratedW11.directFieldMatrixRow

/-- Conditional target route from K23 source geometry plus containment and
K23 no-early fields. -/
def k23FieldMatrixRoute :
    EliminatorTargetRoute
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :=
  EliminatorTargetRoute.ofBrokenLatticeRow
    BrokenLatticeIntegratedW11.k23FieldMatrixRow

/-- Conditional target route from common-neighbor source geometry plus
containment and common-neighbor no-early fields. -/
def commonNeighborFieldMatrixRoute :
    EliminatorTargetRoute
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :=
  EliminatorTargetRoute.ofBrokenLatticeRow
    BrokenLatticeIntegratedW11.commonNeighborFieldMatrixRow

/-! ## Source-facing no-early/no-start routes -/

/-- Conditional target route from checked W11 no-early rows. -/
def noEarlyMatrixRoute :
    TargetRoute (WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}) :=
  TargetRoute.ofTargetClosureRow
    (TargetClosureMatrixW11.noEarlyMatrixRow :
      TargetClosureMatrixW11.TargetProjectionRow
        (WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}))

/-- Conditional target route from checked W11 no-start rows. -/
def noStartMatrixRoute :
    TargetRoute (WindowNoEarlyRowsW11.NoStartMatrix.{u, u}) :=
  TargetRoute.ofTargetClosureRow
    (TargetClosureMatrixW11.noStartMatrixRow :
      TargetClosureMatrixW11.TargetProjectionRow
        (WindowNoEarlyRowsW11.NoStartMatrix.{u, u}))

/-! ## Integrated target ledger -/

/-- Checked source projections that feed the target ledgers while retaining
their displayed input fields. -/
structure SourceFieldLedger : Type (u + 1) where
  topologyBoundary :
    SwanepoelW11IntegratedMatrix.FieldProjectionLedger.{u}
  targetClosure :
    TargetClosureMatrixW11.Matrix.{u}
  swanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.Matrix.{u}
  brokenLatticeIntegrated :
    BrokenLatticeIntegratedW11.Matrix.{u}

/-- The checked source projection ledger assembled from present W11 modules. -/
def sourceFieldLedger : SourceFieldLedger.{u} where
  topologyBoundary :=
    SwanepoelW11IntegratedMatrix.fieldProjectionLedger
  targetClosure :=
    TargetClosureMatrixW11.matrix
  swanepoelIntegrated :=
    SwanepoelW11IntegratedMatrix.matrix
  brokenLatticeIntegrated :=
    BrokenLatticeIntegratedW11.matrix

/-- Existing target-route matrices imported as checked W11 target ledgers. -/
structure ImportedTargetLedgers : Type (u + 1) where
  targetClosure :
    TargetClosureMatrixW11.Matrix.{u}
  swanepoelIntegratedTargets :
    SwanepoelW11IntegratedMatrix.TargetRouteLedger.{u}

/-- The imported target ledgers available in this tree. -/
def importedTargetLedgers : ImportedTargetLedgers.{u} where
  targetClosure :=
    TargetClosureMatrixW11.matrix
  swanepoelIntegratedTargets :=
    SwanepoelW11IntegratedMatrix.targetRouteLedger

/-- Source-facing routes added by the integrated W11 modules. -/
structure SourceFacingTargetRoutes : Type (u + 1) where
  directFields :
    EliminatorTargetRoute
      (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u})
  k23Fields :
    EliminatorTargetRoute
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u})
  commonNeighborFields :
    EliminatorTargetRoute
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u})
  noEarlyRows :
    TargetRoute (WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u})
  noStartRows :
    TargetRoute (WindowNoEarlyRowsW11.NoStartMatrix.{u, u})

/-- The checked source-facing target routes available in this tree. -/
def sourceFacingTargetRoutes : SourceFacingTargetRoutes.{u} where
  directFields := directFieldMatrixRoute
  k23Fields := k23FieldMatrixRoute
  commonNeighborFields := commonNeighborFieldMatrixRoute
  noEarlyRows := noEarlyMatrixRoute
  noStartRows := noStartMatrixRoute

/-- Integrated W11 Swanepoel target matrix.

The matrix stores checked route ledgers only; each route remains conditional on
one of the explicit source packages above. -/
structure Matrix : Type (u + 1) where
  sources : SourceFieldLedger.{u}
  importedTargets : ImportedTargetLedgers.{u}
  sourceFacingTargets : SourceFacingTargetRoutes.{u}

/-- The integrated W11 Swanepoel target matrix assembled from the checked
modules present in this tree. -/
def matrix : Matrix.{u} where
  sources := sourceFieldLedger
  importedTargets := importedTargetLedgers
  sourceFacingTargets := sourceFacingTargetRoutes

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_directFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.{u}.sourceFacingTargets.directFields.eliminator M

theorem no_minimalClearedFailure_of_directFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.{u}.sourceFacingTargets.directFields.noMinimal M

theorem pipelineCleared_of_directFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    PipelineCleared :=
  matrix.{u}.sourceFacingTargets.directFields.pipeline M

theorem targetClosure_of_directFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  matrix.{u}.sourceFacingTargets.directFields.target M

theorem minimalClearedFailureEliminator_of_k23FieldMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.{u}.sourceFacingTargets.k23Fields.eliminator M

theorem no_minimalClearedFailure_of_k23FieldMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.{u}.sourceFacingTargets.k23Fields.noMinimal M

theorem pipelineCleared_of_k23FieldMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    PipelineCleared :=
  matrix.{u}.sourceFacingTargets.k23Fields.pipeline M

theorem targetClosure_of_k23FieldMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  matrix.{u}.sourceFacingTargets.k23Fields.target M

theorem minimalClearedFailureEliminator_of_commonNeighborFieldMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.{u}.sourceFacingTargets.commonNeighborFields.eliminator M

theorem no_minimalClearedFailure_of_commonNeighborFieldMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.{u}.sourceFacingTargets.commonNeighborFields.noMinimal M

theorem pipelineCleared_of_commonNeighborFieldMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    PipelineCleared :=
  matrix.{u}.sourceFacingTargets.commonNeighborFields.pipeline M

theorem targetClosure_of_commonNeighborFieldMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.{u}.sourceFacingTargets.commonNeighborFields.target M

theorem no_minimalClearedFailure_of_noEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}) :
    MinimalFailureExclusion :=
  matrix.{u}.sourceFacingTargets.noEarlyRows.noMinimal M

theorem pipelineCleared_of_noEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}) :
    PipelineCleared :=
  matrix.{u}.sourceFacingTargets.noEarlyRows.pipeline M

theorem targetClosure_of_noEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}) :
    Target :=
  matrix.{u}.sourceFacingTargets.noEarlyRows.target M

theorem no_minimalClearedFailure_of_noStartMatrix
    (M : WindowNoEarlyRowsW11.NoStartMatrix.{u, u}) :
    MinimalFailureExclusion :=
  matrix.{u}.sourceFacingTargets.noStartRows.noMinimal M

theorem pipelineCleared_of_noStartMatrix
    (M : WindowNoEarlyRowsW11.NoStartMatrix.{u, u}) :
    PipelineCleared :=
  matrix.{u}.sourceFacingTargets.noStartRows.pipeline M

theorem targetClosure_of_noStartMatrix
    (M : WindowNoEarlyRowsW11.NoStartMatrix.{u, u}) :
    Target :=
  matrix.{u}.sourceFacingTargets.noStartRows.target M

end

end TargetIntegratedMatrixW11
end Swanepoel
end ErdosProblems1066
