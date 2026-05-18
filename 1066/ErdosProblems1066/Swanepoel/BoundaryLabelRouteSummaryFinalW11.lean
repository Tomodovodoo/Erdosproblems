import ErdosProblems1066.Swanepoel.BoundaryLabelTargetFinalW11
import ErdosProblems1066.Swanepoel.BoundaryLabelFinalIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyTargetFinalW11
import ErdosProblems1066.Swanepoel.SwanepoelRouteSummaryFinalW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalAggregate

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# Final W11 boundary-label route summary

This leaf summary records the boundary-label and no-early route surfaces used
by the final W11 Swanepoel ledgers.  It names the explicit row and matrix
inputs and exposes only target projections that still consume one of those
inputs.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelRouteSummaryFinalW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

abbrev BoundaryLabelTargetRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) :=
  BoundaryLabelTargetFinalW11.Row.{u} C hmin

abbrev BoundaryLabelFinalRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) :=
  BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalFields.{u} C hmin

abbrev NoEarlyTargetRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) :=
  NoEarlyTargetFinalW11.Row.{u} C hmin

abbrev BoundaryLabelTargetMatrix : Type (u + 1) :=
  BoundaryLabelTargetFinalW11.FinalMatrixInput.{u}

abbrev BoundaryLabelFinalMatrix : Type (u + 1) :=
  BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}

abbrev NoEarlyTargetMatrix : Type (u + 1) :=
  NoEarlyTargetFinalW11.FinalMatrixInput.{u}

abbrev BoundaryLabelIntegratedMatrix : Type (u + 1) :=
  BoundaryLabelIntegratedW11.Matrix.{u}

abbrev BoundaryLabelClosureMatrix : Type (u + 1) :=
  BoundaryLabelClosureW11.Matrix.{u}

abbrev FinalNoStartNoEarlyMatrix : Type (u + 1) :=
  NoEarlyFinalIntegratedW11.FinalNoStartNoEarlyMatrix.{u}

abbrev ExplicitNoEarlyMatrix : Type (u + 1) :=
  NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}

abbrev ExplicitNoStartMatrix : Type (u + 1) :=
  NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}

abbrev ExplicitNoStartNoEarlyMatrix : Type (u + 1) :=
  NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u}

abbrev W11NoEarlyMatrix : Type (u + 1) :=
  BoundaryLabelTargetFinalW11.W11NoEarlyMatrix.{u}

abbrev W11NoStartMatrix : Type (u + 1) :=
  BoundaryLabelTargetFinalW11.W11NoStartMatrix.{u}

/-! ## Checked ledgers -/

/-- Checked ledgers used by this route summary. -/
structure CheckedLedgers : Type (u + 4) where
  boundaryLabelTarget :
    BoundaryLabelTargetFinalW11.Matrix.{u}
  boundaryLabelFinal :
    BoundaryLabelFinalIntegratedW11.Matrix.{u}
  noEarlyTarget :
    NoEarlyTargetFinalW11.Matrix.{u}
  swanepoelRouteSummary :
    "ErdosProblems1066.Swanepoel.SwanepoelRouteSummaryFinalW11 imported for checked coexistence" =
    "ErdosProblems1066.Swanepoel.SwanepoelRouteSummaryFinalW11 imported for checked coexistence"
  swanepoelFinalAggregate :
    SwanepoelW11FinalAggregate.Matrix.{u}

/-- Checked ledger values imported by this file. -/
def checkedLedgers :
    CheckedLedgers.{u} where
  boundaryLabelTarget := BoundaryLabelTargetFinalW11.matrix
  boundaryLabelFinal := BoundaryLabelFinalIntegratedW11.matrix
  noEarlyTarget := NoEarlyTargetFinalW11.matrix
  swanepoelRouteSummary := rfl
  swanepoelFinalAggregate := SwanepoelW11FinalAggregate.matrix

/-! ## Explicit row and matrix surfaces -/

/-- Pointwise row surfaces retained by the summary. -/
structure ExplicitRows : Type (u + 2) where
  boundaryLabelTarget :
    forall {n : Nat} (C : _root_.UDConfig n),
      IsMinimalClearedFailure C -> Type (u + 1)
  boundaryLabelFinal :
    forall {n : Nat} (C : _root_.UDConfig n),
      IsMinimalClearedFailure C -> Type (u + 1)
  noEarlyTarget :
    forall {n : Nat} (C : _root_.UDConfig n),
      IsMinimalClearedFailure C -> Type (u + 1)

/-- The pointwise row shapes displayed by this file. -/
def explicitRows :
    ExplicitRows.{u} where
  boundaryLabelTarget := fun C hmin => BoundaryLabelTargetRow.{u} C hmin
  boundaryLabelFinal := fun C hmin => BoundaryLabelFinalRow.{u} C hmin
  noEarlyTarget := fun C hmin => NoEarlyTargetRow.{u} C hmin

/-- Uniform matrix surfaces retained by the summary. -/
structure ExplicitMatrices : Type (u + 2) where
  boundaryLabelTarget :
    Type (u + 1)
  boundaryLabelFinal :
    Type (u + 1)
  noEarlyTarget :
    Type (u + 1)
  boundaryLabelIntegrated :
    Type (u + 1)
  boundaryLabelClosure :
    Type (u + 1)
  finalNoStartNoEarly :
    Type (u + 1)
  explicitNoEarly :
    Type (u + 1)
  explicitNoStart :
    Type (u + 1)
  explicitNoStartNoEarly :
    Type (u + 1)
  w11NoEarly :
    Type (u + 1)
  w11NoStart :
    Type (u + 1)

/-- The explicit matrix shapes displayed by this summary. -/
def explicitMatrices :
    ExplicitMatrices.{u} where
  boundaryLabelTarget := BoundaryLabelTargetMatrix.{u}
  boundaryLabelFinal := BoundaryLabelFinalMatrix.{u}
  noEarlyTarget := NoEarlyTargetMatrix.{u}
  boundaryLabelIntegrated := BoundaryLabelIntegratedMatrix.{u}
  boundaryLabelClosure := BoundaryLabelClosureMatrix.{u}
  finalNoStartNoEarly := FinalNoStartNoEarlyMatrix.{u}
  explicitNoEarly := ExplicitNoEarlyMatrix.{u}
  explicitNoStart := ExplicitNoStartMatrix.{u}
  explicitNoStartNoEarly := ExplicitNoStartNoEarlyMatrix.{u}
  w11NoEarly := W11NoEarlyMatrix.{u}
  w11NoStart := W11NoStartMatrix.{u}

/-! ## Matrix projections -/

/-- Matrix adapters from the final boundary-label target input. -/
structure BoundaryLabelTargetMatrixAdapters : Type (u + 1) where
  boundaryLabelFinal :
    BoundaryLabelTargetMatrix.{u} -> BoundaryLabelFinalMatrix.{u}
  boundaryLabelIntegrated :
    BoundaryLabelTargetMatrix.{u} -> BoundaryLabelIntegratedMatrix.{u}
  finalNoStartNoEarly :
    BoundaryLabelTargetMatrix.{u} -> FinalNoStartNoEarlyMatrix.{u}
  explicitNoEarly :
    BoundaryLabelTargetMatrix.{u} -> ExplicitNoEarlyMatrix.{u}
  explicitNoStart :
    BoundaryLabelTargetMatrix.{u} -> ExplicitNoStartMatrix.{u}
  explicitNoStartNoEarly :
    BoundaryLabelTargetMatrix.{u} -> ExplicitNoStartNoEarlyMatrix.{u}
  w11NoEarly :
    BoundaryLabelTargetMatrix.{u} -> W11NoEarlyMatrix.{u}
  w11NoStart :
    BoundaryLabelTargetMatrix.{u} -> W11NoStartMatrix.{u}

/-- Checked adapters from the final boundary-label target input. -/
def boundaryLabelTargetMatrixAdapters :
    BoundaryLabelTargetMatrixAdapters.{u} where
  boundaryLabelFinal :=
    BoundaryLabelTargetFinalW11.FinalMatrixInput.toBoundaryLabelFinalMatrix
  boundaryLabelIntegrated :=
    BoundaryLabelTargetFinalW11.FinalMatrixInput.toBoundaryLabelIntegratedMatrix
  finalNoStartNoEarly :=
    BoundaryLabelTargetFinalW11.FinalMatrixInput.toNoEarlyFinalMatrix
  explicitNoEarly :=
    BoundaryLabelTargetFinalW11.FinalMatrixInput.toExplicitNoEarlyMatrix
  explicitNoStart :=
    BoundaryLabelTargetFinalW11.FinalMatrixInput.toExplicitNoStartMatrix
  explicitNoStartNoEarly :=
    BoundaryLabelTargetFinalW11.FinalMatrixInput.toExplicitNoStartNoEarlyMatrix
  w11NoEarly :=
    BoundaryLabelTargetFinalW11.FinalMatrixInput.toW11NoEarlyMatrix
  w11NoStart :=
    BoundaryLabelTargetFinalW11.FinalMatrixInput.toW11NoStartMatrix

/-! ## Conditional target projections -/

/-- Conditional projections from final boundary-label target matrices. -/
structure BoundaryLabelTargetProjections : Type (u + 1) where
  eliminator :
    BoundaryLabelTargetMatrix.{u} -> MinimalFailureEliminator
  noMinimal :
    BoundaryLabelTargetMatrix.{u} -> MinimalFailureExclusion
  pipeline :
    BoundaryLabelTargetMatrix.{u} -> PipelineCleared
  boundaryLabel :
    BoundaryLabelTargetMatrix.{u} -> Target
  explicitNoEarly :
    BoundaryLabelTargetMatrix.{u} -> Target
  explicitNoStart :
    BoundaryLabelTargetMatrix.{u} -> Target
  explicitNoStartNoEarly :
    BoundaryLabelTargetMatrix.{u} -> Target
  w11NoEarly :
    BoundaryLabelTargetMatrix.{u} -> Target
  w11NoStart :
    BoundaryLabelTargetMatrix.{u} -> Target
  finalNoEarly :
    BoundaryLabelTargetMatrix.{u} -> Target
  finalNoStart :
    BoundaryLabelTargetMatrix.{u} -> Target
  geometryTarget :
    BoundaryLabelTargetMatrix.{u} -> Target

/-- Checked conditional projections from final boundary-label target matrices. -/
def boundaryLabelTargetProjections :
    BoundaryLabelTargetProjections.{u} where
  eliminator :=
    BoundaryLabelTargetFinalW11.minimalClearedFailureEliminator_of_finalMatrix
  noMinimal := BoundaryLabelTargetFinalW11.no_minimalClearedFailure_of_finalMatrix
  pipeline := BoundaryLabelTargetFinalW11.pipelineCleared_of_finalMatrix
  boundaryLabel := BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_boundaryLabel
  explicitNoEarly :=
    BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_explicitNoEarly
  explicitNoStart :=
    BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_explicitNoStart
  explicitNoStartNoEarly :=
    BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_explicitNoStartNoEarly
  w11NoEarly := BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_w11NoEarly
  w11NoStart := BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_w11NoStart
  finalNoEarly :=
    BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_noEarlyFinal
  finalNoStart :=
    BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_noStartFinal
  geometryTarget :=
    BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_geometryTarget

/-- Conditional projections from final boundary-label matrices. -/
structure BoundaryLabelFinalProjections : Type (u + 1) where
  eliminator :
    BoundaryLabelFinalMatrix.{u} -> MinimalFailureEliminator
  noMinimal :
    BoundaryLabelFinalMatrix.{u} -> MinimalFailureExclusion
  pipeline :
    BoundaryLabelFinalMatrix.{u} -> PipelineCleared
  boundaryLabel :
    BoundaryLabelFinalMatrix.{u} -> Target
  noEarlyFinal :
    BoundaryLabelFinalMatrix.{u} -> Target
  noStartFinal :
    BoundaryLabelFinalMatrix.{u} -> Target
  geometryTarget :
    BoundaryLabelFinalMatrix.{u} -> Target

/-- Checked conditional projections from final boundary-label matrices. -/
def boundaryLabelFinalProjections :
    BoundaryLabelFinalProjections.{u} where
  eliminator :=
    BoundaryLabelFinalIntegratedW11.minimalClearedFailureEliminator_of_finalMatrix
  noMinimal := BoundaryLabelFinalIntegratedW11.no_minimalClearedFailure_of_finalMatrix
  pipeline := BoundaryLabelFinalIntegratedW11.pipelineCleared_of_finalMatrix
  boundaryLabel := BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix
  noEarlyFinal :=
    BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_noEarlyFinal
  noStartFinal :=
    BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_noStartFinal
  geometryTarget :=
    BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_geometryTarget

/-- Conditional projections from final no-early target matrices. -/
structure NoEarlyTargetProjections : Type (u + 1) where
  noMinimal :
    NoEarlyTargetMatrix.{u} -> MinimalFailureExclusion
  pipeline :
    NoEarlyTargetMatrix.{u} -> PipelineCleared
  noEarly :
    NoEarlyTargetMatrix.{u} -> Target
  noStart :
    NoEarlyTargetMatrix.{u} -> Target
  explicitNoEarly :
    NoEarlyTargetMatrix.{u} -> Target
  explicitNoStart :
    NoEarlyTargetMatrix.{u} -> Target

/-- Checked conditional projections from final no-early target matrices. -/
def noEarlyTargetProjections :
    NoEarlyTargetProjections.{u} where
  noMinimal := NoEarlyTargetFinalW11.no_minimalClearedFailure_of_finalMatrix
  pipeline := NoEarlyTargetFinalW11.pipelineCleared_of_finalMatrix
  noEarly := NoEarlyTargetFinalW11.target_of_finalMatrix_via_noEarly
  noStart := NoEarlyTargetFinalW11.target_of_finalMatrix_via_noStart
  explicitNoEarly :=
    NoEarlyTargetFinalW11.target_of_finalMatrix_via_explicitNoEarly
  explicitNoStart :=
    NoEarlyTargetFinalW11.target_of_finalMatrix_via_explicitNoStart

/-- Conditional projections from explicit no-early and no-start matrices. -/
structure ExplicitNoEarlyProjections : Type (u + 1) where
  noEarlyNoMinimal :
    ExplicitNoEarlyMatrix.{u} -> MinimalFailureExclusion
  noEarlyPipeline :
    ExplicitNoEarlyMatrix.{u} -> PipelineCleared
  noEarlyTarget :
    ExplicitNoEarlyMatrix.{u} -> Target
  noStartNoMinimal :
    ExplicitNoStartMatrix.{u} -> MinimalFailureExclusion
  noStartPipeline :
    ExplicitNoStartMatrix.{u} -> PipelineCleared
  noStartTarget :
    ExplicitNoStartMatrix.{u} -> Target
  combinedNoMinimal :
    ExplicitNoStartNoEarlyMatrix.{u} -> MinimalFailureExclusion
  combinedPipeline :
    ExplicitNoStartNoEarlyMatrix.{u} -> PipelineCleared
  combinedTarget :
    ExplicitNoStartNoEarlyMatrix.{u} -> Target

/-- Checked conditional projections from explicit no-early and no-start matrices. -/
def explicitNoEarlyProjections :
    ExplicitNoEarlyProjections.{u} where
  noEarlyNoMinimal :=
    NoEarlyTargetIntegratedW11.no_minimalClearedFailure_of_explicitNoEarlyMatrix
  noEarlyPipeline :=
    NoEarlyTargetIntegratedW11.pipelineCleared_of_explicitNoEarlyMatrix
  noEarlyTarget :=
    NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoEarlyMatrix
  noStartNoMinimal :=
    NoEarlyTargetIntegratedW11.no_minimalClearedFailure_of_explicitNoStartMatrix
  noStartPipeline :=
    NoEarlyTargetIntegratedW11.pipelineCleared_of_explicitNoStartMatrix
  noStartTarget :=
    NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoStartMatrix
  combinedNoMinimal :=
    NoEarlyTargetIntegratedW11.no_minimalClearedFailure_of_explicitNoStartNoEarlyMatrix
  combinedPipeline :=
    NoEarlyTargetIntegratedW11.pipelineCleared_of_explicitNoStartNoEarlyMatrix
  combinedTarget :=
    NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoStartNoEarlyMatrix

/-- Conditional projections re-exported through the final aggregate ledger. -/
structure AggregateProjections : Type (u + 1) where
  boundaryLabel :
    BoundaryLabelFinalMatrix.{u} -> Target
  boundaryLabelNoEarly :
    BoundaryLabelFinalMatrix.{u} -> Target
  boundaryLabelGeometry :
    BoundaryLabelFinalMatrix.{u} -> Target
  noEarly :
    NoEarlyTargetMatrix.{u} -> Target
  noStart :
    NoEarlyTargetMatrix.{u} -> Target
  explicitNoEarly :
    NoEarlyTargetMatrix.{u} -> Target
  boundaryLabelIntegrated :
    BoundaryLabelIntegratedMatrix.{u} -> Target
  explicitNoEarlyTarget :
    ExplicitNoEarlyMatrix.{u} -> Target

/-- Checked conditional projections re-exported through the final aggregate. -/
def aggregateProjections :
    AggregateProjections.{u} where
  boundaryLabel := SwanepoelW11FinalAggregate.target_of_boundaryLabelFinalMatrix
  boundaryLabelNoEarly :=
    SwanepoelW11FinalAggregate.target_of_boundaryLabelFinalMatrix_via_noEarlyFinal
  boundaryLabelGeometry :=
    SwanepoelW11FinalAggregate.target_of_boundaryLabelFinalMatrix_via_geometryTarget
  noEarly :=
    SwanepoelW11FinalAggregate.target_of_noEarlyTargetFinalMatrix_via_noEarly
  noStart :=
    SwanepoelW11FinalAggregate.target_of_noEarlyTargetFinalMatrix_via_noStart
  explicitNoEarly :=
    SwanepoelW11FinalAggregate.target_of_noEarlyTargetFinalMatrix_via_explicitNoEarly
  boundaryLabelIntegrated :=
    SwanepoelW11FinalAggregate.target_of_targetConsistency_boundaryLabelIntegratedMatrix
  explicitNoEarlyTarget :=
    SwanepoelW11FinalAggregate.target_of_targetConsistency_explicitNoEarlyMatrix

/-! ## Final summary matrix -/

/-- Optional route-summary files from the handoff that are not checked imports
of this module. -/
structure OptionalSummaryStatus where
  noEarlyRouteSummaryFinalW11 :
    "ErdosProblems1066.Swanepoel.NoEarlyRouteSummaryFinalW11 is absent from this worktree" =
    "ErdosProblems1066.Swanepoel.NoEarlyRouteSummaryFinalW11 is absent from this worktree"
  swanepoelFinalRouteSummaryW11 :
    "ErdosProblems1066.Swanepoel.SwanepoelFinalRouteSummaryW11 is present but omitted because the existing file fails the pinned Lean run" =
    "ErdosProblems1066.Swanepoel.SwanepoelFinalRouteSummaryW11 is present but omitted because the existing file fails the pinned Lean run"

/-- Status for optional summaries named in the handoff. -/
def optionalSummaryStatus :
    OptionalSummaryStatus where
  noEarlyRouteSummaryFinalW11 := rfl
  swanepoelFinalRouteSummaryW11 := rfl

/-- All conditional route projections exposed by this boundary-label summary. -/
structure ConditionalProjections : Type (u + 1) where
  boundaryLabelTarget :
    BoundaryLabelTargetProjections.{u}
  boundaryLabelFinal :
    BoundaryLabelFinalProjections.{u}
  noEarlyTarget :
    NoEarlyTargetProjections.{u}
  explicitNoEarly :
    ExplicitNoEarlyProjections.{u}
  aggregate :
    AggregateProjections.{u}

/-- Checked conditional route projections. -/
def conditionalProjections :
    ConditionalProjections.{u} where
  boundaryLabelTarget := boundaryLabelTargetProjections
  boundaryLabelFinal := boundaryLabelFinalProjections
  noEarlyTarget := noEarlyTargetProjections
  explicitNoEarly := explicitNoEarlyProjections
  aggregate := aggregateProjections

/-- Final boundary-label/no-early route summary matrix.

The matrix stores checked ledgers, explicit row and matrix surfaces, adapters,
and conditional projections. -/
structure Matrix : Type (u + 4) where
  checked :
    CheckedLedgers.{u}
  rows :
    ExplicitRows.{u}
  matrices :
    ExplicitMatrices.{u}
  adapters :
    BoundaryLabelTargetMatrixAdapters.{u}
  projections :
    ConditionalProjections.{u}
  optional :
    OptionalSummaryStatus

/-- The checked final boundary-label/no-early route summary. -/
def matrix :
    Matrix.{u} where
  checked := checkedLedgers
  rows := explicitRows
  matrices := explicitMatrices
  adapters := boundaryLabelTargetMatrixAdapters
  projections := conditionalProjections
  optional := optionalSummaryStatus

theorem matrix_nonempty :
    Nonempty Matrix.{u} :=
  Nonempty.intro matrix

theorem checked_boundaryLabelTarget :
    matrix.checked.boundaryLabelTarget =
      BoundaryLabelTargetFinalW11.matrix := by
  rfl

theorem checked_boundaryLabelFinal :
    matrix.checked.boundaryLabelFinal =
      BoundaryLabelFinalIntegratedW11.matrix := by
  rfl

theorem checked_noEarlyTarget :
    matrix.checked.noEarlyTarget =
      NoEarlyTargetFinalW11.matrix := by
  rfl

theorem checked_swanepoelFinalAggregate :
    matrix.checked.swanepoelFinalAggregate =
      SwanepoelW11FinalAggregate.matrix := by
  rfl

/-! ## Public conditional projections -/

theorem target_of_boundaryLabelTargetMatrix_via_boundaryLabel
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_boundaryLabel M

theorem target_of_boundaryLabelTargetMatrix_via_explicitNoEarly
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_explicitNoEarly M

theorem target_of_boundaryLabelTargetMatrix_via_explicitNoStart
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_explicitNoStart M

theorem target_of_boundaryLabelTargetMatrix_via_explicitNoStartNoEarly
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_explicitNoStartNoEarly M

theorem target_of_boundaryLabelTargetMatrix_via_w11NoEarly
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_w11NoEarly M

theorem target_of_boundaryLabelTargetMatrix_via_w11NoStart
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_w11NoStart M

theorem target_of_boundaryLabelTargetMatrix_via_noEarlyFinal
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_noEarlyFinal M

theorem target_of_boundaryLabelTargetMatrix_via_noStartFinal
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  BoundaryLabelTargetFinalW11.target_of_finalMatrix_via_noStartFinal M

theorem target_of_boundaryLabelFinalMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix M

theorem target_of_boundaryLabelFinalMatrix_via_noEarlyFinal
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_noEarlyFinal M

theorem target_of_boundaryLabelFinalMatrix_via_noStartFinal
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_noStartFinal M

theorem target_of_boundaryLabelFinalMatrix_via_geometryTarget
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_geometryTarget M

theorem target_of_noEarlyTargetMatrix_via_noEarly
    (M : NoEarlyTargetMatrix.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_noEarly M

theorem target_of_noEarlyTargetMatrix_via_noStart
    (M : NoEarlyTargetMatrix.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_noStart M

theorem target_of_noEarlyTargetMatrix_via_explicitNoEarly
    (M : NoEarlyTargetMatrix.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_explicitNoEarly M

theorem target_of_noEarlyTargetMatrix_via_explicitNoStart
    (M : NoEarlyTargetMatrix.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_explicitNoStart M

theorem target_of_explicitNoEarlyMatrix
    (M : ExplicitNoEarlyMatrix.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoEarlyMatrix M

theorem target_of_explicitNoStartMatrix
    (M : ExplicitNoStartMatrix.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoStartMatrix M

theorem target_of_explicitNoStartNoEarlyMatrix
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoStartNoEarlyMatrix M

theorem target_of_aggregate_boundaryLabelFinalMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_boundaryLabelFinalMatrix M

theorem target_of_aggregate_noEarlyTargetMatrix
    (M : NoEarlyTargetMatrix.{u}) :
    Target :=
  SwanepoelW11FinalAggregate.target_of_noEarlyTargetFinalMatrix_via_noEarly M

theorem target_of_importedSummary_boundaryLabelFinalMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix M

theorem target_of_importedSummary_noEarlyTargetMatrix
    (M : NoEarlyTargetMatrix.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_noEarly M

theorem no_minimalClearedFailure_of_boundaryLabelTargetMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    MinimalFailureExclusion :=
  BoundaryLabelTargetFinalW11.no_minimalClearedFailure_of_finalMatrix M

theorem pipelineCleared_of_boundaryLabelTargetMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    PipelineCleared :=
  BoundaryLabelTargetFinalW11.pipelineCleared_of_finalMatrix M

theorem minimalClearedFailureEliminator_of_boundaryLabelTargetMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    MinimalFailureEliminator :=
  BoundaryLabelTargetFinalW11.minimalClearedFailureEliminator_of_finalMatrix M

end

end BoundaryLabelRouteSummaryFinalW11
end Swanepoel
end ErdosProblems1066
