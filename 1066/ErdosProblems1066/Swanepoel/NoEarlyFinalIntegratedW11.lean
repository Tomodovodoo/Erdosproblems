import ErdosProblems1066.Swanepoel.NoEarlyTargetIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryLabelIntegratedW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 no-early/no-start aggregate

This file is a terminal ledger for the W11 no-early and no-start branch.  The
row family below keeps the boundary-label prefix, local window data, explicit
no-start fields, and concrete no-early fields as visible inputs.  The target
routes are therefore conditional on a uniform family of those rows.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyFinalIntegratedW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  SwanepoelW11IntegratedMatrix.Target

abbrev MinimalFailureExclusion : Prop :=
  SwanepoelW11IntegratedMatrix.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SwanepoelW11IntegratedMatrix.PipelineCleared

abbrev LabelPrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  NoEarlyTargetIntegratedW11.LabelPrefix.{u} C hmin

abbrev WindowFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : LabelPrefix.{u} C hmin) :=
  NoEarlyTargetIntegratedW11.WindowFields B

abbrev NoStartFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : LabelPrefix.{u} C hmin) :=
  NoEarlyTargetIntegratedW11.NoStartFields B

abbrev NoEarlyFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : LabelPrefix.{u} C hmin) :=
  NoEarlyTargetIntegratedW11.NoEarlyFields B

abbrev W11NoEarlyMatrix :=
  WindowNoEarlyRowsW11.NoEarlyMatrix.{u}

abbrev W11NoStartMatrix :=
  WindowNoEarlyRowsW11.NoStartMatrix.{u}

abbrev TargetFacadeMatrix :=
  SwanepoelTargetFacadeW10.Matrix

/-! ## Explicit final rows -/

/-- One final no-start/no-early row with all local source fields displayed. -/
structure Row
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labelPrefix : LabelPrefix.{u} C hmin
  windowFields : WindowFields labelPrefix
  noStart : NoStartFields labelPrefix
  noEarly : NoEarlyFields labelPrefix

namespace Row

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- View a final row as the target-facing explicit no-start/no-early row. -/
def toExplicitNoStartNoEarlyRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyRow.{u} C hmin where
  labelPrefix := R.labelPrefix
  windowFields := R.windowFields
  noStart := R.noStart
  noEarly := R.noEarly

/-- Forget a final row to the explicit no-early row. -/
def toExplicitNoEarlyRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyRow.{u} C hmin :=
  R.toExplicitNoStartNoEarlyRow.toExplicitNoEarlyRow

/-- Forget a final row to the explicit no-start row. -/
def toExplicitNoStartRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoStartRow.{u} C hmin :=
  R.toExplicitNoStartNoEarlyRow.toExplicitNoStartRow

/-- Forget a final row to the source-facing no-early prefix row. -/
def toPrefixNoEarlyRow
    (R : Row.{u} C hmin) :
    NoEarlyIntegratedW11.PrefixNoEarlyRow.{u} C hmin :=
  R.toExplicitNoEarlyRow.toPrefixNoEarlyRow

/-- Forget a final row to the source-facing no-start prefix row. -/
def toPrefixNoStartRow
    (R : Row.{u} C hmin) :
    NoEarlyIntegratedW11.PrefixNoStartRow.{u} C hmin :=
  R.toExplicitNoStartRow.toPrefixNoStartRow

/-- The checked W11 no-early row selected by the final row. -/
def toNoEarlyRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toExplicitNoEarlyRow.toNoEarlyRow

/-- The checked W11 no-start row selected by the final row. -/
def toNoStartRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoStartRow.{u} C hmin :=
  R.toExplicitNoStartRow.toNoStartRow

/-- The target-facing no-early row selected by the final row. -/
def toNoEarlyTargetRow
    (R : Row.{u} C hmin) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRow C hmin :=
  R.toExplicitNoEarlyRow.toNoEarlyTargetRow

/-- The target-facing no-start row selected by the final row. -/
def toNoStartTargetRow
    (R : Row.{u} C hmin) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRow C hmin :=
  R.toExplicitNoStartRow.toNoStartTargetRow

/-- The no-early half of a final row closes the fixed minimal failure. -/
theorem contradiction_of_noEarly
    (R : Row.{u} C hmin) :
    False :=
  R.toExplicitNoStartNoEarlyRow.contradiction_of_noEarly

/-- The no-start half of a final row closes the fixed minimal failure. -/
theorem contradiction_of_noStart
    (R : Row.{u} C hmin) :
    False :=
  R.toExplicitNoStartNoEarlyRow.contradiction_of_noStart

@[simp]
theorem toExplicitNoStartNoEarlyRow_labelPrefix
    (R : Row.{u} C hmin) :
    R.toExplicitNoStartNoEarlyRow.labelPrefix = R.labelPrefix :=
  rfl

@[simp]
theorem toExplicitNoStartNoEarlyRow_windowFields
    (R : Row.{u} C hmin) :
    R.toExplicitNoStartNoEarlyRow.windowFields = R.windowFields :=
  rfl

@[simp]
theorem toExplicitNoStartNoEarlyRow_noStart
    (R : Row.{u} C hmin) :
    R.toExplicitNoStartNoEarlyRow.noStart = R.noStart :=
  rfl

@[simp]
theorem toExplicitNoStartNoEarlyRow_noEarly
    (R : Row.{u} C hmin) :
    R.toExplicitNoStartNoEarlyRow.noEarly = R.noEarly :=
  rfl

end Row

/-! ## Uniform final row families -/

/-- Uniform final rows for every minimal cleared failure. -/
structure FinalNoStartNoEarlyMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Row.{u} C hmin

namespace FinalNoStartNoEarlyMatrix

/-- Forget final rows to the target-facing explicit matrix. -/
def toExplicitNoStartNoEarlyMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toExplicitNoStartNoEarlyRow

/-- Forget final rows to uniform explicit no-early rows. -/
def toExplicitNoEarlyMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u} :=
  M.toExplicitNoStartNoEarlyMatrix.toExplicitNoEarlyMatrix

/-- Forget final rows to uniform explicit no-start rows. -/
def toExplicitNoStartMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u} :=
  M.toExplicitNoStartNoEarlyMatrix.toExplicitNoStartMatrix

/-- Forget final rows to the no-early prefix matrix. -/
def toPrefixNoEarlyMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u} :=
  M.toExplicitNoEarlyMatrix.toPrefixNoEarlyMatrix

/-- Forget final rows to the no-start prefix matrix. -/
def toPrefixNoStartMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    NoEarlyIntegratedW11.PrefixNoStartMatrix.{u} :=
  M.toExplicitNoStartMatrix.toPrefixNoStartMatrix

/-- Project final rows to the checked W11 no-early matrix. -/
def toW11NoEarlyMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    W11NoEarlyMatrix.{u} :=
  M.toExplicitNoStartNoEarlyMatrix.toW11NoEarlyMatrix

/-- Project final rows to the checked W11 no-start matrix. -/
def toW11NoStartMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    W11NoStartMatrix.{u} :=
  M.toExplicitNoStartNoEarlyMatrix.toW11NoStartMatrix

/-- Project final rows to the W10 target facade through no-early fields. -/
def toTargetFacadeMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    TargetFacadeMatrix :=
  M.toExplicitNoStartNoEarlyMatrix.toW10TargetFacadeMatrix

/-- Project final rows to target-facing no-early rows. -/
def toNoEarlyTargetRowFamily
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily :=
  M.toExplicitNoEarlyMatrix.toNoEarlyTargetRowFamily

/-- Project final rows to target-facing no-start rows. -/
def toNoStartTargetRowFamily
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRowFamily :=
  M.toExplicitNoStartMatrix.toNoStartTargetRowFamily

/-- Uniform final rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toExplicitNoStartNoEarlyMatrix.no_minimalClearedFailure

/-- Uniform final rows supply the cleared-pipeline predicate. -/
theorem pipelineCleared
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    PipelineCleared :=
  M.toExplicitNoStartNoEarlyMatrix.pipelineCleared

/-- Conditional Swanepoel target projection through checked no-early rows. -/
theorem swanepoelTarget_of_noEarly
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    Target :=
  SwanepoelW11IntegratedMatrix.targetLowerBoundEightThirtyOne_of_noEarlyMatrix
    M.toW11NoEarlyMatrix

/-- Conditional Swanepoel target projection through checked no-start rows. -/
theorem swanepoelTarget_of_noStart
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    Target :=
  SwanepoelW11IntegratedMatrix.targetLowerBoundEightThirtyOne_of_noStartMatrix
    M.toW11NoStartMatrix

end FinalNoStartNoEarlyMatrix

/-! ## Conditional route rows -/

/-- TargetIntegrated route through the checked no-early projection. -/
def targetIntegratedNoEarlyRoute :
    TargetIntegratedMatrixW11.TargetRoute
      (FinalNoStartNoEarlyMatrix.{u}) where
  noMinimal := FinalNoStartNoEarlyMatrix.no_minimalClearedFailure
  pipeline := FinalNoStartNoEarlyMatrix.pipelineCleared
  target := fun M =>
    TargetIntegratedMatrixW11.targetClosure_of_noEarlyMatrix
      M.toW11NoEarlyMatrix

/-- TargetIntegrated route through the checked no-start projection. -/
def targetIntegratedNoStartRoute :
    TargetIntegratedMatrixW11.TargetRoute
      (FinalNoStartNoEarlyMatrix.{u}) where
  noMinimal := FinalNoStartNoEarlyMatrix.no_minimalClearedFailure
  pipeline := FinalNoStartNoEarlyMatrix.pipelineCleared
  target := fun M =>
    TargetIntegratedMatrixW11.targetClosure_of_noStartMatrix
      M.toW11NoStartMatrix

/-- Swanepoel integrated route through checked no-early rows. -/
def swanepoelNoEarlyRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalNoStartNoEarlyMatrix.{u}) where
  noMinimal := FinalNoStartNoEarlyMatrix.no_minimalClearedFailure
  pipeline := FinalNoStartNoEarlyMatrix.pipelineCleared
  target := FinalNoStartNoEarlyMatrix.swanepoelTarget_of_noEarly

/-- Swanepoel integrated route through checked no-start rows. -/
def swanepoelNoStartRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalNoStartNoEarlyMatrix.{u}) where
  noMinimal := FinalNoStartNoEarlyMatrix.no_minimalClearedFailure
  pipeline := FinalNoStartNoEarlyMatrix.pipelineCleared
  target := FinalNoStartNoEarlyMatrix.swanepoelTarget_of_noStart

/-! ## Aggregate ledger -/

/-- Aggregate ledger for the final no-start/no-early branch. -/
structure Matrix : Type (u + 1) where
  noEarlyIntegrated :
    NoEarlyIntegratedW11.Matrix.{u}
  noEarlyTargetIntegrated :
    NoEarlyTargetIntegratedW11.Matrix.{u}
  boundaryLabelIntegrated :
    BoundaryLabelIntegratedW11.RouteMatrix.{u}
  targetIntegrated :
    TargetIntegratedMatrixW11.Matrix.{u}
  swanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.Matrix.{u}
  finalRowsToExplicit :
    FinalNoStartNoEarlyMatrix.{u} ->
      NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u}
  finalRowsToNoEarlyRows :
    FinalNoStartNoEarlyMatrix.{u} -> W11NoEarlyMatrix.{u}
  finalRowsToNoStartRows :
    FinalNoStartNoEarlyMatrix.{u} -> W11NoStartMatrix.{u}
  finalRowsToTargetFacade :
    FinalNoStartNoEarlyMatrix.{u} -> TargetFacadeMatrix
  targetIntegratedNoEarly :
    TargetIntegratedMatrixW11.TargetRoute
      (FinalNoStartNoEarlyMatrix.{u})
  targetIntegratedNoStart :
    TargetIntegratedMatrixW11.TargetRoute
      (FinalNoStartNoEarlyMatrix.{u})
  swanepoelNoEarly :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalNoStartNoEarlyMatrix.{u})
  swanepoelNoStart :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalNoStartNoEarlyMatrix.{u})

/-- Checked aggregate ledger assembled from existing W11 modules. -/
def matrix : Matrix.{u} where
  noEarlyIntegrated := NoEarlyIntegratedW11.matrix
  noEarlyTargetIntegrated := NoEarlyTargetIntegratedW11.matrix
  boundaryLabelIntegrated := BoundaryLabelIntegratedW11.routeMatrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  swanepoelIntegrated := SwanepoelW11IntegratedMatrix.matrix
  finalRowsToExplicit :=
    FinalNoStartNoEarlyMatrix.toExplicitNoStartNoEarlyMatrix
  finalRowsToNoEarlyRows := FinalNoStartNoEarlyMatrix.toW11NoEarlyMatrix
  finalRowsToNoStartRows := FinalNoStartNoEarlyMatrix.toW11NoStartMatrix
  finalRowsToTargetFacade := FinalNoStartNoEarlyMatrix.toTargetFacadeMatrix
  targetIntegratedNoEarly := targetIntegratedNoEarlyRoute
  targetIntegratedNoStart := targetIntegratedNoStartRoute
  swanepoelNoEarly := swanepoelNoEarlyRoute
  swanepoelNoStart := swanepoelNoStartRoute

/-! ## Public conditional projections -/

/-- Minimal-failure exclusion from a uniform final row family. -/
theorem no_minimalClearedFailure_of_finalMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    MinimalFailureExclusion :=
  M.no_minimalClearedFailure

/-- Cleared-pipeline projection from a uniform final row family. -/
theorem pipelineCleared_of_finalMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    PipelineCleared :=
  M.pipelineCleared

/-- Conditional Swanepoel target projection through final no-early fields. -/
theorem swanepoelTarget_of_finalNoEarlyMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    Target :=
  M.swanepoelTarget_of_noEarly

/-- Conditional Swanepoel target projection through final no-start fields. -/
theorem swanepoelTarget_of_finalNoStartMatrix
    (M : FinalNoStartNoEarlyMatrix.{u}) :
    Target :=
  M.swanepoelTarget_of_noStart

end

end NoEarlyFinalIntegratedW11
end Swanepoel
end ErdosProblems1066
