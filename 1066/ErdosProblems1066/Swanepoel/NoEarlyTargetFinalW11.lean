import ErdosProblems1066.Swanepoel.NoEarlyFinalIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyTargetIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryLabelIntegratedW11
import ErdosProblems1066.Swanepoel.TargetLedgerConsistencyW11
import ErdosProblems1066.Swanepoel.SwanepoelW11ConsistencyMatrix
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# Final W11 no-early target consistency

This file is the target-facing consistency layer for the final W11 no-early
branch.  The row and matrix inputs keep the boundary-label prefix, window
fields, no-start fields, and concrete no-early fields visible.  Every target
projection below remains a route from one of those explicit inputs.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyTargetFinalW11

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

abbrev LabelPrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  NoEarlyTargetIntegratedW11.LabelPrefix.{u} C hmin

abbrev WindowFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : LabelPrefix.{u} C hmin) :=
  NoEarlyTargetIntegratedW11.WindowFields B

abbrev NoEarlyFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : LabelPrefix.{u} C hmin) :=
  NoEarlyTargetIntegratedW11.NoEarlyFields B

abbrev NoStartFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : LabelPrefix.{u} C hmin) :=
  NoEarlyTargetIntegratedW11.NoStartFields B

abbrev W11NoEarlyMatrix :=
  WindowNoEarlyRowsW11.NoEarlyMatrix.{u}

abbrev W11NoStartMatrix :=
  WindowNoEarlyRowsW11.NoStartMatrix.{u}

abbrev ExplicitNoEarlyMatrix :=
  NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}

abbrev ExplicitNoStartMatrix :=
  NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}

abbrev ExplicitNoStartNoEarlyMatrix :=
  NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u}

abbrev FinalIntegratedMatrix :=
  NoEarlyFinalIntegratedW11.FinalNoStartNoEarlyMatrix.{u}

abbrev TargetFacadeMatrix :=
  NoEarlyFinalIntegratedW11.TargetFacadeMatrix

/-! ## Explicit final rows -/

/-- One final no-early target row for a fixed minimal cleared failure. -/
structure Row
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  labelPrefix : LabelPrefix.{u} C hmin
  windowFields : WindowFields labelPrefix
  noStart : NoStartFields labelPrefix
  noEarly : NoEarlyFields labelPrefix

namespace Row

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- View the row as the final integrated no-start/no-early row. -/
def toFinalIntegratedRow
    (R : Row.{u} C hmin) :
    NoEarlyFinalIntegratedW11.Row.{u} C hmin where
  labelPrefix := R.labelPrefix
  windowFields := R.windowFields
  noStart := R.noStart
  noEarly := R.noEarly

/-- View the row as the target-facing explicit no-start/no-early row. -/
def toExplicitNoStartNoEarlyRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyRow.{u} C hmin :=
  R.toFinalIntegratedRow.toExplicitNoStartNoEarlyRow

/-- Project the concrete no-early half of the row. -/
def toExplicitNoEarlyRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyRow.{u} C hmin :=
  R.toExplicitNoStartNoEarlyRow.toExplicitNoEarlyRow

/-- Project the explicit no-start half of the row. -/
def toExplicitNoStartRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoStartRow.{u} C hmin :=
  R.toExplicitNoStartNoEarlyRow.toExplicitNoStartRow

/-- Project the row to checked W11 no-early rows. -/
def toW11NoEarlyRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toExplicitNoEarlyRow.toNoEarlyRow

/-- Project the row to checked W11 no-start rows. -/
def toW11NoStartRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoStartRow.{u} C hmin :=
  R.toExplicitNoStartRow.toNoStartRow

/-- Project the row to target-facing no-early rows. -/
def toNoEarlyTargetRow
    (R : Row.{u} C hmin) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRow C hmin :=
  R.toExplicitNoEarlyRow.toNoEarlyTargetRow

/-- Project the row to target-facing no-start rows. -/
def toNoStartTargetRow
    (R : Row.{u} C hmin) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRow C hmin :=
  R.toExplicitNoStartRow.toNoStartTargetRow

/-- The concrete no-early projection closes the fixed minimal failure. -/
theorem contradiction_via_noEarly
    (R : Row.{u} C hmin) :
    False :=
  R.toFinalIntegratedRow.contradiction_of_noEarly

/-- The explicit no-start projection closes the fixed minimal failure. -/
theorem contradiction_via_noStart
    (R : Row.{u} C hmin) :
    False :=
  R.toFinalIntegratedRow.contradiction_of_noStart

@[simp]
theorem toFinalIntegratedRow_labelPrefix
    (R : Row.{u} C hmin) :
    R.toFinalIntegratedRow.labelPrefix = R.labelPrefix :=
  rfl

@[simp]
theorem toFinalIntegratedRow_windowFields
    (R : Row.{u} C hmin) :
    R.toFinalIntegratedRow.windowFields = R.windowFields :=
  rfl

@[simp]
theorem toFinalIntegratedRow_noStart
    (R : Row.{u} C hmin) :
    R.toFinalIntegratedRow.noStart = R.noStart :=
  rfl

@[simp]
theorem toFinalIntegratedRow_noEarly
    (R : Row.{u} C hmin) :
    R.toFinalIntegratedRow.noEarly = R.noEarly :=
  rfl

end Row

/-! ## Uniform explicit inputs -/

/-- Uniform final no-early target rows for every minimal cleared failure. -/
structure FinalMatrixInput : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Row.{u} C hmin

namespace FinalMatrixInput

/-- Forget final target rows to the final integrated row family. -/
def toFinalIntegratedMatrix
    (M : FinalMatrixInput.{u}) :
    FinalIntegratedMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toFinalIntegratedRow

/-- Forget final target rows to the explicit no-start/no-early matrix. -/
def toExplicitNoStartNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    ExplicitNoStartNoEarlyMatrix.{u} :=
  M.toFinalIntegratedMatrix.toExplicitNoStartNoEarlyMatrix

/-- Project final target rows to explicit no-early matrices. -/
def toExplicitNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    ExplicitNoEarlyMatrix.{u} :=
  M.toExplicitNoStartNoEarlyMatrix.toExplicitNoEarlyMatrix

/-- Project final target rows to explicit no-start matrices. -/
def toExplicitNoStartMatrix
    (M : FinalMatrixInput.{u}) :
    ExplicitNoStartMatrix.{u} :=
  M.toExplicitNoStartNoEarlyMatrix.toExplicitNoStartMatrix

/-- Project final target rows to checked W11 no-early rows. -/
def toW11NoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    W11NoEarlyMatrix.{u} :=
  M.toFinalIntegratedMatrix.toW11NoEarlyMatrix

/-- Project final target rows to checked W11 no-start rows. -/
def toW11NoStartMatrix
    (M : FinalMatrixInput.{u}) :
    W11NoStartMatrix.{u} :=
  M.toFinalIntegratedMatrix.toW11NoStartMatrix

/-- Project final target rows to target-facing no-early row families. -/
def toNoEarlyTargetRowFamily
    (M : FinalMatrixInput.{u}) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily :=
  M.toFinalIntegratedMatrix.toNoEarlyTargetRowFamily

/-- Project final target rows to target-facing no-start row families. -/
def toNoStartTargetRowFamily
    (M : FinalMatrixInput.{u}) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRowFamily :=
  M.toFinalIntegratedMatrix.toNoStartTargetRowFamily

/-- Project final target rows to the W10 target facade. -/
def toTargetFacadeMatrix
    (M : FinalMatrixInput.{u}) :
    TargetFacadeMatrix :=
  M.toFinalIntegratedMatrix.toTargetFacadeMatrix

/-- Final target rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  M.toFinalIntegratedMatrix.no_minimalClearedFailure

/-- Final target rows supply the cleared-pipeline predicate. -/
theorem pipelineCleared
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  M.toFinalIntegratedMatrix.pipelineCleared

/-- Target projection through the final integrated no-early route. -/
theorem target_via_finalNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyFinalIntegratedW11.swanepoelTarget_of_finalNoEarlyMatrix
    M.toFinalIntegratedMatrix

/-- Target projection through the final integrated no-start route. -/
theorem target_via_finalNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyFinalIntegratedW11.swanepoelTarget_of_finalNoStartMatrix
    M.toFinalIntegratedMatrix

/-- Target projection through target-facing explicit no-early rows. -/
theorem target_via_explicitNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoEarlyMatrix
    M.toExplicitNoEarlyMatrix

/-- Target projection through target-facing explicit no-start rows. -/
theorem target_via_explicitNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoStartMatrix
    M.toExplicitNoStartMatrix

/-- Target projection through the W11 target integrated no-early route. -/
theorem target_via_targetIntegratedNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noEarlyMatrix
    M.toW11NoEarlyMatrix

/-- Target projection through the W11 target integrated no-start route. -/
theorem target_via_targetIntegratedNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noStartMatrix
    M.toW11NoStartMatrix

/-- Target projection through the W11 target-ledger consistency no-early
route. -/
theorem target_via_targetLedgerNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_noEarlyMatrix M.toW11NoEarlyMatrix

/-- Target projection through the W11 target-ledger consistency no-start
route. -/
theorem target_via_targetLedgerNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetLedgerConsistencyW11.target_of_noStartMatrix M.toW11NoStartMatrix

/-- Target projection through the broad W11 consistency no-early route. -/
theorem target_via_swanepoelConsistencyNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  SwanepoelW11ConsistencyMatrix.target_of_explicitNoEarlyMatrix
    M.toExplicitNoEarlyMatrix

end FinalMatrixInput

/-! ## Boundary-label bridge -/

/-- Convert integrated boundary-label rows to target-facing no-early rows. -/
def explicitNoEarlyMatrixOfBoundaryLabelIntegrated
    (M : BoundaryLabelIntegratedW11.Matrix.{u}) :
    ExplicitNoEarlyMatrix.{u} :=
  NoEarlyTargetIntegratedW11.explicitNoEarlyMatrixOfBoundaryLabelClosure
    M.toBoundaryLabelClosureMatrix

/-- Target projection from integrated boundary-label rows through the explicit
no-early target bridge. -/
theorem target_of_boundaryLabelIntegratedMatrix
    (M : BoundaryLabelIntegratedW11.Matrix.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoEarlyMatrix
    (explicitNoEarlyMatrixOfBoundaryLabelIntegrated M)

/-! ## Route rows -/

/-- Target-integrated route through final no-early rows. -/
def finalTargetIntegratedNoEarlyRoute :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_targetIntegratedNoEarly

/-- Target-integrated route through final no-start rows. -/
def finalTargetIntegratedNoStartRoute :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_targetIntegratedNoStart

/-- Swanepoel integrated route through final no-early rows. -/
def finalSwanepoelIntegratedNoEarlyRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_finalNoEarly

/-- Swanepoel integrated route through final no-start rows. -/
def finalSwanepoelIntegratedNoStartRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_finalNoStart

/-- Target closure route through target-facing no-early rows. -/
def finalTargetClosureNoEarlyRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_explicitNoEarly

/-- Target closure route through target-facing no-start rows. -/
def finalTargetClosureNoStartRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_explicitNoStart

/-- Target-integrated route from integrated boundary-label rows. -/
def boundaryLabelIntegratedTargetRoute :
    TargetIntegratedMatrixW11.TargetRoute
      (BoundaryLabelIntegratedW11.Matrix.{u}) where
  noMinimal := BoundaryLabelIntegratedW11.no_minimalClearedFailure_of_matrix
  pipeline := BoundaryLabelIntegratedW11.pipelineCleared_of_matrix
  target := target_of_boundaryLabelIntegratedMatrix

/-! ## Final consistency ledger -/

/-- Explicit input shapes owned by this final target layer. -/
structure ExplicitInputLedger : Type (u + 2) where
  pointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C), Type (u + 1)
  finalUniform : Type (u + 1)
  explicitNoEarlyUniform : Type (u + 1)
  explicitNoStartUniform : Type (u + 1)
  boundaryLabelUniform : Type (u + 1)

/-- The row and matrix input shapes used by the route rows above. -/
def explicitInputLedger : ExplicitInputLedger.{u} where
  pointwise := fun C hmin => Row.{u} C hmin
  finalUniform := FinalMatrixInput.{u}
  explicitNoEarlyUniform := ExplicitNoEarlyMatrix.{u}
  explicitNoStartUniform := ExplicitNoStartMatrix.{u}
  boundaryLabelUniform := BoundaryLabelIntegratedW11.Matrix.{u}

/-- Imported checked ledgers used by the final consistency layer. -/
structure ImportedLedgers : Type (u + 2) where
  noEarlyFinal : NoEarlyFinalIntegratedW11.Matrix.{u}
  noEarlyTarget : NoEarlyTargetIntegratedW11.Matrix.{u}
  boundaryLabelIntegrated : BoundaryLabelIntegratedW11.RouteMatrix.{u}
  targetLedgerConsistency : TargetLedgerConsistencyW11.Matrix.{u}
  swanepoelConsistencyNoEarly : ExplicitNoEarlyMatrix.{u} -> Target

/-- Checked ledgers imported by this file. -/
def importedLedgers : ImportedLedgers.{u} where
  noEarlyFinal := NoEarlyFinalIntegratedW11.matrix
  noEarlyTarget := NoEarlyTargetIntegratedW11.matrix
  boundaryLabelIntegrated := BoundaryLabelIntegratedW11.routeMatrix
  targetLedgerConsistency := TargetLedgerConsistencyW11.matrix
  swanepoelConsistencyNoEarly :=
    SwanepoelW11ConsistencyMatrix.target_of_explicitNoEarlyMatrix

/-- Conditional routes exposed by the final target layer. -/
structure ConditionalRoutes : Type (u + 1) where
  finalTargetIntegratedNoEarly :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u})
  finalTargetIntegratedNoStart :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u})
  finalSwanepoelIntegratedNoEarly :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalMatrixInput.{u})
  finalSwanepoelIntegratedNoStart :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalMatrixInput.{u})
  finalTargetClosureNoEarly :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u})
  finalTargetClosureNoStart :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u})
  boundaryLabelIntegrated :
    TargetIntegratedMatrixW11.TargetRoute
      (BoundaryLabelIntegratedW11.Matrix.{u})

/-- Checked conditional routes for the final no-early target layer. -/
def conditionalRoutes : ConditionalRoutes.{u} where
  finalTargetIntegratedNoEarly := finalTargetIntegratedNoEarlyRoute
  finalTargetIntegratedNoStart := finalTargetIntegratedNoStartRoute
  finalSwanepoelIntegratedNoEarly := finalSwanepoelIntegratedNoEarlyRoute
  finalSwanepoelIntegratedNoStart := finalSwanepoelIntegratedNoStartRoute
  finalTargetClosureNoEarly := finalTargetClosureNoEarlyRoute
  finalTargetClosureNoStart := finalTargetClosureNoStartRoute
  boundaryLabelIntegrated := boundaryLabelIntegratedTargetRoute

/-- Final W11 no-early target consistency matrix.

The matrix stores input shapes, imported ledgers, and route rows.  It does not
contain a uniform final input family.
-/
structure Matrix : Type (u + 2) where
  inputs : ExplicitInputLedger.{u}
  imported : ImportedLedgers.{u}
  routes : ConditionalRoutes.{u}

/-- The checked final W11 no-early target consistency matrix. -/
def matrix : Matrix.{u} where
  inputs := explicitInputLedger
  imported := importedLedgers
  routes := conditionalRoutes

/-! ## Public projections -/

/-- Minimal-failure exclusion from a supplied final input family. -/
theorem no_minimalClearedFailure_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  FinalMatrixInput.no_minimalClearedFailure M

/-- Cleared-pipeline projection from a supplied final input family. -/
theorem pipelineCleared_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  FinalMatrixInput.pipelineCleared M

/-- Target projection from a supplied final input family through no-early
rows. -/
theorem target_of_finalMatrix_via_noEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_targetIntegratedNoEarly M

/-- Target projection from a supplied final input family through no-start
rows. -/
theorem target_of_finalMatrix_via_noStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_targetIntegratedNoStart M

/-- Target projection from a supplied final input family through the explicit
no-early target-closure route. -/
theorem target_of_finalMatrix_via_explicitNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_explicitNoEarly M

/-- Target projection from a supplied final input family through the explicit
no-start target-closure route. -/
theorem target_of_finalMatrix_via_explicitNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_explicitNoStart M

/-- Target projection from a supplied integrated boundary-label matrix. -/
theorem target_of_boundaryLabelMatrix
    (M : BoundaryLabelIntegratedW11.Matrix.{u}) :
    Target :=
  target_of_boundaryLabelIntegratedMatrix M

end

end NoEarlyTargetFinalW11
end Swanepoel
end ErdosProblems1066
