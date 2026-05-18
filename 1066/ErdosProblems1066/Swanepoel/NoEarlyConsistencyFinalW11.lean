import ErdosProblems1066.Swanepoel.NoEarlyTargetFinalW11
import ErdosProblems1066.Swanepoel.NoEarlyFinalIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryLabelFinalIntegratedW11
import ErdosProblems1066.Swanepoel.TargetConsistencyFinalW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# Final W11 no-early consistency layer

This module is a final typed ledger for the W11 no-early branch.  It keeps the
last no-early/no-start row family and the boundary-label final row family as
explicit inputs, then exposes only projections that still require one of those
inputs.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyConsistencyFinalW11

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

abbrev FinalNoEarlyRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  NoEarlyTargetFinalW11.Row.{u} C hmin

abbrev BoundaryLabelFinalRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalFields.{u} C hmin

abbrev NoEarlyTargetFinalMatrix :=
  NoEarlyTargetFinalW11.FinalMatrixInput.{u}

abbrev NoEarlyFinalMatrix :=
  NoEarlyFinalIntegratedW11.FinalNoStartNoEarlyMatrix.{u}

abbrev BoundaryLabelFinalMatrix :=
  BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}

abbrev ExplicitNoEarlyMatrix :=
  NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}

abbrev ExplicitNoStartMatrix :=
  NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}

abbrev ExplicitNoStartNoEarlyMatrix :=
  NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u}

abbrev PrefixNoEarlyMatrix :=
  NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}

abbrev PrefixNoStartMatrix :=
  NoEarlyIntegratedW11.PrefixNoStartMatrix.{u}

abbrev W11NoEarlyMatrix :=
  WindowNoEarlyRowsW11.NoEarlyMatrix.{u}

abbrev W11NoStartMatrix :=
  WindowNoEarlyRowsW11.NoStartMatrix.{u}

/-! ## Explicit final rows -/

/-- One final no-early consistency row for a fixed minimal cleared failure. -/
structure Row
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  noEarlyFinal : FinalNoEarlyRow.{u} C hmin
  boundaryLabelFinal : BoundaryLabelFinalRow.{u} C hmin

namespace Row

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- View the row as the no-early target-final row. -/
def toNoEarlyTargetFinalRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetFinalW11.Row.{u} C hmin :=
  R.noEarlyFinal

/-- View the row as the final no-start/no-early integrated row. -/
def toNoEarlyFinalRow
    (R : Row.{u} C hmin) :
    NoEarlyFinalIntegratedW11.Row.{u} C hmin :=
  R.noEarlyFinal.toFinalIntegratedRow

/-- View the row as the boundary-label final row. -/
def toBoundaryLabelFinalRow
    (R : Row.{u} C hmin) :
    BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalFields.{u} C hmin :=
  R.boundaryLabelFinal

/-- Project the no-early target-final row to explicit no-start/no-early data. -/
def toExplicitNoStartNoEarlyRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyRow.{u} C hmin :=
  R.noEarlyFinal.toExplicitNoStartNoEarlyRow

/-- Project the no-early target-final row to explicit no-early data. -/
def toExplicitNoEarlyRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyRow.{u} C hmin :=
  R.noEarlyFinal.toExplicitNoEarlyRow

/-- Project the no-early target-final row to explicit no-start data. -/
def toExplicitNoStartRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoStartRow.{u} C hmin :=
  R.noEarlyFinal.toExplicitNoStartRow

/-- Project the row to checked W11 no-early rows. -/
def toW11NoEarlyRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.noEarlyFinal.toW11NoEarlyRow

/-- Project the row to checked W11 no-start rows. -/
def toW11NoStartRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoStartRow.{u} C hmin :=
  R.noEarlyFinal.toW11NoStartRow

/-- The no-early part of the row closes the fixed minimal failure. -/
theorem contradiction_via_noEarly
    (R : Row.{u} C hmin) :
    False :=
  R.noEarlyFinal.contradiction_via_noEarly

/-- The no-start part of the row closes the fixed minimal failure. -/
theorem contradiction_via_noStart
    (R : Row.{u} C hmin) :
    False :=
  R.noEarlyFinal.contradiction_via_noStart

/-- The boundary-label final row also closes the fixed minimal failure. -/
theorem contradiction_via_boundaryLabel
    (R : Row.{u} C hmin) :
    False :=
  R.boundaryLabelFinal.contradiction

@[simp]
theorem toNoEarlyTargetFinalRow_eq
    (R : Row.{u} C hmin) :
    R.toNoEarlyTargetFinalRow = R.noEarlyFinal :=
  rfl

@[simp]
theorem toBoundaryLabelFinalRow_eq
    (R : Row.{u} C hmin) :
    R.toBoundaryLabelFinalRow = R.boundaryLabelFinal :=
  rfl

end Row

/-! ## Uniform explicit inputs -/

/-- Uniform final no-early consistency rows for every minimal cleared failure. -/
structure FinalMatrixInput : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Row.{u} C hmin

namespace FinalMatrixInput

/-- Forget final rows to the no-early target-final input matrix. -/
def toNoEarlyTargetFinalMatrix
    (M : FinalMatrixInput.{u}) :
    NoEarlyTargetFinalMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toNoEarlyTargetFinalRow

/-- Forget final rows to the final no-start/no-early integrated matrix. -/
def toNoEarlyFinalMatrix
    (M : FinalMatrixInput.{u}) :
    NoEarlyFinalMatrix.{u} :=
  M.toNoEarlyTargetFinalMatrix.toFinalIntegratedMatrix

/-- Forget final rows to the boundary-label final matrix. -/
def toBoundaryLabelFinalMatrix
    (M : FinalMatrixInput.{u}) :
    BoundaryLabelFinalMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toBoundaryLabelFinalRow

/-- Project final rows to explicit no-start/no-early matrices. -/
def toExplicitNoStartNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    ExplicitNoStartNoEarlyMatrix.{u} :=
  M.toNoEarlyTargetFinalMatrix.toExplicitNoStartNoEarlyMatrix

/-- Project final rows to explicit no-early matrices. -/
def toExplicitNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    ExplicitNoEarlyMatrix.{u} :=
  M.toNoEarlyTargetFinalMatrix.toExplicitNoEarlyMatrix

/-- Project final rows to explicit no-start matrices. -/
def toExplicitNoStartMatrix
    (M : FinalMatrixInput.{u}) :
    ExplicitNoStartMatrix.{u} :=
  M.toNoEarlyTargetFinalMatrix.toExplicitNoStartMatrix

/-- Project final rows to the no-early prefix matrix. -/
def toPrefixNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    PrefixNoEarlyMatrix.{u} :=
  M.toNoEarlyFinalMatrix.toPrefixNoEarlyMatrix

/-- Project final rows to the no-start prefix matrix. -/
def toPrefixNoStartMatrix
    (M : FinalMatrixInput.{u}) :
    PrefixNoStartMatrix.{u} :=
  M.toNoEarlyFinalMatrix.toPrefixNoStartMatrix

/-- Project final rows to checked W11 no-early rows. -/
def toW11NoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    W11NoEarlyMatrix.{u} :=
  M.toNoEarlyTargetFinalMatrix.toW11NoEarlyMatrix

/-- Project final rows to checked W11 no-start rows. -/
def toW11NoStartMatrix
    (M : FinalMatrixInput.{u}) :
    W11NoStartMatrix.{u} :=
  M.toNoEarlyTargetFinalMatrix.toW11NoStartMatrix

/-- Project boundary-label final rows to explicit no-early matrices. -/
def toBoundaryLabelExplicitNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    ExplicitNoEarlyMatrix.{u} :=
  M.toBoundaryLabelFinalMatrix.toExplicitNoEarlyMatrix

/-- Project boundary-label final rows to checked W11 no-early rows. -/
def toBoundaryLabelW11NoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    W11NoEarlyMatrix.{u} :=
  M.toBoundaryLabelFinalMatrix.toW11NoEarlyMatrix

/-- Project boundary-label final rows to the induced checked W11 no-start rows. -/
def toBoundaryLabelW11NoStartMatrix
    (M : FinalMatrixInput.{u}) :
    W11NoStartMatrix.{u} :=
  M.toBoundaryLabelFinalMatrix.toW11NoStartMatrix

/-- Final no-early rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  NoEarlyTargetFinalW11.no_minimalClearedFailure_of_finalMatrix
    M.toNoEarlyTargetFinalMatrix

/-- Final no-early rows clear the shared target pipeline. -/
theorem pipelineCleared
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  NoEarlyTargetFinalW11.pipelineCleared_of_finalMatrix
    M.toNoEarlyTargetFinalMatrix

/-- Boundary-label final rows give the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator_via_boundaryLabel
    (M : FinalMatrixInput.{u}) :
    MinimalFailureEliminator :=
  BoundaryLabelFinalIntegratedW11.minimalClearedFailureEliminator_of_finalMatrix
    M.toBoundaryLabelFinalMatrix

/-- Boundary-label final rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure_via_boundaryLabel
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  BoundaryLabelFinalIntegratedW11.no_minimalClearedFailure_of_finalMatrix
    M.toBoundaryLabelFinalMatrix

/-- Boundary-label final rows clear the shared target pipeline. -/
theorem pipelineCleared_via_boundaryLabel
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  BoundaryLabelFinalIntegratedW11.pipelineCleared_of_finalMatrix
    M.toBoundaryLabelFinalMatrix

/-- Final consistency package projection through no-early prefix rows. -/
theorem no_minimalClearedFailure_via_finalConsistencyPrefixNoEarly
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  TargetLedgerConsistencyW11.no_minimalClearedFailure_of_prefixNoEarlyMatrix
    M.toPrefixNoEarlyMatrix

/-- Final consistency package pipeline through no-early prefix rows. -/
theorem pipelineCleared_via_finalConsistencyPrefixNoEarly
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  TargetLedgerConsistencyW11.pipelineCleared_of_prefixNoEarlyMatrix
    M.toPrefixNoEarlyMatrix

/-- Final consistency package projection through no-start prefix rows. -/
theorem no_minimalClearedFailure_via_finalConsistencyPrefixNoStart
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  TargetLedgerConsistencyW11.no_minimalClearedFailure_of_prefixNoStartMatrix
    M.toPrefixNoStartMatrix

/-- Final consistency package pipeline through no-start prefix rows. -/
theorem pipelineCleared_via_finalConsistencyPrefixNoStart
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  TargetLedgerConsistencyW11.pipelineCleared_of_prefixNoStartMatrix
    M.toPrefixNoStartMatrix

/-- Conditional target projection through final no-early rows. -/
theorem target_via_noEarlyFinal
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_noEarly
    M.toNoEarlyTargetFinalMatrix

/-- Conditional target projection through final no-start rows. -/
theorem target_via_noStartFinal
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_noStart
    M.toNoEarlyTargetFinalMatrix

/-- Conditional target projection through explicit no-early rows. -/
theorem target_via_explicitNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_explicitNoEarly
    M.toNoEarlyTargetFinalMatrix

/-- Conditional target projection through explicit no-start rows. -/
theorem target_via_explicitNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_explicitNoStart
    M.toNoEarlyTargetFinalMatrix

/-- Conditional target projection through boundary-label final rows. -/
theorem target_via_boundaryLabelFinal
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix
    M.toBoundaryLabelFinalMatrix

/-- Conditional target projection through the boundary-label no-early route. -/
theorem target_via_boundaryLabelNoEarlyFinal
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_noEarlyFinal
    M.toBoundaryLabelFinalMatrix

/-- Conditional target projection through the induced boundary-label no-start
route. -/
theorem target_via_boundaryLabelNoStartFinal
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_noStartFinal
    M.toBoundaryLabelFinalMatrix

/-- Conditional target projection through the final target-consistency ledger
and explicit no-early rows. -/
theorem target_via_targetConsistencyNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_noEarlyTargetMatrix
    M.toExplicitNoEarlyMatrix

/-- Conditional target projection through the final target-consistency ledger
and explicit no-start rows. -/
theorem target_via_targetConsistencyNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_noStartTargetMatrix
    M.toExplicitNoStartMatrix

/-- Conditional target projection through the final target-consistency ledger
and checked no-early rows. -/
theorem target_via_targetConsistencyCheckedNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_from_ledger_noEarlyMatrix
    M.toW11NoEarlyMatrix

/-- Conditional target projection through the final target-consistency ledger
and checked no-start rows. -/
theorem target_via_targetConsistencyCheckedNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_from_ledger_noStartMatrix
    M.toW11NoStartMatrix

end FinalMatrixInput

/-! ## Route ledgers -/

/-- Explicit input shapes owned by this final no-early consistency layer. -/
structure ExplicitFinalInputLedger : Type (u + 2) where
  pointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C), Type (u + 1)
  uniform : Type (u + 1)
  noEarlyTargetFinal : Type (u + 1)
  noEarlyFinal : Type (u + 1)
  boundaryLabelFinal : Type (u + 1)
  explicitNoEarly : Type (u + 1)
  explicitNoStart : Type (u + 1)
  checkedNoEarly : Type (u + 1)
  checkedNoStart : Type (u + 1)

/-- The explicit row and matrix input surfaces used by this layer. -/
def explicitFinalInputLedger : ExplicitFinalInputLedger.{u} where
  pointwise := fun C hmin => Row.{u} C hmin
  uniform := FinalMatrixInput.{u}
  noEarlyTargetFinal := NoEarlyTargetFinalMatrix.{u}
  noEarlyFinal := NoEarlyFinalMatrix.{u}
  boundaryLabelFinal := BoundaryLabelFinalMatrix.{u}
  explicitNoEarly := ExplicitNoEarlyMatrix.{u}
  explicitNoStart := ExplicitNoStartMatrix.{u}
  checkedNoEarly := W11NoEarlyMatrix.{u}
  checkedNoStart := W11NoStartMatrix.{u}

/-- Checked final ledgers imported by this consistency layer. -/
structure ImportedFinalLedgers : Type (u + 2) where
  noEarlyTargetFinal : NoEarlyTargetFinalW11.Matrix.{u}
  noEarlyFinalIntegrated : NoEarlyFinalIntegratedW11.Matrix.{u}
  boundaryLabelFinalIntegrated :
    BoundaryLabelFinalIntegratedW11.Matrix.{u}
  targetConsistencyFinal : TargetConsistencyFinalW11.Matrix.{u}
  finalConsistencyPrefixNoEarly :
    SwanepoelW11FinalConsistency.ClearedPackageRoute.{u + 2}
      (PrefixNoEarlyMatrix.{u})
  finalConsistencyPrefixNoStart :
    SwanepoelW11FinalConsistency.ClearedPackageRoute.{u + 2}
      (PrefixNoStartMatrix.{u})

/-- The imported final ledgers available in this tree. -/
def importedFinalLedgers : ImportedFinalLedgers.{u} where
  noEarlyTargetFinal := NoEarlyTargetFinalW11.matrix
  noEarlyFinalIntegrated := NoEarlyFinalIntegratedW11.matrix
  boundaryLabelFinalIntegrated := BoundaryLabelFinalIntegratedW11.matrix
  targetConsistencyFinal := TargetConsistencyFinalW11.matrix
  finalConsistencyPrefixNoEarly := {
    noMinimal :=
      TargetLedgerConsistencyW11.no_minimalClearedFailure_of_prefixNoEarlyMatrix
    pipeline := TargetLedgerConsistencyW11.pipelineCleared_of_prefixNoEarlyMatrix
  }
  finalConsistencyPrefixNoStart := {
    noMinimal :=
      TargetLedgerConsistencyW11.no_minimalClearedFailure_of_prefixNoStartMatrix
    pipeline := TargetLedgerConsistencyW11.pipelineCleared_of_prefixNoStartMatrix
  }

/-- Conditional route rows exposed by the final no-early consistency layer. -/
structure ConditionalTargetRoutes : Type (u + 1) where
  noEarlyFinal :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u})
  noStartFinal :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u})
  explicitNoEarly :
    TargetClosureMatrixW11.TargetProjectionRow (FinalMatrixInput.{u})
  explicitNoStart :
    TargetClosureMatrixW11.TargetProjectionRow (FinalMatrixInput.{u})
  boundaryLabelFinal :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalMatrixInput.{u})
  finalConsistencyPrefixNoEarly :
    SwanepoelW11FinalConsistency.ClearedPackageRoute.{u + 2}
      (FinalMatrixInput.{u})
  finalConsistencyPrefixNoStart :
    SwanepoelW11FinalConsistency.ClearedPackageRoute.{u + 2}
      (FinalMatrixInput.{u})

/-- Target route through final no-early rows. -/
def finalNoEarlyTargetRoute :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_noEarlyFinal

/-- Target route through final no-start rows. -/
def finalNoStartTargetRoute :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_noStartFinal

/-- Target-closure row through explicit no-early rows. -/
def explicitNoEarlyTargetRoute :
    TargetClosureMatrixW11.TargetProjectionRow (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_explicitNoEarly

/-- Target-closure row through explicit no-start rows. -/
def explicitNoStartTargetRoute :
    TargetClosureMatrixW11.TargetProjectionRow (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_explicitNoStart

/-- Target route through boundary-label final rows, with the eliminator shown. -/
def boundaryLabelFinalTargetRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalMatrixInput.{u}) where
  eliminator := FinalMatrixInput.minimalClearedFailureEliminator_via_boundaryLabel
  noMinimal := FinalMatrixInput.no_minimalClearedFailure_via_boundaryLabel
  pipeline := FinalMatrixInput.pipelineCleared_via_boundaryLabel
  target := FinalMatrixInput.target_via_boundaryLabelFinal

/-- Final consistency cleared package through no-early prefix rows. -/
def finalConsistencyPrefixNoEarlyRoute :
    SwanepoelW11FinalConsistency.ClearedPackageRoute.{u + 2}
      (FinalMatrixInput.{u}) where
  noMinimal :=
    FinalMatrixInput.no_minimalClearedFailure_via_finalConsistencyPrefixNoEarly
  pipeline :=
    FinalMatrixInput.pipelineCleared_via_finalConsistencyPrefixNoEarly

/-- Final consistency cleared package through no-start prefix rows. -/
def finalConsistencyPrefixNoStartRoute :
    SwanepoelW11FinalConsistency.ClearedPackageRoute.{u + 2}
      (FinalMatrixInput.{u}) where
  noMinimal :=
    FinalMatrixInput.no_minimalClearedFailure_via_finalConsistencyPrefixNoStart
  pipeline :=
    FinalMatrixInput.pipelineCleared_via_finalConsistencyPrefixNoStart

/-- Checked route rows exposed by this final consistency layer. -/
def conditionalTargetRoutes : ConditionalTargetRoutes.{u} where
  noEarlyFinal := finalNoEarlyTargetRoute
  noStartFinal := finalNoStartTargetRoute
  explicitNoEarly := explicitNoEarlyTargetRoute
  explicitNoStart := explicitNoStartTargetRoute
  boundaryLabelFinal := boundaryLabelFinalTargetRoute
  finalConsistencyPrefixNoEarly := finalConsistencyPrefixNoEarlyRoute
  finalConsistencyPrefixNoStart := finalConsistencyPrefixNoStartRoute

/-! ## Final ledger -/

/-- Final W11 no-early consistency matrix.

The matrix stores explicit input surfaces, imported checked ledgers, and
conditional route rows.  It does not supply a uniform final matrix itself.
-/
structure Matrix : Type (u + 2) where
  inputs : ExplicitFinalInputLedger.{u}
  imports : ImportedFinalLedgers.{u}
  routes : ConditionalTargetRoutes.{u}

/-- The checked final W11 no-early consistency matrix. -/
def matrix : Matrix.{u} where
  inputs := explicitFinalInputLedger
  imports := importedFinalLedgers
  routes := conditionalTargetRoutes

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

/-! ## Public projections -/

theorem no_minimalClearedFailure_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  FinalMatrixInput.no_minimalClearedFailure M

theorem pipelineCleared_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  FinalMatrixInput.pipelineCleared M

theorem minimalClearedFailureEliminator_of_finalMatrix_via_boundaryLabel
    (M : FinalMatrixInput.{u}) :
    MinimalFailureEliminator :=
  FinalMatrixInput.minimalClearedFailureEliminator_via_boundaryLabel M

theorem target_of_finalMatrix_via_noEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_noEarlyFinal M

theorem target_of_finalMatrix_via_noStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_noStartFinal M

theorem target_of_finalMatrix_via_explicitNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_explicitNoEarly M

theorem target_of_finalMatrix_via_explicitNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_explicitNoStart M

theorem target_of_finalMatrix_via_boundaryLabel
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_boundaryLabelFinal M

theorem target_of_finalMatrix_via_targetConsistencyNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_targetConsistencyNoEarly M

theorem target_of_finalMatrix_via_targetConsistencyNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_targetConsistencyNoStart M

end

end NoEarlyConsistencyFinalW11
end Swanepoel
end ErdosProblems1066
