import ErdosProblems1066.Swanepoel.NoEarlyConsistencyFinalW11
import ErdosProblems1066.Swanepoel.NoEarlyTargetFinalW11
import ErdosProblems1066.Swanepoel.BoundaryLabelFinalIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelRouteSummaryFinalW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 no-early route summary

This is a compact no-early terminal summary.  It records the checked W11
ledgers used by the no-early route, packages the remaining explicit matrix
input, and exposes only target projections from that supplied input.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyRouteSummaryFinalW11

universe u

noncomputable section

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

/-! ## Checked ledgers -/

/-- Checked W11 ledgers summarized by the final no-early route file. -/
structure CheckedMatrices : Type (u + 2) where
  noEarlyConsistencyFinal :
    NoEarlyConsistencyFinalW11.Matrix.{u}
  noEarlyTargetFinal :
    NoEarlyTargetFinalW11.Matrix.{u}
  boundaryLabelFinal :
    BoundaryLabelFinalIntegratedW11.Matrix.{u}

/-- Imported checked W11 matrices. -/
def checkedMatrices : CheckedMatrices.{u} where
  noEarlyConsistencyFinal := NoEarlyConsistencyFinalW11.matrix
  noEarlyTargetFinal := NoEarlyTargetFinalW11.matrix
  boundaryLabelFinal := BoundaryLabelFinalIntegratedW11.matrix

/-! ## Explicit matrix input -/

/-- The explicit uniform matrix input for the final no-early route. -/
structure ExplicitMatrixInput : Type (u + 1) where
  noEarlyTargetFinal :
    NoEarlyTargetFinalW11.FinalMatrixInput.{u}
  boundaryLabelFinal :
    BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}

namespace ExplicitMatrixInput

/-- Combine the explicit no-early and boundary-label inputs into the final
consistency input. -/
def toConsistencyFinalMatrix
    (M : ExplicitMatrixInput.{u}) :
    NoEarlyConsistencyFinalW11.FinalMatrixInput.{u} where
  row := fun C hmin => {
    noEarlyFinal := M.noEarlyTargetFinal.row C hmin
    boundaryLabelFinal := M.boundaryLabelFinal.row C hmin
  }

/-- Project the no-early target-final matrix. -/
def toNoEarlyTargetFinalMatrix
    (M : ExplicitMatrixInput.{u}) :
    NoEarlyTargetFinalW11.FinalMatrixInput.{u} :=
  M.noEarlyTargetFinal

/-- Project the boundary-label final matrix. -/
def toBoundaryLabelFinalMatrix
    (M : ExplicitMatrixInput.{u}) :
    BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u} :=
  M.boundaryLabelFinal

/-- Project the target-facing explicit no-early matrix. -/
def toExplicitNoEarlyMatrix
    (M : ExplicitMatrixInput.{u}) :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u} :=
  M.toConsistencyFinalMatrix.toExplicitNoEarlyMatrix

/-- Project the target-facing explicit no-start matrix. -/
def toExplicitNoStartMatrix
    (M : ExplicitMatrixInput.{u}) :
    NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u} :=
  M.toConsistencyFinalMatrix.toExplicitNoStartMatrix

/-- Project the checked W11 no-early matrix. -/
def toW11NoEarlyMatrix
    (M : ExplicitMatrixInput.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} :=
  M.toConsistencyFinalMatrix.toW11NoEarlyMatrix

/-- Project the checked W11 no-start matrix. -/
def toW11NoStartMatrix
    (M : ExplicitMatrixInput.{u}) :
    WindowNoEarlyRowsW11.NoStartMatrix.{u} :=
  M.toConsistencyFinalMatrix.toW11NoStartMatrix

end ExplicitMatrixInput

/-- Input surfaces named by this route summary. -/
structure ExplicitInputSurfaces : Type (u + 2) where
  explicitMatrixInput : Type (u + 1)
  consistencyFinal : Type (u + 1)
  noEarlyTargetFinal : Type (u + 1)
  boundaryLabelFinal : Type (u + 1)
  explicitNoEarly : Type (u + 1)
  explicitNoStart : Type (u + 1)
  checkedNoEarly : Type (u + 1)
  checkedNoStart : Type (u + 1)

/-- The explicit input surfaces used by the conditional projections below. -/
def explicitInputSurfaces : ExplicitInputSurfaces.{u} where
  explicitMatrixInput := ExplicitMatrixInput.{u}
  consistencyFinal := NoEarlyConsistencyFinalW11.FinalMatrixInput.{u}
  noEarlyTargetFinal := NoEarlyTargetFinalW11.FinalMatrixInput.{u}
  boundaryLabelFinal :=
    BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}
  explicitNoEarly := NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}
  explicitNoStart := NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}
  checkedNoEarly := WindowNoEarlyRowsW11.NoEarlyMatrix.{u}
  checkedNoStart := WindowNoEarlyRowsW11.NoStartMatrix.{u}

/-! ## Conditional target projections -/

theorem target_of_explicitMatrix_via_noEarlyFinal
    (M : ExplicitMatrixInput.{u}) :
    Target :=
  NoEarlyConsistencyFinalW11.target_of_finalMatrix_via_noEarly
    M.toConsistencyFinalMatrix

theorem target_of_explicitMatrix_via_noStartFinal
    (M : ExplicitMatrixInput.{u}) :
    Target :=
  NoEarlyConsistencyFinalW11.target_of_finalMatrix_via_noStart
    M.toConsistencyFinalMatrix

theorem target_of_explicitMatrix_via_explicitNoEarly
    (M : ExplicitMatrixInput.{u}) :
    Target :=
  NoEarlyConsistencyFinalW11.target_of_finalMatrix_via_explicitNoEarly
    M.toConsistencyFinalMatrix

theorem target_of_explicitMatrix_via_explicitNoStart
    (M : ExplicitMatrixInput.{u}) :
    Target :=
  NoEarlyConsistencyFinalW11.target_of_finalMatrix_via_explicitNoStart
    M.toConsistencyFinalMatrix

theorem target_of_explicitMatrix_via_boundaryLabelFinal
    (M : ExplicitMatrixInput.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix
    M.boundaryLabelFinal

theorem target_of_explicitMatrix_via_boundaryLabelNoEarlyFinal
    (M : ExplicitMatrixInput.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_noEarlyFinal
    M.boundaryLabelFinal

theorem target_of_explicitMatrix_via_boundaryLabelNoStartFinal
    (M : ExplicitMatrixInput.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_noStartFinal
    M.boundaryLabelFinal

theorem target_of_explicitMatrix_via_targetConsistencyNoEarly
    (M : ExplicitMatrixInput.{u}) :
    Target :=
  NoEarlyConsistencyFinalW11.target_of_finalMatrix_via_targetConsistencyNoEarly
    M.toConsistencyFinalMatrix

theorem target_of_explicitMatrix_via_targetConsistencyNoStart
    (M : ExplicitMatrixInput.{u}) :
    Target :=
  NoEarlyConsistencyFinalW11.target_of_finalMatrix_via_targetConsistencyNoStart
    M.toConsistencyFinalMatrix

/-- Target projections retained by this final summary. -/
structure ConditionalTargetProjections : Type (u + 1) where
  noEarlyFinal :
    ExplicitMatrixInput.{u} -> Target
  noStartFinal :
    ExplicitMatrixInput.{u} -> Target
  explicitNoEarly :
    ExplicitMatrixInput.{u} -> Target
  explicitNoStart :
    ExplicitMatrixInput.{u} -> Target
  boundaryLabelFinal :
    ExplicitMatrixInput.{u} -> Target
  boundaryLabelNoEarlyFinal :
    ExplicitMatrixInput.{u} -> Target
  boundaryLabelNoStartFinal :
    ExplicitMatrixInput.{u} -> Target
  targetConsistencyNoEarly :
    ExplicitMatrixInput.{u} -> Target
  targetConsistencyNoStart :
    ExplicitMatrixInput.{u} -> Target

/-- Checked conditional target projections from an explicit no-early matrix
input. -/
def conditionalTargetProjections :
    ConditionalTargetProjections.{u} where
  noEarlyFinal := target_of_explicitMatrix_via_noEarlyFinal
  noStartFinal := target_of_explicitMatrix_via_noStartFinal
  explicitNoEarly := target_of_explicitMatrix_via_explicitNoEarly
  explicitNoStart := target_of_explicitMatrix_via_explicitNoStart
  boundaryLabelFinal := target_of_explicitMatrix_via_boundaryLabelFinal
  boundaryLabelNoEarlyFinal :=
    target_of_explicitMatrix_via_boundaryLabelNoEarlyFinal
  boundaryLabelNoStartFinal :=
    target_of_explicitMatrix_via_boundaryLabelNoStartFinal
  targetConsistencyNoEarly :=
    target_of_explicitMatrix_via_targetConsistencyNoEarly
  targetConsistencyNoStart :=
    target_of_explicitMatrix_via_targetConsistencyNoStart

/-! ## Final summary matrix -/

/-- Final W11 no-early route summary.

The matrix records checked ledgers, explicit input surfaces, and conditional
target projections.  It supplies no target proof without an explicit matrix
input.
-/
structure Matrix : Type (u + 2) where
  checked : CheckedMatrices.{u}
  inputs : ExplicitInputSurfaces.{u}
  projections : ConditionalTargetProjections.{u}

/-- The checked final W11 no-early route summary matrix. -/
def matrix : Matrix.{u} where
  checked := checkedMatrices
  inputs := explicitInputSurfaces
  projections := conditionalTargetProjections

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

end

end NoEarlyRouteSummaryFinalW11
end Swanepoel
end ErdosProblems1066
