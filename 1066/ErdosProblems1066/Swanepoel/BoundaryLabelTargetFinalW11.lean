import ErdosProblems1066.Swanepoel.BoundaryLabelFinalIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryLabelTargetIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyFinalIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# Final W11 boundary-label/no-early target consistency

This module is the target-facing consistency layer for the final W11
boundary-label and no-early branch.  The row input keeps the label prefix,
containment package, and selected no-early route visible.  Every Swanepoel
target projection below consumes a supplied uniform input family.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelTargetFinalW11

open GeometryRemainingFieldsW10
open MinimalGraphFacts

universe u v

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

abbrev LabelPrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) :=
  BoundaryLabelFinalIntegratedW11.LabelPrefix.{u} C hmin

abbrev SourceFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) :=
  BoundaryLabelFinalIntegratedW11.SourceFields.{u} C hmin

abbrev NoEarlyRoute
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (source : SourceFields.{u} C hmin) :=
  BoundaryLabelFinalIntegratedW11.NoEarlyRoute.{u} source

abbrev BoundaryLabelFinalMatrix : Type (u + 1) :=
  BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalMatrix.{u}

abbrev BoundaryLabelTargetMatrix : Type (u + 1) :=
  BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetMatrix.{u}

abbrev BoundaryLabelIntegratedMatrix : Type (u + 1) :=
  BoundaryLabelIntegratedW11.Matrix.{u}

abbrev FinalNoStartNoEarlyMatrix : Type (u + 1) :=
  NoEarlyFinalIntegratedW11.FinalNoStartNoEarlyMatrix.{u}

abbrev ExplicitNoEarlyMatrix : Type (u + 1) :=
  NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}

abbrev ExplicitNoStartMatrix : Type (u + 1) :=
  NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u}

abbrev ExplicitNoStartNoEarlyMatrix : Type (u + 1) :=
  NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyMatrix.{u}

abbrev W11NoEarlyMatrix : Type (u + 1) :=
  WindowNoEarlyRowsW11.NoEarlyMatrix.{u}

abbrev W11NoStartMatrix : Type (u + 1) :=
  WindowNoEarlyRowsW11.NoStartMatrix.{u}

abbrev PrefixNoEarlyMatrix : Type (u + 1) :=
  NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}

abbrev PrefixNoStartMatrix : Type (u + 1) :=
  NoEarlyIntegratedW11.PrefixNoStartMatrix.{u}

abbrev GeometryTargetDirectMatrix : Type (u + 1) :=
  GeometryTargetIntegratedW11.DirectTargetMatrix.{u}

/-! ## Shared route records -/

/-- A checked route to the common cleared-pipeline propositions. -/
structure ClearedRoute (alpha : Type v) : Type v where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared

/-- A checked route to the Swanepoel target proposition from an explicit
input family. -/
structure TargetRoute (alpha : Type v) : Type v where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

/-! ## Explicit final rows -/

/-- One final boundary-label/no-early target row for a fixed minimal cleared
failure. -/
structure Row
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  labelPrefix : LabelPrefix.{u} C hmin
  containment : ContainmentFields labelPrefix.toGeometrySourceFields
  noEarly : NoEarlyRoute labelPrefix.toGeometrySourceFields

namespace Row

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The source geometry selected by the explicit label prefix. -/
def source
    (R : Row.{u} C hmin) :
    SourceFields.{u} C hmin :=
  R.labelPrefix.toGeometrySourceFields

/-- View the row as the final integrated boundary-label row. -/
def toBoundaryLabelFinalFields
    (R : Row.{u} C hmin) :
    BoundaryLabelFinalIntegratedW11.BoundaryLabelFinalFields.{u}
      C hmin where
  labelPrefix := R.labelPrefix
  containment := R.containment
  noEarly := R.noEarly

/-- View the row as the target-facing boundary-label row. -/
def toBoundaryLabelTargetFields
    (R : Row.{u} C hmin) :
    BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetFields.{u}
      C hmin :=
  R.toBoundaryLabelFinalFields.toBoundaryLabelTargetFields

/-- View the row as the source-facing boundary-label row. -/
def toBoundaryLabelIntegratedRow
    (R : Row.{u} C hmin) :
    BoundaryLabelIntegratedW11.Row.{u} C hmin :=
  R.toBoundaryLabelFinalFields.toBoundaryLabelIntegratedRow

/-- View the row as the final no-start/no-early row. -/
def toNoEarlyFinalRow
    (R : Row.{u} C hmin) :
    NoEarlyFinalIntegratedW11.Row.{u} C hmin :=
  R.toBoundaryLabelFinalFields.toNoEarlyFinalRow

/-- View the row as the target-facing explicit no-start/no-early row. -/
def toExplicitNoStartNoEarlyRow
    (R : Row.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoStartNoEarlyRow.{u} C hmin :=
  R.toNoEarlyFinalRow.toExplicitNoStartNoEarlyRow

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
  R.toBoundaryLabelFinalFields.toW11NoEarlyRow

/-- Project the row to checked W11 no-start rows. -/
def toW11NoStartRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoStartRow.{u} C hmin :=
  R.toBoundaryLabelFinalFields.toW11NoStartRow

/-- Project the row to target-facing direct geometry fields. -/
def toGeometryTargetDirectFields
    (R : Row.{u} C hmin) :
    GeometryTargetIntegratedW11.DirectTargetFields.{u} C hmin :=
  R.toBoundaryLabelFinalFields.toGeometryTargetDirectFields

/-- Project the row to source-facing broken-lattice direct fields. -/
def toBrokenLatticeDirectFieldPackage
    (R : Row.{u} C hmin) :
    BrokenLatticeIntegratedW11.DirectFieldPackage.{u} C hmin :=
  R.toBoundaryLabelFinalFields.toBrokenLatticeDirectFieldPackage

/-- The boundary-label projection closes the fixed minimal failure. -/
theorem contradiction_via_boundaryLabel
    (R : Row.{u} C hmin) :
    False :=
  R.toBoundaryLabelFinalFields.contradiction

/-- The concrete no-early projection closes the fixed minimal failure. -/
theorem contradiction_via_noEarly
    (R : Row.{u} C hmin) :
    False :=
  R.toNoEarlyFinalRow.contradiction_of_noEarly

/-- The explicit no-start projection closes the fixed minimal failure. -/
theorem contradiction_via_noStart
    (R : Row.{u} C hmin) :
    False :=
  R.toNoEarlyFinalRow.contradiction_of_noStart

@[simp]
theorem toBoundaryLabelFinalFields_labelPrefix
    (R : Row.{u} C hmin) :
    R.toBoundaryLabelFinalFields.labelPrefix = R.labelPrefix :=
  rfl

@[simp]
theorem toBoundaryLabelFinalFields_containment
    (R : Row.{u} C hmin) :
    R.toBoundaryLabelFinalFields.containment = R.containment :=
  rfl

@[simp]
theorem toBoundaryLabelFinalFields_noEarly
    (R : Row.{u} C hmin) :
    R.toBoundaryLabelFinalFields.noEarly = R.noEarly :=
  rfl

end Row

/-! ## Uniform explicit inputs -/

/-- Uniform final boundary-label/no-early rows for every minimal cleared
failure. -/
structure FinalMatrixInput : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Row.{u} C hmin

namespace FinalMatrixInput

/-- Forget final target rows to the final boundary-label integrated matrix. -/
def toBoundaryLabelFinalMatrix
    (M : FinalMatrixInput.{u}) :
    BoundaryLabelFinalMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toBoundaryLabelFinalFields

/-- Forget final target rows to the target-facing boundary-label matrix. -/
def toBoundaryLabelTargetMatrix
    (M : FinalMatrixInput.{u}) :
    BoundaryLabelTargetMatrix.{u} :=
  M.toBoundaryLabelFinalMatrix.toBoundaryLabelTargetMatrix

/-- Forget final target rows to the source-facing boundary-label matrix. -/
def toBoundaryLabelIntegratedMatrix
    (M : FinalMatrixInput.{u}) :
    BoundaryLabelIntegratedMatrix.{u} :=
  M.toBoundaryLabelFinalMatrix.toBoundaryLabelIntegratedMatrix

/-- Forget final target rows to the final no-start/no-early matrix. -/
def toNoEarlyFinalMatrix
    (M : FinalMatrixInput.{u}) :
    FinalNoStartNoEarlyMatrix.{u} :=
  M.toBoundaryLabelFinalMatrix.toNoEarlyFinalMatrix

/-- Project final target rows to explicit no-start/no-early matrices. -/
def toExplicitNoStartNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    ExplicitNoStartNoEarlyMatrix.{u} :=
  M.toNoEarlyFinalMatrix.toExplicitNoStartNoEarlyMatrix

/-- Project final target rows to explicit no-early matrices. -/
def toExplicitNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    ExplicitNoEarlyMatrix.{u} :=
  M.toNoEarlyFinalMatrix.toExplicitNoEarlyMatrix

/-- Project final target rows to explicit no-start matrices. -/
def toExplicitNoStartMatrix
    (M : FinalMatrixInput.{u}) :
    ExplicitNoStartMatrix.{u} :=
  M.toNoEarlyFinalMatrix.toExplicitNoStartMatrix

/-- Project final target rows to checked W11 no-early rows. -/
def toW11NoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    W11NoEarlyMatrix.{u} :=
  M.toBoundaryLabelFinalMatrix.toW11NoEarlyMatrix

/-- Project final target rows to checked W11 no-start rows. -/
def toW11NoStartMatrix
    (M : FinalMatrixInput.{u}) :
    W11NoStartMatrix.{u} :=
  M.toBoundaryLabelFinalMatrix.toW11NoStartMatrix

/-- Project final target rows to no-early prefix rows. -/
def toPrefixNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    PrefixNoEarlyMatrix.{u} :=
  M.toNoEarlyFinalMatrix.toPrefixNoEarlyMatrix

/-- Project final target rows to no-start prefix rows. -/
def toPrefixNoStartMatrix
    (M : FinalMatrixInput.{u}) :
    PrefixNoStartMatrix.{u} :=
  M.toNoEarlyFinalMatrix.toPrefixNoStartMatrix

/-- Project final target rows to target-facing direct geometry rows. -/
def toGeometryTargetDirectMatrix
    (M : FinalMatrixInput.{u}) :
    GeometryTargetDirectMatrix.{u} :=
  M.toBoundaryLabelFinalMatrix.toGeometryTargetDirectMatrix

/-- Final rows provide the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : FinalMatrixInput.{u}) :
    MinimalFailureEliminator :=
  BoundaryLabelFinalIntegratedW11.minimalClearedFailureEliminator_of_finalMatrix
    M.toBoundaryLabelFinalMatrix

/-- Final rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  BoundaryLabelFinalIntegratedW11.no_minimalClearedFailure_of_finalMatrix
    M.toBoundaryLabelFinalMatrix

/-- Final rows supply the cleared-pipeline predicate. -/
theorem pipelineCleared
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  BoundaryLabelFinalIntegratedW11.pipelineCleared_of_finalMatrix
    M.toBoundaryLabelFinalMatrix

/-- Target projection through the final boundary-label integrated route. -/
theorem target_via_boundaryLabelFinal
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix
    M.toBoundaryLabelFinalMatrix

/-- Target projection through the boundary-label target route. -/
theorem target_via_boundaryLabelTarget
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix
    M.toBoundaryLabelTargetMatrix

/-- Target projection through source-facing boundary labels. -/
theorem target_via_boundaryLabelIntegrated
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix_via_boundaryLabels
    M.toBoundaryLabelTargetMatrix

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

/-- Target projection through target-facing explicit no-start/no-early rows. -/
theorem target_via_explicitNoStartNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoStartNoEarlyMatrix
    M.toExplicitNoStartNoEarlyMatrix

/-- Target projection through final no-early rows. -/
theorem target_via_noEarlyFinal
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyFinalIntegratedW11.swanepoelTarget_of_finalNoEarlyMatrix
    M.toNoEarlyFinalMatrix

/-- Target projection through final no-start rows. -/
theorem target_via_noStartFinal
    (M : FinalMatrixInput.{u}) :
    Target :=
  NoEarlyFinalIntegratedW11.swanepoelTarget_of_finalNoStartMatrix
    M.toNoEarlyFinalMatrix

/-- Target projection through checked W11 no-early rows. -/
theorem target_via_w11NoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noEarlyMatrix
    M.toW11NoEarlyMatrix

/-- Target projection through checked W11 no-start rows. -/
theorem target_via_w11NoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noStartMatrix
    M.toW11NoStartMatrix

/-- Target projection through target-facing direct geometry rows. -/
theorem target_via_geometryTarget
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryLabelFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_geometryTarget
    M.toBoundaryLabelFinalMatrix

end FinalMatrixInput

/-! ## Input and import ledgers -/

/-- Explicit input shapes owned by this target-facing boundary-label layer. -/
structure ExplicitInputLedger : Type (u + 2) where
  pointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C), Type (u + 1)
  finalUniform : Type (u + 1)
  boundaryLabelFinalUniform : Type (u + 1)
  boundaryLabelTargetUniform : Type (u + 1)
  boundaryLabelIntegratedUniform : Type (u + 1)
  noEarlyFinalUniform : Type (u + 1)
  explicitNoEarlyUniform : Type (u + 1)
  explicitNoStartUniform : Type (u + 1)
  explicitNoStartNoEarlyUniform : Type (u + 1)
  w11NoEarlyUniform : Type (u + 1)
  w11NoStartUniform : Type (u + 1)
  geometryTargetDirectUniform : Type (u + 1)

/-- The explicit final input surface and its checked projections. -/
def explicitInputLedger : ExplicitInputLedger.{u} where
  pointwise := fun C hmin => Row.{u} C hmin
  finalUniform := FinalMatrixInput.{u}
  boundaryLabelFinalUniform := BoundaryLabelFinalMatrix.{u}
  boundaryLabelTargetUniform := BoundaryLabelTargetMatrix.{u}
  boundaryLabelIntegratedUniform := BoundaryLabelIntegratedMatrix.{u}
  noEarlyFinalUniform := FinalNoStartNoEarlyMatrix.{u}
  explicitNoEarlyUniform := ExplicitNoEarlyMatrix.{u}
  explicitNoStartUniform := ExplicitNoStartMatrix.{u}
  explicitNoStartNoEarlyUniform := ExplicitNoStartNoEarlyMatrix.{u}
  w11NoEarlyUniform := W11NoEarlyMatrix.{u}
  w11NoStartUniform := W11NoStartMatrix.{u}
  geometryTargetDirectUniform := GeometryTargetDirectMatrix.{u}

/-- Checked ledgers imported by this target-facing wrapper. -/
structure ImportedLedgers : Type (u + 2) where
  boundaryLabelFinal : BoundaryLabelFinalIntegratedW11.Matrix.{u}
  boundaryLabelTarget : BoundaryLabelTargetIntegratedW11.Matrix.{u}
  noEarlyFinal : NoEarlyFinalIntegratedW11.Matrix.{u}
  swanepoelW11FinalConsistency :
    "ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency imported for checked coexistence" =
    "ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency imported for checked coexistence"
  boundaryAngleTargetFinalW11 :
    "ErdosProblems1066.Swanepoel.BoundaryAngleTargetFinalW11 import blocked: existing file has universe metavariables in public projections" =
    "ErdosProblems1066.Swanepoel.BoundaryAngleTargetFinalW11 import blocked: existing file has universe metavariables in public projections"

/-- The imported ledgers checked together for this file. -/
def importedLedgers : ImportedLedgers.{u} where
  boundaryLabelFinal := BoundaryLabelFinalIntegratedW11.matrix
  boundaryLabelTarget := BoundaryLabelTargetIntegratedW11.matrix
  noEarlyFinal := NoEarlyFinalIntegratedW11.matrix
  swanepoelW11FinalConsistency := rfl
  boundaryAngleTargetFinalW11 := rfl

/-! ## Conditional route rows -/

/-- Final boundary-label rows through target-integrated fields. -/
def finalBoundaryLabelTargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalMatrixInput.{u}) where
  eliminator := FinalMatrixInput.minimalClearedFailureEliminator
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_boundaryLabelTarget

/-- Final boundary-label rows through the target-closure boundary-label
route. -/
def finalBoundaryLabelTargetClosureRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_boundaryLabelFinal

/-- Final rows routed through target-facing explicit no-early rows. -/
def finalExplicitNoEarlyTargetRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_explicitNoEarly

/-- Final rows routed through target-facing explicit no-start rows. -/
def finalExplicitNoStartTargetRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_explicitNoStart

/-- Final rows routed through target-facing explicit no-start/no-early rows. -/
def finalExplicitNoStartNoEarlyTargetRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_explicitNoStartNoEarly

/-- Final rows routed through checked W11 no-early rows. -/
def finalW11NoEarlyTargetRoute :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_w11NoEarly

/-- Final rows routed through checked W11 no-start rows. -/
def finalW11NoStartTargetRoute :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_w11NoStart

/-- Final rows routed through the no-early final aggregate. -/
def finalNoEarlySwanepoelRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_noEarlyFinal

/-- Final rows routed through the no-start final aggregate. -/
def finalNoStartSwanepoelRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_noStartFinal

/-- Final rows routed through target-facing geometry. -/
def finalGeometryTargetRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure
  pipeline := FinalMatrixInput.pipelineCleared
  target := FinalMatrixInput.target_via_geometryTarget

/-- Boundary-label/no-early target routes exposed by this final layer. -/
structure BoundaryLabelNoEarlyTargetRoutes : Type (u + 1) where
  boundaryLabelIntegrated :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalMatrixInput.{u})
  boundaryLabelClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u})
  explicitNoEarly :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u})
  explicitNoStart :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u})
  explicitNoStartNoEarly :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u})
  w11NoEarly :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u})
  w11NoStart :
    TargetIntegratedMatrixW11.TargetRoute (FinalMatrixInput.{u})
  noEarlyFinal :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalMatrixInput.{u})
  noStartFinal :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalMatrixInput.{u})
  geometryTarget :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u})

/-- Checked target routes from explicit final boundary-label/no-early rows. -/
def boundaryLabelNoEarlyTargetRoutes :
    BoundaryLabelNoEarlyTargetRoutes.{u} where
  boundaryLabelIntegrated := finalBoundaryLabelTargetIntegratedRoute
  boundaryLabelClosure := finalBoundaryLabelTargetClosureRoute
  explicitNoEarly := finalExplicitNoEarlyTargetRoute
  explicitNoStart := finalExplicitNoStartTargetRoute
  explicitNoStartNoEarly := finalExplicitNoStartNoEarlyTargetRoute
  w11NoEarly := finalW11NoEarlyTargetRoute
  w11NoStart := finalW11NoStartTargetRoute
  noEarlyFinal := finalNoEarlySwanepoelRoute
  noStartFinal := finalNoStartSwanepoelRoute
  geometryTarget := finalGeometryTargetRoute

/-- All checked conditional routes exposed by this final target layer. -/
structure ConditionalSwanepoelTargetRoutes : Type (u + 1) where
  boundaryLabelNoEarly : BoundaryLabelNoEarlyTargetRoutes.{u}

/-- Checked conditional routes from explicit final boundary-label matrices. -/
def conditionalSwanepoelTargetRoutes :
    ConditionalSwanepoelTargetRoutes.{u} where
  boundaryLabelNoEarly := boundaryLabelNoEarlyTargetRoutes

/-! ## Final matrix -/

/-- Final target-facing boundary-label/no-early consistency matrix.

The matrix stores input shapes, checked imports, and conditional routes.  It
does not provide a final boundary-label/no-early input family.
-/
structure Matrix : Type (u + 2) where
  inputs : ExplicitInputLedger.{u}
  imported : ImportedLedgers.{u}
  routes : ConditionalSwanepoelTargetRoutes.{u}

/-- The checked final target-facing boundary-label/no-early consistency
matrix. -/
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
  FinalMatrixInput.no_minimalClearedFailure M

/-- Cleared-pipeline projection from a supplied final input family. -/
theorem pipelineCleared_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  FinalMatrixInput.pipelineCleared M

/-- Pointwise minimal-failure eliminator from a supplied final input family. -/
theorem minimalClearedFailureEliminator_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    MinimalFailureEliminator :=
  FinalMatrixInput.minimalClearedFailureEliminator M

/-- Target projection through the boundary-label final route. -/
theorem target_of_finalMatrix_via_boundaryLabel
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_boundaryLabelTarget M

/-- Target projection through target-facing explicit no-early rows. -/
theorem target_of_finalMatrix_via_explicitNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_explicitNoEarly M

/-- Target projection through target-facing explicit no-start rows. -/
theorem target_of_finalMatrix_via_explicitNoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_explicitNoStart M

/-- Target projection through target-facing explicit no-start/no-early rows. -/
theorem target_of_finalMatrix_via_explicitNoStartNoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_explicitNoStartNoEarly M

/-- Target projection through checked W11 no-early rows. -/
theorem target_of_finalMatrix_via_w11NoEarly
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_w11NoEarly M

/-- Target projection through checked W11 no-start rows. -/
theorem target_of_finalMatrix_via_w11NoStart
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_w11NoStart M

/-- Target projection through the final no-early aggregate. -/
theorem target_of_finalMatrix_via_noEarlyFinal
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_noEarlyFinal M

/-- Target projection through the final no-start aggregate. -/
theorem target_of_finalMatrix_via_noStartFinal
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_noStartFinal M

/-- Target projection through target-facing geometry. -/
theorem target_of_finalMatrix_via_geometryTarget
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_geometryTarget M

end

end BoundaryLabelTargetFinalW11
end Swanepoel
end ErdosProblems1066
