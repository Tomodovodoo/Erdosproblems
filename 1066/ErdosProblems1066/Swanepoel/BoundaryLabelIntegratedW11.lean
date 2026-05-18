import ErdosProblems1066.Swanepoel.BoundaryLabelClosureW11
import ErdosProblems1066.Swanepoel.NoEarlyIntegratedW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 boundary-label integrated matrix

This module is a source-facing ledger for the W11 boundary-label route.
Rows keep the explicit boundary-label prefix, window containment, and selected
no-early route as fields.  The checked adapters then project those same fields
to the boundary-label closure layer, the no-early integrated layer, W11
geometry closure rows, and the target-closure facade.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelIntegratedW11

open GeometryRemainingFieldsW10
open MinimalFailureGeometryMatrixW11
open MinimalGraphFacts

universe u v

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetClosureMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetClosureMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetClosureMatrixW11.PipelineCleared

/-- Explicit boundary-label prefix used by this integrated route. -/
abbrev LabelBasePrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryLabelClosureW11.LabelBasePrefix.{u} C hmin

/-- Source geometry produced from the explicit boundary-label prefix. -/
abbrev SourceFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  GeometrySourceFields.{u} C hmin

/-- Target-route row spelling shared with the W11 target closure facade. -/
abbrev TargetRoute (alpha : Sort v) : Sort (max 1 v) :=
  TargetClosureMatrixW11.TargetProjectionRow alpha

/-! ## Explicit integrated rows -/

/-- A boundary-label integrated row.

The row does not fill in any source data internally: labels, containment, and
the selected no-early route are all explicit fields. -/
structure Row
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  labelPrefix : LabelBasePrefix.{u} C hmin
  containment : ContainmentFields labelPrefix.toGeometrySourceFields
  noEarly : NoEarlyRoute labelPrefix.toGeometrySourceFields

namespace Row

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The source geometry selected by the explicit label prefix. -/
def source
    (R : Row.{u} C hmin) :
    SourceFields.{u} C hmin :=
  R.labelPrefix.toGeometrySourceFields

/-- Forget the integrated row to the boundary-label closure row. -/
def toBoundaryLabelClosureRow
    (R : Row.{u} C hmin) :
    BoundaryLabelClosureW11.Row.{u} C hmin where
  labelPrefix := R.labelPrefix
  containment := R.containment
  noEarly := R.noEarly

/-- Route the row to the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : Row.{u} C hmin) :
    GeometryClosureRow.{u} C hmin :=
  R.toBoundaryLabelClosureRow.toGeometryClosureRow

/-- Route the row to the W11 window row. -/
def toWindowRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.WindowRow.{u} C hmin :=
  R.toBoundaryLabelClosureRow.toWindowRow

/-- Route the row to the W11 concrete no-early row. -/
def toNoEarlyRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toBoundaryLabelClosureRow.toNoEarlyRow

/-- View the same explicit fields as a no-early integrated prefix row. -/
def toPrefixNoEarlyRow
    (R : Row.{u} C hmin) :
    NoEarlyIntegratedW11.PrefixNoEarlyRow.{u} C hmin where
  basePrefix := R.labelPrefix
  windowFields := by
    simpa [
      BoundaryLabelClosureW11.LabelBasePrefix.toGeometrySourceFields,
      BoundaryLabelRowsW11.BoundaryLabelRowPackage.BasePrefix.toW10BaseRow,
      GeometrySourceFields.localLabels,
      GeometrySourceFields.turnBounds
    ] using R.containment.localContainment
  noEarly := by
    simpa [
      BoundaryLabelClosureW11.LabelBasePrefix.toGeometrySourceFields,
      BoundaryLabelRowsW11.BoundaryLabelRowPackage.BasePrefix.toW10BaseRow,
      GeometrySourceFields.localLabels
    ] using R.noEarly.concreteNoEarly

/-- A fixed row closes through the W11 geometry route once supplied. -/
theorem contradiction
    (R : Row.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

@[simp]
theorem toBoundaryLabelClosureRow_labelPrefix
    (R : Row.{u} C hmin) :
    R.toBoundaryLabelClosureRow.labelPrefix = R.labelPrefix :=
  rfl

@[simp]
theorem toGeometryClosureRow_source
    (R : Row.{u} C hmin) :
    R.toGeometryClosureRow.source = R.source :=
  rfl

@[simp]
theorem toPrefixNoEarlyRow_basePrefix
    (R : Row.{u} C hmin) :
    R.toPrefixNoEarlyRow.basePrefix = R.labelPrefix :=
  rfl

end Row

/-! ## Uniform matrices -/

/-- Uniform integrated boundary-label rows for every minimal cleared failure. -/
structure Matrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Row.{u} C hmin

namespace Matrix

/-- Forget integrated rows to the boundary-label closure matrix. -/
def toBoundaryLabelClosureMatrix
    (M : Matrix.{u}) :
    BoundaryLabelClosureW11.Matrix.{u} where
  row := fun C hmin => (M.row C hmin).toBoundaryLabelClosureRow

/-- Route integrated rows to W11 geometry closure rows. -/
def toGeometryClosureMatrix
    (M : Matrix.{u}) :
    GeometryClosureMatrix.{u} :=
  M.toBoundaryLabelClosureMatrix.toGeometryClosureMatrix

/-- Route integrated rows to W11 no-early rows. -/
def toNoEarlyMatrix
    (M : Matrix.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} :=
  M.toBoundaryLabelClosureMatrix.toNoEarlyMatrix

/-- Route integrated rows through the no-early integrated prefix layer. -/
def toPrefixNoEarlyMatrix
    (M : Matrix.{u}) :
    NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toPrefixNoEarlyRow

/-- Route integrated rows to W10 direct-component rows. -/
def toDirectComponentMatrix
    (M : Matrix.{u}) :
    MinimalFailureDirectMatrixW10.DirectComponentMatrix.{u} :=
  M.toBoundaryLabelClosureMatrix.toDirectComponentMatrix

/-- Route integrated rows to the W10 target facade. -/
def toTargetFacadeMatrix
    (M : Matrix.{u}) :
    SwanepoelTargetFacadeW10.Matrix :=
  M.toPrefixNoEarlyMatrix.toTargetFacadeMatrix

/-- Route integrated rows to the narrow W11 geometry input family. -/
def toNarrowClosureInputFamily
    (M : Matrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toPrefixNoEarlyMatrix.toNarrowClosureInputFamily

/-- Route integrated rows to the checked W11 geometry input family. -/
def toCheckedClosureInputFamily
    (M : Matrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toPrefixNoEarlyMatrix.toCheckedClosureInputFamily

/-- Integrated boundary-label rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : Matrix.{u}) :
    MinimalFailureExclusion :=
  M.toBoundaryLabelClosureMatrix.no_minimalClearedFailure

/-- Integrated boundary-label rows supply the cleared-pipeline predicate. -/
theorem pipelineCleared
    (M : Matrix.{u}) :
    PipelineCleared :=
  M.toPrefixNoEarlyMatrix.pipelineCleared

/-- Target-closure projection from explicit integrated boundary-label rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : Matrix.{u}) :
    Target :=
  TargetClosureMatrixW11.noEarlyMatrixRow.target M.toNoEarlyMatrix

end Matrix

/-! ## Target-closure route ledger -/

/-- Target route from integrated boundary-label matrices. -/
def integratedMatrixRoute :
    TargetRoute (Matrix.{u}) where
  noMinimal := Matrix.no_minimalClearedFailure
  pipeline := Matrix.pipelineCleared
  target := Matrix.targetLowerBoundEightThirtyOne

/-- Target route from boundary-label closure matrices. -/
def boundaryLabelClosureMatrixRoute :
    TargetRoute (BoundaryLabelClosureW11.Matrix.{u}) where
  noMinimal := BoundaryLabelClosureW11.Matrix.no_minimalClearedFailure
  pipeline := fun M =>
    TargetClosureMatrixW11.noEarlyMatrixRow.pipeline M.toNoEarlyMatrix
  target := BoundaryLabelClosureW11.Matrix.targetLowerBoundEightThirtyOne

/-- Target route from no-early integrated prefix matrices. -/
def prefixNoEarlyMatrixRoute :
    TargetRoute (NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}) where
  noMinimal := NoEarlyIntegratedW11.PrefixNoEarlyMatrix.no_minimalClearedFailure
  pipeline := NoEarlyIntegratedW11.PrefixNoEarlyMatrix.pipelineCleared
  target := fun M =>
    TargetClosureMatrixW11.noEarlyMatrixRow.target M.toW11NoEarlyMatrix

/-- Target route from W11 geometry closure matrices. -/
def geometryClosureMatrixRoute :
    TargetRoute (GeometryClosureMatrix.{u}) where
  noMinimal := GeometryClosureMatrix.no_minimalClearedFailure
  pipeline := fun M =>
    SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
      M.no_minimalClearedFailure
  target := GeometryClosureMatrix.targetLowerBoundEightThirtyOne

/-- Checked boundary-label integration routes and imported W11 ledgers. -/
structure RouteMatrix : Type (u + 1) where
  targetClosure :
    TargetClosureMatrixW11.Matrix.{u}
  noEarlyIntegrated :
    NoEarlyIntegratedW11.Matrix.{u}
  boundaryLabelClosure :
    BoundaryLabelClosureW11.RouteMatrix.{u}
  integratedRows :
    TargetRoute (Matrix.{u})
  boundaryLabelClosureRows :
    TargetRoute (BoundaryLabelClosureW11.Matrix.{u})
  prefixNoEarlyRows :
    TargetRoute (NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u})
  noEarlyRows :
    TargetRoute (WindowNoEarlyRowsW11.NoEarlyMatrix.{u})
  geometryRows :
    TargetRoute (GeometryClosureMatrix.{u})

/-- The checked integrated boundary-label route matrix. -/
def routeMatrix : RouteMatrix.{u} where
  targetClosure := TargetClosureMatrixW11.matrix
  noEarlyIntegrated := NoEarlyIntegratedW11.matrix
  boundaryLabelClosure := BoundaryLabelClosureW11.routeMatrix
  integratedRows := integratedMatrixRoute
  boundaryLabelClosureRows := boundaryLabelClosureMatrixRoute
  prefixNoEarlyRows := prefixNoEarlyMatrixRoute
  noEarlyRows := TargetClosureMatrixW11.noEarlyMatrixRow
  geometryRows := geometryClosureMatrixRoute

/-! ## Public source-facing projections -/

/-- Minimal-failure exclusion from explicit integrated boundary-label rows. -/
theorem no_minimalClearedFailure_of_matrix
    (M : Matrix.{u}) :
    MinimalFailureExclusion :=
  Matrix.no_minimalClearedFailure M

/-- Cleared-pipeline projection from explicit integrated boundary-label rows. -/
theorem pipelineCleared_of_matrix
    (M : Matrix.{u}) :
    PipelineCleared :=
  Matrix.pipelineCleared M

/-- Target-closure projection from explicit integrated boundary-label rows. -/
theorem targetClosure_of_matrix
    (M : Matrix.{u}) :
    Target :=
  Matrix.targetLowerBoundEightThirtyOne M

/-- Target-closure projection from the no-early integrated prefix matrix. -/
theorem targetClosure_of_prefixNoEarlyMatrix
    (M : NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}) :
    Target :=
  prefixNoEarlyMatrixRoute.target M

end

end BoundaryLabelIntegratedW11
end Swanepoel
end ErdosProblems1066
