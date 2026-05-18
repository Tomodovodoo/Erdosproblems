import ErdosProblems1066.Swanepoel.BoundaryLabelIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyTargetIntegratedW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11
import ErdosProblems1066.Swanepoel.GeometryIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryTargetIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 boundary-label target integration matrix

This module is a target-facing wrapper around the explicit W11 boundary-label
row.  It keeps the label prefix, containment package, and selected no-early
route as visible fields, then records checked conditional projections into the
boundary-label, no-early, geometry, broken-lattice, and Swanepoel target
ledgers.

All public target statements below remain conditional on a supplied uniform
boundary-label target matrix.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelTargetIntegratedW11

open GeometryRemainingFieldsW10
open MinimalGraphFacts

universe u v

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

abbrev LabelPrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryLabelIntegratedW11.LabelBasePrefix.{u} C hmin

abbrev SourceFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryLabelIntegratedW11.SourceFields.{u} C hmin

abbrev W11NoEarlyMatrix :=
  WindowNoEarlyRowsW11.NoEarlyMatrix.{u}

abbrev GeometryClosureMatrix :=
  MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u}

abbrev NarrowClosureInputFamily :=
  MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u}

abbrev CheckedClosureInputFamily :=
  MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u}

abbrev TargetFacadeMatrix :=
  SwanepoelTargetFacadeW10.Matrix

/-! ## Explicit target-facing rows -/

/-- Target-facing boundary-label fields for one minimal cleared failure.

The label prefix determines the source geometry; containment and the selected
no-early route are supplied explicitly for that same source. -/
structure BoundaryLabelTargetFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  labelPrefix : LabelPrefix.{u} C hmin
  containment : ContainmentFields labelPrefix.toGeometrySourceFields
  noEarly :
    MinimalFailureGeometryMatrixW11.NoEarlyRoute
      labelPrefix.toGeometrySourceFields

namespace BoundaryLabelTargetFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The source geometry selected by the explicit label prefix. -/
def source
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    SourceFields.{u} C hmin :=
  R.labelPrefix.toGeometrySourceFields

/-- Repackage the row as the source-facing boundary-label integrated row. -/
def toBoundaryLabelIntegratedRow
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    BoundaryLabelIntegratedW11.Row.{u} C hmin where
  labelPrefix := R.labelPrefix
  containment := R.containment
  noEarly := R.noEarly

/-- Repackage the row as the boundary-label closure row. -/
def toBoundaryLabelClosureRow
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    BoundaryLabelClosureW11.Row.{u} C hmin :=
  R.toBoundaryLabelIntegratedRow.toBoundaryLabelClosureRow

/-- Repackage the row in the explicit no-early target-facing spelling. -/
def toExplicitNoEarlyRow
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyRow.{u} C hmin where
  labelPrefix := R.labelPrefix
  windowFields := R.containment.localContainment
  noEarly := R.noEarly.concreteNoEarly

/-- Forget to the integrated no-early prefix row. -/
def toPrefixNoEarlyRow
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    NoEarlyIntegratedW11.PrefixNoEarlyRow.{u} C hmin :=
  R.toExplicitNoEarlyRow.toPrefixNoEarlyRow

/-- The W11 window row selected by the explicit fields. -/
def toWindowRow
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    WindowNoEarlyRowsW11.WindowRow.{u} C hmin :=
  R.toExplicitNoEarlyRow.toWindowRow

/-- The W11 no-early row selected by the explicit fields. -/
def toW11NoEarlyRow
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toExplicitNoEarlyRow.toNoEarlyRow

/-- The target-facing no-early row selected by the explicit fields. -/
def toNoEarlyTargetRow
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRow C hmin :=
  R.toExplicitNoEarlyRow.toNoEarlyTargetRow

/-- The W11 geometry closure row selected by the same fields. -/
def toGeometryClosureRow
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.toBoundaryLabelIntegratedRow.toGeometryClosureRow

/-- View the selected no-early route as direct five-start fields. -/
def toNoStartNoEarlyFields
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    NoStartNoEarlyFields R.source :=
  R.noEarly.toNoStartNoEarlyFields

/-- Repackage the row as an integrated direct-geometry row. -/
def toGeometryIntegratedDirectFields
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    GeometryIntegratedW11.DirectGeometryFields.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.toNoStartNoEarlyFields

/-- Repackage the row for the target-facing geometry facade. -/
def toGeometryTargetDirectFields
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    GeometryTargetIntegratedW11.DirectTargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.toNoStartNoEarlyFields

/-- Repackage the row as an integrated broken-lattice direct field package. -/
def toBrokenLatticeDirectFieldPackage
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    BrokenLatticeIntegratedW11.DirectFieldPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.toNoStartNoEarlyFields

/-- The narrow concrete closure input selected by this row. -/
def toNarrowClosureInput
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toGeometryClosureRow.toConcreteObligations

/-- The checked refined closure input selected by this row. -/
def toCheckedClosureInput
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  R.toGeometryClosureRow.toCheckedClosureInput

/-- A fixed boundary-label target row closes through the geometry route. -/
theorem contradiction
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

@[simp]
theorem toBoundaryLabelIntegratedRow_labelPrefix
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    R.toBoundaryLabelIntegratedRow.labelPrefix = R.labelPrefix :=
  rfl

@[simp]
theorem toExplicitNoEarlyRow_labelPrefix
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    R.toExplicitNoEarlyRow.labelPrefix = R.labelPrefix :=
  rfl

@[simp]
theorem toGeometryClosureRow_source
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    R.toGeometryClosureRow.source = R.source :=
  rfl

@[simp]
theorem toGeometryIntegratedDirectFields_source
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    R.toGeometryIntegratedDirectFields.source = R.source :=
  rfl

@[simp]
theorem toGeometryTargetDirectFields_source
    (R : BoundaryLabelTargetFields.{u} C hmin) :
    R.toGeometryTargetDirectFields.source = R.source :=
  rfl

end BoundaryLabelTargetFields

/-! ## Uniform explicit matrices -/

/-- Uniform target-facing boundary-label rows for every minimal cleared
failure. -/
structure BoundaryLabelTargetMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BoundaryLabelTargetFields.{u} C hmin

namespace BoundaryLabelTargetMatrix

/-- Forget to the source-facing boundary-label integrated matrix. -/
def toBoundaryLabelIntegratedMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    BoundaryLabelIntegratedW11.Matrix.{u} where
  row := fun C hmin => (M.row C hmin).toBoundaryLabelIntegratedRow

/-- Forget to the boundary-label closure matrix. -/
def toBoundaryLabelClosureMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    BoundaryLabelClosureW11.Matrix.{u} where
  row := fun C hmin => (M.row C hmin).toBoundaryLabelClosureRow

/-- Forget to the explicit no-early target matrix. -/
def toExplicitNoEarlyMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toExplicitNoEarlyRow

/-- Forget to the integrated no-early prefix matrix. -/
def toPrefixNoEarlyMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u} :=
  M.toExplicitNoEarlyMatrix.toPrefixNoEarlyMatrix

/-- View the rows as checked W11 no-early rows. -/
def toW11NoEarlyMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    W11NoEarlyMatrix.{u} :=
  M.toExplicitNoEarlyMatrix.toW11NoEarlyMatrix

/-- View the rows as W11 geometry closure rows. -/
def toGeometryClosureMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    GeometryClosureMatrix.{u} :=
  M.toBoundaryLabelIntegratedMatrix.toGeometryClosureMatrix

/-- View the rows as integrated direct-geometry rows. -/
def toGeometryIntegratedDirectMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    GeometryIntegratedW11.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryIntegratedDirectFields

/-- View the rows as target-facing direct-geometry rows. -/
def toGeometryTargetDirectMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    GeometryTargetIntegratedW11.DirectTargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryTargetDirectFields

/-- View the rows as integrated broken-lattice direct field packages. -/
def toBrokenLatticeDirectFieldMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toBrokenLatticeDirectFieldPackage

/-- Route to the narrow concrete closure input family. -/
def toNarrowClosureInputFamily
    (M : BoundaryLabelTargetMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toNarrowClosureInputFamily

/-- Route to the checked refined closure input family. -/
def toCheckedClosureInputFamily
    (M : BoundaryLabelTargetMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toCheckedClosureInputFamily

/-- Route to the W10 target facade matrix. -/
def toTargetFacadeMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    TargetFacadeMatrix :=
  M.toExplicitNoEarlyMatrix.toW10TargetFacadeMatrix

/-- Uniform explicit boundary-label target rows give a minimal-failure
eliminator through the Swanepoel target matrix. -/
theorem minimalClearedFailureEliminator
    (M : BoundaryLabelTargetMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_directFieldMatrix
    M.toBrokenLatticeDirectFieldMatrix

/-- Uniform explicit boundary-label target rows rule out minimal failures. -/
theorem no_minimalClearedFailure
    (M : BoundaryLabelTargetMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_directFieldMatrix
    M.toBrokenLatticeDirectFieldMatrix

/-- Uniform explicit boundary-label target rows clear the conditional
pipeline. -/
theorem pipelineCleared
    (M : BoundaryLabelTargetMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_directFieldMatrix
    M.toBrokenLatticeDirectFieldMatrix

/-- Conditional target projection through the integrated Swanepoel target
ledger. -/
theorem targetClosure
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix
    M.toBrokenLatticeDirectFieldMatrix

/-- Conditional target projection through the explicit no-early target
facade. -/
theorem target_via_noEarlyTarget
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoEarlyMatrix
    M.toExplicitNoEarlyMatrix

/-- Conditional target projection through the boundary-label integrated
facade. -/
theorem target_via_boundaryLabelIntegrated
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  BoundaryLabelIntegratedW11.targetClosure_of_matrix
    M.toBoundaryLabelIntegratedMatrix

/-- Conditional target projection through checked W11 no-early rows. -/
theorem target_via_w11NoEarly
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noEarlyMatrix
    M.toW11NoEarlyMatrix

/-- Conditional target projection through the geometry integration facade. -/
theorem target_via_geometryIntegrated
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    M.toGeometryIntegratedDirectMatrix

/-- Conditional target projection through the target-facing geometry facade. -/
theorem target_via_geometryTargetIntegrated
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_directTargetMatrix
    M.toGeometryTargetDirectMatrix

end BoundaryLabelTargetMatrix

/-! ## Checked target projection rows -/

/-- Pull back a target-closure row along a matrix adapter. -/
def pullbackTargetClosureRow
    {alpha : Sort v} {beta : Sort u}
    (R : TargetClosureMatrixW11.TargetProjectionRow beta)
    (f : alpha -> beta) :
    TargetClosureMatrixW11.TargetProjectionRow alpha where
  noMinimal := fun a => R.noMinimal (f a)
  pipeline := fun a => R.pipeline (f a)
  target := fun a => R.target (f a)

/-- Boundary-label target matrices as a target-closure projection row. -/
def boundaryLabelTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelTargetMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    BoundaryLabelTargetMatrix.no_minimalClearedFailure
    BoundaryLabelTargetMatrix.targetClosure

/-- Boundary-label target matrices as a Swanepoel integrated projection row. -/
def boundaryLabelSwanepoelIntegratedRow :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (BoundaryLabelTargetMatrix.{u}) where
  noMinimal := BoundaryLabelTargetMatrix.no_minimalClearedFailure
  pipeline := BoundaryLabelTargetMatrix.pipelineCleared
  target := BoundaryLabelTargetMatrix.targetClosure

/-- Boundary-label target matrices as an integrated target route with the
minimal-failure eliminator displayed. -/
def boundaryLabelTargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryLabelTargetMatrix.{u}) where
  eliminator := BoundaryLabelTargetMatrix.minimalClearedFailureEliminator
  noMinimal := BoundaryLabelTargetMatrix.no_minimalClearedFailure
  pipeline := BoundaryLabelTargetMatrix.pipelineCleared
  target := BoundaryLabelTargetMatrix.targetClosure

/-- Boundary-label target matrices as an integrated W11 geometry route. -/
def boundaryLabelGeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (BoundaryLabelTargetMatrix.{u}) where
  geometryClosure := BoundaryLabelTargetMatrix.toGeometryClosureMatrix
  narrowInputs := BoundaryLabelTargetMatrix.toNarrowClosureInputFamily
  checkedInputs := BoundaryLabelTargetMatrix.toCheckedClosureInputFamily
  targetFacade := BoundaryLabelTargetMatrix.toTargetFacadeMatrix
  targetProjection := boundaryLabelTargetClosureRow

/-- Boundary-label target matrices routed through the explicit no-early
target facade. -/
def boundaryLabelNoEarlyTargetRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelTargetMatrix.{u}) :=
  pullbackTargetClosureRow
    NoEarlyTargetIntegratedW11.explicitNoEarlyTargetClosureRoute
    BoundaryLabelTargetMatrix.toExplicitNoEarlyMatrix

/-- Boundary-label target matrices routed through the target-facing geometry
facade. -/
def boundaryLabelGeometryTargetRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelTargetMatrix.{u}) :=
  pullbackTargetClosureRow
    GeometryTargetIntegratedW11.directTargetClosureRow
    BoundaryLabelTargetMatrix.toGeometryTargetDirectMatrix

/-- Boundary-label target matrices routed through checked W11 no-early rows. -/
def boundaryLabelW11NoEarlyRow :
    TargetIntegratedMatrixW11.TargetRoute
      (BoundaryLabelTargetMatrix.{u}) :=
  TargetIntegratedMatrixW11.TargetRoute.ofTargetClosureRow
    (pullbackTargetClosureRow
      TargetClosureMatrixW11.matrix.noEarlyRows
      BoundaryLabelTargetMatrix.toW11NoEarlyMatrix)

/-! ## Target-facing boundary-label ledger -/

/-- Checked W11 target-facing boundary-label integration ledger.

The ledger stores route functions only; it does not construct any label,
containment, or no-early fields. -/
structure Matrix : Type (u + 1) where
  boundaryLabelIntegrated :
    BoundaryLabelIntegratedW11.RouteMatrix.{u}
  boundaryLabelClosure :
    BoundaryLabelClosureW11.RouteMatrix.{u}
  noEarlyTargetIntegrated :
    NoEarlyTargetIntegratedW11.Matrix.{u}
  targetClosure :
    TargetClosureMatrixW11.Matrix.{u}
  targetIntegrated :
    TargetIntegratedMatrixW11.Matrix.{u}
  geometryIntegrated :
    GeometryIntegratedW11.Matrix.{u}
  geometryTargetIntegrated :
    GeometryTargetIntegratedW11.Matrix.{u}
  boundaryLabelTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelTargetMatrix.{u})
  boundaryLabelNoEarlyTarget :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelTargetMatrix.{u})
  boundaryLabelGeometryTarget :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelTargetMatrix.{u})
  boundaryLabelTargetIntegrated :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryLabelTargetMatrix.{u})
  boundaryLabelW11NoEarly :
    TargetIntegratedMatrixW11.TargetRoute
      (BoundaryLabelTargetMatrix.{u})
  boundaryLabelSwanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (BoundaryLabelTargetMatrix.{u})
  boundaryLabelGeometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (BoundaryLabelTargetMatrix.{u})

/-- The checked target-facing boundary-label integration ledger. -/
def matrix : Matrix.{u} where
  boundaryLabelIntegrated := BoundaryLabelIntegratedW11.routeMatrix
  boundaryLabelClosure := BoundaryLabelClosureW11.routeMatrix
  noEarlyTargetIntegrated := NoEarlyTargetIntegratedW11.matrix
  targetClosure := TargetClosureMatrixW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  geometryIntegrated := GeometryIntegratedW11.matrix
  geometryTargetIntegrated := GeometryTargetIntegratedW11.matrix
  boundaryLabelTargetClosure := boundaryLabelTargetClosureRow
  boundaryLabelNoEarlyTarget := boundaryLabelNoEarlyTargetRow
  boundaryLabelGeometryTarget := boundaryLabelGeometryTargetRow
  boundaryLabelTargetIntegrated := boundaryLabelTargetIntegratedRoute
  boundaryLabelW11NoEarly := boundaryLabelW11NoEarlyRow
  boundaryLabelSwanepoelIntegrated := boundaryLabelSwanepoelIntegratedRow
  boundaryLabelGeometry := boundaryLabelGeometryProjectionRow

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_boundaryLabelTargetMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    MinimalFailureEliminator :=
  M.minimalClearedFailureEliminator

theorem no_minimalClearedFailure_of_boundaryLabelTargetMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    MinimalFailureExclusion :=
  M.no_minimalClearedFailure

theorem pipelineCleared_of_boundaryLabelTargetMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    PipelineCleared :=
  M.pipelineCleared

theorem targetClosure_of_boundaryLabelTargetMatrix
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  M.targetClosure

theorem targetClosure_of_boundaryLabelTargetMatrix_via_noEarlyTarget
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  M.target_via_noEarlyTarget

theorem targetClosure_of_boundaryLabelTargetMatrix_via_w11NoEarly
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  M.target_via_w11NoEarly

theorem targetClosure_of_boundaryLabelTargetMatrix_via_boundaryLabels
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  M.target_via_boundaryLabelIntegrated

theorem targetClosure_of_boundaryLabelTargetMatrix_via_geometry
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  M.target_via_geometryIntegrated

theorem targetClosure_of_boundaryLabelTargetMatrix_via_geometryTarget
    (M : BoundaryLabelTargetMatrix.{u}) :
    Target :=
  M.target_via_geometryTargetIntegrated

end

end BoundaryLabelTargetIntegratedW11
end Swanepoel
end ErdosProblems1066
