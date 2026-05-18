import ErdosProblems1066.Swanepoel.BoundaryLabelTargetIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryLabelIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyFinalIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# Final W11 boundary-label aggregate matrix

This terminal ledger keeps the boundary-label prefix, containment package, and
selected no-early route as explicit inputs.  It records checked adapters into
the boundary-label target ledger, the final no-early/no-start aggregate, and
the target-facing geometry aggregate.  All Swanepoel target projections below
remain conditional on a caller-supplied uniform family of those explicit rows.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelFinalIntegratedW11

open GeometryRemainingFieldsW10
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

abbrev LabelPrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryLabelTargetIntegratedW11.LabelPrefix.{u} C hmin

abbrev SourceFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryLabelTargetIntegratedW11.SourceFields.{u} C hmin

abbrev NoEarlyRoute
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (source : SourceFields.{u} C hmin) :=
  MinimalFailureGeometryMatrixW11.NoEarlyRoute.{u} source

abbrev W11NoEarlyMatrix :=
  BoundaryLabelTargetIntegratedW11.W11NoEarlyMatrix.{u}

abbrev W11NoStartMatrix :=
  NoEarlyFinalIntegratedW11.W11NoStartMatrix.{u}

abbrev TargetFacadeMatrix :=
  BoundaryLabelTargetIntegratedW11.TargetFacadeMatrix

/-! ## Explicit final rows -/

/-- One final boundary-label row for a fixed minimal cleared failure.

The row displays exactly the boundary-label prefix, the containment package
over the induced source labels, and the selected no-early route for those same
labels. -/
structure BoundaryLabelFinalFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  labelPrefix : LabelPrefix.{u} C hmin
  containment : ContainmentFields labelPrefix.toGeometrySourceFields
  noEarly : NoEarlyRoute labelPrefix.toGeometrySourceFields

namespace BoundaryLabelFinalFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The source geometry selected by the explicit boundary-label prefix. -/
def source
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    SourceFields.{u} C hmin :=
  R.labelPrefix.toGeometrySourceFields

/-- Repackage final rows as the target-facing boundary-label row. -/
def toBoundaryLabelTargetFields
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetFields.{u}
      C hmin where
  labelPrefix := R.labelPrefix
  containment := R.containment
  noEarly := R.noEarly

/-- Repackage final rows as the source-facing boundary-label row. -/
def toBoundaryLabelIntegratedRow
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    BoundaryLabelIntegratedW11.Row.{u} C hmin :=
  R.toBoundaryLabelTargetFields.toBoundaryLabelIntegratedRow

/-- Repackage final rows as boundary-label closure rows. -/
def toBoundaryLabelClosureRow
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    BoundaryLabelClosureW11.Row.{u} C hmin :=
  R.toBoundaryLabelTargetFields.toBoundaryLabelClosureRow

/-- Repackage final rows as explicit no-early target rows. -/
def toExplicitNoEarlyRow
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyRow.{u} C hmin :=
  R.toBoundaryLabelTargetFields.toExplicitNoEarlyRow

/-- Repackage final rows as final no-start/no-early rows.

The no-start fields are obtained from the selected no-early route by the
checked `NoEarlyRoute.toNoStartNoEarlyFields` adapter. -/
def toNoEarlyFinalRow
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    NoEarlyFinalIntegratedW11.Row.{u} C hmin where
  labelPrefix := R.labelPrefix
  windowFields := R.containment.localContainment
  noStart := R.noEarly.toNoStartNoEarlyFields.noStart
  noEarly := R.noEarly.concreteNoEarly

/-- Repackage final rows as target-facing direct geometry rows. -/
def toGeometryTargetDirectFields
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    GeometryTargetIntegratedW11.DirectTargetFields.{u} C hmin :=
  R.toBoundaryLabelTargetFields.toGeometryTargetDirectFields

/-- Repackage final rows as integrated broken-lattice direct packages. -/
def toBrokenLatticeDirectFieldPackage
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    BrokenLatticeIntegratedW11.DirectFieldPackage.{u} C hmin :=
  R.toBoundaryLabelTargetFields.toBrokenLatticeDirectFieldPackage

/-- The W11 no-early row selected by the explicit final fields. -/
def toW11NoEarlyRow
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toBoundaryLabelTargetFields.toW11NoEarlyRow

/-- The W11 no-start row induced by the selected no-early route. -/
def toW11NoStartRow
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    WindowNoEarlyRowsW11.NoStartRow.{u} C hmin :=
  R.toNoEarlyFinalRow.toNoStartRow

/-- A fixed final row closes through the checked geometry route. -/
theorem contradiction
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    False :=
  R.toBoundaryLabelTargetFields.contradiction

@[simp]
theorem toBoundaryLabelTargetFields_labelPrefix
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    R.toBoundaryLabelTargetFields.labelPrefix = R.labelPrefix :=
  rfl

@[simp]
theorem toNoEarlyFinalRow_labelPrefix
    (R : BoundaryLabelFinalFields.{u} C hmin) :
    R.toNoEarlyFinalRow.labelPrefix = R.labelPrefix :=
  rfl

end BoundaryLabelFinalFields

/-! ## Uniform explicit matrices -/

/-- Uniform final boundary-label rows for every minimal cleared failure. -/
structure BoundaryLabelFinalMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BoundaryLabelFinalFields.{u} C hmin

namespace BoundaryLabelFinalMatrix

/-- Forget final rows to the target-facing boundary-label matrix. -/
def toBoundaryLabelTargetMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    BoundaryLabelTargetIntegratedW11.BoundaryLabelTargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toBoundaryLabelTargetFields

/-- Forget final rows to the source-facing boundary-label matrix. -/
def toBoundaryLabelIntegratedMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    BoundaryLabelIntegratedW11.Matrix.{u} :=
  M.toBoundaryLabelTargetMatrix.toBoundaryLabelIntegratedMatrix

/-- Forget final rows to boundary-label closure rows. -/
def toBoundaryLabelClosureMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    BoundaryLabelClosureW11.Matrix.{u} :=
  M.toBoundaryLabelTargetMatrix.toBoundaryLabelClosureMatrix

/-- Forget final rows to explicit no-early target rows. -/
def toExplicitNoEarlyMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u} :=
  M.toBoundaryLabelTargetMatrix.toExplicitNoEarlyMatrix

/-- Forget final rows to the final no-start/no-early aggregate matrix. -/
def toNoEarlyFinalMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    NoEarlyFinalIntegratedW11.FinalNoStartNoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toNoEarlyFinalRow

/-- Forget final rows to the target-facing direct-geometry matrix. -/
def toGeometryTargetDirectMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    GeometryTargetIntegratedW11.DirectTargetMatrix.{u} :=
  M.toBoundaryLabelTargetMatrix.toGeometryTargetDirectMatrix

/-- Forget final rows to the checked W11 no-early matrix. -/
def toW11NoEarlyMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    W11NoEarlyMatrix.{u} :=
  M.toBoundaryLabelTargetMatrix.toW11NoEarlyMatrix

/-- Forget final rows to the checked W11 no-start matrix induced by no-early. -/
def toW11NoStartMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    W11NoStartMatrix.{u} :=
  M.toNoEarlyFinalMatrix.toW11NoStartMatrix

/-- Forget final rows to the integrated broken-lattice direct matrix. -/
def toBrokenLatticeDirectFieldMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u} :=
  M.toBoundaryLabelTargetMatrix.toBrokenLatticeDirectFieldMatrix

/-- Route final rows to the W10 target facade. -/
def toTargetFacadeMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    TargetFacadeMatrix :=
  M.toBoundaryLabelTargetMatrix.toTargetFacadeMatrix

/-- Route final rows to narrow W11 closure inputs. -/
def toNarrowClosureInputFamily
    (M : BoundaryLabelFinalMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u} :=
  M.toBoundaryLabelTargetMatrix.toNarrowClosureInputFamily

/-- Route final rows to checked refined W11 closure inputs. -/
def toCheckedClosureInputFamily
    (M : BoundaryLabelFinalMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u} :=
  M.toBoundaryLabelTargetMatrix.toCheckedClosureInputFamily

/-- Uniform final rows give the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : BoundaryLabelFinalMatrix.{u}) :
    MinimalFailureEliminator :=
  BoundaryLabelTargetIntegratedW11.minimalClearedFailureEliminator_of_boundaryLabelTargetMatrix
    M.toBoundaryLabelTargetMatrix

/-- Uniform final rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : BoundaryLabelFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  BoundaryLabelTargetIntegratedW11.no_minimalClearedFailure_of_boundaryLabelTargetMatrix
    M.toBoundaryLabelTargetMatrix

/-- Uniform final rows clear the conditional target pipeline. -/
theorem pipelineCleared
    (M : BoundaryLabelFinalMatrix.{u}) :
    PipelineCleared :=
  BoundaryLabelTargetIntegratedW11.pipelineCleared_of_boundaryLabelTargetMatrix
    M.toBoundaryLabelTargetMatrix

/-- Conditional Swanepoel target projection through boundary-label target rows. -/
theorem swanepoelTarget_via_boundaryLabelTarget
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix
    M.toBoundaryLabelTargetMatrix

/-- Conditional Swanepoel target projection through explicit no-early rows. -/
theorem swanepoelTarget_via_noEarlyTarget
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix_via_noEarlyTarget
    M.toBoundaryLabelTargetMatrix

/-- Conditional Swanepoel target projection through source-facing labels. -/
theorem swanepoelTarget_via_boundaryLabelIntegrated
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix_via_boundaryLabels
    M.toBoundaryLabelTargetMatrix

/-- Conditional Swanepoel target projection through checked no-early rows. -/
theorem swanepoelTarget_via_w11NoEarly
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix_via_w11NoEarly
    M.toBoundaryLabelTargetMatrix

/-- Conditional Swanepoel target projection through the final no-early route. -/
theorem swanepoelTarget_via_noEarlyFinal
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  NoEarlyFinalIntegratedW11.swanepoelTarget_of_finalNoEarlyMatrix
    M.toNoEarlyFinalMatrix

/-- Conditional Swanepoel target projection through the induced no-start route. -/
theorem swanepoelTarget_via_noStartFinal
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  NoEarlyFinalIntegratedW11.swanepoelTarget_of_finalNoStartMatrix
    M.toNoEarlyFinalMatrix

/-- Conditional Swanepoel target projection through target-facing geometry. -/
theorem swanepoelTarget_via_geometryTarget
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelTargetIntegratedW11.targetClosure_of_boundaryLabelTargetMatrix_via_geometryTarget
    M.toBoundaryLabelTargetMatrix

end BoundaryLabelFinalMatrix

/-! ## Explicit input and route ledgers -/

/-- The explicit final boundary-label input shapes owned by this aggregate. -/
structure ExplicitBoundaryLabelInputLedger : Type (u + 2) where
  pointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C), Type (u + 1)
  uniform : Type (u + 1)

/-- The pointwise and uniform input surfaces used by this aggregate. -/
def explicitBoundaryLabelInputLedger :
    ExplicitBoundaryLabelInputLedger.{u} where
  pointwise := fun C hmin => BoundaryLabelFinalFields.{u} C hmin
  uniform := BoundaryLabelFinalMatrix.{u}

/-- Imported W11 ledgers gathered by the final boundary-label aggregate. -/
structure ImportedLedgers : Type (u + 1) where
  boundaryLabelTarget :
    BoundaryLabelTargetIntegratedW11.Matrix.{u}
  boundaryLabelIntegrated :
    BoundaryLabelIntegratedW11.RouteMatrix.{u}
  noEarlyFinal :
    NoEarlyFinalIntegratedW11.Matrix.{u}
  geometryTarget :
    GeometryTargetIntegratedW11.Matrix.{u}
  targetIntegrated :
    TargetIntegratedMatrixW11.Matrix.{u}
  swanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.Matrix.{u}

/-- The imported ledgers present in this tree. -/
def importedLedgers : ImportedLedgers.{u} where
  boundaryLabelTarget := BoundaryLabelTargetIntegratedW11.matrix
  boundaryLabelIntegrated := BoundaryLabelIntegratedW11.routeMatrix
  noEarlyFinal := NoEarlyFinalIntegratedW11.matrix
  geometryTarget := GeometryTargetIntegratedW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  swanepoelIntegrated := SwanepoelW11IntegratedMatrix.matrix

/-! ## Conditional Swanepoel target routes -/

/-- Boundary-label final rows as an integrated target route. -/
def boundaryLabelFinalTargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryLabelFinalMatrix.{u}) where
  eliminator := BoundaryLabelFinalMatrix.minimalClearedFailureEliminator
  noMinimal := BoundaryLabelFinalMatrix.no_minimalClearedFailure
  pipeline := BoundaryLabelFinalMatrix.pipelineCleared
  target := BoundaryLabelFinalMatrix.swanepoelTarget_via_boundaryLabelTarget

/-- Boundary-label final rows as a target-closure route. -/
def boundaryLabelFinalTargetClosureRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelFinalMatrix.{u}) where
  noMinimal := BoundaryLabelFinalMatrix.no_minimalClearedFailure
  pipeline := BoundaryLabelFinalMatrix.pipelineCleared
  target := BoundaryLabelFinalMatrix.swanepoelTarget_via_boundaryLabelTarget

/-- Boundary-label final rows routed through the final no-early aggregate. -/
def boundaryLabelFinalNoEarlyRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (BoundaryLabelFinalMatrix.{u}) where
  noMinimal := BoundaryLabelFinalMatrix.no_minimalClearedFailure
  pipeline := BoundaryLabelFinalMatrix.pipelineCleared
  target := BoundaryLabelFinalMatrix.swanepoelTarget_via_noEarlyFinal

/-- Boundary-label final rows routed through the induced final no-start
aggregate. -/
def boundaryLabelFinalNoStartRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (BoundaryLabelFinalMatrix.{u}) where
  noMinimal := BoundaryLabelFinalMatrix.no_minimalClearedFailure
  pipeline := BoundaryLabelFinalMatrix.pipelineCleared
  target := BoundaryLabelFinalMatrix.swanepoelTarget_via_noStartFinal

/-- Boundary-label final rows routed through target-facing direct geometry. -/
def boundaryLabelFinalGeometryTargetRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryLabelFinalMatrix.{u}) where
  eliminator := BoundaryLabelFinalMatrix.minimalClearedFailureEliminator
  noMinimal := BoundaryLabelFinalMatrix.no_minimalClearedFailure
  pipeline := BoundaryLabelFinalMatrix.pipelineCleared
  target := BoundaryLabelFinalMatrix.swanepoelTarget_via_geometryTarget

/-- All conditional Swanepoel target routes exposed by the aggregate. -/
structure ConditionalSwanepoelTargetRoutes : Type (u + 1) where
  boundaryLabelTarget :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryLabelFinalMatrix.{u})
  targetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (BoundaryLabelFinalMatrix.{u})
  noEarlyFinal :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (BoundaryLabelFinalMatrix.{u})
  noStartFinal :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (BoundaryLabelFinalMatrix.{u})
  geometryTarget :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryLabelFinalMatrix.{u})

/-- The checked conditional Swanepoel routes from explicit boundary labels. -/
def conditionalSwanepoelTargetRoutes :
    ConditionalSwanepoelTargetRoutes.{u} where
  boundaryLabelTarget := boundaryLabelFinalTargetIntegratedRoute
  targetClosure := boundaryLabelFinalTargetClosureRoute
  noEarlyFinal := boundaryLabelFinalNoEarlyRoute
  noStartFinal := boundaryLabelFinalNoStartRoute
  geometryTarget := boundaryLabelFinalGeometryTargetRoute

/-! ## Final aggregate ledger -/

/-- Final W11 boundary-label aggregate matrix.

The matrix stores adapters and route rows only.  It does not construct a
uniform boundary-label final matrix. -/
structure Matrix : Type (u + 2) where
  inputs : ExplicitBoundaryLabelInputLedger.{u}
  imported : ImportedLedgers.{u}
  routes : ConditionalSwanepoelTargetRoutes.{u}

/-- The checked final W11 boundary-label aggregate. -/
def matrix : Matrix.{u} where
  inputs := explicitBoundaryLabelInputLedger
  imported := importedLedgers
  routes := conditionalSwanepoelTargetRoutes

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_finalMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    MinimalFailureEliminator :=
  BoundaryLabelFinalMatrix.minimalClearedFailureEliminator M

theorem no_minimalClearedFailure_of_finalMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  BoundaryLabelFinalMatrix.no_minimalClearedFailure M

theorem pipelineCleared_of_finalMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    PipelineCleared :=
  BoundaryLabelFinalMatrix.pipelineCleared M

theorem swanepoelTarget_of_finalMatrix
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalMatrix.swanepoelTarget_via_boundaryLabelTarget M

theorem swanepoelTarget_of_finalMatrix_via_targetClosure
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalMatrix.swanepoelTarget_via_boundaryLabelTarget M

theorem swanepoelTarget_of_finalMatrix_via_noEarlyTarget
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalMatrix.swanepoelTarget_via_noEarlyTarget M

theorem swanepoelTarget_of_finalMatrix_via_boundaryLabels
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalMatrix.swanepoelTarget_via_boundaryLabelIntegrated M

theorem swanepoelTarget_of_finalMatrix_via_w11NoEarly
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalMatrix.swanepoelTarget_via_w11NoEarly M

theorem swanepoelTarget_of_finalMatrix_via_noEarlyFinal
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalMatrix.swanepoelTarget_via_noEarlyFinal M

theorem swanepoelTarget_of_finalMatrix_via_noStartFinal
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalMatrix.swanepoelTarget_via_noStartFinal M

theorem swanepoelTarget_of_finalMatrix_via_geometryTarget
    (M : BoundaryLabelFinalMatrix.{u}) :
    Target :=
  BoundaryLabelFinalMatrix.swanepoelTarget_via_geometryTarget M

end

end BoundaryLabelFinalIntegratedW11
end Swanepoel
end ErdosProblems1066
