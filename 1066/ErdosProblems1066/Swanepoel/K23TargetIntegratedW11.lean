import ErdosProblems1066.Swanepoel.K23IntegratedMatrixW11
import ErdosProblems1066.Swanepoel.K23ClosureW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11
import ErdosProblems1066.Swanepoel.GeometryIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 K23 target integration facade

This file is a target-facing wrapper around the W11 K23/common-neighbor
source rows.  It keeps the source geometry, containment package, and
route-specific obstruction data as visible fields, then records checked
projections into the strongest W11 Swanepoel target ledgers available in this
tree.

All public target statements remain conditional on an explicit uniform input
matrix.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace K23TargetIntegratedW11

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

/-! ## Pointwise explicit target-facing rows -/

/-- Target-facing K23 row for one fixed minimal cleared failure.

The source, containment, and obstruction fields are intentionally separate so
target ledgers can display exactly which local data each route consumes. -/
structure K23TargetFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin
  containment : GeometryRemainingFieldsW10.ContainmentFields source
  k23Obstruction :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs
      source.localLabels.predicates.data

namespace K23TargetFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Repackage the explicit row as the source-facing K23 integration row. -/
def toK23IntegratedFields
    (R : K23TargetFields.{u} C hmin) :
    K23IntegratedMatrixW11.K23IntegratedFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.k23Obstruction

/-- Repackage the explicit row as the checked K23 obstruction fields. -/
def toK23ObstructionW10Fields
    (R : K23TargetFields.{u} C hmin) :
    K23CommonNeighborW11.K23ObstructionW10Fields.{u} C hmin :=
  R.toK23IntegratedFields.toK23ObstructionW10Fields

/-- The W10 K23/no-early fields selected by the displayed obstruction. -/
def toK23NoEarlyFields
    (R : K23TargetFields.{u} C hmin) :
    GeometryRemainingFieldsW10.K23NoEarlyFields R.source :=
  R.toK23ObstructionW10Fields.toK23NoEarlyFields

/-- Repackage the row for the integrated W11 geometry facade. -/
def toGeometryIntegratedK23Fields
    (R : K23TargetFields.{u} C hmin) :
    GeometryIntegratedW11.K23GeometryFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.toK23NoEarlyFields

/-- Repackage the row for the integrated W11 broken-lattice facade. -/
def toBrokenLatticeIntegratedK23FieldPackage
    (R : K23TargetFields.{u} C hmin) :
    BrokenLatticeIntegratedW11.K23FieldPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.toK23NoEarlyFields

/-- A fixed K23 target row closes through the K23 integration layer. -/
theorem contradiction_via_k23Integrated
    (R : K23TargetFields.{u} C hmin) :
    False :=
  K23IntegratedMatrixW11.K23IntegratedFields.contradiction_via_k23Closure
    R.toK23IntegratedFields

/-- A fixed K23 target row closes through the geometry integration layer. -/
theorem contradiction_via_geometryIntegrated
    (R : K23TargetFields.{u} C hmin) :
    False :=
  GeometryIntegratedW11.K23GeometryFields.contradiction
    R.toGeometryIntegratedK23Fields

end K23TargetFields

/-- Target-facing common-neighbor row for one fixed minimal cleared failure.

The common-neighbor obstruction remains the source field; the K23 obstruction
is obtained only through the checked adapter. -/
structure CommonNeighborTargetFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin
  containment : GeometryRemainingFieldsW10.ContainmentFields source
  commonNeighborObstruction :
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
      source.localLabels.predicates.data

namespace CommonNeighborTargetFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Repackage the explicit row as the source-facing common-neighbor
integration row. -/
def toCommonNeighborIntegratedFields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    K23IntegratedMatrixW11.CommonNeighborIntegratedFields.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborObstruction := R.commonNeighborObstruction

/-- Repackage the explicit row as checked common-neighbor obstruction fields. -/
def toCommonNeighborObstructionW10Fields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    K23CommonNeighborW11.CommonNeighborObstructionW10Fields.{u} C hmin :=
  R.toCommonNeighborIntegratedFields.toCommonNeighborObstructionW10Fields

/-- The W10 common-neighbor/no-early fields selected by the displayed
obstruction. -/
def toCommonNeighborNoEarlyFields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields R.source :=
  R.toCommonNeighborObstructionW10Fields.toCommonNeighborNoEarlyFields

/-- Forget common-neighbor obstruction data to the checked K23 target row. -/
def toK23TargetFields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    K23TargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.commonNeighborObstruction.toK23ObstructionInputs

/-- Repackage the row for the integrated W11 geometry facade. -/
def toGeometryIntegratedCommonNeighborFields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    GeometryIntegratedW11.CommonNeighborGeometryFields.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborNoEarly := R.toCommonNeighborNoEarlyFields

/-- Repackage the row for the integrated W11 broken-lattice facade. -/
def toBrokenLatticeIntegratedCommonNeighborFieldPackage
    (R : CommonNeighborTargetFields.{u} C hmin) :
    BrokenLatticeIntegratedW11.CommonNeighborFieldPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborNoEarly := R.toCommonNeighborNoEarlyFields

/-- A fixed common-neighbor target row closes through the K23/common-neighbor
integration layer. -/
theorem contradiction_via_k23Integrated
    (R : CommonNeighborTargetFields.{u} C hmin) :
    False :=
  K23IntegratedMatrixW11.CommonNeighborIntegratedFields.contradiction_via_k23Closure
    R.toCommonNeighborIntegratedFields

/-- A fixed common-neighbor target row closes through the geometry integration
layer. -/
theorem contradiction_via_geometryIntegrated
    (R : CommonNeighborTargetFields.{u} C hmin) :
    False :=
  GeometryIntegratedW11.CommonNeighborGeometryFields.contradiction
    R.toGeometryIntegratedCommonNeighborFields

end CommonNeighborTargetFields

/-! ## Uniform explicit target matrices -/

/-- Uniform target-facing K23 rows for every minimal cleared failure. -/
structure K23TargetMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23TargetFields.{u} C hmin

namespace K23TargetMatrix

/-- Forget to the source-facing K23 integration matrix. -/
def toK23IntegratedMatrix
    (M : K23TargetMatrix.{u}) :
    K23IntegratedMatrixW11.K23IntegratedMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23IntegratedFields

/-- Forget to the checked K23 closure row family. -/
def toK23RowFamily
    (M : K23TargetMatrix.{u}) :
    K23ClosureW11.K23RowFamily.{u} :=
  M.toK23IntegratedMatrix.toK23RowFamily

/-- Forget to the checked W10 K23 geometry matrix. -/
def toW10K23GeometryMatrix
    (M : K23TargetMatrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23IntegratedFields.toK23GeometryPackage

/-- View the rows as the integrated W11 geometry K23 matrix. -/
def toGeometryIntegratedK23GeometryMatrix
    (M : K23TargetMatrix.{u}) :
    GeometryIntegratedW11.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryIntegratedK23Fields

/-- View the rows as the integrated W11 broken-lattice K23 field matrix. -/
def toBrokenLatticeIntegratedK23FieldMatrix
    (M : K23TargetMatrix.{u}) :
    BrokenLatticeIntegratedW11.K23FieldMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeIntegratedK23FieldPackage

/-- View the rows as the target-closure K23 predicate matrix. -/
def toTargetClosureK23GeometryPredicateMatrix
    (M : K23TargetMatrix.{u}) :
    TargetClosureMatrixW11.K23GeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toK23IntegratedFields
      |>.toBrokenLatticeK23GeometryPredicateFields

/-- View the rows as the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : K23TargetMatrix.{u}) :
    GeometryIntegratedW11.GeometryClosureMatrix.{u} :=
  M.toGeometryIntegratedK23GeometryMatrix.toGeometryClosureMatrix

/-- View the rows as narrow concrete closure input families. -/
def toNarrowClosureInputFamily
    (M : K23TargetMatrix.{u}) :
    GeometryIntegratedW11.NarrowClosureInputFamily.{u} :=
  M.toGeometryIntegratedK23GeometryMatrix.toNarrowClosureInputFamily

/-- View the rows as checked refined closure input families. -/
def toCheckedClosureInputFamily
    (M : K23TargetMatrix.{u}) :
    GeometryIntegratedW11.CheckedClosureInputFamily.{u} :=
  M.toGeometryIntegratedK23GeometryMatrix.toCheckedClosureInputFamily

/-- View the rows as the W10 target facade matrix. -/
def toTargetFacadeMatrix
    (M : K23TargetMatrix.{u}) :
    GeometryIntegratedW11.TargetFacadeMatrix :=
  M.toGeometryIntegratedK23GeometryMatrix.toTargetFacadeMatrix

/-- Uniform K23 target rows give a minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : K23TargetMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_k23FieldMatrix
    M.toBrokenLatticeIntegratedK23FieldMatrix

/-- Uniform K23 target rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : K23TargetMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_k23FieldMatrix
    M.toBrokenLatticeIntegratedK23FieldMatrix

/-- Uniform K23 target rows clear the conditional target pipeline. -/
theorem pipelineCleared
    (M : K23TargetMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_k23FieldMatrix
    M.toBrokenLatticeIntegratedK23FieldMatrix

/-- Conditional target projection through the integrated target facade. -/
theorem targetLowerBoundEightThirtyOne
    (M : K23TargetMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_k23FieldMatrix
    M.toBrokenLatticeIntegratedK23FieldMatrix

/-- Conditional target projection through the target-closure facade. -/
theorem target_via_targetClosureMatrix
    (M : K23TargetMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.targetLowerBoundEightThirtyOne_of_k23GeometryPredicateMatrix
    M.toTargetClosureK23GeometryPredicateMatrix

/-- Conditional target projection through the geometry integration facade. -/
theorem target_via_geometryIntegrated
    (M : K23TargetMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    M.toGeometryIntegratedK23GeometryMatrix

/-- Conditional target projection through the original K23 integration
facade. -/
theorem target_via_k23Integrated
    (M : K23TargetMatrix.{u}) :
    Target :=
  K23IntegratedMatrixW11.targetLowerBoundEightThirtyOne_of_k23IntegratedMatrix
    M.toK23IntegratedMatrix

end K23TargetMatrix

/-- Uniform target-facing common-neighbor rows for every minimal cleared
failure. -/
structure CommonNeighborTargetMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborTargetFields.{u} C hmin

namespace CommonNeighborTargetMatrix

/-- Forget to the source-facing common-neighbor integration matrix. -/
def toCommonNeighborIntegratedMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborIntegratedFields

/-- Forget to the corresponding K23 target matrix through the checked
common-neighbor-to-K23 adapter. -/
def toK23TargetMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    K23TargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23TargetFields

/-- Forget to the checked common-neighbor closure row family. -/
def toCommonNeighborRowFamily
    (M : CommonNeighborTargetMatrix.{u}) :
    K23ClosureW11.CommonNeighborRowFamily.{u} :=
  M.toCommonNeighborIntegratedMatrix.toCommonNeighborRowFamily

/-- Forget to the checked W10 common-neighbor geometry matrix. -/
def toW10CommonNeighborGeometryMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toCommonNeighborIntegratedFields
      |>.toCommonNeighborGeometryPackage

/-- View the rows as the integrated W11 geometry common-neighbor matrix. -/
def toGeometryIntegratedCommonNeighborGeometryMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toGeometryIntegratedCommonNeighborFields

/-- View the rows as the integrated W11 broken-lattice common-neighbor field
matrix. -/
def toBrokenLatticeIntegratedCommonNeighborFieldMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeIntegratedCommonNeighborFieldPackage

/-- View the rows as the target-closure common-neighbor predicate matrix. -/
def toTargetClosureCommonNeighborGeometryPredicateMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    TargetClosureMatrixW11.CommonNeighborGeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toCommonNeighborIntegratedFields
      |>.toBrokenLatticeCommonNeighborGeometryPredicateFields

/-- View the rows as the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    GeometryIntegratedW11.GeometryClosureMatrix.{u} :=
  M.toGeometryIntegratedCommonNeighborGeometryMatrix.toGeometryClosureMatrix

/-- View the rows as narrow concrete closure input families. -/
def toNarrowClosureInputFamily
    (M : CommonNeighborTargetMatrix.{u}) :
    GeometryIntegratedW11.NarrowClosureInputFamily.{u} :=
  M.toGeometryIntegratedCommonNeighborGeometryMatrix.toNarrowClosureInputFamily

/-- View the rows as checked refined closure input families. -/
def toCheckedClosureInputFamily
    (M : CommonNeighborTargetMatrix.{u}) :
    GeometryIntegratedW11.CheckedClosureInputFamily.{u} :=
  M.toGeometryIntegratedCommonNeighborGeometryMatrix.toCheckedClosureInputFamily

/-- View the rows as the W10 target facade matrix. -/
def toTargetFacadeMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    GeometryIntegratedW11.TargetFacadeMatrix :=
  M.toGeometryIntegratedCommonNeighborGeometryMatrix.toTargetFacadeMatrix

/-- Uniform common-neighbor target rows give a minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : CommonNeighborTargetMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_commonNeighborFieldMatrix
    M.toBrokenLatticeIntegratedCommonNeighborFieldMatrix

/-- Uniform common-neighbor target rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : CommonNeighborTargetMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_commonNeighborFieldMatrix
    M.toBrokenLatticeIntegratedCommonNeighborFieldMatrix

/-- Uniform common-neighbor target rows clear the conditional target
pipeline. -/
theorem pipelineCleared
    (M : CommonNeighborTargetMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_commonNeighborFieldMatrix
    M.toBrokenLatticeIntegratedCommonNeighborFieldMatrix

/-- Conditional target projection through the integrated target facade. -/
theorem targetLowerBoundEightThirtyOne
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_commonNeighborFieldMatrix
    M.toBrokenLatticeIntegratedCommonNeighborFieldMatrix

/-- Conditional target projection through the target-closure facade. -/
theorem target_via_targetClosureMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryPredicateMatrix
    M.toTargetClosureCommonNeighborGeometryPredicateMatrix

/-- Conditional target projection through the geometry integration facade. -/
theorem target_via_geometryIntegrated
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    M.toGeometryIntegratedCommonNeighborGeometryMatrix

/-- Conditional target projection through the original K23/common-neighbor
integration facade. -/
theorem target_via_k23Integrated
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  K23IntegratedMatrixW11.targetLowerBoundEightThirtyOne_of_commonNeighborIntegratedMatrix
    M.toCommonNeighborIntegratedMatrix

end CommonNeighborTargetMatrix

/-! ## Checked target projection rows -/

/-- K23 target rows as a target-closure projection. -/
def k23TargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (K23TargetMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    K23TargetMatrix.no_minimalClearedFailure
    K23TargetMatrix.targetLowerBoundEightThirtyOne

/-- Common-neighbor target rows as a target-closure projection. -/
def commonNeighborTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (CommonNeighborTargetMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    CommonNeighborTargetMatrix.no_minimalClearedFailure
    CommonNeighborTargetMatrix.targetLowerBoundEightThirtyOne

/-- K23 target rows as an integrated target route with eliminator. -/
def k23TargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (K23TargetMatrix.{u}) where
  eliminator := K23TargetMatrix.minimalClearedFailureEliminator
  noMinimal := K23TargetMatrix.no_minimalClearedFailure
  pipeline := K23TargetMatrix.pipelineCleared
  target := K23TargetMatrix.targetLowerBoundEightThirtyOne

/-- Common-neighbor target rows as an integrated target route with
eliminator. -/
def commonNeighborTargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (CommonNeighborTargetMatrix.{u}) where
  eliminator := CommonNeighborTargetMatrix.minimalClearedFailureEliminator
  noMinimal := CommonNeighborTargetMatrix.no_minimalClearedFailure
  pipeline := CommonNeighborTargetMatrix.pipelineCleared
  target := CommonNeighborTargetMatrix.targetLowerBoundEightThirtyOne

/-- K23 target rows as an integrated W11 geometry projection row. -/
def k23GeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (K23TargetMatrix.{u}) where
  geometryClosure := K23TargetMatrix.toGeometryClosureMatrix
  narrowInputs := K23TargetMatrix.toNarrowClosureInputFamily
  checkedInputs := K23TargetMatrix.toCheckedClosureInputFamily
  targetFacade := K23TargetMatrix.toTargetFacadeMatrix
  targetProjection := k23TargetClosureRow

/-- Common-neighbor target rows as an integrated W11 geometry projection row. -/
def commonNeighborGeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (CommonNeighborTargetMatrix.{u}) where
  geometryClosure := CommonNeighborTargetMatrix.toGeometryClosureMatrix
  narrowInputs := CommonNeighborTargetMatrix.toNarrowClosureInputFamily
  checkedInputs := CommonNeighborTargetMatrix.toCheckedClosureInputFamily
  targetFacade := CommonNeighborTargetMatrix.toTargetFacadeMatrix
  targetProjection := commonNeighborTargetClosureRow

/-! ## Target-facing K23/common-neighbor ledger -/

/-- Checked W11 target-facing K23/common-neighbor integration ledger.

The ledger stores route functions only; it does not construct any source,
containment, or obstruction fields. -/
structure Matrix : Type (u + 1) where
  k23Integrated :
    K23IntegratedMatrixW11.Matrix.{u}
  k23Closure :
    K23ClosureW11.Matrix.{u}
  targetClosure :
    TargetClosureMatrixW11.Matrix.{u}
  targetIntegrated :
    TargetIntegratedMatrixW11.Matrix.{u}
  geometryIntegrated :
    GeometryIntegratedW11.Matrix.{u}
  k23TargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (K23TargetMatrix.{u})
  commonNeighborTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (CommonNeighborTargetMatrix.{u})
  k23TargetIntegrated :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (K23TargetMatrix.{u})
  commonNeighborTargetIntegrated :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (CommonNeighborTargetMatrix.{u})
  k23Geometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (K23TargetMatrix.{u})
  commonNeighborGeometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (CommonNeighborTargetMatrix.{u})

/-- The checked target-facing K23/common-neighbor integration ledger. -/
def matrix : Matrix.{u} where
  k23Integrated := K23IntegratedMatrixW11.matrix
  k23Closure := K23ClosureW11.matrix
  targetClosure := TargetClosureMatrixW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  geometryIntegrated := GeometryIntegratedW11.matrix
  k23TargetClosure := k23TargetClosureRow
  commonNeighborTargetClosure := commonNeighborTargetClosureRow
  k23TargetIntegrated := k23TargetIntegratedRoute
  commonNeighborTargetIntegrated := commonNeighborTargetIntegratedRoute
  k23Geometry := k23GeometryProjectionRow
  commonNeighborGeometry := commonNeighborGeometryProjectionRow

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_k23TargetMatrix
    (M : K23TargetMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.k23TargetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_k23TargetMatrix
    (M : K23TargetMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.k23TargetIntegrated.noMinimal M

theorem pipelineCleared_of_k23TargetMatrix
    (M : K23TargetMatrix.{u}) :
    PipelineCleared :=
  matrix.k23TargetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_k23TargetMatrix
    (M : K23TargetMatrix.{u}) :
    Target :=
  matrix.k23TargetIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_k23TargetMatrix_via_targetClosure
    (M : K23TargetMatrix.{u}) :
    Target :=
  matrix.k23TargetClosure.target M

theorem targetLowerBoundEightThirtyOne_of_k23TargetMatrix_via_geometry
    (M : K23TargetMatrix.{u}) :
    Target :=
  matrix.k23Geometry.target M

theorem minimalClearedFailureEliminator_of_commonNeighborTargetMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.commonNeighborTargetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_commonNeighborTargetMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.commonNeighborTargetIntegrated.noMinimal M

theorem pipelineCleared_of_commonNeighborTargetMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    PipelineCleared :=
  matrix.commonNeighborTargetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  matrix.commonNeighborTargetIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix_via_targetClosure
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  matrix.commonNeighborTargetClosure.target M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix_via_geometry
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  matrix.commonNeighborGeometry.target M

end

end K23TargetIntegratedW11
end Swanepoel
end ErdosProblems1066
