import ErdosProblems1066.Swanepoel.K23TargetIntegratedW11
import ErdosProblems1066.Swanepoel.K23IntegratedMatrixW11
import ErdosProblems1066.Swanepoel.K23ClosureW11
import ErdosProblems1066.Swanepoel.GeometryIntegratedW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 K23/common-neighbor aggregate matrix

This file gathers the checked W11 K23 and common-neighbor target routes behind
one explicit aggregate row.  A row still displays the shared geometry source,
the matching containment package, and both route-specific obstruction packages.

The public target projections below are conditional on a uniform aggregate
matrix.  No uniform aggregate row family is supplied here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace K23FinalIntegratedW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  K23TargetIntegratedW11.Target

abbrev MinimalFailureExclusion : Prop :=
  K23TargetIntegratedW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  K23TargetIntegratedW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  K23TargetIntegratedW11.MinimalFailureEliminator

/-! ## Explicit aggregate rows -/

/-- One final K23/common-neighbor row for a fixed minimal cleared failure.

The row keeps the source geometry, its containment fields, the K23
obstruction, and the common-neighbor-card obstruction as separate fields so
downstream ledgers can project through either route. -/
structure K23CommonNeighborFinalFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin
  containment : GeometryRemainingFieldsW10.ContainmentFields source
  k23Obstruction :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs
      source.localLabels.predicates.data
  commonNeighborObstruction :
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
      source.localLabels.predicates.data

namespace K23CommonNeighborFinalFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Project the aggregate row to the target-facing K23 row. -/
def toK23TargetFields
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    K23TargetIntegratedW11.K23TargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.k23Obstruction

/-- Project the aggregate row to the target-facing common-neighbor row. -/
def toCommonNeighborTargetFields
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    K23TargetIntegratedW11.CommonNeighborTargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborObstruction := R.commonNeighborObstruction

/-- Project the aggregate row to the source-facing K23 integration row. -/
def toK23IntegratedFields
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    K23IntegratedMatrixW11.K23IntegratedFields.{u} C hmin :=
  R.toK23TargetFields.toK23IntegratedFields

/-- Project the aggregate row to the source-facing common-neighbor
integration row. -/
def toCommonNeighborIntegratedFields
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    K23IntegratedMatrixW11.CommonNeighborIntegratedFields.{u} C hmin :=
  R.toCommonNeighborTargetFields.toCommonNeighborIntegratedFields

/-- Project the aggregate row to the checked K23 obstruction fields. -/
def toK23ObstructionW10Fields
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    K23CommonNeighborW11.K23ObstructionW10Fields.{u} C hmin :=
  R.toK23TargetFields.toK23ObstructionW10Fields

/-- Project the aggregate row to the checked common-neighbor obstruction
fields. -/
def toCommonNeighborObstructionW10Fields
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    K23CommonNeighborW11.CommonNeighborObstructionW10Fields.{u} C hmin :=
  R.toCommonNeighborTargetFields.toCommonNeighborObstructionW10Fields

/-- The K23 no-early fields selected by the aggregate row. -/
def toK23NoEarlyFields
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    GeometryRemainingFieldsW10.K23NoEarlyFields R.source :=
  R.toK23TargetFields.toK23NoEarlyFields

/-- The common-neighbor no-early fields selected by the aggregate row. -/
def toCommonNeighborNoEarlyFields
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields R.source :=
  R.toCommonNeighborTargetFields.toCommonNeighborNoEarlyFields

/-- View the aggregate row as the integrated W11 K23 geometry row. -/
def toGeometryIntegratedK23Fields
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    GeometryIntegratedW11.K23GeometryFields.{u} C hmin :=
  R.toK23TargetFields.toGeometryIntegratedK23Fields

/-- View the aggregate row as the integrated W11 common-neighbor geometry
row. -/
def toGeometryIntegratedCommonNeighborFields
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    GeometryIntegratedW11.CommonNeighborGeometryFields.{u} C hmin :=
  R.toCommonNeighborTargetFields.toGeometryIntegratedCommonNeighborFields

/-- View the aggregate row as the integrated W11 broken-lattice K23 package. -/
def toBrokenLatticeIntegratedK23FieldPackage
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    BrokenLatticeIntegratedW11.K23FieldPackage.{u} C hmin :=
  R.toK23TargetFields.toBrokenLatticeIntegratedK23FieldPackage

/-- View the aggregate row as the integrated W11 broken-lattice
common-neighbor package. -/
def toBrokenLatticeIntegratedCommonNeighborFieldPackage
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    BrokenLatticeIntegratedW11.CommonNeighborFieldPackage.{u} C hmin :=
  R.toCommonNeighborTargetFields
    |>.toBrokenLatticeIntegratedCommonNeighborFieldPackage

/-- A fixed aggregate row closes through the K23 target route. -/
theorem contradiction_via_k23Target
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    False :=
  R.toK23TargetFields.contradiction_via_k23Integrated

/-- A fixed aggregate row closes through the common-neighbor target route. -/
theorem contradiction_via_commonNeighborTarget
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    False :=
  R.toCommonNeighborTargetFields.contradiction_via_k23Integrated

/-- A fixed aggregate row closes through the K23 geometry route. -/
theorem contradiction_via_k23Geometry
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    False :=
  R.toK23TargetFields.contradiction_via_geometryIntegrated

/-- A fixed aggregate row closes through the common-neighbor geometry route. -/
theorem contradiction_via_commonNeighborGeometry
    (R : K23CommonNeighborFinalFields.{u} C hmin) :
    False :=
  R.toCommonNeighborTargetFields.contradiction_via_geometryIntegrated

end K23CommonNeighborFinalFields

/-! ## Uniform aggregate matrices -/

/-- Uniform final K23/common-neighbor rows for every minimal cleared failure. -/
structure K23CommonNeighborFinalMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23CommonNeighborFinalFields.{u} C hmin

namespace K23CommonNeighborFinalMatrix

/-- Forget aggregate rows to the target-facing K23 matrix. -/
def toK23TargetMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    K23TargetIntegratedW11.K23TargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23TargetFields

/-- Forget aggregate rows to the target-facing common-neighbor matrix. -/
def toCommonNeighborTargetMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborTargetFields

/-- Forget aggregate rows to the source-facing K23 integration matrix. -/
def toK23IntegratedMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    K23IntegratedMatrixW11.K23IntegratedMatrix.{u} :=
  M.toK23TargetMatrix.toK23IntegratedMatrix

/-- Forget aggregate rows to the source-facing common-neighbor integration
matrix. -/
def toCommonNeighborIntegratedMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u} :=
  M.toCommonNeighborTargetMatrix.toCommonNeighborIntegratedMatrix

/-- Forget aggregate rows to the checked K23 closure row family. -/
def toK23RowFamily
    (M : K23CommonNeighborFinalMatrix.{u}) :
    K23ClosureW11.K23RowFamily.{u} :=
  M.toK23TargetMatrix.toK23RowFamily

/-- Forget aggregate rows to the checked common-neighbor closure row family. -/
def toCommonNeighborRowFamily
    (M : K23CommonNeighborFinalMatrix.{u}) :
    K23ClosureW11.CommonNeighborRowFamily.{u} :=
  M.toCommonNeighborTargetMatrix.toCommonNeighborRowFamily

/-- View aggregate rows as W10 K23 geometry rows. -/
def toW10K23GeometryMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} :=
  M.toK23TargetMatrix.toW10K23GeometryMatrix

/-- View aggregate rows as W10 common-neighbor geometry rows. -/
def toW10CommonNeighborGeometryMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} :=
  M.toCommonNeighborTargetMatrix.toW10CommonNeighborGeometryMatrix

/-- View aggregate rows as the integrated W11 K23 geometry matrix. -/
def toGeometryIntegratedK23GeometryMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    GeometryIntegratedW11.K23GeometryMatrix.{u} :=
  M.toK23TargetMatrix.toGeometryIntegratedK23GeometryMatrix

/-- View aggregate rows as the integrated W11 common-neighbor geometry
matrix. -/
def toGeometryIntegratedCommonNeighborGeometryMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u} :=
  M.toCommonNeighborTargetMatrix
    |>.toGeometryIntegratedCommonNeighborGeometryMatrix

/-- View aggregate rows as the integrated W11 broken-lattice K23 field
matrix. -/
def toBrokenLatticeIntegratedK23FieldMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    BrokenLatticeIntegratedW11.K23FieldMatrix.{u} :=
  M.toK23TargetMatrix.toBrokenLatticeIntegratedK23FieldMatrix

/-- View aggregate rows as the integrated W11 broken-lattice common-neighbor
field matrix. -/
def toBrokenLatticeIntegratedCommonNeighborFieldMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u} :=
  M.toCommonNeighborTargetMatrix
    |>.toBrokenLatticeIntegratedCommonNeighborFieldMatrix

/-- View aggregate rows as target-closure K23 predicate rows. -/
def toTargetClosureK23GeometryPredicateMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    TargetClosureMatrixW11.K23GeometryPredicateMatrix.{u} :=
  M.toK23TargetMatrix.toTargetClosureK23GeometryPredicateMatrix

/-- View aggregate rows as target-closure common-neighbor predicate rows. -/
def toTargetClosureCommonNeighborGeometryPredicateMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    TargetClosureMatrixW11.CommonNeighborGeometryPredicateMatrix.{u} :=
  M.toCommonNeighborTargetMatrix
    |>.toTargetClosureCommonNeighborGeometryPredicateMatrix

/-- View aggregate rows as a K23-selected W11 geometry closure matrix. -/
def toK23GeometryClosureMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    GeometryIntegratedW11.GeometryClosureMatrix.{u} :=
  M.toK23TargetMatrix.toGeometryClosureMatrix

/-- View aggregate rows as a common-neighbor-selected W11 geometry closure
matrix. -/
def toCommonNeighborGeometryClosureMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    GeometryIntegratedW11.GeometryClosureMatrix.{u} :=
  M.toCommonNeighborTargetMatrix.toGeometryClosureMatrix

/-- View aggregate rows as K23-selected narrow closure inputs. -/
def toK23NarrowClosureInputFamily
    (M : K23CommonNeighborFinalMatrix.{u}) :
    GeometryIntegratedW11.NarrowClosureInputFamily.{u} :=
  M.toK23TargetMatrix.toNarrowClosureInputFamily

/-- View aggregate rows as common-neighbor-selected narrow closure inputs. -/
def toCommonNeighborNarrowClosureInputFamily
    (M : K23CommonNeighborFinalMatrix.{u}) :
    GeometryIntegratedW11.NarrowClosureInputFamily.{u} :=
  M.toCommonNeighborTargetMatrix.toNarrowClosureInputFamily

/-- View aggregate rows as K23-selected checked closure inputs. -/
def toK23CheckedClosureInputFamily
    (M : K23CommonNeighborFinalMatrix.{u}) :
    GeometryIntegratedW11.CheckedClosureInputFamily.{u} :=
  M.toK23TargetMatrix.toCheckedClosureInputFamily

/-- View aggregate rows as common-neighbor-selected checked closure inputs. -/
def toCommonNeighborCheckedClosureInputFamily
    (M : K23CommonNeighborFinalMatrix.{u}) :
    GeometryIntegratedW11.CheckedClosureInputFamily.{u} :=
  M.toCommonNeighborTargetMatrix.toCheckedClosureInputFamily

/-- View aggregate rows as the K23-selected W10 target facade matrix. -/
def toK23TargetFacadeMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    GeometryIntegratedW11.TargetFacadeMatrix :=
  M.toK23TargetMatrix.toTargetFacadeMatrix

/-- View aggregate rows as the common-neighbor-selected W10 target facade
matrix. -/
def toCommonNeighborTargetFacadeMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    GeometryIntegratedW11.TargetFacadeMatrix :=
  M.toCommonNeighborTargetMatrix.toTargetFacadeMatrix

/-- Aggregate rows give the minimal-failure eliminator through K23 fields. -/
theorem minimalClearedFailureEliminator_via_k23
    (M : K23CommonNeighborFinalMatrix.{u}) :
    MinimalFailureEliminator :=
  K23TargetIntegratedW11.K23TargetMatrix.minimalClearedFailureEliminator
    M.toK23TargetMatrix

/-- Aggregate rows give the minimal-failure eliminator through
common-neighbor fields. -/
theorem minimalClearedFailureEliminator_via_commonNeighbor
    (M : K23CommonNeighborFinalMatrix.{u}) :
    MinimalFailureEliminator :=
  K23TargetIntegratedW11.CommonNeighborTargetMatrix.minimalClearedFailureEliminator
    M.toCommonNeighborTargetMatrix

/-- Aggregate rows rule out all minimal cleared failures through K23 fields. -/
theorem no_minimalClearedFailure_via_k23
    (M : K23CommonNeighborFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  K23TargetIntegratedW11.K23TargetMatrix.no_minimalClearedFailure
    M.toK23TargetMatrix

/-- Aggregate rows rule out all minimal cleared failures through
common-neighbor fields. -/
theorem no_minimalClearedFailure_via_commonNeighbor
    (M : K23CommonNeighborFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  K23TargetIntegratedW11.CommonNeighborTargetMatrix.no_minimalClearedFailure
    M.toCommonNeighborTargetMatrix

/-- Aggregate rows clear the conditional target pipeline through K23 fields. -/
theorem pipelineCleared_via_k23
    (M : K23CommonNeighborFinalMatrix.{u}) :
    PipelineCleared :=
  K23TargetIntegratedW11.K23TargetMatrix.pipelineCleared
    M.toK23TargetMatrix

/-- Aggregate rows clear the conditional target pipeline through
common-neighbor fields. -/
theorem pipelineCleared_via_commonNeighbor
    (M : K23CommonNeighborFinalMatrix.{u}) :
    PipelineCleared :=
  K23TargetIntegratedW11.CommonNeighborTargetMatrix.pipelineCleared
    M.toCommonNeighborTargetMatrix

/-- Conditional target projection through the K23 integrated route. -/
theorem targetLowerBoundEightThirtyOne_via_k23
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.K23TargetMatrix.targetLowerBoundEightThirtyOne
    M.toK23TargetMatrix

/-- Conditional target projection through the common-neighbor integrated
route. -/
theorem targetLowerBoundEightThirtyOne_via_commonNeighbor
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.CommonNeighborTargetMatrix.targetLowerBoundEightThirtyOne
    M.toCommonNeighborTargetMatrix

/-- Conditional target projection through the K23 target-closure route. -/
theorem targetLowerBoundEightThirtyOne_via_k23TargetClosure
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.K23TargetMatrix.target_via_targetClosureMatrix
    M.toK23TargetMatrix

/-- Conditional target projection through the common-neighbor target-closure
route. -/
theorem targetLowerBoundEightThirtyOne_via_commonNeighborTargetClosure
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.CommonNeighborTargetMatrix.target_via_targetClosureMatrix
    M.toCommonNeighborTargetMatrix

/-- Conditional target projection through the K23 geometry route. -/
theorem targetLowerBoundEightThirtyOne_via_k23Geometry
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.K23TargetMatrix.target_via_geometryIntegrated
    M.toK23TargetMatrix

/-- Conditional target projection through the common-neighbor geometry route. -/
theorem targetLowerBoundEightThirtyOne_via_commonNeighborGeometry
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.CommonNeighborTargetMatrix.target_via_geometryIntegrated
    M.toCommonNeighborTargetMatrix

/-- Conditional target projection through the source-facing K23 integration
route. -/
theorem targetLowerBoundEightThirtyOne_via_k23Integrated
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.K23TargetMatrix.target_via_k23Integrated
    M.toK23TargetMatrix

/-- Conditional target projection through the source-facing common-neighbor
integration route. -/
theorem targetLowerBoundEightThirtyOne_via_commonNeighborIntegrated
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.CommonNeighborTargetMatrix.target_via_k23Integrated
    M.toCommonNeighborTargetMatrix

end K23CommonNeighborFinalMatrix

/-! ## Checked aggregate projection rows -/

/-- K23-selected aggregate rows as a target-closure projection. -/
def k23FinalTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (K23CommonNeighborFinalMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    K23CommonNeighborFinalMatrix.no_minimalClearedFailure_via_k23
    K23CommonNeighborFinalMatrix.targetLowerBoundEightThirtyOne_via_k23

/-- Common-neighbor-selected aggregate rows as a target-closure projection. -/
def commonNeighborFinalTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (K23CommonNeighborFinalMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    K23CommonNeighborFinalMatrix.no_minimalClearedFailure_via_commonNeighbor
    K23CommonNeighborFinalMatrix.targetLowerBoundEightThirtyOne_via_commonNeighbor

/-- K23-selected aggregate rows as an integrated target route. -/
def k23FinalIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (K23CommonNeighborFinalMatrix.{u}) where
  eliminator := K23CommonNeighborFinalMatrix.minimalClearedFailureEliminator_via_k23
  noMinimal := K23CommonNeighborFinalMatrix.no_minimalClearedFailure_via_k23
  pipeline := K23CommonNeighborFinalMatrix.pipelineCleared_via_k23
  target := K23CommonNeighborFinalMatrix.targetLowerBoundEightThirtyOne_via_k23

/-- Common-neighbor-selected aggregate rows as an integrated target route. -/
def commonNeighborFinalIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (K23CommonNeighborFinalMatrix.{u}) where
  eliminator :=
    K23CommonNeighborFinalMatrix.minimalClearedFailureEliminator_via_commonNeighbor
  noMinimal :=
    K23CommonNeighborFinalMatrix.no_minimalClearedFailure_via_commonNeighbor
  pipeline := K23CommonNeighborFinalMatrix.pipelineCleared_via_commonNeighbor
  target :=
    K23CommonNeighborFinalMatrix.targetLowerBoundEightThirtyOne_via_commonNeighbor

/-- K23-selected aggregate rows as an integrated W11 geometry projection. -/
def k23FinalGeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (K23CommonNeighborFinalMatrix.{u}) where
  geometryClosure := K23CommonNeighborFinalMatrix.toK23GeometryClosureMatrix
  narrowInputs := K23CommonNeighborFinalMatrix.toK23NarrowClosureInputFamily
  checkedInputs := K23CommonNeighborFinalMatrix.toK23CheckedClosureInputFamily
  targetFacade := K23CommonNeighborFinalMatrix.toK23TargetFacadeMatrix
  targetProjection := k23FinalTargetClosureRow

/-- Common-neighbor-selected aggregate rows as an integrated W11 geometry
projection. -/
def commonNeighborFinalGeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (K23CommonNeighborFinalMatrix.{u}) where
  geometryClosure :=
    K23CommonNeighborFinalMatrix.toCommonNeighborGeometryClosureMatrix
  narrowInputs :=
    K23CommonNeighborFinalMatrix.toCommonNeighborNarrowClosureInputFamily
  checkedInputs :=
    K23CommonNeighborFinalMatrix.toCommonNeighborCheckedClosureInputFamily
  targetFacade := K23CommonNeighborFinalMatrix.toCommonNeighborTargetFacadeMatrix
  targetProjection := commonNeighborFinalTargetClosureRow

/-! ## Final aggregate ledger -/

/-- Final W11 K23/common-neighbor aggregate ledger.

This record stores checked source ledgers and conditional route rows only.  It
does not supply a uniform aggregate matrix. -/
structure Matrix : Type (u + 1) where
  k23TargetIntegrated :
    K23TargetIntegratedW11.Matrix.{u}
  k23Integrated :
    K23IntegratedMatrixW11.Matrix.{u}
  k23Closure :
    K23ClosureW11.Matrix.{u}
  geometryIntegrated :
    GeometryIntegratedW11.Matrix.{u}
  targetIntegrated :
    TargetIntegratedMatrixW11.Matrix.{u}
  k23TargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (K23CommonNeighborFinalMatrix.{u})
  commonNeighborTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (K23CommonNeighborFinalMatrix.{u})
  k23IntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (K23CommonNeighborFinalMatrix.{u})
  commonNeighborIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (K23CommonNeighborFinalMatrix.{u})
  k23Geometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (K23CommonNeighborFinalMatrix.{u})
  commonNeighborGeometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (K23CommonNeighborFinalMatrix.{u})

/-- The checked final W11 K23/common-neighbor aggregate ledger. -/
def matrix : Matrix.{u} where
  k23TargetIntegrated := K23TargetIntegratedW11.matrix
  k23Integrated := K23IntegratedMatrixW11.matrix
  k23Closure := K23ClosureW11.matrix
  geometryIntegrated := GeometryIntegratedW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  k23TargetClosure := k23FinalTargetClosureRow
  commonNeighborTargetClosure := commonNeighborFinalTargetClosureRow
  k23IntegratedRoute := k23FinalIntegratedRoute
  commonNeighborIntegratedRoute := commonNeighborFinalIntegratedRoute
  k23Geometry := k23FinalGeometryProjectionRow
  commonNeighborGeometry := commonNeighborFinalGeometryProjectionRow

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_finalMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.commonNeighborIntegratedRoute.eliminator M

theorem no_minimalClearedFailure_of_finalMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.commonNeighborIntegratedRoute.noMinimal M

theorem pipelineCleared_of_finalMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    PipelineCleared :=
  matrix.commonNeighborIntegratedRoute.pipeline M

theorem targetLowerBoundEightThirtyOne_of_finalMatrix
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  matrix.commonNeighborIntegratedRoute.target M

theorem targetLowerBoundEightThirtyOne_of_finalMatrix_via_k23
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  matrix.k23IntegratedRoute.target M

theorem targetLowerBoundEightThirtyOne_of_finalMatrix_via_k23TargetClosure
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  matrix.k23TargetClosure.target M

theorem targetLowerBoundEightThirtyOne_of_finalMatrix_via_commonNeighborTargetClosure
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  matrix.commonNeighborTargetClosure.target M

theorem targetLowerBoundEightThirtyOne_of_finalMatrix_via_k23Geometry
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  matrix.k23Geometry.target M

theorem targetLowerBoundEightThirtyOne_of_finalMatrix_via_commonNeighborGeometry
    (M : K23CommonNeighborFinalMatrix.{u}) :
    Target :=
  matrix.commonNeighborGeometry.target M

end

end K23FinalIntegratedW11
end Swanepoel
end ErdosProblems1066
