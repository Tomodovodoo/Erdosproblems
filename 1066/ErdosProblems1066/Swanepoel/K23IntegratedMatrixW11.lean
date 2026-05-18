import ErdosProblems1066.Swanepoel.K23ClosureW11
import ErdosProblems1066.Swanepoel.K23CommonNeighborW11
import ErdosProblems1066.Swanepoel.MinimalFailureGeometryMatrixW11
import ErdosProblems1066.Swanepoel.BrokenLatticeClosureW11
import ErdosProblems1066.Swanepoel.SwanepoelW11ClosureMatrix

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 K23 integrated matrix

This file is the K23/common-neighbor integration layer for the W11 Swanepoel
closure stack.  It keeps the real missing data explicit: every target route
from K23 or common-neighbor information takes a uniform family whose rows
contain the geometry source, the matching containment package, and the
obstruction fields for the same local predicates.

No unconditional Swanepoel target is asserted here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace K23IntegratedMatrixW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  SwanepoelW11ClosureMatrix.Target

abbrev MinimalFailureExclusion : Prop :=
  SwanepoelW11ClosureMatrix.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SwanepoelW11ClosureMatrix.PipelineCleared

/-! ## Explicit source-facing rows -/

/-- Explicit K23 source row for one minimal cleared failure.

The source, containment, and obstruction fields are intentionally separate so
downstream ledgers can see exactly which data remains to be supplied. -/
structure K23IntegratedFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin
  containment : GeometryRemainingFieldsW10.ContainmentFields source
  k23Obstruction :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs
      source.localLabels.predicates.data

namespace K23IntegratedFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Repackage explicit K23 data as the source row consumed by
`K23CommonNeighborW11`. -/
def toK23ObstructionW10Fields
    (R : K23IntegratedFields.{u} C hmin) :
    K23CommonNeighborW11.K23ObstructionW10Fields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.k23Obstruction

/-- Forget to the K23 closure facade fields. -/
def toK23ClosureFields
    (R : K23IntegratedFields.{u} C hmin) :
    K23ClosureW11.K23ClosureFields.{u} C hmin :=
  R.toK23ObstructionW10Fields

/-- Forget to the W10 K23 geometry package. -/
def toK23GeometryPackage
    (R : K23IntegratedFields.{u} C hmin) :
    GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin :=
  R.toK23ObstructionW10Fields.toK23GeometryPackage

/-- View the same row as a W11 minimal-failure geometry closure row. -/
def toGeometryClosureRow
    (R : K23IntegratedFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofK23GeometryPackage
    R.toK23GeometryPackage

/-- View the same row as K23-selected broken-lattice predicate fields. -/
def toBrokenLatticeK23GeometryPredicateFields
    (R : K23IntegratedFields.{u} C hmin) :
    BrokenLatticeFieldsW11.K23GeometryPredicateFields.{u} C hmin where
  localPredicates :=
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.ofGeometrySourceFields
      R.source
  containment := R.containment
  k23NoEarly := R.toK23ObstructionW10Fields.toK23NoEarlyFields

/-- The explicit K23 row closes the fixed minimal failure through
`K23ClosureW11`. -/
theorem contradiction_via_k23Closure
    (R : K23IntegratedFields.{u} C hmin) :
    False :=
  R.toK23ClosureFields.contradiction

/-- The explicit K23 row closes the fixed minimal failure through the W11
minimal-failure geometry facade. -/
theorem contradiction_via_minimalFailureGeometry
    (R : K23IntegratedFields.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

/-- The explicit K23 row closes the fixed minimal failure through the W11
broken-lattice facade. -/
theorem contradiction_via_brokenLattice
    (R : K23IntegratedFields.{u} C hmin) :
    False :=
  R.toBrokenLatticeK23GeometryPredicateFields.contradiction

end K23IntegratedFields

/-- Explicit common-neighbor source row for one minimal cleared failure.

The common-neighbor obstruction is kept as the source field; the K23
obstruction is only obtained by the checked common-neighbor-to-K23 adapter. -/
structure CommonNeighborIntegratedFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin
  containment : GeometryRemainingFieldsW10.ContainmentFields source
  commonNeighborObstruction :
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
      source.localLabels.predicates.data

namespace CommonNeighborIntegratedFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Repackage explicit common-neighbor data as the source row consumed by
`K23CommonNeighborW11`. -/
def toCommonNeighborObstructionW10Fields
    (R : CommonNeighborIntegratedFields.{u} C hmin) :
    K23CommonNeighborW11.CommonNeighborObstructionW10Fields.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborObstruction := R.commonNeighborObstruction

/-- Forget common-neighbor fields to explicit K23 integrated fields. -/
def toK23IntegratedFields
    (R : CommonNeighborIntegratedFields.{u} C hmin) :
    K23IntegratedFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.commonNeighborObstruction.toK23ObstructionInputs

/-- Forget to the common-neighbor closure facade fields. -/
def toCommonNeighborClosureFields
    (R : CommonNeighborIntegratedFields.{u} C hmin) :
    K23ClosureW11.CommonNeighborClosureFields.{u} C hmin :=
  R.toCommonNeighborObstructionW10Fields

/-- Forget to the W10 common-neighbor geometry package. -/
def toCommonNeighborGeometryPackage
    (R : CommonNeighborIntegratedFields.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u} C hmin :=
  R.toCommonNeighborObstructionW10Fields.toCommonNeighborGeometryPackage

/-- View the same row as a W11 minimal-failure geometry closure row. -/
def toGeometryClosureRow
    (R : CommonNeighborIntegratedFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofCommonNeighborGeometryPackage
    R.toCommonNeighborGeometryPackage

/-- View the same row as common-neighbor-selected broken-lattice predicate
fields. -/
def toBrokenLatticeCommonNeighborGeometryPredicateFields
    (R : CommonNeighborIntegratedFields.{u} C hmin) :
    BrokenLatticeFieldsW11.CommonNeighborGeometryPredicateFields.{u}
      C hmin where
  localPredicates :=
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.ofGeometrySourceFields
      R.source
  containment := R.containment
  commonNeighborNoEarly :=
    R.toCommonNeighborObstructionW10Fields.toCommonNeighborNoEarlyFields

/-- The explicit common-neighbor row closes the fixed minimal failure through
`K23ClosureW11`. -/
theorem contradiction_via_k23Closure
    (R : CommonNeighborIntegratedFields.{u} C hmin) :
    False :=
  R.toCommonNeighborClosureFields.contradiction

/-- The explicit common-neighbor row closes the fixed minimal failure through
the W11 minimal-failure geometry facade. -/
theorem contradiction_via_minimalFailureGeometry
    (R : CommonNeighborIntegratedFields.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

/-- The explicit common-neighbor row closes the fixed minimal failure through
the W11 broken-lattice facade. -/
theorem contradiction_via_brokenLattice
    (R : CommonNeighborIntegratedFields.{u} C hmin) :
    False :=
  R.toBrokenLatticeCommonNeighborGeometryPredicateFields.contradiction

end CommonNeighborIntegratedFields

/-! ## Uniform explicit input matrices -/

/-- Uniform explicit K23 rows for every minimal cleared failure. -/
structure K23IntegratedMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23IntegratedFields.{u} C hmin

namespace K23IntegratedMatrix

/-- Forget explicit K23 rows to the K23 closure row family. -/
def toK23RowFamily
    (M : K23IntegratedMatrix.{u}) :
    K23ClosureW11.K23RowFamily.{u} where
  row := fun C hmin => (M.row C hmin).toK23ClosureFields

/-- Forget explicit K23 rows to the W10 K23 geometry matrix. -/
def toW10K23GeometryMatrix
    (M : K23IntegratedMatrix.{u}) :
    SwanepoelW11ClosureMatrix.W10K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPackage

/-- View explicit K23 rows as the W11 minimal-failure geometry matrix. -/
def toMinimalFailureGeometryClosureMatrix
    (M : K23IntegratedMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- View explicit K23 rows as the W11 broken-lattice K23 predicate matrix. -/
def toBrokenLatticeK23GeometryPredicateMatrix
    (M : K23IntegratedMatrix.{u}) :
    BrokenLatticeClosureW11.K23GeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeK23GeometryPredicateFields

/-- Explicit K23 rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : K23IntegratedMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toK23RowFamily.no_minimalClearedFailure

/-- Explicit K23 rows clear the W11 Swanepoel pipeline. -/
theorem pipelineCleared
    (M : K23IntegratedMatrix.{u}) :
    PipelineCleared :=
  SwanepoelW11ClosureMatrix.w10K23GeometryMatrixRow.pipeline
    M.toW10K23GeometryMatrix

/-- Explicit K23 rows reach the public target through the checked W11
Swanepoel closure facade. -/
theorem targetLowerBoundEightThirtyOne
    (M : K23IntegratedMatrix.{u}) :
    Target :=
  SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10K23GeometryMatrix
    M.toW10K23GeometryMatrix

end K23IntegratedMatrix

/-- Uniform explicit common-neighbor rows for every minimal cleared failure. -/
structure CommonNeighborIntegratedMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborIntegratedFields.{u} C hmin

namespace CommonNeighborIntegratedMatrix

/-- Forget explicit common-neighbor rows to the common-neighbor closure row
family. -/
def toCommonNeighborRowFamily
    (M : CommonNeighborIntegratedMatrix.{u}) :
    K23ClosureW11.CommonNeighborRowFamily.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborClosureFields

/-- Forget explicit common-neighbor rows to explicit K23 rows. -/
def toK23IntegratedMatrix
    (M : CommonNeighborIntegratedMatrix.{u}) :
    K23IntegratedMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23IntegratedFields

/-- Forget explicit common-neighbor rows to the W10 common-neighbor geometry
matrix. -/
def toW10CommonNeighborGeometryMatrix
    (M : CommonNeighborIntegratedMatrix.{u}) :
    SwanepoelW11ClosureMatrix.W10CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborGeometryPackage

/-- View explicit common-neighbor rows as the W11 minimal-failure geometry
matrix. -/
def toMinimalFailureGeometryClosureMatrix
    (M : CommonNeighborIntegratedMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- View explicit common-neighbor rows as the W11 broken-lattice
common-neighbor predicate matrix. -/
def toBrokenLatticeCommonNeighborGeometryPredicateMatrix
    (M : CommonNeighborIntegratedMatrix.{u}) :
    BrokenLatticeClosureW11.CommonNeighborGeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeCommonNeighborGeometryPredicateFields

/-- Explicit common-neighbor rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : CommonNeighborIntegratedMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toCommonNeighborRowFamily.no_minimalClearedFailure

/-- Explicit common-neighbor rows clear the W11 Swanepoel pipeline. -/
theorem pipelineCleared
    (M : CommonNeighborIntegratedMatrix.{u}) :
    PipelineCleared :=
  SwanepoelW11ClosureMatrix.w10CommonNeighborGeometryMatrixRow.pipeline
    M.toW10CommonNeighborGeometryMatrix

/-- Explicit common-neighbor rows reach the public target through the checked
W11 Swanepoel closure facade. -/
theorem targetLowerBoundEightThirtyOne
    (M : CommonNeighborIntegratedMatrix.{u}) :
    Target :=
  SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10CommonNeighborGeometryMatrix
    M.toW10CommonNeighborGeometryMatrix

end CommonNeighborIntegratedMatrix

/-! ## Checked projection rows -/

/-- K23 integrated rows as a broad W11 target route. -/
def k23IntegratedMatrixRow :
    SwanepoelW11ClosureMatrix.TargetProjectionRow
      (K23IntegratedMatrix.{u}) :=
  SwanepoelW11ClosureMatrix.TargetProjectionRow.ofNoMinimalAndTarget
    K23IntegratedMatrix.no_minimalClearedFailure
    K23IntegratedMatrix.targetLowerBoundEightThirtyOne

/-- Common-neighbor integrated rows as a broad W11 target route. -/
def commonNeighborIntegratedMatrixRow :
    SwanepoelW11ClosureMatrix.TargetProjectionRow
      (CommonNeighborIntegratedMatrix.{u}) :=
  SwanepoelW11ClosureMatrix.TargetProjectionRow.ofNoMinimalAndTarget
    CommonNeighborIntegratedMatrix.no_minimalClearedFailure
    CommonNeighborIntegratedMatrix.targetLowerBoundEightThirtyOne

/-- Checked route ledger tying explicit K23/common-neighbor inputs into the
available W11 closure facades.

The ledger stores route functions only; it does not contain the geometric
source, containment, or obstruction rows needed to instantiate a target route. -/
structure Matrix : Type (u + 1) where
  k23Closure : K23ClosureW11.Matrix.{u}
  minimalFailureGeometry : MinimalFailureGeometryMatrixW11.Matrix.{u}
  brokenLatticeClosure : BrokenLatticeClosureW11.Matrix.{u}
  swanepoelClosure : SwanepoelW11ClosureMatrix.Matrix.{u}
  k23Integrated :
    SwanepoelW11ClosureMatrix.TargetProjectionRow
      (K23IntegratedMatrix.{u})
  commonNeighborIntegrated :
    SwanepoelW11ClosureMatrix.TargetProjectionRow
      (CommonNeighborIntegratedMatrix.{u})

/-- The checked W11 K23/common-neighbor integration matrix. -/
def matrix : Matrix.{u} where
  k23Closure := K23ClosureW11.matrix
  minimalFailureGeometry := MinimalFailureGeometryMatrixW11.matrix
  brokenLatticeClosure := BrokenLatticeClosureW11.matrix
  swanepoelClosure := SwanepoelW11ClosureMatrix.matrix
  k23Integrated := k23IntegratedMatrixRow
  commonNeighborIntegrated := commonNeighborIntegratedMatrixRow

/-! ## Public conditional projections -/

theorem no_minimalClearedFailure_of_k23IntegratedMatrix
    (M : K23IntegratedMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.k23Integrated.noMinimal M

theorem targetLowerBoundEightThirtyOne_of_k23IntegratedMatrix
    (M : K23IntegratedMatrix.{u}) :
    Target :=
  matrix.k23Integrated.target M

theorem no_minimalClearedFailure_of_commonNeighborIntegratedMatrix
    (M : CommonNeighborIntegratedMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.commonNeighborIntegrated.noMinimal M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborIntegratedMatrix
    (M : CommonNeighborIntegratedMatrix.{u}) :
    Target :=
  matrix.commonNeighborIntegrated.target M

end

end K23IntegratedMatrixW11
end Swanepoel
end ErdosProblems1066
