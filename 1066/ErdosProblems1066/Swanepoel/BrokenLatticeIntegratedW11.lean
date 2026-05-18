import ErdosProblems1066.Swanepoel.BrokenLatticeClosureW11
import ErdosProblems1066.Swanepoel.MinimalFailureGeometryMatrixW11
import ErdosProblems1066.Swanepoel.K23CommonNeighborW11
import ErdosProblems1066.Swanepoel.SwanepoelTargetClosureW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Integrated W11 broken-lattice matrix

This file is a source-facing integration layer for the W11 broken-lattice
rows.  It keeps the geometry source, containment, and the route-specific
no-early field explicit, then records checked adapters into:

* the W11 broken-lattice predicate packages;
* the W11 minimal-failure geometry eliminators;
* the W11 target facade, always with the input package supplied explicitly.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticeIntegratedW11

open MinimalGraphFacts

universe u v

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  SwanepoelTargetClosureW11.Target

abbrev MinimalFailureExclusion : Prop :=
  SwanepoelTargetClosureW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SwanepoelTargetClosureW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  MinimalClearedFailureEliminator

/-! ## Pointwise source-facing packages -/

/-- Direct W11 broken-lattice fields for one fixed minimal failure.

The source geometry, window containment, and direct five-start no-early fields
are kept as separate fields over the same local labels. -/
structure DirectFieldPackage
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin
  containment : GeometryRemainingFieldsW10.ContainmentFields source
  noStartNoEarly : GeometryRemainingFieldsW10.NoStartNoEarlyFields source

namespace DirectFieldPackage

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The exact local-predicate package selected by the displayed source row. -/
def toGeometryLocalPredicateFields
    (R : DirectFieldPackage.{u} C hmin) :
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.{u} C hmin :=
  BrokenLatticeFieldsW11.GeometryLocalPredicateFields.ofGeometrySourceFields
    R.source

/-- Repackage as the W10 direct geometry row. -/
def toDirectGeometryPackage
    (R : DirectFieldPackage.{u} C hmin) :
    GeometryRemainingFieldsW10.DirectGeometryPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

/-- Repackage as the W11 broken-lattice direct predicate fields. -/
def toDirectGeometryPredicateFields
    (R : DirectFieldPackage.{u} C hmin) :
    BrokenLatticeFieldsW11.DirectGeometryPredicateFields.{u} C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

/-- Repackage as the W11 minimal-failure geometry row. -/
def toGeometryClosureRow
    (R : DirectFieldPackage.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofDirectGeometryPackage
    R.toDirectGeometryPackage

/-- A direct pointwise package closes the fixed minimal failure. -/
theorem contradiction
    (R : DirectFieldPackage.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end DirectFieldPackage

/-- K23-derived W11 broken-lattice fields for one fixed minimal failure. -/
structure K23FieldPackage
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin
  containment : GeometryRemainingFieldsW10.ContainmentFields source
  k23NoEarly : GeometryRemainingFieldsW10.K23NoEarlyFields source

namespace K23FieldPackage

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The exact local-predicate package selected by the displayed source row. -/
def toGeometryLocalPredicateFields
    (R : K23FieldPackage.{u} C hmin) :
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.{u} C hmin :=
  BrokenLatticeFieldsW11.GeometryLocalPredicateFields.ofGeometrySourceFields
    R.source

/-- Repackage as the W10 K23 geometry row. -/
def toK23GeometryPackage
    (R : K23FieldPackage.{u} C hmin) :
    GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- Repackage as the W11 broken-lattice K23 predicate fields. -/
def toK23GeometryPredicateFields
    (R : K23FieldPackage.{u} C hmin) :
    BrokenLatticeFieldsW11.K23GeometryPredicateFields.{u} C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- Repackage as the K23/common-neighbor W11 obstruction row. -/
def toK23ObstructionW10Fields
    (R : K23FieldPackage.{u} C hmin) :
    K23CommonNeighborW11.K23ObstructionW10Fields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.k23NoEarly.k23Obstruction

/-- Repackage as the W11 minimal-failure geometry row. -/
def toGeometryClosureRow
    (R : K23FieldPackage.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofK23GeometryPackage
    R.toK23GeometryPackage

/-- A K23 pointwise package closes the fixed minimal failure. -/
theorem contradiction
    (R : K23FieldPackage.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end K23FieldPackage

/-- Common-neighbor-derived W11 broken-lattice fields for one fixed minimal
failure. -/
structure CommonNeighborFieldPackage
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin
  containment : GeometryRemainingFieldsW10.ContainmentFields source
  commonNeighborNoEarly :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields source

namespace CommonNeighborFieldPackage

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The exact local-predicate package selected by the displayed source row. -/
def toGeometryLocalPredicateFields
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.{u} C hmin :=
  BrokenLatticeFieldsW11.GeometryLocalPredicateFields.ofGeometrySourceFields
    R.source

/-- Repackage as the W10 common-neighbor geometry row. -/
def toCommonNeighborGeometryPackage
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Repackage as the W11 broken-lattice common-neighbor predicate fields. -/
def toCommonNeighborGeometryPredicateFields
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    BrokenLatticeFieldsW11.CommonNeighborGeometryPredicateFields.{u}
      C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Repackage as the K23/common-neighbor W11 obstruction row. -/
def toCommonNeighborObstructionW10Fields
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    K23CommonNeighborW11.CommonNeighborObstructionW10Fields.{u}
      C hmin where
  source := R.source
  containment := R.containment
  commonNeighborObstruction :=
    R.commonNeighborNoEarly.commonNeighborObstruction

/-- Forget common-neighbor fields to the K23 source-facing package. -/
def toK23FieldPackage
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    K23FieldPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.commonNeighborNoEarly.toK23NoEarlyFields

/-- Repackage as the W11 minimal-failure geometry row. -/
def toGeometryClosureRow
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofCommonNeighborGeometryPackage
    R.toCommonNeighborGeometryPackage

/-- A common-neighbor pointwise package closes the fixed minimal failure. -/
theorem contradiction
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end CommonNeighborFieldPackage

/-! ## Uniform source-facing matrices -/

/-- Uniform direct W11 packages for every minimal cleared failure. -/
structure DirectFieldMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectFieldPackage.{u} C hmin

namespace DirectFieldMatrix

/-- Convert direct source-facing rows to W11 predicate-field rows. -/
def toDirectGeometryPredicateMatrix
    (M : DirectFieldMatrix.{u}) :
    BrokenLatticeClosureW11.DirectGeometryPredicateMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectGeometryPredicateFields

/-- Convert direct source-facing rows to W10 direct geometry rows. -/
def toW10DirectGeometryMatrix
    (M : DirectFieldMatrix.{u}) :
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectGeometryPackage

/-- Convert direct source-facing rows to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : DirectFieldMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} :=
  MinimalFailureGeometryMatrixW11.directGeometryMatrixToGeometryClosureMatrix
    M.toW10DirectGeometryMatrix

/-- Convert direct rows to the narrow concrete closure input family. -/
def toNarrowClosureInputFamily
    (M : DirectFieldMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toNarrowClosureInputFamily

/-- Convert direct rows to the checked refined closure input family. -/
def toCheckedClosureInputFamily
    (M : DirectFieldMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toCheckedClosureInputFamily

/-- Direct source-facing rows give a minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : DirectFieldMatrix.{u}) :
    MinimalFailureEliminator := by
  intro n C hmin
  exact (M.row C hmin).contradiction

/-- Direct source-facing rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : DirectFieldMatrix.{u}) :
    MinimalFailureExclusion :=
  MinimalGraphFacts.no_minimalClearedFailure
    M.minimalClearedFailureEliminator

/-- Direct source-facing rows clear the target facade pipeline
conditionally. -/
theorem pipelineCleared
    (M : DirectFieldMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

/-- Conditional target projection from direct source-facing rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : DirectFieldMatrix.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    M.toW10DirectGeometryMatrix

end DirectFieldMatrix

/-- Uniform K23-derived W11 packages for every minimal cleared failure. -/
structure K23FieldMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23FieldPackage.{u} C hmin

namespace K23FieldMatrix

/-- Convert K23 source-facing rows to W11 predicate-field rows. -/
def toK23GeometryPredicateMatrix
    (M : K23FieldMatrix.{u}) :
    BrokenLatticeClosureW11.K23GeometryPredicateMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPredicateFields

/-- Convert K23 source-facing rows to W10 K23 geometry rows. -/
def toW10K23GeometryMatrix
    (M : K23FieldMatrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPackage

/-- Convert K23 source-facing rows to the W11 obstruction row family. -/
def toK23ObstructionW10RowFamily
    (M : K23FieldMatrix.{u}) :
    K23CommonNeighborW11.K23ObstructionW10RowFamily.{u} where
  row := fun C hmin => (M.row C hmin).toK23ObstructionW10Fields

/-- Convert K23 source-facing rows to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : K23FieldMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} :=
  MinimalFailureGeometryMatrixW11.k23GeometryMatrixToGeometryClosureMatrix
    M.toW10K23GeometryMatrix

/-- Convert K23 rows to the narrow concrete closure input family. -/
def toNarrowClosureInputFamily
    (M : K23FieldMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toNarrowClosureInputFamily

/-- Convert K23 rows to the checked refined closure input family. -/
def toCheckedClosureInputFamily
    (M : K23FieldMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toCheckedClosureInputFamily

/-- K23 source-facing rows give a minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : K23FieldMatrix.{u}) :
    MinimalFailureEliminator :=
  K23CommonNeighborW11.minimalClearedFailureEliminator_of_k23W10Rows
    M.toK23ObstructionW10RowFamily

/-- K23 source-facing rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : K23FieldMatrix.{u}) :
    MinimalFailureExclusion :=
  MinimalGraphFacts.no_minimalClearedFailure
    M.minimalClearedFailureEliminator

/-- K23 source-facing rows clear the target facade pipeline conditionally. -/
theorem pipelineCleared
    (M : K23FieldMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

/-- Conditional target projection from K23 source-facing rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : K23FieldMatrix.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    M.toW10K23GeometryMatrix

end K23FieldMatrix

/-- Uniform common-neighbor-derived W11 packages for every minimal cleared
failure. -/
structure CommonNeighborFieldMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborFieldPackage.{u} C hmin

namespace CommonNeighborFieldMatrix

/-- Convert common-neighbor rows to W11 predicate-field rows. -/
def toCommonNeighborGeometryPredicateMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    BrokenLatticeClosureW11.CommonNeighborGeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toCommonNeighborGeometryPredicateFields

/-- Convert common-neighbor rows to W10 common-neighbor geometry rows. -/
def toW10CommonNeighborGeometryMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborGeometryPackage

/-- Convert common-neighbor rows to the W11 obstruction row family. -/
def toCommonNeighborObstructionW10RowFamily
    (M : CommonNeighborFieldMatrix.{u}) :
    K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u} where
  row := fun C hmin =>
    (M.row C hmin).toCommonNeighborObstructionW10Fields

/-- Forget common-neighbor source-facing rows to K23 source-facing rows. -/
def toK23FieldMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    K23FieldMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23FieldPackage

/-- Convert common-neighbor rows to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} :=
  MinimalFailureGeometryMatrixW11.commonNeighborGeometryMatrixToGeometryClosureMatrix
    M.toW10CommonNeighborGeometryMatrix

/-- Convert common-neighbor rows to the narrow concrete closure input family.
-/
def toNarrowClosureInputFamily
    (M : CommonNeighborFieldMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toNarrowClosureInputFamily

/-- Convert common-neighbor rows to the checked refined closure input family.
-/
def toCheckedClosureInputFamily
    (M : CommonNeighborFieldMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toCheckedClosureInputFamily

/-- Common-neighbor source-facing rows give a minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : CommonNeighborFieldMatrix.{u}) :
    MinimalFailureEliminator :=
  K23CommonNeighborW11.minimalClearedFailureEliminator_of_commonNeighborW10Rows
    M.toCommonNeighborObstructionW10RowFamily

/-- Common-neighbor source-facing rows rule out every minimal cleared
failure. -/
theorem no_minimalClearedFailure
    (M : CommonNeighborFieldMatrix.{u}) :
    MinimalFailureExclusion :=
  MinimalGraphFacts.no_minimalClearedFailure
    M.minimalClearedFailureEliminator

/-- Common-neighbor source-facing rows clear the target facade pipeline
conditionally. -/
theorem pipelineCleared
    (M : CommonNeighborFieldMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

/-- Conditional target projection from common-neighbor source-facing rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : CommonNeighborFieldMatrix.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    M.toW10CommonNeighborGeometryMatrix

end CommonNeighborFieldMatrix

/-! ## Integrated projection ledger -/

/-- A checked conditional route from an explicit W11 input package. -/
structure ProjectionRow (alpha : Type v) : Type v where
  eliminator : alpha -> MinimalFailureEliminator
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

/-- Projection row for direct source-facing W11 packages. -/
def directFieldMatrixRow :
    ProjectionRow (DirectFieldMatrix.{u}) where
  eliminator := DirectFieldMatrix.minimalClearedFailureEliminator
  noMinimal := DirectFieldMatrix.no_minimalClearedFailure
  pipeline := DirectFieldMatrix.pipelineCleared
  target := DirectFieldMatrix.targetLowerBoundEightThirtyOne

/-- Projection row for K23 source-facing W11 packages. -/
def k23FieldMatrixRow :
    ProjectionRow (K23FieldMatrix.{u}) where
  eliminator := K23FieldMatrix.minimalClearedFailureEliminator
  noMinimal := K23FieldMatrix.no_minimalClearedFailure
  pipeline := K23FieldMatrix.pipelineCleared
  target := K23FieldMatrix.targetLowerBoundEightThirtyOne

/-- Projection row for common-neighbor source-facing W11 packages. -/
def commonNeighborFieldMatrixRow :
    ProjectionRow (CommonNeighborFieldMatrix.{u}) where
  eliminator := CommonNeighborFieldMatrix.minimalClearedFailureEliminator
  noMinimal := CommonNeighborFieldMatrix.no_minimalClearedFailure
  pipeline := CommonNeighborFieldMatrix.pipelineCleared
  target := CommonNeighborFieldMatrix.targetLowerBoundEightThirtyOne

/-- Integrated W11 broken-lattice ledger.

The ledger stores routes only.  Every route still requires one of the explicit
source-facing matrices above. -/
structure Matrix : Type (u + 1) where
  targetClosure : SwanepoelTargetClosureW11.Matrix.{u}
  brokenLatticeClosure : BrokenLatticeClosureW11.Matrix.{u}
  minimalFailureGeometry : MinimalFailureGeometryMatrixW11.Matrix.{u}
  directFields : ProjectionRow (DirectFieldMatrix.{u})
  k23Fields : ProjectionRow (K23FieldMatrix.{u})
  commonNeighborFields : ProjectionRow (CommonNeighborFieldMatrix.{u})

/-- The checked integrated W11 broken-lattice route ledger. -/
def matrix : Matrix.{u} where
  targetClosure := SwanepoelTargetClosureW11.matrix
  brokenLatticeClosure := BrokenLatticeClosureW11.matrix
  minimalFailureGeometry := MinimalFailureGeometryMatrixW11.matrix
  directFields := directFieldMatrixRow
  k23Fields := k23FieldMatrixRow
  commonNeighborFields := commonNeighborFieldMatrixRow

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_directFieldMatrix
    (M : DirectFieldMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.directFields.eliminator M

theorem no_minimalClearedFailure_of_directFieldMatrix
    (M : DirectFieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.directFields.noMinimal M

theorem pipelineCleared_of_directFieldMatrix
    (M : DirectFieldMatrix.{u}) :
    PipelineCleared :=
  matrix.directFields.pipeline M

theorem targetLowerBoundEightThirtyOne_of_directFieldMatrix
    (M : DirectFieldMatrix.{u}) :
    Target :=
  matrix.directFields.target M

theorem minimalClearedFailureEliminator_of_k23FieldMatrix
    (M : K23FieldMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.k23Fields.eliminator M

theorem no_minimalClearedFailure_of_k23FieldMatrix
    (M : K23FieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.k23Fields.noMinimal M

theorem pipelineCleared_of_k23FieldMatrix
    (M : K23FieldMatrix.{u}) :
    PipelineCleared :=
  matrix.k23Fields.pipeline M

theorem targetLowerBoundEightThirtyOne_of_k23FieldMatrix
    (M : K23FieldMatrix.{u}) :
    Target :=
  matrix.k23Fields.target M

theorem minimalClearedFailureEliminator_of_commonNeighborFieldMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.commonNeighborFields.eliminator M

theorem no_minimalClearedFailure_of_commonNeighborFieldMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.commonNeighborFields.noMinimal M

theorem pipelineCleared_of_commonNeighborFieldMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    PipelineCleared :=
  matrix.commonNeighborFields.pipeline M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.commonNeighborFields.target M

end

end BrokenLatticeIntegratedW11
end Swanepoel
end ErdosProblems1066
