import ErdosProblems1066.Swanepoel.BrokenLatticeIntegratedW11
import ErdosProblems1066.Swanepoel.BrokenLatticeClosureW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11
import ErdosProblems1066.Swanepoel.MinimalFailureGeometryClosureW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Target-facing W11 broken-lattice matrix

This file routes the explicit direct, K23, and common-neighbor
broken-lattice source matrices through the W11 target-closure rows.

For each route, the ledger also records the displayed source-geometry view
and the geometry-selected E22/E23 view.  Every public target projection below
takes one of those source matrices as an input.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticeTargetIntegratedW11

open MinimalGraphFacts

universe u v w

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetClosureMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetClosureMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetClosureMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  BrokenLatticeIntegratedW11.MinimalFailureEliminator

/-! ## Generic row adapters -/

/-- Pull a W11 target-closure row back along an explicit projection. -/
def pullbackTargetClosureRow
    {alpha : Sort v} {beta : Sort w}
    (R : TargetClosureMatrixW11.TargetProjectionRow beta)
    (f : alpha -> beta) :
    TargetClosureMatrixW11.TargetProjectionRow alpha where
  noMinimal := fun a => R.noMinimal (f a)
  pipeline := fun a => R.pipeline (f a)
  target := fun a => R.target (f a)

/-- Reuse a broader W11 target row as a target-closure row. -/
def targetClosureRowOfW11Row
    {alpha : Sort v}
    (R : SwanepoelW11ClosureMatrix.TargetProjectionRow alpha) :
    TargetClosureMatrixW11.TargetProjectionRow alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-! ## Pointwise explicit views -/

/-- Direct source rows expose the geometry-selected E22/E23 package. -/
def directFieldPackageToGeometryE22E23PredicateFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.DirectFieldPackage.{u} C hmin) :
    BrokenLatticeFieldsW11.GeometryE22E23PredicateFields.{u} C hmin :=
  BrokenLatticeFieldsW11.DirectGeometryPredicateFields.toGeometryE22E23PredicateFields
    R.toDirectGeometryPredicateFields

/-- Direct source rows as explicit minimal-failure geometry rows. -/
def directFieldPackageToMinimalFailureDirectGeometryFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.DirectFieldPackage.{u} C hmin) :
    MinimalFailureGeometryClosureW11.DirectGeometryFields.{u} C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

@[simp]
theorem directFieldPackage_e22e23_source
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.DirectFieldPackage.{u} C hmin) :
    (directFieldPackageToGeometryE22E23PredicateFields R).localPredicates.source =
      R.source :=
  rfl

@[simp]
theorem directFieldPackage_sourceGeometry_source
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.DirectFieldPackage.{u} C hmin) :
    (directFieldPackageToMinimalFailureDirectGeometryFields R).source =
      R.source :=
  rfl

/-- K23 source rows expose the geometry-selected E22/E23 package. -/
def k23FieldPackageToGeometryE22E23PredicateFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.K23FieldPackage.{u} C hmin) :
    BrokenLatticeFieldsW11.GeometryE22E23PredicateFields.{u} C hmin :=
  BrokenLatticeFieldsW11.DirectGeometryPredicateFields.toGeometryE22E23PredicateFields
    (BrokenLatticeFieldsW11.K23GeometryPredicateFields.toDirectGeometryPredicateFields
      R.toK23GeometryPredicateFields)

/-- K23 source rows as explicit minimal-failure geometry rows. -/
def k23FieldPackageToMinimalFailureK23GeometryFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.K23FieldPackage.{u} C hmin) :
    MinimalFailureGeometryClosureW11.K23GeometryFields.{u} C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  k23NoEarly := R.k23NoEarly

@[simp]
theorem k23FieldPackage_e22e23_source
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.K23FieldPackage.{u} C hmin) :
    (k23FieldPackageToGeometryE22E23PredicateFields R).localPredicates.source =
      R.source :=
  rfl

@[simp]
theorem k23FieldPackage_sourceGeometry_source
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.K23FieldPackage.{u} C hmin) :
    (k23FieldPackageToMinimalFailureK23GeometryFields R).source =
      R.source :=
  rfl

/-- Common-neighbor source rows expose the geometry-selected E22/E23 package. -/
def commonNeighborFieldPackageToGeometryE22E23PredicateFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.CommonNeighborFieldPackage.{u} C hmin) :
    BrokenLatticeFieldsW11.GeometryE22E23PredicateFields.{u} C hmin :=
  BrokenLatticeFieldsW11.DirectGeometryPredicateFields.toGeometryE22E23PredicateFields
    (BrokenLatticeFieldsW11.K23GeometryPredicateFields.toDirectGeometryPredicateFields
      (BrokenLatticeFieldsW11.CommonNeighborGeometryPredicateFields.toK23GeometryPredicateFields
        R.toCommonNeighborGeometryPredicateFields))

/-- Common-neighbor source rows as explicit minimal-failure geometry rows. -/
def commonNeighborFieldPackageToMinimalFailureCommonNeighborGeometryFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.CommonNeighborFieldPackage.{u} C hmin) :
    MinimalFailureGeometryClosureW11.CommonNeighborGeometryFields.{u}
      C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

@[simp]
theorem commonNeighborFieldPackage_e22e23_source
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.CommonNeighborFieldPackage.{u} C hmin) :
    (commonNeighborFieldPackageToGeometryE22E23PredicateFields
      R).localPredicates.source = R.source :=
  rfl

@[simp]
theorem commonNeighborFieldPackage_sourceGeometry_source
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BrokenLatticeIntegratedW11.CommonNeighborFieldPackage.{u} C hmin) :
    (commonNeighborFieldPackageToMinimalFailureCommonNeighborGeometryFields
      R).source = R.source :=
  rfl

/-! ## Uniform matrix projections -/

def directFieldMatrixToTargetDirectGeometryPredicateMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    TargetClosureMatrixW11.DirectGeometryPredicateMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectGeometryPredicateFields

def directFieldMatrixToGeometryE22E23PredicateMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    TargetClosureMatrixW11.GeometryE22E23PredicateMatrix.{u} where
  row := fun C hmin =>
    directFieldPackageToGeometryE22E23PredicateFields (M.row C hmin)

def directFieldMatrixToMinimalFailureDirectGeometryMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    MinimalFailureGeometryClosureW11.DirectGeometryMatrix.{u} where
  row := fun C hmin =>
    directFieldPackageToMinimalFailureDirectGeometryFields (M.row C hmin)

def k23FieldMatrixToTargetK23GeometryPredicateMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    TargetClosureMatrixW11.K23GeometryPredicateMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPredicateFields

def k23FieldMatrixToGeometryE22E23PredicateMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    TargetClosureMatrixW11.GeometryE22E23PredicateMatrix.{u} where
  row := fun C hmin =>
    k23FieldPackageToGeometryE22E23PredicateFields (M.row C hmin)

def k23FieldMatrixToMinimalFailureK23GeometryMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    MinimalFailureGeometryClosureW11.K23GeometryMatrix.{u} where
  row := fun C hmin =>
    k23FieldPackageToMinimalFailureK23GeometryFields (M.row C hmin)

def k23FieldMatrixToTargetK23ObstructionRows
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    K23CommonNeighborW11.K23ObstructionW10RowFamily.{u} :=
  M.toK23ObstructionW10RowFamily

def commonNeighborFieldMatrixToTargetCommonNeighborGeometryPredicateMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    TargetClosureMatrixW11.CommonNeighborGeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toCommonNeighborGeometryPredicateFields

def commonNeighborFieldMatrixToGeometryE22E23PredicateMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    TargetClosureMatrixW11.GeometryE22E23PredicateMatrix.{u} where
  row := fun C hmin =>
    commonNeighborFieldPackageToGeometryE22E23PredicateFields
      (M.row C hmin)

def commonNeighborFieldMatrixToMinimalFailureCommonNeighborGeometryMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    MinimalFailureGeometryClosureW11.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin =>
    commonNeighborFieldPackageToMinimalFailureCommonNeighborGeometryFields
      (M.row C hmin)

def commonNeighborFieldMatrixToTargetCommonNeighborObstructionRows
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u} :=
  M.toCommonNeighborObstructionW10RowFamily

/-! ## Target-closure rows for source-facing broken-lattice matrices -/

def directFieldMatrixViaSourceGeometryRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :=
  pullbackTargetClosureRow
    (targetClosureRowOfW11Row
      MinimalFailureGeometryClosureW11.directGeometryTargetProjectionRow)
    directFieldMatrixToMinimalFailureDirectGeometryMatrix

def directFieldMatrixViaE22E23Row :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :=
  pullbackTargetClosureRow
    TargetClosureMatrixW11.matrix.geometryE22E23Predicates
    directFieldMatrixToGeometryE22E23PredicateMatrix

def directFieldMatrixViaBrokenLatticeRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :=
  pullbackTargetClosureRow
    TargetClosureMatrixW11.matrix.directGeometryPredicates
    directFieldMatrixToTargetDirectGeometryPredicateMatrix

def k23FieldMatrixViaSourceGeometryRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :=
  pullbackTargetClosureRow
    (targetClosureRowOfW11Row
      MinimalFailureGeometryClosureW11.k23GeometryTargetProjectionRow)
    k23FieldMatrixToMinimalFailureK23GeometryMatrix

def k23FieldMatrixViaE22E23Row :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :=
  pullbackTargetClosureRow
    TargetClosureMatrixW11.matrix.geometryE22E23Predicates
    k23FieldMatrixToGeometryE22E23PredicateMatrix

def k23FieldMatrixViaBrokenLatticeRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :=
  pullbackTargetClosureRow
    TargetClosureMatrixW11.matrix.k23GeometryPredicates
    k23FieldMatrixToTargetK23GeometryPredicateMatrix

def k23FieldMatrixViaObstructionRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :=
  pullbackTargetClosureRow
    TargetClosureMatrixW11.matrix.k23W10Rows
    k23FieldMatrixToTargetK23ObstructionRows

def commonNeighborFieldMatrixViaSourceGeometryRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :=
  pullbackTargetClosureRow
    (targetClosureRowOfW11Row
      MinimalFailureGeometryClosureW11.commonNeighborGeometryTargetProjectionRow)
    commonNeighborFieldMatrixToMinimalFailureCommonNeighborGeometryMatrix

def commonNeighborFieldMatrixViaE22E23Row :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :=
  pullbackTargetClosureRow
    TargetClosureMatrixW11.matrix.geometryE22E23Predicates
    commonNeighborFieldMatrixToGeometryE22E23PredicateMatrix

def commonNeighborFieldMatrixViaBrokenLatticeRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :=
  pullbackTargetClosureRow
    TargetClosureMatrixW11.matrix.commonNeighborGeometryPredicates
    commonNeighborFieldMatrixToTargetCommonNeighborGeometryPredicateMatrix

def commonNeighborFieldMatrixViaObstructionRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :=
  pullbackTargetClosureRow
    TargetClosureMatrixW11.matrix.commonNeighborW10Rows
    commonNeighborFieldMatrixToTargetCommonNeighborObstructionRows

/-! ## Integrated target-facing ledger -/

/-- Target-facing routes for W11 direct broken-lattice source matrices. -/
structure DirectTargetRows : Type (u + 1) where
  sourceGeometry :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u})
  e22e23 :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u})
  brokenLattice :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u})

/-- Target-facing routes for W11 K23 broken-lattice source matrices. -/
structure K23TargetRows : Type (u + 1) where
  sourceGeometry :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u})
  e22e23 :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u})
  brokenLattice :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u})
  obstruction :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.K23FieldMatrix.{u})

/-- Target-facing routes for W11 common-neighbor broken-lattice matrices. -/
structure CommonNeighborTargetRows : Type (u + 1) where
  sourceGeometry :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u})
  e22e23 :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u})
  brokenLattice :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u})
  obstruction :
    TargetClosureMatrixW11.TargetProjectionRow
      (BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u})

def directTargetRows : DirectTargetRows.{u} where
  sourceGeometry := directFieldMatrixViaSourceGeometryRow
  e22e23 := directFieldMatrixViaE22E23Row
  brokenLattice := directFieldMatrixViaBrokenLatticeRow

def k23TargetRows : K23TargetRows.{u} where
  sourceGeometry := k23FieldMatrixViaSourceGeometryRow
  e22e23 := k23FieldMatrixViaE22E23Row
  brokenLattice := k23FieldMatrixViaBrokenLatticeRow
  obstruction := k23FieldMatrixViaObstructionRow

def commonNeighborTargetRows : CommonNeighborTargetRows.{u} where
  sourceGeometry := commonNeighborFieldMatrixViaSourceGeometryRow
  e22e23 := commonNeighborFieldMatrixViaE22E23Row
  brokenLattice := commonNeighborFieldMatrixViaBrokenLatticeRow
  obstruction := commonNeighborFieldMatrixViaObstructionRow

/-- Integrated W11 broken-lattice target matrix.

The stored route rows are checked projections only.  They do not supply the
source matrices needed by the public target projections below. -/
structure Matrix : Type (u + 1) where
  targetClosure : TargetClosureMatrixW11.Matrix.{u}
  targetIntegrated : TargetIntegratedMatrixW11.Matrix.{u}
  brokenLatticeClosure : BrokenLatticeClosureW11.Matrix.{u}
  brokenLatticeIntegrated : BrokenLatticeIntegratedW11.Matrix.{u}
  minimalFailureGeometry : MinimalFailureGeometryClosureW11.Matrix.{u}
  directRows : DirectTargetRows.{u}
  k23Rows : K23TargetRows.{u}
  commonNeighborRows : CommonNeighborTargetRows.{u}

/-- The checked target-facing broken-lattice ledger. -/
def matrix : Matrix.{u} where
  targetClosure := TargetClosureMatrixW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  brokenLatticeClosure := BrokenLatticeClosureW11.matrix
  brokenLatticeIntegrated := BrokenLatticeIntegratedW11.matrix
  minimalFailureGeometry := MinimalFailureGeometryClosureW11.matrix
  directRows := directTargetRows
  k23Rows := k23TargetRows
  commonNeighborRows := commonNeighborTargetRows

/-! ## Public source-matrix projections -/

theorem no_minimalClearedFailure_of_directFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.directRows.brokenLattice.noMinimal M

theorem pipelineCleared_of_directFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    PipelineCleared :=
  matrix.directRows.brokenLattice.pipeline M

theorem targetClosure_of_directFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  matrix.directRows.brokenLattice.target M

theorem targetClosure_of_directFieldMatrix_via_e22e23
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  matrix.directRows.e22e23.target M

theorem targetClosure_of_directFieldMatrix_via_sourceGeometry
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  matrix.directRows.sourceGeometry.target M

theorem no_minimalClearedFailure_of_k23FieldMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.k23Rows.brokenLattice.noMinimal M

theorem pipelineCleared_of_k23FieldMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    PipelineCleared :=
  matrix.k23Rows.brokenLattice.pipeline M

theorem targetClosure_of_k23FieldMatrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  matrix.k23Rows.brokenLattice.target M

theorem targetClosure_of_k23FieldMatrix_via_e22e23
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  matrix.k23Rows.e22e23.target M

theorem targetClosure_of_k23FieldMatrix_via_sourceGeometry
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  matrix.k23Rows.sourceGeometry.target M

theorem targetClosure_of_k23FieldMatrix_via_obstruction
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  matrix.k23Rows.obstruction.target M

theorem no_minimalClearedFailure_of_commonNeighborFieldMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.commonNeighborRows.brokenLattice.noMinimal M

theorem pipelineCleared_of_commonNeighborFieldMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    PipelineCleared :=
  matrix.commonNeighborRows.brokenLattice.pipeline M

theorem targetClosure_of_commonNeighborFieldMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.commonNeighborRows.brokenLattice.target M

theorem targetClosure_of_commonNeighborFieldMatrix_via_e22e23
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.commonNeighborRows.e22e23.target M

theorem targetClosure_of_commonNeighborFieldMatrix_via_sourceGeometry
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.commonNeighborRows.sourceGeometry.target M

theorem targetClosure_of_commonNeighborFieldMatrix_via_obstruction
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.commonNeighborRows.obstruction.target M

end

end BrokenLatticeTargetIntegratedW11
end Swanepoel
end ErdosProblems1066
