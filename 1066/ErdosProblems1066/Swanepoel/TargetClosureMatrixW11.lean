import ErdosProblems1066.Swanepoel.SwanepoelTargetClosureW11
import ErdosProblems1066.Swanepoel.WindowNoEarlyRowsW11
import ErdosProblems1066.Swanepoel.K23CommonNeighborW11
import ErdosProblems1066.Swanepoel.BrokenLatticeFieldsW11
import ErdosProblems1066.Swanepoel.SwanepoelW10ClosureMatrix

set_option autoImplicit false

/-!
# W11 Swanepoel target closure matrix

This module collects the target-facing W11 routes that are checked in the
current Swanepoel stack.  Every target row below is conditional on an explicit
input family; source geometry, boundary labels, local predicate facts,
containment, no-early, K23, common-neighbor, and analytic fields remain visible
as fields of those input families.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TargetClosureMatrixW11

universe u v

noncomputable section

abbrev Target : Prop :=
  SwanepoelTargetClosureW11.Target

abbrev MinimalFailureExclusion : Prop :=
  SwanepoelTargetClosureW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SwanepoelTargetClosureW11.PipelineCleared

/-! ## Generic target rows -/

/-- A conditional W11 route to the Swanepoel target. -/
structure TargetProjectionRow (alpha : Sort u) : Sort (max 1 u) where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace TargetProjectionRow

/-- Build a target row from a minimal-failure eliminator and target theorem. -/
def ofNoMinimalAndTarget
    {alpha : Sort u}
    (noMinimal : alpha -> MinimalFailureExclusion)
    (target : alpha -> Target) :
    TargetProjectionRow alpha where
  noMinimal := noMinimal
  pipeline := fun a =>
    SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
      (noMinimal a)
  target := target

/-- Build a W11 target row from one of the checked W10 projection rows. -/
def ofW10ProjectionRow
    {alpha : Type v}
    (R : SwanepoelW10ClosureMatrix.ProjectionRow alpha) :
    TargetProjectionRow alpha where
  noMinimal := R.noMinimal
  pipeline := fun a =>
    SwanepoelTargetClosureW11.pipelineCleared_of_projectionRow R a
  target := fun a =>
    SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_projectionRow
      R a

end TargetProjectionRow

/-! ## W10 target rows retained at W11 -/

def minimalFailureDirectW10Row :
    TargetProjectionRow
      (SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix.{u}) :=
  TargetProjectionRow.ofW10ProjectionRow
    (SwanepoelW10ClosureMatrix.minimalFailureDirectW10MatrixRow :
      SwanepoelW10ClosureMatrix.ProjectionRow
        (SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix.{u}))

def directGeometryW10Row :
    TargetProjectionRow
      (SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u}) :=
  TargetProjectionRow.ofW10ProjectionRow
    (SwanepoelW10ClosureMatrix.directGeometryMatrixRow :
      SwanepoelW10ClosureMatrix.ProjectionRow
        (SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u}))

def k23GeometryW10Row :
    TargetProjectionRow
      (SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u}) :=
  TargetProjectionRow.ofW10ProjectionRow
    (SwanepoelW10ClosureMatrix.k23GeometryMatrixRow :
      SwanepoelW10ClosureMatrix.ProjectionRow
        (SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u}))

def commonNeighborGeometryW10Row :
    TargetProjectionRow
      (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u}) :=
  TargetProjectionRow.ofW10ProjectionRow
    (SwanepoelW10ClosureMatrix.commonNeighborGeometryMatrixRow :
      SwanepoelW10ClosureMatrix.ProjectionRow
        (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u}))

/-! ## Window and no-early W11 rows -/

def noEarlyMatrixRow :
    TargetProjectionRow (WindowNoEarlyRowsW11.NoEarlyMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    WindowNoEarlyRowsW11.NoEarlyMatrix.no_minimalClearedFailure
    WindowNoEarlyRowsW11.NoEarlyMatrix.targetLowerBoundEightThirtyOne

def noStartMatrixRow :
    TargetProjectionRow (WindowNoEarlyRowsW11.NoStartMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    WindowNoEarlyRowsW11.NoStartMatrix.no_minimalClearedFailure
    WindowNoEarlyRowsW11.NoStartMatrix.targetLowerBoundEightThirtyOne

/-! ## K23 and common-neighbor W11 source rows -/

/-- Forget uniform W11 K23 obstruction rows to the checked W10 K23 geometry
matrix. -/
def k23RowsToW10K23GeometryMatrix
    (H : K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (H.row C hmin).toK23GeometryPackage

/-- Forget uniform W11 common-neighbor rows to the checked W10
common-neighbor geometry matrix. -/
def commonNeighborRowsToW10CommonNeighborGeometryMatrix
    (H : K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (H.row C hmin).toCommonNeighborGeometryPackage

theorem targetLowerBoundEightThirtyOne_of_k23W10Rows
    (H : K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    (k23RowsToW10K23GeometryMatrix H)

theorem targetLowerBoundEightThirtyOne_of_commonNeighborW10Rows
    (H : K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    (commonNeighborRowsToW10CommonNeighborGeometryMatrix H)

def k23W10RowsRow :
    TargetProjectionRow
      (K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    K23CommonNeighborW11.no_minimalClearedFailure_of_k23W10Rows
    targetLowerBoundEightThirtyOne_of_k23W10Rows

def commonNeighborW10RowsRow :
    TargetProjectionRow
      (K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    K23CommonNeighborW11.no_minimalClearedFailure_of_commonNeighborW10Rows
    targetLowerBoundEightThirtyOne_of_commonNeighborW10Rows

/-! ## Broken-lattice W11 field families -/

/-- Uniform analytic E22/E23 plus late-triples rows for every minimal
failure. -/
structure E22E23LocalPredicateMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BrokenLatticeFieldsW11.E22E23LocalPredicateFields C hmin

namespace E22E23LocalPredicateMatrix

theorem no_minimalClearedFailure
    (M : E22E23LocalPredicateMatrix) :
    MinimalFailureExclusion := by
  intro n C hmin
  exact (M.row C hmin).contradiction

theorem pipelineCleared
    (M : E22E23LocalPredicateMatrix) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (M : E22E23LocalPredicateMatrix) :
    Target :=
  SwanepoelTargetFacadeW10.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

end E22E23LocalPredicateMatrix

/-- Uniform geometry-selected E22/E23 plus late-triples rows for every
minimal failure. -/
structure GeometryE22E23PredicateMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BrokenLatticeFieldsW11.GeometryE22E23PredicateFields.{u} C hmin

namespace GeometryE22E23PredicateMatrix

theorem no_minimalClearedFailure
    (M : GeometryE22E23PredicateMatrix.{u}) :
    MinimalFailureExclusion := by
  intro n C hmin
  exact (M.row C hmin).contradiction

theorem pipelineCleared
    (M : GeometryE22E23PredicateMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (M : GeometryE22E23PredicateMatrix.{u}) :
    Target :=
  SwanepoelTargetFacadeW10.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

end GeometryE22E23PredicateMatrix

/-- Uniform direct W11 geometry rows for every minimal failure. -/
structure DirectGeometryPredicateMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BrokenLatticeFieldsW11.DirectGeometryPredicateFields.{u} C hmin

namespace DirectGeometryPredicateMatrix

/-- Forget W11 direct geometry rows to the checked W10 direct geometry
matrix. -/
def toW10DirectGeometryMatrix
    (M : DirectGeometryPredicateMatrix.{u}) :
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectGeometryPackage

theorem no_minimalClearedFailure
    (M : DirectGeometryPredicateMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toW10DirectGeometryMatrix.no_minimalClearedFailure

theorem pipelineCleared
    (M : DirectGeometryPredicateMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (M : DirectGeometryPredicateMatrix.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    M.toW10DirectGeometryMatrix

end DirectGeometryPredicateMatrix

/-- Uniform K23-derived W11 geometry rows for every minimal failure. -/
structure K23GeometryPredicateMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BrokenLatticeFieldsW11.K23GeometryPredicateFields.{u} C hmin

namespace K23GeometryPredicateMatrix

/-- Forget W11 K23 geometry rows to the checked W10 K23 geometry matrix. -/
def toW10K23GeometryMatrix
    (M : K23GeometryPredicateMatrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPackage

theorem no_minimalClearedFailure
    (M : K23GeometryPredicateMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toW10K23GeometryMatrix.no_minimalClearedFailure

theorem pipelineCleared
    (M : K23GeometryPredicateMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (M : K23GeometryPredicateMatrix.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    M.toW10K23GeometryMatrix

end K23GeometryPredicateMatrix

/-- Uniform common-neighbor-derived W11 geometry rows for every minimal
failure. -/
structure CommonNeighborGeometryPredicateMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BrokenLatticeFieldsW11.CommonNeighborGeometryPredicateFields.{u}
          C hmin

namespace CommonNeighborGeometryPredicateMatrix

/-- Forget W11 common-neighbor geometry rows to the checked W10
common-neighbor geometry matrix. -/
def toW10CommonNeighborGeometryMatrix
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborGeometryPackage

theorem no_minimalClearedFailure
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toW10CommonNeighborGeometryMatrix.no_minimalClearedFailure

theorem pipelineCleared
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    M.toW10CommonNeighborGeometryMatrix

end CommonNeighborGeometryPredicateMatrix

/-! ## Broken-lattice target rows -/

def e22e23LocalPredicateRow :
    TargetProjectionRow E22E23LocalPredicateMatrix :=
  TargetProjectionRow.ofNoMinimalAndTarget
    E22E23LocalPredicateMatrix.no_minimalClearedFailure
    E22E23LocalPredicateMatrix.targetLowerBoundEightThirtyOne

def geometryE22E23PredicateRow :
    TargetProjectionRow (GeometryE22E23PredicateMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    GeometryE22E23PredicateMatrix.no_minimalClearedFailure
    GeometryE22E23PredicateMatrix.targetLowerBoundEightThirtyOne

def directGeometryPredicateRow :
    TargetProjectionRow (DirectGeometryPredicateMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    DirectGeometryPredicateMatrix.no_minimalClearedFailure
    DirectGeometryPredicateMatrix.targetLowerBoundEightThirtyOne

def k23GeometryPredicateRow :
    TargetProjectionRow (K23GeometryPredicateMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    K23GeometryPredicateMatrix.no_minimalClearedFailure
    K23GeometryPredicateMatrix.targetLowerBoundEightThirtyOne

def commonNeighborGeometryPredicateRow :
    TargetProjectionRow (CommonNeighborGeometryPredicateMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    CommonNeighborGeometryPredicateMatrix.no_minimalClearedFailure
    CommonNeighborGeometryPredicateMatrix.targetLowerBoundEightThirtyOne

/-! ## Checked W11 target closure matrix -/

/-- Consolidated W11 target closure matrix of conditional routes. -/
structure Matrix : Type (u + 1) where
  w10ClosureMatrix : SwanepoelW10ClosureMatrix.Matrix.{u}
  w11TargetClosure : SwanepoelTargetClosureW11.Matrix.{u}
  commonNeighborGeometryW10 :
    TargetProjectionRow
      (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u})
  k23GeometryW10 :
    TargetProjectionRow
      (SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u})
  directGeometryW10 :
    TargetProjectionRow
      (SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u})
  minimalFailureDirectW10 :
    TargetProjectionRow
      (SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix.{u})
  commonNeighborW10Rows :
    TargetProjectionRow
      (K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u})
  k23W10Rows :
    TargetProjectionRow
      (K23CommonNeighborW11.K23ObstructionW10RowFamily.{u})
  noEarlyRows :
    TargetProjectionRow (WindowNoEarlyRowsW11.NoEarlyMatrix.{u})
  noStartRows :
    TargetProjectionRow (WindowNoEarlyRowsW11.NoStartMatrix.{u})
  e22e23LocalPredicates :
    TargetProjectionRow E22E23LocalPredicateMatrix
  geometryE22E23Predicates :
    TargetProjectionRow (GeometryE22E23PredicateMatrix.{u})
  directGeometryPredicates :
    TargetProjectionRow (DirectGeometryPredicateMatrix.{u})
  k23GeometryPredicates :
    TargetProjectionRow (K23GeometryPredicateMatrix.{u})
  commonNeighborGeometryPredicates :
    TargetProjectionRow (CommonNeighborGeometryPredicateMatrix.{u})

/-- The checked W11 target closure matrix. -/
def matrix : Matrix.{u} where
  w10ClosureMatrix := SwanepoelW10ClosureMatrix.matrix
  w11TargetClosure := SwanepoelTargetClosureW11.matrix
  commonNeighborGeometryW10 := commonNeighborGeometryW10Row
  k23GeometryW10 := k23GeometryW10Row
  directGeometryW10 := directGeometryW10Row
  minimalFailureDirectW10 := minimalFailureDirectW10Row
  commonNeighborW10Rows := commonNeighborW10RowsRow
  k23W10Rows := k23W10RowsRow
  noEarlyRows := noEarlyMatrixRow
  noStartRows := noStartMatrixRow
  e22e23LocalPredicates := e22e23LocalPredicateRow
  geometryE22E23Predicates := geometryE22E23PredicateRow
  directGeometryPredicates := directGeometryPredicateRow
  k23GeometryPredicates := k23GeometryPredicateRow
  commonNeighborGeometryPredicates := commonNeighborGeometryPredicateRow

/-! ## Public conditional projections -/

theorem targetLowerBoundEightThirtyOne_of_noEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u}) :
    Target :=
  WindowNoEarlyRowsW11.NoEarlyMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_noStartMatrix
    (M : WindowNoEarlyRowsW11.NoStartMatrix.{u}) :
    Target :=
  WindowNoEarlyRowsW11.NoStartMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_e22e23LocalPredicateMatrix
    (M : E22E23LocalPredicateMatrix) :
    Target :=
  E22E23LocalPredicateMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_geometryE22E23PredicateMatrix
    (M : GeometryE22E23PredicateMatrix.{u}) :
    Target :=
  GeometryE22E23PredicateMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_directGeometryPredicateMatrix
    (M : DirectGeometryPredicateMatrix.{u}) :
    Target :=
  DirectGeometryPredicateMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_k23GeometryPredicateMatrix
    (M : K23GeometryPredicateMatrix.{u}) :
    Target :=
  K23GeometryPredicateMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborGeometryPredicateMatrix
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    Target :=
  CommonNeighborGeometryPredicateMatrix.targetLowerBoundEightThirtyOne M

theorem no_minimalClearedFailure_of_commonNeighborW10Rows
    (M : K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}) :
    MinimalFailureExclusion :=
  K23CommonNeighborW11.no_minimalClearedFailure_of_commonNeighborW10Rows M

theorem no_minimalClearedFailure_of_k23W10Rows
    (M : K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}) :
    MinimalFailureExclusion :=
  K23CommonNeighborW11.no_minimalClearedFailure_of_k23W10Rows M

theorem no_minimalClearedFailure_of_noEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u}) :
    MinimalFailureExclusion :=
  WindowNoEarlyRowsW11.NoEarlyMatrix.no_minimalClearedFailure M

theorem no_minimalClearedFailure_of_noStartMatrix
    (M : WindowNoEarlyRowsW11.NoStartMatrix.{u}) :
    MinimalFailureExclusion :=
  WindowNoEarlyRowsW11.NoStartMatrix.no_minimalClearedFailure M

end

end TargetClosureMatrixW11
end Swanepoel
end ErdosProblems1066
