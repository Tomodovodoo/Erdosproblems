import ErdosProblems1066.Swanepoel.SwanepoelTargetFacadeW10
import ErdosProblems1066.Swanepoel.SwanepoelW10ClosureMatrix

set_option autoImplicit false

/-!
# Swanepoel W11 target-closure facade

This module is a narrow target facade over the strongest checked Swanepoel
W10 closure rows that are available to W11.  It does not add a public
`KnownBounds` theorem and it does not assert the `8 / 31` target without an
explicit input package.

The common-neighbor geometry row is listed first because it is the strongest
current W10 route: it forgets to the K23 geometry row, then to the direct
geometry row, and finally to the W9 target consumer.  The K23, direct geometry,
and W10 direct minimal-failure rows are kept as honest fallback projections.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelTargetClosureW11

universe u

noncomputable section

abbrev Target : Prop :=
  SwanepoelTargetFacadeW10.Target

abbrev MinimalFailureExclusion : Prop :=
  SwanepoelTargetFacadeW10.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SwanepoelTargetFacadeW10.PipelineCleared

abbrev W10ProjectionRow (alpha : Type u) :=
  SwanepoelW10ClosureMatrix.ProjectionRow alpha

/-! ## Generic projection routing -/

/-- Convert a checked W10 projection row and a real input package into the W10
target-facade matrix. -/
def toW10TargetFacadeMatrix
    {alpha : Type u} (R : W10ProjectionRow alpha) (a : alpha) :
    SwanepoelTargetFacadeW10.Matrix where
  excludesMinimalFailures := R.noMinimal a

/-- A checked W10 projection row rules out all minimal cleared failures once
its explicit input package is supplied. -/
theorem no_minimalClearedFailure_of_projectionRow
    {alpha : Type u} (R : W10ProjectionRow alpha) (a : alpha) :
    MinimalFailureExclusion :=
  (toW10TargetFacadeMatrix R a).no_minimalClearedFailure

/-- A checked W10 projection row supplies the cleared pipeline predicate once
its explicit input package is supplied. -/
theorem pipelineCleared_of_projectionRow
    {alpha : Type u} (R : W10ProjectionRow alpha) (a : alpha) :
    PipelineCleared :=
  (toW10TargetFacadeMatrix R a).pipelineCleared

/-- A checked W10 projection row reaches the Swanepoel target once its
explicit input package is supplied. -/
theorem targetLowerBoundEightThirtyOne_of_projectionRow
    {alpha : Type u} (R : W10ProjectionRow alpha) (a : alpha) :
    Target :=
  (toW10TargetFacadeMatrix R a).targetLowerBoundEightThirtyOne

/-! ## W11 target-closure matrix -/

/-- W11 target facade over the strongest checked W10 closure rows.

Each field is a route from an explicit input package to the target.  The record
stores projection routes only; it is not itself an input package for the final
target. -/
structure Matrix where
  commonNeighborGeometry :
    W10ProjectionRow
      (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u})
  k23Geometry :
    W10ProjectionRow
      (SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u})
  directGeometry :
    W10ProjectionRow
      (SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u})
  minimalFailureDirectW10 :
    W10ProjectionRow
      (SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix.{u})

/-- The checked W11 target-closure facade. -/
def matrix : Matrix where
  commonNeighborGeometry :=
    SwanepoelW10ClosureMatrix.commonNeighborGeometryMatrixRow
  k23Geometry :=
    SwanepoelW10ClosureMatrix.k23GeometryMatrixRow
  directGeometry :=
    SwanepoelW10ClosureMatrix.directGeometryMatrixRow
  minimalFailureDirectW10 :=
    SwanepoelW10ClosureMatrix.minimalFailureDirectW10MatrixRow

/-! ## Strong W10 route projections -/

/-- Target projection from the common-neighbor W10 geometry matrix. -/
theorem targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    (M : SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_projectionRow
    (SwanepoelW10ClosureMatrix.commonNeighborGeometryMatrixRow :
      W10ProjectionRow
        (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u})) M

/-- Minimal-failure exclusion from the common-neighbor W10 geometry matrix. -/
theorem no_minimalClearedFailure_of_commonNeighborGeometryMatrix
    (M : SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_projectionRow
    (SwanepoelW10ClosureMatrix.commonNeighborGeometryMatrixRow :
      W10ProjectionRow
        (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u})) M

/-- Pipeline-cleared projection from the common-neighbor W10 geometry matrix.
-/
theorem pipelineCleared_of_commonNeighborGeometryMatrix
    (M : SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u}) :
    PipelineCleared :=
  pipelineCleared_of_projectionRow
    (SwanepoelW10ClosureMatrix.commonNeighborGeometryMatrixRow :
      W10ProjectionRow
        (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u})) M

/-- Target projection from the K23 W10 geometry matrix. -/
theorem targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    (M : SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_projectionRow
    (SwanepoelW10ClosureMatrix.k23GeometryMatrixRow :
      W10ProjectionRow
        (SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u})) M

/-- Target projection from the direct W10 geometry matrix. -/
theorem targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    (M : SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_projectionRow
    (SwanepoelW10ClosureMatrix.directGeometryMatrixRow :
      W10ProjectionRow
        (SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u})) M

/-- Target projection from the existing W10 direct minimal-failure matrix. -/
theorem targetLowerBoundEightThirtyOne_of_minimalFailureDirectW10Matrix
    (M : SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_projectionRow
    (SwanepoelW10ClosureMatrix.minimalFailureDirectW10MatrixRow :
      W10ProjectionRow
        (SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix.{u})) M

end

end SwanepoelTargetClosureW11
end Swanepoel
end ErdosProblems1066
