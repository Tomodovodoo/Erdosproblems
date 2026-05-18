import ErdosProblems1066.Swanepoel.FinalConditional
import ErdosProblems1066.Swanepoel.SwanepoelTargetFacadeW10
import ErdosProblems1066.Swanepoel.SwanepoelW10ClosureMatrix

set_option autoImplicit false

/-!
# Swanepoel W11 closure matrix

This file is the W11 consolidation ledger for the Swanepoel route.  No
separate W11 row modules are present in this checkout, so the ledger records
the checked W10-to-W11 routes that are available now.

Each target-producing row keeps the input package visible and records the
same route shape:

* minimal-cleared-failure exclusion;
* the cleared pipeline predicate;
* the public Swanepoel `8 / 31` target.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW11ClosureMatrix

universe u

noncomputable section

abbrev Target : Prop :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

abbrev MinimalFailureExclusion : Prop :=
  SwanepoelTargetFacadeW10.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SwanepoelTargetFacadeW10.PipelineCleared

abbrev W8Matrix :=
  SwanepoelW8ClosureMatrix.Matrix

abbrev W9DirectMatrix :=
  SwanepoelRemainingObligationsW9.DirectMatrix

abbrev W9K23Matrix :=
  SwanepoelRemainingObligationsW9.K23Matrix

abbrev W10TargetFacadeMatrix :=
  SwanepoelTargetFacadeW10.Matrix

abbrev W10DirectComponentMatrix :=
  SwanepoelW10ClosureMatrix.DirectComponentMatrix

abbrev W10K23ComponentMatrix :=
  SwanepoelW10ClosureMatrix.K23ComponentMatrix

abbrev W10MinimalFailureDirectMatrix :=
  SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix

abbrev W10DirectGeometryMatrix :=
  SwanepoelW10ClosureMatrix.DirectGeometryMatrix

abbrev W10K23GeometryMatrix :=
  SwanepoelW10ClosureMatrix.K23GeometryMatrix

abbrev W10CommonNeighborGeometryMatrix :=
  SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix

abbrev FinalSeparatedConstructionEliminator :=
  FinalConditional.MinimalFailureM8SeparatedConstructionEliminator

abbrev FinalConstructionInterfaceEliminator :=
  FinalConditional.MinimalFailureM8ConstructionInterfaceEliminator

abbrev FinalE22E23NoEarlyEliminator :=
  FinalConditional.MinimalFailureM8E22E23NoEarlyConstructionEliminator

abbrev FinalWindowNoEarlyEliminator :=
  FinalConditional.MinimalFailureM8WindowNoEarlyConstructionEliminator

abbrev FinalTurnWindowNoEarlyEliminator :=
  FinalConditional.MinimalFailureM8TurnWindowNoEarlyEliminator

/-- A W11 target route with all checked projections kept visible. -/
structure TargetProjectionRow (alpha : Sort u) : Sort (max 1 u) where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace TargetProjectionRow

/-- Build a W11 route from the checked minimal-failure and target projections. -/
def ofNoMinimalAndTarget
    {alpha : Sort u}
    (noMinimal : alpha -> MinimalFailureExclusion)
    (target : alpha -> Target) :
    TargetProjectionRow alpha where
  noMinimal := noMinimal
  pipeline := fun x =>
    SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
      (noMinimal x)
  target := target

end TargetProjectionRow

/-! ## Checked projection rows -/

/-- Retained W8 route, passed through the W10 target facade. -/
def w8MatrixRow :
    TargetProjectionRow (W8Matrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    SwanepoelTargetFacadeW10.no_minimalClearedFailure_of_w8Matrix
    SwanepoelW10ClosureMatrix.targetLowerBoundEightThirtyOne_of_w8Matrix

/-- W9 direct route, passed through the W10 target facade. -/
def w9DirectMatrixRow :
    TargetProjectionRow (W9DirectMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    SwanepoelTargetFacadeW10.no_minimalClearedFailure_of_w9DirectMatrix
    SwanepoelW10ClosureMatrix.targetLowerBoundEightThirtyOne_of_directMatrix

/-- W9 K23 route, passed through the W10 target facade. -/
def w9K23MatrixRow :
    TargetProjectionRow (W9K23Matrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    SwanepoelTargetFacadeW10.no_minimalClearedFailure_of_w9K23Matrix
    SwanepoelW10ClosureMatrix.targetLowerBoundEightThirtyOne_of_k23Matrix

/-- W10 target-facade route. -/
def w10TargetFacadeMatrixRow :
    TargetProjectionRow W10TargetFacadeMatrix :=
  { noMinimal := SwanepoelTargetFacadeW10.Matrix.no_minimalClearedFailure
    pipeline := SwanepoelTargetFacadeW10.Matrix.pipelineCleared
    target := SwanepoelTargetFacadeW10.Matrix.targetLowerBoundEightThirtyOne }

/-- W10 direct-component route through the W9 direct matrix. -/
def w10DirectComponentMatrixRow :
    TargetProjectionRow (W10DirectComponentMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    SwanepoelW10ClosureMatrix.DirectComponentMatrix.no_minimalClearedFailure
    SwanepoelW10ClosureMatrix.DirectComponentMatrix.targetLowerBoundEightThirtyOne

/-- W10 K23-component route through the W9 K23 matrix. -/
def w10K23ComponentMatrixRow :
    TargetProjectionRow (W10K23ComponentMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    SwanepoelW10ClosureMatrix.K23ComponentMatrix.no_minimalClearedFailure
    SwanepoelW10ClosureMatrix.K23ComponentMatrix.targetLowerBoundEightThirtyOne

/-- W10 direct minimal-failure matrix route through the W9 direct matrix. -/
def w10MinimalFailureDirectMatrixRow :
    TargetProjectionRow (W10MinimalFailureDirectMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix.no_minimalClearedFailure
    SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix.targetLowerBoundEightThirtyOne

/-- W10 direct-geometry route through the W9 direct matrix. -/
def w10DirectGeometryMatrixRow :
    TargetProjectionRow (W10DirectGeometryMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.no_minimalClearedFailure
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.targetLowerBoundEightThirtyOne

/-- W10 K23-geometry route through the W9 K23 matrix. -/
def w10K23GeometryMatrixRow :
    TargetProjectionRow (W10K23GeometryMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.no_minimalClearedFailure
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.targetLowerBoundEightThirtyOne

/-- W10 common-neighbor geometry route through the W9 K23 matrix. -/
def w10CommonNeighborGeometryMatrixRow :
    TargetProjectionRow (W10CommonNeighborGeometryMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.no_minimalClearedFailure
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.targetLowerBoundEightThirtyOne

/-- Final separated-construction route. -/
def finalSeparatedConstructionEliminatorRow :
    TargetProjectionRow FinalSeparatedConstructionEliminator :=
  TargetProjectionRow.ofNoMinimalAndTarget
    FinalConditional.no_minimalClearedFailure_of_m8SeparatedConstructionEliminator
    FinalConditional.targetLowerBoundEightThirtyOne_of_m8SeparatedConstructionEliminator

/-- Final construction-interface route. -/
def finalConstructionInterfaceEliminatorRow :
    TargetProjectionRow FinalConstructionInterfaceEliminator :=
  TargetProjectionRow.ofNoMinimalAndTarget
    FinalConditional.no_minimalClearedFailure_of_m8ConstructionInterfaceEliminator
    FinalConditional.targetLowerBoundEightThirtyOne_of_m8ConstructionInterfaceEliminator

/-- Final E22/E23 plus no-early route. -/
def finalE22E23NoEarlyEliminatorRow :
    TargetProjectionRow FinalE22E23NoEarlyEliminator :=
  TargetProjectionRow.ofNoMinimalAndTarget
    FinalConditional.no_minimalClearedFailure_of_m8E22E23NoEarlyConstructionEliminator
    FinalConditional.targetLowerBoundEightThirtyOne_of_m8E22E23NoEarlyConstructionEliminator

/-- Final window plus no-early route. -/
def finalWindowNoEarlyEliminatorRow :
    TargetProjectionRow FinalWindowNoEarlyEliminator :=
  TargetProjectionRow.ofNoMinimalAndTarget
    FinalConditional.no_minimalClearedFailure_of_m8WindowNoEarlyConstructionEliminator
    FinalConditional.targetLowerBoundEightThirtyOne_of_m8WindowNoEarlyConstructionEliminator

/-- Final turn/window/no-early route. -/
def finalTurnWindowNoEarlyEliminatorRow :
    TargetProjectionRow FinalTurnWindowNoEarlyEliminator :=
  TargetProjectionRow.ofNoMinimalAndTarget
    FinalConditional.no_minimalClearedFailure_of_turnWindowNoEarlyEliminator
    FinalConditional.targetLowerBoundEightThirtyOne_of_turnWindowNoEarlyEliminator

/-! ## Explicit W10-to-W11 field ledger -/

/-- The route rows still visible in the checked W11 ledger. -/
structure RemainingFieldLedger : Type (u + 1) where
  w8 : TargetProjectionRow (W8Matrix.{u})
  w9Direct : TargetProjectionRow (W9DirectMatrix.{u})
  w9K23 : TargetProjectionRow (W9K23Matrix.{u})
  w10TargetFacade : TargetProjectionRow W10TargetFacadeMatrix
  w10DirectComponents : TargetProjectionRow (W10DirectComponentMatrix.{u})
  w10K23Components : TargetProjectionRow (W10K23ComponentMatrix.{u})
  w10MinimalFailureDirect :
    TargetProjectionRow (W10MinimalFailureDirectMatrix.{u})
  w10DirectGeometry : TargetProjectionRow (W10DirectGeometryMatrix.{u})
  w10K23Geometry : TargetProjectionRow (W10K23GeometryMatrix.{u})
  w10CommonNeighborGeometry :
    TargetProjectionRow (W10CommonNeighborGeometryMatrix.{u})
  finalSeparatedConstruction :
    TargetProjectionRow FinalSeparatedConstructionEliminator
  finalConstructionInterface :
    TargetProjectionRow FinalConstructionInterfaceEliminator
  finalE22E23NoEarly :
    TargetProjectionRow FinalE22E23NoEarlyEliminator
  finalWindowNoEarly :
    TargetProjectionRow FinalWindowNoEarlyEliminator
  finalTurnWindowNoEarly :
    TargetProjectionRow FinalTurnWindowNoEarlyEliminator

/-- The W11 ledger of visible route rows. -/
def remainingFieldLedger : RemainingFieldLedger.{u} where
  w8 := w8MatrixRow
  w9Direct := w9DirectMatrixRow
  w9K23 := w9K23MatrixRow
  w10TargetFacade := w10TargetFacadeMatrixRow
  w10DirectComponents := w10DirectComponentMatrixRow
  w10K23Components := w10K23ComponentMatrixRow
  w10MinimalFailureDirect := w10MinimalFailureDirectMatrixRow
  w10DirectGeometry := w10DirectGeometryMatrixRow
  w10K23Geometry := w10K23GeometryMatrixRow
  w10CommonNeighborGeometry := w10CommonNeighborGeometryMatrixRow
  finalSeparatedConstruction := finalSeparatedConstructionEliminatorRow
  finalConstructionInterface := finalConstructionInterfaceEliminatorRow
  finalE22E23NoEarly := finalE22E23NoEarlyEliminatorRow
  finalWindowNoEarly := finalWindowNoEarlyEliminatorRow
  finalTurnWindowNoEarly := finalTurnWindowNoEarlyEliminatorRow

/-! ## W11 closure matrix -/

/-- Consolidated W11 Swanepoel closure matrix.

Every target-producing entry remains conditional on its visible input package.
-/
structure Matrix : Type (u + 1) where
  ledger : RemainingFieldLedger.{u}
  w10ClosureMatrix : SwanepoelW10ClosureMatrix.Matrix.{u}
  w8 : TargetProjectionRow (W8Matrix.{u})
  w9Direct : TargetProjectionRow (W9DirectMatrix.{u})
  w9K23 : TargetProjectionRow (W9K23Matrix.{u})
  w10TargetFacade : TargetProjectionRow W10TargetFacadeMatrix
  w10DirectComponents : TargetProjectionRow (W10DirectComponentMatrix.{u})
  w10K23Components : TargetProjectionRow (W10K23ComponentMatrix.{u})
  w10MinimalFailureDirect :
    TargetProjectionRow (W10MinimalFailureDirectMatrix.{u})
  w10DirectGeometry : TargetProjectionRow (W10DirectGeometryMatrix.{u})
  w10K23Geometry : TargetProjectionRow (W10K23GeometryMatrix.{u})
  w10CommonNeighborGeometry :
    TargetProjectionRow (W10CommonNeighborGeometryMatrix.{u})
  finalSeparatedConstruction :
    TargetProjectionRow FinalSeparatedConstructionEliminator
  finalConstructionInterface :
    TargetProjectionRow FinalConstructionInterfaceEliminator
  finalE22E23NoEarly :
    TargetProjectionRow FinalE22E23NoEarlyEliminator
  finalWindowNoEarly :
    TargetProjectionRow FinalWindowNoEarlyEliminator
  finalTurnWindowNoEarly :
    TargetProjectionRow FinalTurnWindowNoEarlyEliminator

/-- The checked W11 ledger assembled from currently available routes. -/
def matrix : Matrix.{u} where
  ledger := remainingFieldLedger
  w10ClosureMatrix := SwanepoelW10ClosureMatrix.matrix
  w8 := w8MatrixRow
  w9Direct := w9DirectMatrixRow
  w9K23 := w9K23MatrixRow
  w10TargetFacade := w10TargetFacadeMatrixRow
  w10DirectComponents := w10DirectComponentMatrixRow
  w10K23Components := w10K23ComponentMatrixRow
  w10MinimalFailureDirect := w10MinimalFailureDirectMatrixRow
  w10DirectGeometry := w10DirectGeometryMatrixRow
  w10K23Geometry := w10K23GeometryMatrixRow
  w10CommonNeighborGeometry := w10CommonNeighborGeometryMatrixRow
  finalSeparatedConstruction := finalSeparatedConstructionEliminatorRow
  finalConstructionInterface := finalConstructionInterfaceEliminatorRow
  finalE22E23NoEarly := finalE22E23NoEarlyEliminatorRow
  finalWindowNoEarly := finalWindowNoEarlyEliminatorRow
  finalTurnWindowNoEarly := finalTurnWindowNoEarlyEliminatorRow

/-! ## Public W11 target projections -/

theorem targetLowerBoundEightThirtyOne_of_w8Matrix
    (M : W8Matrix.{u}) :
    Target :=
  SwanepoelW10ClosureMatrix.targetLowerBoundEightThirtyOne_of_w8Matrix M

theorem targetLowerBoundEightThirtyOne_of_w9DirectMatrix
    (M : W9DirectMatrix.{u}) :
    Target :=
  SwanepoelW10ClosureMatrix.targetLowerBoundEightThirtyOne_of_directMatrix M

theorem targetLowerBoundEightThirtyOne_of_w9K23Matrix
    (M : W9K23Matrix.{u}) :
    Target :=
  SwanepoelW10ClosureMatrix.targetLowerBoundEightThirtyOne_of_k23Matrix M

theorem targetLowerBoundEightThirtyOne_of_w10TargetFacadeMatrix
    (M : W10TargetFacadeMatrix) :
    Target :=
  SwanepoelTargetFacadeW10.targetLowerBoundEightThirtyOne_of_matrix M

theorem targetLowerBoundEightThirtyOne_of_w10DirectComponentMatrix
    (M : W10DirectComponentMatrix.{u}) :
    Target :=
  SwanepoelW10ClosureMatrix.DirectComponentMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_w10K23ComponentMatrix
    (M : W10K23ComponentMatrix.{u}) :
    Target :=
  SwanepoelW10ClosureMatrix.K23ComponentMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_w10MinimalFailureDirectMatrix
    (M : W10MinimalFailureDirectMatrix.{u}) :
    Target :=
  SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_w10DirectGeometryMatrix
    (M : W10DirectGeometryMatrix.{u}) :
    Target :=
  SwanepoelW10ClosureMatrix.DirectGeometryMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_w10K23GeometryMatrix
    (M : W10K23GeometryMatrix.{u}) :
    Target :=
  SwanepoelW10ClosureMatrix.K23GeometryMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_w10CommonNeighborGeometryMatrix
    (M : W10CommonNeighborGeometryMatrix.{u}) :
    Target :=
  SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.targetLowerBoundEightThirtyOne M

theorem targetLowerBoundEightThirtyOne_of_finalSeparatedConstructionEliminator
    (h : FinalSeparatedConstructionEliminator) :
    Target :=
  FinalConditional.targetLowerBoundEightThirtyOne_of_m8SeparatedConstructionEliminator h

theorem targetLowerBoundEightThirtyOne_of_finalConstructionInterfaceEliminator
    (h : FinalConstructionInterfaceEliminator) :
    Target :=
  FinalConditional.targetLowerBoundEightThirtyOne_of_m8ConstructionInterfaceEliminator h

theorem targetLowerBoundEightThirtyOne_of_finalE22E23NoEarlyEliminator
    (h : FinalE22E23NoEarlyEliminator) :
    Target :=
  FinalConditional.targetLowerBoundEightThirtyOne_of_m8E22E23NoEarlyConstructionEliminator h

theorem targetLowerBoundEightThirtyOne_of_finalWindowNoEarlyEliminator
    (h : FinalWindowNoEarlyEliminator) :
    Target :=
  FinalConditional.targetLowerBoundEightThirtyOne_of_m8WindowNoEarlyConstructionEliminator h

theorem targetLowerBoundEightThirtyOne_of_finalTurnWindowNoEarlyEliminator
    (h : FinalTurnWindowNoEarlyEliminator) :
    Target :=
  FinalConditional.targetLowerBoundEightThirtyOne_of_turnWindowNoEarlyEliminator h

end

end SwanepoelW11ClosureMatrix
end Swanepoel
end ErdosProblems1066
