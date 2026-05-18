import ErdosProblems1066.Swanepoel.MinimalFailureGeometryMatrixW11
import ErdosProblems1066.Swanepoel.SwanepoelTargetClosureW11
import ErdosProblems1066.Swanepoel.SwanepoelW11ClosureMatrix
import ErdosProblems1066.Swanepoel.BrokenLatticeFieldsW11
import ErdosProblems1066.Swanepoel.K23CommonNeighborW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Minimal-failure geometry closure, W11

This file is a conditional closure ledger over the W11 geometry rows.  It
keeps the source geometry, local-predicate facts, containment data, and the
selected no-early route visible, then projects those explicit row families to
the checked target facade.

Every lower-bound result below takes an explicit matrix or row family.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureGeometryClosureW11

open GeometryRemainingFieldsW10
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev GeometryClosureMatrix :=
  MinimalFailureGeometryMatrixW11.GeometryClosureMatrix

abbrev NarrowClosureInputFamily :=
  MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily

abbrev CheckedClosureInputFamily :=
  MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily

abbrev Target : Prop :=
  SwanepoelTargetClosureW11.Target

abbrev MinimalFailureExclusion : Prop :=
  SwanepoelTargetClosureW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SwanepoelTargetClosureW11.PipelineCleared

abbrev W10ProjectionRow (alpha : Type u) :=
  SwanepoelTargetClosureW11.W10ProjectionRow alpha

abbrev W11TargetProjectionRow (alpha : Sort u) :=
  SwanepoelW11ClosureMatrix.TargetProjectionRow alpha

/-! ## Facade projections for the W11 geometry matrix -/

/-- The W10 target facade obtained from an explicit W11 geometry matrix. -/
def targetFacadeMatrixOfGeometryClosureMatrix
    (M : GeometryClosureMatrix.{u}) :
    SwanepoelTargetFacadeW10.Matrix :=
  SwanepoelTargetClosureW11.toW10TargetFacadeMatrix
    (MinimalFailureGeometryMatrixW11.geometryClosureMatrixRow :
      W10ProjectionRow (GeometryClosureMatrix.{u})) M

/-- Minimal failures are excluded by an explicit W11 geometry matrix. -/
theorem no_minimalClearedFailure_of_geometryClosureMatrix
    (M : GeometryClosureMatrix.{u}) :
    MinimalFailureExclusion :=
  SwanepoelTargetClosureW11.no_minimalClearedFailure_of_projectionRow
    (MinimalFailureGeometryMatrixW11.geometryClosureMatrixRow :
      W10ProjectionRow (GeometryClosureMatrix.{u})) M

/-- The target pipeline is cleared by an explicit W11 geometry matrix. -/
theorem pipelineCleared_of_geometryClosureMatrix
    (M : GeometryClosureMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetClosureW11.pipelineCleared_of_projectionRow
    (MinimalFailureGeometryMatrixW11.geometryClosureMatrixRow :
      W10ProjectionRow (GeometryClosureMatrix.{u})) M

/-- Conditional target projection from an explicit W11 geometry matrix. -/
theorem targetLowerBoundEightThirtyOne_of_geometryClosureMatrix
    (M : GeometryClosureMatrix.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_projectionRow
    (MinimalFailureGeometryMatrixW11.geometryClosureMatrixRow :
      W10ProjectionRow (GeometryClosureMatrix.{u})) M

/-- W11 target-projection row for explicit W11 geometry matrices. -/
def geometryClosureTargetProjectionRow :
    W11TargetProjectionRow (GeometryClosureMatrix.{u}) :=
  SwanepoelW11ClosureMatrix.TargetProjectionRow.ofNoMinimalAndTarget
    no_minimalClearedFailure_of_geometryClosureMatrix
    targetLowerBoundEightThirtyOne_of_geometryClosureMatrix

/-! ## Explicit pointwise geometry rows -/

/-- Direct W11 geometry fields with the local-predicate input displayed. -/
structure DirectGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localPredicates :
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.{u} C hmin
  containment : ContainmentFields localPredicates.source
  noStartNoEarly : NoStartNoEarlyFields localPredicates.source

namespace DirectGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The geometry source row selected by the direct fields. -/
def source
    (D : DirectGeometryFields.{u} C hmin) :
    GeometrySourceFields.{u} C hmin :=
  D.localPredicates.source

/-- View the explicit fields as the broken-lattice W11 row. -/
def toBrokenLatticePredicateFields
    (D : DirectGeometryFields.{u} C hmin) :
    BrokenLatticeFieldsW11.DirectGeometryPredicateFields.{u} C hmin where
  localPredicates := D.localPredicates
  containment := D.containment
  noStartNoEarly := D.noStartNoEarly

/-- Forget to the W10 direct geometry package. -/
def toDirectGeometryPackage
    (D : DirectGeometryFields.{u} C hmin) :
    DirectGeometryPackage.{u} C hmin where
  source := D.source
  containment := D.containment
  noStartNoEarly := D.noStartNoEarly

/-- Project the explicit direct row to the W11 closure row. -/
def toGeometryClosureRow
    (D : DirectGeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofDirectGeometryPackage
    D.toDirectGeometryPackage

/-- Project the direct row to the narrow lower-bound input. -/
def toNarrowClosureInput
    (D : DirectGeometryFields.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  D.toGeometryClosureRow.toConcreteObligations

/-- Project the direct row to the checked lower-bound input. -/
def toCheckedClosureInput
    (D : DirectGeometryFields.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  D.toGeometryClosureRow.toCheckedClosureInput

/-- The explicit direct row closes the fixed minimal failure. -/
theorem contradiction
    (D : DirectGeometryFields.{u} C hmin) :
    False :=
  D.toGeometryClosureRow.contradiction

/-- The same direct row closes through the broken-lattice W11 row. -/
theorem contradiction_via_brokenLattice
    (D : DirectGeometryFields.{u} C hmin) :
    False :=
  D.toBrokenLatticePredicateFields.contradiction

end DirectGeometryFields

/-- K23 W11 geometry fields with the local-predicate input displayed. -/
structure K23GeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localPredicates :
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.{u} C hmin
  containment : ContainmentFields localPredicates.source
  k23NoEarly : K23NoEarlyFields localPredicates.source

namespace K23GeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The geometry source row selected by the K23 fields. -/
def source
    (K : K23GeometryFields.{u} C hmin) :
    GeometrySourceFields.{u} C hmin :=
  K.localPredicates.source

/-- View the explicit fields as the broken-lattice W11 K23 row. -/
def toBrokenLatticePredicateFields
    (K : K23GeometryFields.{u} C hmin) :
    BrokenLatticeFieldsW11.K23GeometryPredicateFields.{u} C hmin where
  localPredicates := K.localPredicates
  containment := K.containment
  k23NoEarly := K.k23NoEarly

/-- Forget to the W10 K23 geometry package. -/
def toK23GeometryPackage
    (K : K23GeometryFields.{u} C hmin) :
    K23GeometryPackage.{u} C hmin where
  source := K.source
  containment := K.containment
  k23NoEarly := K.k23NoEarly

/-- View the same data as the W11 K23 obstruction row. -/
def toK23ObstructionW10Fields
    (K : K23GeometryFields.{u} C hmin) :
    K23CommonNeighborW11.K23ObstructionW10Fields.{u} C hmin where
  source := K.source
  containment := K.containment
  k23Obstruction := K.k23NoEarly.k23Obstruction

/-- Project the explicit K23 row to the W11 closure row. -/
def toGeometryClosureRow
    (K : K23GeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofK23GeometryPackage
    K.toK23GeometryPackage

/-- Project the K23 row to the narrow lower-bound input. -/
def toNarrowClosureInput
    (K : K23GeometryFields.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  K.toGeometryClosureRow.toConcreteObligations

/-- Project the K23 row to the checked lower-bound input. -/
def toCheckedClosureInput
    (K : K23GeometryFields.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  K.toGeometryClosureRow.toCheckedClosureInput

/-- The explicit K23 row closes the fixed minimal failure. -/
theorem contradiction
    (K : K23GeometryFields.{u} C hmin) :
    False :=
  K.toGeometryClosureRow.contradiction

/-- The same K23 row closes through the obstruction W11 row. -/
theorem contradiction_via_obstruction
    (K : K23GeometryFields.{u} C hmin) :
    False :=
  K.toK23ObstructionW10Fields.contradiction

end K23GeometryFields

/-- Common-neighbor W11 geometry fields with the local-predicate input
displayed. -/
structure CommonNeighborGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localPredicates :
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.{u} C hmin
  containment : ContainmentFields localPredicates.source
  commonNeighborNoEarly : CommonNeighborNoEarlyFields localPredicates.source

namespace CommonNeighborGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The geometry source row selected by the common-neighbor fields. -/
def source
    (K : CommonNeighborGeometryFields.{u} C hmin) :
    GeometrySourceFields.{u} C hmin :=
  K.localPredicates.source

/-- View the explicit fields as the broken-lattice W11 common-neighbor row. -/
def toBrokenLatticePredicateFields
    (K : CommonNeighborGeometryFields.{u} C hmin) :
    BrokenLatticeFieldsW11.CommonNeighborGeometryPredicateFields.{u}
      C hmin where
  localPredicates := K.localPredicates
  containment := K.containment
  commonNeighborNoEarly := K.commonNeighborNoEarly

/-- Forget to the W10 common-neighbor geometry package. -/
def toCommonNeighborGeometryPackage
    (K : CommonNeighborGeometryFields.{u} C hmin) :
    CommonNeighborGeometryPackage.{u} C hmin where
  source := K.source
  containment := K.containment
  commonNeighborNoEarly := K.commonNeighborNoEarly

/-- View the same data as the W11 common-neighbor obstruction row. -/
def toCommonNeighborObstructionW10Fields
    (K : CommonNeighborGeometryFields.{u} C hmin) :
    K23CommonNeighborW11.CommonNeighborObstructionW10Fields.{u}
      C hmin where
  source := K.source
  containment := K.containment
  commonNeighborObstruction :=
    K.commonNeighborNoEarly.commonNeighborObstruction

/-- Project the explicit common-neighbor row to the W11 closure row. -/
def toGeometryClosureRow
    (K : CommonNeighborGeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofCommonNeighborGeometryPackage
    K.toCommonNeighborGeometryPackage

/-- Project the common-neighbor row to the narrow lower-bound input. -/
def toNarrowClosureInput
    (K : CommonNeighborGeometryFields.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  K.toGeometryClosureRow.toConcreteObligations

/-- Project the common-neighbor row to the checked lower-bound input. -/
def toCheckedClosureInput
    (K : CommonNeighborGeometryFields.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  K.toGeometryClosureRow.toCheckedClosureInput

/-- The explicit common-neighbor row closes the fixed minimal failure. -/
theorem contradiction
    (K : CommonNeighborGeometryFields.{u} C hmin) :
    False :=
  K.toGeometryClosureRow.contradiction

/-- The same common-neighbor row closes through the obstruction W11 row. -/
theorem contradiction_via_obstruction
    (K : CommonNeighborGeometryFields.{u} C hmin) :
    False :=
  K.toCommonNeighborObstructionW10Fields.contradiction

end CommonNeighborGeometryFields

/-! ## Uniform explicit source matrices -/

/-- Uniform direct geometry rows with all source fields displayed. -/
structure DirectGeometryMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectGeometryFields.{u} C hmin

namespace DirectGeometryMatrix

/-- Forget direct source rows to the W10 geometry matrix. -/
def toW10DirectGeometryMatrix
    (M : DirectGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectGeometryPackage

/-- Project direct source rows to the W11 geometry matrix. -/
def toGeometryClosureMatrix
    (M : DirectGeometryMatrix.{u}) :
    GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Project direct source rows to the narrow lower-bound input family. -/
def toNarrowClosureInputFamily
    (M : DirectGeometryMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toNarrowClosureInputFamily

/-- Project direct source rows to the checked lower-bound input family. -/
def toCheckedClosureInputFamily
    (M : DirectGeometryMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toCheckedClosureInputFamily

/-- Project direct source rows to the W10 target facade. -/
def toTargetFacadeMatrix
    (M : DirectGeometryMatrix.{u}) :
    SwanepoelTargetFacadeW10.Matrix :=
  targetFacadeMatrixOfGeometryClosureMatrix M.toGeometryClosureMatrix

/-- Direct source rows exclude minimal failures. -/
theorem no_minimalClearedFailure
    (M : DirectGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_geometryClosureMatrix
    M.toGeometryClosureMatrix

/-- Direct source rows clear the target pipeline. -/
theorem pipelineCleared
    (M : DirectGeometryMatrix.{u}) :
    PipelineCleared :=
  pipelineCleared_of_geometryClosureMatrix M.toGeometryClosureMatrix

/-- Conditional target projection from direct source rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : DirectGeometryMatrix.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_geometryClosureMatrix
    M.toGeometryClosureMatrix

end DirectGeometryMatrix

/-- Uniform K23 geometry rows with all source fields displayed. -/
structure K23GeometryMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23GeometryFields.{u} C hmin

namespace K23GeometryMatrix

/-- Forget K23 source rows to the W10 geometry matrix. -/
def toW10K23GeometryMatrix
    (M : K23GeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPackage

/-- Project K23 source rows to the W11 geometry matrix. -/
def toGeometryClosureMatrix
    (M : K23GeometryMatrix.{u}) :
    GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Project K23 source rows to the narrow lower-bound input family. -/
def toNarrowClosureInputFamily
    (M : K23GeometryMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toNarrowClosureInputFamily

/-- Project K23 source rows to the checked lower-bound input family. -/
def toCheckedClosureInputFamily
    (M : K23GeometryMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toCheckedClosureInputFamily

/-- Project K23 source rows to the W10 target facade. -/
def toTargetFacadeMatrix
    (M : K23GeometryMatrix.{u}) :
    SwanepoelTargetFacadeW10.Matrix :=
  targetFacadeMatrixOfGeometryClosureMatrix M.toGeometryClosureMatrix

/-- K23 source rows exclude minimal failures. -/
theorem no_minimalClearedFailure
    (M : K23GeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_geometryClosureMatrix
    M.toGeometryClosureMatrix

/-- K23 source rows clear the target pipeline. -/
theorem pipelineCleared
    (M : K23GeometryMatrix.{u}) :
    PipelineCleared :=
  pipelineCleared_of_geometryClosureMatrix M.toGeometryClosureMatrix

/-- Conditional target projection from K23 source rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : K23GeometryMatrix.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_geometryClosureMatrix
    M.toGeometryClosureMatrix

end K23GeometryMatrix

/-- Uniform common-neighbor geometry rows with all source fields displayed. -/
structure CommonNeighborGeometryMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborGeometryFields.{u} C hmin

namespace CommonNeighborGeometryMatrix

/-- Forget common-neighbor source rows to the W10 geometry matrix. -/
def toW10CommonNeighborGeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborGeometryPackage

/-- Project common-neighbor source rows to the W11 geometry matrix. -/
def toGeometryClosureMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Project common-neighbor rows to the narrow lower-bound input family. -/
def toNarrowClosureInputFamily
    (M : CommonNeighborGeometryMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toNarrowClosureInputFamily

/-- Project common-neighbor rows to the checked lower-bound input family. -/
def toCheckedClosureInputFamily
    (M : CommonNeighborGeometryMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toCheckedClosureInputFamily

/-- Project common-neighbor source rows to the W10 target facade. -/
def toTargetFacadeMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    SwanepoelTargetFacadeW10.Matrix :=
  targetFacadeMatrixOfGeometryClosureMatrix M.toGeometryClosureMatrix

/-- Common-neighbor source rows exclude minimal failures. -/
theorem no_minimalClearedFailure
    (M : CommonNeighborGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_geometryClosureMatrix
    M.toGeometryClosureMatrix

/-- Common-neighbor source rows clear the target pipeline. -/
theorem pipelineCleared
    (M : CommonNeighborGeometryMatrix.{u}) :
    PipelineCleared :=
  pipelineCleared_of_geometryClosureMatrix M.toGeometryClosureMatrix

/-- Conditional target projection from common-neighbor source rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : CommonNeighborGeometryMatrix.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_geometryClosureMatrix
    M.toGeometryClosureMatrix

end CommonNeighborGeometryMatrix

/-! ## Obstruction-row projections to the same facade -/

/-- Project K23 obstruction row families to W11 geometry matrices. -/
def geometryClosureMatrixOfK23ObstructionRows
    (H : K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}) :
    GeometryClosureMatrix.{u} where
  row := fun C hmin =>
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofK23GeometryPackage
      ((H.row C hmin).toK23GeometryPackage)

/-- Project common-neighbor obstruction row families to W11 geometry matrices. -/
def geometryClosureMatrixOfCommonNeighborObstructionRows
    (H : K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}) :
    GeometryClosureMatrix.{u} where
  row := fun C hmin =>
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofCommonNeighborGeometryPackage
      ((H.row C hmin).toCommonNeighborGeometryPackage)

/-- K23 obstruction rows exclude minimal failures. -/
theorem no_minimalClearedFailure_of_k23ObstructionRows
    (H : K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_geometryClosureMatrix
    (geometryClosureMatrixOfK23ObstructionRows H)

/-- Common-neighbor obstruction rows exclude minimal failures. -/
theorem no_minimalClearedFailure_of_commonNeighborObstructionRows
    (H : K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_geometryClosureMatrix
    (geometryClosureMatrixOfCommonNeighborObstructionRows H)

/-- Conditional target projection from K23 obstruction rows. -/
theorem targetLowerBoundEightThirtyOne_of_k23ObstructionRows
    (H : K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_geometryClosureMatrix
    (geometryClosureMatrixOfK23ObstructionRows H)

/-- Conditional target projection from common-neighbor obstruction rows. -/
theorem targetLowerBoundEightThirtyOne_of_commonNeighborObstructionRows
    (H : K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_geometryClosureMatrix
    (geometryClosureMatrixOfCommonNeighborObstructionRows H)

/-! ## W11 projection ledger -/

/-- W11 target-projection row for explicit direct source matrices. -/
def directGeometryTargetProjectionRow :
    W11TargetProjectionRow (DirectGeometryMatrix.{u}) :=
  SwanepoelW11ClosureMatrix.TargetProjectionRow.ofNoMinimalAndTarget
    DirectGeometryMatrix.no_minimalClearedFailure
    DirectGeometryMatrix.targetLowerBoundEightThirtyOne

/-- W11 target-projection row for explicit K23 source matrices. -/
def k23GeometryTargetProjectionRow :
    W11TargetProjectionRow (K23GeometryMatrix.{u}) :=
  SwanepoelW11ClosureMatrix.TargetProjectionRow.ofNoMinimalAndTarget
    K23GeometryMatrix.no_minimalClearedFailure
    K23GeometryMatrix.targetLowerBoundEightThirtyOne

/-- W11 target-projection row for explicit common-neighbor source matrices. -/
def commonNeighborGeometryTargetProjectionRow :
    W11TargetProjectionRow (CommonNeighborGeometryMatrix.{u}) :=
  SwanepoelW11ClosureMatrix.TargetProjectionRow.ofNoMinimalAndTarget
    CommonNeighborGeometryMatrix.no_minimalClearedFailure
    CommonNeighborGeometryMatrix.targetLowerBoundEightThirtyOne

/-- W11 target-projection row for K23 obstruction row families. -/
def k23ObstructionTargetProjectionRow :
    W11TargetProjectionRow
      (K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}) :=
  SwanepoelW11ClosureMatrix.TargetProjectionRow.ofNoMinimalAndTarget
    no_minimalClearedFailure_of_k23ObstructionRows
    targetLowerBoundEightThirtyOne_of_k23ObstructionRows

/-- W11 target-projection row for common-neighbor obstruction row families. -/
def commonNeighborObstructionTargetProjectionRow :
    W11TargetProjectionRow
      (K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}) :=
  SwanepoelW11ClosureMatrix.TargetProjectionRow.ofNoMinimalAndTarget
    no_minimalClearedFailure_of_commonNeighborObstructionRows
    targetLowerBoundEightThirtyOne_of_commonNeighborObstructionRows

/-- Consolidated conditional ledger for exact geometry-source projections. -/
structure Matrix : Type (u + 1) where
  checkedInputs : W11TargetProjectionRow (CheckedClosureInputFamily.{u})
  narrowInputs : W11TargetProjectionRow (NarrowClosureInputFamily.{u})
  geometryClosure : W11TargetProjectionRow (GeometryClosureMatrix.{u})
  directGeometry : W11TargetProjectionRow (DirectGeometryMatrix.{u})
  k23Geometry : W11TargetProjectionRow (K23GeometryMatrix.{u})
  commonNeighborGeometry :
    W11TargetProjectionRow (CommonNeighborGeometryMatrix.{u})
  k23Obstruction :
    W11TargetProjectionRow
      (K23CommonNeighborW11.K23ObstructionW10RowFamily.{u})
  commonNeighborObstruction :
    W11TargetProjectionRow
      (K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u})

/-- The checked W11 conditional ledger. -/
def matrix : Matrix.{u} where
  checkedInputs :=
    SwanepoelW11ClosureMatrix.TargetProjectionRow.ofNoMinimalAndTarget
      (SwanepoelTargetClosureW11.no_minimalClearedFailure_of_projectionRow
        (MinimalFailureGeometryMatrixW11.checkedClosureInputFamilyRow :
          W10ProjectionRow (CheckedClosureInputFamily.{u})))
      (SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_projectionRow
        (MinimalFailureGeometryMatrixW11.checkedClosureInputFamilyRow :
          W10ProjectionRow (CheckedClosureInputFamily.{u})))
  narrowInputs :=
    SwanepoelW11ClosureMatrix.TargetProjectionRow.ofNoMinimalAndTarget
      (SwanepoelTargetClosureW11.no_minimalClearedFailure_of_projectionRow
        (MinimalFailureGeometryMatrixW11.narrowClosureInputFamilyRow :
          W10ProjectionRow (NarrowClosureInputFamily.{u})))
      (SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_projectionRow
        (MinimalFailureGeometryMatrixW11.narrowClosureInputFamilyRow :
          W10ProjectionRow (NarrowClosureInputFamily.{u})))
  geometryClosure := geometryClosureTargetProjectionRow
  directGeometry := directGeometryTargetProjectionRow
  k23Geometry := k23GeometryTargetProjectionRow
  commonNeighborGeometry := commonNeighborGeometryTargetProjectionRow
  k23Obstruction := k23ObstructionTargetProjectionRow
  commonNeighborObstruction := commonNeighborObstructionTargetProjectionRow

end

end MinimalFailureGeometryClosureW11
end Swanepoel
end ErdosProblems1066
