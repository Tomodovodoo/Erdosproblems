import ErdosProblems1066.Swanepoel.MinimalFailureGeometryClosureW11
import ErdosProblems1066.Swanepoel.MinimalFailureGeometryMatrixW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11
import ErdosProblems1066.Swanepoel.BrokenLatticeClosureW11
import ErdosProblems1066.Swanepoel.K23ClosureW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Integrated W11 geometry closure matrix

This module is a source-facing ledger for the W11 geometry routes.  It keeps
the selected geometry source, topology/enclosure fields, angle/long-arc data,
window containment, and route-specific no-early data visible, then records the
checked projections into:

* the W11 minimal-failure geometry closure input;
* the W11 broken-lattice closure rows;
* the W11 K23/common-neighbor closure rows; and
* the conditional Swanepoel target facade.

Every public target theorem below takes an explicit uniform input matrix.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace GeometryIntegratedW11

open GeometryRemainingFieldsW10
open MinimalGraphFacts

universe u v

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetClosureMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetClosureMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetClosureMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  MinimalClearedFailureEliminator

abbrev GeometryClosureMatrix :=
  MinimalFailureGeometryMatrixW11.GeometryClosureMatrix

abbrev NarrowClosureInputFamily :=
  MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily

abbrev CheckedClosureInputFamily :=
  MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily

abbrev TargetFacadeMatrix :=
  SwanepoelTargetFacadeW10.Matrix

abbrev TargetProjectionRow (alpha : Sort v) :=
  TargetClosureMatrixW11.TargetProjectionRow alpha

/-! ## Pointwise source-facing geometry rows -/

/-- Direct W11 geometry fields for one fixed minimal failure. -/
structure DirectGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  noStartNoEarly : NoStartNoEarlyFields source

namespace DirectGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The exact topology/enclosure data selected by the source row. -/
def topology
    (R : DirectGeometryFields.{u} C hmin) :=
  R.source.geometry.topology

/-- The outer-boundary angle data selected by the source row. -/
def outerAngleBounds
    (R : DirectGeometryFields.{u} C hmin) :=
  R.source.geometry.outerAngleBounds

/-- The selected long nonconcave arc data. -/
def longArc
    (R : DirectGeometryFields.{u} C hmin) :=
  R.source.geometry.longArc

/-- The selected construction turn bounds. -/
def turnBounds
    (R : DirectGeometryFields.{u} C hmin) :=
  R.source.turnBounds

/-- The exact local containment fields for the selected source row. -/
def localContainment
    (R : DirectGeometryFields.{u} C hmin) :=
  R.containment.localContainment

/-- The local-predicate package selected by the displayed source row. -/
def toGeometryLocalPredicateFields
    (R : DirectGeometryFields.{u} C hmin) :
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.{u} C hmin :=
  BrokenLatticeFieldsW11.GeometryLocalPredicateFields.ofGeometrySourceFields
    R.source

/-- Repackage as the W10 direct geometry row. -/
def toDirectGeometryPackage
    (R : DirectGeometryFields.{u} C hmin) :
    DirectGeometryPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

/-- Repackage as the W11 broken-lattice direct predicate row. -/
def toBrokenLatticeDirectGeometryPredicateFields
    (R : DirectGeometryFields.{u} C hmin) :
    BrokenLatticeFieldsW11.DirectGeometryPredicateFields.{u} C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

/-- Repackage as the W11 minimal-failure closure direct row. -/
def toMinimalFailureDirectGeometryFields
    (R : DirectGeometryFields.{u} C hmin) :
    MinimalFailureGeometryClosureW11.DirectGeometryFields.{u} C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

/-- Repackage as the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : DirectGeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofDirectGeometryPackage
    R.toDirectGeometryPackage

/-- The narrow concrete closure input selected by the direct row. -/
def toNarrowClosureInput
    (R : DirectGeometryFields.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toGeometryClosureRow.toConcreteObligations

/-- The checked refined closure input selected by the direct row. -/
def toCheckedClosureInput
    (R : DirectGeometryFields.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  R.toGeometryClosureRow.toCheckedClosureInput

/-- A fixed direct W11 geometry row closes the selected minimal failure. -/
theorem contradiction
    (R : DirectGeometryFields.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

/-- The same direct row closes through the broken-lattice facade. -/
theorem contradiction_via_brokenLattice
    (R : DirectGeometryFields.{u} C hmin) :
    False :=
  BrokenLatticeClosureW11.contradiction_of_directGeometryPredicateFields
    R.toBrokenLatticeDirectGeometryPredicateFields

end DirectGeometryFields

/-- K23-derived W11 geometry fields for one fixed minimal failure. -/
structure K23GeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  k23NoEarly : K23NoEarlyFields source

namespace K23GeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The exact topology/enclosure data selected by the source row. -/
def topology
    (R : K23GeometryFields.{u} C hmin) :=
  R.source.geometry.topology

/-- The outer-boundary angle data selected by the source row. -/
def outerAngleBounds
    (R : K23GeometryFields.{u} C hmin) :=
  R.source.geometry.outerAngleBounds

/-- The selected long nonconcave arc data. -/
def longArc
    (R : K23GeometryFields.{u} C hmin) :=
  R.source.geometry.longArc

/-- The selected construction turn bounds. -/
def turnBounds
    (R : K23GeometryFields.{u} C hmin) :=
  R.source.turnBounds

/-- The exact local containment fields for the selected source row. -/
def localContainment
    (R : K23GeometryFields.{u} C hmin) :=
  R.containment.localContainment

/-- The local-predicate package selected by the displayed source row. -/
def toGeometryLocalPredicateFields
    (R : K23GeometryFields.{u} C hmin) :
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.{u} C hmin :=
  BrokenLatticeFieldsW11.GeometryLocalPredicateFields.ofGeometrySourceFields
    R.source

/-- Repackage as the W10 K23 geometry row. -/
def toK23GeometryPackage
    (R : K23GeometryFields.{u} C hmin) :
    K23GeometryPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- Repackage as the W11 K23 obstruction row. -/
def toK23ObstructionW10Fields
    (R : K23GeometryFields.{u} C hmin) :
    K23CommonNeighborW11.K23ObstructionW10Fields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.k23NoEarly.k23Obstruction

/-- Repackage as the W11 broken-lattice K23 predicate row. -/
def toBrokenLatticeK23GeometryPredicateFields
    (R : K23GeometryFields.{u} C hmin) :
    BrokenLatticeFieldsW11.K23GeometryPredicateFields.{u} C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- Repackage as the W11 minimal-failure closure K23 row. -/
def toMinimalFailureK23GeometryFields
    (R : K23GeometryFields.{u} C hmin) :
    MinimalFailureGeometryClosureW11.K23GeometryFields.{u} C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- Repackage as the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : K23GeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofK23GeometryPackage
    R.toK23GeometryPackage

/-- The narrow concrete closure input selected by the K23 row. -/
def toNarrowClosureInput
    (R : K23GeometryFields.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toGeometryClosureRow.toConcreteObligations

/-- The checked refined closure input selected by the K23 row. -/
def toCheckedClosureInput
    (R : K23GeometryFields.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  R.toGeometryClosureRow.toCheckedClosureInput

/-- A fixed K23 W11 geometry row closes the selected minimal failure. -/
theorem contradiction
    (R : K23GeometryFields.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

/-- The same K23 row closes through the K23 closure facade. -/
theorem contradiction_via_k23Closure
    (R : K23GeometryFields.{u} C hmin) :
    False :=
  K23ClosureW11.K23ClosureFields.contradiction
    R.toK23ObstructionW10Fields

end K23GeometryFields

/-- Common-neighbor-derived W11 geometry fields for one fixed minimal
failure. -/
structure CommonNeighborGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  commonNeighborNoEarly : CommonNeighborNoEarlyFields source

namespace CommonNeighborGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The exact topology/enclosure data selected by the source row. -/
def topology
    (R : CommonNeighborGeometryFields.{u} C hmin) :=
  R.source.geometry.topology

/-- The outer-boundary angle data selected by the source row. -/
def outerAngleBounds
    (R : CommonNeighborGeometryFields.{u} C hmin) :=
  R.source.geometry.outerAngleBounds

/-- The selected long nonconcave arc data. -/
def longArc
    (R : CommonNeighborGeometryFields.{u} C hmin) :=
  R.source.geometry.longArc

/-- The selected construction turn bounds. -/
def turnBounds
    (R : CommonNeighborGeometryFields.{u} C hmin) :=
  R.source.turnBounds

/-- The exact local containment fields for the selected source row. -/
def localContainment
    (R : CommonNeighborGeometryFields.{u} C hmin) :=
  R.containment.localContainment

/-- The local-predicate package selected by the displayed source row. -/
def toGeometryLocalPredicateFields
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    BrokenLatticeFieldsW11.GeometryLocalPredicateFields.{u} C hmin :=
  BrokenLatticeFieldsW11.GeometryLocalPredicateFields.ofGeometrySourceFields
    R.source

/-- Repackage as the W10 common-neighbor geometry row. -/
def toCommonNeighborGeometryPackage
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    CommonNeighborGeometryPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Repackage as the W11 common-neighbor obstruction row. -/
def toCommonNeighborObstructionW10Fields
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    K23CommonNeighborW11.CommonNeighborObstructionW10Fields.{u}
      C hmin where
  source := R.source
  containment := R.containment
  commonNeighborObstruction :=
    R.commonNeighborNoEarly.commonNeighborObstruction

/-- Forget common-neighbor fields to the corresponding K23 route. -/
def toK23GeometryFields
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    K23GeometryFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.commonNeighborNoEarly.toK23NoEarlyFields

/-- Repackage as the W11 broken-lattice common-neighbor predicate row. -/
def toBrokenLatticeCommonNeighborGeometryPredicateFields
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    BrokenLatticeFieldsW11.CommonNeighborGeometryPredicateFields.{u}
      C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Repackage as the W11 minimal-failure closure common-neighbor row. -/
def toMinimalFailureCommonNeighborGeometryFields
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    MinimalFailureGeometryClosureW11.CommonNeighborGeometryFields.{u}
      C hmin where
  localPredicates := R.toGeometryLocalPredicateFields
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Repackage as the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofCommonNeighborGeometryPackage
    R.toCommonNeighborGeometryPackage

/-- The narrow concrete closure input selected by the common-neighbor row. -/
def toNarrowClosureInput
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toGeometryClosureRow.toConcreteObligations

/-- The checked refined closure input selected by the common-neighbor row. -/
def toCheckedClosureInput
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  R.toGeometryClosureRow.toCheckedClosureInput

/-- A fixed common-neighbor W11 geometry row closes the selected minimal
failure. -/
theorem contradiction
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

/-- The same common-neighbor row closes through the K23/common-neighbor
facade. -/
theorem contradiction_via_commonNeighborClosure
    (R : CommonNeighborGeometryFields.{u} C hmin) :
    False :=
  K23ClosureW11.CommonNeighborClosureFields.contradiction
    R.toCommonNeighborObstructionW10Fields

end CommonNeighborGeometryFields

/-! ## Uniform explicit geometry matrices -/

/-- Uniform direct W11 geometry rows for every minimal cleared failure. -/
structure DirectGeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectGeometryFields.{u} C hmin

namespace DirectGeometryMatrix

/-- Route direct rows to the W11 minimal-failure geometry closure matrix. -/
def toMinimalFailureDirectGeometryMatrix
    (M : DirectGeometryMatrix.{u}) :
    MinimalFailureGeometryClosureW11.DirectGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toMinimalFailureDirectGeometryFields

/-- Route direct rows to the W11 broken-lattice direct predicate matrix. -/
def toBrokenLatticeDirectGeometryPredicateMatrix
    (M : DirectGeometryMatrix.{u}) :
    BrokenLatticeClosureW11.DirectGeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeDirectGeometryPredicateFields

/-- Route direct rows to the W11 target-closure direct predicate matrix. -/
def toTargetClosureDirectGeometryPredicateMatrix
    (M : DirectGeometryMatrix.{u}) :
    TargetClosureMatrixW11.DirectGeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeDirectGeometryPredicateFields

/-- Route direct rows to the W10 direct geometry matrix. -/
def toW10DirectGeometryMatrix
    (M : DirectGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectGeometryPackage

/-- Route direct rows to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : DirectGeometryMatrix.{u}) :
    GeometryClosureMatrix.{u} :=
  M.toMinimalFailureDirectGeometryMatrix.toGeometryClosureMatrix

/-- Route direct rows to the narrow concrete closure input family. -/
def toNarrowClosureInputFamily
    (M : DirectGeometryMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toNarrowClosureInputFamily

/-- Route direct rows to the checked refined closure input family. -/
def toCheckedClosureInputFamily
    (M : DirectGeometryMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toCheckedClosureInputFamily

/-- Route direct rows to the W10 target facade matrix. -/
def toTargetFacadeMatrix
    (M : DirectGeometryMatrix.{u}) :
    TargetFacadeMatrix :=
  MinimalFailureGeometryClosureW11.targetFacadeMatrixOfGeometryClosureMatrix
    M.toGeometryClosureMatrix

/-- Direct rows give the pointwise minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : DirectGeometryMatrix.{u}) :
    MinimalFailureEliminator := by
  intro n C hmin
  exact (M.row C hmin).contradiction

/-- Direct rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : DirectGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  MinimalFailureGeometryClosureW11.DirectGeometryMatrix.no_minimalClearedFailure
    M.toMinimalFailureDirectGeometryMatrix

/-- Direct rows clear the conditional target pipeline. -/
theorem pipelineCleared
    (M : DirectGeometryMatrix.{u}) :
    PipelineCleared :=
  MinimalFailureGeometryClosureW11.DirectGeometryMatrix.pipelineCleared
    M.toMinimalFailureDirectGeometryMatrix

/-- Conditional target projection from direct W11 geometry rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : DirectGeometryMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.targetLowerBoundEightThirtyOne_of_directGeometryPredicateMatrix
    M.toTargetClosureDirectGeometryPredicateMatrix

end DirectGeometryMatrix

/-- Uniform K23-derived W11 geometry rows for every minimal cleared failure. -/
structure K23GeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23GeometryFields.{u} C hmin

namespace K23GeometryMatrix

/-- Route K23 rows to the W11 minimal-failure geometry closure matrix. -/
def toMinimalFailureK23GeometryMatrix
    (M : K23GeometryMatrix.{u}) :
    MinimalFailureGeometryClosureW11.K23GeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toMinimalFailureK23GeometryFields

/-- Route K23 rows to the W11 broken-lattice K23 predicate matrix. -/
def toBrokenLatticeK23GeometryPredicateMatrix
    (M : K23GeometryMatrix.{u}) :
    BrokenLatticeClosureW11.K23GeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeK23GeometryPredicateFields

/-- Route K23 rows to the W11 K23 obstruction row family. -/
def toK23RowFamily
    (M : K23GeometryMatrix.{u}) :
    K23ClosureW11.K23RowFamily.{u} where
  row := fun C hmin => (M.row C hmin).toK23ObstructionW10Fields

/-- Route K23 rows to the W10 K23 geometry matrix. -/
def toW10K23GeometryMatrix
    (M : K23GeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPackage

/-- Route K23 rows to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : K23GeometryMatrix.{u}) :
    GeometryClosureMatrix.{u} :=
  M.toMinimalFailureK23GeometryMatrix.toGeometryClosureMatrix

/-- Route K23 rows to the narrow concrete closure input family. -/
def toNarrowClosureInputFamily
    (M : K23GeometryMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toNarrowClosureInputFamily

/-- Route K23 rows to the checked refined closure input family. -/
def toCheckedClosureInputFamily
    (M : K23GeometryMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toCheckedClosureInputFamily

/-- Route K23 rows to the W10 target facade matrix. -/
def toTargetFacadeMatrix
    (M : K23GeometryMatrix.{u}) :
    TargetFacadeMatrix :=
  MinimalFailureGeometryClosureW11.targetFacadeMatrixOfGeometryClosureMatrix
    M.toGeometryClosureMatrix

/-- K23 rows give the pointwise minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : K23GeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  K23ClosureW11.K23RowFamily.minimalClearedFailureEliminator
    M.toK23RowFamily

/-- K23 rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : K23GeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  K23ClosureW11.K23RowFamily.no_minimalClearedFailure
    M.toK23RowFamily

/-- K23 rows clear the conditional target pipeline. -/
theorem pipelineCleared
    (M : K23GeometryMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

/-- Conditional target projection from K23 W11 geometry rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : K23GeometryMatrix.{u}) :
    Target :=
  K23ClosureW11.K23RowFamily.targetLowerBoundEightThirtyOne
    M.toK23RowFamily

end K23GeometryMatrix

/-- Uniform common-neighbor-derived W11 geometry rows for every minimal
cleared failure. -/
structure CommonNeighborGeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborGeometryFields.{u} C hmin

namespace CommonNeighborGeometryMatrix

/-- Route common-neighbor rows to the W11 minimal-failure geometry closure
matrix. -/
def toMinimalFailureCommonNeighborGeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    MinimalFailureGeometryClosureW11.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toMinimalFailureCommonNeighborGeometryFields

/-- Route common-neighbor rows to the W11 broken-lattice predicate matrix. -/
def toBrokenLatticeCommonNeighborGeometryPredicateMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    BrokenLatticeClosureW11.CommonNeighborGeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeCommonNeighborGeometryPredicateFields

/-- Route common-neighbor rows to the W11 common-neighbor obstruction family. -/
def toCommonNeighborRowFamily
    (M : CommonNeighborGeometryMatrix.{u}) :
    K23ClosureW11.CommonNeighborRowFamily.{u} where
  row := fun C hmin =>
    (M.row C hmin).toCommonNeighborObstructionW10Fields

/-- Forget common-neighbor rows to K23 rows through the checked adapter. -/
def toK23GeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryFields

/-- Route common-neighbor rows to the W10 common-neighbor geometry matrix. -/
def toW10CommonNeighborGeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toCommonNeighborGeometryPackage

/-- Route common-neighbor rows to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    GeometryClosureMatrix.{u} :=
  M.toMinimalFailureCommonNeighborGeometryMatrix.toGeometryClosureMatrix

/-- Route common-neighbor rows to the narrow concrete closure input family. -/
def toNarrowClosureInputFamily
    (M : CommonNeighborGeometryMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toNarrowClosureInputFamily

/-- Route common-neighbor rows to the checked refined closure input family. -/
def toCheckedClosureInputFamily
    (M : CommonNeighborGeometryMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toGeometryClosureMatrix.toCheckedClosureInputFamily

/-- Route common-neighbor rows to the W10 target facade matrix. -/
def toTargetFacadeMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    TargetFacadeMatrix :=
  MinimalFailureGeometryClosureW11.targetFacadeMatrixOfGeometryClosureMatrix
    M.toGeometryClosureMatrix

/-- Common-neighbor rows give the pointwise minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : CommonNeighborGeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  K23ClosureW11.CommonNeighborRowFamily.minimalClearedFailureEliminator
    M.toCommonNeighborRowFamily

/-- Common-neighbor rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : CommonNeighborGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  K23ClosureW11.CommonNeighborRowFamily.no_minimalClearedFailure
    M.toCommonNeighborRowFamily

/-- Common-neighbor rows clear the conditional target pipeline. -/
theorem pipelineCleared
    (M : CommonNeighborGeometryMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

/-- Conditional target projection from common-neighbor W11 geometry rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : CommonNeighborGeometryMatrix.{u}) :
    Target :=
  K23ClosureW11.CommonNeighborRowFamily.targetLowerBoundEightThirtyOne
    M.toCommonNeighborRowFamily

end CommonNeighborGeometryMatrix

/-! ## Integrated projection rows -/

/-- A checked route from a visible geometry matrix to the closure inputs and
target-facing conclusions. -/
structure GeometryProjectionRow (alpha : Type v) where
  geometryClosure :
    alpha -> MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u}
  narrowInputs :
    alpha -> MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u}
  checkedInputs :
    alpha -> MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u}
  targetFacade : alpha -> TargetFacadeMatrix
  targetProjection : TargetProjectionRow alpha

namespace GeometryProjectionRow

/-- Minimal-failure exclusion supplied by the target projection row. -/
def noMinimal
    {alpha : Type v} (R : GeometryProjectionRow.{u, v} alpha)
    (a : alpha) :
    MinimalFailureExclusion :=
  R.targetProjection.noMinimal a

/-- Cleared-pipeline projection supplied by the target projection row. -/
def pipeline
    {alpha : Type v} (R : GeometryProjectionRow.{u, v} alpha)
    (a : alpha) :
    PipelineCleared :=
  R.targetProjection.pipeline a

/-- Conditional target projection supplied by the target projection row. -/
def target
    {alpha : Type v} (R : GeometryProjectionRow.{u, v} alpha)
    (a : alpha) :
    Target :=
  R.targetProjection.target a

end GeometryProjectionRow

/-- Target route for direct integrated geometry matrices. -/
def directTargetProjectionRow :
    TargetProjectionRow (DirectGeometryMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    DirectGeometryMatrix.no_minimalClearedFailure
    DirectGeometryMatrix.targetLowerBoundEightThirtyOne

/-- Target route for K23 integrated geometry matrices. -/
def k23TargetProjectionRow :
    TargetProjectionRow (K23GeometryMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    K23GeometryMatrix.no_minimalClearedFailure
    K23GeometryMatrix.targetLowerBoundEightThirtyOne

/-- Target route for common-neighbor integrated geometry matrices. -/
def commonNeighborTargetProjectionRow :
    TargetProjectionRow (CommonNeighborGeometryMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    CommonNeighborGeometryMatrix.no_minimalClearedFailure
    CommonNeighborGeometryMatrix.targetLowerBoundEightThirtyOne

/-- Integrated route row for direct geometry matrices. -/
def directGeometryProjectionRow :
    GeometryProjectionRow (DirectGeometryMatrix.{u}) where
  geometryClosure := DirectGeometryMatrix.toGeometryClosureMatrix
  narrowInputs := DirectGeometryMatrix.toNarrowClosureInputFamily
  checkedInputs := DirectGeometryMatrix.toCheckedClosureInputFamily
  targetFacade := DirectGeometryMatrix.toTargetFacadeMatrix
  targetProjection := directTargetProjectionRow

/-- Integrated route row for K23 geometry matrices. -/
def k23GeometryProjectionRow :
    GeometryProjectionRow (K23GeometryMatrix.{u}) where
  geometryClosure := K23GeometryMatrix.toGeometryClosureMatrix
  narrowInputs := K23GeometryMatrix.toNarrowClosureInputFamily
  checkedInputs := K23GeometryMatrix.toCheckedClosureInputFamily
  targetFacade := K23GeometryMatrix.toTargetFacadeMatrix
  targetProjection := k23TargetProjectionRow

/-- Integrated route row for common-neighbor geometry matrices. -/
def commonNeighborGeometryProjectionRow :
    GeometryProjectionRow (CommonNeighborGeometryMatrix.{u}) where
  geometryClosure := CommonNeighborGeometryMatrix.toGeometryClosureMatrix
  narrowInputs := CommonNeighborGeometryMatrix.toNarrowClosureInputFamily
  checkedInputs := CommonNeighborGeometryMatrix.toCheckedClosureInputFamily
  targetFacade := CommonNeighborGeometryMatrix.toTargetFacadeMatrix
  targetProjection := commonNeighborTargetProjectionRow

/-! ## Integrated geometry closure matrix -/

/-- Integrated W11 geometry closure matrix.

The record stores adapters and conditional route rows only.  It does not
construct any direct, K23, or common-neighbor geometry input matrix. -/
structure Matrix : Type (u + 1) where
  minimalFailureGeometry :
    MinimalFailureGeometryMatrixW11.Matrix.{u}
  minimalFailureGeometryClosure :
    MinimalFailureGeometryClosureW11.Matrix.{u}
  targetClosure : TargetClosureMatrixW11.Matrix.{u}
  brokenLatticeClosure : BrokenLatticeClosureW11.Matrix.{u}
  k23Closure : K23ClosureW11.Matrix.{u}
  directGeometry :
    GeometryProjectionRow (DirectGeometryMatrix.{u})
  k23Geometry :
    GeometryProjectionRow (K23GeometryMatrix.{u})
  commonNeighborGeometry :
    GeometryProjectionRow (CommonNeighborGeometryMatrix.{u})

/-- The checked integrated W11 geometry closure ledger. -/
def matrix : Matrix.{u} where
  minimalFailureGeometry := MinimalFailureGeometryMatrixW11.matrix
  minimalFailureGeometryClosure := MinimalFailureGeometryClosureW11.matrix
  targetClosure := TargetClosureMatrixW11.matrix
  brokenLatticeClosure := BrokenLatticeClosureW11.matrix
  k23Closure := K23ClosureW11.matrix
  directGeometry := directGeometryProjectionRow
  k23Geometry := k23GeometryProjectionRow
  commonNeighborGeometry := commonNeighborGeometryProjectionRow

/-! ## Public conditional projections -/

/-- Minimal-failure exclusion from uniform direct W11 geometry rows. -/
theorem no_minimalClearedFailure_of_directGeometryMatrix
    (M : DirectGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.directGeometry.noMinimal M

/-- Cleared-pipeline projection from uniform direct W11 geometry rows. -/
theorem pipelineCleared_of_directGeometryMatrix
    (M : DirectGeometryMatrix.{u}) :
    PipelineCleared :=
  matrix.directGeometry.pipeline M

/-- Conditional target projection from uniform direct W11 geometry rows. -/
theorem targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    (M : DirectGeometryMatrix.{u}) :
    Target :=
  matrix.directGeometry.target M

/-- Minimal-failure exclusion from uniform K23 W11 geometry rows. -/
theorem no_minimalClearedFailure_of_k23GeometryMatrix
    (M : K23GeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.k23Geometry.noMinimal M

/-- Cleared-pipeline projection from uniform K23 W11 geometry rows. -/
theorem pipelineCleared_of_k23GeometryMatrix
    (M : K23GeometryMatrix.{u}) :
    PipelineCleared :=
  matrix.k23Geometry.pipeline M

/-- Conditional target projection from uniform K23 W11 geometry rows. -/
theorem targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    (M : K23GeometryMatrix.{u}) :
    Target :=
  matrix.k23Geometry.target M

/-- Minimal-failure exclusion from uniform common-neighbor W11 geometry rows. -/
theorem no_minimalClearedFailure_of_commonNeighborGeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.commonNeighborGeometry.noMinimal M

/-- Cleared-pipeline projection from uniform common-neighbor W11 geometry
rows. -/
theorem pipelineCleared_of_commonNeighborGeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    PipelineCleared :=
  matrix.commonNeighborGeometry.pipeline M

/-- Conditional target projection from uniform common-neighbor W11 geometry
rows. -/
theorem targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    Target :=
  matrix.commonNeighborGeometry.target M

end

end GeometryIntegratedW11
end Swanepoel
end ErdosProblems1066
