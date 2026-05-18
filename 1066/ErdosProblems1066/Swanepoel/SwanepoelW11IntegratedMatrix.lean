import ErdosProblems1066.Swanepoel.TopologyInstantiationW11
import ErdosProblems1066.Swanepoel.SubpolygonFamilyW11
import ErdosProblems1066.Swanepoel.BoundaryLabelRowsW11
import ErdosProblems1066.Swanepoel.BoundaryAngleTurnW11
import ErdosProblems1066.Swanepoel.SubpolygonClosureW11
import ErdosProblems1066.Swanepoel.WindowNoEarlyRowsW11
import ErdosProblems1066.Swanepoel.WindowNoEarlyClosureW11
import ErdosProblems1066.Swanepoel.K23CommonNeighborW11
import ErdosProblems1066.Swanepoel.K23ClosureW11
import ErdosProblems1066.Swanepoel.BrokenLatticeFieldsW11
import ErdosProblems1066.Swanepoel.MinimalFailureGeometryMatrixW11
import ErdosProblems1066.Swanepoel.MinimalFailureGeometryClosureW11
import ErdosProblems1066.Swanepoel.SwanepoelTargetClosureW11
import ErdosProblems1066.Swanepoel.SwanepoelW11ClosureMatrix
import ErdosProblems1066.Swanepoel.BrokenLatticeClosureW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11

set_option autoImplicit false

/-!
# Swanepoel W11 integrated matrix

This file collects the checked W11 Swanepoel modules present in this tree.
The integrated matrix is a ledger of projections and conditional routes; it
does not provide any missing geometric, topological, window, or no-early
fields by itself.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW11IntegratedMatrix

universe u v

noncomputable section

abbrev Target : Prop :=
  SwanepoelTargetClosureW11.Target

abbrev MinimalFailureExclusion : Prop :=
  SwanepoelTargetClosureW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SwanepoelTargetClosureW11.PipelineCleared

/-! ## Conditional target routes -/

/-- A conditional route to the public Swanepoel target from a visible input. -/
structure TargetProjectionRow (alpha : Sort v) : Sort (max 1 v) where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace TargetProjectionRow

/-- Build a route from a minimal-failure exclusion and target projection. -/
def ofNoMinimalAndTarget
    {alpha : Sort v}
    (noMinimal : alpha -> MinimalFailureExclusion)
    (target : alpha -> Target) :
    TargetProjectionRow alpha where
  noMinimal := noMinimal
  pipeline := fun x =>
    SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
      (noMinimal x)
  target := target

/-- Reuse a W10 projection row inside the W11 integrated ledger. -/
def ofW10ProjectionRow
    {alpha : Type v}
    (R : SwanepoelW10ClosureMatrix.ProjectionRow alpha) :
    TargetProjectionRow alpha :=
  ofNoMinimalAndTarget R.noMinimal R.target

/-- Reuse the W11 closure-matrix route row inside the integrated ledger. -/
def ofW11ProjectionRow
    {alpha : Sort v}
    (R : SwanepoelW11ClosureMatrix.TargetProjectionRow alpha) :
    TargetProjectionRow alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end TargetProjectionRow

/-! ## Non-target W11 projection ledger -/

/-- Checked W11 projections that feed later rows but do not reach the public
target on their own. -/
structure FieldProjectionLedger : Type (u + 1) where
  topologyExact :
    forall {n : Nat} (C : _root_.UDConfig n),
      TopologyInstantiationW11.CheckedTopologyPackageTarget C <->
        TopologyFrontierW10.ExactOuterBoundaryTopologyFieldTarget C
  topologyRemaining :
    forall {n : Nat} {C : _root_.UDConfig n},
      TopologyInstantiationW11.CheckedTopologyPackage C ->
        OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C
  subpolygonCounting :
    forall {n : Nat}
      {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
      {D : SubpolygonInstantiation.ExplicitOuterBoundaryFaceData.{u} G}
      (F : SubpolygonFamilyW11.SubpolygonFamilyPackage.{u} D),
        PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
          F.toPlanarBoundaryData
  subpolygonBoundaryRoute :
    forall {n : Nat} {C : _root_.UDConfig n},
      SubpolygonClosureW11.ClassifiedRoute.SubpolygonBoundaryPackage.{u}
        C ->
        SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C
  boundaryLabelBase :
    forall {n : Nat} {C : _root_.UDConfig n}
      {hmin : MinimalGraphFacts.IsMinimalClearedFailure C},
      BoundaryLabelRowsW11.BoundaryLabelRowPackage.BasePrefix.{u}
        C hmin ->
        SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin
  boundaryAngleTopology :
    forall {n : Nat} {C : _root_.UDConfig n},
      BoundaryAngleTurnW11.UDConfigRoute.BoundaryAngleTurnTopologyPackage.{u}
        C ->
        SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C

/-- The checked non-target W11 projection ledger. -/
def fieldProjectionLedger : FieldProjectionLedger.{u} where
  topologyExact := fun C =>
    TopologyInstantiationW11.checkedTopologyPackageTarget_iff_exactFieldTarget
      C
  topologyRemaining := fun P =>
    TopologyInstantiationW11.remainingCoreTopologyRequirements_of_checkedTopologyPackage
      P
  subpolygonCounting := fun F =>
    F.faceCountingTheorems
  subpolygonBoundaryRoute := fun P =>
    P.toW9TopologyAngleSubpolygonRow
  boundaryLabelBase := fun B =>
    B.toW10BaseRow
  boundaryAngleTopology := fun Q =>
    Q.toW9TopologyAngleSubpolygonRow

/-! ## Target-producing W11 rows -/

/-- Target route from uniform W11 no-early rows. -/
def windowNoEarlyMatrixRow :
    TargetProjectionRow (WindowNoEarlyRowsW11.NoEarlyMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    WindowNoEarlyClosureW11.no_minimalClearedFailure_of_noEarlyMatrix
    WindowNoEarlyClosureW11.targetLowerBoundEightThirtyOne_of_noEarlyMatrix

/-- Target route from uniform W11 no-start rows. -/
def windowNoStartMatrixRow :
    TargetProjectionRow (WindowNoEarlyRowsW11.NoStartMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    WindowNoEarlyClosureW11.no_minimalClearedFailure_of_noStartMatrix
    WindowNoEarlyClosureW11.targetLowerBoundEightThirtyOne_of_noStartMatrix

/-- Target route from uniform K23 obstruction rows. -/
def k23ObstructionW10RowsRow :
    TargetProjectionRow
      (K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    K23ClosureW11.K23RowFamily.no_minimalClearedFailure
    K23ClosureW11.K23RowFamily.targetLowerBoundEightThirtyOne

/-- Target route from uniform common-neighbor obstruction rows. -/
def commonNeighborObstructionW10RowsRow :
    TargetProjectionRow
      (K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    K23ClosureW11.CommonNeighborRowFamily.no_minimalClearedFailure
    K23ClosureW11.CommonNeighborRowFamily.targetLowerBoundEightThirtyOne

/-- Target route from refined checked closure inputs. -/
def minimalFailureCheckedInputsRow :
    TargetProjectionRow
      (MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u}) :=
  TargetProjectionRow.ofW10ProjectionRow
    MinimalFailureGeometryMatrixW11.checkedClosureInputFamilyRow

/-- Target route from narrow concrete closure inputs. -/
def minimalFailureNarrowInputsRow :
    TargetProjectionRow
      (MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u}) :=
  TargetProjectionRow.ofW10ProjectionRow
    MinimalFailureGeometryMatrixW11.narrowClosureInputFamilyRow

/-- Target route from uniform W11 geometry closure rows. -/
def minimalFailureGeometryClosureMatrixRow :
    TargetProjectionRow
      (MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u}) :=
  TargetProjectionRow.ofW11ProjectionRow
    MinimalFailureGeometryClosureW11.geometryClosureTargetProjectionRow

/-- Target route from W11 broken-lattice local E22/E23 rows. -/
def brokenLatticeE22E23LocalPredicateMatrixRow :
    TargetProjectionRow
      BrokenLatticeClosureW11.E22E23LocalPredicateMatrix :=
  TargetProjectionRow.ofNoMinimalAndTarget
    BrokenLatticeClosureW11.E22E23LocalPredicateMatrix.no_minimalClearedFailure
    BrokenLatticeClosureW11.E22E23LocalPredicateMatrix.targetLowerBoundEightThirtyOne

/-- Target route from W11 broken-lattice geometry E22/E23 rows. -/
def brokenLatticeGeometryE22E23PredicateMatrixRow :
    TargetProjectionRow
      (BrokenLatticeClosureW11.GeometryE22E23PredicateMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    BrokenLatticeClosureW11.GeometryE22E23PredicateMatrix.no_minimalClearedFailure
    BrokenLatticeClosureW11.GeometryE22E23PredicateMatrix.targetLowerBoundEightThirtyOne

/-- Target route from W11 broken-lattice direct-geometry rows. -/
def brokenLatticeDirectGeometryPredicateMatrixRow :
    TargetProjectionRow
      (BrokenLatticeClosureW11.DirectGeometryPredicateMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    BrokenLatticeClosureW11.DirectGeometryPredicateMatrix.no_minimalClearedFailure
    BrokenLatticeClosureW11.DirectGeometryPredicateMatrix.targetLowerBoundEightThirtyOne

/-- Target route from W11 broken-lattice K23-geometry rows. -/
def brokenLatticeK23GeometryPredicateMatrixRow :
    TargetProjectionRow
      (BrokenLatticeClosureW11.K23GeometryPredicateMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    BrokenLatticeClosureW11.K23GeometryPredicateMatrix.no_minimalClearedFailure
    BrokenLatticeClosureW11.K23GeometryPredicateMatrix.targetLowerBoundEightThirtyOne

/-- Target route from W11 broken-lattice common-neighbor geometry rows. -/
def brokenLatticeCommonNeighborGeometryPredicateMatrixRow :
    TargetProjectionRow
      (BrokenLatticeClosureW11.CommonNeighborGeometryPredicateMatrix.{u}) :=
  TargetProjectionRow.ofNoMinimalAndTarget
    BrokenLatticeClosureW11.CommonNeighborGeometryPredicateMatrix.no_minimalClearedFailure
    BrokenLatticeClosureW11.CommonNeighborGeometryPredicateMatrix.targetLowerBoundEightThirtyOne

/-- The target-producing portion of the integrated W11 ledger. -/
structure TargetRouteLedger : Type (u + 1) where
  targetClosureMatrix : TargetClosureMatrixW11.Matrix.{u}
  targetClosure : SwanepoelTargetClosureW11.Matrix.{u}
  w11Closure : SwanepoelW11ClosureMatrix.Matrix.{u}
  minimalFailureGeometryClosure : MinimalFailureGeometryClosureW11.Matrix.{u}
  minimalFailureGeometry : MinimalFailureGeometryMatrixW11.Matrix.{u}
  k23Closure : K23ClosureW11.Matrix.{u}
  brokenLatticeClosure : BrokenLatticeClosureW11.Matrix.{u}
  windowNoEarly :
    TargetProjectionRow (WindowNoEarlyRowsW11.NoEarlyMatrix.{u})
  windowNoStart :
    TargetProjectionRow (WindowNoEarlyRowsW11.NoStartMatrix.{u})
  k23ObstructionW10Rows :
    TargetProjectionRow
      (K23CommonNeighborW11.K23ObstructionW10RowFamily.{u})
  commonNeighborObstructionW10Rows :
    TargetProjectionRow
      (K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u})
  minimalFailureCheckedInputs :
    TargetProjectionRow
      (MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u})
  minimalFailureNarrowInputs :
    TargetProjectionRow
      (MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u})
  minimalFailureGeometryClosureRoute :
    TargetProjectionRow
      (MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u})
  brokenLatticeE22E23Local :
    TargetProjectionRow
      BrokenLatticeClosureW11.E22E23LocalPredicateMatrix
  brokenLatticeGeometryE22E23 :
    TargetProjectionRow
      (BrokenLatticeClosureW11.GeometryE22E23PredicateMatrix.{u})
  brokenLatticeDirectGeometry :
    TargetProjectionRow
      (BrokenLatticeClosureW11.DirectGeometryPredicateMatrix.{u})
  brokenLatticeK23Geometry :
    TargetProjectionRow
      (BrokenLatticeClosureW11.K23GeometryPredicateMatrix.{u})
  brokenLatticeCommonNeighborGeometry :
    TargetProjectionRow
      (BrokenLatticeClosureW11.CommonNeighborGeometryPredicateMatrix.{u})

/-- The checked target-route ledger assembled from the W11 modules. -/
def targetRouteLedger : TargetRouteLedger.{u} where
  targetClosureMatrix := TargetClosureMatrixW11.matrix
  targetClosure := SwanepoelTargetClosureW11.matrix
  w11Closure := SwanepoelW11ClosureMatrix.matrix
  minimalFailureGeometryClosure := MinimalFailureGeometryClosureW11.matrix
  minimalFailureGeometry := MinimalFailureGeometryMatrixW11.matrix
  k23Closure := K23ClosureW11.matrix
  brokenLatticeClosure := BrokenLatticeClosureW11.matrix
  windowNoEarly := windowNoEarlyMatrixRow
  windowNoStart := windowNoStartMatrixRow
  k23ObstructionW10Rows := k23ObstructionW10RowsRow
  commonNeighborObstructionW10Rows := commonNeighborObstructionW10RowsRow
  minimalFailureCheckedInputs := minimalFailureCheckedInputsRow
  minimalFailureNarrowInputs := minimalFailureNarrowInputsRow
  minimalFailureGeometryClosureRoute := minimalFailureGeometryClosureMatrixRow
  brokenLatticeE22E23Local :=
    brokenLatticeE22E23LocalPredicateMatrixRow
  brokenLatticeGeometryE22E23 :=
    brokenLatticeGeometryE22E23PredicateMatrixRow
  brokenLatticeDirectGeometry :=
    brokenLatticeDirectGeometryPredicateMatrixRow
  brokenLatticeK23Geometry :=
    brokenLatticeK23GeometryPredicateMatrixRow
  brokenLatticeCommonNeighborGeometry :=
    brokenLatticeCommonNeighborGeometryPredicateMatrixRow

/-! ## Integrated checked matrix -/

/-- Integrated W11 Swanepoel matrix.

The record stores checked projections and conditional target routes only. -/
structure Matrix : Type (u + 1) where
  fields : FieldProjectionLedger.{u}
  targets : TargetRouteLedger.{u}

/-- The integrated W11 matrix assembled from all checked W11 modules present
in this tree. -/
def matrix : Matrix.{u} where
  fields := fieldProjectionLedger
  targets := targetRouteLedger

/-! ## Explicit target projections -/

theorem targetLowerBoundEightThirtyOne_of_noEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u}) :
    Target :=
  windowNoEarlyMatrixRow.target M

theorem targetLowerBoundEightThirtyOne_of_noStartMatrix
    (M : WindowNoEarlyRowsW11.NoStartMatrix.{u}) :
    Target :=
  windowNoStartMatrixRow.target M

theorem targetLowerBoundEightThirtyOne_of_k23ObstructionW10Rows
    (H : K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}) :
    Target :=
  k23ObstructionW10RowsRow.target H

theorem targetLowerBoundEightThirtyOne_of_commonNeighborObstructionW10Rows
    (H : K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}) :
    Target :=
  commonNeighborObstructionW10RowsRow.target H

theorem targetLowerBoundEightThirtyOne_of_checkedClosureInputFamily
    (H : MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u}) :
    Target :=
  minimalFailureCheckedInputsRow.target H

theorem targetLowerBoundEightThirtyOne_of_narrowClosureInputFamily
    (H : MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u}) :
    Target :=
  minimalFailureNarrowInputsRow.target H

theorem targetLowerBoundEightThirtyOne_of_geometryClosureMatrix
    (M : MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u}) :
    Target :=
  minimalFailureGeometryClosureMatrixRow.target M

theorem targetLowerBoundEightThirtyOne_of_e22e23LocalPredicateMatrix
    (M : BrokenLatticeClosureW11.E22E23LocalPredicateMatrix) :
    Target :=
  brokenLatticeE22E23LocalPredicateMatrixRow.target M

theorem targetLowerBoundEightThirtyOne_of_geometryE22E23PredicateMatrix
    (M : BrokenLatticeClosureW11.GeometryE22E23PredicateMatrix.{u}) :
    Target :=
  brokenLatticeGeometryE22E23PredicateMatrixRow.target M

theorem targetLowerBoundEightThirtyOne_of_directGeometryPredicateMatrix
    (M : BrokenLatticeClosureW11.DirectGeometryPredicateMatrix.{u}) :
    Target :=
  brokenLatticeDirectGeometryPredicateMatrixRow.target M

theorem targetLowerBoundEightThirtyOne_of_k23GeometryPredicateMatrix
    (M : BrokenLatticeClosureW11.K23GeometryPredicateMatrix.{u}) :
    Target :=
  brokenLatticeK23GeometryPredicateMatrixRow.target M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborGeometryPredicateMatrix
    (M : BrokenLatticeClosureW11.CommonNeighborGeometryPredicateMatrix.{u}) :
    Target :=
  brokenLatticeCommonNeighborGeometryPredicateMatrixRow.target M

end

end SwanepoelW11IntegratedMatrix
end Swanepoel
end ErdosProblems1066
