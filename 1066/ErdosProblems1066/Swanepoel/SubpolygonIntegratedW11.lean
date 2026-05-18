import ErdosProblems1066.Swanepoel.SubpolygonClosureW11
import ErdosProblems1066.Swanepoel.SubpolygonFamilyW11
import ErdosProblems1066.Swanepoel.BoundaryAngleClosureW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 integrated subpolygon matrix

This module is a source-facing integration layer for the W11 subpolygon and
boundary-angle packages.

It keeps the still-supplied topology, concrete subpolygon cycle fields,
boundary labels, window containment, and selected no-early route as visible
fields.  The checked routes below only repackage those fields into the W11
geometry and target-closure facades already present in the Swanepoel stack.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonIntegratedW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetClosureMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetClosureMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetClosureMatrixW11.PipelineCleared

abbrev BoundaryInput (C : _root_.UDConfig n) :=
  BoundaryAngleClosureW11.BoundaryAngleClosureInput.{u} C

/-! ## Subpolygon field ledger -/

/-- Checked non-target projections supplied by the concrete subpolygon family
and the classified boundary route. -/
structure SubpolygonFieldLedger : Type (u + 1) where
  faceDataSummary :
    forall {n : Nat}
      {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
      {D : SubpolygonInstantiation.ExplicitOuterBoundaryFaceData.{u} G}
      (F : SubpolygonFamilyW11.SubpolygonFamilyPackage.{u} D),
        SubpolygonClosureW11.FaceData.ConcreteFamily.ObligationSummary F
  topologyFamilySummary :
    forall {n : Nat} {C : _root_.UDConfig n}
      (P : SubpolygonClosureW11.Topology.ConcreteFamilyPackage.{u} C),
        forall S : P.Subpolygon,
          6 <= 2 * (P.subpolygonCounts S).D2 +
            (P.subpolygonCounts S).D3
  boundaryRoute :
    forall {n : Nat} {C : _root_.UDConfig n},
      SubpolygonClosureW11.ClassifiedRoute.SubpolygonBoundaryPackage.{u}
        C ->
        SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C

/-- The checked subpolygon field ledger assembled from the W11 subpolygon
closure package. -/
def subpolygonFieldLedger : SubpolygonFieldLedger.{u} where
  faceDataSummary := fun F =>
    SubpolygonClosureW11.FaceData.ConcreteFamily.obligationSummary F
  topologyFamilySummary := fun P S =>
    P.lowDegree S
  boundaryRoute := fun P =>
    P.toW9TopologyAngleSubpolygonRow

/-! ## Pointwise rows into W11 geometry -/

/-- Direct geometry row sourced from concrete boundary-angle and subpolygon
data.  The label, containment, and direct no-start/no-early rows remain
separate fields over the same boundary source. -/
structure DirectBoundaryGeometryRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundary : BoundaryInput.{u} C
  labels :
    GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
      C hmin boundary.toGeometryTopologyAngleLongArcFields
  containment :
    GeometryRemainingFieldsW10.ContainmentFields
      (boundary.toGeometrySourceFields labels)
  noStartNoEarly :
    GeometryRemainingFieldsW10.NoStartNoEarlyFields
      (boundary.toGeometrySourceFields labels)

namespace DirectBoundaryGeometryRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget to the boundary-angle closure row. -/
def toBoundaryDirectGeometryRow
    (R : DirectBoundaryGeometryRow.{u} C hmin) :
    BoundaryAngleClosureW11.BoundaryDirectGeometryRow.{u} C hmin where
  boundary := R.boundary
  labels := R.labels
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

/-- Forget to the W10 direct geometry package. -/
def toDirectGeometryPackage
    (R : DirectBoundaryGeometryRow.{u} C hmin) :
    GeometryRemainingFieldsW10.DirectGeometryPackage.{u} C hmin :=
  R.toBoundaryDirectGeometryRow.toDirectGeometryPackage

/-- Route to the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : DirectBoundaryGeometryRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.toBoundaryDirectGeometryRow.toGeometryClosureRow

/-- A completed direct row closes the fixed minimal failure. -/
theorem contradiction
    (R : DirectBoundaryGeometryRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end DirectBoundaryGeometryRow

/-- K23 geometry row sourced from concrete boundary-angle and subpolygon data.
The K23 no-early field is kept explicit. -/
structure K23BoundaryGeometryRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundary : BoundaryInput.{u} C
  labels :
    GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
      C hmin boundary.toGeometryTopologyAngleLongArcFields
  containment :
    GeometryRemainingFieldsW10.ContainmentFields
      (boundary.toGeometrySourceFields labels)
  k23NoEarly :
    GeometryRemainingFieldsW10.K23NoEarlyFields
      (boundary.toGeometrySourceFields labels)

namespace K23BoundaryGeometryRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget to the boundary-angle closure row. -/
def toBoundaryK23GeometryRow
    (R : K23BoundaryGeometryRow.{u} C hmin) :
    BoundaryAngleClosureW11.BoundaryK23GeometryRow.{u} C hmin where
  boundary := R.boundary
  labels := R.labels
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- Forget to the W10 K23 geometry package. -/
def toK23GeometryPackage
    (R : K23BoundaryGeometryRow.{u} C hmin) :
    GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin :=
  R.toBoundaryK23GeometryRow.toK23GeometryPackage

/-- Route to the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : K23BoundaryGeometryRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.toBoundaryK23GeometryRow.toGeometryClosureRow

/-- A completed K23 row closes the fixed minimal failure. -/
theorem contradiction
    (R : K23BoundaryGeometryRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end K23BoundaryGeometryRow

/-- Common-neighbor geometry row sourced from concrete boundary-angle and
subpolygon data.  The common-neighbor no-early field is kept explicit. -/
structure CommonNeighborBoundaryGeometryRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundary : BoundaryInput.{u} C
  labels :
    GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
      C hmin boundary.toGeometryTopologyAngleLongArcFields
  containment :
    GeometryRemainingFieldsW10.ContainmentFields
      (boundary.toGeometrySourceFields labels)
  commonNeighborNoEarly :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
      (boundary.toGeometrySourceFields labels)

namespace CommonNeighborBoundaryGeometryRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget to the boundary-angle closure row. -/
def toBoundaryCommonNeighborGeometryRow
    (R : CommonNeighborBoundaryGeometryRow.{u} C hmin) :
    BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryRow.{u}
      C hmin where
  boundary := R.boundary
  labels := R.labels
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Forget to the W10 common-neighbor geometry package. -/
def toCommonNeighborGeometryPackage
    (R : CommonNeighborBoundaryGeometryRow.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u} C hmin :=
  R.toBoundaryCommonNeighborGeometryRow.toCommonNeighborGeometryPackage

/-- Route to the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : CommonNeighborBoundaryGeometryRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.toBoundaryCommonNeighborGeometryRow.toGeometryClosureRow

/-- A completed common-neighbor row closes the fixed minimal failure. -/
theorem contradiction
    (R : CommonNeighborBoundaryGeometryRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end CommonNeighborBoundaryGeometryRow

/-! ## Uniform matrices -/

/-- Uniform direct rows for every minimal cleared failure. -/
structure DirectBoundaryGeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectBoundaryGeometryRow.{u} C hmin

namespace DirectBoundaryGeometryMatrix

/-- Forget to the boundary-angle closure matrix. -/
def toBoundaryDirectGeometryMatrix
    (M : DirectBoundaryGeometryMatrix.{u}) :
    BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBoundaryDirectGeometryRow

/-- Forget to the W10 direct geometry matrix. -/
def toW10DirectGeometryMatrix
    (M : DirectBoundaryGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u} :=
  M.toBoundaryDirectGeometryMatrix.toW10DirectGeometryMatrix

/-- Route to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : DirectBoundaryGeometryMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} :=
  M.toBoundaryDirectGeometryMatrix.toW11GeometryClosureMatrix

/-- Direct boundary rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : DirectBoundaryGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetClosureMatrixW11.directGeometryW10Row.noMinimal
    M.toW10DirectGeometryMatrix

/-- Direct boundary rows clear the target pipeline. -/
theorem pipelineCleared
    (M : DirectBoundaryGeometryMatrix.{u}) :
    PipelineCleared :=
  TargetClosureMatrixW11.directGeometryW10Row.pipeline
    M.toW10DirectGeometryMatrix

/-- Direct boundary rows reach the target closure facade. -/
theorem targetLowerBoundEightThirtyOne
    (M : DirectBoundaryGeometryMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.directGeometryW10Row.target
    M.toW10DirectGeometryMatrix

end DirectBoundaryGeometryMatrix

/-- Uniform K23 rows for every minimal cleared failure. -/
structure K23BoundaryGeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23BoundaryGeometryRow.{u} C hmin

namespace K23BoundaryGeometryMatrix

/-- Forget to the boundary-angle closure matrix. -/
def toBoundaryK23GeometryMatrix
    (M : K23BoundaryGeometryMatrix.{u}) :
    BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBoundaryK23GeometryRow

/-- Forget to the W10 K23 geometry matrix. -/
def toW10K23GeometryMatrix
    (M : K23BoundaryGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} :=
  M.toBoundaryK23GeometryMatrix.toW10K23GeometryMatrix

/-- Route to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : K23BoundaryGeometryMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} :=
  M.toBoundaryK23GeometryMatrix.toW11GeometryClosureMatrix

/-- K23 boundary rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : K23BoundaryGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetClosureMatrixW11.k23GeometryW10Row.noMinimal
    M.toW10K23GeometryMatrix

/-- K23 boundary rows clear the target pipeline. -/
theorem pipelineCleared
    (M : K23BoundaryGeometryMatrix.{u}) :
    PipelineCleared :=
  TargetClosureMatrixW11.k23GeometryW10Row.pipeline
    M.toW10K23GeometryMatrix

/-- K23 boundary rows reach the target closure facade. -/
theorem targetLowerBoundEightThirtyOne
    (M : K23BoundaryGeometryMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.k23GeometryW10Row.target
    M.toW10K23GeometryMatrix

end K23BoundaryGeometryMatrix

/-- Uniform common-neighbor rows for every minimal cleared failure. -/
structure CommonNeighborBoundaryGeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborBoundaryGeometryRow.{u} C hmin

namespace CommonNeighborBoundaryGeometryMatrix

/-- Forget to the boundary-angle closure matrix. -/
def toBoundaryCommonNeighborGeometryMatrix
    (M : CommonNeighborBoundaryGeometryMatrix.{u}) :
    BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBoundaryCommonNeighborGeometryRow

/-- Forget to the W10 common-neighbor geometry matrix. -/
def toW10CommonNeighborGeometryMatrix
    (M : CommonNeighborBoundaryGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} :=
  M.toBoundaryCommonNeighborGeometryMatrix.toW10CommonNeighborGeometryMatrix

/-- Route to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : CommonNeighborBoundaryGeometryMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} :=
  M.toBoundaryCommonNeighborGeometryMatrix.toW11GeometryClosureMatrix

/-- Common-neighbor boundary rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : CommonNeighborBoundaryGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetClosureMatrixW11.commonNeighborGeometryW10Row.noMinimal
    M.toW10CommonNeighborGeometryMatrix

/-- Common-neighbor boundary rows clear the target pipeline. -/
theorem pipelineCleared
    (M : CommonNeighborBoundaryGeometryMatrix.{u}) :
    PipelineCleared :=
  TargetClosureMatrixW11.commonNeighborGeometryW10Row.pipeline
    M.toW10CommonNeighborGeometryMatrix

/-- Common-neighbor boundary rows reach the target closure facade. -/
theorem targetLowerBoundEightThirtyOne
    (M : CommonNeighborBoundaryGeometryMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.commonNeighborGeometryW10Row.target
    M.toW10CommonNeighborGeometryMatrix

end CommonNeighborBoundaryGeometryMatrix

/-! ## Integrated matrix -/

/-- Integrated subpolygon route matrix.

The matrix stores routes only.  It still requires explicit source matrices
whose rows contain topology, concrete subpolygon fields, boundary labels,
window containment, and one selected no-early route. -/
structure Matrix : Type (u + 3) where
  fields : SubpolygonFieldLedger.{u}
  targetClosure : TargetClosureMatrixW11.Matrix.{u}
  directToBoundaryClosure :
    DirectBoundaryGeometryMatrix.{u} ->
      BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.{u}
  k23ToBoundaryClosure :
    K23BoundaryGeometryMatrix.{u} ->
      BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.{u}
  commonNeighborToBoundaryClosure :
    CommonNeighborBoundaryGeometryMatrix.{u} ->
      BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.{u}
  directNoMinimal :
    DirectBoundaryGeometryMatrix.{u} -> MinimalFailureExclusion
  k23NoMinimal :
    K23BoundaryGeometryMatrix.{u} -> MinimalFailureExclusion
  commonNeighborNoMinimal :
    CommonNeighborBoundaryGeometryMatrix.{u} -> MinimalFailureExclusion
  directPipeline :
    DirectBoundaryGeometryMatrix.{u} -> PipelineCleared
  k23Pipeline :
    K23BoundaryGeometryMatrix.{u} -> PipelineCleared
  commonNeighborPipeline :
    CommonNeighborBoundaryGeometryMatrix.{u} -> PipelineCleared
  directTarget :
    DirectBoundaryGeometryMatrix.{u} -> Target
  k23Target :
    K23BoundaryGeometryMatrix.{u} -> Target
  commonNeighborTarget :
    CommonNeighborBoundaryGeometryMatrix.{u} -> Target

/-- The checked integrated W11 subpolygon matrix. -/
def matrix : Matrix.{u} where
  fields := subpolygonFieldLedger
  targetClosure := TargetClosureMatrixW11.matrix
  directToBoundaryClosure :=
    DirectBoundaryGeometryMatrix.toBoundaryDirectGeometryMatrix
  k23ToBoundaryClosure :=
    K23BoundaryGeometryMatrix.toBoundaryK23GeometryMatrix
  commonNeighborToBoundaryClosure :=
    CommonNeighborBoundaryGeometryMatrix.toBoundaryCommonNeighborGeometryMatrix
  directNoMinimal := DirectBoundaryGeometryMatrix.no_minimalClearedFailure
  k23NoMinimal := K23BoundaryGeometryMatrix.no_minimalClearedFailure
  commonNeighborNoMinimal :=
    CommonNeighborBoundaryGeometryMatrix.no_minimalClearedFailure
  directPipeline := DirectBoundaryGeometryMatrix.pipelineCleared
  k23Pipeline := K23BoundaryGeometryMatrix.pipelineCleared
  commonNeighborPipeline :=
    CommonNeighborBoundaryGeometryMatrix.pipelineCleared
  directTarget :=
    DirectBoundaryGeometryMatrix.targetLowerBoundEightThirtyOne
  k23Target :=
    K23BoundaryGeometryMatrix.targetLowerBoundEightThirtyOne
  commonNeighborTarget :=
    CommonNeighborBoundaryGeometryMatrix.targetLowerBoundEightThirtyOne

/-! ## Public projections -/

theorem no_minimalClearedFailure_of_directBoundaryGeometryMatrix
    (M : DirectBoundaryGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.directNoMinimal M

theorem targetLowerBoundEightThirtyOne_of_directBoundaryGeometryMatrix
    (M : DirectBoundaryGeometryMatrix.{u}) :
    Target :=
  matrix.directTarget M

theorem no_minimalClearedFailure_of_k23BoundaryGeometryMatrix
    (M : K23BoundaryGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.k23NoMinimal M

theorem targetLowerBoundEightThirtyOne_of_k23BoundaryGeometryMatrix
    (M : K23BoundaryGeometryMatrix.{u}) :
    Target :=
  matrix.k23Target M

theorem no_minimalClearedFailure_of_commonNeighborBoundaryGeometryMatrix
    (M : CommonNeighborBoundaryGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.commonNeighborNoMinimal M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborBoundaryGeometryMatrix
    (M : CommonNeighborBoundaryGeometryMatrix.{u}) :
    Target :=
  matrix.commonNeighborTarget M

end

end SubpolygonIntegratedW11
end Swanepoel
end ErdosProblems1066
