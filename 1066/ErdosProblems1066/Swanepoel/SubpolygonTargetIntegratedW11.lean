import ErdosProblems1066.Swanepoel.SubpolygonIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryAngleIntegratedW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Target-facing W11 subpolygon integration

This module keeps the subpolygon route, boundary labels, window containment,
and selected no-early alternative visible up to the Swanepoel target facade.

The public target projections below are all conditional on uniform explicit
input matrices.  The file does not provide those matrices.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonTargetIntegratedW11

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

abbrev SubpolygonRoute (C : _root_.UDConfig n) :=
  SubpolygonClosureW11.ClassifiedRoute.SubpolygonBoundaryPackage.{u} C

/-! ## Subpolygon route prefix -/

namespace SubpolygonRoute

variable {C : _root_.UDConfig n}

/-- The topology component selected by the explicit subpolygon route. -/
def toW10TopologyComponentFields
    (P : SubpolygonRoute.{u} C) :
    MinimalFailureDirectMatrixW10.TopologyComponentFields C where
  topology := P.topology

/-- The cycle, count, angle, and long-arc component selected by the same
subpolygon route. -/
def toW10PartitionAngleComponentFields
    (P : SubpolygonRoute.{u} C) :
    MinimalFailureDirectMatrixW10.PartitionAngleComponentFields.{u}
      C P.toW10TopologyComponentFields where
  outerAngleBounds := P.boundary.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.toBoundaryAngleTurnTopologyPackage.w9LongArc

/-- The W9 topology/angle/subpolygon row obtained from the explicit route. -/
def toTopologyAngleSubpolygonRow
    (P : SubpolygonRoute.{u} C) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  P.toW9TopologyAngleSubpolygonRow

/-- The explicit subpolygon cycle/count/angle datum. -/
def cycleData
    (P : SubpolygonRoute.{u} C) (S : P.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  P.subpolygonData S

/-- The checked E13 low-degree conclusion for a supplied subpolygon cycle. -/
theorem cycle_lowDegree
    (P : SubpolygonRoute.{u} C) (S : P.Subpolygon) :
    6 <= 2 * (P.cycleData S).counts.D2 +
      (P.cycleData S).counts.D3 :=
  P.lowDegree S

end SubpolygonRoute

/-- Explicit subpolygon topology/cycle data plus matching boundary labels. -/
structure SubpolygonLabelPrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  route : SubpolygonRoute.{u} C
  labels :
    BoundaryLabelRowsW11.BoundaryLabelRowPackage.{u}
      C hmin route.toW10TopologyComponentFields
        route.toW10PartitionAngleComponentFields

namespace SubpolygonLabelPrefix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The boundary-label base prefix used by the no-early and geometry rows. -/
def toLabelBasePrefix
    (P : SubpolygonLabelPrefix.{u} C hmin) :
    BoundaryLabelRowsW11.BoundaryLabelRowPackage.BasePrefix.{u}
      C hmin where
  topology := P.route.toW10TopologyComponentFields
  partitionAngle := P.route.toW10PartitionAngleComponentFields
  labels := P.labels

/-- The same prefix in the boundary-label closure spelling. -/
def toClosureLabelPrefix
    (P : SubpolygonLabelPrefix.{u} C hmin) :
    BoundaryLabelClosureW11.LabelBasePrefix.{u} C hmin :=
  P.toLabelBasePrefix

/-- The W9 base row after adding the explicit labels. -/
def toW9BaseRow
    (P : SubpolygonLabelPrefix.{u} C hmin) :
    SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin :=
  P.toLabelBasePrefix.toW10BaseRow

/-- The W10 geometry source row selected by the same subpolygon and labels. -/
def toGeometrySourceFields
    (P : SubpolygonLabelPrefix.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  P.toClosureLabelPrefix.toGeometrySourceFields

/-- The topology/angle/subpolygon row remains the one carried by the route. -/
def toTopologyAngleSubpolygonRow
    (P : SubpolygonLabelPrefix.{u} C hmin) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  P.route.toTopologyAngleSubpolygonRow

/-- The displayed subpolygon index type. -/
def Subpolygon (P : SubpolygonLabelPrefix.{u} C hmin) : Type u :=
  P.route.Subpolygon

/-- The displayed cycle/count/angle datum over one subpolygon. -/
def cycleData
    (P : SubpolygonLabelPrefix.{u} C hmin) (S : P.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  P.route.cycleData S

/-- Low-degree conclusion retained with the displayed cycle data. -/
theorem cycle_lowDegree
    (P : SubpolygonLabelPrefix.{u} C hmin) (S : P.Subpolygon) :
    6 <= 2 * (P.cycleData S).counts.D2 +
      (P.cycleData S).counts.D3 :=
  P.route.cycle_lowDegree S

/-- The checked outer-boundary E12 count route retained from the boundary
angle package. -/
theorem boundaryAngleCount
    (P : SubpolygonLabelPrefix.{u} C hmin) :
    P.route.classification.counts.d5 +
          2 * P.route.classification.counts.d6 +
        P.route.classification.counts.b +
          P.route.classification.counts.B + 6 <=
      P.route.classification.counts.d3 :=
  P.route.boundaryAngleCount

end SubpolygonLabelPrefix

/-! ## Pointwise target-facing rows -/

/-- Direct row: explicit subpolygon prefix, labels, containment, and
five-start no-early data. -/
structure DirectRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labelPrefix : SubpolygonLabelPrefix.{u} C hmin
  window :
    GeometryRemainingFieldsW10.ContainmentFields
      labelPrefix.toGeometrySourceFields
  noStartNoEarly :
    GeometryRemainingFieldsW10.NoStartNoEarlyFields
      labelPrefix.toGeometrySourceFields

namespace DirectRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Window row selected by the direct explicit fields. -/
def toWindowRow
    (R : DirectRow.{u} C hmin) :
    WindowNoEarlyRowsW11.WindowRow.{u} C hmin where
  base := R.labelPrefix.toGeometrySourceFields.toW9BaseRow
  windowFields := R.window.localContainment

/-- Concrete no-early data induced by the five no-start fields. -/
def noEarly
    (R : DirectRow.{u} C hmin) :=
  R.noStartNoEarly.noEarly

/-- W11 no-start row selected by the direct explicit fields. -/
def toNoStartRow
    (R : DirectRow.{u} C hmin) :
    WindowNoEarlyRowsW11.NoStartRow.{u} C hmin where
  window := R.toWindowRow
  noStart := R.noStartNoEarly.noStart

/-- W11 no-early row selected by the direct explicit fields. -/
def toNoEarlyRow
    (R : DirectRow.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toNoStartRow.toNoEarlyRow

/-- Forget to the W10 direct geometry package. -/
def toDirectGeometryPackage
    (R : DirectRow.{u} C hmin) :
    GeometryRemainingFieldsW10.DirectGeometryPackage.{u} C hmin where
  source := R.labelPrefix.toGeometrySourceFields
  containment := R.window
  noStartNoEarly := R.noStartNoEarly

/-- Route to the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : DirectRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofDirectGeometryPackage
    R.toDirectGeometryPackage

/-- Narrow concrete closure input induced by this row. -/
def toNarrowClosureInput
    (R : DirectRow.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toGeometryClosureRow.toConcreteObligations

/-- A fixed direct row closes its minimal failure. -/
theorem contradiction
    (R : DirectRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end DirectRow

/-- K23 row: explicit subpolygon prefix, labels, containment, and K23
no-early data. -/
structure K23Row
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labelPrefix : SubpolygonLabelPrefix.{u} C hmin
  window :
    GeometryRemainingFieldsW10.ContainmentFields
      labelPrefix.toGeometrySourceFields
  k23NoEarly :
    GeometryRemainingFieldsW10.K23NoEarlyFields
      labelPrefix.toGeometrySourceFields

namespace K23Row

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Window row selected by the K23 explicit fields. -/
def toWindowRow
    (R : K23Row.{u} C hmin) :
    WindowNoEarlyRowsW11.WindowRow.{u} C hmin where
  base := R.labelPrefix.toGeometrySourceFields.toW9BaseRow
  windowFields := R.window.localContainment

/-- Concrete no-early data obtained from the K23 obstruction. -/
def noEarly
    (R : K23Row.{u} C hmin) :=
  R.k23NoEarly.noEarly

/-- W11 no-early row selected by the K23 explicit fields. -/
def toNoEarlyRow
    (R : K23Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin where
  window := R.toWindowRow
  noEarly := R.k23NoEarly.noEarly

/-- Forget to the W10 K23 geometry package. -/
def toK23GeometryPackage
    (R : K23Row.{u} C hmin) :
    GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin where
  source := R.labelPrefix.toGeometrySourceFields
  containment := R.window
  k23NoEarly := R.k23NoEarly

/-- Route to the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : K23Row.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofK23GeometryPackage
    R.toK23GeometryPackage

/-- A fixed K23 row closes its minimal failure. -/
theorem contradiction
    (R : K23Row.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end K23Row

/-- Common-neighbor row: explicit subpolygon prefix, labels, containment, and
common-neighbor no-early data. -/
structure CommonNeighborRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labelPrefix : SubpolygonLabelPrefix.{u} C hmin
  window :
    GeometryRemainingFieldsW10.ContainmentFields
      labelPrefix.toGeometrySourceFields
  commonNeighborNoEarly :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
      labelPrefix.toGeometrySourceFields

namespace CommonNeighborRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Window row selected by the common-neighbor explicit fields. -/
def toWindowRow
    (R : CommonNeighborRow.{u} C hmin) :
    WindowNoEarlyRowsW11.WindowRow.{u} C hmin where
  base := R.labelPrefix.toGeometrySourceFields.toW9BaseRow
  windowFields := R.window.localContainment

/-- Concrete no-early data obtained from the common-neighbor obstruction. -/
def noEarly
    (R : CommonNeighborRow.{u} C hmin) :=
  R.commonNeighborNoEarly.noEarly

/-- W11 no-early row selected by the common-neighbor explicit fields. -/
def toNoEarlyRow
    (R : CommonNeighborRow.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin where
  window := R.toWindowRow
  noEarly := R.commonNeighborNoEarly.noEarly

/-- Forget to the W10 common-neighbor geometry package. -/
def toCommonNeighborGeometryPackage
    (R : CommonNeighborRow.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u}
      C hmin where
  source := R.labelPrefix.toGeometrySourceFields
  containment := R.window
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Route to the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : CommonNeighborRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofCommonNeighborGeometryPackage
    R.toCommonNeighborGeometryPackage

/-- A fixed common-neighbor row closes its minimal failure. -/
theorem contradiction
    (R : CommonNeighborRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end CommonNeighborRow

/-! ## Uniform explicit matrices -/

/-- Uniform direct rows for every minimal cleared failure. -/
structure DirectMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectRow.{u} C hmin

namespace DirectMatrix

/-- Forget to the W10 direct geometry matrix. -/
def toW10DirectGeometryMatrix
    (M : DirectMatrix.{u}) :
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectGeometryPackage

/-- Route to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : DirectMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Forget to checked W11 no-start rows. -/
def toNoStartMatrix
    (M : DirectMatrix.{u}) :
    WindowNoEarlyRowsW11.NoStartMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toNoStartRow

/-- Forget to checked W11 no-early rows. -/
def toNoEarlyMatrix
    (M : DirectMatrix.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} :=
  M.toNoStartMatrix.toNoEarlyMatrix

/-- Direct explicit rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : DirectMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetClosureMatrixW11.directGeometryW10Row.noMinimal
    M.toW10DirectGeometryMatrix

/-- Direct explicit rows clear the target pipeline. -/
theorem pipelineCleared
    (M : DirectMatrix.{u}) :
    PipelineCleared :=
  TargetClosureMatrixW11.directGeometryW10Row.pipeline
    M.toW10DirectGeometryMatrix

/-- Conditional Swanepoel target projection from direct explicit rows. -/
theorem targetClosure
    (M : DirectMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.directGeometryW10Row.target
    M.toW10DirectGeometryMatrix

end DirectMatrix

/-- Uniform K23 rows for every minimal cleared failure. -/
structure K23Matrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23Row.{u} C hmin

namespace K23Matrix

/-- Forget to the W10 K23 geometry matrix. -/
def toW10K23GeometryMatrix
    (M : K23Matrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPackage

/-- Route to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : K23Matrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Forget to checked W11 no-early rows. -/
def toNoEarlyMatrix
    (M : K23Matrix.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toNoEarlyRow

/-- K23 explicit rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : K23Matrix.{u}) :
    MinimalFailureExclusion :=
  TargetClosureMatrixW11.k23GeometryW10Row.noMinimal
    M.toW10K23GeometryMatrix

/-- K23 explicit rows clear the target pipeline. -/
theorem pipelineCleared
    (M : K23Matrix.{u}) :
    PipelineCleared :=
  TargetClosureMatrixW11.k23GeometryW10Row.pipeline
    M.toW10K23GeometryMatrix

/-- Conditional Swanepoel target projection from K23 explicit rows. -/
theorem targetClosure
    (M : K23Matrix.{u}) :
    Target :=
  TargetClosureMatrixW11.k23GeometryW10Row.target
    M.toW10K23GeometryMatrix

end K23Matrix

/-- Uniform common-neighbor rows for every minimal cleared failure. -/
structure CommonNeighborMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborRow.{u} C hmin

namespace CommonNeighborMatrix

/-- Forget to the W10 common-neighbor geometry matrix. -/
def toW10CommonNeighborGeometryMatrix
    (M : CommonNeighborMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborGeometryPackage

/-- Route to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : CommonNeighborMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Forget to checked W11 no-early rows. -/
def toNoEarlyMatrix
    (M : CommonNeighborMatrix.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toNoEarlyRow

/-- Common-neighbor explicit rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : CommonNeighborMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetClosureMatrixW11.commonNeighborGeometryW10Row.noMinimal
    M.toW10CommonNeighborGeometryMatrix

/-- Common-neighbor explicit rows clear the target pipeline. -/
theorem pipelineCleared
    (M : CommonNeighborMatrix.{u}) :
    PipelineCleared :=
  TargetClosureMatrixW11.commonNeighborGeometryW10Row.pipeline
    M.toW10CommonNeighborGeometryMatrix

/-- Conditional Swanepoel target projection from common-neighbor explicit
rows. -/
theorem targetClosure
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.commonNeighborGeometryW10Row.target
    M.toW10CommonNeighborGeometryMatrix

end CommonNeighborMatrix

/-! ## Target route ledger -/

/-- Checked conditional routes from the explicit subpolygon matrices. -/
structure TargetRows : Type (u + 1) where
  direct :
    TargetClosureMatrixW11.TargetProjectionRow (DirectMatrix.{u})
  k23 :
    TargetClosureMatrixW11.TargetProjectionRow (K23Matrix.{u})
  commonNeighbor :
    TargetClosureMatrixW11.TargetProjectionRow (CommonNeighborMatrix.{u})

/-- Target rows assembled from the W10/W11 target closure matrix. -/
def targetRows : TargetRows.{u} where
  direct := {
    noMinimal := DirectMatrix.no_minimalClearedFailure
    pipeline := DirectMatrix.pipelineCleared
    target := DirectMatrix.targetClosure
  }
  k23 := {
    noMinimal := K23Matrix.no_minimalClearedFailure
    pipeline := K23Matrix.pipelineCleared
    target := K23Matrix.targetClosure
  }
  commonNeighbor := {
    noMinimal := CommonNeighborMatrix.no_minimalClearedFailure
    pipeline := CommonNeighborMatrix.pipelineCleared
    target := CommonNeighborMatrix.targetClosure
  }

/-- Integrated target-facing subpolygon ledger.

The imported matrices are route ledgers only.  The `targetRows` field still
requires an explicit uniform source matrix before any target conclusion can be
projected. -/
structure Matrix : Type (u + 3) where
  subpolygonIntegrated : SubpolygonIntegratedW11.Matrix.{u}
  boundaryAngleIntegrated : BoundaryAngleIntegratedW11.Matrix.{u}
  targetClosure : TargetClosureMatrixW11.Matrix.{u}
  routes : TargetRows.{u}

/-- The checked target-facing subpolygon integration ledger. -/
def matrix : Matrix.{u} where
  subpolygonIntegrated := SubpolygonIntegratedW11.matrix
  boundaryAngleIntegrated := BoundaryAngleIntegratedW11.matrix
  targetClosure := TargetClosureMatrixW11.matrix
  routes := targetRows

/-! ## Public conditional projections -/

theorem no_minimalClearedFailure_of_directMatrix
    (M : DirectMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.routes.direct.noMinimal M

theorem pipelineCleared_of_directMatrix
    (M : DirectMatrix.{u}) :
    PipelineCleared :=
  matrix.routes.direct.pipeline M

theorem targetClosure_of_directMatrix
    (M : DirectMatrix.{u}) :
    Target :=
  matrix.routes.direct.target M

theorem no_minimalClearedFailure_of_k23Matrix
    (M : K23Matrix.{u}) :
    MinimalFailureExclusion :=
  matrix.routes.k23.noMinimal M

theorem pipelineCleared_of_k23Matrix
    (M : K23Matrix.{u}) :
    PipelineCleared :=
  matrix.routes.k23.pipeline M

theorem targetClosure_of_k23Matrix
    (M : K23Matrix.{u}) :
    Target :=
  matrix.routes.k23.target M

theorem no_minimalClearedFailure_of_commonNeighborMatrix
    (M : CommonNeighborMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.routes.commonNeighbor.noMinimal M

theorem pipelineCleared_of_commonNeighborMatrix
    (M : CommonNeighborMatrix.{u}) :
    PipelineCleared :=
  matrix.routes.commonNeighbor.pipeline M

theorem targetClosure_of_commonNeighborMatrix
    (M : CommonNeighborMatrix.{u}) :
    Target :=
  matrix.routes.commonNeighbor.target M

end

end SubpolygonTargetIntegratedW11
end Swanepoel
end ErdosProblems1066
