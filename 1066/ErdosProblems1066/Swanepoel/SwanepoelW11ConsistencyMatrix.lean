import ErdosProblems1066.Swanepoel.SwanepoelW11IntegratedMatrix
import ErdosProblems1066.Swanepoel.BoundaryAngleClosureW11
import ErdosProblems1066.Swanepoel.BoundaryLabelClosureW11
import ErdosProblems1066.Swanepoel.TopologyClosureW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11
import ErdosProblems1066.Swanepoel.BoundaryAngleIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryLabelIntegratedW11
import ErdosProblems1066.Swanepoel.BrokenLatticeIntegratedW11
import ErdosProblems1066.Swanepoel.BrokenLatticeTargetIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryIntegratedW11
import ErdosProblems1066.Swanepoel.K23IntegratedMatrixW11
import ErdosProblems1066.Swanepoel.K23TargetIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyIntegratedW11
import ErdosProblems1066.Swanepoel.NoEarlyTargetIntegratedW11
import ErdosProblems1066.Swanepoel.SubpolygonIntegratedW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Swanepoel W11 consistency matrix

This file imports the checked W11 closure and integrated ledgers that currently
coexist.  It stores only conditional routes from explicit source packages, and
it records the integrated topology module as a checked blocker rather than
importing a failing module.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW11ConsistencyMatrix

universe u v

noncomputable section

abbrev Target : Prop :=
  TargetClosureMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetClosureMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetClosureMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  BrokenLatticeIntegratedW11.MinimalFailureEliminator

/-! ## Shared route shapes -/

/-- A conditional target route from an explicit input package. -/
structure TargetRoute (alpha : Sort v) : Sort (max 1 v) where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace TargetRoute

/-- Reuse a target-closure row in the consistency matrix. -/
def ofTargetClosureRow
    {alpha : Sort v}
    (R : TargetClosureMatrixW11.TargetProjectionRow alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse a Swanepoel integrated row in the consistency matrix. -/
def ofSwanepoelIntegratedRow
    {alpha : Sort v}
    (R : SwanepoelW11IntegratedMatrix.TargetProjectionRow alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end TargetRoute

/-! ## Closure-file routes -/

/-- Target route from boundary-angle closure direct geometry matrices. -/
def boundaryAngleClosureDirectRoute :
    TargetRoute (BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.{u}) where
  noMinimal := fun M =>
    TargetClosureMatrixW11.directGeometryW10Row.noMinimal
      (BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.toW10DirectGeometryMatrix
        M)
  pipeline := fun M =>
    TargetClosureMatrixW11.directGeometryW10Row.pipeline
      (BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.toW10DirectGeometryMatrix
        M)
  target := fun M =>
    TargetClosureMatrixW11.directGeometryW10Row.target
      (BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.toW10DirectGeometryMatrix
        M)

/-- Target route from boundary-angle closure K23 geometry matrices. -/
def boundaryAngleClosureK23Route :
    TargetRoute (BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.{u}) where
  noMinimal := fun M =>
    TargetClosureMatrixW11.k23GeometryW10Row.noMinimal
      (BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.toW10K23GeometryMatrix
        M)
  pipeline := fun M =>
    TargetClosureMatrixW11.k23GeometryW10Row.pipeline
      (BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.toW10K23GeometryMatrix
        M)
  target := fun M =>
    TargetClosureMatrixW11.k23GeometryW10Row.target
      (BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.toW10K23GeometryMatrix
        M)

/-- Target route from boundary-angle closure common-neighbor geometry
matrices. -/
def boundaryAngleClosureCommonNeighborRoute :
    TargetRoute
      (BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.{u}) where
  noMinimal := fun M =>
    TargetClosureMatrixW11.commonNeighborGeometryW10Row.noMinimal
      (BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.toW10CommonNeighborGeometryMatrix
        M)
  pipeline := fun M =>
    TargetClosureMatrixW11.commonNeighborGeometryW10Row.pipeline
      (BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.toW10CommonNeighborGeometryMatrix
        M)
  target := fun M =>
    TargetClosureMatrixW11.commonNeighborGeometryW10Row.target
      (BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.toW10CommonNeighborGeometryMatrix
        M)

/-- Target route from boundary-label closure matrices. -/
def boundaryLabelClosureRoute :
    TargetRoute (BoundaryLabelClosureW11.Matrix.{u}) where
  noMinimal := BoundaryLabelClosureW11.Matrix.no_minimalClearedFailure
  pipeline := fun M =>
    TargetClosureMatrixW11.noEarlyMatrixRow.pipeline M.toNoEarlyMatrix
  target := BoundaryLabelClosureW11.Matrix.targetLowerBoundEightThirtyOne

/-! ## Imported W11 ledgers -/

/-- Closure files and their route ledgers that typecheck together. -/
structure ClosureLedgers where
  topologyClosure : TopologyClosureW11.Matrix.{u}
  boundaryLabelClosure : BoundaryLabelClosureW11.RouteMatrix.{u}
  targetClosure : TargetClosureMatrixW11.Matrix.{u}
  swanepoelIntegrated : SwanepoelW11IntegratedMatrix.Matrix.{u}
  swanepoelFieldProjections :
    SwanepoelW11IntegratedMatrix.FieldProjectionLedger.{u}

/-- Checked closure-file ledgers. -/
def closureLedgers : ClosureLedgers where
  topologyClosure := TopologyClosureW11.matrix
  boundaryLabelClosure := BoundaryLabelClosureW11.routeMatrix
  targetClosure := TargetClosureMatrixW11.matrix
  swanepoelIntegrated := SwanepoelW11IntegratedMatrix.matrix
  swanepoelFieldProjections :=
    SwanepoelW11IntegratedMatrix.fieldProjectionLedger

/-- Integrated modules that typecheck together in this checkout. -/
structure IntegratedLedgers where
  boundaryAngle : BoundaryAngleIntegratedW11.Matrix.{u}
  boundaryLabel : BoundaryLabelIntegratedW11.RouteMatrix.{u}
  brokenLattice : BrokenLatticeIntegratedW11.Matrix.{u}
  brokenLatticeTarget : BrokenLatticeTargetIntegratedW11.Matrix.{u}
  geometry : GeometryIntegratedW11.Matrix.{u}
  k23 : K23IntegratedMatrixW11.Matrix.{u}
  k23Target : K23TargetIntegratedW11.Matrix.{u}
  noEarly : NoEarlyIntegratedW11.Matrix.{u}
  noEarlyTarget : NoEarlyTargetIntegratedW11.Matrix.{u}
  subpolygon : SubpolygonIntegratedW11.Matrix.{u}
  target : TargetIntegratedMatrixW11.Matrix.{u}

/-- Checked integrated W11 ledgers. -/
def integratedLedgers : IntegratedLedgers where
  boundaryAngle := BoundaryAngleIntegratedW11.matrix
  boundaryLabel := BoundaryLabelIntegratedW11.routeMatrix
  brokenLattice := BrokenLatticeIntegratedW11.matrix
  brokenLatticeTarget := BrokenLatticeTargetIntegratedW11.matrix
  geometry := GeometryIntegratedW11.matrix
  k23 := K23IntegratedMatrixW11.matrix
  k23Target := K23TargetIntegratedW11.matrix
  noEarly := NoEarlyIntegratedW11.matrix
  noEarlyTarget := NoEarlyTargetIntegratedW11.matrix
  subpolygon := SubpolygonIntegratedW11.matrix
  target := TargetIntegratedMatrixW11.matrix

/-- Imported modules that are intentionally omitted because the module itself
does not typecheck. -/
structure ImportBlockers : Type where
  topologyIntegratedW11 :
    "ErdosProblems1066.Swanepoel.TopologyIntegratedW11 import blocked: topology fact universe mismatch; unresolved boundary-geometry route names; matrix universe mismatch" =
    "ErdosProblems1066.Swanepoel.TopologyIntegratedW11 import blocked: topology fact universe mismatch; unresolved boundary-geometry route names; matrix universe mismatch"

/-- Current import blockers for the consistency matrix. -/
def importBlockers : ImportBlockers where
  topologyIntegratedW11 := rfl

/-! ## Projection matrix -/

/-- Public conditional projections assembled only from real imported fields. -/
structure ProjectionRoutes where
  boundaryAngleClosureDirect :
    TargetRoute (BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.{u})
  boundaryAngleClosureK23 :
    TargetRoute (BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.{u})
  boundaryAngleClosureCommonNeighbor :
    TargetRoute
      (BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.{u})
  boundaryLabelClosure :
    TargetRoute (BoundaryLabelClosureW11.Matrix.{u})
  boundaryLabelIntegrated :
    TargetRoute (BoundaryLabelIntegratedW11.Matrix.{u})
  noEarlyPrefix :
    TargetRoute (NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u})
  noEarlyExplicit :
    TargetRoute (NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u})
  noStartExplicit :
    TargetRoute (NoEarlyTargetIntegratedW11.ExplicitNoStartMatrix.{u})
  geometryDirect :
    TargetRoute (GeometryIntegratedW11.DirectGeometryMatrix.{u})
  geometryK23 :
    TargetRoute (GeometryIntegratedW11.K23GeometryMatrix.{u})
  geometryCommonNeighbor :
    TargetRoute (GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u})
  brokenLatticeDirect :
    TargetRoute (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u})
  k23Integrated :
    TargetRoute (K23IntegratedMatrixW11.K23IntegratedMatrix.{u})
  commonNeighborIntegrated :
    TargetRoute (K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u})
  k23Target :
    TargetRoute (K23TargetIntegratedW11.K23TargetMatrix.{u})
  commonNeighborTarget :
    TargetRoute (K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u})
  subpolygonDirect :
    TargetRoute (SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u})
  targetIntegratedDirect :
    TargetRoute (BrokenLatticeIntegratedW11.DirectFieldMatrix.{u})

/-- Checked projection routes from explicit input packages. -/
def projectionRoutes : ProjectionRoutes where
  boundaryAngleClosureDirect := boundaryAngleClosureDirectRoute
  boundaryAngleClosureK23 := boundaryAngleClosureK23Route
  boundaryAngleClosureCommonNeighbor :=
    boundaryAngleClosureCommonNeighborRoute
  boundaryLabelClosure := boundaryLabelClosureRoute
  boundaryLabelIntegrated := {
    noMinimal := BoundaryLabelIntegratedW11.no_minimalClearedFailure_of_matrix
    pipeline := BoundaryLabelIntegratedW11.pipelineCleared_of_matrix
    target := BoundaryLabelIntegratedW11.targetClosure_of_matrix
  }
  noEarlyPrefix := {
    noMinimal :=
      NoEarlyIntegratedW11.PrefixNoEarlyMatrix.no_minimalClearedFailure
    pipeline := NoEarlyIntegratedW11.PrefixNoEarlyMatrix.pipelineCleared
    target := fun M =>
      TargetClosureMatrixW11.noEarlyMatrixRow.target M.toW11NoEarlyMatrix
  }
  noEarlyExplicit := {
    noMinimal :=
      NoEarlyTargetIntegratedW11.no_minimalClearedFailure_of_explicitNoEarlyMatrix
    pipeline :=
      NoEarlyTargetIntegratedW11.pipelineCleared_of_explicitNoEarlyMatrix
    target :=
      NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoEarlyMatrix
  }
  noStartExplicit := {
    noMinimal :=
      NoEarlyTargetIntegratedW11.no_minimalClearedFailure_of_explicitNoStartMatrix
    pipeline :=
      NoEarlyTargetIntegratedW11.pipelineCleared_of_explicitNoStartMatrix
    target :=
      NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoStartMatrix
  }
  geometryDirect := {
    noMinimal :=
      GeometryIntegratedW11.no_minimalClearedFailure_of_directGeometryMatrix
    pipeline :=
      GeometryIntegratedW11.pipelineCleared_of_directGeometryMatrix
    target :=
      GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
  }
  geometryK23 := {
    noMinimal :=
      GeometryIntegratedW11.no_minimalClearedFailure_of_k23GeometryMatrix
    pipeline :=
      GeometryIntegratedW11.pipelineCleared_of_k23GeometryMatrix
    target :=
      GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
  }
  geometryCommonNeighbor := {
    noMinimal :=
      GeometryIntegratedW11.no_minimalClearedFailure_of_commonNeighborGeometryMatrix
    pipeline :=
      GeometryIntegratedW11.pipelineCleared_of_commonNeighborGeometryMatrix
    target :=
      GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
  }
  brokenLatticeDirect := {
    noMinimal :=
      BrokenLatticeIntegratedW11.no_minimalClearedFailure_of_directFieldMatrix
    pipeline :=
      BrokenLatticeIntegratedW11.pipelineCleared_of_directFieldMatrix
    target :=
      BrokenLatticeIntegratedW11.targetLowerBoundEightThirtyOne_of_directFieldMatrix
  }
  k23Integrated := {
    noMinimal :=
      K23IntegratedMatrixW11.no_minimalClearedFailure_of_k23IntegratedMatrix
    pipeline := fun M =>
      K23IntegratedMatrixW11.K23IntegratedMatrix.pipelineCleared M
    target :=
      K23IntegratedMatrixW11.targetLowerBoundEightThirtyOne_of_k23IntegratedMatrix
  }
  commonNeighborIntegrated := {
    noMinimal :=
      K23IntegratedMatrixW11.no_minimalClearedFailure_of_commonNeighborIntegratedMatrix
    pipeline := fun M =>
      K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.pipelineCleared M
    target :=
      K23IntegratedMatrixW11.targetLowerBoundEightThirtyOne_of_commonNeighborIntegratedMatrix
  }
  k23Target := {
    noMinimal :=
      K23TargetIntegratedW11.no_minimalClearedFailure_of_k23TargetMatrix
    pipeline :=
      K23TargetIntegratedW11.pipelineCleared_of_k23TargetMatrix
    target :=
      K23TargetIntegratedW11.targetLowerBoundEightThirtyOne_of_k23TargetMatrix
  }
  commonNeighborTarget := {
    noMinimal :=
      K23TargetIntegratedW11.no_minimalClearedFailure_of_commonNeighborTargetMatrix
    pipeline :=
      K23TargetIntegratedW11.pipelineCleared_of_commonNeighborTargetMatrix
    target :=
      K23TargetIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
  }
  subpolygonDirect := {
    noMinimal :=
      SubpolygonIntegratedW11.no_minimalClearedFailure_of_directBoundaryGeometryMatrix
    pipeline := fun M =>
      SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.pipelineCleared M
    target :=
      SubpolygonIntegratedW11.targetLowerBoundEightThirtyOne_of_directBoundaryGeometryMatrix
  }
  targetIntegratedDirect := {
    noMinimal := TargetIntegratedMatrixW11.no_minimalClearedFailure_of_directFieldMatrix
    pipeline := TargetIntegratedMatrixW11.pipelineCleared_of_directFieldMatrix
    target := TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix
  }

/-! ## Consistency matrix -/

/-- Checked consistency matrix for the W11 Swanepoel closure files. -/
structure Matrix where
  closures : ClosureLedgers
  integrated : IntegratedLedgers
  projections : ProjectionRoutes
  blockers : ImportBlockers

/-- The checked W11 consistency matrix. -/
def matrix : Matrix where
  closures := closureLedgers
  integrated := integratedLedgers
  projections := projectionRoutes
  blockers := importBlockers

/-! ## Public conditional projections -/

theorem exactFieldTarget_of_topologyFrontierPackage
    {n : Nat} {C : _root_.UDConfig n}
    (T : TopologyClosureW11.TopologyFrontierPackage C) :
    TopologyClosureW11.W10ExactFieldTarget C :=
  T.exactFieldTarget

theorem target_of_boundaryAngleClosureDirectMatrix
    (M : BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.{u}) :
    Target :=
  boundaryAngleClosureDirectRoute.target M

theorem target_of_boundaryLabelClosureMatrix
    (M : BoundaryLabelClosureW11.Matrix.{u}) :
    Target :=
  boundaryLabelClosureRoute.target M

theorem target_of_boundaryLabelIntegratedMatrix
    (M : BoundaryLabelIntegratedW11.Matrix.{u}) :
    Target :=
  BoundaryLabelIntegratedW11.targetClosure_of_matrix M

theorem target_of_prefixNoEarlyMatrix
    (M : NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.noEarlyMatrixRow.target M.toW11NoEarlyMatrix

theorem target_of_explicitNoEarlyMatrix
    (M : NoEarlyTargetIntegratedW11.ExplicitNoEarlyMatrix.{u}) :
    Target :=
  NoEarlyTargetIntegratedW11.targetClosure_of_explicitNoEarlyMatrix M

theorem target_of_geometryDirectMatrix
    (M : GeometryIntegratedW11.DirectGeometryMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    M

theorem target_of_brokenLatticeDirectFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  BrokenLatticeIntegratedW11.targetLowerBoundEightThirtyOne_of_directFieldMatrix
    M

theorem target_of_k23TargetMatrix
    (M : K23TargetIntegratedW11.K23TargetMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.targetLowerBoundEightThirtyOne_of_k23TargetMatrix M

theorem target_of_subpolygonDirectBoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u}) :
    Target :=
  SubpolygonIntegratedW11.targetLowerBoundEightThirtyOne_of_directBoundaryGeometryMatrix
    M

theorem target_of_targetIntegratedDirectFieldMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix M

end

end SwanepoelW11ConsistencyMatrix
end Swanepoel
end ErdosProblems1066
