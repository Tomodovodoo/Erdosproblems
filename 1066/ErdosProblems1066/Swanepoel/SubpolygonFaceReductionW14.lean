import ErdosProblems1066.Swanepoel.SubpolygonInstantiationW13
import ErdosProblems1066.Swanepoel.SubpolygonPackageW12
import ErdosProblems1066.Swanepoel.SubpolygonTargetIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W14 subpolygon face-reduction bridge

This file connects the checked W13/W12 subpolygon low-degree inequalities to
the existing Swanepoel minimal-failure route.  The geometric/topological
matching between a checked face-reduced subpolygon family and the route's
selected cycle data remains explicit.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonFaceReductionW14

open BoundaryCounting
open FaceReduction
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  SubpolygonTargetIntegratedW11.Target

abbrev MinimalFailureExclusion : Prop :=
  SubpolygonTargetIntegratedW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SubpolygonTargetIntegratedW11.PipelineCleared

abbrev SubpolygonRoute (C : _root_.UDConfig n) :=
  SubpolygonTargetIntegratedW11.SubpolygonRoute.{u} C

/-! ## Checked face-reduced low-degree families -/

/-- A proposition-valued family carrying exactly the E13 conclusions needed
to compare against a minimal-failure subpolygon route. -/
structure CheckedLowDegreeFamily : Type (u + 1) where
  Subpolygon : Type u
  counts : Subpolygon -> SubpolygonDegreeCounts
  lowDegreeWithHighDegreeSlack :
    forall S : Subpolygon,
      (counts S).D5 + 2 * (counts S).D6 + 6 <=
        2 * (counts S).D2 + (counts S).D3
  lowDegree :
    forall S : Subpolygon,
      6 <= 2 * (counts S).D2 + (counts S).D3

/-- W13 explicit face-boundary data, bundled as a family over one canonical
unit-distance face-boundary witness. -/
structure ExplicitFaceBoundaryFamily
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : UnitDistanceFaceBoundaryHypotheses G
  Subpolygon : Type u
  data :
    Subpolygon ->
      SubpolygonInstantiationW13.ExplicitFaceBoundaryData faceBoundary

namespace ExplicitFaceBoundaryFamily

variable {G : CanonicalStraightLineUnitDistanceGraph n}

def subpolygonCounts
    (F : ExplicitFaceBoundaryFamily.{u} G) (S : F.Subpolygon) :
    SubpolygonDegreeCounts :=
  (F.data S).counts

def subpolygonData
    (F : ExplicitFaceBoundaryFamily.{u} G) (S : F.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData G :=
  (F.data S).toExplicitBoundaryData.toCycleCountAngleData

@[simp]
theorem subpolygonData_counts
    (F : ExplicitFaceBoundaryFamily.{u} G) (S : F.Subpolygon) :
    (F.subpolygonData S).counts = F.subpolygonCounts S :=
  rfl

theorem subpolygonLowDegreeWithHighDegreeSlack
    (F : ExplicitFaceBoundaryFamily.{u} G) (S : F.Subpolygon) :
    (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
      2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 := by
  simpa [subpolygonCounts] using (F.data S).lowDegreeWithHighDegreeSlack

theorem subpolygonLowDegree
    (F : ExplicitFaceBoundaryFamily.{u} G) (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 +
      (F.subpolygonCounts S).D3 := by
  simpa [subpolygonCounts] using (F.data S).lowDegree

def toCheckedLowDegreeFamily
    (F : ExplicitFaceBoundaryFamily.{u} G) :
    CheckedLowDegreeFamily.{u} where
  Subpolygon := F.Subpolygon
  counts := F.subpolygonCounts
  lowDegreeWithHighDegreeSlack := F.subpolygonLowDegreeWithHighDegreeSlack
  lowDegree := F.subpolygonLowDegree

def toPlanarBoundaryData
    (F : ExplicitFaceBoundaryFamily.{u} G)
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G where
  core := core
  outerAngleBounds := outerAngleBounds
  Subpolygon := F.Subpolygon
  subpolygonData := F.subpolygonData

end ExplicitFaceBoundaryFamily

/-! ## W12 honest packages as face-reduced planar-boundary inputs -/

/-- A W13 explicit family, tied to the same face-boundary witness as the
outer-boundary core used by `PlanarBoundaryClosure`. -/
structure ExplicitFacePlanarInput
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  core : OuterBoundaryCore G
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  family : ExplicitFaceBoundaryFamily.{u} G
  faceBoundary_eq : family.faceBoundary = core.faceBoundary

namespace ExplicitFacePlanarInput

variable {G : CanonicalStraightLineUnitDistanceGraph n}

def planarBoundaryData
    (I : ExplicitFacePlanarInput.{u} G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  I.family.toPlanarBoundaryData I.core I.outerAngleBounds

theorem subpolygonLowDegree
    (I : ExplicitFacePlanarInput.{u} G) (S : I.family.Subpolygon) :
    6 <= 2 * (I.planarBoundaryData.subpolygonData S).counts.D2 +
      (I.planarBoundaryData.subpolygonData S).counts.D3 := by
  simpa [planarBoundaryData] using I.family.subpolygonLowDegree S

theorem faceCountingTheorems
    (I : ExplicitFacePlanarInput.{u} G) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      I.planarBoundaryData :=
  I.planarBoundaryData.faceCountingTheorems

end ExplicitFacePlanarInput

/-- A W12 honest family, tied to the same face-boundary witness as the
outer-boundary core used by `PlanarBoundaryClosure`. -/
structure HonestFacePlanarInput
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  core : OuterBoundaryCore G
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  family : SubpolygonPackageW12.HonestSubpolygonFamilyPackage.{u} G
  faceBoundary_eq : family.faceBoundary = core.faceBoundary

namespace HonestFacePlanarInput

variable {G : CanonicalStraightLineUnitDistanceGraph n}

def planarBoundaryData
    (I : HonestFacePlanarInput.{u} G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G where
  core := I.core
  outerAngleBounds := I.outerAngleBounds
  Subpolygon := I.family.Subpolygon
  subpolygonData := I.family.subpolygonData

theorem subpolygonLowDegree
    (I : HonestFacePlanarInput.{u} G) (S : I.family.Subpolygon) :
    6 <= 2 * (I.planarBoundaryData.subpolygonData S).counts.D2 +
      (I.planarBoundaryData.subpolygonData S).counts.D3 := by
  simpa [planarBoundaryData] using I.family.subpolygonLowDegree S

theorem faceCountingTheorems
    (I : HonestFacePlanarInput.{u} G) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      I.planarBoundaryData :=
  I.planarBoundaryData.faceCountingTheorems

end HonestFacePlanarInput

/-! ## Matching checked families to the minimal-failure route -/

/-- Explicit matching data between a checked low-degree family and the
subpolygon cycles selected by a Swanepoel route. -/
structure RouteLowDegreeMatch
    (C : _root_.UDConfig n) (route : SubpolygonRoute.{u} C) :
    Type (u + 1) where
  checked : CheckedLowDegreeFamily.{u}
  subpolygonOfRoute : route.Subpolygon -> checked.Subpolygon
  counts_eq :
    forall S : route.Subpolygon,
      (route.cycleData S).counts =
        checked.counts (subpolygonOfRoute S)

namespace RouteLowDegreeMatch

variable {C : _root_.UDConfig n}
variable {route : SubpolygonRoute.{u} C}

theorem routeLowDegreeWithHighDegreeSlack
    (M : RouteLowDegreeMatch.{u} C route) (S : route.Subpolygon) :
    (route.cycleData S).counts.D5 +
        2 * (route.cycleData S).counts.D6 + 6 <=
      2 * (route.cycleData S).counts.D2 +
        (route.cycleData S).counts.D3 := by
  rw [M.counts_eq S]
  exact M.checked.lowDegreeWithHighDegreeSlack (M.subpolygonOfRoute S)

theorem routeLowDegree
    (M : RouteLowDegreeMatch.{u} C route) (S : route.Subpolygon) :
    6 <= 2 * (route.cycleData S).counts.D2 +
      (route.cycleData S).counts.D3 := by
  rw [M.counts_eq S]
  exact M.checked.lowDegree (M.subpolygonOfRoute S)

end RouteLowDegreeMatch

/-- W13 explicit face-reduced data matched to a minimal-failure route. -/
structure ExplicitFaceRouteMatch
    (C : _root_.UDConfig n) (route : SubpolygonRoute.{u} C) :
    Type (u + 1) where
  family :
    ExplicitFaceBoundaryFamily.{u}
      (JordanTopologyFactsConcrete.canonicalGraph C)
  faceBoundary_eq : family.faceBoundary = route.topology.faceBoundary
  subpolygonOfRoute : route.Subpolygon -> family.Subpolygon
  counts_eq :
    forall S : route.Subpolygon,
      (route.cycleData S).counts =
        family.subpolygonCounts (subpolygonOfRoute S)

namespace ExplicitFaceRouteMatch

variable {C : _root_.UDConfig n}
variable {route : SubpolygonRoute.{u} C}

def toRouteLowDegreeMatch
    (M : ExplicitFaceRouteMatch.{u} C route) :
    RouteLowDegreeMatch.{u} C route where
  checked := M.family.toCheckedLowDegreeFamily
  subpolygonOfRoute := M.subpolygonOfRoute
  counts_eq := M.counts_eq

theorem routeLowDegreeWithHighDegreeSlack
    (M : ExplicitFaceRouteMatch.{u} C route) (S : route.Subpolygon) :
    (route.cycleData S).counts.D5 +
        2 * (route.cycleData S).counts.D6 + 6 <=
      2 * (route.cycleData S).counts.D2 +
        (route.cycleData S).counts.D3 :=
  M.toRouteLowDegreeMatch.routeLowDegreeWithHighDegreeSlack S

theorem routeLowDegree
    (M : ExplicitFaceRouteMatch.{u} C route) (S : route.Subpolygon) :
    6 <= 2 * (route.cycleData S).counts.D2 +
      (route.cycleData S).counts.D3 :=
  M.toRouteLowDegreeMatch.routeLowDegree S

end ExplicitFaceRouteMatch

/-- W12 honest face-reduced data matched to a minimal-failure route. -/
structure HonestFaceRouteMatch
    (C : _root_.UDConfig n) (route : SubpolygonRoute.{u} C) :
    Type (u + 1) where
  family :
    SubpolygonPackageW12.HonestSubpolygonFamilyPackage.{u}
      (JordanTopologyFactsConcrete.canonicalGraph C)
  faceBoundary_eq : family.faceBoundary = route.topology.faceBoundary
  subpolygonOfRoute : route.Subpolygon -> family.Subpolygon
  counts_eq :
    forall S : route.Subpolygon,
      (route.cycleData S).counts =
        family.subpolygonCounts (subpolygonOfRoute S)

namespace HonestFaceRouteMatch

variable {C : _root_.UDConfig n}
variable {route : SubpolygonRoute.{u} C}

def toRouteLowDegreeMatch
    (M : HonestFaceRouteMatch.{u} C route) :
    RouteLowDegreeMatch.{u} C route where
  checked := {
    Subpolygon := M.family.Subpolygon
    counts := M.family.subpolygonCounts
    lowDegreeWithHighDegreeSlack :=
      M.family.subpolygonLowDegreeWithHighDegreeSlack
    lowDegree := M.family.subpolygonLowDegree
  }
  subpolygonOfRoute := M.subpolygonOfRoute
  counts_eq := M.counts_eq

theorem routeLowDegreeWithHighDegreeSlack
    (M : HonestFaceRouteMatch.{u} C route) (S : route.Subpolygon) :
    (route.cycleData S).counts.D5 +
        2 * (route.cycleData S).counts.D6 + 6 <=
      2 * (route.cycleData S).counts.D2 +
        (route.cycleData S).counts.D3 :=
  M.toRouteLowDegreeMatch.routeLowDegreeWithHighDegreeSlack S

theorem routeLowDegree
    (M : HonestFaceRouteMatch.{u} C route) (S : route.Subpolygon) :
    6 <= 2 * (route.cycleData S).counts.D2 +
      (route.cycleData S).counts.D3 :=
  M.toRouteLowDegreeMatch.routeLowDegree S

end HonestFaceRouteMatch

/-! ## Pointwise minimal-failure rows retaining the checked match -/

structure DirectRouteWithCheckedLowDegree
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  row : SubpolygonTargetIntegratedW11.DirectRow.{u} C hmin
  lowDegreeMatch : RouteLowDegreeMatch.{u} C row.labelPrefix.route

namespace DirectRouteWithCheckedLowDegree

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

theorem cycleLowDegreeWithHighDegreeSlack
    (R : DirectRouteWithCheckedLowDegree.{u} C hmin)
    (S : R.row.labelPrefix.route.Subpolygon) :
    (R.row.labelPrefix.route.cycleData S).counts.D5 +
        2 * (R.row.labelPrefix.route.cycleData S).counts.D6 + 6 <=
      2 * (R.row.labelPrefix.route.cycleData S).counts.D2 +
        (R.row.labelPrefix.route.cycleData S).counts.D3 :=
  R.lowDegreeMatch.routeLowDegreeWithHighDegreeSlack S

theorem cycleLowDegree
    (R : DirectRouteWithCheckedLowDegree.{u} C hmin)
    (S : R.row.labelPrefix.route.Subpolygon) :
    6 <= 2 * (R.row.labelPrefix.route.cycleData S).counts.D2 +
      (R.row.labelPrefix.route.cycleData S).counts.D3 :=
  R.lowDegreeMatch.routeLowDegree S

theorem contradiction
    (R : DirectRouteWithCheckedLowDegree.{u} C hmin) :
    False :=
  R.row.contradiction

end DirectRouteWithCheckedLowDegree

structure K23RouteWithCheckedLowDegree
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  row : SubpolygonTargetIntegratedW11.K23Row.{u} C hmin
  lowDegreeMatch : RouteLowDegreeMatch.{u} C row.labelPrefix.route

namespace K23RouteWithCheckedLowDegree

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

theorem cycleLowDegreeWithHighDegreeSlack
    (R : K23RouteWithCheckedLowDegree.{u} C hmin)
    (S : R.row.labelPrefix.route.Subpolygon) :
    (R.row.labelPrefix.route.cycleData S).counts.D5 +
        2 * (R.row.labelPrefix.route.cycleData S).counts.D6 + 6 <=
      2 * (R.row.labelPrefix.route.cycleData S).counts.D2 +
        (R.row.labelPrefix.route.cycleData S).counts.D3 :=
  R.lowDegreeMatch.routeLowDegreeWithHighDegreeSlack S

theorem cycleLowDegree
    (R : K23RouteWithCheckedLowDegree.{u} C hmin)
    (S : R.row.labelPrefix.route.Subpolygon) :
    6 <= 2 * (R.row.labelPrefix.route.cycleData S).counts.D2 +
      (R.row.labelPrefix.route.cycleData S).counts.D3 :=
  R.lowDegreeMatch.routeLowDegree S

theorem contradiction
    (R : K23RouteWithCheckedLowDegree.{u} C hmin) :
    False :=
  R.row.contradiction

end K23RouteWithCheckedLowDegree

structure CommonNeighborRouteWithCheckedLowDegree
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  row : SubpolygonTargetIntegratedW11.CommonNeighborRow.{u} C hmin
  lowDegreeMatch : RouteLowDegreeMatch.{u} C row.labelPrefix.route

namespace CommonNeighborRouteWithCheckedLowDegree

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

theorem cycleLowDegreeWithHighDegreeSlack
    (R : CommonNeighborRouteWithCheckedLowDegree.{u} C hmin)
    (S : R.row.labelPrefix.route.Subpolygon) :
    (R.row.labelPrefix.route.cycleData S).counts.D5 +
        2 * (R.row.labelPrefix.route.cycleData S).counts.D6 + 6 <=
      2 * (R.row.labelPrefix.route.cycleData S).counts.D2 +
        (R.row.labelPrefix.route.cycleData S).counts.D3 :=
  R.lowDegreeMatch.routeLowDegreeWithHighDegreeSlack S

theorem cycleLowDegree
    (R : CommonNeighborRouteWithCheckedLowDegree.{u} C hmin)
    (S : R.row.labelPrefix.route.Subpolygon) :
    6 <= 2 * (R.row.labelPrefix.route.cycleData S).counts.D2 +
      (R.row.labelPrefix.route.cycleData S).counts.D3 :=
  R.lowDegreeMatch.routeLowDegree S

theorem contradiction
    (R : CommonNeighborRouteWithCheckedLowDegree.{u} C hmin) :
    False :=
  R.row.contradiction

end CommonNeighborRouteWithCheckedLowDegree

/-! ## Uniform minimal-failure matrices -/

structure DirectMatrixWithCheckedLowDegree : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectRouteWithCheckedLowDegree.{u} C hmin

namespace DirectMatrixWithCheckedLowDegree

def toDirectMatrix
    (M : DirectMatrixWithCheckedLowDegree.{u}) :
    SubpolygonTargetIntegratedW11.DirectMatrix.{u} where
  row := fun C hmin => (M.row C hmin).row

theorem no_minimalClearedFailure
    (M : DirectMatrixWithCheckedLowDegree.{u}) :
    MinimalFailureExclusion :=
  SubpolygonTargetIntegratedW11.DirectMatrix.no_minimalClearedFailure
    M.toDirectMatrix

theorem pipelineCleared
    (M : DirectMatrixWithCheckedLowDegree.{u}) :
    PipelineCleared :=
  SubpolygonTargetIntegratedW11.DirectMatrix.pipelineCleared
    M.toDirectMatrix

theorem targetClosure
    (M : DirectMatrixWithCheckedLowDegree.{u}) :
    Target :=
  SubpolygonTargetIntegratedW11.DirectMatrix.targetClosure
    M.toDirectMatrix

end DirectMatrixWithCheckedLowDegree

structure K23MatrixWithCheckedLowDegree : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23RouteWithCheckedLowDegree.{u} C hmin

namespace K23MatrixWithCheckedLowDegree

def toK23Matrix
    (M : K23MatrixWithCheckedLowDegree.{u}) :
    SubpolygonTargetIntegratedW11.K23Matrix.{u} where
  row := fun C hmin => (M.row C hmin).row

theorem no_minimalClearedFailure
    (M : K23MatrixWithCheckedLowDegree.{u}) :
    MinimalFailureExclusion :=
  SubpolygonTargetIntegratedW11.K23Matrix.no_minimalClearedFailure
    M.toK23Matrix

theorem pipelineCleared
    (M : K23MatrixWithCheckedLowDegree.{u}) :
    PipelineCleared :=
  SubpolygonTargetIntegratedW11.K23Matrix.pipelineCleared
    M.toK23Matrix

theorem targetClosure
    (M : K23MatrixWithCheckedLowDegree.{u}) :
    Target :=
  SubpolygonTargetIntegratedW11.K23Matrix.targetClosure
    M.toK23Matrix

end K23MatrixWithCheckedLowDegree

structure CommonNeighborMatrixWithCheckedLowDegree : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborRouteWithCheckedLowDegree.{u} C hmin

namespace CommonNeighborMatrixWithCheckedLowDegree

def toCommonNeighborMatrix
    (M : CommonNeighborMatrixWithCheckedLowDegree.{u}) :
    SubpolygonTargetIntegratedW11.CommonNeighborMatrix.{u} where
  row := fun C hmin => (M.row C hmin).row

theorem no_minimalClearedFailure
    (M : CommonNeighborMatrixWithCheckedLowDegree.{u}) :
    MinimalFailureExclusion :=
  SubpolygonTargetIntegratedW11.CommonNeighborMatrix.no_minimalClearedFailure
    M.toCommonNeighborMatrix

theorem pipelineCleared
    (M : CommonNeighborMatrixWithCheckedLowDegree.{u}) :
    PipelineCleared :=
  SubpolygonTargetIntegratedW11.CommonNeighborMatrix.pipelineCleared
    M.toCommonNeighborMatrix

theorem targetClosure
    (M : CommonNeighborMatrixWithCheckedLowDegree.{u}) :
    Target :=
  SubpolygonTargetIntegratedW11.CommonNeighborMatrix.targetClosure
    M.toCommonNeighborMatrix

end CommonNeighborMatrixWithCheckedLowDegree

end

end SubpolygonFaceReductionW14
end Swanepoel
end ErdosProblems1066
