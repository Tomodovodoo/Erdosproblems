import ErdosProblems1066.Swanepoel.OuterBoundaryCore
import ErdosProblems1066.Swanepoel.SubpolygonAssembly
import ErdosProblems1066.Swanepoel.BoundaryCountingInstantiationW10

set_option autoImplicit false

/-!
# Concrete subpolygon data from an outer-boundary core

This module packages the honest data needed to build
`SubpolygonAssembly.PlanarBoundarySubpolygonInputs` from a supplied
`OuterBoundaryCore`.

The construction is deliberately exact about what is known and what remains to
be proved.  Boundary cycles and induced degree counts are concrete; the
inside/on predicates, their exact finite vertex-set description, and the real
angle comparisons are explicit fields supplied by the caller.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonDataConcrete

open BoundaryCounting
open FaceReduction
open PlanarInterface
open SubpolygonAssembly
open SubpolygonAngleRealization
open SubpolygonCore

universe u

noncomputable section

variable {n : Nat}

/-! ## Subpolygon data tied to an outer-boundary core -/

/--
Concrete geometric data for one subpolygon inside the ambient graph carried by
an `OuterBoundaryCore`.

The finite vertex set is not merely known to contain the boundary: the
`vertices_iff_insideOrOn` field records that it is exactly the set of ambient
vertices whose points lie inside or on the supplied subpolygon predicate.  The
counts derived below are therefore the induced boundary-degree counts for this
explicit finite set.
-/
structure CoreSubpolygonGeometryData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (_core : OuterBoundaryCore G) where
  boundary : BoundaryCycle G
  vertices : Finset (Fin n)
  boundary_subset : boundary.vertexFinset ⊆ vertices
  insideOrOn : Point -> Prop
  onBoundary : Fin n -> Prop
  boundary_vertex_onBoundary :
    forall k : Fin boundary.length, onBoundary (boundary.vertex k)
  vertices_iff_insideOrOn :
    forall v : Fin n, v ∈ vertices <-> insideOrOn (G.point v)
  onBoundary_iff_cycle :
    forall v : Fin n,
      onBoundary v <->
        Exists fun k : Fin boundary.length => boundary.vertex k = v

namespace CoreSubpolygonGeometryData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- The induced vertex-set package used by `SubpolygonCore`. -/
def vertexSet (D : CoreSubpolygonGeometryData core) :
    InducedVertexSet G D.boundary :=
  inducedVertexSetOfFinset D.boundary D.vertices D.boundary_subset

/-- Vertices in the explicit finite set are exactly inside or on the
subpolygon. -/
theorem vertices_insideOrOn
    (D : CoreSubpolygonGeometryData core) :
    forall v : Fin n, v ∈ D.vertices -> D.insideOrOn (G.point v) :=
  fun v hv => (D.vertices_iff_insideOrOn v).1 hv

/-- Every boundary vertex lies in the explicit finite vertex set. -/
theorem boundary_vertex_mem
    (D : CoreSubpolygonGeometryData core)
    (k : Fin D.boundary.length) :
    D.boundary.vertex k ∈ D.vertices :=
  D.boundary_subset (D.boundary.vertex_mem_vertexFinset k)

/-- Every boundary vertex is inside or on the supplied subpolygon predicate. -/
theorem boundary_vertex_insideOrOn
    (D : CoreSubpolygonGeometryData core)
    (k : Fin D.boundary.length) :
    D.insideOrOn (G.point (D.boundary.vertex k)) :=
  D.vertices_insideOrOn (D.boundary.vertex k) (D.boundary_vertex_mem k)

/-- The ambient outer core still contains every subpolygon vertex. -/
theorem vertex_outer_insideOrOn
    (_D : CoreSubpolygonGeometryData core)
    (v : Fin n) :
    core.outerEnclosure.insideOrOn (G.point v) :=
  core.all_vertices_insideOrOn v

/-- Forget to the honest geometric subpolygon package from
`SubpolygonAssembly`. -/
def toHonestGeometricSubpolygon
    (D : CoreSubpolygonGeometryData core) :
    HonestGeometricSubpolygon G where
  boundary := D.boundary
  vertexSet := D.vertexSet
  insideOrOn := D.insideOrOn
  onBoundary := D.onBoundary
  boundary_vertex_onBoundary := D.boundary_vertex_onBoundary
  vertices_insideOrOn := D.vertices_insideOrOn
  onBoundary_iff_cycle := D.onBoundary_iff_cycle

@[simp]
theorem toHonestGeometricSubpolygon_boundary
    (D : CoreSubpolygonGeometryData core) :
    D.toHonestGeometricSubpolygon.boundary = D.boundary :=
  rfl

@[simp]
theorem toHonestGeometricSubpolygon_vertexSet
    (D : CoreSubpolygonGeometryData core) :
    D.toHonestGeometricSubpolygon.vertexSet = D.vertexSet :=
  rfl

/-- The computed E13 counts for this induced subpolygon. -/
def counts (D : CoreSubpolygonGeometryData core) :
    SubpolygonDegreeCounts :=
  D.vertexSet.degreeCounts

@[simp]
theorem toHonestGeometricSubpolygon_counts
    (D : CoreSubpolygonGeometryData core) :
    D.toHonestGeometricSubpolygon.counts = D.counts :=
  rfl

@[simp]
theorem counts_eq_degreeCounts
    (D : CoreSubpolygonGeometryData core) :
    D.counts = D.vertexSet.degreeCounts :=
  rfl

@[simp]
theorem counts_D2
    (D : CoreSubpolygonGeometryData core) :
    D.counts.D2 = D.vertexSet.countBoundaryDegree 2 :=
  rfl

@[simp]
theorem counts_D3
    (D : CoreSubpolygonGeometryData core) :
    D.counts.D3 = D.vertexSet.countBoundaryDegree 3 :=
  rfl

@[simp]
theorem counts_D4
    (D : CoreSubpolygonGeometryData core) :
    D.counts.D4 = D.vertexSet.countBoundaryDegree 4 :=
  rfl

@[simp]
theorem counts_D5
    (D : CoreSubpolygonGeometryData core) :
    D.counts.D5 = D.vertexSet.countBoundaryDegree 5 :=
  rfl

@[simp]
theorem counts_D6
    (D : CoreSubpolygonGeometryData core) :
    D.counts.D6 = D.vertexSet.countBoundaryDegree 6 :=
  rfl

end CoreSubpolygonGeometryData

/-- Concrete subpolygon geometry plus the real angle comparisons needed for
the E13 counting inequality. -/
structure CoreSubpolygonAngleData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) where
  geometry : CoreSubpolygonGeometryData core
  geometricAngleSum : Real
  forced_le_geometric :
    geometry.counts.forcedSubpolygonAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= geometry.counts.polygonAngleSum

namespace CoreSubpolygonAngleData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- The computed E13 counts carried by the concrete data. -/
def counts (D : CoreSubpolygonAngleData core) :
    SubpolygonDegreeCounts :=
  D.geometry.counts

/-- Forget to the `SubpolygonAssembly` angle package. -/
def toHonestGeometricSubpolygonAngleData
    (D : CoreSubpolygonAngleData core) :
    HonestGeometricSubpolygonAngleData G where
  subpolygon := D.geometry.toHonestGeometricSubpolygon
  geometricAngleSum := D.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, CoreSubpolygonGeometryData.counts] using
      D.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts, CoreSubpolygonGeometryData.counts] using
      D.geometric_le_polygon

/-- The `PlanarBoundaryClosure`-facing cycle/count/angle package. -/
def toSubpolygonCycleCountAngleData
    (D : CoreSubpolygonAngleData core) :
    SubpolygonCycleCountAngleData G :=
  D.toHonestGeometricSubpolygonAngleData.toSubpolygonCycleCountAngleData

@[simp]
theorem toHonestGeometricSubpolygonAngleData_counts
    (D : CoreSubpolygonAngleData core) :
    D.toHonestGeometricSubpolygonAngleData.counts = D.counts :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_counts
    (D : CoreSubpolygonAngleData core) :
    D.toSubpolygonCycleCountAngleData.counts = D.counts :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_boundary
    (D : CoreSubpolygonAngleData core) :
    D.toSubpolygonCycleCountAngleData.boundary = D.geometry.boundary :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_vertexSet
    (D : CoreSubpolygonAngleData core) :
    D.toSubpolygonCycleCountAngleData.vertexSet = D.geometry.vertexSet :=
  rfl

/-- E13 with high-degree slack for the computed induced counts. -/
theorem lowDegreeWithHighDegreeSlack
    (D : CoreSubpolygonAngleData core) :
    D.counts.D5 + 2 * D.counts.D6 + 6 <=
      2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using
    D.toHonestGeometricSubpolygonAngleData.lowDegreeWithHighDegreeSlack

/-- Swanepoel's low-degree conclusion for the computed induced counts. -/
theorem lowDegree
    (D : CoreSubpolygonAngleData core) :
    6 <= 2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using
    D.toHonestGeometricSubpolygonAngleData.lowDegreeInequality

/-- Build aggregate core-subpolygon angle data from native concrete
triangulation rows once the supplied geometric angle sum is identified with
the triangulated boundary interior-angle sum. -/
def ofConcreteSubpolygonInteriorAngleTriangulationRows
    (geometry : CoreSubpolygonGeometryData core)
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G geometry.boundary geometry.vertexSet)
    (geometricAngleSum : Real)
    (hforced :
      geometry.counts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hgeometric :
      geometricAngleSum =
        SubpolygonAngleRealization.boundaryInteriorAngleSum
          geometry.boundary R.previousIndex) :
    CoreSubpolygonAngleData core where
  geometry := geometry
  geometricAngleSum := geometricAngleSum
  forced_le_geometric := hforced
  geometric_le_polygon := by
    rw [hgeometric]
    simpa [CoreSubpolygonGeometryData.counts] using
      R.boundaryInteriorAngleSum_le_subpolygonPolygonAngleSum

/-- Build core-subpolygon angle data by using the genuine triangulated
boundary interior-angle sum itself as the geometric angle sum. -/
def ofConcreteSubpolygonInteriorAngleTriangulationRowsBoundaryInteriorAngleSum
    (geometry : CoreSubpolygonGeometryData core)
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G geometry.boundary geometry.vertexSet)
    (hforced :
      geometry.counts.forcedSubpolygonAngleSum <=
        SubpolygonAngleRealization.boundaryInteriorAngleSum
          geometry.boundary R.previousIndex) :
    CoreSubpolygonAngleData core :=
  ofConcreteSubpolygonInteriorAngleTriangulationRows geometry R
    (SubpolygonAngleRealization.boundaryInteriorAngleSum
      geometry.boundary R.previousIndex)
    hforced rfl

/-- Direct E13 slack for a core subpolygon from native triangulation rows and
the forced-angle lower bound for the actual boundary interior-angle sum. -/
theorem lowDegreeWithHighDegreeSlack_ofConcreteSubpolygonInteriorAngleTriangulationRows
    (geometry : CoreSubpolygonGeometryData core)
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G geometry.boundary geometry.vertexSet)
    (hforced :
      geometry.counts.forcedSubpolygonAngleSum <=
        SubpolygonAngleRealization.boundaryInteriorAngleSum
          geometry.boundary R.previousIndex) :
    geometry.counts.D5 + 2 * geometry.counts.D6 + 6 <=
      2 * geometry.counts.D2 + geometry.counts.D3 :=
  (ofConcreteSubpolygonInteriorAngleTriangulationRowsBoundaryInteriorAngleSum
    geometry R hforced).lowDegreeWithHighDegreeSlack

end CoreSubpolygonAngleData

/-! ## Core subpolygons with actual angle realizations -/

/-- Concrete subpolygon geometry plus explicit pointwise real angle data
realizing the E13 lower bound for the computed induced counts. -/
structure CoreSubpolygonAngleRealizationData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) where
  geometry : CoreSubpolygonGeometryData core
  angleRealization :
    ConcreteAngleRealization G geometry.boundary geometry.vertexSet

namespace CoreSubpolygonAngleRealizationData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- The computed E13 counts carried by the concrete data. -/
def counts (D : CoreSubpolygonAngleRealizationData core) :
    SubpolygonDegreeCounts :=
  D.geometry.counts

/-- Forget explicit pointwise angle data to the aggregate core-subpolygon angle
package. -/
def toCoreSubpolygonAngleData
    (D : CoreSubpolygonAngleRealizationData core) :
    CoreSubpolygonAngleData core where
  geometry := D.geometry
  geometricAngleSum := D.angleRealization.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, CoreSubpolygonGeometryData.counts] using
      D.angleRealization.forced_le_geometricAngleSum
  geometric_le_polygon := by
    simpa [counts, CoreSubpolygonGeometryData.counts] using
      D.angleRealization.geometric_le_polygon

@[simp]
theorem toCoreSubpolygonAngleData_counts
    (D : CoreSubpolygonAngleRealizationData core) :
    D.toCoreSubpolygonAngleData.counts = D.counts :=
  rfl

/-- The `PlanarBoundaryClosure`-facing cycle/count/angle package. -/
def toSubpolygonCycleCountAngleData
    (D : CoreSubpolygonAngleRealizationData core) :
    SubpolygonCycleCountAngleData G :=
  D.toCoreSubpolygonAngleData.toSubpolygonCycleCountAngleData

@[simp]
theorem toSubpolygonCycleCountAngleData_counts
    (D : CoreSubpolygonAngleRealizationData core) :
    D.toSubpolygonCycleCountAngleData.counts = D.counts :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_boundary
    (D : CoreSubpolygonAngleRealizationData core) :
    D.toSubpolygonCycleCountAngleData.boundary = D.geometry.boundary :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_vertexSet
    (D : CoreSubpolygonAngleRealizationData core) :
    D.toSubpolygonCycleCountAngleData.vertexSet = D.geometry.vertexSet :=
  rfl

/-- E13 with high-degree slack for the computed induced counts. -/
theorem lowDegreeWithHighDegreeSlack
    (D : CoreSubpolygonAngleRealizationData core) :
    D.counts.D5 + 2 * D.counts.D6 + 6 <=
      2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using
    D.toCoreSubpolygonAngleData.lowDegreeWithHighDegreeSlack

/-- Swanepoel's low-degree conclusion for the computed induced counts. -/
theorem lowDegree
    (D : CoreSubpolygonAngleRealizationData core) :
    6 <= 2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using D.toCoreSubpolygonAngleData.lowDegree

end CoreSubpolygonAngleRealizationData

/-! ## Outer-boundary triangulation rows -/

/--
Local outer-boundary triangulation rows.

This is the upstream analogue of
`PlanarBoundaryFaceDataRefinement.SimplePolygonInteriorAngleTriangulationRows`,
kept here to avoid importing the downstream refinement module back into the
subpolygon layer.  The fields are deliberately geometric: actual triangle
corner points, actual `AngleGeometry.angleAt` triangle angles, one `pi` angle
sum per triangle, and an equality between the selected outer-cycle
predecessor/current/successor angle sum and the sum of triangle angles.
-/
structure CoreOuterBoundaryInteriorAngleTriangulationRows
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) : Type (u + 1) where
  boundaryLength_ge_three : 3 <= core.outerCycle.length
  Triangle : Type u
  triangleFintype : Fintype Triangle
  triangleCount_eq_boundaryLength_sub_two :
    @Fintype.card Triangle triangleFintype = core.outerCycle.length - 2
  trianglePoint : Triangle -> Fin 3 -> PlanarInterface.Point
  triangleAngleSum_eq_pi :
    forall T : Triangle,
      Finset.sum (Finset.univ : Finset (Fin 3))
          (fun c => SubpolygonAngleRealization.triangleCornerAngle
            (trianglePoint T) c) =
        Real.pi
  simplePolygonInteriorAngleSum_eq_triangleAngleSum :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        core =
      letI := triangleFintype
      Finset.sum (Finset.univ : Finset Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c => SubpolygonAngleRealization.triangleCornerAngle
              (trianglePoint T) c))

namespace CoreOuterBoundaryInteriorAngleTriangulationRows

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- A genuine outer-cycle triangulation gives the cycle-length polygon angle
sum used by the W10 boundary-sector rows. -/
theorem triangleAngleSum_eq_boundaryCyclePolygonAngleSum
    (R : CoreOuterBoundaryInteriorAngleTriangulationRows.{u} core) :
    letI := R.triangleFintype
    Finset.sum (Finset.univ : Finset R.Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c => SubpolygonAngleRealization.triangleCornerAngle
              (R.trianglePoint T) c)) =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        core := by
  classical
  letI := R.triangleFintype
  have htwo : 2 <= core.outerCycle.length :=
    Nat.le_trans (by norm_num) R.boundaryLength_ge_three
  calc
    Finset.sum (Finset.univ : Finset R.Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c => SubpolygonAngleRealization.triangleCornerAngle
              (R.trianglePoint T) c)) =
        Finset.sum (Finset.univ : Finset R.Triangle) (fun _ => Real.pi) := by
          exact Finset.sum_congr rfl
            (fun T _ => R.triangleAngleSum_eq_pi T)
    _ = (Fintype.card R.Triangle : Real) * Real.pi := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ((core.outerCycle.length - 2 : Nat) : Real) * Real.pi := by
          rw [R.triangleCount_eq_boundaryLength_sub_two]
    _ = Real.pi * ((core.outerCycle.length : Real) - 2) := by
          rw [Nat.cast_sub htwo]
          ring
    _ = BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
          core := by
          rfl

/-- Equality form of the genuine simple-polygon interior-angle theorem
supplied by these triangulation rows. -/
theorem simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum
    (R : CoreOuterBoundaryInteriorAngleTriangulationRows.{u} core) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        core =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        core := by
  classical
  rw [R.simplePolygonInteriorAngleSum_eq_triangleAngleSum]
  exact R.triangleAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Inequality form consumed by the W10 boundary-neighbor sector package. -/
theorem simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum
    (R : CoreOuterBoundaryInteriorAngleTriangulationRows.{u} core) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        core <=
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        core :=
  le_of_eq R.simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Genuine outer-cycle triangulation rows supply W10's canonical
predecessor/current/successor sector-sum package. -/
def toBoundaryNeighborSectorAngleSumRows
    (R : CoreOuterBoundaryInteriorAngleTriangulationRows.{u} core) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
      core :=
  open BoundaryCountingInstantiationW10.ClassifiedBoundary in
  BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfSimplePolygonInteriorAngleSum
    R.boundaryLength_ge_three
    R.simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum

/-- The predecessor map carried by native triangulation rows is the canonical
cyclic predecessor, because its successor is definitionally the current
boundary index. -/
theorem concreteSubpolygonPreviousIndex_eq_cyclicPred
    (S : SubpolygonCore.InducedVertexSet G
      (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace))
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace) S)
    (k : Fin (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace).length) :
    R.previousIndex k =
      PlanarInterface.cyclicPred
        (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace).length_pos k := by
  apply PlanarInterface.cyclicSucc_injective
    (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace).length_pos
  rw [R.previousIndex_succ k]
  exact (PlanarInterface.cyclicSucc_cyclicPred
    (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace).length_pos k).symm

/-- Native subpolygon predecessor/current/successor angles on the selected
outer face are the W10 simple-polygon interior angles for the outer core. -/
theorem simplePolygonInteriorAngleSum_eq_boundaryInteriorAngleSum
    (S : SubpolygonCore.InducedVertexSet G
      (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace))
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace) S) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        core =
      SubpolygonAngleRealization.boundaryInteriorAngleSum
        (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace)
        R.previousIndex := by
  classical
  unfold BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
  unfold SubpolygonAngleRealization.boundaryInteriorAngleSum
  apply Finset.sum_congr rfl
  intro k _hk
  unfold BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleAt
  unfold SubpolygonAngleRealization.boundaryInteriorAngleAt
  rw [concreteSubpolygonPreviousIndex_eq_cyclicPred (core := core) S R k]
  rfl

/--
Bridge from the native subpolygon triangulation rows to the outer-boundary
rows.  The native rows already identify their predecessor map as the cyclic
predecessor through `previousIndex_succ`, so no separate angle-sum
compatibility premise is needed.
-/
def ofConcreteSubpolygonInteriorAngleTriangulationRows
    (S : SubpolygonCore.InducedVertexSet G
      (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace))
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G (boundaryCycleOfFaceBoundary core.faceBoundary core.outerFace) S) :
    CoreOuterBoundaryInteriorAngleTriangulationRows.{u} core where
  boundaryLength_ge_three := R.boundaryLength_ge_three
  Triangle := R.Triangle
  triangleFintype := R.triangleFintype
  triangleCount_eq_boundaryLength_sub_two :=
    R.triangleCount_eq_boundaryLength_sub_two
  trianglePoint := R.trianglePoint
  triangleAngleSum_eq_pi := R.triangleAngleSum_eq_pi
  simplePolygonInteriorAngleSum_eq_triangleAngleSum := by
    rw [simplePolygonInteriorAngleSum_eq_boundaryInteriorAngleSum
      (core := core) S R]
    exact R.boundaryInteriorAngleSum_eq_triangleAngleSum

end CoreOuterBoundaryInteriorAngleTriangulationRows

/-! ## Face-boundary cycles supplied by the outer core -/

/--
Concrete subpolygon geometry whose boundary cycle is one recorded face-boundary
cycle from the outer core's face-boundary witness.

This is the most direct route from `OuterBoundaryCore` data to a concrete
subpolygon: the boundary cycle is projected from `core.faceBoundary`, while
the exact induced vertex set and inside/on predicates remain explicit
obligations.
-/
structure CoreFaceSubpolygonGeometryData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) where
  face : core.faceBoundary.Face
  vertices : Finset (Fin n)
  boundary_subset :
    (boundaryCycleOfFaceBoundary core.faceBoundary face).vertexFinset ⊆
      vertices
  insideOrOn : Point -> Prop
  onBoundary : Fin n -> Prop
  boundary_vertex_onBoundary :
    forall k : Fin (core.faceBoundary.boundaryLength face),
      onBoundary (core.faceBoundary.boundaryVertex face k)
  vertices_iff_insideOrOn :
    forall v : Fin n, v ∈ vertices <-> insideOrOn (G.point v)
  onBoundary_iff_cycle :
    forall v : Fin n,
      onBoundary v <->
        Exists fun k : Fin (core.faceBoundary.boundaryLength face) =>
          core.faceBoundary.boundaryVertex face k = v

namespace CoreFaceSubpolygonGeometryData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- The boundary cycle projected from the supplied face-boundary witness. -/
def boundary (D : CoreFaceSubpolygonGeometryData core) :
    BoundaryCycle G :=
  boundaryCycleOfFaceBoundary core.faceBoundary D.face

/-- Forget a face-boundary subpolygon to the generic core-subpolygon geometry
package. -/
def toCoreSubpolygonGeometryData
    (D : CoreFaceSubpolygonGeometryData core) :
    CoreSubpolygonGeometryData core where
  boundary := D.boundary
  vertices := D.vertices
  boundary_subset := D.boundary_subset
  insideOrOn := D.insideOrOn
  onBoundary := D.onBoundary
  boundary_vertex_onBoundary := D.boundary_vertex_onBoundary
  vertices_iff_insideOrOn := D.vertices_iff_insideOrOn
  onBoundary_iff_cycle := D.onBoundary_iff_cycle

@[simp]
theorem toCoreSubpolygonGeometryData_boundary
    (D : CoreFaceSubpolygonGeometryData core) :
    D.toCoreSubpolygonGeometryData.boundary =
      boundaryCycleOfFaceBoundary core.faceBoundary D.face :=
  rfl

/-- The induced vertex-set package for this face-boundary subpolygon. -/
def vertexSet (D : CoreFaceSubpolygonGeometryData core) :
    InducedVertexSet G D.boundary :=
  D.toCoreSubpolygonGeometryData.vertexSet

/-- The computed E13 counts for this face-boundary subpolygon. -/
def counts (D : CoreFaceSubpolygonGeometryData core) :
    SubpolygonDegreeCounts :=
  D.toCoreSubpolygonGeometryData.counts

@[simp]
theorem counts_eq_degreeCounts
    (D : CoreFaceSubpolygonGeometryData core) :
    D.counts = D.vertexSet.degreeCounts :=
  rfl

end CoreFaceSubpolygonGeometryData

/-- Face-boundary subpolygon geometry plus the real angle comparisons needed
for E13. -/
structure CoreFaceSubpolygonAngleData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) where
  geometry : CoreFaceSubpolygonGeometryData core
  geometricAngleSum : Real
  forced_le_geometric :
    geometry.counts.forcedSubpolygonAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= geometry.counts.polygonAngleSum

namespace CoreFaceSubpolygonAngleData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- Forget to the generic core-subpolygon angle package. -/
def toCoreSubpolygonAngleData
    (D : CoreFaceSubpolygonAngleData core) :
    CoreSubpolygonAngleData core where
  geometry := D.geometry.toCoreSubpolygonGeometryData
  geometricAngleSum := D.geometricAngleSum
  forced_le_geometric := by
    simpa [CoreFaceSubpolygonGeometryData.counts] using
      D.forced_le_geometric
  geometric_le_polygon := by
    simpa [CoreFaceSubpolygonGeometryData.counts] using
      D.geometric_le_polygon

/-- The computed E13 counts carried by the face-boundary data. -/
def counts (D : CoreFaceSubpolygonAngleData core) :
    SubpolygonDegreeCounts :=
  D.geometry.counts

@[simp]
theorem toCoreSubpolygonAngleData_counts
    (D : CoreFaceSubpolygonAngleData core) :
    D.toCoreSubpolygonAngleData.counts = D.counts :=
  rfl

/-- The `PlanarBoundaryClosure`-facing cycle/count/angle package. -/
def toSubpolygonCycleCountAngleData
    (D : CoreFaceSubpolygonAngleData core) :
    SubpolygonCycleCountAngleData G :=
  D.toCoreSubpolygonAngleData.toSubpolygonCycleCountAngleData

@[simp]
theorem toSubpolygonCycleCountAngleData_boundary
    (D : CoreFaceSubpolygonAngleData core) :
    D.toSubpolygonCycleCountAngleData.boundary =
      boundaryCycleOfFaceBoundary core.faceBoundary D.geometry.face :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_counts
    (D : CoreFaceSubpolygonAngleData core) :
    D.toSubpolygonCycleCountAngleData.counts = D.counts :=
  rfl

/-- E13 with high-degree slack for the computed induced counts. -/
theorem lowDegreeWithHighDegreeSlack
    (D : CoreFaceSubpolygonAngleData core) :
    D.counts.D5 + 2 * D.counts.D6 + 6 <=
      2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using D.toCoreSubpolygonAngleData.lowDegreeWithHighDegreeSlack

/-- Swanepoel's low-degree conclusion for the computed induced counts. -/
theorem lowDegree
    (D : CoreFaceSubpolygonAngleData core) :
    6 <= 2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using D.toCoreSubpolygonAngleData.lowDegree

/-- Build aggregate face-subpolygon angle data from native concrete
triangulation rows once the supplied geometric angle sum is identified with
the triangulated boundary interior-angle sum. -/
def ofConcreteSubpolygonInteriorAngleTriangulationRows
    (geometry : CoreFaceSubpolygonGeometryData core)
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G geometry.boundary geometry.vertexSet)
    (geometricAngleSum : Real)
    (hforced :
      geometry.counts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hgeometric :
      geometricAngleSum =
        SubpolygonAngleRealization.boundaryInteriorAngleSum
          geometry.boundary R.previousIndex) :
    CoreFaceSubpolygonAngleData core where
  geometry := geometry
  geometricAngleSum := geometricAngleSum
  forced_le_geometric := hforced
  geometric_le_polygon := by
    rw [hgeometric]
    simpa [CoreFaceSubpolygonGeometryData.counts] using
      R.boundaryInteriorAngleSum_le_subpolygonPolygonAngleSum

/-- Build face-subpolygon angle data by using the genuine triangulated
boundary interior-angle sum itself as the geometric angle sum. -/
def ofConcreteSubpolygonInteriorAngleTriangulationRowsBoundaryInteriorAngleSum
    (geometry : CoreFaceSubpolygonGeometryData core)
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G geometry.boundary geometry.vertexSet)
    (hforced :
      geometry.counts.forcedSubpolygonAngleSum <=
        SubpolygonAngleRealization.boundaryInteriorAngleSum
          geometry.boundary R.previousIndex) :
    CoreFaceSubpolygonAngleData core :=
  ofConcreteSubpolygonInteriorAngleTriangulationRows geometry R
    (SubpolygonAngleRealization.boundaryInteriorAngleSum
      geometry.boundary R.previousIndex)
    hforced rfl

/-- Direct E13 slack for a face subpolygon from native triangulation rows and
the forced-angle lower bound for the actual boundary interior-angle sum. -/
theorem lowDegreeWithHighDegreeSlack_ofConcreteSubpolygonInteriorAngleTriangulationRows
    (geometry : CoreFaceSubpolygonGeometryData core)
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G geometry.boundary geometry.vertexSet)
    (hforced :
      geometry.counts.forcedSubpolygonAngleSum <=
        SubpolygonAngleRealization.boundaryInteriorAngleSum
          geometry.boundary R.previousIndex) :
    geometry.counts.D5 + 2 * geometry.counts.D6 + 6 <=
      2 * geometry.counts.D2 + geometry.counts.D3 :=
  (ofConcreteSubpolygonInteriorAngleTriangulationRowsBoundaryInteriorAngleSum
    geometry R hforced).lowDegreeWithHighDegreeSlack

end CoreFaceSubpolygonAngleData

/-! ## Face-boundary subpolygons with actual angle realizations -/

/-- Face-boundary subpolygon geometry plus explicit pointwise real angle data
realizing the E13 lower bound for the computed induced counts. -/
structure CoreFaceSubpolygonAngleRealizationData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) where
  geometry : CoreFaceSubpolygonGeometryData core
  angleRealization :
    ConcreteAngleRealization G geometry.boundary geometry.vertexSet

namespace CoreFaceSubpolygonAngleRealizationData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- Forget to the generic core-subpolygon angle-realization package. -/
def toCoreSubpolygonAngleRealizationData
    (D : CoreFaceSubpolygonAngleRealizationData core) :
    CoreSubpolygonAngleRealizationData core where
  geometry := D.geometry.toCoreSubpolygonGeometryData
  angleRealization := D.angleRealization

/-- The computed E13 counts carried by the face-boundary data. -/
def counts (D : CoreFaceSubpolygonAngleRealizationData core) :
    SubpolygonDegreeCounts :=
  D.geometry.counts

@[simp]
theorem toCoreSubpolygonAngleRealizationData_counts
    (D : CoreFaceSubpolygonAngleRealizationData core) :
    D.toCoreSubpolygonAngleRealizationData.counts = D.counts :=
  rfl

/-- Forget explicit pointwise angle data to the aggregate face-subpolygon angle
package. -/
def toCoreFaceSubpolygonAngleData
    (D : CoreFaceSubpolygonAngleRealizationData core) :
    CoreFaceSubpolygonAngleData core where
  geometry := D.geometry
  geometricAngleSum := D.angleRealization.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, CoreFaceSubpolygonGeometryData.counts] using
      D.angleRealization.forced_le_geometricAngleSum
  geometric_le_polygon := by
    simpa [counts, CoreFaceSubpolygonGeometryData.counts] using
      D.angleRealization.geometric_le_polygon

@[simp]
theorem toCoreFaceSubpolygonAngleData_counts
    (D : CoreFaceSubpolygonAngleRealizationData core) :
    D.toCoreFaceSubpolygonAngleData.counts = D.counts :=
  rfl

/-- The `PlanarBoundaryClosure`-facing cycle/count/angle package. -/
def toSubpolygonCycleCountAngleData
    (D : CoreFaceSubpolygonAngleRealizationData core) :
    SubpolygonCycleCountAngleData G :=
  D.toCoreFaceSubpolygonAngleData.toSubpolygonCycleCountAngleData

@[simp]
theorem toSubpolygonCycleCountAngleData_boundary
    (D : CoreFaceSubpolygonAngleRealizationData core) :
    D.toSubpolygonCycleCountAngleData.boundary =
      boundaryCycleOfFaceBoundary core.faceBoundary D.geometry.face :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_counts
    (D : CoreFaceSubpolygonAngleRealizationData core) :
    D.toSubpolygonCycleCountAngleData.counts = D.counts :=
  rfl

/-- E13 with high-degree slack for the computed induced counts. -/
theorem lowDegreeWithHighDegreeSlack
    (D : CoreFaceSubpolygonAngleRealizationData core) :
    D.counts.D5 + 2 * D.counts.D6 + 6 <=
      2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using
    D.toCoreFaceSubpolygonAngleData.lowDegreeWithHighDegreeSlack

/-- Swanepoel's low-degree conclusion for the computed induced counts. -/
theorem lowDegree
    (D : CoreFaceSubpolygonAngleRealizationData core) :
    6 <= 2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using D.toCoreFaceSubpolygonAngleData.lowDegree

end CoreFaceSubpolygonAngleRealizationData

/-! ## Families of subpolygons for planar-boundary data -/

/-- A family of concrete subpolygon data tied to one outer-boundary core. -/
structure CoreSubpolygonFamilyData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) where
  Subpolygon : Type u
  subpolygonData : Subpolygon -> CoreSubpolygonAngleData core

namespace CoreSubpolygonFamilyData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- Build the exact subpolygon input package consumed by
`PlanarBoundaryClosure.PlanarBoundaryData`. -/
def toPlanarBoundarySubpolygonInputs
    (F : CoreSubpolygonFamilyData.{u} core) :
    PlanarBoundarySubpolygonInputs.{u} G where
  faceBoundary := core.faceBoundary
  Subpolygon := F.Subpolygon
  subpolygonAngleData :=
    fun S => (F.subpolygonData S).toHonestGeometricSubpolygonAngleData

@[simp]
theorem toPlanarBoundarySubpolygonInputs_faceBoundary
    (F : CoreSubpolygonFamilyData.{u} core) :
    F.toPlanarBoundarySubpolygonInputs.faceBoundary = core.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_Subpolygon
    (F : CoreSubpolygonFamilyData.{u} core) :
    F.toPlanarBoundarySubpolygonInputs.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_subpolygonData
    (F : CoreSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    F.toPlanarBoundarySubpolygonInputs.subpolygonData S =
      (F.subpolygonData S).toSubpolygonCycleCountAngleData :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_subpolygonDegreeCounts
    (F : CoreSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    F.toPlanarBoundarySubpolygonInputs.subpolygonDegreeCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- The face-boundary equality required by the planar-boundary facade. -/
theorem sameFaceBoundary
    (F : CoreSubpolygonFamilyData.{u} core) :
    F.toPlanarBoundarySubpolygonInputs.faceBoundary = core.faceBoundary :=
  rfl

/-- E13 for every concrete subpolygon in the family. -/
theorem subpolygonLowDegree
    (F : CoreSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonData S).counts.D2 +
      (F.subpolygonData S).counts.D3 :=
  (F.subpolygonData S).lowDegree

/-- A concrete subpolygon family cannot contain a carrier whose computed
`D2`/`D3` row is strictly below the E13 low-degree threshold. -/
theorem false_of_subpolygonStrictLowDegree_countData
    (F : CoreSubpolygonFamilyData.{u} core)
    {S : F.Subpolygon} {D2 D3 : Nat}
    (hD2 : (F.subpolygonData S).counts.D2 = D2)
    (hD3 : (F.subpolygonData S).counts.D3 = D3)
    (hstrict : 2 * D2 + D3 < 6) :
    False := by
  have hlow := F.subpolygonLowDegree S
  have hstrict' :
      2 * (F.subpolygonData S).counts.D2 +
          (F.subpolygonData S).counts.D3 < 6 := by
    rw [hD2, hD3]
    exact hstrict
  exact (not_lt_of_ge hlow) hstrict'

end CoreSubpolygonFamilyData

/-- Exact carrier/count row for the Lemma 6 strict subpolygon branch.

It names a member of the current core-subpolygon family and records the
computed `D2`/`D3` values that make the low-degree expression strictly below
the E13 threshold. -/
structure CoreSubpolygonCarrierCountData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    {core : OuterBoundaryCore G}
    (F : CoreSubpolygonFamilyData.{u} core) where
  carrier : F.Subpolygon
  D2 : Nat
  D3 : Nat
  counts_D2 : (F.subpolygonData carrier).counts.D2 = D2
  counts_D3 : (F.subpolygonData carrier).counts.D3 = D3
  strict : 2 * D2 + D3 < 6

namespace CoreSubpolygonCarrierCountData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}
variable {F : CoreSubpolygonFamilyData.{u} core}

/-- Forget the named carrier/count row to the existential shape used by older
Lemma 6 bridge theorems. -/
def toExists (D : CoreSubpolygonCarrierCountData F) :
    Exists fun S : F.Subpolygon =>
      Exists fun D2 : Nat =>
        Exists fun D3 : Nat =>
          (F.subpolygonData S).counts.D2 = D2 /\
          (F.subpolygonData S).counts.D3 = D3 /\
          2 * D2 + D3 < 6 :=
  ⟨D.carrier, D.D2, D.D3, D.counts_D2, D.counts_D3, D.strict⟩

/-- Any exact strict carrier row contradicts the E13 low-degree theorem already
carried by the same core-subpolygon family. -/
theorem false (D : CoreSubpolygonCarrierCountData F) : False :=
  F.false_of_subpolygonStrictLowDegree_countData D.counts_D2
    D.counts_D3 D.strict

end CoreSubpolygonCarrierCountData

/-- A family of concrete subpolygon data whose E13 lower bounds are supplied by
explicit pointwise real angle realizations. -/
structure CoreSubpolygonAngleRealizationFamilyData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) where
  Subpolygon : Type u
  subpolygonData : Subpolygon -> CoreSubpolygonAngleRealizationData core

namespace CoreSubpolygonAngleRealizationFamilyData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- Forget explicit pointwise angle realizations to the aggregate concrete
subpolygon family package. -/
def toCoreSubpolygonFamilyData
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core) :
    CoreSubpolygonFamilyData.{u} core where
  Subpolygon := F.Subpolygon
  subpolygonData := fun S => (F.subpolygonData S).toCoreSubpolygonAngleData

/-- Build the exact subpolygon input package consumed by
`PlanarBoundaryClosure.PlanarBoundaryData`. -/
def toPlanarBoundarySubpolygonInputs
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core) :
    PlanarBoundarySubpolygonInputs.{u} G :=
  F.toCoreSubpolygonFamilyData.toPlanarBoundarySubpolygonInputs

@[simp]
theorem toPlanarBoundarySubpolygonInputs_faceBoundary
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core) :
    F.toPlanarBoundarySubpolygonInputs.faceBoundary = core.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_Subpolygon
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core) :
    F.toPlanarBoundarySubpolygonInputs.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_subpolygonDegreeCounts
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    (S : F.Subpolygon) :
    F.toPlanarBoundarySubpolygonInputs.subpolygonDegreeCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- E13 for every concrete subpolygon in the family. -/
theorem subpolygonLowDegree
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonData S).counts.D2 +
      (F.subpolygonData S).counts.D3 :=
  (F.subpolygonData S).lowDegree

end CoreSubpolygonAngleRealizationFamilyData

/-- A family whose members are all projected from face-boundary cycles supplied
by the same outer core. -/
structure CoreFaceSubpolygonFamilyData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) where
  Subpolygon : Type u
  subpolygonData : Subpolygon -> CoreFaceSubpolygonAngleData core

namespace CoreFaceSubpolygonFamilyData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- Forget a face-boundary family to the generic core-subpolygon family. -/
def toCoreSubpolygonFamilyData
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    CoreSubpolygonFamilyData.{u} core where
  Subpolygon := F.Subpolygon
  subpolygonData := fun S => (F.subpolygonData S).toCoreSubpolygonAngleData

/-- Build the exact subpolygon input package consumed by
`PlanarBoundaryClosure.PlanarBoundaryData`. -/
def toPlanarBoundarySubpolygonInputs
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    PlanarBoundarySubpolygonInputs.{u} G :=
  F.toCoreSubpolygonFamilyData.toPlanarBoundarySubpolygonInputs

@[simp]
theorem toPlanarBoundarySubpolygonInputs_faceBoundary
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    F.toPlanarBoundarySubpolygonInputs.faceBoundary = core.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_Subpolygon
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    F.toPlanarBoundarySubpolygonInputs.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_subpolygonDegreeCounts
    (F : CoreFaceSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    F.toPlanarBoundarySubpolygonInputs.subpolygonDegreeCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- The face-boundary equality required by the planar-boundary facade. -/
theorem sameFaceBoundary
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    F.toPlanarBoundarySubpolygonInputs.faceBoundary = core.faceBoundary :=
  rfl

/-- E13 for every face-boundary subpolygon in the family. -/
theorem subpolygonLowDegree
    (F : CoreFaceSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonData S).counts.D2 +
      (F.subpolygonData S).counts.D3 :=
  (F.subpolygonData S).lowDegree

end CoreFaceSubpolygonFamilyData

/-- A face-boundary subpolygon family whose E13 lower bounds are supplied by
explicit pointwise real angle realizations. -/
structure CoreFaceSubpolygonAngleRealizationFamilyData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) where
  Subpolygon : Type u
  subpolygonData : Subpolygon -> CoreFaceSubpolygonAngleRealizationData core

namespace CoreFaceSubpolygonAngleRealizationFamilyData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- Forget a face-boundary realization family to the generic realization
family. -/
def toCoreSubpolygonAngleRealizationFamilyData
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core) :
    CoreSubpolygonAngleRealizationFamilyData.{u} core where
  Subpolygon := F.Subpolygon
  subpolygonData :=
    fun S => (F.subpolygonData S).toCoreSubpolygonAngleRealizationData

/-- Forget explicit pointwise angle realizations to the aggregate face-family
package. -/
def toCoreFaceSubpolygonFamilyData
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core) :
    CoreFaceSubpolygonFamilyData.{u} core where
  Subpolygon := F.Subpolygon
  subpolygonData := fun S => (F.subpolygonData S).toCoreFaceSubpolygonAngleData

/-- Build the exact subpolygon input package consumed by
`PlanarBoundaryClosure.PlanarBoundaryData`. -/
def toPlanarBoundarySubpolygonInputs
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core) :
    PlanarBoundarySubpolygonInputs.{u} G :=
  F.toCoreFaceSubpolygonFamilyData.toPlanarBoundarySubpolygonInputs

@[simp]
theorem toPlanarBoundarySubpolygonInputs_faceBoundary
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core) :
    F.toPlanarBoundarySubpolygonInputs.faceBoundary = core.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_Subpolygon
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core) :
    F.toPlanarBoundarySubpolygonInputs.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_subpolygonDegreeCounts
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    (S : F.Subpolygon) :
    F.toPlanarBoundarySubpolygonInputs.subpolygonDegreeCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- E13 for every face-boundary subpolygon in the family. -/
theorem subpolygonLowDegree
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonData S).counts.D2 +
      (F.subpolygonData S).counts.D3 :=
  (F.subpolygonData S).lowDegree

end CoreFaceSubpolygonAngleRealizationFamilyData

end

end SubpolygonDataConcrete
end Swanepoel
end ErdosProblems1066
