import ErdosProblems1066.Swanepoel.OuterBoundaryCore
import ErdosProblems1066.Swanepoel.SubpolygonAssembly

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

end CoreSubpolygonAngleData

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

end CoreFaceSubpolygonAngleData

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

end CoreSubpolygonFamilyData

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

end

end SubpolygonDataConcrete
end Swanepoel
end ErdosProblems1066
