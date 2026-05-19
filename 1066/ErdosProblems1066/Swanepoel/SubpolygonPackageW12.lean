import ErdosProblems1066.Swanepoel.SubpolygonAssembly

set_option autoImplicit false

/-!
# W12 honest subpolygon package

This module is a small worker layer for honest geometric subpolygons.  It keeps
the geometric data explicit, computes the induced vertex set and boundary
degree counts from that data, and then feeds the checked packages in
`SubpolygonAssembly`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonPackageW12

open BoundaryCounting
open FaceReduction
open PlanarInterface
open SubpolygonAssembly
open SubpolygonCore
open SubpolygonAngleRealization

universe u

noncomputable section

variable {n : Nat}

/-! ## Exact inside-or-on vertex sets -/

/-- The finite ambient vertex set whose points satisfy a supplied inside-or-on
predicate. -/
def insideOrOnVertexSet
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (insideOrOn : Point -> Prop)
    [DecidablePred (fun v : Fin n => insideOrOn (G.point v))] :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    fun v : Fin n => insideOrOn (G.point v)

@[simp]
theorem mem_insideOrOnVertexSet
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (insideOrOn : Point -> Prop)
    [DecidablePred (fun v : Fin n => insideOrOn (G.point v))]
    (v : Fin n) :
    v ∈ insideOrOnVertexSet G insideOrOn <->
      insideOrOn (G.point v) := by
  simp [insideOrOnVertexSet]

/-! ## One honest subpolygon -/

/--
Honest geometric data for a subpolygon in a canonical unit-distance graph.

The `vertices_iff_insideOrOn` field says the finite vertex set is exactly the
ambient vertices whose points lie inside or on the supplied region.  The
degree counts below are therefore computed from the induced graph on this
exact finite set, not supplied independently.
-/
structure HonestSubpolygonPackage
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  boundary : BoundaryCycle G
  insideOrOn : Point -> Prop
  onBoundary : Fin n -> Prop
  vertices : Finset (Fin n)
  boundary_subset : boundary.vertexFinset ⊆ vertices
  vertices_iff_insideOrOn :
    forall v : Fin n, v ∈ vertices <-> insideOrOn (G.point v)
  boundary_vertex_onBoundary :
    forall k : Fin boundary.length, onBoundary (boundary.vertex k)
  onBoundary_iff_cycle :
    forall v : Fin n,
      onBoundary v <->
        Exists fun k : Fin boundary.length => boundary.vertex k = v

namespace HonestSubpolygonPackage

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Build an honest package by computing the vertex set from the inside-or-on
predicate. -/
def ofInsideOrOnVertexSet
    (boundary : BoundaryCycle G)
    (insideOrOn : Point -> Prop)
    [DecidablePred (fun v : Fin n => insideOrOn (G.point v))]
    (onBoundary : Fin n -> Prop)
    (boundary_vertex_insideOrOn :
      forall k : Fin boundary.length, insideOrOn (G.point (boundary.vertex k)))
    (boundary_vertex_onBoundary :
      forall k : Fin boundary.length, onBoundary (boundary.vertex k))
    (onBoundary_iff_cycle :
      forall v : Fin n,
        onBoundary v <->
          Exists fun k : Fin boundary.length => boundary.vertex k = v) :
    HonestSubpolygonPackage G where
  boundary := boundary
  insideOrOn := insideOrOn
  onBoundary := onBoundary
  vertices := insideOrOnVertexSet G insideOrOn
  boundary_subset := by
    intro v hv
    rcases (boundary.mem_vertexFinset_iff v).1 hv with ⟨k, hk⟩
    rw [← hk]
    exact (mem_insideOrOnVertexSet G insideOrOn (boundary.vertex k)).2
      (boundary_vertex_insideOrOn k)
  vertices_iff_insideOrOn := mem_insideOrOnVertexSet G insideOrOn
  boundary_vertex_onBoundary := boundary_vertex_onBoundary
  onBoundary_iff_cycle := onBoundary_iff_cycle

/-- Build an honest package whose boundary is a recorded face-boundary cycle,
with the vertex set computed from the inside-or-on predicate. -/
def ofFaceBoundaryInsideOrOnVertexSet
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (face : faceBoundary.Face)
    (insideOrOn : Point -> Prop)
    [DecidablePred (fun v : Fin n => insideOrOn (G.point v))]
    (onBoundary : Fin n -> Prop)
    (boundary_vertex_insideOrOn :
      forall k : Fin (faceBoundary.boundaryLength face),
        insideOrOn (G.point (faceBoundary.boundaryVertex face k)))
    (boundary_vertex_onBoundary :
      forall k : Fin (faceBoundary.boundaryLength face),
        onBoundary (faceBoundary.boundaryVertex face k))
    (onBoundary_iff_cycle :
      forall v : Fin n,
        onBoundary v <->
          Exists fun k : Fin (faceBoundary.boundaryLength face) =>
            faceBoundary.boundaryVertex face k = v) :
    HonestSubpolygonPackage G :=
  ofInsideOrOnVertexSet
    (boundaryCycleOfFaceBoundary faceBoundary face)
    insideOrOn onBoundary
    boundary_vertex_insideOrOn
    boundary_vertex_onBoundary
    onBoundary_iff_cycle

/-- The induced vertex-set package used by `SubpolygonCore`. -/
def vertexSet (P : HonestSubpolygonPackage G) :
    InducedVertexSet G P.boundary :=
  inducedVertexSetOfFinset P.boundary P.vertices P.boundary_subset

@[simp]
theorem vertexSet_vertices (P : HonestSubpolygonPackage G) :
    P.vertexSet.vertices = P.vertices :=
  rfl

/-- The induced subconfiguration on the exact inside-or-on vertex set. -/
def induced (P : HonestSubpolygonPackage G) :
    InducedSubconfiguration.Induced
      (m := P.vertices.card) G.config P.vertices :=
  P.vertexSet.induced

@[simp]
theorem induced_image_univ (P : HonestSubpolygonPackage G) :
    ((Finset.univ : Finset (Fin P.vertices.card)).image P.induced.embed) =
      P.vertices :=
  P.induced.image_univ

/-- A stored vertex is exactly an ambient vertex inside or on the subpolygon. -/
theorem vertex_mem_iff_insideOrOn
    (P : HonestSubpolygonPackage G) (v : Fin n) :
    v ∈ P.vertices <-> P.insideOrOn (G.point v) :=
  P.vertices_iff_insideOrOn v

/-- Every boundary vertex belongs to the induced vertex set. -/
theorem boundary_vertex_mem
    (P : HonestSubpolygonPackage G) (k : Fin P.boundary.length) :
    P.boundary.vertex k ∈ P.vertices :=
  P.boundary_subset (P.boundary.vertex_mem_vertexFinset k)

/-- Every boundary vertex has a representative in the induced configuration. -/
theorem exists_induced_index_of_boundary_vertex
    (P : HonestSubpolygonPackage G) (k : Fin P.boundary.length) :
    Exists fun i : Fin P.vertices.card =>
      P.induced.embed i = P.boundary.vertex k :=
  (P.induced.mem_kept_iff (P.boundary.vertex k)).1
    (P.boundary_vertex_mem k)

/-- The induced neighbor set of a boundary vertex. -/
def boundaryNeighborSet
    (P : HonestSubpolygonPackage G) (k : Fin P.boundary.length) :
    Finset (Fin n) :=
  P.vertexSet.inducedNeighborSet (P.boundary.vertex k)

@[simp]
theorem mem_boundaryNeighborSet
    (P : HonestSubpolygonPackage G) (k : Fin P.boundary.length)
    (v : Fin n) :
    v ∈ P.boundaryNeighborSet k <->
      v ∈ P.vertices ∧ G.Adj (P.boundary.vertex k) v := by
  simp [boundaryNeighborSet, vertexSet, inducedVertexSetOfFinset,
    InducedVertexSet.mem_inducedNeighborSet]

/-- The degree of a boundary vertex in the induced subpolygon graph. -/
def boundaryDegree
    (P : HonestSubpolygonPackage G) (k : Fin P.boundary.length) : Nat :=
  (P.boundaryNeighborSet k).card

@[simp]
theorem boundaryDegree_eq_inducedDegree
    (P : HonestSubpolygonPackage G) (k : Fin P.boundary.length) :
    P.boundaryDegree k =
      P.vertexSet.inducedDegree (P.boundary.vertex k) :=
  rfl

/-- Count boundary vertices with induced degree `d`. -/
def countBoundaryDegree (P : HonestSubpolygonPackage G) (d : Nat) : Nat :=
  P.vertexSet.countBoundaryDegree d

@[simp]
theorem countBoundaryDegree_eq_filter
    (P : HonestSubpolygonPackage G) (d : Nat) :
    P.countBoundaryDegree d =
      ((Finset.univ : Finset (Fin P.boundary.length)).filter
        fun k : Fin P.boundary.length => P.boundaryDegree k = d).card :=
  rfl

/-- The computed E13 degree counts for the induced boundary degrees. -/
def counts (P : HonestSubpolygonPackage G) : SubpolygonDegreeCounts :=
  P.vertexSet.degreeCounts

@[simp]
theorem counts_eq_degreeCounts (P : HonestSubpolygonPackage G) :
    P.counts = P.vertexSet.degreeCounts :=
  rfl

@[simp]
theorem counts_D2 (P : HonestSubpolygonPackage G) :
    P.counts.D2 = P.countBoundaryDegree 2 :=
  rfl

@[simp]
theorem counts_D3 (P : HonestSubpolygonPackage G) :
    P.counts.D3 = P.countBoundaryDegree 3 :=
  rfl

@[simp]
theorem counts_D4 (P : HonestSubpolygonPackage G) :
    P.counts.D4 = P.countBoundaryDegree 4 :=
  rfl

@[simp]
theorem counts_D5 (P : HonestSubpolygonPackage G) :
    P.counts.D5 = P.countBoundaryDegree 5 :=
  rfl

@[simp]
theorem counts_D6 (P : HonestSubpolygonPackage G) :
    P.counts.D6 = P.countBoundaryDegree 6 :=
  rfl

/-- Projection to the honest geometric package in `SubpolygonAssembly`. -/
def toAssemblySubpolygon
    (P : HonestSubpolygonPackage G) :
    HonestGeometricSubpolygon G where
  boundary := P.boundary
  vertexSet := P.vertexSet
  insideOrOn := P.insideOrOn
  onBoundary := P.onBoundary
  boundary_vertex_onBoundary := P.boundary_vertex_onBoundary
  vertices_insideOrOn := by
    intro v hv
    exact (P.vertices_iff_insideOrOn v).1 hv
  onBoundary_iff_cycle := P.onBoundary_iff_cycle

@[simp]
theorem toAssemblySubpolygon_counts
    (P : HonestSubpolygonPackage G) :
    P.toAssemblySubpolygon.counts = P.counts :=
  rfl

/-- Projection to the core package once the computed counts have an angle
lower bound. -/
def toSubpolygonPackage
    (P : HonestSubpolygonPackage G)
    (angleLowerBound : P.counts.AngleLowerBound) :
    SubpolygonPackage G :=
  P.toAssemblySubpolygon.toSubpolygonPackage angleLowerBound

@[simp]
theorem toSubpolygonPackage_counts
    (P : HonestSubpolygonPackage G)
    (angleLowerBound : P.counts.AngleLowerBound) :
    (P.toSubpolygonPackage angleLowerBound).counts = P.counts :=
  rfl

/-- E13 with high-degree slack for the computed induced boundary degrees. -/
theorem lowDegreeWithHighDegreeSlack
    (P : HonestSubpolygonPackage G)
    (angleLowerBound : P.counts.AngleLowerBound) :
    P.counts.D5 + 2 * P.counts.D6 + 6 <=
      2 * P.counts.D2 + P.counts.D3 := by
  simpa using P.toAssemblySubpolygon.lowDegreeWithHighDegreeSlack
    angleLowerBound

/-- Swanepoel's E13 low-degree conclusion for the computed counts. -/
theorem lowDegree
    (P : HonestSubpolygonPackage G)
    (angleLowerBound : P.counts.AngleLowerBound) :
    6 <= 2 * P.counts.D2 + P.counts.D3 := by
  simpa using P.toAssemblySubpolygon.lowDegreeInequality
    angleLowerBound

end HonestSubpolygonPackage

/-! ## Angle data over honest packages -/

/-- An honest subpolygon package plus the real angle comparisons needed by
E13. -/
structure HonestSubpolygonAnglePackage
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  package : HonestSubpolygonPackage G
  geometricAngleSum : Real
  forced_le_geometric :
    package.counts.forcedSubpolygonAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= package.counts.polygonAngleSum

namespace HonestSubpolygonAnglePackage

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The computed E13 counts carried by the package. -/
def counts (A : HonestSubpolygonAnglePackage G) :
    SubpolygonDegreeCounts :=
  A.package.counts

/-- Projection to `SubpolygonAssembly`'s honest angle package. -/
def toAssemblyAngleData
    (A : HonestSubpolygonAnglePackage G) :
    HonestGeometricSubpolygonAngleData G where
  subpolygon := A.package.toAssemblySubpolygon
  geometricAngleSum := A.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, HonestSubpolygonPackage.counts] using
      A.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts, HonestSubpolygonPackage.counts] using
      A.geometric_le_polygon

/-- Projection to the cycle/count/angle data consumed by planar-boundary
assembly. -/
def toSubpolygonCycleCountAngleData
    (A : HonestSubpolygonAnglePackage G) :
    SubpolygonCycleCountAngleData G :=
  A.toAssemblyAngleData.toSubpolygonCycleCountAngleData

@[simp]
theorem toSubpolygonCycleCountAngleData_counts
    (A : HonestSubpolygonAnglePackage G) :
    A.toSubpolygonCycleCountAngleData.counts = A.counts :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_boundary
    (A : HonestSubpolygonAnglePackage G) :
    A.toSubpolygonCycleCountAngleData.boundary = A.package.boundary :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_vertexSet
    (A : HonestSubpolygonAnglePackage G) :
    A.toSubpolygonCycleCountAngleData.vertexSet = A.package.vertexSet :=
  rfl

/-- The angle lower bound for the computed induced counts. -/
theorem angleLowerBound
    (A : HonestSubpolygonAnglePackage G) :
    A.counts.AngleLowerBound := by
  simpa [counts] using A.toAssemblyAngleData.angleLowerBound

/-- Projection to the core package. -/
def toSubpolygonPackage
    (A : HonestSubpolygonAnglePackage G) :
    SubpolygonPackage G :=
  A.package.toSubpolygonPackage A.angleLowerBound

@[simp]
theorem toSubpolygonPackage_counts
    (A : HonestSubpolygonAnglePackage G) :
    A.toSubpolygonPackage.counts = A.counts :=
  rfl

/-- E13 with high-degree slack for the computed induced counts. -/
theorem lowDegreeWithHighDegreeSlack
    (A : HonestSubpolygonAnglePackage G) :
    A.counts.D5 + 2 * A.counts.D6 + 6 <=
      2 * A.counts.D2 + A.counts.D3 := by
  simpa [counts] using A.toAssemblyAngleData.lowDegreeWithHighDegreeSlack

/-- Swanepoel's E13 low-degree conclusion for the computed counts. -/
theorem lowDegree
    (A : HonestSubpolygonAnglePackage G) :
    6 <= 2 * A.counts.D2 + A.counts.D3 := by
  simpa [counts] using A.toAssemblyAngleData.lowDegreeInequality

end HonestSubpolygonAnglePackage

/-! ## Actual angle realizations over honest packages -/

/-- An honest subpolygon package plus explicit pointwise real angle data
realizing the E13 lower bound for its computed induced counts. -/
structure HonestSubpolygonAngleRealizationPackage
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  package : HonestSubpolygonPackage G
  angleRealization :
    SubpolygonAngleRealization.ConcreteAngleRealization G
      package.boundary package.vertexSet

namespace HonestSubpolygonAngleRealizationPackage

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The computed E13 counts carried by the package. -/
def counts (A : HonestSubpolygonAngleRealizationPackage G) :
    SubpolygonDegreeCounts :=
  A.package.counts

/-- Forget explicit pointwise angle data to the aggregate honest angle package. -/
def toHonestSubpolygonAnglePackage
    (A : HonestSubpolygonAngleRealizationPackage G) :
    HonestSubpolygonAnglePackage G where
  package := A.package
  geometricAngleSum := A.angleRealization.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, HonestSubpolygonPackage.counts] using
      A.angleRealization.forced_le_geometricAngleSum
  geometric_le_polygon := by
    simpa [counts, HonestSubpolygonPackage.counts] using
      A.angleRealization.geometric_le_polygon

/-- Projection to `SubpolygonAssembly`'s honest angle package. -/
def toAssemblyAngleData
    (A : HonestSubpolygonAngleRealizationPackage G) :
    HonestGeometricSubpolygonAngleData G :=
  A.toHonestSubpolygonAnglePackage.toAssemblyAngleData

/-- Projection to the cycle/count/angle data consumed by planar-boundary
assembly. -/
def toSubpolygonCycleCountAngleData
    (A : HonestSubpolygonAngleRealizationPackage G) :
    SubpolygonCycleCountAngleData G :=
  A.toAssemblyAngleData.toSubpolygonCycleCountAngleData

@[simp]
theorem toHonestSubpolygonAnglePackage_counts
    (A : HonestSubpolygonAngleRealizationPackage G) :
    A.toHonestSubpolygonAnglePackage.counts = A.counts :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_counts
    (A : HonestSubpolygonAngleRealizationPackage G) :
    A.toSubpolygonCycleCountAngleData.counts = A.counts :=
  rfl

/-- The angle lower bound for the computed induced counts. -/
theorem angleLowerBound
    (A : HonestSubpolygonAngleRealizationPackage G) :
    A.counts.AngleLowerBound := by
  simpa [counts] using A.toHonestSubpolygonAnglePackage.angleLowerBound

/-- Projection to the core package. -/
def toSubpolygonPackage
    (A : HonestSubpolygonAngleRealizationPackage G) :
    SubpolygonPackage G :=
  A.package.toSubpolygonPackage A.angleLowerBound

@[simp]
theorem toSubpolygonPackage_counts
    (A : HonestSubpolygonAngleRealizationPackage G) :
    A.toSubpolygonPackage.counts = A.counts :=
  rfl

/-- E13 with high-degree slack for the computed induced counts. -/
theorem lowDegreeWithHighDegreeSlack
    (A : HonestSubpolygonAngleRealizationPackage G) :
    A.counts.D5 + 2 * A.counts.D6 + 6 <=
      2 * A.counts.D2 + A.counts.D3 := by
  simpa [counts] using
    A.toHonestSubpolygonAnglePackage.lowDegreeWithHighDegreeSlack

/-- Swanepoel's E13 low-degree conclusion for the computed counts. -/
theorem lowDegree
    (A : HonestSubpolygonAngleRealizationPackage G) :
    6 <= 2 * A.counts.D2 + A.counts.D3 := by
  simpa [counts] using A.toHonestSubpolygonAnglePackage.lowDegree

end HonestSubpolygonAngleRealizationPackage

/-! ## Families feeding `SubpolygonAssembly` -/

/-- A family of honest subpolygon angle packages tied to one face-boundary
witness. -/
structure HonestSubpolygonFamilyPackage
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : UnitDistanceFaceBoundaryHypotheses G
  Subpolygon : Type u
  package : Subpolygon -> HonestSubpolygonAnglePackage G

namespace HonestSubpolygonFamilyPackage

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Computed E13 counts for a member of the family. -/
def subpolygonCounts
    (F : HonestSubpolygonFamilyPackage.{u} G) (S : F.Subpolygon) :
    SubpolygonDegreeCounts :=
  (F.package S).counts

/-- Boundary degree function for a family member, computed in the induced
subpolygon graph. -/
def boundaryDegree
    (F : HonestSubpolygonFamilyPackage.{u} G) (S : F.Subpolygon)
    (k : Fin (F.package S).package.boundary.length) : Nat :=
  (F.package S).package.boundaryDegree k

/-- The exact subpolygon inputs consumed by `SubpolygonAssembly`. -/
def toPlanarBoundarySubpolygonInputs
    (F : HonestSubpolygonFamilyPackage.{u} G) :
    PlanarBoundarySubpolygonInputs.{u} G where
  faceBoundary := F.faceBoundary
  Subpolygon := F.Subpolygon
  subpolygonAngleData :=
    fun S => (F.package S).toAssemblyAngleData

@[simp]
theorem toPlanarBoundarySubpolygonInputs_faceBoundary
    (F : HonestSubpolygonFamilyPackage.{u} G) :
    F.toPlanarBoundarySubpolygonInputs.faceBoundary = F.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_Subpolygon
    (F : HonestSubpolygonFamilyPackage.{u} G) :
    F.toPlanarBoundarySubpolygonInputs.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_subpolygonDegreeCounts
    (F : HonestSubpolygonFamilyPackage.{u} G) (S : F.Subpolygon) :
    F.toPlanarBoundarySubpolygonInputs.subpolygonDegreeCounts S =
      F.subpolygonCounts S :=
  rfl

/-- The cycle/count/angle data for one member, in assembly shape. -/
def subpolygonData
    (F : HonestSubpolygonFamilyPackage.{u} G) (S : F.Subpolygon) :
    SubpolygonCycleCountAngleData G :=
  F.toPlanarBoundarySubpolygonInputs.subpolygonData S

@[simp]
theorem subpolygonData_counts
    (F : HonestSubpolygonFamilyPackage.{u} G) (S : F.Subpolygon) :
    (F.subpolygonData S).counts = F.subpolygonCounts S :=
  rfl

/-- Canonical face-counting package for one family member. -/
def canonicalSubpolygonCountHypotheses
    (F : HonestSubpolygonFamilyPackage.{u} G) (S : F.Subpolygon) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G :=
  F.toPlanarBoundarySubpolygonInputs.canonicalSubpolygonCountHypotheses S

@[simp]
theorem canonicalSubpolygonCountHypotheses_faceBoundary
    (F : HonestSubpolygonFamilyPackage.{u} G) (S : F.Subpolygon) :
    (F.canonicalSubpolygonCountHypotheses S).faceBoundary =
      F.faceBoundary :=
  rfl

@[simp]
theorem canonicalSubpolygonCountHypotheses_counts
    (F : HonestSubpolygonFamilyPackage.{u} G) (S : F.Subpolygon) :
    (F.canonicalSubpolygonCountHypotheses S).counts =
      F.subpolygonCounts S :=
  rfl

/-- E13 with high-degree slack for every honest subpolygon in the family. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (F : HonestSubpolygonFamilyPackage.{u} G) (S : F.Subpolygon) :
    (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
      2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 := by
  simpa [subpolygonCounts] using
    F.toPlanarBoundarySubpolygonInputs.subpolygonLowDegreeWithHighDegreeSlack S

/-- Swanepoel's E13 low-degree conclusion for every honest subpolygon in the
family. -/
theorem subpolygonLowDegree
    (F : HonestSubpolygonFamilyPackage.{u} G) (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 +
      (F.subpolygonCounts S).D3 := by
  simpa [subpolygonCounts] using
    F.toPlanarBoundarySubpolygonInputs.subpolygonLowDegree S

end HonestSubpolygonFamilyPackage

/-! ## Families with actual angle realizations -/

/-- A family of honest subpolygon packages whose E13 lower bounds are supplied
by explicit pointwise real angle realizations. -/
structure HonestSubpolygonAngleRealizationFamilyPackage
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : UnitDistanceFaceBoundaryHypotheses G
  Subpolygon : Type u
  package : Subpolygon -> HonestSubpolygonAngleRealizationPackage G

namespace HonestSubpolygonAngleRealizationFamilyPackage

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Computed E13 counts for a member of the family. -/
def subpolygonCounts
    (F : HonestSubpolygonAngleRealizationFamilyPackage.{u} G)
    (S : F.Subpolygon) :
    SubpolygonDegreeCounts :=
  (F.package S).counts

/-- Forget explicit pointwise realizations to the aggregate honest family
package. -/
def toHonestSubpolygonFamilyPackage
    (F : HonestSubpolygonAngleRealizationFamilyPackage.{u} G) :
    HonestSubpolygonFamilyPackage.{u} G where
  faceBoundary := F.faceBoundary
  Subpolygon := F.Subpolygon
  package := fun S => (F.package S).toHonestSubpolygonAnglePackage

/-- The exact subpolygon inputs consumed by `SubpolygonAssembly`. -/
def toPlanarBoundarySubpolygonInputs
    (F : HonestSubpolygonAngleRealizationFamilyPackage.{u} G) :
    PlanarBoundarySubpolygonInputs.{u} G :=
  F.toHonestSubpolygonFamilyPackage.toPlanarBoundarySubpolygonInputs

@[simp]
theorem toPlanarBoundarySubpolygonInputs_faceBoundary
    (F : HonestSubpolygonAngleRealizationFamilyPackage.{u} G) :
    F.toPlanarBoundarySubpolygonInputs.faceBoundary = F.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_Subpolygon
    (F : HonestSubpolygonAngleRealizationFamilyPackage.{u} G) :
    F.toPlanarBoundarySubpolygonInputs.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_subpolygonDegreeCounts
    (F : HonestSubpolygonAngleRealizationFamilyPackage.{u} G)
    (S : F.Subpolygon) :
    F.toPlanarBoundarySubpolygonInputs.subpolygonDegreeCounts S =
      F.subpolygonCounts S :=
  rfl

/-- The cycle/count/angle data for one member, in assembly shape. -/
def subpolygonData
    (F : HonestSubpolygonAngleRealizationFamilyPackage.{u} G)
    (S : F.Subpolygon) :
    SubpolygonCycleCountAngleData G :=
  F.toPlanarBoundarySubpolygonInputs.subpolygonData S

@[simp]
theorem subpolygonData_counts
    (F : HonestSubpolygonAngleRealizationFamilyPackage.{u} G)
    (S : F.Subpolygon) :
    (F.subpolygonData S).counts = F.subpolygonCounts S :=
  rfl

/-- E13 with high-degree slack for every honest subpolygon in the family. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (F : HonestSubpolygonAngleRealizationFamilyPackage.{u} G)
    (S : F.Subpolygon) :
    (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
      2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 := by
  simpa [subpolygonCounts] using
    F.toPlanarBoundarySubpolygonInputs.subpolygonLowDegreeWithHighDegreeSlack S

/-- Swanepoel's E13 low-degree conclusion for every honest subpolygon in the
family. -/
theorem subpolygonLowDegree
    (F : HonestSubpolygonAngleRealizationFamilyPackage.{u} G)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 +
      (F.subpolygonCounts S).D3 := by
  simpa [subpolygonCounts] using
    F.toPlanarBoundarySubpolygonInputs.subpolygonLowDegree S

end HonestSubpolygonAngleRealizationFamilyPackage

end

end SubpolygonPackageW12
end Swanepoel
end ErdosProblems1066
