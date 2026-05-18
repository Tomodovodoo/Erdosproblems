import ErdosProblems1066.Swanepoel.FaceCountingBridge
import ErdosProblems1066.Swanepoel.InducedSubconfiguration

/-!
# Core subpolygon interface

This module records the honest data needed to use Swanepoel's subpolygon
low-degree count.  A subpolygon consists of a concrete boundary cycle in the
canonical unit-distance graph, a finite induced vertex set containing that
cycle, the induced `UDConfig` on that set, and degree counts computed from the
induced adjacency.  The geometric angle lower bound remains an explicit
hypothesis; once supplied, the package routes to the existing E13 counting
theorems.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonCore

open BoundaryCounting
open FaceCountingBridge
open FaceReduction
open PlanarInterface

noncomputable section

variable {n : Nat}

/-! ## Boundary cycles -/

/-- A concrete cyclic boundary walk in a canonical unit-distance graph. -/
structure BoundaryCycle (G : CanonicalStraightLineUnitDistanceGraph n) where
  length : Nat
  length_pos : 0 < length
  vertex : Fin length -> Fin n
  adjacent :
    forall k : Fin length,
      G.Adj (vertex k) (vertex (cyclicSucc length_pos k))
  simple : Function.Injective vertex

namespace BoundaryCycle

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The geometric point of a boundary vertex. -/
def point (C : BoundaryCycle G) (k : Fin C.length) : Point :=
  G.point (C.vertex k)

/-- Boundary-cycle adjacency as unit-distance adjacency in the ambient config. -/
theorem adjacent_unitDistanceAdj (C : BoundaryCycle G) (k : Fin C.length) :
    GraphBridge.UnitDistanceAdj G.config (C.vertex k)
      (C.vertex (cyclicSucc C.length_pos k)) :=
  (G.adj_iff_unitDistanceAdj _ _).1 (C.adjacent k)

/-- Boundary-cycle edges have Euclidean length one. -/
theorem edge_geometry_dist_eq_one (C : BoundaryCycle G) (k : Fin C.length) :
    Geometry.Distance.eucDist (C.point k)
      (C.point (cyclicSucc C.length_pos k)) = 1 :=
  G.adj_geometry_dist_eq_one (C.adjacent k)

/-- The set of ambient vertices occurring on the boundary cycle. -/
def vertexFinset (C : BoundaryCycle G) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin C.length)).image C.vertex

lemma mem_vertexFinset_iff (C : BoundaryCycle G) (v : Fin n) :
    v ∈ C.vertexFinset <-> Exists fun k : Fin C.length => C.vertex k = v := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨k, _hk, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    exact Finset.mem_image_of_mem C.vertex (Finset.mem_univ k)

lemma vertex_mem_vertexFinset (C : BoundaryCycle G) (k : Fin C.length) :
    C.vertex k ∈ C.vertexFinset := by
  exact (C.mem_vertexFinset_iff (C.vertex k)).2 ⟨k, rfl⟩

end BoundaryCycle

/-! ## Induced vertex sets and degrees -/

/-- A finite vertex set inducing the graph used by a subpolygon. -/
structure InducedVertexSet
    (G : CanonicalStraightLineUnitDistanceGraph n) (C : BoundaryCycle G) where
  vertices : Finset (Fin n)
  boundary_subset : C.vertexFinset ⊆ vertices

namespace InducedVertexSet

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}

/-- The induced `UDConfig` on the recorded vertex set. -/
def induced (S : InducedVertexSet G C) :
    InducedSubconfiguration.Induced (m := S.vertices.card) G.config S.vertices :=
  InducedSubconfiguration.ofFinset G.config S.vertices

/-- Boundary vertices belong to the induced vertex set. -/
lemma boundary_vertex_mem (S : InducedVertexSet G C) (k : Fin C.length) :
    C.vertex k ∈ S.vertices :=
  S.boundary_subset (C.vertex_mem_vertexFinset k)

/-- Every boundary vertex has a representative in the induced configuration. -/
lemma exists_induced_index_of_boundary_vertex
    (S : InducedVertexSet G C) (k : Fin C.length) :
    Exists fun i : Fin S.vertices.card => S.induced.embed i = C.vertex k := by
  exact (S.induced.mem_kept_iff (C.vertex k)).1 (S.boundary_vertex_mem k)

/-- Neighbors of an ambient vertex inside the induced subpolygon vertex set. -/
def inducedNeighborSet (S : InducedVertexSet G C) (v : Fin n) : Finset (Fin n) := by
  classical
  exact S.vertices.filter fun u => G.Adj v u

lemma mem_inducedNeighborSet (S : InducedVertexSet G C) (v u : Fin n) :
    u ∈ S.inducedNeighborSet v <-> u ∈ S.vertices ∧ G.Adj v u := by
  classical
  simp [inducedNeighborSet]

/-- The degree of an ambient vertex in the graph induced by the subpolygon set. -/
def inducedDegree (S : InducedVertexSet G C) (v : Fin n) : Nat :=
  (S.inducedNeighborSet v).card

/-- Count boundary vertices whose induced degree is exactly `d`. -/
def countBoundaryDegree (S : InducedVertexSet G C) (d : Nat) : Nat := by
  classical
  exact ((Finset.univ : Finset (Fin C.length)).filter
    fun k => S.inducedDegree (C.vertex k) = d).card

/-- The E13 degree-count input, computed from the induced boundary degrees. -/
def degreeCounts (S : InducedVertexSet G C) : SubpolygonDegreeCounts where
  D2 := S.countBoundaryDegree 2
  D3 := S.countBoundaryDegree 3
  D4 := S.countBoundaryDegree 4
  D5 := S.countBoundaryDegree 5
  D6 := S.countBoundaryDegree 6

lemma degreeCounts_D2 (S : InducedVertexSet G C) :
    S.degreeCounts.D2 = S.countBoundaryDegree 2 :=
  rfl

lemma degreeCounts_D3 (S : InducedVertexSet G C) :
    S.degreeCounts.D3 = S.countBoundaryDegree 3 :=
  rfl

lemma degreeCounts_D4 (S : InducedVertexSet G C) :
    S.degreeCounts.D4 = S.countBoundaryDegree 4 :=
  rfl

lemma degreeCounts_D5 (S : InducedVertexSet G C) :
    S.degreeCounts.D5 = S.countBoundaryDegree 5 :=
  rfl

lemma degreeCounts_D6 (S : InducedVertexSet G C) :
    S.degreeCounts.D6 = S.countBoundaryDegree 6 :=
  rfl

end InducedVertexSet

/-! ## Degree-count data and conversions -/

/-- Computed degree counts together with the geometric angle lower bound needed
by Swanepoel's subpolygon count. -/
structure DegreeCountData
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (C : BoundaryCycle G) (S : InducedVertexSet G C) where
  angleLowerBound : S.degreeCounts.AngleLowerBound

namespace DegreeCountData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {S : InducedVertexSet G C}

/-- Forget the provenance and expose the existing arithmetic input. -/
def toSubpolygonDegreeCounts (_D : DegreeCountData G C S) :
    SubpolygonDegreeCounts :=
  S.degreeCounts

/-- Package the computed counts for the existing canonical face-counting bridge. -/
def toCanonicalSubpolygonCountHypotheses
    (D : DegreeCountData G C S)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    CanonicalSubpolygonCountHypotheses G where
  faceBoundary := faceBoundary
  counts := S.degreeCounts
  angleLowerBound := D.angleLowerBound

/-- E13 with high-degree slack, using the computed induced boundary counts. -/
theorem lowDegreeWithHighDegreeSlack (D : DegreeCountData G C S) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack
    S.degreeCounts D.angleLowerBound

/-- Swanepoel Lemma 4 low-degree conclusion for the computed counts. -/
theorem lowDegreeInequality (D : DegreeCountData G C S) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_inequality
    S.degreeCounts D.angleLowerBound

end DegreeCountData

/-! ## Full subpolygon package -/

/-- Full core package for one subpolygon: boundary cycle, induced vertex set,
canonical induced configuration, computed degree counts, and angle lower bound. -/
structure SubpolygonPackage (G : CanonicalStraightLineUnitDistanceGraph n) where
  boundary : BoundaryCycle G
  vertexSet : InducedVertexSet G boundary
  degreeData : DegreeCountData G boundary vertexSet

namespace SubpolygonPackage

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The induced configuration carried by the package. -/
def induced (P : SubpolygonPackage G) :
    InducedSubconfiguration.Induced
      (m := P.vertexSet.vertices.card) G.config P.vertexSet.vertices :=
  P.vertexSet.induced

/-- The computed E13 degree counts carried by the package. -/
def counts (P : SubpolygonPackage G) : SubpolygonDegreeCounts :=
  P.vertexSet.degreeCounts

/-- The package as the raw existing subpolygon degree-count input. -/
def toSubpolygonDegreeCounts (P : SubpolygonPackage G) : SubpolygonDegreeCounts :=
  P.counts

/-- Convert to the existing canonical face-counting input when face-boundary
data is available. -/
def toCanonicalSubpolygonCountHypotheses
    (P : SubpolygonPackage G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    CanonicalSubpolygonCountHypotheses G :=
  P.degreeData.toCanonicalSubpolygonCountHypotheses faceBoundary

/-- E13 with high-degree slack for the packaged computed counts. -/
theorem lowDegreeWithHighDegreeSlack (P : SubpolygonPackage G) :
    P.counts.D5 + 2 * P.counts.D6 + 6 <=
      2 * P.counts.D2 + P.counts.D3 :=
  P.degreeData.lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4 low-degree conclusion for the packaged computed counts. -/
theorem lowDegreeInequality (P : SubpolygonPackage G) :
    6 <= 2 * P.counts.D2 + P.counts.D3 :=
  P.degreeData.lowDegreeInequality

/-- The same low-degree conclusion routed through the face-counting bridge. -/
theorem lowDegreeInequality_viaFaceCountingBridge
    (P : SubpolygonPackage G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    6 <= 2 * P.counts.D2 + P.counts.D3 :=
  (P.toCanonicalSubpolygonCountHypotheses faceBoundary).subpolygonLowDegreeInequality

end SubpolygonPackage

end

end SubpolygonCore
end Swanepoel
end ErdosProblems1066
