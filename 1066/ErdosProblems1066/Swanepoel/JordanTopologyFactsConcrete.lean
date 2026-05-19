import ErdosProblems1066.Swanepoel.JordanBoundaryConcrete
import ErdosProblems1066.Swanepoel.CutVertexFinal
import ErdosProblems1066.Swanepoel.MinimalConnectednessClosure
import ErdosProblems1066.Swanepoel.BoundaryWalkBridge
import Mathlib.GroupTheory.Perm.Cycle.Factors

set_option autoImplicit false

/-!
# Concrete Jordan-topology fact package

This file deliberately does not prove or assume a Jordan-curve theorem.  It
isolates a smaller topology-facing package: explicit face-boundary data, a
chosen outer face, and the enclosure predicates for that face.  The lemmas
below are only projections and conversions into the already checked
`JordanBoundaryExtraction`, `JordanBoundaryConcrete`, and `OuterBoundaryCore`
interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace JordanTopologyFactsConcrete

open FaceReduction
open OuterBoundaryInterface

universe u

noncomputable section

variable {n : Nat}

/-! ## Graph-level outer-face data -/

/--
The part of the topology input that names the finite face-boundary surface and
selects the outer face.

No enclosure predicate is included here; this smaller record is enough to
recover the boundary cycle, the old planar face-boundary interface, and the
canonical noncrossing theorem already proved for unit-distance edges.
-/
structure OuterFaceData
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : UnitDistanceFaceBoundaryHypotheses G
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace

namespace OuterFaceData

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Forget to the old planar face-boundary interface. -/
def planarFaceBoundary (D : OuterFaceData G) :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine :=
  D.faceBoundary.toFaceBoundaryHypotheses

@[simp]
theorem planarFaceBoundary_eq (D : OuterFaceData G) :
    D.planarFaceBoundary = D.faceBoundary.toFaceBoundaryHypotheses :=
  rfl

/-- Repackage selected-face data for the extraction facade. -/
def toExtractionOuterFaceData (D : OuterFaceData G) :
    JordanBoundaryExtraction.OuterFaceData G where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

@[simp]
theorem toExtractionOuterFaceData_faceBoundary (D : OuterFaceData G) :
    D.toExtractionOuterFaceData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toExtractionOuterFaceData_outerFace (D : OuterFaceData G) :
    D.toExtractionOuterFaceData.outerFace = D.outerFace :=
  rfl

theorem toExtractionOuterFaceData_outerFace_isOuter (D : OuterFaceData G) :
    D.toExtractionOuterFaceData.faceBoundary.IsOuterFace
      D.toExtractionOuterFaceData.outerFace :=
  D.outerFace_isOuter

/-- Repackage extraction selected-face data in the concrete topology namespace. -/
def ofExtractionOuterFaceData
    (D : JordanBoundaryExtraction.OuterFaceData G) :
    OuterFaceData G where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

@[simp]
theorem ofExtractionOuterFaceData_faceBoundary
    (D : JordanBoundaryExtraction.OuterFaceData G) :
    (ofExtractionOuterFaceData D).faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem ofExtractionOuterFaceData_outerFace
    (D : JordanBoundaryExtraction.OuterFaceData G) :
    (ofExtractionOuterFaceData D).outerFace = D.outerFace :=
  rfl

theorem ofExtractionOuterFaceData_outerFace_isOuter
    (D : JordanBoundaryExtraction.OuterFaceData G) :
    (ofExtractionOuterFaceData D).faceBoundary.IsOuterFace
      (ofExtractionOuterFaceData D).outerFace :=
  D.outerFace_isOuter

@[simp]
theorem ofExtractionOuterFaceData_toExtractionOuterFaceData
    (D : OuterFaceData G) :
    ofExtractionOuterFaceData D.toExtractionOuterFaceData = D := by
  cases D
  rfl

@[simp]
theorem toExtractionOuterFaceData_ofExtractionOuterFaceData
    (D : JordanBoundaryExtraction.OuterFaceData G) :
    (ofExtractionOuterFaceData D).toExtractionOuterFaceData = D := by
  cases D
  rfl

/-- Repackage an already checked core as selected outer-face data. -/
def ofCore (P : OuterBoundaryCore G) : OuterFaceData G where
  faceBoundary := P.faceBoundary
  outerFace := P.outerFace
  outerFace_isOuter := P.outerFace_isOuter

@[simp]
theorem ofCore_faceBoundary (P : OuterBoundaryCore G) :
    (ofCore P).faceBoundary = P.faceBoundary :=
  rfl

@[simp]
theorem ofCore_outerFace (P : OuterBoundaryCore G) :
    (ofCore P).outerFace = P.outerFace :=
  rfl

theorem ofCore_outerFace_isOuter (P : OuterBoundaryCore G) :
    (ofCore P).faceBoundary.IsOuterFace (ofCore P).outerFace :=
  P.outerFace_isOuter

/-- The canonical graph supplies the noncrossing theorem; it is not topology input. -/
theorem pairwiseNoncrossing (_D : OuterFaceData G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  G.pairwiseNoncrossing

/-- The selected outer boundary cycle. -/
def outerCycle (D : OuterFaceData G) : BoundaryCycle G :=
  BoundaryCycle.ofFaceBoundary D.faceBoundary D.outerFace

@[simp]
theorem outerCycle_eq (D : OuterFaceData G) :
    D.outerCycle = BoundaryCycle.ofFaceBoundary D.faceBoundary D.outerFace :=
  rfl

@[simp]
theorem outerCycle_length (D : OuterFaceData G) :
    D.outerCycle.length = D.faceBoundary.boundaryLength D.outerFace :=
  rfl

theorem outerCycle_length_pos (D : OuterFaceData G) :
    0 < D.outerCycle.length :=
  D.faceBoundary.boundaryLength_pos D.outerFace

@[simp]
theorem outerCycle_vertex (D : OuterFaceData G)
    (k : Fin D.outerCycle.length) :
    D.outerCycle.vertex k = D.faceBoundary.boundaryVertex D.outerFace k :=
  rfl

@[simp]
theorem outerCycle_point (D : OuterFaceData G)
    (k : Fin D.outerCycle.length) :
    D.outerCycle.point k =
      G.point (D.faceBoundary.boundaryVertex D.outerFace k) :=
  rfl

/-- The selected outer face is marked outer in the supplied face data. -/
theorem isOuterFace (D : OuterFaceData G) :
    D.faceBoundary.IsOuterFace D.outerFace :=
  D.outerFace_isOuter

/-- The selected boundary cycle is vertex-simple. -/
theorem outerCycle_vertex_injective (D : OuterFaceData G) :
    Function.Injective D.outerCycle.vertex :=
  D.faceBoundary.boundarySimple D.outerFace

/-- Boundary adjacency on the selected cycle, as a graph adjacency fact. -/
theorem outerCycle_adjacent
    (D : OuterFaceData G) (k : Fin D.outerCycle.length) :
    G.Adj (D.outerCycle.vertex k)
      (D.outerCycle.vertex
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) :=
  D.outerCycle.adjacent k

/-- Boundary adjacency on the selected cycle, as unit-distance adjacency. -/
theorem outerCycle_adjacent_unitDistanceAdj
    (D : OuterFaceData G) (k : Fin D.outerCycle.length) :
    GraphBridge.UnitDistanceAdj G.config (D.outerCycle.vertex k)
      (D.outerCycle.vertex
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) :=
  D.outerCycle.adjacent_unitDistanceAdj k

/-- Boundary edges on the selected cycle have Euclidean length one. -/
theorem outerCycle_edge_geometry_dist_eq_one
    (D : OuterFaceData G) (k : Fin D.outerCycle.length) :
    Geometry.Distance.eucDist (D.outerCycle.point k)
      (D.outerCycle.point
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) = 1 :=
  D.outerCycle.edge_geometry_dist_eq_one k

/-- The simple-polygon witness derivable from the canonical noncrossing theorem. -/
def outerSimplePolygon (D : OuterFaceData G) :
    SimplePolygon G D.outerCycle :=
  OuterBoundaryReduction.BoundaryCycle.simplePolygonOfFaceBoundary
    D.faceBoundary D.outerFace

end OuterFaceData

/-! ## Enclosure data over a selected outer face -/

/--
The enclosure predicates attached to a chosen outer face.

This is intentionally just the project-level enclosure record, separated from
`OuterFaceData` so downstream callers can use boundary-cycle projections even
before they have supplied inside/on-boundary predicates.
-/
structure EnclosureData
    {G : CanonicalStraightLineUnitDistanceGraph n} (D : OuterFaceData G) where
  outerEnclosure :
    OuterBoundaryEnclosure G D.faceBoundary D.outerFace

namespace EnclosureData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {D : OuterFaceData G}

/-- Package the selected face and enclosure as the core outer-boundary input. -/
def toCore (E : EnclosureData D) : OuterBoundaryCore G where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter
  outerEnclosure := E.outerEnclosure

@[simp]
theorem toCore_faceBoundary (E : EnclosureData D) :
    E.toCore.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toCore_outerFace (E : EnclosureData D) :
    E.toCore.outerFace = D.outerFace :=
  rfl

theorem toCore_outerFace_isOuter (E : EnclosureData D) :
    E.toCore.faceBoundary.IsOuterFace E.toCore.outerFace :=
  D.outerFace_isOuter

@[simp]
theorem toCore_outerEnclosure (E : EnclosureData D) :
    E.toCore.outerEnclosure = E.outerEnclosure :=
  rfl

/-- Repackage enclosure data for the extraction facade. -/
def toExtractionEnclosureData (E : EnclosureData D) :
    JordanBoundaryExtraction.EnclosureData
      D.toExtractionOuterFaceData where
  outerEnclosure := E.outerEnclosure

@[simp]
theorem toExtractionEnclosureData_outerEnclosure
    (E : EnclosureData D) :
    E.toExtractionEnclosureData.outerEnclosure =
      E.outerEnclosure :=
  rfl

/-- Repackage extraction enclosure data in the concrete topology namespace. -/
def ofExtractionEnclosureData
    (D : JordanBoundaryExtraction.OuterFaceData G)
    (E : JordanBoundaryExtraction.EnclosureData D) :
    EnclosureData (OuterFaceData.ofExtractionOuterFaceData D) where
  outerEnclosure := E.outerEnclosure

@[simp]
theorem ofExtractionEnclosureData_outerEnclosure
    (D : JordanBoundaryExtraction.OuterFaceData G)
    (E : JordanBoundaryExtraction.EnclosureData D) :
    (ofExtractionEnclosureData D E).outerEnclosure =
      E.outerEnclosure :=
  rfl

/-- Repackage selected-face and enclosure data as extraction data. -/
def toExtractionData (E : EnclosureData D) :
    JordanBoundaryExtraction.Data G where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter
  outerEnclosure := E.outerEnclosure

@[simp]
theorem toExtractionData_faceBoundary (E : EnclosureData D) :
    E.toExtractionData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toExtractionData_outerFace (E : EnclosureData D) :
    E.toExtractionData.outerFace = D.outerFace :=
  rfl

theorem toExtractionData_outerFace_isOuter (E : EnclosureData D) :
    E.toExtractionData.faceBoundary.IsOuterFace
      E.toExtractionData.outerFace :=
  D.outerFace_isOuter

@[simp]
theorem toExtractionData_outerEnclosure (E : EnclosureData D) :
    E.toExtractionData.outerEnclosure = E.outerEnclosure :=
  rfl

@[simp]
theorem toExtractionData_toCore (E : EnclosureData D) :
    E.toExtractionData.toCore = E.toCore :=
  rfl

/-- Repackage an already checked core as enclosure data. -/
def ofCore (P : OuterBoundaryCore G) :
    EnclosureData (OuterFaceData.ofCore P) where
  outerEnclosure := P.outerEnclosure

@[simp]
theorem ofCore_outerEnclosure (P : OuterBoundaryCore G) :
    (ofCore P).outerEnclosure = P.outerEnclosure :=
  rfl

@[simp]
theorem ofCore_toCore (P : OuterBoundaryCore G) :
    (ofCore P).toCore = P := by
  cases P
  rfl

/-- Boundary vertices satisfy the supplied boundary predicate. -/
theorem boundary_vertex_onBoundary
    (E : EnclosureData D)
    (k : Fin (D.faceBoundary.boundaryLength D.outerFace)) :
    E.outerEnclosure.onBoundary
      (D.faceBoundary.boundaryVertex D.outerFace k) :=
  E.outerEnclosure.boundary_vertex_onBoundary k

/-- The same boundary predicate, expressed on the selected boundary cycle. -/
theorem outerCycle_vertex_onBoundary
    (E : EnclosureData D) (k : Fin D.outerCycle.length) :
    E.outerEnclosure.onBoundary (D.outerCycle.vertex k) :=
  E.outerEnclosure.boundary_vertex_onBoundary k

/-- Boundary points satisfy the supplied inside-or-on predicate. -/
theorem boundary_point_insideOrOn
    (E : EnclosureData D)
    (k : Fin (D.faceBoundary.boundaryLength D.outerFace)) :
    E.outerEnclosure.insideOrOn
      (G.point (D.faceBoundary.boundaryVertex D.outerFace k)) :=
  E.outerEnclosure.boundary_point_insideOrOn k

/-- The same inside-or-on predicate, expressed on the selected boundary cycle. -/
theorem outerCycle_point_insideOrOn
    (E : EnclosureData D) (k : Fin D.outerCycle.length) :
    E.outerEnclosure.insideOrOn (D.outerCycle.point k) :=
  E.outerEnclosure.boundary_point_insideOrOn k

/-- Every ambient vertex lies inside or on the supplied enclosure. -/
theorem all_vertices_insideOrOn (E : EnclosureData D) (v : Fin n) :
    E.outerEnclosure.insideOrOn (G.point v) :=
  E.outerEnclosure.all_vertices_insideOrOn v

/-- The supplied boundary predicate is exactly the selected outer face cycle. -/
theorem onBoundary_iff_outer_cycle (E : EnclosureData D) (v : Fin n) :
    E.outerEnclosure.onBoundary v <->
      Exists fun k : Fin D.outerCycle.length => D.outerCycle.vertex k = v :=
  E.outerEnclosure.onBoundary_iff_outer_cycle v

/-- Boundary-cycle membership gives the supplied boundary predicate. -/
theorem onBoundary_of_exists_outerCycle
    (E : EnclosureData D) {v : Fin n}
    (hv : Exists fun k : Fin D.outerCycle.length => D.outerCycle.vertex k = v) :
    E.outerEnclosure.onBoundary v :=
  (E.onBoundary_iff_outer_cycle v).2 hv

/-- The supplied boundary predicate gives boundary-cycle membership. -/
theorem exists_outerCycle_of_onBoundary
    (E : EnclosureData D) {v : Fin n}
    (hv : E.outerEnclosure.onBoundary v) :
    Exists fun k : Fin D.outerCycle.length => D.outerCycle.vertex k = v :=
  (E.onBoundary_iff_outer_cycle v).1 hv

/-! ## Planar-boundary closure bridge -/

/-- Extend the selected outer face and enclosure by angle/subpolygon data to
the full planar-boundary package. -/
def toPlanarBoundaryData
    (E : EnclosureData D)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G where
  core := E.toCore
  outerAngleBounds := outerAngleBounds
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData

@[simp]
theorem toPlanarBoundaryData_core
    (E : EnclosureData D)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (E.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).core =
      E.toCore :=
  rfl

@[simp]
theorem toPlanarBoundaryData_faceBoundary
    (E : EnclosureData D)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (E.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).faceBoundary =
      D.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_planarFaceBoundary
    (E : EnclosureData D)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (E.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).planarFaceBoundary =
      D.planarFaceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerFace
    (E : EnclosureData D)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (E.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).outerFace =
      D.outerFace :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerCycle
    (E : EnclosureData D)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (E.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).outerCycle =
      D.outerCycle :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerBoundaryCounts
    (E : EnclosureData D)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (E.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).outerBoundaryCounts =
      outerAngleBounds.counts :=
  rfl

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (E : EnclosureData D)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (E.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).Subpolygon =
      Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundaryData_subpolygonData
    (E : EnclosureData D)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (E.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).subpolygonData =
      subpolygonData :=
  rfl

/-- The full planar-boundary theorem summary obtained from the assembled data. -/
theorem toPlanarBoundaryData_faceCountingTheorems
    (E : EnclosureData D)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      (E.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData) :=
  (E.toPlanarBoundaryData outerAngleBounds Subpolygon
    subpolygonData).faceCountingTheorems

end EnclosureData

/-! ## Concrete `UDConfig` wrapper -/

/-- The canonical graph attached to a `UDConfig`, re-exported for this file. -/
abbrev canonicalGraph (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n :=
  JordanBoundaryConcrete.canonicalGraph C

/--
Concrete topology facts for the canonical unit-distance graph of a `UDConfig`.

The noncrossing theorem is still proved by the project.  The fields here are
only the remaining explicit topology-facing data: face boundaries, the selected
outer face, and enclosure predicates for that face.
-/
structure TopologyFacts (C : _root_.UDConfig n) where
  outerFaceData : OuterFaceData (canonicalGraph C)
  enclosureData : EnclosureData outerFaceData

namespace TopologyFacts

variable {C : _root_.UDConfig n}

/-- The supplied face-boundary data. -/
def faceBoundary (T : TopologyFacts C) :
    UnitDistanceFaceBoundaryHypotheses (canonicalGraph C) :=
  T.outerFaceData.faceBoundary

/-- The supplied selected outer face. -/
def outerFace (T : TopologyFacts C) : T.faceBoundary.Face :=
  T.outerFaceData.outerFace

/-- The supplied proof that the selected face is outer. -/
theorem outerFace_isOuter (T : TopologyFacts C) :
    T.faceBoundary.IsOuterFace T.outerFace :=
  T.outerFaceData.outerFace_isOuter

/-- The supplied enclosure predicates and projection facts. -/
def outerEnclosure (T : TopologyFacts C) :
    OuterBoundaryEnclosure (canonicalGraph C) T.faceBoundary T.outerFace :=
  T.enclosureData.outerEnclosure

/-- Convert to the extraction facade used by the existing boundary modules. -/
def toExtractionData (T : TopologyFacts C) :
    JordanBoundaryExtraction.Data (canonicalGraph C) where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter
  outerEnclosure := T.outerEnclosure

/-- Convert to the explicit missing-topology package from `JordanBoundaryConcrete`. -/
def toMissingTopologyFacts (T : TopologyFacts C) :
    JordanBoundaryConcrete.MissingTopologyFacts C where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter
  outerEnclosure := T.outerEnclosure

/-- Convert directly to the checked outer-boundary core. -/
def toCore (T : TopologyFacts C) : OuterBoundaryCore (canonicalGraph C) :=
  T.enclosureData.toCore

/-- Build concrete topology facts from the extraction facade. -/
def ofExtractionData
    (D : JordanBoundaryExtraction.Data (canonicalGraph C)) :
    TopologyFacts C where
  outerFaceData :=
    OuterFaceData.ofExtractionOuterFaceData D.toOuterFaceData
  enclosureData :=
    EnclosureData.ofExtractionEnclosureData
      D.toOuterFaceData D.toEnclosureData

/-- Build concrete topology facts from the older missing-topology package. -/
def ofMissingTopologyFacts
    (D : JordanBoundaryConcrete.MissingTopologyFacts C) :
    TopologyFacts C :=
  ofExtractionData D.toExtractionData

/-- Build concrete topology facts from an already checked outer-boundary core. -/
def ofCore (P : OuterBoundaryCore (canonicalGraph C)) :
    TopologyFacts C where
  outerFaceData := OuterFaceData.ofCore P
  enclosureData := EnclosureData.ofCore P

@[simp]
theorem toExtractionData_faceBoundary (T : TopologyFacts C) :
    T.toExtractionData.faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem toExtractionData_outerFace (T : TopologyFacts C) :
    T.toExtractionData.outerFace = T.outerFace :=
  rfl

theorem toExtractionData_outerFace_isOuter (T : TopologyFacts C) :
    T.toExtractionData.faceBoundary.IsOuterFace
      T.toExtractionData.outerFace :=
  T.outerFace_isOuter

@[simp]
theorem toExtractionData_outerEnclosure (T : TopologyFacts C) :
    T.toExtractionData.outerEnclosure = T.outerEnclosure :=
  rfl

@[simp]
theorem toMissingTopologyFacts_faceBoundary (T : TopologyFacts C) :
    T.toMissingTopologyFacts.faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem toMissingTopologyFacts_outerFace (T : TopologyFacts C) :
    T.toMissingTopologyFacts.outerFace = T.outerFace :=
  rfl

theorem toMissingTopologyFacts_outerFace_isOuter (T : TopologyFacts C) :
    T.toMissingTopologyFacts.faceBoundary.IsOuterFace
      T.toMissingTopologyFacts.outerFace :=
  T.outerFace_isOuter

@[simp]
theorem toMissingTopologyFacts_outerEnclosure (T : TopologyFacts C) :
    T.toMissingTopologyFacts.outerEnclosure = T.outerEnclosure :=
  rfl

@[simp]
theorem toCore_faceBoundary (T : TopologyFacts C) :
    T.toCore.faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem toCore_outerFace (T : TopologyFacts C) :
    T.toCore.outerFace = T.outerFace :=
  rfl

theorem toCore_outerFace_isOuter (T : TopologyFacts C) :
    T.toCore.faceBoundary.IsOuterFace T.toCore.outerFace :=
  T.outerFace_isOuter

@[simp]
theorem toCore_outerEnclosure (T : TopologyFacts C) :
    T.toCore.outerEnclosure = T.outerEnclosure :=
  rfl

@[simp]
theorem toExtractionData_ofExtractionData
    (D : JordanBoundaryExtraction.Data (canonicalGraph C)) :
    (ofExtractionData D).toExtractionData = D := by
  cases D
  rfl

@[simp]
theorem ofExtractionData_toExtractionData (T : TopologyFacts C) :
    ofExtractionData T.toExtractionData = T := by
  cases T with
  | mk D E =>
    cases D
    cases E
    rfl

@[simp]
theorem toMissingTopologyFacts_ofMissingTopologyFacts
    (D : JordanBoundaryConcrete.MissingTopologyFacts C) :
    (ofMissingTopologyFacts D).toMissingTopologyFacts = D := by
  cases D
  rfl

@[simp]
theorem ofMissingTopologyFacts_toMissingTopologyFacts
    (T : TopologyFacts C) :
    ofMissingTopologyFacts T.toMissingTopologyFacts = T := by
  cases T with
  | mk D E =>
    cases D
    cases E
    rfl

@[simp]
theorem toCore_ofCore
    (P : OuterBoundaryCore (canonicalGraph C)) :
    (ofCore P).toCore = P := by
  cases P
  rfl

@[simp]
theorem ofCore_toCore (T : TopologyFacts C) :
    ofCore T.toCore = T := by
  cases T with
  | mk D E =>
    cases D
    cases E
    rfl

/-! ## Concrete projections -/

/-- The selected outer boundary cycle. -/
def outerCycle (T : TopologyFacts C) :
    BoundaryCycle (canonicalGraph C) :=
  T.outerFaceData.outerCycle

@[simp]
theorem outerCycle_eq (T : TopologyFacts C) :
    T.outerCycle = BoundaryCycle.ofFaceBoundary T.faceBoundary T.outerFace :=
  rfl

@[simp]
theorem outerCycle_length (T : TopologyFacts C) :
    T.outerCycle.length = T.faceBoundary.boundaryLength T.outerFace :=
  rfl

@[simp]
theorem outerCycle_vertex
    (T : TopologyFacts C) (k : Fin T.outerCycle.length) :
    T.outerCycle.vertex k = T.faceBoundary.boundaryVertex T.outerFace k :=
  rfl

theorem outerCycle_vertex_injective (T : TopologyFacts C) :
    Function.Injective T.outerCycle.vertex :=
  T.outerFaceData.outerCycle_vertex_injective

theorem outerCycle_adjacent
    (T : TopologyFacts C) (k : Fin T.outerCycle.length) :
    (canonicalGraph C).Adj (T.outerCycle.vertex k)
      (T.outerCycle.vertex
        (PlanarInterface.cyclicSucc T.outerCycle.length_pos k)) :=
  T.outerFaceData.outerCycle_adjacent k

theorem outerCycle_adjacent_unitDistanceAdj
    (T : TopologyFacts C) (k : Fin T.outerCycle.length) :
    GraphBridge.UnitDistanceAdj (canonicalGraph C).config
      (T.outerCycle.vertex k)
      (T.outerCycle.vertex
        (PlanarInterface.cyclicSucc T.outerCycle.length_pos k)) :=
  T.outerFaceData.outerCycle_adjacent_unitDistanceAdj k

theorem outerCycle_edge_geometry_dist_eq_one
    (T : TopologyFacts C) (k : Fin T.outerCycle.length) :
    Geometry.Distance.eucDist (T.outerCycle.point k)
      (T.outerCycle.point
        (PlanarInterface.cyclicSucc T.outerCycle.length_pos k)) = 1 :=
  T.outerFaceData.outerCycle_edge_geometry_dist_eq_one k

/-- The selected outer boundary cycle has the derived simple-polygon witness. -/
def outerSimplePolygon (T : TopologyFacts C) :
    SimplePolygon (canonicalGraph C) T.outerCycle :=
  T.outerFaceData.outerSimplePolygon

theorem boundary_vertex_onBoundary
    (T : TopologyFacts C)
    (k : Fin (T.faceBoundary.boundaryLength T.outerFace)) :
    T.outerEnclosure.onBoundary (T.faceBoundary.boundaryVertex T.outerFace k) :=
  T.enclosureData.boundary_vertex_onBoundary k

theorem outerCycle_vertex_onBoundary
    (T : TopologyFacts C) (k : Fin T.outerCycle.length) :
    T.outerEnclosure.onBoundary (T.outerCycle.vertex k) :=
  T.enclosureData.outerCycle_vertex_onBoundary k

theorem boundary_point_insideOrOn
    (T : TopologyFacts C)
    (k : Fin (T.faceBoundary.boundaryLength T.outerFace)) :
    T.outerEnclosure.insideOrOn
      ((canonicalGraph C).point (T.faceBoundary.boundaryVertex T.outerFace k)) :=
  T.enclosureData.boundary_point_insideOrOn k

theorem outerCycle_point_insideOrOn
    (T : TopologyFacts C) (k : Fin T.outerCycle.length) :
    T.outerEnclosure.insideOrOn (T.outerCycle.point k) :=
  T.enclosureData.outerCycle_point_insideOrOn k

theorem all_vertices_insideOrOn (T : TopologyFacts C) (v : Fin n) :
    T.outerEnclosure.insideOrOn ((canonicalGraph C).point v) :=
  T.enclosureData.all_vertices_insideOrOn v

theorem onBoundary_iff_outer_cycle (T : TopologyFacts C) (v : Fin n) :
    T.outerEnclosure.onBoundary v <->
      Exists fun k : Fin T.outerCycle.length => T.outerCycle.vertex k = v :=
  T.enclosureData.onBoundary_iff_outer_cycle v

theorem onBoundary_of_exists_outerCycle
    (T : TopologyFacts C) {v : Fin n}
    (hv : Exists fun k : Fin T.outerCycle.length => T.outerCycle.vertex k = v) :
    T.outerEnclosure.onBoundary v :=
  (T.onBoundary_iff_outer_cycle v).2 hv

theorem exists_outerCycle_of_onBoundary
    (T : TopologyFacts C) {v : Fin n}
    (hv : T.outerEnclosure.onBoundary v) :
    Exists fun k : Fin T.outerCycle.length => T.outerCycle.vertex k = v :=
  (T.onBoundary_iff_outer_cycle v).1 hv

/-- The old planar face-boundary interface obtained from the supplied faces. -/
def planarFaceBoundary (T : TopologyFacts C) :
    PlanarInterface.FaceBoundaryHypotheses (canonicalGraph C).toStraightLine :=
  T.outerFaceData.planarFaceBoundary

@[simp]
theorem planarFaceBoundary_eq (T : TopologyFacts C) :
    T.planarFaceBoundary = T.faceBoundary.toFaceBoundaryHypotheses :=
  rfl

/-- Pairwise noncrossing projected from the canonical graph theorem. -/
theorem pairwiseNoncrossing (T : TopologyFacts C) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  T.outerFaceData.pairwiseNoncrossing

/-! ## Conversion compatibility and planar-boundary closure bridge -/

@[simp]
theorem toExtractionData_toCore (T : TopologyFacts C) :
    T.toExtractionData.toCore = T.toCore :=
  rfl

@[simp]
theorem toMissingTopologyFacts_toCore (T : TopologyFacts C) :
    T.toMissingTopologyFacts.toCore = T.toCore :=
  rfl

@[simp]
theorem toCore_toFaceBoundaryHypotheses (T : TopologyFacts C) :
    T.toCore.toFaceBoundaryHypotheses = T.planarFaceBoundary :=
  rfl

@[simp]
theorem toCore_outerCycle (T : TopologyFacts C) :
    T.toCore.outerCycle = T.outerCycle :=
  rfl

@[simp]
theorem toExtractionData_outerCycle (T : TopologyFacts C) :
    T.toExtractionData.outerCycle = T.outerCycle :=
  rfl

@[simp]
theorem toMissingTopologyFacts_outerCycle (T : TopologyFacts C) :
    T.toMissingTopologyFacts.outerCycle = T.outerCycle :=
  rfl

@[simp]
theorem toCore_outerSimplePolygon (T : TopologyFacts C) :
    T.toCore.outerSimplePolygon = T.outerSimplePolygon :=
  rfl

@[simp]
theorem toExtractionData_planarFaceBoundary (T : TopologyFacts C) :
    T.toExtractionData.planarFaceBoundary = T.planarFaceBoundary :=
  rfl

@[simp]
theorem toMissingTopologyFacts_planarFaceBoundary (T : TopologyFacts C) :
    T.toMissingTopologyFacts.planarFaceBoundary = T.planarFaceBoundary :=
  rfl

/-- Extend the concrete topology facts by angle/subpolygon data to the full
planar-boundary package. -/
def toPlanarBoundaryData
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (canonicalGraph C) :=
  T.enclosureData.toPlanarBoundaryData
    outerAngleBounds Subpolygon subpolygonData

@[simp]
theorem toPlanarBoundaryData_core
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).core =
      T.toCore :=
  rfl

@[simp]
theorem toPlanarBoundaryData_faceBoundary
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).faceBoundary =
      T.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_planarFaceBoundary
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).planarFaceBoundary =
      T.planarFaceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerFace
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).outerFace =
      T.outerFace :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerCycle
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).outerCycle =
      T.outerCycle :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerBoundaryCounts
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).outerBoundaryCounts =
      outerAngleBounds.counts :=
  rfl

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).Subpolygon =
      Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundaryData_subpolygonData
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).subpolygonData =
      subpolygonData :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerAngleData_core
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).outerAngleData.core =
      T.toCore :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerAngleData_angleBounds
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData).outerAngleData.angleBounds =
      outerAngleBounds :=
  rfl

/-- The full planar-boundary theorem summary obtained from concrete topology
facts plus angle and subpolygon data. -/
theorem toPlanarBoundaryData_faceCountingTheorems
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData) :=
  (T.toPlanarBoundaryData outerAngleBounds Subpolygon
    subpolygonData).faceCountingTheorems

/-! ## Direct adapters from older topology packages to planar-boundary data -/

/-- Convert the older missing-topology package directly to full
planar-boundary data once angle/subpolygon data is supplied. -/
def planarBoundaryDataOfMissingTopologyFacts
    (D : JordanBoundaryConcrete.MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (canonicalGraph C) :=
  (ofMissingTopologyFacts D).toPlanarBoundaryData
    outerAngleBounds Subpolygon subpolygonData

@[simp]
theorem planarBoundaryDataOfMissingTopologyFacts_core
    (D : JordanBoundaryConcrete.MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (planarBoundaryDataOfMissingTopologyFacts
      D outerAngleBounds Subpolygon subpolygonData).core = D.toCore :=
  rfl

/-- Convert extraction data directly to full planar-boundary data once
angle/subpolygon data is supplied. -/
def planarBoundaryDataOfExtractionData
    (D : JordanBoundaryExtraction.Data (canonicalGraph C))
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (canonicalGraph C) :=
  (ofExtractionData D).toPlanarBoundaryData
    outerAngleBounds Subpolygon subpolygonData

@[simp]
theorem planarBoundaryDataOfExtractionData_core
    (D : JordanBoundaryExtraction.Data (canonicalGraph C))
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (planarBoundaryDataOfExtractionData
      D outerAngleBounds Subpolygon subpolygonData).core = D.toCore :=
  rfl

end TopologyFacts

/-! ## W12 minimal-failure topology frontier -/

namespace MinimalFailureTopology

variable {C : _root_.UDConfig n}

/--
The raw face/enclosure field still needed after the graph route is cleared.

It is deliberately only the dependent face-boundary payload: a finite
face-boundary surface for the canonical graph, a selected outer face, and
enclosure predicates for that selected face.
-/
def ExactOuterBoundaryTopologyFields (C : _root_.UDConfig n) : Prop :=
  Exists fun H : UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C) =>
    Exists fun F : H.Face =>
      H.IsOuterFace F /\
        Nonempty (OuterBoundaryEnclosure (canonicalGraph C) H F)

/-- Package concrete topology facts as the exact raw face/enclosure field. -/
theorem exactOuterBoundaryTopologyFields_of_topologyFacts
    {C : _root_.UDConfig n}
    (T : TopologyFacts.{0} C) :
    ExactOuterBoundaryTopologyFields C :=
  ⟨T.faceBoundary, T.outerFace, T.outerFace_isOuter,
    ⟨T.outerEnclosure⟩⟩

/-- Package missing-topology facts as the exact raw face/enclosure field. -/
theorem exactOuterBoundaryTopologyFields_of_missingTopologyFacts
    {C : _root_.UDConfig n}
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    ExactOuterBoundaryTopologyFields C :=
  ⟨T.faceBoundary, T.outerFace, T.outerFace_isOuter,
    ⟨T.outerEnclosure⟩⟩

/-- Package an already checked outer-boundary core as the exact raw field. -/
theorem exactOuterBoundaryTopologyFields_of_outerBoundaryCore
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (canonicalGraph C)) :
    ExactOuterBoundaryTopologyFields C :=
  ⟨P.faceBoundary, P.outerFace, P.outerFace_isOuter,
    ⟨P.outerEnclosure⟩⟩

/-- Minimal failure alone gives a positive vertex count. -/
theorem positiveCard_of_minimalClearedFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    0 < n := by
  rcases MinimalConnectednessClosure.fin_nonempty_of_minimalClearedFailure
      (C := C) hmin with ⟨v⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le v.val) v.isLt

/--
The graph-side data already obtained from minimality: connectedness,
degree range, and canonical noncrossing.  This still contains no face or
enclosure data.
-/
structure MinimalFailureConnectedNoncrossingRoute
    (C : _root_.UDConfig n) : Prop where
  positiveCard : 0 < n
  connectedDegreeRange : CutVertexFinal.ConnectedDegreeRangeCertificate C
  pairwiseNoncrossing :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet

/-- Minimal cleared failure supplies the connected/noncrossing graph route. -/
theorem connectedNoncrossingRoute_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalFailureConnectedNoncrossingRoute C := by
  let hn := positiveCard_of_minimalClearedFailure (C := C) hmin
  exact
    { positiveCard := hn
      connectedDegreeRange :=
        CutVertexFinal.connectedDegreeRangeCertificate_of_minimalFailure
          (C := C) hn hmin
      pairwiseNoncrossing := (canonicalGraph C).pairwiseNoncrossing }

/--
The graph-side route after the current conditional no-cut input is supplied.
It packages connectedness, no-cut, degree range, and canonical noncrossing,
but still does not produce the face/enclosure fields.
-/
structure MinimalFailureGraphRoute
    (C : _root_.UDConfig n) : Prop where
  positiveCard : 0 < n
  connectedNoCutDegreeRange :
    CutVertexFinal.ConnectedNoCutDegreeRangeCertificate C
  pairwiseNoncrossing :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet

/-- The no-cut graph route from minimality plus the current slack payload. -/
theorem graphRoute_of_minimalFailure_remainingSlack
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexFinal.RemainingNoCutSlackFact C) :
    MinimalFailureGraphRoute C := by
  let hn := positiveCard_of_minimalClearedFailure (C := C) hmin
  exact
    { positiveCard := hn
      connectedNoCutDegreeRange :=
        CutVertexFinal.connectedNoCutDegreeRangeCertificate_of_minimalFailure_remainingSlack
          (C := C) hn hmin hslack
      pairwiseNoncrossing := (canonicalGraph C).pairwiseNoncrossing }

/-! ## Finite planar outer-component theorem surface -/

/--
Checked graph-side inputs for the missing finite planar straight-line
outer-component theorem.

This record intentionally contains no `insideOrOn` or `onBoundary` predicate.
Those predicates are exactly the remaining topology content needed to construct
`JordanBoundaryConcrete.ChosenJordanOuterComponentRow`.
-/
structure FinitePlanarOuterComponentInputs
    (C : _root_.UDConfig n) : Prop where
  connected : (GraphBridge.unitDistanceSimpleGraph C).Connected
  noCutVertex : CutVertexInterface.NoCutVertex C
  pairwiseNoncrossing :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet
  hasUnitDistanceCycle :
    Nonempty (JordanBoundaryConcrete.UnitDistanceCycleBoundary C)

namespace FinitePlanarOuterComponentInputs

variable {C : _root_.UDConfig n}

/-- Connectedness gives the preconnected form used by graph-cut APIs. -/
theorem preconnected (I : FinitePlanarOuterComponentInputs C) :
    (GraphBridge.unitDistanceSimpleGraph C).Preconnected :=
  I.connected.preconnected

/-- Connectedness also carries nonempty vertex type data. -/
theorem vertex_nonempty (I : FinitePlanarOuterComponentInputs C) :
    Nonempty (Fin n) :=
  I.connected.nonempty

/-- The supplied cycle input can always be chosen with length at least three. -/
theorem exists_unitDistanceCycle_length_ge_three
    (I : FinitePlanarOuterComponentInputs C) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      3 <= B.length := by
  rcases I.hasUnitDistanceCycle with ⟨B⟩
  exact ⟨B, B.length_ge_three⟩

/-- The supplied graph cycle carries the checked simple-polygon witness already
available from the local noncrossing bridge. -/
theorem exists_unitDistanceCycle_simplePolygon
    (I : FinitePlanarOuterComponentInputs C) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      Nonempty
        (OuterBoundaryInterface.SimplePolygon
          (canonicalGraph C) B.toBoundaryCycle) := by
  rcases I.hasUnitDistanceCycle with ⟨B⟩
  exact ⟨B, ⟨B.toSimplePolygon⟩⟩

end FinitePlanarOuterComponentInputs

/-! ### Dart/rotation-system source rows -/

/-- An oriented unit-distance edge of the Mathlib graph attached to `C`. -/
structure UnitDistanceDart (C : _root_.UDConfig n) where
  tail : Fin n
  head : Fin n
  adj : (GraphBridge.unitDistanceSimpleGraph C).Adj tail head

namespace UnitDistanceDart

variable {C : _root_.UDConfig n}

/-- The endpoints of a unit-distance dart are distinct. -/
theorem tail_ne_head (d : UnitDistanceDart C) : d.tail ≠ d.head :=
  (GraphBridge.unitDistanceSimpleGraph C).ne_of_adj d.adj

/-- The dart's geometric edge has Euclidean length one. -/
theorem dist_eq_one (d : UnitDistanceDart C) :
    _root_.eucDist (C.pts d.tail) (C.pts d.head) = 1 :=
  (GraphBridge.unitDistanceSimpleGraph_adj C d.tail d.head).1 d.adj

/-- Reverse the orientation of a unit-distance dart. -/
def reverse (d : UnitDistanceDart C) : UnitDistanceDart C where
  tail := d.head
  head := d.tail
  adj := (GraphBridge.unitDistanceSimpleGraph C).symm d.adj

@[simp]
theorem reverse_tail (d : UnitDistanceDart C) :
    d.reverse.tail = d.head :=
  rfl

@[simp]
theorem reverse_head (d : UnitDistanceDart C) :
    d.reverse.head = d.tail :=
  rfl

@[simp]
theorem reverse_reverse (d : UnitDistanceDart C) :
    d.reverse.reverse = d := by
  cases d
  rfl

theorem reverse_injective :
    Function.Injective (UnitDistanceDart.reverse (C := C)) := by
  intro d e h
  calc
    d = d.reverse.reverse := (reverse_reverse d).symm
    _ = e.reverse.reverse := by rw [h]
    _ = e := reverse_reverse e

/-- A unit-distance dart is an edge of the canonical straight-line graph. -/
theorem canonicalAdj (d : UnitDistanceDart C) :
    (canonicalGraph C).Adj d.tail d.head :=
  ((canonicalGraph C).adj_iff_unitDistanceAdj d.tail d.head).2 d.dist_eq_one

/-- The oriented dart carried by one directed edge of a concrete unit-distance
cycle boundary. -/
def ofBoundary
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) : UnitDistanceDart C where
  tail := B.vertex k
  head := B.vertex (PlanarInterface.cyclicSucc B.length_pos k)
  adj :=
    (GraphBridge.unitDistanceSimpleGraph_adj C _ _).2
      (((canonicalGraph C).adj_iff_unitDistanceAdj _ _).1
        (B.adjacent k))

@[simp]
theorem ofBoundary_tail
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) :
    (ofBoundary B k).tail = B.vertex k :=
  rfl

@[simp]
theorem ofBoundary_head
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) :
    (ofBoundary B k).head =
      B.vertex (PlanarInterface.cyclicSucc B.length_pos k) :=
  rfl

/-- Forget a dart to its ordered endpoint pair. -/
def endpointPair (d : UnitDistanceDart C) : Fin n × Fin n :=
  (d.tail, d.head)

theorem endpointPair_injective :
    Function.Injective (endpointPair (C := C)) := by
  intro d e h
  cases d with
  | mk tail head adj =>
    cases e with
    | mk tail' head' adj' =>
      simp [endpointPair] at h
      rcases h with ⟨htail, hhead⟩
      subst tail'
      subst head'
      rfl

theorem ext_endpoints {d e : UnitDistanceDart C}
    (htail : d.tail = e.tail) (hhead : d.head = e.head) :
    d = e :=
  endpointPair_injective (by simp [endpointPair, htail, hhead])

theorem eq_ofBoundary_of_tail_head
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) (d : UnitDistanceDart C)
    (htail : d.tail = B.vertex k)
    (hhead :
      d.head =
        B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) :
    d = ofBoundary B k := by
  apply endpointPair_injective
  simp [endpointPair, htail, hhead]

instance instFinite : Finite (UnitDistanceDart C) :=
  Finite.of_injective (endpointPair (C := C)) endpointPair_injective

/-- The outgoing-dart subtype at the dart's tail. -/
def outgoing (d : UnitDistanceDart C) :
    {e : UnitDistanceDart C // e.tail = d.tail} :=
  ⟨d, rfl⟩

end UnitDistanceDart

/-- Unit-distance darts outgoing from a fixed vertex. -/
abbrev OutgoingUnitDistanceDart
    (C : _root_.UDConfig n) (v : Fin n) :=
  {d : UnitDistanceDart C // d.tail = v}

namespace OutgoingUnitDistanceDart

variable {C : _root_.UDConfig n} {v w : Fin n}

/-- Transport outgoing unit-distance darts along an equality of tail vertices. -/
def congr (h : v = w) :
    OutgoingUnitDistanceDart C v ≃ OutgoingUnitDistanceDart C w where
  toFun d := ⟨d.1, by simpa [h] using d.2⟩
  invFun d := ⟨d.1, by simpa [h] using d.2⟩
  left_inv := by
    intro d
    cases d
    rfl
  right_inv := by
    intro d
    cases d
    rfl

end OutgoingUnitDistanceDart

instance instFiniteOutgoingUnitDistanceDart
    (C : _root_.UDConfig n) (v : Fin n) :
    Finite (OutgoingUnitDistanceDart C v) := by
  infer_instance

/--
Cyclic angular successor data for the outgoing unit-distance darts around one
vertex.  The future geometry theorem must instantiate this from the real
angular order of incident straight-line unit edges.
-/
structure VertexCyclicAngularSuccessor
    (C : _root_.UDConfig n) (v : Fin n) where
  next :
    OutgoingUnitDistanceDart C v -> OutgoingUnitDistanceDart C v
  prev :
    OutgoingUnitDistanceDart C v -> OutgoingUnitDistanceDart C v
  next_prev : forall d, next (prev d) = d
  prev_next : forall d, prev (next d) = d

namespace VertexCyclicAngularSuccessor

variable {C : _root_.UDConfig n} {v : Fin n}

theorem next_injective (S : VertexCyclicAngularSuccessor C v) :
    Function.Injective S.next := by
  intro a b h
  calc
    a = S.prev (S.next a) := (S.prev_next a).symm
    _ = S.prev (S.next b) := by rw [h]
    _ = b := S.prev_next b

theorem prev_injective (S : VertexCyclicAngularSuccessor C v) :
    Function.Injective S.prev := by
  intro a b h
  calc
    a = S.next (S.prev a) := (S.next_prev a).symm
    _ = S.next (S.prev b) := by rw [h]
    _ = b := S.next_prev b

theorem next_surjective (S : VertexCyclicAngularSuccessor C v) :
    Function.Surjective S.next := by
  intro d
  exact ⟨S.prev d, S.next_prev d⟩

theorem prev_surjective (S : VertexCyclicAngularSuccessor C v) :
    Function.Surjective S.prev := by
  intro d
  exact ⟨S.next d, S.prev_next d⟩

theorem next_bijective (S : VertexCyclicAngularSuccessor C v) :
    Function.Bijective S.next :=
  ⟨S.next_injective, S.next_surjective⟩

theorem prev_bijective (S : VertexCyclicAngularSuccessor C v) :
    Function.Bijective S.prev :=
  ⟨S.prev_injective, S.prev_surjective⟩

end VertexCyclicAngularSuccessor

/--
A cyclic order of the finite unit-neighbor darts at one vertex, expressed as a
permutation of the outgoing-dart subtype.  The geometry work can populate this
with the angular order of the incident straight-line unit edges.
-/
structure VertexFiniteUnitNeighborCyclicOrder
    (C : _root_.UDConfig n) (v : Fin n) where
  perm : Equiv.Perm (OutgoingUnitDistanceDart C v)

namespace VertexFiniteUnitNeighborCyclicOrder

variable {C : _root_.UDConfig n} {v : Fin n}

/-- Convert a finite-neighbor cyclic order into the local successor rows. -/
def toVertexCyclicAngularSuccessor
    (P : VertexFiniteUnitNeighborCyclicOrder C v) :
    VertexCyclicAngularSuccessor C v where
  next := P.perm
  prev := P.perm.symm
  next_prev := P.perm.apply_symm_apply
  prev_next := P.perm.symm_apply_apply

/-- Repackage local successor rows as a permutation of the finite neighbor set. -/
def ofVertexCyclicAngularSuccessor
    (S : VertexCyclicAngularSuccessor C v) :
    VertexFiniteUnitNeighborCyclicOrder C v where
  perm :=
    { toFun := S.next
      invFun := S.prev
      left_inv := S.prev_next
      right_inv := S.next_prev }

@[simp]
theorem toVertexCyclicAngularSuccessor_ofVertexCyclicAngularSuccessor
    (S : VertexCyclicAngularSuccessor C v) :
    (ofVertexCyclicAngularSuccessor S).toVertexCyclicAngularSuccessor = S := by
  cases S
  rfl

@[simp]
theorem toVertexCyclicAngularSuccessor_next
    (P : VertexFiniteUnitNeighborCyclicOrder C v)
    (d : OutgoingUnitDistanceDart C v) :
    P.toVertexCyclicAngularSuccessor.next d = P.perm d :=
  rfl

@[simp]
theorem toVertexCyclicAngularSuccessor_prev
    (P : VertexFiniteUnitNeighborCyclicOrder C v)
    (d : OutgoingUnitDistanceDart C v) :
    P.toVertexCyclicAngularSuccessor.prev d = P.perm.symm d :=
  rfl

/-- Extract the actual per-vertex angular successor rows from finite
unit-neighbor cyclic-order data. -/
def angularSuccessorRows
    (cyclicOrderAt :
      (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v) :
    (v : Fin n) -> VertexCyclicAngularSuccessor C v :=
  fun v => (cyclicOrderAt v).toVertexCyclicAngularSuccessor

@[simp]
theorem angularSuccessorRows_next
    (cyclicOrderAt :
      (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v)
    (v : Fin n) (d : OutgoingUnitDistanceDart C v) :
    (angularSuccessorRows cyclicOrderAt v).next d =
      (cyclicOrderAt v).perm d :=
  rfl

@[simp]
theorem angularSuccessorRows_prev
    (cyclicOrderAt :
      (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v)
    (v : Fin n) (d : OutgoingUnitDistanceDart C v) :
    (angularSuccessorRows cyclicOrderAt v).prev d =
      (cyclicOrderAt v).perm.symm d :=
  rfl

/-- The identity order is a concrete cyclic-order row on the finite outgoing
unit-neighbor dart set at one vertex. -/
def identity (C : _root_.UDConfig n) (v : Fin n) :
    VertexFiniteUnitNeighborCyclicOrder C v where
  perm := Equiv.refl _

@[simp]
theorem identity_perm (C : _root_.UDConfig n) (v : Fin n) :
    (identity C v).perm = Equiv.refl _ :=
  rfl

/-- Pointwise identity cyclic-order rows for all finite outgoing unit-neighbor
dart sets of the configuration. -/
def identityRows (C : _root_.UDConfig n) :
    (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v :=
  fun v => identity C v

@[simp]
theorem identityRows_apply (C : _root_.UDConfig n) (v : Fin n) :
    identityRows C v = identity C v :=
  rfl

/-- The angular-successor rows extracted from the concrete identity cyclic
orders on every finite outgoing unit-neighbor set. -/
def identityAngularSuccessorRows (C : _root_.UDConfig n) :
    (v : Fin n) -> VertexCyclicAngularSuccessor C v :=
  angularSuccessorRows (identityRows C)

@[simp]
theorem identityAngularSuccessorRows_apply
    (C : _root_.UDConfig n) (v : Fin n) :
    identityAngularSuccessorRows C v =
      (identity C v).toVertexCyclicAngularSuccessor :=
  rfl

@[simp]
theorem identityAngularSuccessorRows_next
    (C : _root_.UDConfig n) (v : Fin n)
    (d : OutgoingUnitDistanceDart C v) :
    (identityAngularSuccessorRows C v).next d = d :=
  rfl

@[simp]
theorem identityAngularSuccessorRows_prev
    (C : _root_.UDConfig n) (v : Fin n)
    (d : OutgoingUnitDistanceDart C v) :
    (identityAngularSuccessorRows C v).prev d = d :=
  rfl

theorem nonempty (C : _root_.UDConfig n) (v : Fin n) :
    Nonempty (VertexFiniteUnitNeighborCyclicOrder C v) :=
  ⟨identity C v⟩

theorem rows_nonempty (C : _root_.UDConfig n) :
    Nonempty ((v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v) :=
  ⟨identityRows C⟩

/-- The concrete finite-neighbor rows give concrete angular-successor rows at
every vertex. -/
theorem angularSuccessorRows_nonempty (C : _root_.UDConfig n) :
    Nonempty ((v : Fin n) -> VertexCyclicAngularSuccessor C v) :=
  ⟨identityAngularSuccessorRows C⟩

end VertexFiniteUnitNeighborCyclicOrder

/--
Finite-neighbor cyclic-order source for the whole unit-distance graph.  This
is the concrete source row from which the rotation system is mechanically
assembled.
-/
structure FiniteUnitNeighborRotationSource
    (C : _root_.UDConfig n) where
  cyclicOrderAt :
    (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v

/-- Rotation-system source data: a cyclic angular successor at every vertex. -/
structure UnitDistanceRotationSystem (C : _root_.UDConfig n) where
  rotationAt :
    (v : Fin n) -> VertexCyclicAngularSuccessor C v

namespace FiniteUnitNeighborRotationSource

variable {C : _root_.UDConfig n}

/-- Package a family of per-vertex finite unit-neighbor cyclic orders as the
whole-graph finite-neighbor rotation source. -/
def ofCyclicOrderRows
    (cyclicOrderAt :
      (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v) :
    FiniteUnitNeighborRotationSource C where
  cyclicOrderAt := cyclicOrderAt

@[simp]
theorem ofCyclicOrderRows_cyclicOrderAt
    (cyclicOrderAt :
      (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v) :
    (ofCyclicOrderRows cyclicOrderAt).cyclicOrderAt = cyclicOrderAt :=
  rfl

/-- The actual per-vertex successor rows carried by finite unit-neighbor
cyclic-order source data. -/
def angularSuccessorRows
    (S : FiniteUnitNeighborRotationSource C) :
    (v : Fin n) -> VertexCyclicAngularSuccessor C v :=
  VertexFiniteUnitNeighborCyclicOrder.angularSuccessorRows S.cyclicOrderAt

@[simp]
theorem angularSuccessorRows_ofCyclicOrderRows
    (cyclicOrderAt :
      (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v) :
    (ofCyclicOrderRows cyclicOrderAt).angularSuccessorRows =
      VertexFiniteUnitNeighborCyclicOrder.angularSuccessorRows cyclicOrderAt :=
  rfl

@[simp]
theorem angularSuccessorRows_next
    (S : FiniteUnitNeighborRotationSource C)
    (v : Fin n) (d : OutgoingUnitDistanceDart C v) :
    (S.angularSuccessorRows v).next d =
      (S.cyclicOrderAt v).perm d :=
  rfl

@[simp]
theorem angularSuccessorRows_prev
    (S : FiniteUnitNeighborRotationSource C)
    (v : Fin n) (d : OutgoingUnitDistanceDart C v) :
    (S.angularSuccessorRows v).prev d =
      (S.cyclicOrderAt v).perm.symm d :=
  rfl

/-- Repackage a per-vertex angular successor family as finite-neighbor cyclic
orders.  This is the narrow conversion the eventual Euclidean angular-order
proof needs before the rotation system is assembled. -/
def ofAngularSuccessor
    (rotationAt : (v : Fin n) -> VertexCyclicAngularSuccessor C v) :
    FiniteUnitNeighborRotationSource C where
  cyclicOrderAt := fun v =>
    VertexFiniteUnitNeighborCyclicOrder.ofVertexCyclicAngularSuccessor
      (rotationAt v)

/-- A per-vertex angular successor family supplies the finite-neighbor
rotation source. -/
theorem nonempty_of_angularSuccessor
    (rotationAt : (v : Fin n) -> VertexCyclicAngularSuccessor C v) :
    Nonempty (FiniteUnitNeighborRotationSource C) :=
  ⟨ofAngularSuccessor rotationAt⟩

@[simp]
theorem angularSuccessorRows_ofAngularSuccessor
    (rotationAt : (v : Fin n) -> VertexCyclicAngularSuccessor C v) :
    (ofAngularSuccessor rotationAt).angularSuccessorRows = rotationAt := by
  funext v
  exact
    VertexFiniteUnitNeighborCyclicOrder.toVertexCyclicAngularSuccessor_ofVertexCyclicAngularSuccessor
      (rotationAt v)

/-- Assemble the graph rotation system from per-vertex finite-neighbor orders. -/
def toUnitDistanceRotationSystem
    (S : FiniteUnitNeighborRotationSource C) :
    UnitDistanceRotationSystem C where
  rotationAt := S.angularSuccessorRows

/-- The concrete finite-neighbor source obtained from identity cyclic orders on
the finite outgoing unit-neighbor sets. -/
def identity (C : _root_.UDConfig n) :
    FiniteUnitNeighborRotationSource C :=
  ofCyclicOrderRows
    (VertexFiniteUnitNeighborCyclicOrder.identityRows C)

@[simp]
theorem identity_cyclicOrderAt (C : _root_.UDConfig n) :
    (identity C).cyclicOrderAt =
      VertexFiniteUnitNeighborCyclicOrder.identityRows C :=
  rfl

@[simp]
theorem identity_angularSuccessorRows (C : _root_.UDConfig n) :
    (identity C).angularSuccessorRows =
      VertexFiniteUnitNeighborCyclicOrder.identityAngularSuccessorRows C :=
  rfl

theorem nonempty (C : _root_.UDConfig n) :
    Nonempty (FiniteUnitNeighborRotationSource C) :=
  ⟨identity C⟩

@[simp]
theorem toUnitDistanceRotationSystem_rotationAt
    (S : FiniteUnitNeighborRotationSource C) (v : Fin n) :
    S.toUnitDistanceRotationSystem.rotationAt v =
      S.angularSuccessorRows v :=
  rfl

@[simp]
theorem toUnitDistanceRotationSystem_ofAngularSuccessor
    (rotationAt : (v : Fin n) -> VertexCyclicAngularSuccessor C v) :
    (ofAngularSuccessor rotationAt).toUnitDistanceRotationSystem =
      { rotationAt := rotationAt : UnitDistanceRotationSystem C } := by
  exact congrArg UnitDistanceRotationSystem.mk
    (angularSuccessorRows_ofAngularSuccessor rotationAt)

@[simp]
theorem toUnitDistanceRotationSystem_ofCyclicOrderRows
    (cyclicOrderAt :
      (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v) :
    (ofCyclicOrderRows cyclicOrderAt).toUnitDistanceRotationSystem =
      { rotationAt :=
          VertexFiniteUnitNeighborCyclicOrder.angularSuccessorRows
            cyclicOrderAt : UnitDistanceRotationSystem C } :=
  rfl

@[simp]
theorem identity_toUnitDistanceRotationSystem (C : _root_.UDConfig n) :
    (identity C).toUnitDistanceRotationSystem =
      { rotationAt :=
          VertexFiniteUnitNeighborCyclicOrder.identityAngularSuccessorRows
            C : UnitDistanceRotationSystem C } :=
  rfl

end FiniteUnitNeighborRotationSource

namespace UnitDistanceRotationSystem

variable {C : _root_.UDConfig n}

/-- Assemble a rotation system directly from finite unit-neighbor cyclic-order
rows. -/
def ofFiniteUnitNeighborCyclicOrderRows
    (cyclicOrderAt :
      (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v) :
    UnitDistanceRotationSystem C :=
  (FiniteUnitNeighborRotationSource.ofCyclicOrderRows
    cyclicOrderAt).toUnitDistanceRotationSystem

@[simp]
theorem ofFiniteUnitNeighborCyclicOrderRows_rotationAt
    (cyclicOrderAt :
      (v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v)
    (v : Fin n) :
    (ofFiniteUnitNeighborCyclicOrderRows cyclicOrderAt).rotationAt v =
      VertexFiniteUnitNeighborCyclicOrder.angularSuccessorRows
        cyclicOrderAt v :=
  rfl

/-- The concrete rotation system from identity cyclic orders on finite outgoing
unit-neighbor sets. -/
def identity (C : _root_.UDConfig n) : UnitDistanceRotationSystem C :=
  (FiniteUnitNeighborRotationSource.identity C).toUnitDistanceRotationSystem

@[simp]
theorem identity_rotationAt
    (C : _root_.UDConfig n) (v : Fin n) :
    (identity C).rotationAt v =
      VertexFiniteUnitNeighborCyclicOrder.identityAngularSuccessorRows C v :=
  rfl

/-- The finite outgoing unit-neighbor sets always supply a concrete rotation
system. -/
theorem nonempty (C : _root_.UDConfig n) :
    Nonempty (UnitDistanceRotationSystem C) :=
  ⟨identity C⟩

/-- Repackage a rotation system as cyclic permutations of finite neighbor sets. -/
def toFiniteUnitNeighborRotationSource
    (R : UnitDistanceRotationSystem C) :
    FiniteUnitNeighborRotationSource C where
  cyclicOrderAt := fun v =>
    VertexFiniteUnitNeighborCyclicOrder.ofVertexCyclicAngularSuccessor
      (R.rotationAt v)

/-- Rotation systems are equivalent to per-vertex cyclic orders on finite
unit-neighbor dart sets. -/
theorem nonempty_iff_finiteUnitNeighborRotationSource
    (C : _root_.UDConfig n) :
    Nonempty (UnitDistanceRotationSystem C) <->
      Nonempty (FiniteUnitNeighborRotationSource C) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.toFiniteUnitNeighborRotationSource⟩
  · rintro ⟨S⟩
    exact ⟨S.toUnitDistanceRotationSystem⟩

/-- A finite-neighbor cyclic-order source supplies the rotation system needed
by face-orbit construction. -/
theorem nonempty_of_finiteUnitNeighborRotationSource
    (S : FiniteUnitNeighborRotationSource C) :
    Nonempty (UnitDistanceRotationSystem C) :=
  ⟨S.toUnitDistanceRotationSystem⟩

/-- The next outgoing dart in the cyclic order around the same tail vertex. -/
def nextAround (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) : UnitDistanceDart C :=
  let e := (R.rotationAt d.tail).next d.outgoing
  { tail := d.tail
    head := e.1.head
    adj := by simpa [e.2] using e.1.adj }

/-- The previous outgoing dart in the cyclic order around the same tail vertex. -/
def prevAround (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) : UnitDistanceDart C :=
  let e := (R.rotationAt d.tail).prev d.outgoing
  { tail := d.tail
    head := e.1.head
    adj := by simpa [e.2] using e.1.adj }

@[simp]
theorem nextAround_tail_eq (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    (R.nextAround d).tail = d.tail :=
  rfl

@[simp]
theorem prevAround_tail_eq (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    (R.prevAround d).tail = d.tail :=
  rfl

@[simp]
theorem nextAround_outgoing (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    (R.nextAround d).outgoing =
      (R.rotationAt d.tail).next d.outgoing := by
  apply Subtype.ext
  apply UnitDistanceDart.endpointPair_injective
  apply Prod.ext
  · exact ((R.rotationAt d.tail).next d.outgoing).2.symm
  · rfl

@[simp]
theorem prevAround_outgoing (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    (R.prevAround d).outgoing =
      (R.rotationAt d.tail).prev d.outgoing := by
  apply Subtype.ext
  apply UnitDistanceDart.endpointPair_injective
  apply Prod.ext
  · exact ((R.rotationAt d.tail).prev d.outgoing).2.symm
  · rfl

theorem nextAround_adj (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    (GraphBridge.unitDistanceSimpleGraph C).Adj
      (R.nextAround d).tail (R.nextAround d).head :=
  (R.nextAround d).adj

theorem prevAround_adj (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    (GraphBridge.unitDistanceSimpleGraph C).Adj
      (R.prevAround d).tail (R.prevAround d).head :=
  (R.prevAround d).adj

theorem prevAround_nextAround (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    R.prevAround (R.nextAround d) = d := by
  have h :
      (R.prevAround (R.nextAround d)).outgoing = d.outgoing := by
    simpa using (R.rotationAt d.tail).prev_next d.outgoing
  exact congrArg Subtype.val h

theorem nextAround_prevAround (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    R.nextAround (R.prevAround d) = d := by
  have h :
      (R.nextAround (R.prevAround d)).outgoing = d.outgoing := by
    simpa using (R.rotationAt d.tail).next_prev d.outgoing
  exact congrArg Subtype.val h

/-- The face successor of a dart: reverse it, then advance around the new tail. -/
def faceSucc (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) : UnitDistanceDart C :=
  R.nextAround d.reverse

theorem faceSucc_tail_eq_head (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    (R.faceSucc d).tail = d.head := by
  simp [faceSucc]

theorem faceSucc_adj (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    (GraphBridge.unitDistanceSimpleGraph C).Adj
      (R.faceSucc d).tail (R.faceSucc d).head :=
  (R.faceSucc d).adj

theorem faceSucc_dist_eq_one (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    _root_.eucDist (C.pts (R.faceSucc d).tail)
      (C.pts (R.faceSucc d).head) = 1 :=
  (R.faceSucc d).dist_eq_one

theorem faceSucc_canonicalAdj (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    (canonicalGraph C).Adj (R.faceSucc d).tail (R.faceSucc d).head :=
  (R.faceSucc d).canonicalAdj

theorem endpoint_chaining_of_faceSucc_eq_next
    (R : UnitDistanceRotationSystem C)
    {d e : UnitDistanceDart C}
    (h : R.faceSucc d = e) :
    d.head = e.tail := by
  rw [← h]
  exact (R.faceSucc_tail_eq_head d).symm

/-- The face predecessor of a dart: move back around the tail, then reverse. -/
def facePred (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) : UnitDistanceDart C :=
  (R.prevAround d).reverse

@[simp]
theorem facePred_faceSucc (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    R.facePred (R.faceSucc d) = d := by
  simp [facePred, faceSucc, R.prevAround_nextAround d.reverse]

@[simp]
theorem faceSucc_facePred (R : UnitDistanceRotationSystem C)
    (d : UnitDistanceDart C) :
    R.faceSucc (R.facePred d) = d := by
  simp [facePred, faceSucc, R.nextAround_prevAround d]

/-- The face-successor map as a permutation of unit-distance darts. -/
def faceSuccPerm (R : UnitDistanceRotationSystem C) :
    Equiv.Perm (UnitDistanceDart C) where
  toFun := R.faceSucc
  invFun := R.facePred
  left_inv := R.facePred_faceSucc
  right_inv := R.faceSucc_facePred

/-- A finite permutation orbit has a least positive return time at each
point.  This is the finite-period row used by the S2 face-successor orbit
construction. -/
theorem perm_exists_pos_min_period {α : Type u} [Finite α]
    (f : Equiv.Perm α) (x : α) :
    Exists fun p : Nat =>
      0 < p ∧ (f ^ p) x = x ∧
        forall q : Nat, 0 < q -> (f ^ q) x = x -> p <= q := by
  classical
  letI : DecidableRel f.SameCycle := Classical.decRel _
  refine Exists.intro (orderOf (f.cycleOf x)) ?_
  constructor
  · exact orderOf_pos (f.cycleOf x)
  constructor
  · rw [← Equiv.Perm.cycleOf_pow_apply_self f x,
      pow_orderOf_eq_one]
    rfl
  · intro q hq hqx
    by_cases hx : f x = x
    · rw [(Equiv.Perm.cycleOf_eq_one_iff f).mpr hx]
      simpa using hq
    · have hc : (f.cycleOf x ^ q) x = x := by
        rwa [Equiv.Perm.cycleOf_pow_apply_self f x]
      have hpow : f.cycleOf x ^ q = 1 := by
        exact
          ((Equiv.Perm.isCycle_cycleOf f hx).pow_eq_one_iff'
            (by rwa [Equiv.Perm.cycleOf_apply_self])).mpr hc
      exact orderOf_le_of_pow_eq_one hq hpow

/-- The face-successor permutation has a least positive return time from any
starting unit-distance dart. -/
theorem faceSuccPerm_exists_pos_min_period
    (R : UnitDistanceRotationSystem C) (d : UnitDistanceDart C) :
    Exists fun p : Nat =>
      0 < p ∧ (R.faceSuccPerm ^ p) d = d ∧
        forall q : Nat, 0 < q -> (R.faceSuccPerm ^ q) d = d -> p <= q :=
  perm_exists_pos_min_period R.faceSuccPerm d

/-- The `cycleOf` component of the face-successor permutation containing the
chosen starting dart. -/
noncomputable def faceSuccPermCycle
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C) :
    Equiv.Perm (UnitDistanceDart C) := by
  classical
  letI : DecidableRel R.faceSuccPerm.SameCycle := Classical.decRel _
  exact R.faceSuccPerm.cycleOf start

/-- The least positive return time of the face-successor permutation from the
chosen starting dart, defined as the order of its `cycleOf` component. -/
noncomputable def faceSuccPermPeriod
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C) :
    Nat :=
  Classical.choose (faceSuccPerm_exists_pos_min_period R start)

@[simp]
theorem faceSuccPermPeriod_eq_choose
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C) :
    faceSuccPermPeriod R start =
      Classical.choose (faceSuccPerm_exists_pos_min_period R start) :=
  rfl

theorem faceSuccPermPeriod_pos
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C) :
    0 < faceSuccPermPeriod R start :=
  (Classical.choose_spec
    (faceSuccPerm_exists_pos_min_period R start)).1

theorem faceSuccPermPeriod_return
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C) :
    (R.faceSuccPerm ^ faceSuccPermPeriod R start) start = start :=
  (Classical.choose_spec
    (faceSuccPerm_exists_pos_min_period R start)).2.1

theorem faceSuccPermPeriod_minimal
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C) :
    forall q : Nat, 0 < q ->
      (R.faceSuccPerm ^ q) start = start ->
        faceSuccPermPeriod R start <= q :=
  (Classical.choose_spec
    (faceSuccPerm_exists_pos_min_period R start)).2.2

/-- The raw finite orbit of the face-successor permutation from a chosen
starting dart, with its least positive return time. -/
structure RawFaceSuccOrbit
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C) where
  period : Nat
  period_pos : 0 < period
  dart : Fin period -> UnitDistanceDart C
  dart_eq_iterate :
    forall k, dart k = (R.faceSuccPerm ^ k.val) start
  period_return :
    (R.faceSuccPerm ^ period) start = start
  period_minimal :
    forall q : Nat, 0 < q ->
      (R.faceSuccPerm ^ q) start = start -> period <= q

namespace RawFaceSuccOrbit

variable {C : _root_.UDConfig n} {R : UnitDistanceRotationSystem C}
variable {start : UnitDistanceDart C}

/-- Build the raw face-successor orbit using the `cycleOf` order of the
face-successor permutation at the starting dart. -/
noncomputable def ofFaceSuccPerm
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C) :
    RawFaceSuccOrbit R start where
  period := faceSuccPermPeriod R start
  period_pos := faceSuccPermPeriod_pos R start
  dart := fun k => (R.faceSuccPerm ^ k.val) start
  dart_eq_iterate := by
    intro k
    rfl
  period_return := faceSuccPermPeriod_return R start
  period_minimal := faceSuccPermPeriod_minimal R start

@[simp]
theorem ofFaceSuccPerm_period
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C) :
    (ofFaceSuccPerm R start).period =
      faceSuccPermPeriod R start :=
  rfl

@[simp]
theorem ofFaceSuccPerm_dart
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C)
    (k : Fin (ofFaceSuccPerm R start).period) :
    (ofFaceSuccPerm R start).dart k =
      (R.faceSuccPerm ^ k.val) start :=
  rfl

@[simp]
theorem dart_zero (O : RawFaceSuccOrbit R start) :
    O.dart ⟨0, O.period_pos⟩ = start := by
  rw [O.dart_eq_iterate]
  rfl

theorem period_eq_faceSuccPermPeriod
    (O : RawFaceSuccOrbit R start) :
    O.period = faceSuccPermPeriod R start := by
  apply Nat.le_antisymm
  · exact O.period_minimal
      (faceSuccPermPeriod R start)
      (faceSuccPermPeriod_pos R start)
      (faceSuccPermPeriod_return R start)
  · exact faceSuccPermPeriod_minimal R start
      O.period O.period_pos O.period_return

/-- Every concrete seed for the face-successor permutation has a raw finite
orbit.  Downstream geometric proofs instantiate `R` with the geometric
rotation system and `start` with the actual exterior seed. -/
theorem nonempty
    (R : UnitDistanceRotationSystem C) (start : UnitDistanceDart C) :
    Nonempty (RawFaceSuccOrbit R start) :=
  ⟨ofFaceSuccPerm R start⟩

/-- The raw period orbit carries the expected cyclic face-successor row. -/
@[simp]
theorem faceSucc_dart_eq_cyclicSucc
    (O : RawFaceSuccOrbit R start) (k : Fin O.period) :
    R.faceSucc (O.dart k) =
      O.dart (PlanarInterface.cyclicSucc O.period_pos k) := by
  rw [O.dart_eq_iterate k]
  rw [O.dart_eq_iterate (PlanarInterface.cyclicSucc O.period_pos k)]
  change R.faceSuccPerm ((R.faceSuccPerm ^ k.val) start) =
    (R.faceSuccPerm ^
      (PlanarInterface.cyclicSucc O.period_pos k).val) start
  by_cases hnext : k.val + 1 < O.period
  · have hsucc_val :
      (PlanarInterface.cyclicSucc O.period_pos k).val = k.val + 1 := by
      simp [PlanarInterface.cyclicSucc, Nat.mod_eq_of_lt hnext]
    rw [hsucc_val]
    rw [← Equiv.Perm.mul_apply]
    rw [Commute.self_pow]
    rw [pow_succ]
  · have hlast : k.val + 1 = O.period :=
      eq_of_le_of_not_lt (Nat.succ_le_of_lt k.isLt) hnext
    have hsucc_val :
      (PlanarInterface.cyclicSucc O.period_pos k).val = 0 := by
      simp [PlanarInterface.cyclicSucc, hlast]
    rw [hsucc_val]
    simp only [pow_zero, Equiv.Perm.coe_one, id_eq]
    have hstep :
        R.faceSuccPerm ((R.faceSuccPerm ^ k.val) start) =
          (R.faceSuccPerm ^ (k.val + 1)) start := by
      rw [← Equiv.Perm.mul_apply]
      rw [Commute.self_pow]
      rw [pow_succ]
    rw [hstep, hlast]
    exact O.period_return

/-- Consecutive darts in a raw face-successor orbit are endpoint-chained. -/
theorem dart_head_eq_cyclicSucc_tail
    (O : RawFaceSuccOrbit R start) (k : Fin O.period) :
    (O.dart k).head =
      (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
  R.endpoint_chaining_of_faceSucc_eq_next
    (O.faceSucc_dart_eq_cyclicSucc k)

end RawFaceSuccOrbit

/-- At one boundary vertex, swap the incoming boundary dart with the outgoing
boundary dart and leave all other outgoing darts fixed. -/
def boundaryTurnSwap
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (j : Fin B.length) :
    Equiv.Perm (OutgoingUnitDistanceDart C (B.vertex j)) := by
  classical
  exact
    Equiv.swap
      (α := OutgoingUnitDistanceDart C (B.vertex j))
      ⟨(UnitDistanceDart.ofBoundary B
          (PlanarInterface.cyclicPred B.length_pos j)).reverse, by
        rw [UnitDistanceDart.reverse_tail]
        rw [UnitDistanceDart.ofBoundary_head]
        rw [PlanarInterface.cyclicSucc_cyclicPred]⟩
      ⟨UnitDistanceDart.ofBoundary B j, rfl⟩

/-- The boundary-turn swap transported to an arbitrary vertex known to be the
given boundary vertex. -/
def boundaryTurnSwapAt
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (v : Fin n) (j : Fin B.length) (hj : B.vertex j = v) :
    Equiv.Perm (OutgoingUnitDistanceDart C v) :=
  let e := OutgoingUnitDistanceDart.congr (C := C) hj
  e.symm.trans ((boundaryTurnSwap (C := C) B j).trans e)

/-- Concrete per-vertex cyclic order that follows the displayed boundary cycle
whenever the vertex lies on that boundary. -/
noncomputable def boundaryFollowingCyclicOrder
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (v : Fin n) :
    VertexFiniteUnitNeighborCyclicOrder C v where
  perm :=
    if h : Exists fun j : Fin B.length => B.vertex j = v then
      boundaryTurnSwapAt (C := C) B v (Classical.choose h)
        (Classical.choose_spec h)
    else
      Equiv.refl _

/-- Rotation system whose local successor rows advance along the supplied
boundary cycle. -/
noncomputable def ofBoundaryCycle
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C) :
    UnitDistanceRotationSystem C :=
  ofFiniteUnitNeighborCyclicOrderRows
    (fun v => boundaryFollowingCyclicOrder (C := C) B v)

end UnitDistanceRotationSystem

/-- Actual face-successor rows for a concrete boundary cycle in a supplied
rotation system.  This is the combinatorial data saying that the rotation
system's face walk follows the displayed simple unit-distance cycle. -/
structure UnitDistanceCycleFaceSuccRows
    (C : _root_.UDConfig n) (R : UnitDistanceRotationSystem C)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C) where
  faceSucc_eq_next :
    forall k : Fin B.length,
      R.faceSucc (UnitDistanceDart.ofBoundary B k) =
        UnitDistanceDart.ofBoundary B
          (PlanarInterface.cyclicSucc B.length_pos k)

namespace UnitDistanceCycleFaceSuccRows

variable {C : _root_.UDConfig n}

/-- The boundary-following rotation system supplies concrete face-successor
rows for the displayed unit-distance cycle. -/
noncomputable def ofBoundaryCycle
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C) :
    UnitDistanceCycleFaceSuccRows C
      (UnitDistanceRotationSystem.ofBoundaryCycle (C := C) B) B where
  faceSucc_eq_next := by
    classical
    intro k
    let j := PlanarInterface.cyclicSucc B.length_pos k
    have hmem : Exists fun t : Fin B.length => B.vertex t = B.vertex j :=
      ⟨j, rfl⟩
    have hchoose : Classical.choose hmem = j :=
      B.simple (Classical.choose_spec hmem)
    have hpred : PlanarInterface.cyclicPred B.length_pos j = k := by
      simp [j, PlanarInterface.cyclicPred_cyclicSucc]
    apply UnitDistanceDart.endpointPair_injective
    simp [UnitDistanceDart.endpointPair,
      UnitDistanceRotationSystem.ofBoundaryCycle,
      UnitDistanceRotationSystem.faceSucc,
      UnitDistanceRotationSystem.nextAround,
      UnitDistanceRotationSystem.boundaryFollowingCyclicOrder,
      UnitDistanceRotationSystem.boundaryTurnSwapAt,
      UnitDistanceRotationSystem.boundaryTurnSwap,
      UnitDistanceDart.outgoing,
      OutgoingUnitDistanceDart.congr, j, hmem, hchoose, hpred]

end UnitDistanceCycleFaceSuccRows

/--
A finite face orbit in a supplied rotation system, tied to a checked
unit-distance cycle boundary.  The orbit records both dart succession and the
agreement between dart endpoints and consecutive boundary-cycle vertices.
-/
structure FaceDartOrbit
    (C : _root_.UDConfig n) (R : UnitDistanceRotationSystem C) where
  boundary : JordanBoundaryConcrete.UnitDistanceCycleBoundary C
  dart : Fin boundary.length -> UnitDistanceDart C
  dart_tail_eq_vertex :
    forall k, (dart k).tail = boundary.vertex k
  dart_head_eq_succ_vertex :
    forall k, (dart k).head =
      boundary.vertex (PlanarInterface.cyclicSucc boundary.length_pos k)
  faceSucc_eq_next :
    forall k, R.faceSucc (dart k) =
      dart (PlanarInterface.cyclicSucc boundary.length_pos k)

namespace FaceDartOrbit

variable {C : _root_.UDConfig n} {R : UnitDistanceRotationSystem C}

/-- The orbit boundary is nondegenerate. -/
theorem length_ge_three (O : FaceDartOrbit C R) :
    3 <= O.boundary.length :=
  O.boundary.length_ge_three

/-- The orbit boundary as the existing boundary-cycle interface. -/
def toBoundaryCycle (O : FaceDartOrbit C R) :
    OuterBoundaryInterface.BoundaryCycle (canonicalGraph C) :=
  O.boundary.toBoundaryCycle

/-- The orbit boundary carries the checked simple-polygon witness. -/
def toSimplePolygon (O : FaceDartOrbit C R) :
    OuterBoundaryInterface.SimplePolygon (canonicalGraph C) O.toBoundaryCycle :=
  O.boundary.toSimplePolygon

/-- Build the concrete face orbit from a unit-distance cycle and the actual
face-successor rows for that same cycle.  Simplicity/no-repeat comes from the
cycle boundary itself. -/
def ofBoundaryFaceSuccRows
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows : UnitDistanceCycleFaceSuccRows C R B) :
    FaceDartOrbit C R where
  boundary := B
  dart := UnitDistanceDart.ofBoundary B
  dart_tail_eq_vertex := by
    intro k
    rfl
  dart_head_eq_succ_vertex := by
    intro k
    rfl
  faceSucc_eq_next := rows.faceSucc_eq_next

@[simp]
theorem ofBoundaryFaceSuccRows_boundary
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows : UnitDistanceCycleFaceSuccRows C R B) :
    (ofBoundaryFaceSuccRows B rows).boundary = B :=
  rfl

@[simp]
theorem ofBoundaryFaceSuccRows_dart
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows : UnitDistanceCycleFaceSuccRows C R B)
    (k : Fin B.length) :
    (ofBoundaryFaceSuccRows B rows).dart k =
      UnitDistanceDart.ofBoundary B k :=
  rfl

/-- Build a concrete face-dart orbit from a raw face-successor period orbit
once a downstream boundary construction has identified the same cyclic period
and endpoint rows.  This is the direct bridge from an actual seed orbit to the
existing `FaceDartOrbit` API; it introduces no additional source package. -/
def ofRawFaceSuccOrbit
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hperiod : B.length = O.period)
    (tail_eq : forall k : Fin B.length,
      (O.dart (Fin.cast hperiod k)).tail = B.vertex k)
    (head_eq : forall k : Fin B.length,
      (O.dart (Fin.cast hperiod k)).head =
        B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) :
    FaceDartOrbit C R where
  boundary := B
  dart := fun k => O.dart (Fin.cast hperiod k)
  dart_tail_eq_vertex := tail_eq
  dart_head_eq_succ_vertex := head_eq
  faceSucc_eq_next := by
    intro k
    have hcast_succ :
        Fin.cast hperiod (PlanarInterface.cyclicSucc B.length_pos k) =
          PlanarInterface.cyclicSucc O.period_pos (Fin.cast hperiod k) := by
      ext
      simp [PlanarInterface.cyclicSucc, hperiod]
    rw [hcast_succ]
    exact O.faceSucc_dart_eq_cyclicSucc (Fin.cast hperiod k)

/-- Every dart in the orbit is an edge of the canonical straight-line graph. -/
theorem dart_canonicalAdj (O : FaceDartOrbit C R)
    (k : Fin O.boundary.length) :
    (canonicalGraph C).Adj (O.dart k).tail (O.dart k).head :=
  (O.dart k).canonicalAdj

theorem dart_tail_injective (O : FaceDartOrbit C R) :
    Function.Injective fun k : Fin O.boundary.length => (O.dart k).tail := by
  intro i j h
  apply O.boundary.simple
  calc
    O.boundary.vertex i = (O.dart i).tail := (O.dart_tail_eq_vertex i).symm
    _ = (O.dart j).tail := h
    _ = O.boundary.vertex j := O.dart_tail_eq_vertex j

theorem dart_injective (O : FaceDartOrbit C R) :
    Function.Injective O.dart := by
  intro i j h
  exact O.dart_tail_injective (congrArg UnitDistanceDart.tail h)

/-- The constructed orbit has no repeated darts. -/
theorem ofBoundaryFaceSuccRows_dart_injective
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows : UnitDistanceCycleFaceSuccRows C R B) :
    Function.Injective (ofBoundaryFaceSuccRows B rows).dart :=
  (ofBoundaryFaceSuccRows B rows).dart_injective

/-- The endpoint rows in a face orbit identify each stored dart with the
canonical dart of its recorded boundary edge. -/
theorem dart_eq_ofBoundary
    (O : FaceDartOrbit C R) (k : Fin O.boundary.length) :
    O.dart k = UnitDistanceDart.ofBoundary O.boundary k :=
  UnitDistanceDart.eq_ofBoundary_of_tail_head O.boundary k (O.dart k)
    (O.dart_tail_eq_vertex k) (O.dart_head_eq_succ_vertex k)

/-- A face orbit can be forgotten to the concrete boundary face-successor rows
expected by the older boundary-row interface. -/
def toUnitDistanceCycleFaceSuccRows
    (O : FaceDartOrbit C R) :
    UnitDistanceCycleFaceSuccRows C R O.boundary where
  faceSucc_eq_next := by
    intro k
    rw [← O.dart_eq_ofBoundary k]
    rw [← O.dart_eq_ofBoundary
      (PlanarInterface.cyclicSucc O.boundary.length_pos k)]
    exact O.faceSucc_eq_next k

/-- The face successor lands at the next boundary-cycle vertex. -/
theorem faceSucc_tail_eq_next_vertex
    (O : FaceDartOrbit C R) (k : Fin O.boundary.length) :
    (R.faceSucc (O.dart k)).tail =
      O.boundary.vertex
        (PlanarInterface.cyclicSucc O.boundary.length_pos k) := by
  rw [O.faceSucc_eq_next k]
  exact O.dart_tail_eq_vertex _

/-- The dart head is the same next boundary-cycle vertex as the face successor tail. -/
theorem dart_head_eq_faceSucc_tail
    (O : FaceDartOrbit C R) (k : Fin O.boundary.length) :
    (O.dart k).head = (R.faceSucc (O.dart k)).tail := by
  rw [O.faceSucc_tail_eq_next_vertex k]
  exact O.dart_head_eq_succ_vertex k

/-- Consecutive darts in a face orbit are endpoint-chained. -/
theorem dart_head_eq_next_tail
    (O : FaceDartOrbit C R) (k : Fin O.boundary.length) :
    (O.dart k).head =
      (O.dart
        (PlanarInterface.cyclicSucc O.boundary.length_pos k)).tail :=
  R.endpoint_chaining_of_faceSucc_eq_next (O.faceSucc_eq_next k)

end FaceDartOrbit

/--
Exterior-face enclosure predicates for a concrete dart orbit.  These are the
topological fields that remain to be proved from the exterior component; this
record only packages them against the orbit that they describe.
-/
structure ExteriorDartOrbitEnclosure
    (C : _root_.UDConfig n) (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R) where
  exteriorDart : UnitDistanceDart C
  exteriorDart_on_orbit :
    Exists fun k : Fin O.boundary.length => O.dart k = exteriorDart
  insideOrOn : PlanarInterface.Point -> Prop
  onBoundary : Fin n -> Prop
  boundary_vertex_onBoundary :
    forall k : Fin O.boundary.length, onBoundary (O.boundary.vertex k)
  boundary_point_insideOrOn :
    forall k : Fin O.boundary.length,
      insideOrOn ((canonicalGraph C).point (O.boundary.vertex k))
  all_vertices_insideOrOn :
    forall v : Fin n, insideOrOn ((canonicalGraph C).point v)
  onBoundary_iff_orbit_vertex :
    forall v : Fin n, onBoundary v <->
      Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v

namespace ExteriorDartOrbitEnclosure

variable {C : _root_.UDConfig n} {R : UnitDistanceRotationSystem C}
variable {O : FaceDartOrbit C R}

/-- Forget exterior-dart orbit enclosure rows to the existing Jordan enclosure. -/
def toJordanOuterComponentEnclosure
    (E : ExteriorDartOrbitEnclosure C R O) :
    JordanBoundaryConcrete.JordanOuterComponentEnclosure C O.boundary where
  insideOrOn := E.insideOrOn
  onBoundary := E.onBoundary
  boundary_vertex_onBoundary := E.boundary_vertex_onBoundary
  boundary_point_insideOrOn := E.boundary_point_insideOrOn
  all_vertices_insideOrOn := E.all_vertices_insideOrOn
  onBoundary_iff_outer_cycle := E.onBoundary_iff_orbit_vertex

theorem exteriorDart_mem_boundary
    (E : ExteriorDartOrbitEnclosure C R O) :
    Exists fun k : Fin O.boundary.length => O.dart k = E.exteriorDart :=
  E.exteriorDart_on_orbit

theorem onBoundary_of_orbit_vertex
    (E : ExteriorDartOrbitEnclosure C R O) {v : Fin n}
    (hv : Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v) :
    E.onBoundary v :=
  (E.onBoundary_iff_orbit_vertex v).2 hv

theorem exists_orbit_vertex_of_onBoundary
    (E : ExteriorDartOrbitEnclosure C R O) {v : Fin n}
    (hv : E.onBoundary v) :
    Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v :=
  (E.onBoundary_iff_orbit_vertex v).1 hv

theorem exteriorDart_tail_onBoundary
    (E : ExteriorDartOrbitEnclosure C R O) :
    E.onBoundary E.exteriorDart.tail := by
  rcases E.exteriorDart_on_orbit with ⟨k, hk⟩
  rw [← hk]
  rw [O.dart_tail_eq_vertex k]
  exact E.boundary_vertex_onBoundary k

theorem exteriorDart_head_onBoundary
    (E : ExteriorDartOrbitEnclosure C R O) :
    E.onBoundary E.exteriorDart.head := by
  rcases E.exteriorDart_on_orbit with ⟨k, hk⟩
  rw [← hk]
  rw [O.dart_head_eq_succ_vertex k]
  exact
    E.boundary_vertex_onBoundary
      (PlanarInterface.cyclicSucc O.boundary.length_pos k)

theorem exteriorDart_tail_point_insideOrOn
    (E : ExteriorDartOrbitEnclosure C R O) :
    E.insideOrOn ((canonicalGraph C).point E.exteriorDart.tail) :=
  E.all_vertices_insideOrOn E.exteriorDart.tail

theorem exteriorDart_head_point_insideOrOn
    (E : ExteriorDartOrbitEnclosure C R O) :
    E.insideOrOn ((canonicalGraph C).point E.exteriorDart.head) :=
  E.all_vertices_insideOrOn E.exteriorDart.head

/-- Promote a Jordan enclosure for the same face orbit to exterior-dart rows. -/
def ofJordanOuterComponentEnclosure
    (O : FaceDartOrbit C R)
    (k0 : Fin O.boundary.length)
    (E : JordanBoundaryConcrete.JordanOuterComponentEnclosure C O.boundary) :
    ExteriorDartOrbitEnclosure C R O where
  exteriorDart := O.dart k0
  exteriorDart_on_orbit := ⟨k0, rfl⟩
  insideOrOn := E.insideOrOn
  onBoundary := E.onBoundary
  boundary_vertex_onBoundary := E.boundary_vertex_onBoundary
  boundary_point_insideOrOn := E.boundary_point_insideOrOn
  all_vertices_insideOrOn := E.all_vertices_insideOrOn
  onBoundary_iff_orbit_vertex := E.onBoundary_iff_outer_cycle

@[simp]
theorem toJordanOuterComponentEnclosure_ofJordanOuterComponentEnclosure
    (O : FaceDartOrbit C R)
    (k0 : Fin O.boundary.length)
    (E : JordanBoundaryConcrete.JordanOuterComponentEnclosure C O.boundary) :
    (ofJordanOuterComponentEnclosure O k0 E).toJordanOuterComponentEnclosure =
      E :=
  rfl

end ExteriorDartOrbitEnclosure

/--
The complete local dart/rotation source for the finite planar theorem: a
rotation system, one exterior face orbit in that system, and enclosure
predicates proved for that same orbit.
-/
structure ExteriorDartOrbitSource (C : _root_.UDConfig n) where
  rotation : UnitDistanceRotationSystem C
  orbit : FaceDartOrbit C rotation
  enclosure : ExteriorDartOrbitEnclosure C rotation orbit

namespace ExteriorDartOrbitSource

variable {C : _root_.UDConfig n}

/-- Project the exterior dart orbit source to the positive chosen-cycle row. -/
def toChosenJordanOuterComponentRow
    (S : ExteriorDartOrbitSource C) :
    JordanBoundaryConcrete.ChosenJordanOuterComponentRow C where
  boundary := S.orbit.boundary
  enclosure := S.enclosure.toJordanOuterComponentEnclosure

/-- Build the exterior-dart source from a proved face orbit and matching
Jordan enclosure for that same orbit boundary. -/
def ofFaceDartOrbitAndJordanEnclosure
    (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R)
    (k0 : Fin O.boundary.length)
    (E : JordanBoundaryConcrete.JordanOuterComponentEnclosure C O.boundary) :
    ExteriorDartOrbitSource C where
  rotation := R
  orbit := O
  enclosure :=
    ExteriorDartOrbitEnclosure.ofJordanOuterComponentEnclosure O k0 E

theorem nonempty_of_faceDartOrbit_jordanEnclosure
    (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R)
    (k0 : Fin O.boundary.length)
    (E : JordanBoundaryConcrete.JordanOuterComponentEnclosure C O.boundary) :
    Nonempty (ExteriorDartOrbitSource C) :=
  ⟨ofFaceDartOrbitAndJordanEnclosure R O k0 E⟩

/-- A supplied exterior dart orbit source gives the chosen outer component row. -/
theorem gives_chosenJordanOuterComponentRow
    (S : ExteriorDartOrbitSource C) :
    Nonempty (JordanBoundaryConcrete.ChosenJordanOuterComponentRow C) :=
  Nonempty.intro S.toChosenJordanOuterComponentRow

end ExteriorDartOrbitSource

/--
The reduced S2 source package: a rotation system, one face orbit for that
system, and Jordan outer-component enclosure predicates for exactly that orbit
boundary.
-/
structure FaceOrbitJordanEnclosureSource (C : _root_.UDConfig n) where
  rotation : UnitDistanceRotationSystem C
  orbit : FaceDartOrbit C rotation
  enclosure :
    JordanBoundaryConcrete.JordanOuterComponentEnclosure C orbit.boundary

namespace FaceOrbitJordanEnclosureSource

variable {C : _root_.UDConfig n}

/-- Promote the reduced source package to the exterior-dart-orbit source. -/
def toExteriorDartOrbitSource
    (S : FaceOrbitJordanEnclosureSource C) :
    ExteriorDartOrbitSource C :=
  let k0 : Fin S.orbit.boundary.length :=
    ⟨0, S.orbit.boundary.length_pos⟩
  ExteriorDartOrbitSource.ofFaceDartOrbitAndJordanEnclosure
    S.rotation S.orbit k0 S.enclosure

/-- Project the reduced source package directly to the chosen outer component. -/
def toChosenJordanOuterComponentRow
    (S : FaceOrbitJordanEnclosureSource C) :
    JordanBoundaryConcrete.ChosenJordanOuterComponentRow C :=
  S.toExteriorDartOrbitSource.toChosenJordanOuterComponentRow

/-- Forget an exterior-dart source to the reduced face-orbit/Jordan-enclosure
source package. -/
def ofExteriorDartOrbitSource
    (S : ExteriorDartOrbitSource C) :
    FaceOrbitJordanEnclosureSource C where
  rotation := S.rotation
  orbit := S.orbit
  enclosure := S.enclosure.toJordanOuterComponentEnclosure

/-- The reduced source package is nonempty exactly when the exterior-dart
source package is nonempty. -/
theorem nonempty_iff_exteriorDartOrbitSource
    (C : _root_.UDConfig n) :
    Nonempty (FaceOrbitJordanEnclosureSource C) <->
      Nonempty (ExteriorDartOrbitSource C) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.toExteriorDartOrbitSource⟩
  · rintro ⟨S⟩
    exact ⟨ofExteriorDartOrbitSource S⟩

/-- A reduced source package gives the chosen outer-component row. -/
theorem gives_chosenJordanOuterComponentRow
    (S : FaceOrbitJordanEnclosureSource C) :
    Nonempty (JordanBoundaryConcrete.ChosenJordanOuterComponentRow C) :=
  Nonempty.intro S.toChosenJordanOuterComponentRow

/-- Build the reduced face-orbit/Jordan-enclosure source from finite-neighbor
rotation data and a face orbit for the assembled rotation system. -/
def ofFiniteUnitNeighborRotationSource
    (S : FiniteUnitNeighborRotationSource C)
    (O : FaceDartOrbit C S.toUnitDistanceRotationSystem)
    (E : JordanBoundaryConcrete.JordanOuterComponentEnclosure C O.boundary) :
    FaceOrbitJordanEnclosureSource C where
  rotation := S.toUnitDistanceRotationSystem
  orbit := O
  enclosure := E

/-- Finite-neighbor rotation data plus a matching face orbit and Jordan
enclosure inhabits the reduced S2 source package. -/
theorem nonempty_of_finiteUnitNeighborRotationSource_faceDartOrbit_jordanEnclosure
    (S : FiniteUnitNeighborRotationSource C)
    (O : FaceDartOrbit C S.toUnitDistanceRotationSystem)
    (E : JordanBoundaryConcrete.JordanOuterComponentEnclosure C O.boundary) :
    Nonempty (FaceOrbitJordanEnclosureSource C) :=
  ⟨ofFiniteUnitNeighborRotationSource S O E⟩

/-- Build the reduced source directly from a concrete boundary cycle, its
face-successor rows, and the matching Jordan enclosure. -/
def ofBoundaryFaceSuccRows
    (R : UnitDistanceRotationSystem C)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows : UnitDistanceCycleFaceSuccRows C R B)
    (E : JordanBoundaryConcrete.JordanOuterComponentEnclosure C B) :
    FaceOrbitJordanEnclosureSource C where
  rotation := R
  orbit := FaceDartOrbit.ofBoundaryFaceSuccRows B rows
  enclosure := E

/-- Concrete boundary successor rows plus the matching enclosure inhabit the
reduced source package. -/
theorem nonempty_of_boundaryFaceSuccRows_jordanEnclosure
    (R : UnitDistanceRotationSystem C)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows : UnitDistanceCycleFaceSuccRows C R B)
    (E : JordanBoundaryConcrete.JordanOuterComponentEnclosure C B) :
    Nonempty (FaceOrbitJordanEnclosureSource C) :=
  ⟨ofBoundaryFaceSuccRows R B rows E⟩

end FaceOrbitJordanEnclosureSource

namespace ExteriorDartOrbitSource

variable {C : _root_.UDConfig n}

/-- Build the exterior-dart source from concrete boundary face-successor rows
and the matching Jordan enclosure. -/
def ofBoundaryFaceSuccRows
    (R : UnitDistanceRotationSystem C)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows : UnitDistanceCycleFaceSuccRows C R B)
    (E : JordanBoundaryConcrete.JordanOuterComponentEnclosure C B) :
    ExteriorDartOrbitSource C :=
  (FaceOrbitJordanEnclosureSource.ofBoundaryFaceSuccRows
    R B rows E).toExteriorDartOrbitSource

/-- Concrete boundary successor rows plus the matching enclosure inhabit the
exterior-dart source package. -/
theorem nonempty_of_boundaryFaceSuccRows_jordanEnclosure
    (R : UnitDistanceRotationSystem C)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows : UnitDistanceCycleFaceSuccRows C R B)
    (E : JordanBoundaryConcrete.JordanOuterComponentEnclosure C B) :
    Nonempty (ExteriorDartOrbitSource C) :=
  ⟨ofBoundaryFaceSuccRows R B rows E⟩

end ExteriorDartOrbitSource

namespace FinitePlanarOuterComponentInputs

variable {C : _root_.UDConfig n}

/-- The concrete simple cycle supplied by the graph-side inputs, selected once
for downstream orbit construction. -/
def selectedBoundary (I : FinitePlanarOuterComponentInputs C) :
    JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
  Classical.choice I.hasUnitDistanceCycle

/-- The selected input cycle is nondegenerate. -/
theorem selectedBoundary_length_ge_three
    (I : FinitePlanarOuterComponentInputs C) :
    3 <= I.selectedBoundary.length :=
  I.selectedBoundary.length_ge_three

/-- Build the selected simple face orbit once the actual face-successor rows are
proved for the selected input cycle. -/
def selectedFaceDartOrbit
    (I : FinitePlanarOuterComponentInputs C)
    (R : UnitDistanceRotationSystem C)
    (rows : UnitDistanceCycleFaceSuccRows C R I.selectedBoundary) :
    FaceDartOrbit C R :=
  FaceDartOrbit.ofBoundaryFaceSuccRows I.selectedBoundary rows

/-- The rotation system obtained by making the selected boundary cycle turn to
its next displayed boundary edge at every selected boundary vertex.

This is not the identity cyclic order: at each selected boundary vertex it uses
the boundary-turn swap rows, so the face-successor computation follows the
chosen cycle. -/
noncomputable def selectedBoundaryRotation
    (I : FinitePlanarOuterComponentInputs C) :
    UnitDistanceRotationSystem C :=
  UnitDistanceRotationSystem.ofBoundaryCycle I.selectedBoundary

/-- Concrete face-successor rows for the selected input boundary in the
boundary-following rotation system. -/
noncomputable def selectedBoundaryFaceSuccRows
    (I : FinitePlanarOuterComponentInputs C) :
    UnitDistanceCycleFaceSuccRows
      C I.selectedBoundaryRotation I.selectedBoundary :=
  UnitDistanceCycleFaceSuccRows.ofBoundaryCycle I.selectedBoundary

/-- The selected input boundary as a concrete face-dart orbit in the
boundary-following rotation system. -/
noncomputable def selectedBoundaryFaceDartOrbit
    (I : FinitePlanarOuterComponentInputs C) :
    FaceDartOrbit C I.selectedBoundaryRotation :=
  I.selectedFaceDartOrbit
    I.selectedBoundaryRotation I.selectedBoundaryFaceSuccRows

@[simp]
theorem selectedBoundaryFaceDartOrbit_boundary
    (I : FinitePlanarOuterComponentInputs C) :
    I.selectedBoundaryFaceDartOrbit.boundary = I.selectedBoundary :=
  rfl

@[simp]
theorem selectedBoundaryFaceDartOrbit_dart
    (I : FinitePlanarOuterComponentInputs C)
    (k : Fin I.selectedBoundary.length) :
    I.selectedBoundaryFaceDartOrbit.dart k =
      UnitDistanceDart.ofBoundary I.selectedBoundary k :=
  rfl

/-- The exposed selected-boundary face orbit supplies the older concrete
face-successor row interface without adding any further geometric assumption. -/
theorem selectedBoundaryFaceDartOrbit_toFaceSuccRows
    (I : FinitePlanarOuterComponentInputs C) :
    I.selectedBoundaryFaceDartOrbit.toUnitDistanceCycleFaceSuccRows =
      I.selectedBoundaryFaceSuccRows := by
  rfl

/-- The selected orbit has no repeated darts, by the checked cycle simplicity. -/
theorem selectedFaceDartOrbit_dart_injective
    (I : FinitePlanarOuterComponentInputs C)
    (R : UnitDistanceRotationSystem C)
    (rows : UnitDistanceCycleFaceSuccRows C R I.selectedBoundary) :
    Function.Injective (I.selectedFaceDartOrbit R rows).dart :=
  (I.selectedFaceDartOrbit R rows).dart_injective

/-- The graph-side inputs give an exterior-dart source exactly when the selected
cycle has real face-successor rows and a matching Jordan enclosure. -/
def selectedExteriorDartOrbitSource
    (I : FinitePlanarOuterComponentInputs C)
    (R : UnitDistanceRotationSystem C)
    (rows : UnitDistanceCycleFaceSuccRows C R I.selectedBoundary)
    (E :
      JordanBoundaryConcrete.JordanOuterComponentEnclosure
        C I.selectedBoundary) :
    ExteriorDartOrbitSource C :=
  ExteriorDartOrbitSource.ofBoundaryFaceSuccRows
    R I.selectedBoundary rows E

/-- The graph-side inputs give the reduced face-orbit/Jordan-enclosure source
once the selected cycle has real face-successor rows and a matching Jordan
enclosure. -/
def selectedFaceOrbitJordanEnclosureSource
    (I : FinitePlanarOuterComponentInputs C)
    (R : UnitDistanceRotationSystem C)
    (rows : UnitDistanceCycleFaceSuccRows C R I.selectedBoundary)
    (E :
      JordanBoundaryConcrete.JordanOuterComponentEnclosure
        C I.selectedBoundary) :
    FaceOrbitJordanEnclosureSource C :=
  FaceOrbitJordanEnclosureSource.ofBoundaryFaceSuccRows
    R I.selectedBoundary rows E

/-- Nonempty reduced source form for the selected input cycle. -/
theorem nonempty_selectedFaceOrbitJordanEnclosureSource
    (I : FinitePlanarOuterComponentInputs C)
    (R : UnitDistanceRotationSystem C)
    (rows : UnitDistanceCycleFaceSuccRows C R I.selectedBoundary)
    (E :
      JordanBoundaryConcrete.JordanOuterComponentEnclosure
        C I.selectedBoundary) :
    Nonempty (FaceOrbitJordanEnclosureSource C) :=
  Nonempty.intro
    (I.selectedFaceOrbitJordanEnclosureSource R rows E)

end FinitePlanarOuterComponentInputs

/--
Sharper theorem surface for the dart/rotation route: instantiate the checked
graph-side inputs with a genuine exterior dart orbit source.
-/
abbrev FinitePlanarStraightLineExteriorDartOrbitTheorem : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    FinitePlanarOuterComponentInputs C ->
      Nonempty (ExteriorDartOrbitSource C)

/--
Precise missing theorem surface: from the checked connected/no-cut/noncrossing
unit-distance graph data and the existence of a simple unit-distance cycle,
choose the genuine outer-component cycle and prove its matching Jordan
enclosure predicates.
-/
abbrev FinitePlanarStraightLineOuterComponentTheorem : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    FinitePlanarOuterComponentInputs C ->
      Nonempty (JordanBoundaryConcrete.ChosenJordanOuterComponentRow C)

/-- The exterior-dart-orbit theorem is enough for the existing S2 outer-component theorem. -/
def finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (h : FinitePlanarStraightLineExteriorDartOrbitTheorem) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  fun C inputs =>
    let source := h C inputs
    Nonempty.elim source
      (fun S => S.gives_chosenJordanOuterComponentRow)

/-- The exterior-dart theorem is equivalent to producing the reduced
face-orbit/Jordan-enclosure source for every checked graph input. -/
theorem finitePlanarStraightLineExteriorDartOrbitTheorem_iff_faceOrbitJordanEnclosureSource :
    FinitePlanarStraightLineExteriorDartOrbitTheorem <->
      (forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Nonempty (FaceOrbitJordanEnclosureSource C)) := by
  constructor
  · intro h n C inputs
    rcases h C inputs with ⟨S⟩
    exact ⟨FaceOrbitJordanEnclosureSource.ofExteriorDartOrbitSource S⟩
  · intro h n C inputs
    rcases h C inputs with ⟨S⟩
    exact ⟨S.toExteriorDartOrbitSource⟩

/-- A family of reduced source packages proves the exterior-dart-orbit theorem. -/
def finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosureSource
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Nonempty (FaceOrbitJordanEnclosureSource C)) :
    FinitePlanarStraightLineExteriorDartOrbitTheorem :=
  finitePlanarStraightLineExteriorDartOrbitTheorem_iff_faceOrbitJordanEnclosureSource.2
    h

/-- A family of reduced source packages proves the chosen outer-component
theorem surface. -/
def finitePlanarStraightLineOuterComponentTheorem_of_faceOrbitJordanEnclosureSource
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Nonempty (FaceOrbitJordanEnclosureSource C)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosureSource
      h)

/-- It is enough to construct finite-neighbor cyclic order data, then a face
orbit and Jordan enclosure for the rotation system assembled from it. -/
def finitePlanarStraightLineExteriorDartOrbitTheorem_of_finiteUnitNeighborRotationSource_faceOrbitJordanEnclosure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun S : FiniteUnitNeighborRotationSource C =>
            Exists fun O : FaceDartOrbit C S.toUnitDistanceRotationSystem =>
              Nonempty
                (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                  C O.boundary)) :
    FinitePlanarStraightLineExteriorDartOrbitTheorem :=
  finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosureSource
    (fun C inputs => by
      rcases h C inputs with ⟨S, O, ⟨E⟩⟩
      exact
        FaceOrbitJordanEnclosureSource.nonempty_of_finiteUnitNeighborRotationSource_faceDartOrbit_jordanEnclosure
          S O E)

/-- The same finite-neighbor cyclic-order rows also prove the chosen
outer-component theorem surface once the matching face orbit and Jordan
enclosure are supplied. -/
def finitePlanarStraightLineOuterComponentTheorem_of_finiteUnitNeighborRotationSource_faceOrbitJordanEnclosure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun S : FiniteUnitNeighborRotationSource C =>
            Exists fun O : FaceDartOrbit C S.toUnitDistanceRotationSystem =>
              Nonempty
                (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                  C O.boundary)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (finitePlanarStraightLineExteriorDartOrbitTheorem_of_finiteUnitNeighborRotationSource_faceOrbitJordanEnclosure
      h)

/-- It is enough to construct finite unit-neighbor cyclic angular order rows;
their extracted per-vertex angular successors feed the angular-successor
outer-component reduction directly. -/
def finitePlanarStraightLineOuterComponentTheorem_of_finiteUnitNeighborCyclicOrderRows
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun cyclicOrderAt :
            ((v : Fin n) -> VertexFiniteUnitNeighborCyclicOrder C v) =>
            Exists fun O :
              FaceDartOrbit C
                (FiniteUnitNeighborRotationSource.ofAngularSuccessor
                  (VertexFiniteUnitNeighborCyclicOrder.angularSuccessorRows
                    cyclicOrderAt)).toUnitDistanceRotationSystem =>
              Nonempty
                (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                  C O.boundary)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_finiteUnitNeighborRotationSource_faceOrbitJordanEnclosure
    (fun C inputs => by
      rcases h C inputs with ⟨cyclicOrderAt, O, hE⟩
      exact
        ⟨FiniteUnitNeighborRotationSource.ofAngularSuccessor
            (VertexFiniteUnitNeighborCyclicOrder.angularSuccessorRows
              cyclicOrderAt),
          O, hE⟩)

/-- It is enough to construct the actual angular successor rows, then a face
orbit and Jordan enclosure for the rotation system assembled from those rows. -/
def finitePlanarStraightLineOuterComponentTheorem_of_angularSuccessorRows
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun rotationAt :
            ((v : Fin n) -> VertexCyclicAngularSuccessor C v) =>
            Exists fun O :
              FaceDartOrbit C
                (FiniteUnitNeighborRotationSource.ofAngularSuccessor
                  rotationAt).toUnitDistanceRotationSystem =>
              Nonempty
                (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                  C O.boundary)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_finiteUnitNeighborCyclicOrderRows
    (fun C inputs => by
      rcases h C inputs with ⟨rotationAt, O, hE⟩
      let cyclicOrderAt :=
        (FiniteUnitNeighborRotationSource.ofAngularSuccessor
          rotationAt).cyclicOrderAt
      have hrows :
          VertexFiniteUnitNeighborCyclicOrder.angularSuccessorRows
              cyclicOrderAt =
            rotationAt := by
        change
          (FiniteUnitNeighborRotationSource.ofAngularSuccessor
            rotationAt).angularSuccessorRows = rotationAt
        exact
          FiniteUnitNeighborRotationSource.angularSuccessorRows_ofAngularSuccessor
            rotationAt
      have hrotation :
          (FiniteUnitNeighborRotationSource.ofAngularSuccessor
              (VertexFiniteUnitNeighborCyclicOrder.angularSuccessorRows
                cyclicOrderAt)).toUnitDistanceRotationSystem =
            (FiniteUnitNeighborRotationSource.ofAngularSuccessor
              rotationAt).toUnitDistanceRotationSystem := by
        rw [hrows]
      cases hrotation
      exact ⟨cyclicOrderAt, O, hE⟩)

/-- It is enough to prove a genuine rotation-system face orbit and matching
Jordan enclosure for that same orbit boundary. -/
def finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun O : FaceDartOrbit C R =>
              Nonempty
                (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                  C O.boundary)) :
    FinitePlanarStraightLineExteriorDartOrbitTheorem :=
  fun C inputs => by
    rcases h C inputs with ⟨R, O, ⟨E⟩⟩
    let k0 : Fin O.boundary.length := ⟨0, O.boundary.length_pos⟩
    exact
      ExteriorDartOrbitSource.nonempty_of_faceDartOrbit_jordanEnclosure
        R O k0 E

/-- The same concrete face-orbit/Jordan-enclosure rows also prove the
outer-component theorem surface. -/
def finitePlanarStraightLineOuterComponentTheorem_of_faceOrbitJordanEnclosure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun O : FaceDartOrbit C R =>
              Nonempty
                (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                  C O.boundary)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosure h)

/-- It is enough to supply a concrete simple unit-distance cycle, the actual
face-successor rows showing that the rotation system follows that cycle, and a
matching Jordan outer-component enclosure for that same cycle. -/
def finitePlanarStraightLineExteriorDartOrbitTheorem_of_boundaryFaceSuccRows_jordanEnclosure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
              Exists fun _rows : UnitDistanceCycleFaceSuccRows C R B =>
                Nonempty
                  (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                    C B)) :
    FinitePlanarStraightLineExteriorDartOrbitTheorem :=
  finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosure
    (fun C inputs => by
      rcases h C inputs with ⟨R, B, rows, ⟨E⟩⟩
      exact
        ⟨R, FaceDartOrbit.ofBoundaryFaceSuccRows B rows,
          ⟨E⟩⟩)

/-- Concrete cycle face-successor rows plus the matching Jordan enclosure prove
the finite planar straight-line outer-component theorem surface. -/
def finitePlanarStraightLineOuterComponentTheorem_of_boundaryFaceSuccRows_jordanEnclosure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
              Exists fun _rows : UnitDistanceCycleFaceSuccRows C R B =>
                Nonempty
                  (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                    C B)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (finitePlanarStraightLineExteriorDartOrbitTheorem_of_boundaryFaceSuccRows_jordanEnclosure
      h)

/-- It is enough to prove face-successor rows and a matching Jordan enclosure
for the unit-distance cycle already selected from the graph-side inputs.  This
is the selected-boundary variant of
`finitePlanarStraightLineExteriorDartOrbitTheorem_of_boundaryFaceSuccRows_jordanEnclosure`
with the separate cycle-choice field eliminated. -/
def finitePlanarStraightLineExteriorDartOrbitTheorem_of_selectedBoundaryFaceSuccRows_jordanEnclosure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun _rows :
              UnitDistanceCycleFaceSuccRows C R inputs.selectedBoundary =>
                Nonempty
                  (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                    C inputs.selectedBoundary)) :
    FinitePlanarStraightLineExteriorDartOrbitTheorem :=
  finitePlanarStraightLineExteriorDartOrbitTheorem_of_boundaryFaceSuccRows_jordanEnclosure
    (fun C inputs => by
      rcases h C inputs with ⟨R, rows, hE⟩
      exact ⟨R, inputs.selectedBoundary, rows, hE⟩)

/-- Selected-boundary face-successor rows plus the matching Jordan enclosure
prove the finite planar straight-line outer-component theorem surface. -/
def finitePlanarStraightLineOuterComponentTheorem_of_selectedBoundaryFaceSuccRows_jordanEnclosure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun _rows :
              UnitDistanceCycleFaceSuccRows C R inputs.selectedBoundary =>
                Nonempty
                  (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                    C inputs.selectedBoundary)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (finitePlanarStraightLineExteriorDartOrbitTheorem_of_selectedBoundaryFaceSuccRows_jordanEnclosure
      h)

/-- It is enough to construct finite-neighbor rotation data, a concrete cycle
whose face-successor rows are computed in the assembled rotation system, and
the matching Jordan enclosure. -/
def finitePlanarStraightLineExteriorDartOrbitTheorem_of_finiteUnitNeighborRotationSource_boundaryFaceSuccRows_jordanEnclosure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun S : FiniteUnitNeighborRotationSource C =>
            Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
              Exists fun _rows :
                UnitDistanceCycleFaceSuccRows
                  C S.toUnitDistanceRotationSystem B =>
                Nonempty
                  (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                    C B)) :
    FinitePlanarStraightLineExteriorDartOrbitTheorem :=
  finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosureSource
    (fun C inputs => by
      rcases h C inputs with ⟨S, B, rows, ⟨E⟩⟩
      exact
        FaceOrbitJordanEnclosureSource.nonempty_of_boundaryFaceSuccRows_jordanEnclosure
          S.toUnitDistanceRotationSystem B rows E)

/-- Finite-neighbor rotation rows together with concrete face-successor rows
for a simple exterior unit-distance cycle and the matching Jordan enclosure
prove the finite planar straight-line outer-component theorem surface. -/
def finitePlanarStraightLineOuterComponentTheorem_of_finiteUnitNeighborRotationSource_boundaryFaceSuccRows_jordanEnclosure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun S : FiniteUnitNeighborRotationSource C =>
            Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
              Exists fun _rows :
                UnitDistanceCycleFaceSuccRows
                  C S.toUnitDistanceRotationSystem B =>
                Nonempty
                  (JordanBoundaryConcrete.JordanOuterComponentEnclosure
                    C B)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (finitePlanarStraightLineExteriorDartOrbitTheorem_of_finiteUnitNeighborRotationSource_boundaryFaceSuccRows_jordanEnclosure
      h)

/-- Minimal failure plus an already proved no-cut theorem supplies all checked
graph-side inputs for the missing finite planar outer-component theorem. -/
theorem finitePlanarOuterComponentInputs_of_minimalFailure_noCutVertex
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hno : CutVertexInterface.NoCutVertex C) :
    FinitePlanarOuterComponentInputs C where
  connected :=
    MinimalConnectednessClosure.unitDistanceSimpleGraph_connected_of_minimalClearedFailure
      (C := C) hmin
  noCutVertex := hno
  pairwiseNoncrossing := (canonicalGraph C).pairwiseNoncrossing
  hasUnitDistanceCycle :=
    JordanBoundaryConcrete.nonempty_unitDistanceCycleBoundary_of_minimalClearedFailure
      (C := C) hmin

/-- The existing `MinimalFailureGraphRoute` supplies the checked graph-side
inputs once the remaining cycle existence from minimality is added. -/
theorem finitePlanarOuterComponentInputs_of_graphRoute
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (route : MinimalFailureGraphRoute C) :
    FinitePlanarOuterComponentInputs C where
  connected := route.connectedNoCutDegreeRange.connected
  noCutVertex := route.connectedNoCutDegreeRange.noCutVertex
  pairwiseNoncrossing := route.pairwiseNoncrossing
  hasUnitDistanceCycle :=
    JordanBoundaryConcrete.nonempty_unitDistanceCycleBoundary_of_minimalClearedFailure
      (C := C) hmin

/-- Minimality plus the current no-cut slack payload supplies the checked
graph-side inputs for the missing finite planar outer-component theorem. -/
theorem finitePlanarOuterComponentInputs_of_minimalFailure_remainingSlack
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexFinal.RemainingNoCutSlackFact C) :
    FinitePlanarOuterComponentInputs C :=
  finitePlanarOuterComponentInputs_of_graphRoute
    (C := C) hmin
    (graphRoute_of_minimalFailure_remainingSlack
      (C := C) hmin hslack)

/-- If the finite planar outer-component theorem is proved, and no-cut is
available for minimal failures, then the live S2 chosen-cycle row family follows
without fixing the canonical girth cycle. -/
noncomputable def minimalFailureChosenRows_of_finitePlanarOuterComponentTheorem
    (outerComponent :
      FinitePlanarStraightLineOuterComponentTheorem)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    JordanBoundaryConcrete.MinimalFailureChosenJordanOuterComponentRows :=
  fun {n} C hmin =>
    Classical.choice
      (outerComponent C
        (finitePlanarOuterComponentInputs_of_minimalFailure_noCutVertex
          (C := C) hmin (noCutRows (n := n) C hmin)))

/-- The raw face/enclosure field is exactly nonempty concrete topology facts. -/
theorem exactOuterBoundaryTopologyFields_iff_topologyFacts
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFields C <->
      Nonempty (TopologyFacts.{0} C) := by
  constructor
  · rintro ⟨H, F, hF, ⟨E⟩⟩
    exact
      ⟨{
        outerFaceData :=
          { faceBoundary := H
            outerFace := F
            outerFace_isOuter := hF }
        enclosureData :=
          { outerEnclosure := E } }⟩
  · rintro ⟨T⟩
    exact exactOuterBoundaryTopologyFields_of_topologyFacts T

/-- The raw face/enclosure field is exactly nonempty missing-topology facts. -/
theorem exactOuterBoundaryTopologyFields_iff_missingTopologyFacts
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFields C <->
      Nonempty (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) := by
  constructor
  · rintro ⟨H, F, hF, ⟨E⟩⟩
    exact
      ⟨{
        faceBoundary := H
        outerFace := F
        outerFace_isOuter := hF
        outerEnclosure := E }⟩
  · rintro ⟨T⟩
    exact exactOuterBoundaryTopologyFields_of_missingTopologyFacts T

/-- The raw face/enclosure field is exactly nonempty checked core data. -/
theorem exactOuterBoundaryTopologyFields_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFields C <->
      Nonempty (OuterBoundaryCore.{0} (canonicalGraph C)) := by
  constructor
  · rintro ⟨H, F, hF, ⟨E⟩⟩
    exact
      ⟨{
        faceBoundary := H
        outerFace := F
        outerFace_isOuter := hF
        outerEnclosure := E }⟩
  · rintro ⟨P⟩
    exact exactOuterBoundaryTopologyFields_of_outerBoundaryCore P

/--
Topology completion after the graph route is cleared.  The equivalence below
shows that the only remaining content is the raw face/enclosure field.
-/
def MinimalFailureTopologyCompletion (C : _root_.UDConfig n) : Prop :=
  Exists fun _route : MinimalFailureGraphRoute C =>
    ExactOuterBoundaryTopologyFields C

/--
Once the graph route is available, completing the minimal-failure topology
package is equivalent to producing concrete topology facts.
-/
theorem minimalFailureTopologyCompletion_iff_topologyFacts_of_graphRoute
    {C : _root_.UDConfig n}
    (route : MinimalFailureGraphRoute C) :
    MinimalFailureTopologyCompletion C <->
      Nonempty (TopologyFacts.{0} C) := by
  constructor
  · rintro ⟨_route, hfields⟩
    exact (exactOuterBoundaryTopologyFields_iff_topologyFacts C).1 hfields
  · intro hT
    exact
      ⟨route, (exactOuterBoundaryTopologyFields_iff_topologyFacts C).2 hT⟩

/--
Minimality plus the current no-cut slack reduces the requested W12 package to
exactly the face/enclosure field above.
-/
theorem minimalFailureTopologyCompletion_iff_topologyFacts_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexFinal.RemainingNoCutSlackFact C) :
    MinimalFailureTopologyCompletion C <->
      Nonempty (TopologyFacts.{0} C) :=
  minimalFailureTopologyCompletion_iff_topologyFacts_of_graphRoute
    (graphRoute_of_minimalFailure_remainingSlack
      (C := C) hmin hslack)

end MinimalFailureTopology

end

end JordanTopologyFactsConcrete
end Swanepoel
end ErdosProblems1066
