import ErdosProblems1066.Swanepoel.JordanBoundaryConcrete

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

end

end JordanTopologyFactsConcrete
end Swanepoel
end ErdosProblems1066
