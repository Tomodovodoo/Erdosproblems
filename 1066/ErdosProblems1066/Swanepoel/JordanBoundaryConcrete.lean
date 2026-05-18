import ErdosProblems1066.Swanepoel.JordanBoundaryExtraction

set_option autoImplicit false

/-!
# Concrete `UDConfig` Jordan-boundary adapter

This module is the concrete entry point from a `UDConfig` to the checked
outer-boundary/Jordan extraction facade.

The canonical unit-distance edge set is already known to be noncrossing, via
`NoncrossingUnitEdges` and `FaceReduction`.  What is not constructed in the
current Mathlib/project stack is the topological face theory: the finite face
type, its cyclic boundary walks, the selected unbounded face, and the enclosure
predicates coming from a Jordan-curve theorem.  Those are therefore packaged as
the minimal explicit `MissingTopologyFacts` below.  Everything after that point
is a proved projection into the existing planar and outer-boundary interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace JordanBoundaryConcrete

noncomputable section

variable {n : Nat}
universe u

/-- The canonical straight-line unit-distance graph attached to a `UDConfig`. -/
abbrev canonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C

/-- The actual noncrossing theorem available for every `UDConfig`. -/
theorem unitDistanceEdges_pairwiseNoncrossing (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing C (GraphBridge.unitDistanceEdges C) :=
  FaceReduction.unitDistanceEdges_pairwiseNoncrossing C

/-- The canonical graph over `C` has pairwise noncrossing unit edges. -/
theorem canonicalGraph_pairwiseNoncrossing (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  (canonicalGraph C).pairwiseNoncrossing

/-! ## Split topology-facing input -/

/--
The face-boundary and selected-outer-face part of the still-missing topology
input for the canonical graph of a `UDConfig`.

This is the first half of `JordanBoundaryExtraction.Data`: it gives the finite
face-boundary surface and identifies the outer face, but it does not yet supply
the Jordan/enclosure predicates.
-/
structure MissingOuterFaceData (C : _root_.UDConfig n) where
  faceBoundary :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses (canonicalGraph C)
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace

namespace MissingOuterFaceData

variable {C : _root_.UDConfig n}

/-- Repackage the selected outer-face data for the extraction facade. -/
def toExtractionOuterFaceData (D : MissingOuterFaceData C) :
    JordanBoundaryExtraction.OuterFaceData (canonicalGraph C) where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

/-- Repackage extraction selected-face data in the concrete namespace. -/
def ofExtractionOuterFaceData
    (D : JordanBoundaryExtraction.OuterFaceData (canonicalGraph C)) :
    MissingOuterFaceData C where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

@[simp]
theorem toExtractionOuterFaceData_faceBoundary
    (D : MissingOuterFaceData C) :
    D.toExtractionOuterFaceData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toExtractionOuterFaceData_outerFace
    (D : MissingOuterFaceData C) :
    D.toExtractionOuterFaceData.outerFace = D.outerFace :=
  rfl

theorem toExtractionOuterFaceData_outerFace_isOuter
    (D : MissingOuterFaceData C) :
    D.toExtractionOuterFaceData.faceBoundary.IsOuterFace
      D.toExtractionOuterFaceData.outerFace :=
  D.outerFace_isOuter

@[simp]
theorem ofExtractionOuterFaceData_faceBoundary
    (D : JordanBoundaryExtraction.OuterFaceData (canonicalGraph C)) :
    (ofExtractionOuterFaceData D).faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem ofExtractionOuterFaceData_outerFace
    (D : JordanBoundaryExtraction.OuterFaceData (canonicalGraph C)) :
    (ofExtractionOuterFaceData D).outerFace = D.outerFace :=
  rfl

theorem ofExtractionOuterFaceData_outerFace_isOuter
    (D : JordanBoundaryExtraction.OuterFaceData (canonicalGraph C)) :
    (ofExtractionOuterFaceData D).faceBoundary.IsOuterFace
      (ofExtractionOuterFaceData D).outerFace :=
  D.outerFace_isOuter

@[simp]
theorem ofExtractionOuterFaceData_toExtractionOuterFaceData
    (D : MissingOuterFaceData C) :
    ofExtractionOuterFaceData D.toExtractionOuterFaceData = D := by
  cases D
  rfl

@[simp]
theorem toExtractionOuterFaceData_ofExtractionOuterFaceData
    (D : JordanBoundaryExtraction.OuterFaceData (canonicalGraph C)) :
    (ofExtractionOuterFaceData D).toExtractionOuterFaceData = D := by
  cases D
  rfl

/-- Repackage an already checked core as selected outer-face data. -/
def ofCore (P : OuterBoundaryCore (canonicalGraph C)) :
    MissingOuterFaceData C where
  faceBoundary := P.faceBoundary
  outerFace := P.outerFace
  outerFace_isOuter := P.outerFace_isOuter

@[simp]
theorem ofCore_faceBoundary
    (P : OuterBoundaryCore (canonicalGraph C)) :
    (ofCore P).faceBoundary = P.faceBoundary :=
  rfl

@[simp]
theorem ofCore_outerFace
    (P : OuterBoundaryCore (canonicalGraph C)) :
    (ofCore P).outerFace = P.outerFace :=
  rfl

theorem ofCore_outerFace_isOuter
    (P : OuterBoundaryCore (canonicalGraph C)) :
    (ofCore P).faceBoundary.IsOuterFace (ofCore P).outerFace :=
  P.outerFace_isOuter

/-- The old planar face-boundary interface obtained from the supplied faces. -/
def planarFaceBoundary (D : MissingOuterFaceData C) :
    PlanarInterface.FaceBoundaryHypotheses (canonicalGraph C).toStraightLine :=
  D.toExtractionOuterFaceData.planarFaceBoundary

@[simp]
theorem planarFaceBoundary_eq (D : MissingOuterFaceData C) :
    D.planarFaceBoundary = D.faceBoundary.toFaceBoundaryHypotheses :=
  rfl

/-- The canonical graph supplies noncrossing; it is not topology input. -/
theorem pairwiseNoncrossing (_D : MissingOuterFaceData C) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  canonicalGraph_pairwiseNoncrossing C

/-- The selected outer boundary cycle. -/
def outerCycle (D : MissingOuterFaceData C) :
    OuterBoundaryInterface.BoundaryCycle (canonicalGraph C) :=
  D.toExtractionOuterFaceData.outerCycle

@[simp]
theorem outerCycle_eq (D : MissingOuterFaceData C) :
    D.outerCycle =
      OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
        D.faceBoundary D.outerFace :=
  rfl

@[simp]
theorem outerCycle_length (D : MissingOuterFaceData C) :
    D.outerCycle.length = D.faceBoundary.boundaryLength D.outerFace :=
  rfl

theorem outerCycle_vertex_injective (D : MissingOuterFaceData C) :
    Function.Injective D.outerCycle.vertex :=
  D.toExtractionOuterFaceData.outerCycle_vertex_injective

theorem outerCycle_adjacent_unitDistanceAdj
    (D : MissingOuterFaceData C) (k : Fin D.outerCycle.length) :
    GraphBridge.UnitDistanceAdj (canonicalGraph C).config
      (D.outerCycle.vertex k)
      (D.outerCycle.vertex
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) :=
  D.toExtractionOuterFaceData.outerCycle_adjacent_unitDistanceAdj k

theorem outerCycle_edge_geometry_dist_eq_one
    (D : MissingOuterFaceData C) (k : Fin D.outerCycle.length) :
    Geometry.Distance.eucDist (D.outerCycle.point k)
      (D.outerCycle.point
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) = 1 :=
  D.toExtractionOuterFaceData.outerCycle_edge_geometry_dist_eq_one k

/-- The selected outer boundary cycle has the derived simple-polygon witness. -/
def outerSimplePolygon (D : MissingOuterFaceData C) :
    OuterBoundaryInterface.SimplePolygon (canonicalGraph C) D.outerCycle :=
  D.toExtractionOuterFaceData.outerSimplePolygon

/-- The selected face is marked outer in the supplied face data. -/
theorem isOuterFace (D : MissingOuterFaceData C) :
    D.faceBoundary.IsOuterFace D.outerFace :=
  D.toExtractionOuterFaceData.isOuterFace

end MissingOuterFaceData

/--
The enclosure half of the still-missing topology input, over an already chosen
outer face.
-/
structure MissingEnclosureData {C : _root_.UDConfig n}
    (D : MissingOuterFaceData C) where
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (canonicalGraph C) D.faceBoundary D.outerFace

namespace MissingEnclosureData

variable {C : _root_.UDConfig n}
variable {D : MissingOuterFaceData C}

/-- Repackage the enclosure predicates for the extraction facade. -/
def toExtractionEnclosureData (E : MissingEnclosureData D) :
    JordanBoundaryExtraction.EnclosureData
      D.toExtractionOuterFaceData where
  outerEnclosure := E.outerEnclosure

@[simp]
theorem toExtractionEnclosureData_outerEnclosure
    (E : MissingEnclosureData D) :
    E.toExtractionEnclosureData.outerEnclosure = E.outerEnclosure :=
  rfl

/-- Package selected-face and enclosure data as extraction data. -/
def toExtractionData (E : MissingEnclosureData D) :
    JordanBoundaryExtraction.Data (canonicalGraph C) :=
  JordanBoundaryExtraction.Data.ofEnclosureData
    D.toExtractionOuterFaceData E.toExtractionEnclosureData

@[simp]
theorem toExtractionData_faceBoundary
    (E : MissingEnclosureData D) :
    E.toExtractionData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toExtractionData_outerFace
    (E : MissingEnclosureData D) :
    E.toExtractionData.outerFace = D.outerFace :=
  rfl

theorem toExtractionData_outerFace_isOuter
    (E : MissingEnclosureData D) :
    E.toExtractionData.faceBoundary.IsOuterFace
      E.toExtractionData.outerFace :=
  D.outerFace_isOuter

@[simp]
theorem toExtractionData_outerEnclosure
    (E : MissingEnclosureData D) :
    E.toExtractionData.outerEnclosure = E.outerEnclosure :=
  rfl

/-- Package selected-face and enclosure data as the checked core. -/
def toCore (E : MissingEnclosureData D) :
    OuterBoundaryCore (canonicalGraph C) :=
  E.toExtractionData.toCore

@[simp]
theorem toCore_faceBoundary (E : MissingEnclosureData D) :
    E.toCore.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toCore_outerFace (E : MissingEnclosureData D) :
    E.toCore.outerFace = D.outerFace :=
  rfl

theorem toCore_outerFace_isOuter (E : MissingEnclosureData D) :
    E.toCore.faceBoundary.IsOuterFace E.toCore.outerFace :=
  D.outerFace_isOuter

@[simp]
theorem toCore_outerEnclosure (E : MissingEnclosureData D) :
    E.toCore.outerEnclosure = E.outerEnclosure :=
  rfl

end MissingEnclosureData

/--
The topological facts still missing from a fully concrete Jordan extraction.

These are exactly the data not produced by the current Mathlib/project
development: finite face-boundary data for the canonical drawing, a chosen
outer face, the proof that it is outer, and the enclosure predicates/facts for
that face.  Noncrossing is deliberately absent, because it is proved above from
the `UDConfig` separation condition.
-/
structure MissingTopologyFacts (C : _root_.UDConfig n) where
  faceBoundary :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses (canonicalGraph C)
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (canonicalGraph C) faceBoundary outerFace

namespace MissingTopologyFacts

variable {C : _root_.UDConfig n}

/-! ## Split topology-facing projections -/

/-- Forget the enclosure predicates, retaining only the selected outer face. -/
def toOuterFaceData (T : MissingTopologyFacts C) :
    MissingOuterFaceData C where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter

/-- The enclosure predicates over `toOuterFaceData`. -/
def toEnclosureData (T : MissingTopologyFacts C) :
    MissingEnclosureData T.toOuterFaceData where
  outerEnclosure := T.outerEnclosure

/-- Assemble the older missing-topology package from the split data. -/
def ofEnclosureData
    (D : MissingOuterFaceData C) (E : MissingEnclosureData D) :
    MissingTopologyFacts C where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter
  outerEnclosure := E.outerEnclosure

@[simp]
theorem toOuterFaceData_faceBoundary (T : MissingTopologyFacts C) :
    T.toOuterFaceData.faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem toOuterFaceData_outerFace (T : MissingTopologyFacts C) :
    T.toOuterFaceData.outerFace = T.outerFace :=
  rfl

theorem toOuterFaceData_outerFace_isOuter (T : MissingTopologyFacts C) :
    T.toOuterFaceData.faceBoundary.IsOuterFace
      T.toOuterFaceData.outerFace :=
  T.outerFace_isOuter

@[simp]
theorem toEnclosureData_outerEnclosure (T : MissingTopologyFacts C) :
    T.toEnclosureData.outerEnclosure = T.outerEnclosure :=
  rfl

@[simp]
theorem ofEnclosureData_faceBoundary
    (D : MissingOuterFaceData C) (E : MissingEnclosureData D) :
    (ofEnclosureData D E).faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem ofEnclosureData_outerFace
    (D : MissingOuterFaceData C) (E : MissingEnclosureData D) :
    (ofEnclosureData D E).outerFace = D.outerFace :=
  rfl

theorem ofEnclosureData_outerFace_isOuter
    (D : MissingOuterFaceData C) (E : MissingEnclosureData D) :
    (ofEnclosureData D E).faceBoundary.IsOuterFace
      (ofEnclosureData D E).outerFace :=
  D.outerFace_isOuter

@[simp]
theorem ofEnclosureData_outerEnclosure
    (D : MissingOuterFaceData C) (E : MissingEnclosureData D) :
    (ofEnclosureData D E).outerEnclosure = E.outerEnclosure :=
  rfl

@[simp]
theorem ofEnclosureData_toOuterFaceData
    (D : MissingOuterFaceData C) (E : MissingEnclosureData D) :
    (ofEnclosureData D E).toOuterFaceData = D := by
  cases D
  cases E
  rfl

@[simp]
theorem ofEnclosureData_toEnclosureData
    (D : MissingOuterFaceData C) (E : MissingEnclosureData D) :
    (ofEnclosureData D E).toEnclosureData = E := by
  cases D
  cases E
  rfl

@[simp]
theorem ofEnclosureData_toOuterFaceData_toEnclosureData
    (T : MissingTopologyFacts C) :
    ofEnclosureData T.toOuterFaceData T.toEnclosureData = T := by
  cases T
  rfl

/-- Package the missing topology facts as the existing extraction facade. -/
def toExtractionData (T : MissingTopologyFacts C) :
    JordanBoundaryExtraction.Data (canonicalGraph C) where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter
  outerEnclosure := T.outerEnclosure

@[simp]
theorem toExtractionData_faceBoundary (T : MissingTopologyFacts C) :
    T.toExtractionData.faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem toExtractionData_outerFace (T : MissingTopologyFacts C) :
    T.toExtractionData.outerFace = T.outerFace :=
  rfl

theorem toExtractionData_outerFace_isOuter (T : MissingTopologyFacts C) :
    T.toExtractionData.faceBoundary.IsOuterFace T.toExtractionData.outerFace :=
  T.outerFace_isOuter

@[simp]
theorem toExtractionData_outerEnclosure (T : MissingTopologyFacts C) :
    T.toExtractionData.outerEnclosure = T.outerEnclosure :=
  rfl

/-- Repackage extraction data as the older missing-topology package. -/
def ofExtractionData
    (D : JordanBoundaryExtraction.Data (canonicalGraph C)) :
    MissingTopologyFacts C where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter
  outerEnclosure := D.outerEnclosure

/-- Repackage an already checked outer-boundary core as concrete topology data. -/
def ofCore (P : OuterBoundaryCore (canonicalGraph C)) :
    MissingTopologyFacts C where
  faceBoundary := P.faceBoundary
  outerFace := P.outerFace
  outerFace_isOuter := P.outerFace_isOuter
  outerEnclosure := P.outerEnclosure

@[simp]
theorem ofExtractionData_faceBoundary
    (D : JordanBoundaryExtraction.Data (canonicalGraph C)) :
    (ofExtractionData D).faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem ofExtractionData_outerFace
    (D : JordanBoundaryExtraction.Data (canonicalGraph C)) :
    (ofExtractionData D).outerFace = D.outerFace :=
  rfl

theorem ofExtractionData_outerFace_isOuter
    (D : JordanBoundaryExtraction.Data (canonicalGraph C)) :
    (ofExtractionData D).faceBoundary.IsOuterFace
      (ofExtractionData D).outerFace :=
  D.outerFace_isOuter

@[simp]
theorem ofExtractionData_outerEnclosure
    (D : JordanBoundaryExtraction.Data (canonicalGraph C)) :
    (ofExtractionData D).outerEnclosure = D.outerEnclosure :=
  rfl

@[simp]
theorem ofCore_faceBoundary
    (P : OuterBoundaryCore (canonicalGraph C)) :
    (ofCore P).faceBoundary = P.faceBoundary :=
  rfl

@[simp]
theorem ofCore_outerFace
    (P : OuterBoundaryCore (canonicalGraph C)) :
    (ofCore P).outerFace = P.outerFace :=
  rfl

theorem ofCore_outerFace_isOuter
    (P : OuterBoundaryCore (canonicalGraph C)) :
    (ofCore P).faceBoundary.IsOuterFace (ofCore P).outerFace :=
  P.outerFace_isOuter

@[simp]
theorem ofCore_outerEnclosure
    (P : OuterBoundaryCore (canonicalGraph C)) :
    (ofCore P).outerEnclosure = P.outerEnclosure :=
  rfl

@[simp]
theorem toExtractionData_ofExtractionData
    (D : JordanBoundaryExtraction.Data (canonicalGraph C)) :
    (ofExtractionData D).toExtractionData = D := by
  cases D
  rfl

@[simp]
theorem ofExtractionData_toExtractionData
    (T : MissingTopologyFacts C) :
    ofExtractionData T.toExtractionData = T := by
  cases T
  rfl

@[simp]
theorem toExtractionData_eq_split_toExtractionData
    (T : MissingTopologyFacts C) :
    T.toExtractionData = T.toEnclosureData.toExtractionData := by
  cases T
  rfl

/-! ## Projections to `OuterBoundaryCore` -/

/-- The honest outer-boundary core obtained from the concrete `UDConfig` input. -/
def toCore (T : MissingTopologyFacts C) :
    OuterBoundaryCore (canonicalGraph C) :=
  T.toExtractionData.toCore

@[simp]
theorem toCore_faceBoundary (T : MissingTopologyFacts C) :
    T.toCore.faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem toCore_outerFace (T : MissingTopologyFacts C) :
    T.toCore.outerFace = T.outerFace :=
  rfl

theorem toCore_outerFace_isOuter (T : MissingTopologyFacts C) :
    T.toCore.faceBoundary.IsOuterFace T.toCore.outerFace :=
  T.outerFace_isOuter

@[simp]
theorem toCore_outerEnclosure (T : MissingTopologyFacts C) :
    T.toCore.outerEnclosure = T.outerEnclosure :=
  rfl

@[simp]
theorem toCore_ofCore
    (P : OuterBoundaryCore (canonicalGraph C)) :
    (ofCore P).toCore = P := by
  cases P
  rfl

@[simp]
theorem ofCore_toCore
    (T : MissingTopologyFacts C) :
    ofCore T.toCore = T := by
  cases T
  rfl

@[simp]
theorem ofExtractionData_eq_ofCore_toCore
    (D : JordanBoundaryExtraction.Data (canonicalGraph C)) :
    ofExtractionData D = ofCore D.toCore := by
  cases D
  rfl

/-! ## Projections to the planar interface -/

/-- The old planar face-boundary interface obtained from the supplied faces. -/
def planarFaceBoundary (T : MissingTopologyFacts C) :
    PlanarInterface.FaceBoundaryHypotheses (canonicalGraph C).toStraightLine :=
  T.toExtractionData.planarFaceBoundary

@[simp]
theorem planarFaceBoundary_eq (T : MissingTopologyFacts C) :
    T.planarFaceBoundary = T.faceBoundary.toFaceBoundaryHypotheses :=
  rfl

/-- The noncrossing field in the planar interface is the proved canonical fact. -/
theorem planarFaceBoundary_noncrossing (T : MissingTopologyFacts C) :
    T.planarFaceBoundary.noncrossing =
      canonicalGraph_pairwiseNoncrossing C :=
  rfl

/-- Pairwise noncrossing projected through the extraction facade. -/
theorem pairwiseNoncrossing (T : MissingTopologyFacts C) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  T.toExtractionData.pairwiseNoncrossing

/-! ## Outer-boundary cycle and enclosure projections -/

/-- The selected outer boundary cycle. -/
def outerCycle (T : MissingTopologyFacts C) :
    OuterBoundaryInterface.BoundaryCycle (canonicalGraph C) :=
  T.toExtractionData.outerCycle

@[simp]
theorem outerCycle_eq (T : MissingTopologyFacts C) :
    T.outerCycle =
      OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
        T.faceBoundary T.outerFace :=
  rfl

theorem outerCycle_vertex_injective (T : MissingTopologyFacts C) :
    Function.Injective T.outerCycle.vertex :=
  T.toExtractionData.outerCycle_vertex_injective

theorem outerCycle_adjacent_unitDistanceAdj
    (T : MissingTopologyFacts C) (k : Fin T.outerCycle.length) :
    GraphBridge.UnitDistanceAdj (canonicalGraph C).config
      (T.outerCycle.vertex k)
      (T.outerCycle.vertex
        (PlanarInterface.cyclicSucc T.outerCycle.length_pos k)) :=
  T.toExtractionData.outerCycle_adjacent_unitDistanceAdj k

theorem outerCycle_edge_geometry_dist_eq_one
    (T : MissingTopologyFacts C) (k : Fin T.outerCycle.length) :
    Geometry.Distance.eucDist (T.outerCycle.point k)
      (T.outerCycle.point
        (PlanarInterface.cyclicSucc T.outerCycle.length_pos k)) = 1 :=
  T.toExtractionData.outerCycle_edge_geometry_dist_eq_one k

/-- The selected outer boundary cycle has the derived simple-polygon witness. -/
def outerSimplePolygon (T : MissingTopologyFacts C) :
    OuterBoundaryInterface.SimplePolygon (canonicalGraph C) T.outerCycle :=
  T.toExtractionData.outerSimplePolygon

/-- The selected face is marked outer in the supplied face data. -/
theorem isOuterFace (T : MissingTopologyFacts C) :
    T.faceBoundary.IsOuterFace T.outerFace :=
  T.toExtractionData.isOuterFace

/-- Boundary vertices satisfy the supplied boundary predicate. -/
theorem boundary_vertex_onBoundary
    (T : MissingTopologyFacts C)
    (k : Fin (T.faceBoundary.boundaryLength T.outerFace)) :
    T.outerEnclosure.onBoundary
      (T.faceBoundary.boundaryVertex T.outerFace k) :=
  T.toExtractionData.boundary_vertex_onBoundary k

/-- Boundary points satisfy the supplied inside-or-on predicate. -/
theorem boundary_point_insideOrOn
    (T : MissingTopologyFacts C)
    (k : Fin (T.faceBoundary.boundaryLength T.outerFace)) :
    T.outerEnclosure.insideOrOn
      ((canonicalGraph C).point
        (T.faceBoundary.boundaryVertex T.outerFace k)) :=
  T.toExtractionData.boundary_point_insideOrOn k

/-- Every ambient vertex lies inside or on the supplied outer enclosure. -/
theorem all_vertices_insideOrOn (T : MissingTopologyFacts C) (v : Fin n) :
    T.outerEnclosure.insideOrOn ((canonicalGraph C).point v) :=
  T.toExtractionData.all_vertices_insideOrOn v

/-- The supplied boundary predicate is exactly the selected outer cycle. -/
theorem onBoundary_iff_outer_cycle (T : MissingTopologyFacts C) (v : Fin n) :
    T.outerEnclosure.onBoundary v <->
      Exists fun k : Fin (T.faceBoundary.boundaryLength T.outerFace) =>
        T.faceBoundary.boundaryVertex T.outerFace k = v :=
  T.toExtractionData.onBoundary_iff_outer_cycle v

/-! ## Counting facade projections -/

/-- The planar face-boundary input seen by `PlanarBoundaryFinal`. -/
def finalPlanarFaceBoundary (T : MissingTopologyFacts C) :
    PlanarInterface.FaceBoundaryHypotheses (canonicalGraph C).toStraightLine :=
  T.toExtractionData.finalPlanarFaceBoundary

@[simp]
theorem finalPlanarFaceBoundary_eq (T : MissingTopologyFacts C) :
    T.finalPlanarFaceBoundary = T.planarFaceBoundary :=
  rfl

/-- The canonical noncrossing input seen by `PlanarBoundaryFinal`. -/
theorem finalPairwiseNoncrossing (T : MissingTopologyFacts C) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  T.toExtractionData.finalPairwiseNoncrossing

/-- Direct counting-layer angle lower bound for supplied angle comparisons. -/
def finalOuterBoundaryAngleLowerBound
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.AngleLowerBound :=
  T.toExtractionData.finalOuterBoundaryAngleLowerBound
    counts geometricAngleSum hforced hpolygon

/-- Canonical face-counting package consumed by the final facade. -/
def finalCanonicalBoundaryCountHypotheses
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses (canonicalGraph C) :=
  T.toExtractionData.finalCanonicalBoundaryCountHypotheses
    counts geometricAngleSum hforced hpolygon

@[simp]
theorem finalCanonicalBoundaryCountHypotheses_faceBoundary
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    (T.finalCanonicalBoundaryCountHypotheses
      counts geometricAngleSum hforced hpolygon).faceBoundary =
        T.faceBoundary :=
  rfl

@[simp]
theorem finalCanonicalBoundaryCountHypotheses_counts
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    (T.finalCanonicalBoundaryCountHypotheses
      counts geometricAngleSum hforced hpolygon).counts = counts :=
  rfl

/-- E12 count inequality routed through the final facade. -/
theorem finalBoundaryAngleCountInequality
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.d5 + 2 * counts.d6 + counts.b + counts.B + 6 <= counts.d3 :=
  T.toExtractionData.finalBoundaryAngleCountInequality
    counts geometricAngleSum hforced hpolygon

/-- Negative-element E12 count inequality routed through the final facade. -/
theorem finalBoundaryNegativeCountInequality
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.negativeCount + counts.B + 6 <= counts.d3 :=
  T.toExtractionData.finalBoundaryNegativeCountInequality
    counts geometricAngleSum hforced hpolygon

/-! ## Full planar-boundary consumer projections -/

/--
Extend the concrete topology facts by the still-explicit angle and subpolygon
data to the full planar-boundary package consumed downstream.
-/
def toPlanarBoundaryData
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (canonicalGraph C) where
  core := T.toCore
  outerAngleBounds := outerAngleBounds
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData

@[simp]
theorem toPlanarBoundaryData_core
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).core = T.toCore :=
  rfl

@[simp]
theorem toPlanarBoundaryData_faceBoundary
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).faceBoundary =
        T.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_planarFaceBoundary
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).planarFaceBoundary =
        T.planarFaceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerFace
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).outerFace =
        T.outerFace :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerCycle
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).outerCycle =
        T.outerCycle :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerBoundaryCounts
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).outerBoundaryCounts =
        outerAngleBounds.counts :=
  rfl

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).Subpolygon =
        Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundaryData_subpolygonData
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C))
    (S : Subpolygon) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).subpolygonData S =
        subpolygonData S :=
  rfl

/-- The assembled face-counting bridge input consumed by the planar closure. -/
def toFaceCountingBridgeData
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    PlanarBoundaryClosure.FaceCountingBridgeData.{u} (canonicalGraph C) :=
  (T.toPlanarBoundaryData
    outerAngleBounds Subpolygon subpolygonData).toFaceCountingBridgeData

@[simp]
theorem toFaceCountingBridgeData_faceBoundary
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toFaceCountingBridgeData
      outerAngleBounds Subpolygon subpolygonData).faceBoundary =
        T.faceBoundary :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_planarFaceBoundary
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toFaceCountingBridgeData
      outerAngleBounds Subpolygon subpolygonData).planarFaceBoundary =
        T.planarFaceBoundary :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_outerCounts
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.toFaceCountingBridgeData
      outerAngleBounds Subpolygon subpolygonData).outerCounts =
        outerAngleBounds.counts :=
  rfl

/-- Checked counting conclusions exposed in the bridge consumer's shape. -/
theorem toFaceCountingBridgeData_countingTheorems
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    PlanarBoundaryClosure.FaceCountingBridgeData.CountingTheorems
      (T.toFaceCountingBridgeData outerAngleBounds Subpolygon subpolygonData) :=
  (T.toFaceCountingBridgeData
    outerAngleBounds Subpolygon subpolygonData).countingTheorems

/-- Concrete face-counting data exposed by `PlanarBoundaryFinal`. -/
def concreteFaceCountingData
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData) :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)

@[simp]
theorem concreteFaceCountingData_faceBoundary
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.concreteFaceCountingData
      outerAngleBounds Subpolygon subpolygonData).faceBoundary =
        T.faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_planarFaceBoundary
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.concreteFaceCountingData
      outerAngleBounds Subpolygon subpolygonData).planarFaceBoundary =
        T.planarFaceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryCounts
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.concreteFaceCountingData
      outerAngleBounds Subpolygon subpolygonData).boundaryCounts =
        outerAngleBounds.counts :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryCountHypotheses
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.concreteFaceCountingData
      outerAngleBounds Subpolygon subpolygonData).boundaryCountHypotheses =
        (T.toPlanarBoundaryData
          outerAngleBounds Subpolygon subpolygonData).canonicalBoundaryCountHypotheses :=
  rfl

@[simp]
theorem concreteFaceCountingData_Subpolygon
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    (T.concreteFaceCountingData
      outerAngleBounds Subpolygon subpolygonData).Subpolygon =
        Subpolygon :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonCounts
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C))
    (S : Subpolygon) :
    (T.concreteFaceCountingData
      outerAngleBounds Subpolygon subpolygonData).subpolygonCounts S =
        (subpolygonData S).counts :=
  rfl

/-- The full planar-boundary theorem summary obtained from concrete topology. -/
theorem toPlanarBoundaryData_faceCountingTheorems
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData) :=
  (T.toPlanarBoundaryData
    outerAngleBounds Subpolygon subpolygonData).faceCountingTheorems

/-- E12 after projecting the concrete topology facts to planar-boundary data. -/
theorem toPlanarBoundaryData_boundaryAngleCount
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    outerAngleBounds.counts.d5 + 2 * outerAngleBounds.counts.d6 +
        outerAngleBounds.counts.b + outerAngleBounds.counts.B + 6 <=
      outerAngleBounds.counts.d3 := by
  simpa using
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).boundaryAngleCountInequality

/-- Negative-element E12 after projecting to planar-boundary data. -/
theorem toPlanarBoundaryData_boundaryNegativeCount
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    outerAngleBounds.counts.negativeCount + outerAngleBounds.counts.B + 6 <=
      outerAngleBounds.counts.d3 := by
  simpa using
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).boundaryNegativeCountInequality

/-- Low-degree subpolygon conclusion after projecting to planar-boundary data. -/
theorem toPlanarBoundaryData_subpolygonLowDegree
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C))
    (S : Subpolygon) :
    6 <= 2 * (subpolygonData S).counts.D2 +
      (subpolygonData S).counts.D3 := by
  simpa using
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).subpolygonLowDegreeInequality S

/-- High-degree-slack subpolygon conclusion after planar-boundary projection. -/
theorem toPlanarBoundaryData_subpolygonLowDegreeWithHighDegreeSlack
    (T : MissingTopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C))
    (S : Subpolygon) :
    (subpolygonData S).counts.D5 +
        2 * (subpolygonData S).counts.D6 + 6 <=
      2 * (subpolygonData S).counts.D2 +
        (subpolygonData S).counts.D3 := by
  simpa using
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).subpolygonLowDegreeWithHighDegreeSlack S

/-! ## Honest remaining construction statement -/

/--
The minimal topology construction still missing for the canonical unit-distance
graph of `C`.

All graph-theoretic input in this file is already concrete: `canonicalGraph C`
is built from `C`, and noncrossing of its unit edges is proved by
`canonicalGraph_pairwiseNoncrossing`.  What remains is exactly the existence of
finite face-boundary data, a selected outer face, and enclosure predicates for
that selected face.
-/
def RemainingTopologyTheorem (C : _root_.UDConfig n) : Prop :=
  Nonempty (MissingTopologyFacts.{0} C)

/--
Equivalent split form of the remaining theorem: first construct the
face-boundary surface and selected outer face, then construct the enclosure
data over that selected face.
-/
theorem remainingTopologyTheorem_iff_split (C : _root_.UDConfig n) :
    RemainingTopologyTheorem C <->
      Exists fun D : MissingOuterFaceData.{0} C =>
        Nonempty (MissingEnclosureData.{0} D) := by
  constructor
  · rintro ⟨T⟩
    exact ⟨T.toOuterFaceData, ⟨T.toEnclosureData⟩⟩
  · rintro ⟨D, ⟨E⟩⟩
    exact ⟨MissingTopologyFacts.ofEnclosureData D E⟩

/--
Equivalent extraction-facade form of the remaining theorem.  This confirms that
`MissingTopologyFacts` adds no extra assumptions beyond the existing
`JordanBoundaryExtraction.Data` record.
-/
theorem remainingTopologyTheorem_iff_extractionData
    (C : _root_.UDConfig n) :
    RemainingTopologyTheorem C <->
      Nonempty (JordanBoundaryExtraction.Data.{0} (canonicalGraph C)) := by
  constructor
  · rintro ⟨T⟩
    exact ⟨T.toExtractionData⟩
  · rintro ⟨D⟩
    exact ⟨MissingTopologyFacts.ofExtractionData D⟩

/--
Equivalent checked-core form of the remaining theorem.  Thus the honest
construction target can also be read as: construct an `OuterBoundaryCore` for
the canonical graph attached to `C`.
-/
theorem remainingTopologyTheorem_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    RemainingTopologyTheorem C <->
      Nonempty (OuterBoundaryCore.{0} (canonicalGraph C)) := by
  constructor
  · rintro ⟨T⟩
    exact ⟨T.toCore⟩
  · rintro ⟨P⟩
    exact ⟨MissingTopologyFacts.ofCore P⟩

/--
If the remaining topology construction is supplied, then any already explicit
angle and subpolygon data assemble into the full planar-boundary consumer.
-/
theorem remainingTopologyTheorem_to_planarBoundaryData
    {C : _root_.UDConfig n}
    (h : RemainingTopologyTheorem C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (canonicalGraph C)) :
    Nonempty (PlanarBoundaryClosure.PlanarBoundaryData.{u, 0}
      (canonicalGraph C)) := by
  rcases h with ⟨T⟩
  exact ⟨T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData⟩

/--
Conversely, any full planar-boundary consumer for the canonical graph already
contains enough topology/core data to discharge `RemainingTopologyTheorem`.
-/
theorem remainingTopologyTheorem_of_planarBoundaryData
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u, 0} (canonicalGraph C)) :
    RemainingTopologyTheorem C :=
  ⟨MissingTopologyFacts.ofCore D.core⟩

/--
The global paper-facing construction theorem that is not supplied by the
current Mathlib/project topology stack.

This is intentionally a proposition, not a global assumption or declaration
with a fake witness.  Proving it would close the concrete outer-face/Jordan
extraction for every `UDConfig`; the lemmas above show the exact checked
records it must produce.
-/
def RemainingTopologyConstructionTheorem : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n), RemainingTopologyTheorem C

end MissingTopologyFacts

end

end JordanBoundaryConcrete
end Swanepoel
end ErdosProblems1066
