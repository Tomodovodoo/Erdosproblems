import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Girth
import ErdosProblems1066.Swanepoel.JordanBoundaryExtraction
import ErdosProblems1066.Swanepoel.CutVertexFinal
import ErdosProblems1066.Swanepoel.MinimalConnectednessClosure

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

/-! ## Concrete selected-face construction from a real unit edge -/

/--
A real unit-distance adjacency supplies the currently recorded selected
outer-face data: the unique recorded face is the two-endpoint cyclic boundary
carried by that edge.
-/
def ofUnitDistanceAdj {i j : Fin n}
    (hAdj : GraphBridge.UnitDistanceAdj C i j) :
    MissingOuterFaceData C := by
  let hGAdj : (canonicalGraph C).Adj i j :=
    ((canonicalGraph C).adj_iff_unitDistanceAdj i j).2 hAdj
  let H :=
    FaceReduction.UnitDistanceFaceBoundaryHypotheses.ofAdjacentPair
      (canonicalGraph C) hGAdj
  exact
    { faceBoundary := H
      outerFace := PUnit.unit
      outerFace_isOuter := trivial }

@[simp]
theorem ofUnitDistanceAdj_outerCycle_length {i j : Fin n}
    (hAdj : GraphBridge.UnitDistanceAdj C i j) :
    (ofUnitDistanceAdj (C := C) hAdj).outerCycle.length = 2 :=
  rfl

/-- The accepted adjacent-pair selected-face witness is only a two-vertex
cycle, so it does not satisfy the stronger nondegenerate cycle lane. -/
theorem not_three_le_ofUnitDistanceAdj_outerCycle_length {i j : Fin n}
    (hAdj : GraphBridge.UnitDistanceAdj C i j) :
    Not (3 <= (ofUnitDistanceAdj (C := C) hAdj).outerCycle.length) := by
  intro hcycle
  rw [ofUnitDistanceAdj_outerCycle_length (C := C) hAdj] at hcycle
  norm_num at hcycle

/-- Any selected outer-face payload contains at least one unit-distance
adjacency along its recorded cyclic boundary. -/
theorem exists_unitDistanceAdj (D : MissingOuterFaceData C) :
    Exists fun i : Fin n =>
      Exists fun j : Fin n => GraphBridge.UnitDistanceAdj C i j := by
  simpa using
    D.faceBoundary.exists_unitDistanceAdj_of_selectedFace D.outerFace

/-- The selected outer-face payload is exactly the data of one real unit edge
for the present formal face-boundary interface. -/
theorem nonempty_iff_exists_unitDistanceAdj :
    Nonempty (MissingOuterFaceData C) <->
      Exists fun i : Fin n =>
        Exists fun j : Fin n => GraphBridge.UnitDistanceAdj C i j := by
  constructor
  · rintro ⟨D⟩
    exact D.exists_unitDistanceAdj
  · rintro ⟨i, j, hAdj⟩
    exact ⟨ofUnitDistanceAdj (C := C) hAdj⟩

end MissingOuterFaceData

/-! ## Nondegenerate actual outer-boundary cycle data -/

/--
The stronger selected outer-boundary payload needed by the geometry route.

It starts from an actual `OuterBoundaryCore`, hence it carries the face-boundary
surface, the selected outer face, the enclosure predicates, and the selected
boundary cycle.  The extra length field rules out the accepted two-endpoint
interface witness supplied by `MissingOuterFaceData.ofUnitDistanceAdj`.
-/
structure ActualOuterBoundaryCycleData (C : _root_.UDConfig n) where
  core : OuterBoundaryCore.{u} (canonicalGraph C)
  outerCycle_length_ge_three : 3 <= core.outerCycle.length

namespace ActualOuterBoundaryCycleData

variable {C : _root_.UDConfig n}

/-- The supplied face-boundary data for the actual selected outer face. -/
def faceBoundary (D : ActualOuterBoundaryCycleData C) :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses (canonicalGraph C) :=
  D.core.faceBoundary

/-- The selected outer face in the supplied face-boundary data. -/
def outerFace (D : ActualOuterBoundaryCycleData C) :
    D.faceBoundary.Face :=
  D.core.outerFace

/-- The selected face is marked as outer in the supplied face data. -/
theorem outerFace_isOuter (D : ActualOuterBoundaryCycleData C) :
    D.faceBoundary.IsOuterFace D.outerFace :=
  D.core.outerFace_isOuter

/-- The enclosure predicates attached to the selected outer face. -/
def outerEnclosure (D : ActualOuterBoundaryCycleData C) :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (canonicalGraph C) D.faceBoundary D.outerFace :=
  D.core.outerEnclosure

/-- The actual selected outer-boundary cycle. -/
def outerCycle (D : ActualOuterBoundaryCycleData C) :
    OuterBoundaryInterface.BoundaryCycle (canonicalGraph C) :=
  D.core.outerCycle

@[simp]
theorem outerCycle_eq (D : ActualOuterBoundaryCycleData C) :
    D.outerCycle =
      OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
        D.faceBoundary D.outerFace :=
  rfl

/-- The actual selected outer-boundary cycle is nondegenerate. -/
theorem three_le_outerCycle_length (D : ActualOuterBoundaryCycleData C) :
    3 <= D.outerCycle.length :=
  D.outerCycle_length_ge_three

/-- The actual selected outer-boundary cycle has more than two vertices. -/
theorem two_lt_outerCycle_length (D : ActualOuterBoundaryCycleData C) :
    2 < D.outerCycle.length :=
  Nat.lt_of_lt_of_le (by decide) D.three_le_outerCycle_length

/-- The actual selected outer-boundary cycle is not the two-endpoint weak
selected-face witness. -/
theorem outerCycle_length_ne_two (D : ActualOuterBoundaryCycleData C) :
    D.outerCycle.length ≠ 2 :=
  Nat.ne_of_gt D.two_lt_outerCycle_length

/-- The actual selected outer-boundary cycle is vertex-simple. -/
theorem outerCycle_vertex_injective (D : ActualOuterBoundaryCycleData C) :
    Function.Injective D.outerCycle.vertex :=
  D.core.outerCycle_vertex_injective

/-- Different positions on the actual selected outer cycle name different
ambient vertices. -/
theorem outerCycle_vertex_ne_of_ne
    (D : ActualOuterBoundaryCycleData C)
    {i j : Fin D.outerCycle.length} (hij : i ≠ j) :
    D.outerCycle.vertex i ≠ D.outerCycle.vertex j := by
  intro hv
  exact hij (D.outerCycle_vertex_injective hv)

/-- Consecutive vertices on the actual selected outer cycle are unit adjacent. -/
theorem outerCycle_adjacent_unitDistanceAdj
    (D : ActualOuterBoundaryCycleData C) (k : Fin D.outerCycle.length) :
    GraphBridge.UnitDistanceAdj (canonicalGraph C).config
      (D.outerCycle.vertex k)
      (D.outerCycle.vertex
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) :=
  D.core.outerCycle_adjacent_unitDistanceAdj k

/-- Consecutive edges on the actual selected outer cycle have unit length. -/
theorem outerCycle_edge_geometry_dist_eq_one
    (D : ActualOuterBoundaryCycleData C) (k : Fin D.outerCycle.length) :
    Geometry.Distance.eucDist (D.outerCycle.point k)
      (D.outerCycle.point
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) = 1 :=
  D.core.outerCycle_edge_geometry_dist_eq_one k

/-- The actual selected outer-boundary cycle has the simple-polygon witness. -/
def outerSimplePolygon (D : ActualOuterBoundaryCycleData C) :
    OuterBoundaryInterface.SimplePolygon
      (canonicalGraph C) D.outerCycle :=
  D.core.outerSimplePolygon

/-- Boundary vertices satisfy the actual boundary predicate. -/
theorem boundary_vertex_onBoundary
    (D : ActualOuterBoundaryCycleData C) (k : Fin D.outerCycle.length) :
    D.outerEnclosure.onBoundary (D.outerCycle.vertex k) :=
  D.core.boundary_vertex_onBoundary k

/-- Boundary points satisfy the actual inside-or-on predicate. -/
theorem boundary_point_insideOrOn
    (D : ActualOuterBoundaryCycleData C) (k : Fin D.outerCycle.length) :
    D.outerEnclosure.insideOrOn (D.outerCycle.point k) :=
  D.core.boundary_point_insideOrOn k

/-- Every ambient vertex lies inside or on the actual selected enclosure. -/
theorem all_vertices_insideOrOn
    (D : ActualOuterBoundaryCycleData C) (v : Fin n) :
    D.outerEnclosure.insideOrOn ((canonicalGraph C).point v) :=
  D.core.all_vertices_insideOrOn v

/-- The actual boundary predicate is exactly membership in the selected cycle. -/
theorem onBoundary_iff_outerCycle
    (D : ActualOuterBoundaryCycleData C) (v : Fin n) :
    D.outerEnclosure.onBoundary v <->
      Exists fun k : Fin D.outerCycle.length =>
        D.outerCycle.vertex k = v :=
  D.core.onBoundary_iff_outer_cycle v

/-- Forget the nondegenerate cycle fact, retaining the accepted selected-face
interface. -/
def toMissingOuterFaceData
    (D : ActualOuterBoundaryCycleData C) :
    MissingOuterFaceData C where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

@[simp]
theorem toMissingOuterFaceData_outerCycle
    (D : ActualOuterBoundaryCycleData C) :
    D.toMissingOuterFaceData.outerCycle = D.outerCycle :=
  rfl

/-- Build the stronger cycle payload from an already supplied core and a
nondegenerate selected-cycle length proof. -/
def ofCore
    (P : OuterBoundaryCore.{u} (canonicalGraph C))
    (hcycle : 3 <= P.outerCycle.length) :
    ActualOuterBoundaryCycleData C where
  core := P
  outerCycle_length_ge_three := hcycle

/-- Nonempty stronger cycle data is exactly an outer-boundary core whose
selected cycle is nondegenerate. -/
theorem nonempty_iff_outerBoundaryCore_with_length_ge_three :
    Nonempty (ActualOuterBoundaryCycleData.{u} C) <->
      Exists fun P : OuterBoundaryCore.{u} (canonicalGraph C) =>
        3 <= P.outerCycle.length := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact Exists.intro D.core D.outerCycle_length_ge_three
  case mpr =>
    intro h
    cases h with
    | intro P hcycle =>
        exact Nonempty.intro (ofCore P hcycle)

end ActualOuterBoundaryCycleData

/-! ## Simple cyclic boundary plus matching enclosure rows -/

/--
Concrete Jordan-boundary source rows for the strong S2 lane.

The row names a simple cyclic unit-distance boundary of length at least three
in the canonical graph, and it carries the enclosure predicates for that same
cycle.  This is the nondegenerate data needed downstream; it deliberately does
not use the two-vertex adjacent-pair selected-face witness.
-/
structure SimpleCyclicOuterBoundaryEnclosureRows
    (C : _root_.UDConfig n) where
  length : Nat
  length_pos : 0 < length
  vertex : Fin length -> Fin n
  adjacent :
    forall k : Fin length,
      (canonicalGraph C).Adj (vertex k)
        (vertex (PlanarInterface.cyclicSucc length_pos k))
  simple : Function.Injective vertex
  length_ge_three : 3 <= length
  insideOrOn : PlanarInterface.Point -> Prop
  onBoundary : Fin n -> Prop
  boundary_vertex_onBoundary :
    forall k : Fin length, onBoundary (vertex k)
  boundary_point_insideOrOn :
    forall k : Fin length, insideOrOn ((canonicalGraph C).point (vertex k))
  all_vertices_insideOrOn :
    forall v : Fin n, insideOrOn ((canonicalGraph C).point v)
  onBoundary_iff_outer_cycle :
    forall v : Fin n, onBoundary v <->
      Exists fun k : Fin length => vertex k = v

namespace SimpleCyclicOuterBoundaryEnclosureRows

variable {C : _root_.UDConfig n}

/-- Repackage the row as the boundary-cycle interface. -/
def toBoundaryCycle
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    OuterBoundaryInterface.BoundaryCycle (canonicalGraph C) where
  length := Rows.length
  length_pos := Rows.length_pos
  vertex := Rows.vertex
  adjacent := Rows.adjacent
  simple := Rows.simple

/-- The face-boundary surface generated by the extracted simple cycle. -/
def toFaceBoundaryHypotheses
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C) :=
  FaceReduction.UnitDistanceFaceBoundaryHypotheses.ofOuterBoundaryCycle
    (canonicalGraph C) Rows.length_pos Rows.vertex Rows.adjacent Rows.simple

@[simp]
theorem toFaceBoundaryHypotheses_boundaryLength
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    Rows.toFaceBoundaryHypotheses.boundaryLength PUnit.unit =
      Rows.length :=
  rfl

@[simp]
theorem toFaceBoundaryHypotheses_boundaryVertex
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    Rows.toFaceBoundaryHypotheses.boundaryVertex PUnit.unit =
      Rows.vertex :=
  rfl

theorem toFaceBoundaryHypotheses_isOuterFace
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    Rows.toFaceBoundaryHypotheses.IsOuterFace PUnit.unit :=
  trivial

theorem toFaceBoundaryHypotheses_boundaryLength_ge_three
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    3 <= Rows.toFaceBoundaryHypotheses.boundaryLength PUnit.unit := by
  simpa using Rows.length_ge_three

/-- The enclosure predicates attached to the exact face-boundary surface. -/
def toOuterEnclosure
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (canonicalGraph C) Rows.toFaceBoundaryHypotheses PUnit.unit where
  insideOrOn := Rows.insideOrOn
  onBoundary := Rows.onBoundary
  boundary_vertex_onBoundary := by
    intro k
    simpa using Rows.boundary_vertex_onBoundary k
  boundary_point_insideOrOn := by
    intro k
    simpa using Rows.boundary_point_insideOrOn k
  all_vertices_insideOrOn := Rows.all_vertices_insideOrOn
  onBoundary_iff_outer_cycle := by
    intro v
    simpa using Rows.onBoundary_iff_outer_cycle v

@[simp]
theorem toOuterEnclosure_insideOrOn
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    Rows.toOuterEnclosure.insideOrOn = Rows.insideOrOn :=
  rfl

@[simp]
theorem toOuterEnclosure_onBoundary
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    Rows.toOuterEnclosure.onBoundary = Rows.onBoundary :=
  rfl

/-- The checked outer-boundary core generated by the simple cycle and its
matching enclosure predicates. -/
def toOuterBoundaryCore
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    OuterBoundaryCore.{0} (canonicalGraph C) where
  faceBoundary := Rows.toFaceBoundaryHypotheses
  outerFace := PUnit.unit
  outerFace_isOuter := Rows.toFaceBoundaryHypotheses_isOuterFace
  outerEnclosure := Rows.toOuterEnclosure

@[simp]
theorem toOuterBoundaryCore_faceBoundary
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    Rows.toOuterBoundaryCore.faceBoundary =
      Rows.toFaceBoundaryHypotheses :=
  rfl

@[simp]
theorem toOuterBoundaryCore_outerFace
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    Rows.toOuterBoundaryCore.outerFace = PUnit.unit :=
  rfl

@[simp]
theorem toOuterBoundaryCore_outerCycle_length
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    Rows.toOuterBoundaryCore.outerCycle.length = Rows.length :=
  rfl

@[simp]
theorem toOuterBoundaryCore_outerCycle_vertex
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    Rows.toOuterBoundaryCore.outerCycle.vertex = Rows.vertex :=
  rfl

/-- The simple cyclic boundary/enclosure rows supply the strong actual
outer-boundary cycle data used by W28/S2. -/
def toActualOuterBoundaryCycleData
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    ActualOuterBoundaryCycleData.{0} C :=
  ActualOuterBoundaryCycleData.ofCore Rows.toOuterBoundaryCore (by
    simpa using Rows.length_ge_three)

/-- Build the simple cyclic row package from already checked actual
outer-boundary-cycle data. -/
def ofActualOuterBoundaryCycleData
    (D : ActualOuterBoundaryCycleData.{0} C) :
    SimpleCyclicOuterBoundaryEnclosureRows C where
  length := D.outerCycle.length
  length_pos := D.outerCycle.length_pos
  vertex := D.outerCycle.vertex
  adjacent := D.outerCycle.adjacent
  simple := D.outerCycle.simple
  length_ge_three := D.outerCycle_length_ge_three
  insideOrOn := D.outerEnclosure.insideOrOn
  onBoundary := D.outerEnclosure.onBoundary
  boundary_vertex_onBoundary := D.boundary_vertex_onBoundary
  boundary_point_insideOrOn := D.boundary_point_insideOrOn
  all_vertices_insideOrOn := D.all_vertices_insideOrOn
  onBoundary_iff_outer_cycle := D.onBoundary_iff_outerCycle

/-- Nonempty simple cyclic boundary/enclosure rows are equivalent to the
strong actual outer-boundary-cycle data. -/
theorem nonempty_iff_actualOuterBoundaryCycleData
    (C : _root_.UDConfig n) :
    Nonempty (SimpleCyclicOuterBoundaryEnclosureRows C) <->
      Nonempty (ActualOuterBoundaryCycleData.{0} C) := by
  constructor
  · rintro ⟨Rows⟩
    exact ⟨Rows.toActualOuterBoundaryCycleData⟩
  · rintro ⟨D⟩
    exact ⟨ofActualOuterBoundaryCycleData D⟩

end SimpleCyclicOuterBoundaryEnclosureRows

/-! ## Canonical graph-cycle boundary and Jordan outer component source -/

/-- The Mathlib unit-distance graph attached to a `UDConfig`. -/
abbrev UnitDistanceSimpleGraph (C : _root_.UDConfig n) :
    SimpleGraph (Fin n) :=
  GraphBridge.unitDistanceSimpleGraph C

/-- A simple cycle in the concrete unit-distance graph of `C`. -/
structure UnitDistanceCycleBoundary (C : _root_.UDConfig n) where
  base : Fin n
  walk : (UnitDistanceSimpleGraph C).Walk base base
  isCycle : walk.IsCycle

namespace UnitDistanceCycleBoundary

variable {C : _root_.UDConfig n}

/-- The length of the extracted unit-distance cycle. -/
def length (B : UnitDistanceCycleBoundary C) : Nat :=
  B.walk.length

/-- The extracted cycle is nonempty. -/
theorem length_pos (B : UnitDistanceCycleBoundary C) : 0 < B.length :=
  Nat.lt_of_lt_of_le (by decide : 0 < 3)
    (SimpleGraph.Walk.IsCycle.three_le_length B.isCycle)

/-- The ambient vertex at a cyclic boundary position. -/
def vertex (B : UnitDistanceCycleBoundary C) (k : Fin B.length) : Fin n :=
  B.walk.getVert k.val

/-- Consecutive vertices in the extracted cycle are adjacent in the canonical
straight-line unit-distance graph. -/
theorem adjacent (B : UnitDistanceCycleBoundary C) (k : Fin B.length) :
    (canonicalGraph C).Adj (B.vertex k)
      (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) := by
  by_cases hk : k.val + 1 < B.walk.length
  · have hsucc_val :
        (PlanarInterface.cyclicSucc B.length_pos k).val = k.val + 1 := by
      simp [PlanarInterface.cyclicSucc, length, Nat.mod_eq_of_lt hk]
    have hadj :
        (UnitDistanceSimpleGraph C).Adj
          (B.walk.getVert k.val) (B.walk.getVert (k.val + 1)) :=
      B.walk.adj_getVert_succ k.isLt
    have hadj_canon :
        (canonicalGraph C).Adj
          (B.walk.getVert k.val) (B.walk.getVert (k.val + 1)) :=
      ((canonicalGraph C).adj_iff_unitDistanceAdj _ _).2
        ((GraphBridge.unitDistanceSimpleGraph_adj C _ _).1 hadj)
    change
      (canonicalGraph C).Adj
        (B.walk.getVert k.val)
        (B.walk.getVert
          (PlanarInterface.cyclicSucc B.length_pos k).val)
    rw [hsucc_val]
    exact hadj_canon
  · have hlast : k.val + 1 = B.walk.length :=
      eq_of_le_of_not_lt (Nat.succ_le_of_lt k.isLt) hk
    have hsucc_val :
        (PlanarInterface.cyclicSucc B.length_pos k).val = 0 := by
      simp [PlanarInterface.cyclicSucc, length, hlast]
    have hadj :
        (UnitDistanceSimpleGraph C).Adj
          (B.walk.getVert k.val) (B.walk.getVert (k.val + 1)) :=
      B.walk.adj_getVert_succ k.isLt
    have hend : B.walk.getVert (k.val + 1) = B.walk.getVert 0 := by
      rw [hlast, SimpleGraph.Walk.getVert_length,
        SimpleGraph.Walk.getVert_zero]
    have hadj_zero :
        (UnitDistanceSimpleGraph C).Adj
          (B.walk.getVert k.val) (B.walk.getVert 0) := by
      simpa [hend] using hadj
    have hadj_canon :
        (canonicalGraph C).Adj
          (B.walk.getVert k.val) (B.walk.getVert 0) :=
      ((canonicalGraph C).adj_iff_unitDistanceAdj _ _).2
        ((GraphBridge.unitDistanceSimpleGraph_adj C _ _).1 hadj_zero)
    change
      (canonicalGraph C).Adj
        (B.walk.getVert k.val)
        (B.walk.getVert
          (PlanarInterface.cyclicSucc B.length_pos k).val)
    rw [hsucc_val]
    exact hadj_canon

/-- The extracted cycle has no repeated boundary vertex. -/
theorem simple (B : UnitDistanceCycleBoundary C) :
    Function.Injective B.vertex := by
  intro a b h
  apply Fin.ext
  exact
    SimpleGraph.Walk.IsCycle.getVert_injOn' B.isCycle
      (Nat.le_sub_one_of_lt a.isLt)
      (Nat.le_sub_one_of_lt b.isLt)
      h

/-- The extracted simple cycle has length at least three. -/
theorem length_ge_three (B : UnitDistanceCycleBoundary C) :
    3 <= B.length :=
  SimpleGraph.Walk.IsCycle.three_le_length B.isCycle

/-- Forget a unit-distance graph-cycle boundary to the outer-boundary-cycle
interface. -/
def toBoundaryCycle (B : UnitDistanceCycleBoundary C) :
    OuterBoundaryInterface.BoundaryCycle (canonicalGraph C) where
  length := B.length
  length_pos := B.length_pos
  vertex := B.vertex
  adjacent := B.adjacent
  simple := B.simple

/-- The canonical unit-distance graph cycle has the repository simple-polygon
noncrossing witness.  This is the geometric input to any future Jordan
outer-component enclosure construction for this same cycle. -/
def toSimplePolygon (B : UnitDistanceCycleBoundary C) :
    OuterBoundaryInterface.SimplePolygon (canonicalGraph C) B.toBoundaryCycle :=
  OuterBoundaryReduction.BoundaryCycle.toSimplePolygon B.toBoundaryCycle

end UnitDistanceCycleBoundary

/-- Enclosure predicates for the specific unit-distance cycle selected by the
outer-component/Jordan step.  This is the genuine missing S2 theorem surface:
the cycle is concrete, while `insideOrOn` and `onBoundary` must be proved for
that same cycle. -/
structure JordanOuterComponentEnclosure
    (C : _root_.UDConfig n) (B : UnitDistanceCycleBoundary C) where
  insideOrOn : PlanarInterface.Point -> Prop
  onBoundary : Fin n -> Prop
  boundary_vertex_onBoundary :
    forall k : Fin B.length, onBoundary (B.vertex k)
  boundary_point_insideOrOn :
    forall k : Fin B.length, insideOrOn ((canonicalGraph C).point (B.vertex k))
  all_vertices_insideOrOn :
    forall v : Fin n, insideOrOn ((canonicalGraph C).point v)
  onBoundary_iff_outer_cycle :
    forall v : Fin n, onBoundary v <->
      Exists fun k : Fin B.length => B.vertex k = v

namespace JordanOuterComponentEnclosure

variable {C : _root_.UDConfig n} {B : UnitDistanceCycleBoundary C}

/-- The canonical graph cycle plus its matching Jordan enclosure gives the
strong simple cyclic boundary/enclosure rows. -/
def toSimpleCyclicOuterBoundaryEnclosureRows
    (E : JordanOuterComponentEnclosure C B) :
    SimpleCyclicOuterBoundaryEnclosureRows C where
  length := B.length
  length_pos := B.length_pos
  vertex := B.vertex
  adjacent := B.adjacent
  simple := B.simple
  length_ge_three := B.length_ge_three
  insideOrOn := E.insideOrOn
  onBoundary := E.onBoundary
  boundary_vertex_onBoundary := E.boundary_vertex_onBoundary
  boundary_point_insideOrOn := E.boundary_point_insideOrOn
  all_vertices_insideOrOn := E.all_vertices_insideOrOn
  onBoundary_iff_outer_cycle := E.onBoundary_iff_outer_cycle

end JordanOuterComponentEnclosure

/-- Positive one-configuration S2 row: choose the unit-distance cycle that is
actually the outer component, then prove the Jordan enclosure predicates for
that same cycle.  This avoids fixing the canonical girth cycle, which may be an
interior cycle in future geometry work. -/
structure ChosenJordanOuterComponentRow (C : _root_.UDConfig n) where
  boundary : UnitDistanceCycleBoundary C
  enclosure : JordanOuterComponentEnclosure C boundary

/-- A concrete outer-component source: a unit-distance simple cycle together
with Jordan enclosure predicates for exactly that cycle. -/
structure JordanOuterComponentSource (C : _root_.UDConfig n) where
  boundary : UnitDistanceCycleBoundary C
  enclosure : JordanOuterComponentEnclosure C boundary

namespace JordanOuterComponentSource

variable {C : _root_.UDConfig n}

/-- Build the source package from an explicitly chosen boundary and its
matching enclosure proof. -/
def ofBoundaryEnclosure
    (B : UnitDistanceCycleBoundary C)
    (E : JordanOuterComponentEnclosure C B) :
    JordanOuterComponentSource C where
  boundary := B
  enclosure := E

/-- Build the source package from the positive chosen-cycle row. -/
def ofChosenRow
    (row : ChosenJordanOuterComponentRow C) :
    JordanOuterComponentSource C :=
  ofBoundaryEnclosure row.boundary row.enclosure

/-- Build the source package from an actual concrete cycle packaged with its
matching Jordan outer-component enclosure. -/
def ofBoundaryEnclosureRow
    (row :
      Sigma fun B : UnitDistanceCycleBoundary C =>
        JordanOuterComponentEnclosure C B) :
    JordanOuterComponentSource C :=
  ofBoundaryEnclosure row.1 row.2

/-- Forget the source package to the chosen-cycle row shape. -/
def toChosenRow
    (J : JordanOuterComponentSource C) :
    ChosenJordanOuterComponentRow C where
  boundary := J.boundary
  enclosure := J.enclosure

/-- A source exists exactly when some unit-distance cycle has a matching real
Jordan enclosure. -/
theorem nonempty_iff_chosenRow :
    Nonempty (JordanOuterComponentSource C) <->
      Nonempty (ChosenJordanOuterComponentRow C) := by
  constructor
  · rintro ⟨J⟩
    exact ⟨J.toChosenRow⟩
  · rintro ⟨row⟩
    exact ⟨ofChosenRow row⟩

/-- The chosen source's boundary as the repository boundary-cycle interface. -/
def toBoundaryCycle
    (J : JordanOuterComponentSource C) :
    OuterBoundaryInterface.BoundaryCycle (canonicalGraph C) :=
  J.boundary.toBoundaryCycle

/-- The chosen source carries the checked simple-polygon witness for that same
cycle. -/
def toSimplePolygon
    (J : JordanOuterComponentSource C) :
    OuterBoundaryInterface.SimplePolygon (canonicalGraph C) J.toBoundaryCycle :=
  J.boundary.toSimplePolygon

/-- Project the outer-component source to the strong S2 simple cyclic rows. -/
def toSimpleCyclicOuterBoundaryEnclosureRows
    (J : JordanOuterComponentSource C) :
    SimpleCyclicOuterBoundaryEnclosureRows C :=
  J.enclosure.toSimpleCyclicOuterBoundaryEnclosureRows

/-- Project the chosen source to the checked outer-boundary core. -/
def toOuterBoundaryCore
    (J : JordanOuterComponentSource C) :
    OuterBoundaryCore.{0} (canonicalGraph C) :=
  J.toSimpleCyclicOuterBoundaryEnclosureRows.toOuterBoundaryCore

/-- Project the chosen source to the strong actual outer-boundary-cycle data. -/
def toActualOuterBoundaryCycleData
    (J : JordanOuterComponentSource C) :
    ActualOuterBoundaryCycleData.{0} C :=
  J.toSimpleCyclicOuterBoundaryEnclosureRows.toActualOuterBoundaryCycleData

/-- The outer-component source supplies strong actual outer-boundary-cycle
data without using the synthetic extracted-cycle enclosure. -/
theorem nonempty_actualOuterBoundaryCycleData
    (J : JordanOuterComponentSource C) :
    Nonempty (ActualOuterBoundaryCycleData.{0} C) :=
  Nonempty.intro J.toActualOuterBoundaryCycleData

/-- A chosen outer-component source supplies the strong simple cyclic rows. -/
theorem nonempty_simpleCyclicOuterBoundaryEnclosureRows
    (J : JordanOuterComponentSource C) :
    Nonempty (SimpleCyclicOuterBoundaryEnclosureRows C) :=
  Nonempty.intro J.toSimpleCyclicOuterBoundaryEnclosureRows

end JordanOuterComponentSource

/-- The Mathlib graph degree agrees with the finite unit-neighbor set used in
the minimal-failure degree arguments. -/
theorem unitDistanceSimpleGraph_degree_eq_neighborSet_card
    (C : _root_.UDConfig n) (v : Fin n) :
    ((UnitDistanceSimpleGraph C).neighborFinset v).card =
      (DegreePipeline.unitDistanceNeighborSet C v).card := by
  classical
  congr 1
  ext w
  rw [SimpleGraph.neighborFinset_def]
  simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet]
  rw [DegreePipeline.mem_unitDistanceNeighborSet C v w]
  constructor
  · intro h
    have hpair :=
      (GraphBridge.unitDistanceSimpleGraph_adj_iff_ne_and_dist C v w).1 h
    exact
      And.intro
        ((bne_iff_ne (a := w) (b := v)).2
          (fun hwv => hpair.1 hwv.symm))
        (by simpa [_root_.eucDist_comm] using hpair.2)
  · intro h
    exact
      (GraphBridge.unitDistanceSimpleGraph_adj C v w).2
        (by simpa [_root_.eucDist_comm] using h.2)

/-- Minimal cleared failures have a cycle in the concrete unit-distance graph. -/
theorem unitDistanceSimpleGraph_not_acyclic_of_minimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Not (UnitDistanceSimpleGraph C).IsAcyclic := by
  classical
  let G : SimpleGraph (Fin n) := UnitDistanceSimpleGraph C
  rcases MinimalConnectednessClosure.fin_nonempty_of_minimalClearedFailure
      (C := C) hmin with ⟨v0⟩
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le v0.val) v0.isLt
  haveI : Nonempty (Fin n) := Nonempty.intro v0
  have hdegree_two : forall v : Fin n, 2 <= G.degree v := by
    intro v
    have hthree :
        3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
      CutVertexFinal.minimumDegree_of_minimalFailure hmin v
    have hdeg_card :
        (G.neighborFinset v).card =
          (DegreePipeline.unitDistanceNeighborSet C v).card := by
      congr 1
      ext w
      rw [SimpleGraph.neighborFinset_def]
      simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet]
      rw [DegreePipeline.mem_unitDistanceNeighborSet C v w]
      constructor
      · intro h
        have hunit : (UnitDistanceSimpleGraph C).Adj v w := by
          simpa [G] using h
        have hpair :=
          (GraphBridge.unitDistanceSimpleGraph_adj_iff_ne_and_dist C v w).1
            hunit
        exact
          And.intro
            ((bne_iff_ne (a := w) (b := v)).2
              (fun hwv => hpair.1 hwv.symm))
            (by simpa [_root_.eucDist_comm] using hpair.2)
      · intro h
        have hunit : (UnitDistanceSimpleGraph C).Adj v w :=
          (GraphBridge.unitDistanceSimpleGraph_adj C v w).2
            (by simpa [_root_.eucDist_comm] using h.2)
        simpa [G] using hunit
    have hcard_bound : 2 <= (G.neighborFinset v).card := by
      rw [hdeg_card]
      exact Nat.le_trans (by decide : 2 <= 3) hthree
    have hdeg_eq :
        (G.neighborFinset v).card = G.degree v :=
      SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := v)
    exact hdeg_eq ▸ hcard_bound
  have hminDegree_two : 2 <= G.minDegree :=
    SimpleGraph.le_minDegree_of_forall_le_degree (G := G) 2 hdegree_two
  have hcard_gt_one : 1 < Fintype.card (Fin n) := by
    let v : Fin n := v0
    have hvdeg : 2 <= G.degree v := hdegree_two v
    have hvlt : G.degree v < Fintype.card (Fin n) :=
      SimpleGraph.degree_lt_card_verts (G := G) v
    exact Nat.lt_trans (by decide : 1 < 2) (Nat.lt_of_le_of_lt hvdeg hvlt)
  haveI : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp hcard_gt_one
  intro hacyclic
  have hconnected : G.Connected := by
    simpa [G] using
      CutVertexFinal.connected_of_minimalFailure
        (C := C) hn hmin
  have htree : G.IsTree := ⟨hconnected, hacyclic⟩
  have hminDegree_one : G.minDegree = 1 :=
    SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial
      (G := G) htree
  rw [hminDegree_one] at hminDegree_two
  exact Nat.not_succ_le_self 1 hminDegree_two

/-- The canonical simple-cycle boundary extracted from a minimal cleared
failure's unit-distance graph.  This is only the graph-cycle half of S2; the
Jordan outer-component enclosure is the separate `JordanOuterComponentEnclosure`
obligation for this boundary. -/
noncomputable def unitDistanceCycleBoundaryOfMinimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    UnitDistanceCycleBoundary C := by
  classical
  let G : SimpleGraph (Fin n) := UnitDistanceSimpleGraph C
  have hnotAcyclic :
      Not G.IsAcyclic := by
    simpa [G] using
      unitDistanceSimpleGraph_not_acyclic_of_minimalClearedFailure
        (C := C) hmin
  let hexists := (SimpleGraph.exists_girth_eq_length (G := G)).2 hnotAcyclic
  let base : Fin n := Classical.choose hexists
  let hwalkExists := Classical.choose_spec hexists
  let walk : G.Walk base base := Classical.choose hwalkExists
  have hcycle : walk.IsCycle := (Classical.choose_spec hwalkExists).1
  exact
    { base := base
      walk := walk
      isCycle := hcycle }

/-- Minimal failures always supply the graph-cycle boundary part of the
outer-component theorem. -/
theorem nonempty_unitDistanceCycleBoundary_of_minimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (UnitDistanceCycleBoundary C) :=
  Nonempty.intro
    (unitDistanceCycleBoundaryOfMinimalClearedFailure (C := C) hmin)

/-- Precise S2 Jordan theorem surface for minimal failures: prove enclosure
predicates for the canonical simple cycle extracted from the unit-distance
graph. -/
abbrev MinimalFailureCanonicalJordanOuterComponentRows :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      JordanOuterComponentEnclosure C
        (unitDistanceCycleBoundaryOfMinimalClearedFailure (C := C) hmin)

/-- A row family of full outer-component sources over minimal failures. -/
abbrev MinimalFailureJordanOuterComponentSourceRows :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      JordanOuterComponentSource C

/-- Positive minimal-failure row family where the Jordan step may choose the
outer-component cycle for each configuration instead of proving enclosure for
the canonical girth cycle. -/
abbrev MinimalFailureChosenJordanOuterComponentRows :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      ChosenJordanOuterComponentRow C

/-- A concrete boundary cycle plus matching Jordan enclosure is already a
chosen outer-component row. -/
def chosenJordanOuterComponentRowOfBoundaryEnclosure
    {C : _root_.UDConfig n}
    (B : UnitDistanceCycleBoundary C)
    (E : JordanOuterComponentEnclosure C B) :
    ChosenJordanOuterComponentRow C where
  boundary := B
  enclosure := E

/-- A full Jordan outer-component source immediately gives the flexible
chosen-row surface consumed by the downstream S2 adapters. -/
def chosenJordanOuterComponentRowOfJordanOuterComponentSource
    {C : _root_.UDConfig n}
    (J : JordanOuterComponentSource C) :
    ChosenJordanOuterComponentRow C :=
  J.toChosenRow

/-- Nonempty form of the source-to-chosen constructor. -/
theorem nonempty_chosenJordanOuterComponentRow_of_jordanOuterComponentSource
    {C : _root_.UDConfig n}
    (J : JordanOuterComponentSource C) :
    Nonempty (ChosenJordanOuterComponentRow C) :=
  Nonempty.intro
    (chosenJordanOuterComponentRowOfJordanOuterComponentSource J)

/-- Per-configuration minimal-failure constructor: once the canonical
minimal-failure cycle has its matching Jordan enclosure, it is a chosen
outer-component row. -/
noncomputable def chosenJordanOuterComponentRow_of_minimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (E :
      JordanOuterComponentEnclosure C
        (unitDistanceCycleBoundaryOfMinimalClearedFailure (C := C) hmin)) :
    ChosenJordanOuterComponentRow C :=
  chosenJordanOuterComponentRowOfBoundaryEnclosure
    (unitDistanceCycleBoundaryOfMinimalClearedFailure (C := C) hmin) E

/-- Source-row families also supply the chosen-row family, without fixing the
canonical girth cycle as the outer cycle. -/
def minimalFailureChosenJordanOuterComponentRowsOfSourceRows
    (rows : MinimalFailureJordanOuterComponentSourceRows) :
    MinimalFailureChosenJordanOuterComponentRows :=
  fun {n} C hmin =>
    chosenJordanOuterComponentRowOfJordanOuterComponentSource
      (rows (n := n) C hmin)

/-- Nonempty form of the source-row to chosen-row constructor. -/
theorem nonempty_minimalFailureChosenJordanOuterComponentRows_of_sourceRows
    (rows : MinimalFailureJordanOuterComponentSourceRows) :
    Nonempty MinimalFailureChosenJordanOuterComponentRows :=
  Nonempty.intro
    (minimalFailureChosenJordanOuterComponentRowsOfSourceRows rows)

/-- The canonical enclosure theorem is a sufficient special case of the
flexible chosen-row family. -/
noncomputable def minimalFailureChosenJordanOuterComponentRowsOfCanonical
    (rows : MinimalFailureCanonicalJordanOuterComponentRows) :
    MinimalFailureChosenJordanOuterComponentRows :=
  fun {n} C hmin =>
    chosenJordanOuterComponentRow_of_minimalClearedFailure
      (C := C) hmin (rows (n := n) C hmin)

/-- Nonempty form of the canonical-enclosure to chosen-row constructor. -/
theorem nonempty_minimalFailureChosenJordanOuterComponentRows_of_canonicalRows
    (rows : MinimalFailureCanonicalJordanOuterComponentRows) :
    Nonempty MinimalFailureChosenJordanOuterComponentRows :=
  Nonempty.intro
    (minimalFailureChosenJordanOuterComponentRowsOfCanonical rows)

/-- Chosen-cycle rows supply full outer-component source rows. -/
def minimalFailureJordanOuterComponentSourceRowsOfChosen
    (rows : MinimalFailureChosenJordanOuterComponentRows) :
    MinimalFailureJordanOuterComponentSourceRows :=
  fun {n} C hmin =>
    JordanOuterComponentSource.ofChosenRow (rows (n := n) C hmin)

/-- Actual concrete cycle/enclosure rows over minimal failures supply full
outer-component source rows.  This is the positive S2 row shape available in
this file: the selected cycle is a real `UnitDistanceCycleBoundary`, and the
enclosure is proved for that same boundary. -/
def minimalFailureJordanOuterComponentSourceRowsOfBoundaryEnclosureRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          Sigma fun B : UnitDistanceCycleBoundary C =>
            JordanOuterComponentEnclosure C B) :
    MinimalFailureJordanOuterComponentSourceRows :=
  fun {n} C hmin =>
    JordanOuterComponentSource.ofBoundaryEnclosureRow
      (rows (n := n) C hmin)

/-- Actual concrete cycle/enclosure rows over minimal failures also supply the
flexible chosen-cycle row family consumed by the strong S2 route. -/
def minimalFailureChosenJordanOuterComponentRowsOfBoundaryEnclosureRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          Sigma fun B : UnitDistanceCycleBoundary C =>
            JordanOuterComponentEnclosure C B) :
    MinimalFailureChosenJordanOuterComponentRows :=
  minimalFailureChosenJordanOuterComponentRowsOfSourceRows
    (minimalFailureJordanOuterComponentSourceRowsOfBoundaryEnclosureRows rows)

/-- The canonical Jordan outer-component theorem supplies full
outer-component sources by pairing each proved enclosure with the canonical
cycle selected from minimality. -/
noncomputable def minimalFailureJordanOuterComponentSourceRowsOfCanonical
    (rows : MinimalFailureCanonicalJordanOuterComponentRows) :
    MinimalFailureJordanOuterComponentSourceRows :=
  fun {n} C hmin =>
    { boundary := unitDistanceCycleBoundaryOfMinimalClearedFailure (C := C) hmin
      enclosure := rows (n := n) C hmin }

/-- Full outer-component source rows project to the strong simple cyclic
boundary/enclosure rows used by S2. -/
def simpleCyclicOuterBoundaryEnclosureRowsOfJordanOuterComponentSourceRows
    (rows : MinimalFailureJordanOuterComponentSourceRows) :
    forall {n : Nat} (C : _root_.UDConfig n),
      MinimalGraphFacts.IsMinimalClearedFailure C ->
        SimpleCyclicOuterBoundaryEnclosureRows C :=
  fun {n} C hmin =>
    (rows (n := n) C hmin).toSimpleCyclicOuterBoundaryEnclosureRows

/-- Chosen-cycle rows project to the strong simple cyclic boundary/enclosure
rows used by S2. -/
def simpleCyclicOuterBoundaryEnclosureRowsOfChosenJordanOuterComponentRows
    (rows : MinimalFailureChosenJordanOuterComponentRows) :
    forall {n : Nat} (C : _root_.UDConfig n),
      MinimalGraphFacts.IsMinimalClearedFailure C ->
        SimpleCyclicOuterBoundaryEnclosureRows C :=
  simpleCyclicOuterBoundaryEnclosureRowsOfJordanOuterComponentSourceRows
    (minimalFailureJordanOuterComponentSourceRowsOfChosen rows)

/-- Full outer-component source rows project to the strong actual
outer-boundary-cycle rows used by the exact S2 target. -/
def actualOuterBoundaryCycleDataRowsOfJordanOuterComponentSourceRows
    (rows : MinimalFailureJordanOuterComponentSourceRows) :
    forall {n : Nat} (C : _root_.UDConfig n),
      MinimalGraphFacts.IsMinimalClearedFailure C ->
        ActualOuterBoundaryCycleData.{0} C :=
  fun {n} C hmin =>
    (rows (n := n) C hmin).toActualOuterBoundaryCycleData

/-- Chosen-cycle rows project all the way to the strong actual
outer-boundary-cycle rows. -/
def actualOuterBoundaryCycleDataRowsOfChosenJordanOuterComponentRows
    (rows : MinimalFailureChosenJordanOuterComponentRows) :
    forall {n : Nat} (C : _root_.UDConfig n),
      MinimalGraphFacts.IsMinimalClearedFailure C ->
        ActualOuterBoundaryCycleData.{0} C :=
  actualOuterBoundaryCycleDataRowsOfJordanOuterComponentSourceRows
    (minimalFailureJordanOuterComponentSourceRowsOfChosen rows)

/-! The older adjacent-pair selected-face witness remains below; it is not the
nondegenerate Jordan outer-component route above. -/

namespace MissingOuterFaceData

variable {C : _root_.UDConfig n}

/-- Minimal cleared failures have at least one real unit-distance edge. -/
theorem exists_unitDistanceAdj_of_minimalClearedFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Exists fun i : Fin n =>
      Exists fun j : Fin n => GraphBridge.UnitDistanceAdj C i j := by
  rcases MinimalConnectednessClosure.fin_nonempty_of_minimalClearedFailure
      (C := C) hmin with ⟨v⟩
  have hdeg :
      3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
    CutVertexFinal.minimumDegree_of_minimalFailure hmin v
  have hpos : 0 < (DegreePipeline.unitDistanceNeighborSet C v).card := by
    exact Nat.lt_of_lt_of_le (by norm_num) hdeg
  rcases Finset.card_pos.mp hpos with ⟨j, hj⟩
  have hj' := (DegreePipeline.mem_unitDistanceNeighborSet C v j).1 hj
  exact ⟨j, v, hj'.2⟩

/-- Minimal cleared failures supply the selected outer-face payload requested
by the current formal interface. -/
theorem nonempty_of_minimalClearedFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (MissingOuterFaceData C) := by
  rcases exists_unitDistanceAdj_of_minimalClearedFailure
      (C := C) hmin with ⟨i, j, hAdj⟩
  exact ⟨ofUnitDistanceAdj (C := C) hAdj⟩

end MissingOuterFaceData

/-- The unqualified global selected-face payload is too strong for the current
interface: the empty configuration has no unit edge, while any selected-face
payload contains a boundary unit edge. -/
theorem not_forall_missingOuterFaceData :
    Not
      (forall {n : Nat} (C : _root_.UDConfig n),
        Nonempty (MissingOuterFaceData.{0} C)) := by
  intro h
  let C0 : _root_.UDConfig 0 := {
    pts := fun i => Fin.elim0 i
    sep := by
      intro i
      exact Fin.elim0 i }
  rcases h C0 with ⟨D⟩
  rcases D.exists_unitDistanceAdj with ⟨i, _j, _hAdj⟩
  exact Fin.elim0 i

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

/-! ## Strong actual-cycle projections -/

/-- Strengthen full topology facts to the actual nondegenerate cycle payload
once the selected outer cycle is known to have length at least three. -/
def toActualOuterBoundaryCycleData
    (T : MissingTopologyFacts.{u} C)
    (hcycle : 3 <= T.outerCycle.length) :
    ActualOuterBoundaryCycleData.{u} C :=
  ActualOuterBoundaryCycleData.ofCore T.toCore (by simpa [outerCycle] using hcycle)

@[simp]
theorem toActualOuterBoundaryCycleData_core
    (T : MissingTopologyFacts.{u} C)
    (hcycle : 3 <= T.outerCycle.length) :
    (T.toActualOuterBoundaryCycleData hcycle).core = T.toCore :=
  rfl

@[simp]
theorem toActualOuterBoundaryCycleData_outerCycle
    (T : MissingTopologyFacts.{u} C)
    (hcycle : 3 <= T.outerCycle.length) :
    (T.toActualOuterBoundaryCycleData hcycle).outerCycle = T.outerCycle :=
  rfl

theorem nonempty_actualOuterBoundaryCycleData_of_length_ge_three
    (T : MissingTopologyFacts.{u} C)
    (hcycle : 3 <= T.outerCycle.length) :
    Nonempty (ActualOuterBoundaryCycleData.{u} C) :=
  ⟨T.toActualOuterBoundaryCycleData hcycle⟩

end MissingTopologyFacts

namespace ActualOuterBoundaryCycleData

variable {C : _root_.UDConfig n}

/-- Forget only the nondegenerate-cycle proof, retaining the full topology
facts and enclosure predicates. -/
def toMissingTopologyFacts
    (D : ActualOuterBoundaryCycleData.{u} C) :
    MissingTopologyFacts.{u} C :=
  MissingTopologyFacts.ofCore D.core

@[simp]
theorem toMissingTopologyFacts_toCore
    (D : ActualOuterBoundaryCycleData.{u} C) :
    D.toMissingTopologyFacts.toCore = D.core :=
  rfl

@[simp]
theorem toMissingTopologyFacts_outerCycle
    (D : ActualOuterBoundaryCycleData.{u} C) :
    D.toMissingTopologyFacts.outerCycle = D.outerCycle :=
  rfl

theorem toMissingTopologyFacts_three_le_outerCycle_length
    (D : ActualOuterBoundaryCycleData.{u} C) :
    3 <= D.toMissingTopologyFacts.outerCycle.length := by
  simpa using D.three_le_outerCycle_length

end ActualOuterBoundaryCycleData

namespace JordanOuterComponentSource

variable {C : _root_.UDConfig n}

/-- Forget only the nondegenerate-cycle proof from a chosen outer-component
source, retaining the full concrete topology/enclosure package. -/
def toMissingTopologyFacts
    (J : JordanOuterComponentSource C) :
    MissingTopologyFacts.{0} C :=
  J.toActualOuterBoundaryCycleData.toMissingTopologyFacts

@[simp]
theorem toMissingTopologyFacts_outerCycle
    (J : JordanOuterComponentSource C) :
    J.toMissingTopologyFacts.outerCycle =
      J.toActualOuterBoundaryCycleData.outerCycle :=
  rfl

/-- The chosen source's forgotten topology still remembers that the selected
cycle is nondegenerate. -/
theorem toMissingTopologyFacts_three_le_outerCycle_length
    (J : JordanOuterComponentSource C) :
    3 <= J.toMissingTopologyFacts.outerCycle.length := by
  simpa using
    J.toActualOuterBoundaryCycleData.toMissingTopologyFacts_three_le_outerCycle_length

/-- A chosen outer-component source supplies the older full topology package. -/
theorem nonempty_missingTopologyFacts
    (J : JordanOuterComponentSource C) :
    Nonempty (MissingTopologyFacts.{0} C) :=
  ⟨J.toMissingTopologyFacts⟩

end JordanOuterComponentSource

namespace MissingTopologyFacts

variable {C : _root_.UDConfig n}

/-- Full topology plus a nondegenerate selected-cycle length proof is exactly
the strong actual outer-boundary cycle payload. -/
theorem nonempty_actualOuterBoundaryCycleData_iff_exists_missingTopologyFacts
    (C : _root_.UDConfig n) :
    Nonempty (ActualOuterBoundaryCycleData.{u} C) <->
      Exists fun T : MissingTopologyFacts.{u} C =>
        3 <= T.outerCycle.length := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.toMissingTopologyFacts, D.toMissingTopologyFacts_three_le_outerCycle_length⟩
  · rintro ⟨T, hcycle⟩
    exact ⟨T.toActualOuterBoundaryCycleData hcycle⟩

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

/-- Strong remaining topology target: construct actual outer-boundary data
whose selected cycle is nondegenerate. -/
def RemainingActualOuterBoundaryCycleTheorem
    (C : _root_.UDConfig n) : Prop :=
  Nonempty (ActualOuterBoundaryCycleData.{0} C)

/-- Simple cyclic boundary/enclosure rows close the strong remaining
actual-cycle target. -/
theorem remainingActualOuterBoundaryCycleTheorem_of_simpleCyclicOuterBoundaryEnclosureRows
    {C : _root_.UDConfig n}
    (Rows : SimpleCyclicOuterBoundaryEnclosureRows C) :
    RemainingActualOuterBoundaryCycleTheorem C :=
  Nonempty.intro Rows.toActualOuterBoundaryCycleData

/-- A chosen outer-component source closes the strong remaining actual-cycle
target by projecting through the simple cyclic boundary/enclosure rows. -/
theorem remainingActualOuterBoundaryCycleTheorem_of_jordanOuterComponentSource
    {C : _root_.UDConfig n}
    (J : JordanOuterComponentSource C) :
    RemainingActualOuterBoundaryCycleTheorem C :=
  Nonempty.intro J.toActualOuterBoundaryCycleData

/-- A positive chosen-cycle row closes the strong remaining actual-cycle target
without fixing the canonical girth cycle. -/
theorem remainingActualOuterBoundaryCycleTheorem_of_chosenJordanOuterComponentRow
    {C : _root_.UDConfig n}
    (row : ChosenJordanOuterComponentRow C) :
    RemainingActualOuterBoundaryCycleTheorem C :=
  remainingActualOuterBoundaryCycleTheorem_of_jordanOuterComponentSource
    (JordanOuterComponentSource.ofChosenRow row)

/-- The strong remaining target is exactly a checked core with a
nondegenerate selected outer cycle. -/
theorem remainingActualOuterBoundaryCycleTheorem_iff_outerBoundaryCore_with_length_ge_three
    (C : _root_.UDConfig n) :
    RemainingActualOuterBoundaryCycleTheorem C <->
      Exists fun P : OuterBoundaryCore.{0} (canonicalGraph C) =>
        3 <= P.outerCycle.length :=
  ActualOuterBoundaryCycleData.nonempty_iff_outerBoundaryCore_with_length_ge_three
    (C := C)

/-- The strong remaining target is equivalently full topology facts plus the
nondegenerate selected-cycle length proof. -/
theorem remainingActualOuterBoundaryCycleTheorem_iff_missingTopologyFacts_with_length_ge_three
    (C : _root_.UDConfig n) :
    RemainingActualOuterBoundaryCycleTheorem C <->
      Exists fun T : MissingTopologyFacts.{0} C =>
        3 <= T.outerCycle.length :=
  MissingTopologyFacts.nonempty_actualOuterBoundaryCycleData_iff_exists_missingTopologyFacts
    (C := C)

/-- Strong actual boundary-cycle data still supplies the older topology target
by forgetting only the nondegenerate length proof. -/
theorem remainingTopologyTheorem_of_remainingActualOuterBoundaryCycleTheorem
    {C : _root_.UDConfig n}
    (h : RemainingActualOuterBoundaryCycleTheorem C) :
    RemainingTopologyTheorem C := by
  rcases h with ⟨D⟩
  exact ⟨D.toMissingTopologyFacts⟩

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
