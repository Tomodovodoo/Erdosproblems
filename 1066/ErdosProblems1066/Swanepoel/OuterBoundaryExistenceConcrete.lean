import ErdosProblems1066.Swanepoel.GraphBridge
import ErdosProblems1066.Swanepoel.NoncrossingUnitEdges
import ErdosProblems1066.Swanepoel.FaceReduction
import ErdosProblems1066.Swanepoel.JordanBoundaryConcrete
import ErdosProblems1066.Swanepoel.OuterBoundaryCoreConstruction

set_option autoImplicit false

/-!
# Concrete outer-boundary existence bridge

This file records the checked part of the route from a concrete `UDConfig` to
the outer-boundary core construction target.

The graph-level input is fully concrete: the canonical graph is the
unit-distance graph of the configuration, its edges are the `GraphBridge`
finite unit-edge set, and noncrossing follows from the separated-unit-edge
obstruction.  The remaining field is therefore exactly the topology/core data:
face-boundary data, a chosen outer face, and enclosure predicates for that face.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryExistenceConcrete

open FaceReduction
open JordanBoundaryConcrete
open OuterBoundaryCoreConstruction
open OuterBoundaryInterface

noncomputable section

variable {n : Nat}

/-! ## Concrete canonical graph facts -/

/-- The canonical graph used by the outer-boundary construction target. -/
abbrev canonicalGraph (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n :=
  OuterBoundaryCoreConstruction.canonicalGraph C

/-- The canonical graph stores exactly the `GraphBridge` unit-distance edges. -/
theorem canonicalGraph_edgeSet_eq_unitDistanceEdges
    (C : _root_.UDConfig n) :
    (canonicalGraph C).edgeSet = GraphBridge.unitDistanceEdges C :=
  rfl

/-- Membership in the canonical edge set is membership in the concrete
unit-distance edge set. -/
theorem mem_canonicalGraph_edgeSet_iff_unitDistanceEdges
    (C : _root_.UDConfig n) (e : PlanarInterface.Edge n) :
    e ∈ (canonicalGraph C).edgeSet <->
      e ∈ GraphBridge.unitDistanceEdges C := by
  rw [canonicalGraph_edgeSet_eq_unitDistanceEdges]

/-- Canonical edges are ordered in the concrete finite edge set. -/
theorem canonicalGraph_edge_ordered
    (C : _root_.UDConfig n) {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet) :
    e.1 < e.2 := by
  exact GraphBridge.unitDistanceEdges_ordered C
    ((mem_canonicalGraph_edgeSet_iff_unitDistanceEdges C e).1 he)

/-- Canonical edges are concrete unit-distance adjacencies. -/
theorem canonicalGraph_edge_unitDistanceAdj
    (C : _root_.UDConfig n) {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet) :
    GraphBridge.UnitDistanceAdj C e.1 e.2 := by
  exact PlanarInterface.mem_unitDistanceEdges_unitDistanceAdj C
    ((mem_canonicalGraph_edgeSet_iff_unitDistanceEdges C e).1 he)

/-- Canonical edges have Euclidean length one. -/
theorem canonicalGraph_edge_dist_eq_one
    (C : _root_.UDConfig n) {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet) :
    Geometry.Distance.eucDist (C.pts e.1) (C.pts e.2) = 1 := by
  exact PlanarInterface.mem_unitDistanceEdges_endpoints_geometry_dist_eq_one C
    ((mem_canonicalGraph_edgeSet_iff_unitDistanceEdges C e).1 he)

/-- The analytic noncrossing bridge for the concrete unit-distance edge set. -/
theorem unitDistanceEdges_not_cross
    (C : _root_.UDConfig n) {e f : PlanarInterface.Edge n}
    (hdisj : PlanarInterface.EdgeVertexDisjoint e f)
    (he : e ∈ GraphBridge.unitDistanceEdges C)
    (hf : f ∈ GraphBridge.unitDistanceEdges C) :
    Not (PlanarInterface.EdgeSegmentsCross C e f) :=
  NoncrossingUnitEdges.unitDistanceEdges_not_cross C hdisj he hf

/-- The canonical graph has pairwise noncrossing edges, with no topology input. -/
theorem canonicalGraph_pairwiseNoncrossing (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  OuterBoundaryCoreConstruction.canonicalGraph_pairwiseNoncrossing C

/-- Concrete pairwise noncrossing for `GraphBridge.unitDistanceEdges`. -/
theorem unitDistanceEdges_pairwiseNoncrossing
    (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      C (GraphBridge.unitDistanceEdges C) :=
  FaceReduction.unitDistanceEdges_pairwiseNoncrossing C

/-- A compact record of the graph-level facts already proved from `UDConfig`. -/
structure ConcreteGraphFacts (C : _root_.UDConfig n) : Prop where
  edgeSet_eq_unitDistanceEdges :
    (canonicalGraph C).edgeSet = GraphBridge.unitDistanceEdges C
  pairwiseNoncrossing :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet

/-- The concrete graph facts are available for every `UDConfig`. -/
theorem concreteGraphFacts (C : _root_.UDConfig n) :
    ConcreteGraphFacts C where
  edgeSet_eq_unitDistanceEdges := canonicalGraph_edgeSet_eq_unitDistanceEdges C
  pairwiseNoncrossing := canonicalGraph_pairwiseNoncrossing C

/-! ## The exact remaining topology/core field -/

/-- The raw dependent topology field still needed for the canonical graph. -/
def ExactTopologyFields (C : _root_.UDConfig n) : Prop :=
  Exists fun H : UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C) =>
    Exists fun F : H.Face =>
      H.IsOuterFace F /\
        Nonempty (OuterBoundaryEnclosure (canonicalGraph C) H F)

/--
The extracted simple cyclic outer-boundary row for the canonical
unit-distance graph.

These are exactly the fields consumed by
`FaceReduction.UnitDistanceFaceBoundaryHypotheses.ofOuterBoundaryCycle`,
together with the nondegenerate length lower bound needed by the actual
outer-boundary-cycle route.
-/
structure ExtractedSimpleCyclicOuterBoundaryRow
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

namespace ExtractedSimpleCyclicOuterBoundaryRow

variable {C : _root_.UDConfig n}

/-- Repackage the extracted row as the existing explicit boundary-cycle type. -/
def toBoundaryCycle
    (R : ExtractedSimpleCyclicOuterBoundaryRow C) :
    OuterBoundaryInterface.BoundaryCycle (canonicalGraph C) where
  length := R.length
  length_pos := R.length_pos
  vertex := R.vertex
  adjacent := R.adjacent
  simple := R.simple

/-- Build the extracted row from an already exposed boundary cycle. -/
def ofBoundaryCycle
    (B : OuterBoundaryInterface.BoundaryCycle (canonicalGraph C))
    (hlen : 3 <= B.length) :
    ExtractedSimpleCyclicOuterBoundaryRow C where
  length := B.length
  length_pos := B.length_pos
  vertex := B.vertex
  adjacent := B.adjacent
  simple := B.simple
  length_ge_three := hlen

/-- The exact face-boundary row consumed downstream by `FaceReduction`. -/
def toFaceBoundaryHypotheses
    (R : ExtractedSimpleCyclicOuterBoundaryRow C) :
    UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C) :=
  UnitDistanceFaceBoundaryHypotheses.ofOuterBoundaryCycle
    (canonicalGraph C) R.length_pos R.vertex R.adjacent R.simple

/-- Mencius's bridge, specialized to the extracted S2 boundary row: it gives
the selected face-boundary surface, outer face, outer-face proof, and
nondegenerate boundary length before enclosure is attached. -/
theorem exists_outerFace_length_ge_three
    (R : ExtractedSimpleCyclicOuterBoundaryRow C) :
    Exists fun H : UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C) =>
      Exists fun F : H.Face =>
        H.IsOuterFace F /\ 3 <= H.boundaryLength F :=
  UnitDistanceFaceBoundaryHypotheses.exists_outerFace_length_ge_three_ofOuterBoundaryCycle
    (canonicalGraph C) R.length_pos R.vertex R.adjacent R.simple
    R.length_ge_three

@[simp]
theorem toFaceBoundaryHypotheses_boundaryLength
    (R : ExtractedSimpleCyclicOuterBoundaryRow C) :
    R.toFaceBoundaryHypotheses.boundaryLength PUnit.unit = R.length :=
  rfl

@[simp]
theorem toFaceBoundaryHypotheses_boundaryVertex
    (R : ExtractedSimpleCyclicOuterBoundaryRow C) :
    R.toFaceBoundaryHypotheses.boundaryVertex PUnit.unit = R.vertex :=
  rfl

theorem toFaceBoundaryHypotheses_isOuterFace
    (R : ExtractedSimpleCyclicOuterBoundaryRow C) :
    R.toFaceBoundaryHypotheses.IsOuterFace PUnit.unit :=
  trivial

theorem toFaceBoundaryHypotheses_boundaryLength_ge_three
    (R : ExtractedSimpleCyclicOuterBoundaryRow C) :
    3 <= R.toFaceBoundaryHypotheses.boundaryLength PUnit.unit := by
  simpa using R.length_ge_three

@[simp]
theorem toBoundaryCycle_length
    (R : ExtractedSimpleCyclicOuterBoundaryRow C) :
    R.toBoundaryCycle.length = R.length :=
  rfl

@[simp]
theorem toBoundaryCycle_vertex
    (R : ExtractedSimpleCyclicOuterBoundaryRow C) :
    R.toBoundaryCycle.vertex = R.vertex :=
  rfl

@[simp]
theorem ofBoundaryCycle_toBoundaryCycle
    (R : ExtractedSimpleCyclicOuterBoundaryRow C) :
    ofBoundaryCycle R.toBoundaryCycle R.length_ge_three = R := by
  cases R
  rfl

end ExtractedSimpleCyclicOuterBoundaryRow

/-- The nondegenerate exact topology field needed by the actual
outer-boundary-cycle route.  Compared with `ExactTopologyFields`, this keeps
the same dependent face/enclosure data and adds the boundary-length lower
bound that rules out the adjacent-pair weak witness. -/
def ExactActualTopologyFields (C : _root_.UDConfig n) : Prop :=
  Exists fun H : UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C) =>
    Exists fun F : H.Face =>
      H.IsOuterFace F /\
        3 <= H.boundaryLength F /\
          Nonempty (OuterBoundaryEnclosure (canonicalGraph C) H F)

/-- Direct constructor for the nondegenerate exact topology field. -/
theorem exactActualTopologyFields_of_faceBoundaryFields
    {C : _root_.UDConfig n}
    {H : UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C)}
    {F : H.Face}
    (hF : H.IsOuterFace F)
    (hlen : 3 <= H.boundaryLength F)
    (hE : Nonempty (OuterBoundaryEnclosure (canonicalGraph C) H F)) :
    ExactActualTopologyFields C := by
  exact ⟨H, F, hF, hlen, hE⟩

/-- A checked outer-boundary core with a nondegenerate selected boundary cycle
directly supplies the exact actual topology field.  The enclosure predicates
come from the same core as the selected face and length row. -/
theorem exactActualTopologyFields_of_outerBoundaryCoreWithLength
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (canonicalGraph C))
    (hlen : 3 <= P.outerCycle.length) :
    ExactActualTopologyFields C := by
  exact
    exactActualTopologyFields_of_faceBoundaryFields
      (C := C) (H := P.faceBoundary) (F := P.outerFace)
      P.outerFace_isOuter
      (by
        change 3 <= P.outerCycle.length
        exact hlen)
      (Nonempty.intro P.outerEnclosure)

/-- Strong actual outer-boundary-cycle data is already an exact actual
topology field, without passing through the extracted graph-cycle shim. -/
theorem exactActualTopologyFields_of_actualOuterBoundaryCycleData
    {C : _root_.UDConfig n}
    (D : JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) :
    ExactActualTopologyFields C :=
  exactActualTopologyFields_of_outerBoundaryCoreWithLength
    (C := C) D.core D.outerCycle_length_ge_three

/-- Nonempty actual outer-boundary-cycle data directly supplies the exact
actual topology field.  The selected face and enclosure are read from the
actual-cycle core itself. -/
theorem exactActualTopologyFields_of_nonempty_actualOuterBoundaryCycleData
    {C : _root_.UDConfig n}
    (hD : Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C)) :
    ExactActualTopologyFields C := by
  rcases hD with ⟨D⟩
  exact exactActualTopologyFields_of_actualOuterBoundaryCycleData (C := C) D

/-- A real core plus its nondegenerate boundary length directly gives the
strong remaining actual-cycle target.  This keeps the core's own enclosure
field rather than manufacturing an extracted-cycle enclosure. -/
theorem remainingActualOuterBoundaryCycleTheorem_of_outerBoundaryCoreWithLength
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (canonicalGraph C))
    (hlen : 3 <= P.outerCycle.length) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
      C := by
  exact
    Nonempty.intro
      (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.ofCore P hlen)

/-- Actual outer-boundary-cycle data itself closes the strong remaining
actual-cycle target. -/
theorem remainingActualOuterBoundaryCycleTheorem_of_actualOuterBoundaryCycleData
    {C : _root_.UDConfig n}
    (D : JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
      C :=
  Nonempty.intro D

/-- The concrete simple-cycle plus matching enclosure row surface feeds exact
actual topology fields through its real actual-cycle data projection. -/
theorem exactActualTopologyFields_of_simpleCyclicOuterBoundaryEnclosureRows
    {C : _root_.UDConfig n}
    (Rows : JordanBoundaryConcrete.SimpleCyclicOuterBoundaryEnclosureRows C) :
    ExactActualTopologyFields C :=
  exactActualTopologyFields_of_actualOuterBoundaryCycleData
    (C := C) Rows.toActualOuterBoundaryCycleData

/-- Nonempty concrete simple-cycle/enclosure rows directly supply exact
actual topology fields, preserving the row package's actual enclosure. -/
theorem exactActualTopologyFields_of_nonempty_simpleCyclicOuterBoundaryEnclosureRows
    {C : _root_.UDConfig n}
    (hRows :
      Nonempty (JordanBoundaryConcrete.SimpleCyclicOuterBoundaryEnclosureRows C)) :
    ExactActualTopologyFields C := by
  rcases hRows with ⟨Rows⟩
  exact exactActualTopologyFields_of_simpleCyclicOuterBoundaryEnclosureRows
    (C := C) Rows

/-- A chosen Jordan outer-component row supplies exact actual topology fields
through the real enclosure attached to the chosen cycle. -/
theorem exactActualTopologyFields_of_chosenJordanOuterComponentRow
    {C : _root_.UDConfig n}
    (row : JordanBoundaryConcrete.ChosenJordanOuterComponentRow C) :
    ExactActualTopologyFields C :=
  exactActualTopologyFields_of_actualOuterBoundaryCycleData
    (C := C)
    (JordanBoundaryConcrete.JordanOuterComponentSource.ofChosenRow
      row).toActualOuterBoundaryCycleData

/-- Nonempty chosen Jordan outer-component rows supply exact actual topology
fields without introducing a synthetic enclosure. -/
theorem exactActualTopologyFields_of_nonempty_chosenJordanOuterComponentRow
    {C : _root_.UDConfig n}
    (hrow :
      Nonempty (JordanBoundaryConcrete.ChosenJordanOuterComponentRow C)) :
    ExactActualTopologyFields C := by
  rcases hrow with ⟨row⟩
  exact exactActualTopologyFields_of_chosenJordanOuterComponentRow (C := C) row

/-- The finite planar straight-line outer-component theorem is a direct
per-configuration constructor for exact actual topology fields once its
checked graph-side inputs are supplied. -/
theorem exactActualTopologyFields_of_finitePlanarOuterComponentTheorem
    {C : _root_.UDConfig n}
    (outerComponent :
      JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarStraightLineOuterComponentTheorem)
    (inputs :
      JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
        C) :
    ExactActualTopologyFields C :=
  exactActualTopologyFields_of_nonempty_chosenJordanOuterComponentRow
    (C := C) (outerComponent C inputs)

/-- Attach enclosure predicates to the extracted simple cyclic row, after
turning that row into the exact face-boundary surface consumed by
`FaceReduction.UnitDistanceFaceBoundaryHypotheses.ofOuterBoundaryCycle`. -/
theorem exactActualTopologyFields_of_extractedSimpleCyclicOuterBoundaryRow_enclosure
    {C : _root_.UDConfig n}
    (R : ExtractedSimpleCyclicOuterBoundaryRow C)
    (insideOrOn : PlanarInterface.Point -> Prop)
    (onBoundary : Fin n -> Prop)
    (boundary_vertex_onBoundary :
      forall k : Fin R.length, onBoundary (R.vertex k))
    (boundary_point_insideOrOn :
      forall k : Fin R.length, insideOrOn ((canonicalGraph C).point (R.vertex k)))
    (all_vertices_insideOrOn :
      forall v : Fin n, insideOrOn ((canonicalGraph C).point v))
    (onBoundary_iff_outer_cycle :
      forall v : Fin n, onBoundary v <->
        Exists fun k : Fin R.length => R.vertex k = v) :
    ExactActualTopologyFields C := by
  let H : UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C) :=
    R.toFaceBoundaryHypotheses
  let E : OuterBoundaryEnclosure (canonicalGraph C) H PUnit.unit := {
    insideOrOn := insideOrOn
    onBoundary := onBoundary
    boundary_vertex_onBoundary := boundary_vertex_onBoundary
    boundary_point_insideOrOn := boundary_point_insideOrOn
    all_vertices_insideOrOn := all_vertices_insideOrOn
    onBoundary_iff_outer_cycle := onBoundary_iff_outer_cycle }
  exact
    exactActualTopologyFields_of_faceBoundaryFields
      (C := C) (H := H) (F := PUnit.unit)
      (ExtractedSimpleCyclicOuterBoundaryRow.toFaceBoundaryHypotheses_isOuterFace R)
      (ExtractedSimpleCyclicOuterBoundaryRow.toFaceBoundaryHypotheses_boundaryLength_ge_three R)
      (Nonempty.intro E)

/-- An extracted simple cyclic outer-boundary row supplies the `H/F/outer`
and nondegenerate length rows through `FaceReduction.ofOuterBoundaryCycle`;
adding the matching raw enclosure predicates gives the exact actual topology
field. -/
theorem exactActualTopologyFields_of_extractedOuterBoundaryCycle_enclosure
    {C : _root_.UDConfig n}
    (B : OuterBoundaryInterface.BoundaryCycle (canonicalGraph C))
    (hlen : 3 <= B.length)
    (insideOrOn : PlanarInterface.Point -> Prop)
    (onBoundary : Fin n -> Prop)
    (boundary_vertex_onBoundary :
      forall k : Fin B.length, onBoundary (B.vertex k))
    (boundary_point_insideOrOn :
      forall k : Fin B.length, insideOrOn ((canonicalGraph C).point (B.vertex k)))
    (all_vertices_insideOrOn :
      forall v : Fin n, insideOrOn ((canonicalGraph C).point v))
    (onBoundary_iff_outer_cycle :
      forall v : Fin n, onBoundary v <->
        Exists fun k : Fin B.length => B.vertex k = v) :
    ExactActualTopologyFields C := by
  exact
    exactActualTopologyFields_of_extractedSimpleCyclicOuterBoundaryRow_enclosure
      (C := C)
      (ExtractedSimpleCyclicOuterBoundaryRow.ofBoundaryCycle B hlen)
      insideOrOn onBoundary boundary_vertex_onBoundary
      boundary_point_insideOrOn all_vertices_insideOrOn
      onBoundary_iff_outer_cycle

/-- Positive S2 row package: an extracted simple cyclic outer-boundary row
and enclosure predicates indexed by that same extracted boundary. -/
structure ExtractedSimpleCyclicOuterBoundaryEnclosureRows
    (C : _root_.UDConfig n) where
  boundary : ExtractedSimpleCyclicOuterBoundaryRow C
  insideOrOn : PlanarInterface.Point -> Prop
  onBoundary : Fin n -> Prop
  boundary_vertex_onBoundary :
    forall k : Fin boundary.length, onBoundary (boundary.vertex k)
  boundary_point_insideOrOn :
    forall k : Fin boundary.length,
      insideOrOn ((canonicalGraph C).point (boundary.vertex k))
  all_vertices_insideOrOn :
    forall v : Fin n, insideOrOn ((canonicalGraph C).point v)
  onBoundary_iff_outer_cycle :
    forall v : Fin n, onBoundary v <->
      Exists fun k : Fin boundary.length => boundary.vertex k = v

namespace ExtractedSimpleCyclicOuterBoundaryEnclosureRows

variable {C : _root_.UDConfig n}

/-- The extracted boundary/enclosure row package is exactly enough to inhabit
the nondegenerate actual topology field for this configuration. -/
theorem toExactActualTopologyFields
    (Rows : ExtractedSimpleCyclicOuterBoundaryEnclosureRows C) :
    ExactActualTopologyFields C :=
  exactActualTopologyFields_of_extractedSimpleCyclicOuterBoundaryRow_enclosure
    (C := C) (R := Rows.boundary)
    (insideOrOn := Rows.insideOrOn)
    (onBoundary := Rows.onBoundary)
    (boundary_vertex_onBoundary := Rows.boundary_vertex_onBoundary)
    (boundary_point_insideOrOn := Rows.boundary_point_insideOrOn)
    (all_vertices_insideOrOn := Rows.all_vertices_insideOrOn)
    (onBoundary_iff_outer_cycle := Rows.onBoundary_iff_outer_cycle)

/-- A checked outer-boundary core with a nondegenerate selected cycle is
exactly the extracted boundary row plus the matching enclosure rows. -/
def ofOuterBoundaryCoreWithLength
    (P : OuterBoundaryCore.{0} (canonicalGraph C))
    (hlen : 3 <= P.outerCycle.length) :
    ExtractedSimpleCyclicOuterBoundaryEnclosureRows C where
  boundary :=
    ExtractedSimpleCyclicOuterBoundaryRow.ofBoundaryCycle
      P.outerCycle hlen
  insideOrOn := P.outerEnclosure.insideOrOn
  onBoundary := P.outerEnclosure.onBoundary
  boundary_vertex_onBoundary :=
    P.outerEnclosure.boundary_vertex_onBoundary
  boundary_point_insideOrOn :=
    P.outerEnclosure.boundary_point_insideOrOn
  all_vertices_insideOrOn :=
    P.outerEnclosure.all_vertices_insideOrOn
  onBoundary_iff_outer_cycle :=
    P.outerEnclosure.onBoundary_iff_outer_cycle

/-- Strong actual outer-boundary-cycle data projects to the extracted
boundary/enclosure row package. -/
def ofActualOuterBoundaryCycleData
    (D : JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) :
    ExtractedSimpleCyclicOuterBoundaryEnclosureRows C :=
  ofOuterBoundaryCoreWithLength D.core D.outerCycle_length_ge_three

/-- Exact actual topology fields contain the same concrete data as the
extracted boundary/enclosure row package, up to repackaging the selected face
as an `OuterBoundaryCore`. -/
theorem nonempty_of_exactActualTopologyFields
    (h : ExactActualTopologyFields C) :
    Nonempty (ExtractedSimpleCyclicOuterBoundaryEnclosureRows C) := by
  rcases h with ⟨H, F, hF, hlen, ⟨E⟩⟩
  let P : OuterBoundaryCore.{0} (canonicalGraph C) := {
    faceBoundary := H
    outerFace := F
    outerFace_isOuter := hF
    outerEnclosure := E }
  exact ⟨ofOuterBoundaryCoreWithLength P (by
    change 3 <= H.boundaryLength F
    exact hlen)⟩

/-- The compact extracted boundary/enclosure row package is equivalent to the
nondegenerate exact actual topology field for a fixed configuration.  The
reverse direction uses the actual recorded enclosure predicates. -/
theorem nonempty_iff_exactActualTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (ExtractedSimpleCyclicOuterBoundaryEnclosureRows C) <->
      ExactActualTopologyFields C := by
  constructor
  · rintro ⟨Rows⟩
    exact Rows.toExactActualTopologyFields
  · exact nonempty_of_exactActualTopologyFields

end ExtractedSimpleCyclicOuterBoundaryEnclosureRows

/-- The nondegenerate field still supplies the older topology field after
forgetting only the boundary-length proof. -/
theorem exactTopologyFields_of_exactActualTopologyFields
    {C : _root_.UDConfig n}
    (h : ExactActualTopologyFields C) :
    ExactTopologyFields C := by
  rcases h with ⟨H, F, hF, _hlen, hE⟩
  exact ⟨H, F, hF, hE⟩

/-- The nondegenerate exact topology field is exactly a checked
outer-boundary core whose selected boundary has length at least three. -/
theorem exactActualTopologyFields_iff_outerBoundaryCore_with_length_ge_three
    (C : _root_.UDConfig n) :
    ExactActualTopologyFields C <->
      Exists fun P : OuterBoundaryCore.{0} (canonicalGraph C) =>
        3 <= P.outerCycle.length := by
  constructor
  · rintro ⟨H, F, hF, hlen, ⟨E⟩⟩
    let P : OuterBoundaryCore.{0} (canonicalGraph C) := {
      faceBoundary := H
      outerFace := F
      outerFace_isOuter := hF
      outerEnclosure := E }
    exact ⟨P, by
      change 3 <= H.boundaryLength F
      exact hlen⟩
  · rintro ⟨P, hP⟩
    exact ⟨P.faceBoundary, P.outerFace, P.outerFace_isOuter, by
      change 3 <= P.outerCycle.length
      exact hP, ⟨P.outerEnclosure⟩⟩

/-- Exact actual topology fields repackage to actual outer-boundary-cycle data
without changing the selected face or the recorded enclosure predicates. -/
theorem nonempty_actualOuterBoundaryCycleData_of_exactActualTopologyFields
    {C : _root_.UDConfig n}
    (h : ExactActualTopologyFields C) :
    Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) := by
  rcases h with ⟨H, F, hF, hlen, ⟨E⟩⟩
  let P : OuterBoundaryCore.{0} (canonicalGraph C) := {
    faceBoundary := H
    outerFace := F
    outerFace_isOuter := hF
    outerEnclosure := E }
  exact
    Nonempty.intro
      (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.ofCore P (by
        change 3 <= H.boundaryLength F
        exact hlen))

/-- Nonempty actual outer-boundary-cycle data is equivalent to the exact
actual topology field.  Both directions preserve the actual core/enclosure
data; no synthetic extracted-cycle enclosure is introduced. -/
theorem exactActualTopologyFields_iff_nonempty_actualOuterBoundaryCycleData
    (C : _root_.UDConfig n) :
    ExactActualTopologyFields C <->
      Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) := by
  constructor
  · exact nonempty_actualOuterBoundaryCycleData_of_exactActualTopologyFields
  · exact exactActualTopologyFields_of_nonempty_actualOuterBoundaryCycleData

theorem nonempty_actualOuterBoundaryCycleData_iff_exactActualTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) <->
      ExactActualTopologyFields C :=
  (exactActualTopologyFields_iff_nonempty_actualOuterBoundaryCycleData C).symm

/-- Exact actual topology fields also repackage as concrete simple-cycle
enclosure rows, using the actual-cycle data and its stored enclosure. -/
theorem nonempty_simpleCyclicOuterBoundaryEnclosureRows_of_exactActualTopologyFields
    {C : _root_.UDConfig n}
    (h : ExactActualTopologyFields C) :
    Nonempty (JordanBoundaryConcrete.SimpleCyclicOuterBoundaryEnclosureRows C) := by
  exact
    (JordanBoundaryConcrete.SimpleCyclicOuterBoundaryEnclosureRows.nonempty_iff_actualOuterBoundaryCycleData
      C).2
      (nonempty_actualOuterBoundaryCycleData_of_exactActualTopologyFields h)

/-- The concrete simple-cycle/enclosure row surface is equivalent to exact
actual topology fields, via the real actual-cycle data it carries. -/
theorem exactActualTopologyFields_iff_nonempty_simpleCyclicOuterBoundaryEnclosureRows
    (C : _root_.UDConfig n) :
    ExactActualTopologyFields C <->
      Nonempty (JordanBoundaryConcrete.SimpleCyclicOuterBoundaryEnclosureRows C) := by
  constructor
  · exact nonempty_simpleCyclicOuterBoundaryEnclosureRows_of_exactActualTopologyFields
  · exact exactActualTopologyFields_of_nonempty_simpleCyclicOuterBoundaryEnclosureRows

theorem nonempty_simpleCyclicOuterBoundaryEnclosureRows_iff_exactActualTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (JordanBoundaryConcrete.SimpleCyclicOuterBoundaryEnclosureRows C) <->
      ExactActualTopologyFields C :=
  (exactActualTopologyFields_iff_nonempty_simpleCyclicOuterBoundaryEnclosureRows
    C).symm

namespace ExtractedSimpleCyclicOuterBoundaryEnclosureRows

/-- The extracted boundary/enclosure rows are also exactly a nondegenerate
outer-boundary core for the canonical graph. -/
theorem nonempty_iff_outerBoundaryCore_with_length_ge_three
    (C : _root_.UDConfig n) :
    Nonempty (ExtractedSimpleCyclicOuterBoundaryEnclosureRows C) <->
      Exists fun P : OuterBoundaryCore.{0} (canonicalGraph C) =>
        3 <= P.outerCycle.length := by
  exact Iff.trans
    (nonempty_iff_exactActualTopologyFields C)
    (exactActualTopologyFields_iff_outerBoundaryCore_with_length_ge_three C)

end ExtractedSimpleCyclicOuterBoundaryEnclosureRows

/-- The exact nondegenerate topology field is precisely the strong remaining
actual outer-boundary-cycle theorem exposed by `JordanBoundaryConcrete`. -/
theorem exactActualTopologyFields_iff_remainingActualOuterBoundaryCycleTheorem
    (C : _root_.UDConfig n) :
    ExactActualTopologyFields C <->
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C :=
  exactActualTopologyFields_iff_nonempty_actualOuterBoundaryCycleData C

/-- The strong remaining actual-cycle theorem supplies exact actual topology
fields by unpacking its actual-cycle data, preserving the stored core
enclosure. -/
theorem exactActualTopologyFields_of_remainingActualOuterBoundaryCycleTheorem
    {C : _root_.UDConfig n}
    (h :
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C) :
    ExactActualTopologyFields C :=
  exactActualTopologyFields_of_nonempty_actualOuterBoundaryCycleData (C := C) h

/-- Symmetric form for callers whose source is the strong remaining
actual-cycle theorem. -/
theorem remainingActualOuterBoundaryCycleTheorem_iff_exactActualTopologyFields
    (C : _root_.UDConfig n) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C <->
      ExactActualTopologyFields C :=
  (exactActualTopologyFields_iff_remainingActualOuterBoundaryCycleTheorem C).symm

/-- Concrete nondegenerate face-boundary fields close the strong remaining
actual outer-boundary-cycle theorem. -/
theorem remainingActualOuterBoundaryCycleTheorem_of_exactActualTopologyFields
    {C : _root_.UDConfig n}
    (h : ExactActualTopologyFields C) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
      C :=
  nonempty_actualOuterBoundaryCycleData_of_exactActualTopologyFields h

/-- The raw field is exactly the construction target in
`OuterBoundaryCoreConstruction`. -/
theorem remainingCoreTopologyRequirements_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    RemainingCoreTopologyRequirements C <-> ExactTopologyFields C := by
  constructor
  · rintro ⟨D, ⟨E⟩⟩
    exact ⟨D.faceBoundary, D.outerFace, D.outerFace_isOuter,
      ⟨E.outerEnclosure⟩⟩
  · rintro ⟨H, F, hF, ⟨E⟩⟩
    let D : OuterFaceData.{0} (canonicalGraph C) := {
      faceBoundary := H
      outerFace := F
      outerFace_isOuter := hF }
    exact ⟨D, ⟨{ outerEnclosure := E }⟩⟩

/-- Supplying exactly face data, a selected outer face, and enclosure data
discharges the remaining core-topology target. -/
theorem remainingCoreTopologyRequirements_of_exactTopologyFields
    {C : _root_.UDConfig n}
    {H : UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C)}
    {F : H.Face}
    (hF : H.IsOuterFace F)
    (hE : Nonempty (OuterBoundaryEnclosure (canonicalGraph C) H F)) :
    RemainingCoreTopologyRequirements C := by
  exact
    (remainingCoreTopologyRequirements_iff_exactTopologyFields C).2
      ⟨H, F, hF, hE⟩

/-- The remaining target is equivalently nonempty checked core data. -/
theorem remainingCoreTopologyRequirements_iff_coreNonempty
    (C : _root_.UDConfig n) :
    RemainingCoreTopologyRequirements C <->
      Nonempty (OuterBoundaryCore.{0} (canonicalGraph C)) :=
  OuterBoundaryCoreConstruction.remainingCoreTopologyRequirements_iff_outerBoundaryCore C

/-- A checked core discharges the remaining target. -/
theorem remainingCoreTopologyRequirements_of_core
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (canonicalGraph C)) :
    RemainingCoreTopologyRequirements C :=
  (remainingCoreTopologyRequirements_iff_coreNonempty C).2 ⟨P⟩

/-- The remaining target is equivalently the concrete Jordan-boundary topology
frontier already exposed in `JordanBoundaryConcrete`. -/
theorem remainingCoreTopologyRequirements_iff_missingTopologyFacts
    (C : _root_.UDConfig n) :
    RemainingCoreTopologyRequirements C <->
      Nonempty (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :=
  OuterBoundaryCoreConstruction.remainingCoreTopologyRequirements_iff_jordanBoundaryConcrete C

/-- Concrete missing-topology facts discharge the remaining target. -/
theorem remainingCoreTopologyRequirements_of_missingTopologyFacts
    {C : _root_.UDConfig n}
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    RemainingCoreTopologyRequirements C :=
  (remainingCoreTopologyRequirements_iff_missingTopologyFacts C).2 ⟨T⟩

/-- The remaining target is also equivalently nonempty concrete topology facts
from `JordanTopologyFactsConcrete`. -/
theorem remainingCoreTopologyRequirements_iff_topologyFacts
    (C : _root_.UDConfig n) :
    RemainingCoreTopologyRequirements C <->
      Nonempty (JordanTopologyFactsConcrete.TopologyFacts.{0} C) := by
  constructor
  · intro h
    rcases (remainingCoreTopologyRequirements_iff_coreNonempty C).1 h with ⟨P⟩
    exact ⟨JordanTopologyFactsConcrete.TopologyFacts.ofCore P⟩
  · rintro ⟨T⟩
    exact remainingCoreTopologyRequirements_of_core T.toCore

/-- Concrete topology facts discharge the remaining target. -/
theorem remainingCoreTopologyRequirements_of_topologyFacts
    {C : _root_.UDConfig n}
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    RemainingCoreTopologyRequirements C :=
  (remainingCoreTopologyRequirements_iff_topologyFacts C).2 ⟨T⟩

/-- The graph side is complete; the global construction target is exactly the
remaining topology field for every concrete configuration. -/
theorem globalTarget_iff_exactTopologyFields :
    GlobalOuterBoundaryCoreConstructionTarget <->
      forall (n : Nat) (C : _root_.UDConfig n), ExactTopologyFields C := by
  constructor
  · intro h n C
    exact (remainingCoreTopologyRequirements_iff_exactTopologyFields C).1
      (h n C)
  · intro h n C
    exact (remainingCoreTopologyRequirements_iff_exactTopologyFields C).2
      (h n C)

end

end OuterBoundaryExistenceConcrete
end Swanepoel
end ErdosProblems1066
