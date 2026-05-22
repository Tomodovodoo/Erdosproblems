import ErdosProblems1066.Swanepoel.S2ExteriorBoundarySource

set_option autoImplicit false

/-!
# S2 boundary-free raw source certificates

This file owns the reusable certificate shapes for the current S2 route:
pointwise boundary-free two-germ/no-third-germ rows, and raw-orbit coverage of
the actual unbounded-frontier carrier edges.  The heavy topology and local
geometry remain in their owner modules; this file only turns those certificates
into the checked S2 source rows.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace ExteriorComponentTopology

open JordanTopologyFactsConcrete
open JordanTopologyFactsConcrete.MinimalFailureTopology
open FinitePlaneDrawing
open GeometricRotationSystem

variable {n : Nat}
universe u

/-- Boundary-free local two-germ source at every graph vertex on the actual
unbounded exterior frontier.

The selected `left` and `right` edges are actual carrier edges, and
`no_third_germ` excludes any third incident germ carrying nearby frontier
points. -/
structure BoundaryFreeNoThirdGermSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  left :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Fin n
  right :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Fin n
  left_edge :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs
  right_edge :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs
  heads_ne :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      left a ≠ right a
  no_third_germ :
    ∀ (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
      q ∈ Metric.ball ((canonicalGraph C).point a.1) ε →
        q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
          (canonicalGraph C).Adj a.1 x →
            q ∈ vertexIncidentGermW3 C a.1 x ε →
              q ≠ (canonicalGraph C).point a.1 →
                x ≠ left a →
                  x ≠ right a →
                    False

namespace BoundaryFreeNoThirdGermSource

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- Existential projection consumed by the older S2 reducers. -/
def toExistsSource
    (source : BoundaryFreeNoThirdGermSource inputs) :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Exists fun left : Fin n =>
        Exists fun right : Fin n =>
          ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
            (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
          ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
            (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
          left ≠ right ∧
          ∀ (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε →
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
                (canonicalGraph C).Adj a.1 x →
                  q ∈ vertexIncidentGermW3 C a.1 x ε →
                    q ≠ (canonicalGraph C).point a.1 →
                      x ≠ left →
                        x ≠ right →
                          False := by
  intro a
  exact
    ⟨source.left a, source.right a,
      source.left_edge a, source.right_edge a, source.heads_ne a,
      source.no_third_germ a⟩

/-- Package the older existential two-neighbour source row as the structured
boundary-free no-third-germ source used by the newer S2 route. -/
noncomputable def ofExistsSource
    (source :
      ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun left : Fin n =>
          Exists fun right : Fin n =>
            ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            ∀ (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) ε →
                q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
                  (canonicalGraph C).Adj a.1 x →
                    q ∈ vertexIncidentGermW3 C a.1 x ε →
                      q ≠ (canonicalGraph C).point a.1 →
                        x ≠ left →
                          x ≠ right →
                            False) :
    BoundaryFreeNoThirdGermSource inputs where
  left := fun a => Classical.choose (source a)
  right := fun a => Classical.choose (Classical.choose_spec (source a))
  left_edge := by
    intro a
    let hleft := Classical.choose_spec (source a)
    let hspec := Classical.choose_spec hleft
    exact hspec.1
  right_edge := by
    intro a
    let hleft := Classical.choose_spec (source a)
    let hspec := Classical.choose_spec hleft
    exact hspec.2.1
  heads_ne := by
    intro a
    let hleft := Classical.choose_spec (source a)
    let hspec := Classical.choose_spec hleft
    exact hspec.2.2.1
  no_third_germ := by
    intro a
    let hleft := Classical.choose_spec (source a)
    let hspec := Classical.choose_spec hleft
    exact hspec.2.2.2

/-- Boundary-cycle predecessor/successor angular rows package directly as the
structured no-third-germ source used by the newer S2 route. -/
noncomputable def ofBoundaryCycleAngularRows
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      ∀ v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_edge_mem :
      ∀ k : Fin B.length,
        (B.vertex k,
            B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) ∈
            unboundedFrontierEdgeSet C inputs ∨
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k),
            B.vertex k) ∈
            unboundedFrontierEdgeSet C inputs)
    (angularRows :
      ∀ k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k)
    (third_germ_between :
      ∀ (k : Fin B.length) (ε : Real) (q : PlanarInterface.Point)
          (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) ε →
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
            (canonicalGraph C).Adj (B.vertex k) x →
              q ∈ vertexIncidentGermW3 C (B.vertex k) x ε →
                q ≠ (canonicalGraph C).point (B.vertex k) →
                  x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) →
                    x ≠
                        B.vertex (PlanarInterface.cyclicSucc B.length_pos k) →
                      GeometricRotationSystem.BoundaryPredSuccAngularBetween
                        C B k x) :
    BoundaryFreeNoThirdGermSource inputs :=
  ofExistsSource
    (C := C) (inputs := inputs)
    (S2_boundaryFree_twoSelectedEdges_noThirdGerm_source_of_boundaryCycle_angularRows
      (C := C) (inputs := inputs) B frontier_iff_cycle_vertex
      cycle_edge_mem angularRows third_germ_between)

/-- Boundary-cycle angular rows plus the point-ray local exterior-sector row
package as the structured boundary-free no-third-germ source.

This is only the local conversion: it reuses the checked theorem that a
nearby noncenter frontier point in a third W3 germ transfers its point-angle
sector statement to the incident graph dart. -/
noncomputable def ofBoundaryCycleAngularRows_localExteriorSector
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_edge_mem :
      forall k : Fin B.length,
        (B.vertex k,
            B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) ∈
            unboundedFrontierEdgeSet C inputs ∨
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k),
            B.vertex k) ∈
            unboundedFrontierEdgeSet C inputs)
    (angularRows :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k)
    (local_exterior_sector :
      forall (k : Fin B.length) (eps : Real) (q : PlanarInterface.Point)
          (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) eps ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj (B.vertex k) x ->
              q ∈ vertexIncidentGermW3 C (B.vertex k) x eps ->
                q ≠ (canonicalGraph C).point (B.vertex k) ->
                  x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
                    x ≠
                        B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
                      BoundaryPredSuccPointAngularBetween C B k q) :
    BoundaryFreeNoThirdGermSource inputs :=
  ofBoundaryCycleAngularRows
    (C := C) (inputs := inputs)
    B frontier_iff_cycle_vertex cycle_edge_mem angularRows
    (boundary_frontier_third_germ_between_of_local_exterior_sector_source
      (C := C) (inputs := inputs) (B := B) local_exterior_sector)

set_option linter.style.longLine false in
/-- Boundary-cycle angular rows plus the closed-segment local exterior-angular
row package as the structured boundary-free no-third-germ source.

This is the narrow closed-germ reducer: the far-endpoint case is part of the
same closed-segment angular row, so no all-adjacent endpoint/chord classifier
or synthetic enclosure row is introduced. -/
noncomputable def ofBoundaryCycleAngularRows_closedSegmentLocalExteriorAngular
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_edge_mem :
      forall k : Fin B.length,
        (B.vertex k,
            B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) ∈
            unboundedFrontierEdgeSet C inputs ∨
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k),
            B.vertex k) ∈
            unboundedFrontierEdgeSet C inputs)
    (angularRows :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k)
    (closedSegment_local_exterior_angular :
      BoundaryFrontierClosedSegmentLocalExteriorAngularSector inputs B) :
    BoundaryFreeNoThirdGermSource inputs :=
  ofBoundaryCycleAngularRows
    (C := C) (inputs := inputs)
    B frontier_iff_cycle_vertex cycle_edge_mem angularRows
    (fun k eps q x hqball hqfrontier hadj hgerm hqne hxpred hxsucc =>
      closedSegment_local_exterior_angular k eps q x hqball hqfrontier hadj
        hgerm.2 hqne hxpred hxsucc)

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundaryfree-no-third-germ-source-20260520f`.

Actual boundary-cycle rows, boundary angular no-between rows, and the
same-boundary closed-segment local exterior-angular row strictly reduce the
global boundary-free no-third-germ source. -/
noncomputable def
    S2_agent_boundaryfree_no_third_germ_source_20260520f_of_actualBoundaryRows_angular_closedSegmentLocalExteriorAngular
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k)
    (closedSegment_local_exterior_angular :
      BoundaryFrontierClosedSegmentLocalExteriorAngularSector
        inputs actualRows.boundary) :
    BoundaryFreeNoThirdGermSource inputs :=
  ofBoundaryCycleAngularRows_closedSegmentLocalExteriorAngular
    (C := C) (inputs := inputs)
    actualRows.boundary
    actualRows.frontier_iff_cycle_vertex
    (fun k => actualRows.cycle_edge_mem_unboundedFrontierEdgeSet_or_symm k)
    angularRows
    closedSegment_local_exterior_angular

set_option linter.style.longLine false in
/-- Claim `S2-agent-closed-segment-local-exterior-angular-source-20260520g`,
boundary-free consumer form.

This is the strict same-boundary reduction of the closed-segment angular leaf
exposed by
`S2_agent_boundaryfree_no_third_germ_source_20260520f_of_actualBoundaryRows_angular_closedSegmentLocalExteriorAngular`.
The residual is selected-edge-gated: the exact incident closed segment is first
promoted to `unboundedFrontierEdgeSet`, and bad selected incident edges are
ruled out through repeated exterior-boundary arc separation rows. -/
noncomputable def
    S2_agent_boundaryfree_no_third_germ_source_20260520g_of_actualBoundaryRows_angular_closedSegmentSelectedEdge_badIncidentEdgeArcRows
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k)
    (closedSegment_selected_edge :
      BoundaryFrontierClosedSegmentSelectedEdgeSource
        inputs actualRows.boundary)
    (badIncidentEdge_arcRows :
      forall k : Fin actualRows.boundary.length, forall x : Fin n,
        ((actualRows.boundary.vertex k, x) ∈
            unboundedFrontierEdgeSet C inputs ∨
          (x, actualRows.boundary.vertex k) ∈
            unboundedFrontierEdgeSet C inputs) ->
          x ≠
              actualRows.boundary.vertex
                (PlanarInterface.cyclicPred
                  actualRows.boundary.length_pos k) ->
            x ≠
                actualRows.boundary.vertex
                  (PlanarInterface.cyclicSucc
                    actualRows.boundary.length_pos k) ->
              Nonempty
                (Sigma fun i : Fin actualRows.boundary.length =>
                  Sigma fun j : Fin actualRows.boundary.length =>
                    RepeatedExteriorBoundaryArcSeparationRows C
                      actualRows.boundary.vertex i j)) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_agent_boundaryfree_no_third_germ_source_20260520f_of_actualBoundaryRows_angular_closedSegmentLocalExteriorAngular
    (C := C) (inputs := inputs)
    actualRows angularRows
    (S2_agent_closed_segment_local_exterior_angular_source_20260520g
      (C := C) (inputs := inputs) (B := actualRows.boundary)
      closedSegment_selected_edge badIncidentEdge_arcRows)

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundary-free-no-third-selected-edge-worker-20260520l4`.

Selected closed-segment source rows and bad selected incident-edge arc rows are
the current selected-edge-only residual for the global boundary-free
no-third-germ source.  The conversion stays on actual
`unboundedFrontierEdgeSet` incidences: the closed segment first names the
selected incident edge, and the bad selected incident edge is then ruled out
through repeated exterior-boundary arc rows plus `inputs.noCutVertex`. -/
noncomputable def
    S2_agent_boundary_free_no_third_selected_edge_worker_20260520l4
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k)
    (closedSegment_selected_edge :
      BoundaryFrontierClosedSegmentSelectedEdgeSource
        inputs actualRows.boundary)
    (badIncidentEdge_arcRows :
      forall k : Fin actualRows.boundary.length, forall x : Fin n,
        ((actualRows.boundary.vertex k, x) ∈
            unboundedFrontierEdgeSet C inputs ∨
          (x, actualRows.boundary.vertex k) ∈
            unboundedFrontierEdgeSet C inputs) ->
          x ≠
              actualRows.boundary.vertex
                (PlanarInterface.cyclicPred
                  actualRows.boundary.length_pos k) ->
            x ≠
                actualRows.boundary.vertex
                  (PlanarInterface.cyclicSucc
                    actualRows.boundary.length_pos k) ->
              Nonempty
                (Sigma fun i : Fin actualRows.boundary.length =>
                  Sigma fun j : Fin actualRows.boundary.length =>
                    RepeatedExteriorBoundaryArcSeparationRows C
                      actualRows.boundary.vertex i j)) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_agent_boundaryfree_no_third_germ_source_20260520g_of_actualBoundaryRows_angular_closedSegmentSelectedEdge_badIncidentEdgeArcRows
    (C := C) (inputs := inputs)
    actualRows angularRows closedSegment_selected_edge badIncidentEdge_arcRows

set_option linter.style.longLine false in
/-- Nonempty form of
`S2_agent_boundary_free_no_third_selected_edge_worker_20260520l4`. -/
noncomputable def
    S2_agent_boundary_free_no_third_selected_edge_worker_nonempty_20260520l4
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k)
    (closedSegment_selected_edge :
      BoundaryFrontierClosedSegmentSelectedEdgeSource
        inputs actualRows.boundary)
    (badIncidentEdge_arcRows :
      forall k : Fin actualRows.boundary.length, forall x : Fin n,
        ((actualRows.boundary.vertex k, x) ∈
            unboundedFrontierEdgeSet C inputs ∨
          (x, actualRows.boundary.vertex k) ∈
            unboundedFrontierEdgeSet C inputs) ->
          x ≠
              actualRows.boundary.vertex
                (PlanarInterface.cyclicPred
                  actualRows.boundary.length_pos k) ->
            x ≠
                actualRows.boundary.vertex
                  (PlanarInterface.cyclicSucc
                    actualRows.boundary.length_pos k) ->
              Nonempty
                (Sigma fun i : Fin actualRows.boundary.length =>
                  Sigma fun j : Fin actualRows.boundary.length =>
                    RepeatedExteriorBoundaryArcSeparationRows C
                      actualRows.boundary.vertex i j)) :
    Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  ⟨S2_agent_boundary_free_no_third_selected_edge_worker_20260520l4
    (C := C) (inputs := inputs)
    actualRows angularRows closedSegment_selected_edge badIncidentEdge_arcRows⟩

set_option linter.style.longLine false in
/-- Family form of the selected-edge-only l4 boundary-free source reducer. -/
noncomputable def
    S2_agent_boundary_free_no_third_selected_edge_worker_family_20260520l4
    (actualRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall k : Fin (actualRows C inputs).boundary.length,
            GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
              C (actualRows C inputs).boundary k)
    (closedSegment_selected_edge :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFrontierClosedSegmentSelectedEdgeSource
            inputs (actualRows C inputs).boundary)
    (badIncidentEdge_arcRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall k : Fin (actualRows C inputs).boundary.length,
            forall x : Fin m,
              (((actualRows C inputs).boundary.vertex k, x) ∈
                  unboundedFrontierEdgeSet C inputs ∨
                (x, (actualRows C inputs).boundary.vertex k) ∈
                  unboundedFrontierEdgeSet C inputs) ->
                x ≠
                    (actualRows C inputs).boundary.vertex
                      (PlanarInterface.cyclicPred
                        (actualRows C inputs).boundary.length_pos k) ->
                  x ≠
                      (actualRows C inputs).boundary.vertex
                        (PlanarInterface.cyclicSucc
                          (actualRows C inputs).boundary.length_pos k) ->
                    Nonempty
                      (Sigma fun i : Fin (actualRows C inputs).boundary.length =>
                        Sigma fun j : Fin (actualRows C inputs).boundary.length =>
                          RepeatedExteriorBoundaryArcSeparationRows C
                            (actualRows C inputs).boundary.vertex i j)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeNoThirdGermSource inputs := by
  intro m C inputs
  exact
    S2_agent_boundary_free_no_third_selected_edge_worker_20260520l4
      (C := C) (inputs := inputs)
      (actualRows C inputs)
      (angularRows C inputs)
      (closedSegment_selected_edge C inputs)
      (badIncidentEdge_arcRows C inputs)

set_option linter.style.longLine false in
/-- Face-successor/orientation form of the 20260520f boundary-free
no-third-germ reducer. -/
noncomputable def
    S2_agent_boundaryfree_no_third_germ_source_20260520f_of_actualBoundaryRows_faceSucc_closedSegmentLocalExteriorAngular
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary)
    (boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k)))
    (closedSegment_local_exterior_angular :
      BoundaryFrontierClosedSegmentLocalExteriorAngularSector
        inputs actualRows.boundary) :
    BoundaryFreeNoThirdGermSource inputs :=
  let angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k :=
    GeometricRotationSystem.boundaryVertexAngularNoBetweenRows_of_faceSuccRows_pred_arg_lt_succ_arg
      C actualRows.boundary faceSuccRows boundary_orientation
  S2_agent_boundaryfree_no_third_germ_source_20260520f_of_actualBoundaryRows_angular_closedSegmentLocalExteriorAngular
    (C := C) (inputs := inputs)
    actualRows angularRows closedSegment_local_exterior_angular

/-- Actual boundary-cycle rows, angular no-between rows, the open-segment
local exterior-sector source, and the endpoint-only incident row give the
structured boundary-free no-third-germ source.

This is the source-owner form used by the selected raw-orbit route: the actual
boundary rows supply both the frontier vertex equivalence and the selected
unbounded-frontier edge membership for consecutive boundary sides.  The
endpoint-only row is the honest branch needed to upgrade open-segment local
geometry to the W3/closed-germ local source. -/
noncomputable def ofActualBoundaryRowsAngularOpenSegmentEndpoint
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k)
    (local_exterior_sector :
      BoundaryFrontierOpenSegmentLocalExteriorSector inputs
        actualRows.boundary)
    (endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
        actualRows.boundary) :
    BoundaryFreeNoThirdGermSource inputs :=
  ofBoundaryCycleAngularRows_localExteriorSector
    (C := C) (inputs := inputs)
    actualRows.boundary
    actualRows.frontier_iff_cycle_vertex
    (fun k => actualRows.cycle_edge_mem_unboundedFrontierEdgeSet_or_symm k)
    angularRows
    (boundary_frontier_local_exterior_sector_of_openSegment_pointSector_endpoint_incident_only
      (C := C) (inputs := inputs) (B := actualRows.boundary)
      local_exterior_sector endpoint_incident_only)

set_option linter.style.longLine false in
/-- Actual boundary-cycle rows, geometric `faceSucc` rows, ordinary boundary
orientation, open-segment local exterior sectors, and endpoint-only incidence
give the structured boundary-free no-third-germ source.

This is the face-successor owner form of
`ofActualBoundaryRowsAngularOpenSegmentEndpoint`: it derives the angular
no-between rows from the genuine geometric `faceSucc` rows instead of asking
callers to pass them separately. -/
noncomputable def ofActualBoundaryRowsFaceSuccOpenSegmentEndpoint
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary)
    (boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k)))
    (local_exterior_sector :
      BoundaryFrontierOpenSegmentLocalExteriorSector inputs
        actualRows.boundary)
    (endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
        actualRows.boundary) :
    BoundaryFreeNoThirdGermSource inputs :=
  let angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k :=
    GeometricRotationSystem.boundaryVertexAngularNoBetweenRows_of_faceSuccRows_pred_arg_lt_succ_arg
      C actualRows.boundary faceSuccRows boundary_orientation
  ofActualBoundaryRowsAngularOpenSegmentEndpoint
    (C := C) (inputs := inputs)
    actualRows angularRows local_exterior_sector endpoint_incident_only

/-- Nonempty wrapper for
`ofActualBoundaryRowsAngularOpenSegmentEndpoint`. -/
noncomputable def nonemptyOfActualBoundaryRowsAngularOpenSegmentEndpoint
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k)
    (local_exterior_sector :
      BoundaryFrontierOpenSegmentLocalExteriorSector inputs
        actualRows.boundary)
    (endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
        actualRows.boundary) :
    Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  ⟨ofActualBoundaryRowsAngularOpenSegmentEndpoint
    (C := C) (inputs := inputs)
    actualRows angularRows local_exterior_sector endpoint_incident_only⟩

/-- Boundary-free no-third-germ rows give the local two-germ rows. -/
def toLocalTwoGermRows
    (source : BoundaryFreeNoThirdGermSource inputs) :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
  S2_localTwoGermRows_of_noThirdGermFamily
    source.left source.right source.left_edge source.right_edge
    source.heads_ne source.no_third_germ

/-- Boundary-free no-third-germ rows give the local-sector rows used for
carrier degree two. -/
def toLocalSectorRows
    (source : BoundaryFreeNoThirdGermSource inputs) :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2_localSectorRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
    (C := C) (inputs := inputs) source.toExistsSource

/-- Boundary-free local carrier realization plus component-avoidance
Janiszewski rows give connectedness of the actual frontier carrier graph. -/
theorem connected_of_janiszewskiComponentAvoidance
    (source : BoundaryFreeNoThirdGermSource inputs)
    (component_avoidance :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_janiszewskiComponentAvoidance_localSectorRows
    (C := C) inputs component_avoidance source.toLocalSectorRows

/-- Boundary-free no-third-germ rows erase to the ambient deleted-neighbour
source.

This is the endpoint-free CW handoff: the source first forgets to the checked
local-sector rows, and those rows discharge the deleted-neighbour residual.
No adjacent-endpoint incident or closure row is introduced. -/
def toUnreachableAfterDeleteInputSource
    (source : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  unboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource_of_localSectorRows
    source.toLocalSectorRows

/-- Boundary-free no-third-germ rows also fill the explicit local-separation
source used by the deleted-neighbour route.

For a purported third carrier neighbour, the local-sector row already says it
is one of the two selected heads.  Thus the side-separation fields are
vacuous in exactly that branch, while the named selected edges are preserved. -/
def toDeletedNeighborLocalSeparationInputSource
    (source : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
      C inputs where
  rows := by
    intro a
    let localRows := source.toLocalSectorRows a
    exact
      { left := localRows.left
        right := localRows.right
        left_edge := localRows.left_edge
        right_edge := localRows.right_edge
        heads_ne := localRows.heads_ne
        third_neighbor_side := fun _ _ _ _ x =>
          if x = localRows.left then true else false
        left_side := by
          intro b hb hb_left hb_right
          simp
        third_neighbor_side_false := by
          intro b hb hb_left hb_right
          simp [hb_left]
        anticomplete := by
          intro b hb hb_left hb_right x y hx_cut hy_cut hx_side hy_side hAdj
          rcases localRows.only b hb with hleft | hright
          · exact hb_left hleft
          · exact hb_right hright }

/-- Boundary-free no-third-germ rows give the current pointwise neighbour-pair
source for the concrete unbounded-frontier carrier. -/
def toNeighborPairRows
    (source : BoundaryFreeNoThirdGermSource inputs) :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a :=
  fun a => (source.toLocalSectorRows a).toNeighborPairAt

/-- Boundary-free no-third-germ rows supply the selected-edge incidence row
at every unbounded-frontier graph vertex. -/
def toFrontierVertexIncidentSource
    (source : BoundaryFreeNoThirdGermSource inputs) :
    FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
  frontierVertexIncidentSource_of_neighborPairRows
    (C := C) (inputs := inputs) source.toNeighborPairRows

/-- Boundary-free no-third-germ rows supply the selected-edge cover of the
actual unbounded exterior frontier. -/
def toSelectedFrontierEdgeCover
    (source : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorSelectedFrontierEdgeCover C inputs :=
  frontier_edge_cover_of_localSectorRows_fixedSide
    inputs source.toLocalSectorRows

/-- Boundary-free no-third-germ rows plus actual frontier preconnectedness fill
the local/component topology package.

The local source supplies only the fixed-side local-sector cover of the actual
`unboundedFrontierEdgeSet`; the topology field remains the honest
preconnectedness of `frontier (unboundedExteriorComponentRows C inputs).exterior`. -/
def toComponentTopologyRowsFromFrontierPreconnected
    (source : BoundaryFreeNoThirdGermSource inputs)
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior)) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  componentTopologySourceRows_of_frontierPreconnected_localSectorRows
    (C := C) inputs frontier_preconnected source.toLocalSectorRows

/-- Finite-drawing no-closed-separation plus boundary-free no-third-germ rows
fill the local/component topology package. -/
def toComponentTopologyRowsFromFiniteDrawingNoClosedSeparation
    (source : BoundaryFreeNoThirdGermSource inputs)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  source.toComponentTopologyRowsFromFrontierPreconnected
    (C := C) (inputs := inputs)
    (actualFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      (C := C) inputs frontier_noClosedSeparation)

/-- Claim `S2-agent-component-topology-source-worker-20260520r4`,
boundary-free local-cover form.

The finite-drawing topology row supplies actual frontier preconnectedness, and
the boundary-free local source supplies the concrete selected
`unboundedFrontierEdgeSet` cover through fixed-side local-sector rows. -/
def S2_agent_component_topology_source_worker_20260520r4_boundaryFree
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (source : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  source.toComponentTopologyRowsFromFiniteDrawingNoClosedSeparation
    (C := C) (inputs := inputs) frontier_noClosedSeparation

/-- Claim `S2-agent-cw-boundaryfree-from-deleted-neighbor`.

The boundary-free local source reduces to the current deleted-neighbour
source.  This composes the existing local-sector eraser with the
deleted-neighbour eraser and intentionally avoids the false adjacent-endpoint
incident/closure source rows. -/
def S2_agent_cw_unreachableAfterDeleteInputSource_of_boundaryFreeNoThirdGermSource_20260520
    (source : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  source.toUnreachableAfterDeleteInputSource

/-- Claim `S2-pool-cx-local-two-germ-source`.

The deleted-neighbour source is reduced through the explicit local-separation
surface to the boundary-free no-third/two-germ row.  The remaining source is
therefore the actual input-level construction of
`BoundaryFreeNoThirdGermSource inputs`, not a separate deleted-neighbour
premise. -/
def S2_pool_cx_unreachableAfterDeleteInputSource_of_boundaryFreeNoThirdGermSource
    (source : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  S2_agent_cv_deleted_neighbor_source_of_localSeparation_20260520
    source.toDeletedNeighborLocalSeparationInputSource

/-- Nonempty form of the CW boundary-free-to-deleted-neighbour eraser. -/
def S2_agent_cw_unreachableAfterDeleteInputSource_nonempty_of_boundaryFreeNoThirdGermSource_20260520
    (source : Nonempty (BoundaryFreeNoThirdGermSource inputs)) :
    Nonempty
      (UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :=
  ⟨(Classical.choice source).toUnreachableAfterDeleteInputSource⟩

/-- Claim `S2-agent-local-component-rows-source-20260520e`.

Sharp local/component row reducer from the actual frontier preconnectedness row
and the same boundary-free no-third-germ local source.  The returned subtype
preserves the local source as data and proves the component-topology field from
the fixed-side local-sector cover derived from that source. -/
def boundaryFreeLocalComponentRows_of_frontierPreconnected_boundaryFreeNoThirdGermSource_20260520e
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (source : BoundaryFreeNoThirdGermSource inputs) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        UnboundedExteriorFrontierComponentTopologySourceRows inputs) where
  val := source
  property :=
    source.toComponentTopologyRowsFromFrontierPreconnected
      (C := C) (inputs := inputs) frontier_preconnected

/-- Claim `S2-agent-local-component-rows-source-20260520e`.

Current finite-drawing topology form of the local/component row reducer.  The
only global topology leaf is
`FiniteDrawingUnboundedComplementFrontierNoClosedSeparation`; the local leaf is
the supplied `BoundaryFreeNoThirdGermSource`. -/
def boundaryFreeLocalComponentRows_of_finiteDrawingNoClosedSeparation_boundaryFreeNoThirdGermSource_20260520e
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (source : BoundaryFreeNoThirdGermSource inputs) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        UnboundedExteriorFrontierComponentTopologySourceRows inputs) where
  val := source
  property :=
    source.toComponentTopologyRowsFromFiniteDrawingNoClosedSeparation
      (C := C) (inputs := inputs) frontier_noClosedSeparation

/-- Family form of
`boundaryFreeLocalComponentRows_of_finiteDrawingNoClosedSeparation_boundaryFreeNoThirdGermSource_20260520e`. -/
def boundaryFreeLocalComponentRows_family_of_finiteDrawingNoClosedSeparation_boundaryFreeNoThirdGermSource_20260520e
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeNoThirdGermSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Subtype
          (fun _ : BoundaryFreeNoThirdGermSource inputs =>
            UnboundedExteriorFrontierComponentTopologySourceRows inputs) := by
  intro m C inputs
  exact
    boundaryFreeLocalComponentRows_of_finiteDrawingNoClosedSeparation_boundaryFreeNoThirdGermSource_20260520e
      (C := C) (inputs := inputs) frontier_noClosedSeparation (source C inputs)

/-- Claim `S2-agent-finite-no-closed-separation-source-20260520f`,
boundary-free local/component form.

The same-`K` Janiszewski boundary-bumping point source supplies the exact
actual-frontier preconnectedness row consumed by the boundary-free local
component reducer; the local leaf remains the supplied
`BoundaryFreeNoThirdGermSource`. -/
def boundaryFreeLocalComponentRows_of_janiszewskiKComponentPointsBetween_boundaryFreeNoThirdGermSource_20260520f
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (source : BoundaryFreeNoThirdGermSource inputs) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        UnboundedExteriorFrontierComponentTopologySourceRows inputs) :=
  boundaryFreeLocalComponentRows_of_frontierPreconnected_boundaryFreeNoThirdGermSource_20260520e
    (C := C) (inputs := inputs)
    (S2_agent_frontier_preconnected_source_for_boundaryFreeReducers_20260520f
      (C := C) inputs points_between)
    source

/-- Family form of
`boundaryFreeLocalComponentRows_of_janiszewskiKComponentPointsBetween_boundaryFreeNoThirdGermSource_20260520f`. -/
def boundaryFreeLocalComponentRows_family_of_janiszewskiKComponentPointsBetween_boundaryFreeNoThirdGermSource_20260520f
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeNoThirdGermSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Subtype
          (fun _ : BoundaryFreeNoThirdGermSource inputs =>
            UnboundedExteriorFrontierComponentTopologySourceRows inputs) := by
  intro m C inputs
  exact
    boundaryFreeLocalComponentRows_of_janiszewskiKComponentPointsBetween_boundaryFreeNoThirdGermSource_20260520f
      (C := C) (inputs := inputs) points_between (source C inputs)

/-- Edge-chain connectivity plus boundary-free no-third-germ rows fill the
component-topology source package. -/
def toComponentTopologyRowsFromEdgeChain
    (source : BoundaryFreeNoThirdGermSource inputs)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  unboundedExteriorFrontierComponentTopologySourceRows_of_edgeChain_neighborPairRows
    (C := C) inputs edge_segment_chain source.toNeighborPairRows

/-- Edge-chain connectivity plus boundary-free no-third-germ rows fill the
input-facing component-topology source package used by W32. -/
def toComponentTopologyInputRowsFromEdgeChain
    (source : BoundaryFreeNoThirdGermSource inputs)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs where
  frontier_preconnected :=
    (source.toComponentTopologyRowsFromEdgeChain edge_segment_chain).frontier_preconnected
  frontier_vertex_incident := source.toFrontierVertexIncidentSource

end BoundaryFreeNoThirdGermSource

/-- Honest local no-third-germ source for the boundary-free S2 row.

This is the non-endpoint-chord source surface: at each actual unbounded
frontier carrier vertex it chooses two selected incident carrier edges, a
local radius, and proves that within that local radius no nearby frontier
point in an incident germ can belong to a third head.  It does not classify an
arbitrary adjacent graph endpoint lying on the frontier far away from the
chosen local neighbourhood. -/
structure BoundaryFreeLocalNoThirdGermSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  left :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Fin n
  right :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Fin n
  left_edge :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs
  right_edge :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs
  heads_ne :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      left a ≠ right a
  radius :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Real
  radius_pos :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      0 < radius a
  local_no_third_germ :
    ∀ (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
      q ∈ Metric.ball ((canonicalGraph C).point a.1) (radius a) →
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε →
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
            (canonicalGraph C).Adj a.1 x →
              q ∈ vertexIncidentGermW3 C a.1 x ε →
                q ≠ (canonicalGraph C).point a.1 →
                  x ≠ left a →
                    x ≠ right a →
                      False

namespace BoundaryFreeLocalNoThirdGermSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- A global `BoundaryFreeNoThirdGermSource` forgets to the honest local
source.  This is a compatibility eraser only; the local source below is the
weaker residual intended for the non-chord route. -/
def ofBoundaryFreeNoThirdGermSource
    (source : BoundaryFreeNoThirdGermSource inputs) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs where
  left := source.left
  right := source.right
  left_edge := source.left_edge
  right_edge := source.right_edge
  heads_ne := source.heads_ne
  radius := fun _ => 1
  radius_pos := by
    intro _a
    exact zero_lt_one
  local_no_third_germ := by
    intro a ε q x _hq_local hqball hqfrontier hadj hgerm hqne hx_left hx_right
    exact
      source.no_third_germ a ε q x hqball hqfrontier hadj hgerm hqne
        hx_left hx_right

/-- Concrete carrier neighbour-pair rows already contain enough local
information for the honest local no-third-germ source.

The radius is the local two-germ radius produced from vertex-star isolation.
If a nearby frontier point lies on one of the two selected germs and also on
a third incident germ, then the common closed-segment point either is an
endpoint, where point injectivity / vertex-not-in-open-segment applies, or is
an interior point of both unit segments, where the same-left uniqueness lemma
identifies the two heads. -/
noncomputable def ofNeighborPairRows
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs := by
  classical
  let twoRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
    S2LocalTwoGermAssembly.localTwoGermRows_of_neighborPairRows
      (C := C) (inputs := inputs) neighborRows
  refine
    { left := fun a => (twoRows a).left
      right := fun a => (twoRows a).right
      left_edge := fun a => (twoRows a).left_edge
      right_edge := fun a => (twoRows a).right_edge
      heads_ne := fun a => (twoRows a).heads_ne
      radius := fun a => Classical.choose (twoRows a).local_two_germ
      radius_pos := ?_
      local_no_third_germ := ?_ }
  · intro a
    exact (Classical.choose_spec (twoRows a).local_two_germ).1
  · intro a ε q x hq_local _hqball hqfrontier hadj hgerm hqne hx_left hx_right
    let row : UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := twoRows a
    have hrow :
        0 < Classical.choose row.local_two_germ ∧
          forall q : PlanarInterface.Point,
            q ∈ Metric.ball ((canonicalGraph C).point a.1)
                (Classical.choose row.local_two_germ) ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                q ∈ vertexIncidentGermW3 C a.1 row.left
                    (Classical.choose row.local_two_germ) ∨
                  q ∈ vertexIncidentGermW3 C a.1 row.right
                    (Classical.choose row.local_two_germ) :=
      Classical.choose_spec row.local_two_germ
    have htwo :
        q ∈ vertexIncidentGermW3 C a.1 row.left
            (Classical.choose row.local_two_germ) ∨
          q ∈ vertexIncidentGermW3 C a.1 row.right
            (Classical.choose row.local_two_germ) :=
      hrow.2 q hq_local hqfrontier
    have hleft_adj : (canonicalGraph C).Adj a.1 row.left := by
      rcases row.left_edge with h | h
      · exact unboundedFrontierEdgeSet_adj h
      · exact canonicalAdj_symm (unboundedFrontierEdgeSet_adj h)
    have hright_adj : (canonicalGraph C).Adj a.1 row.right := by
      rcases row.right_edge with h | h
      · exact unboundedFrontierEdgeSet_adj h
      · exact canonicalAdj_symm (unboundedFrontierEdgeSet_adj h)
    have head_eq_of_common_germ :
        forall {y : Fin n} {η : Real},
          (canonicalGraph C).Adj a.1 y ->
            q ∈ vertexIncidentGermW3 C a.1 y η ->
              x = y := by
      intro y η hyadj hygerm
      rcases hygerm with ⟨_hqball_y, hyseg⟩
      rcases hgerm with ⟨_hqball_x, hxseg⟩
      rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hyseg with
        hy_center | hy_endpoint | hy_open
      · exact False.elim (hqne hy_center)
      · rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hxseg with
          hx_center | hx_endpoint | hx_open
        · exact False.elim (hqne hx_center)
        · have hpoint :
              (canonicalGraph C).point x = (canonicalGraph C).point y := by
            rw [← hx_endpoint, hy_endpoint]
          exact canonical_point_injective C hpoint
        · have hy_point_open :
              PlanarInterface.InOpenSegment ((canonicalGraph C).point y)
                ((canonicalGraph C).point a.1)
                ((canonicalGraph C).point x) := by
            simpa [hy_endpoint] using hx_open
          exact False.elim
            ((graph_vertex_not_inOpenSegment_of_adj
              (C := C) (v := y) hadj) hy_point_open)
      · rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hxseg with
          hx_center | hx_endpoint | hx_open
        · exact False.elim (hqne hx_center)
        · have hx_point_open :
              PlanarInterface.InOpenSegment ((canonicalGraph C).point x)
                ((canonicalGraph C).point a.1)
                ((canonicalGraph C).point y) := by
            simpa [hx_endpoint] using hy_open
          exact False.elim
            ((graph_vertex_not_inOpenSegment_of_adj
              (C := C) (v := x) hyadj) hx_point_open)
        · exact
            (same_left_inOpenSegment_other_endpoint_eq
              (C := C) hyadj hadj hy_open hx_open).symm
    rcases htwo with hleft | hright
    · exact hx_left (by
        simpa [row] using
          (head_eq_of_common_germ hleft_adj hleft))
    · exact hx_right (by
        simpa [row] using
          (head_eq_of_common_germ hright_adj hright))

/-- Local no-third-germ rows give the pointwise local two-germ family.

The proof first shrinks the standard local frontier-star ball by the source
radius.  Thus every noncenter nearby frontier point is assigned to an incident
germ inside the local radius, and the local no-third row rules out every head
except the two selected carrier heads. -/
noncomputable def toLocalTwoGermRows
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  classical
  intro a
  let starRadius : Real :=
    Classical.choose
      (exists_ball_forall_unboundedExterior_frontier_mem_vertexIncidentGermW3
        C inputs a.1)
  have hstarSpec :
      0 < starRadius ∧
        ∀ q : PlanarInterface.Point,
          q ∈ Metric.ball ((canonicalGraph C).point a.1) starRadius →
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
              Exists fun x : Fin n =>
                (canonicalGraph C).Adj a.1 x ∧
                  q ∈ vertexIncidentGermW3 C a.1 x starRadius :=
    Classical.choose_spec
      (exists_ball_forall_unboundedExterior_frontier_mem_vertexIncidentGermW3
        C inputs a.1)
  let localRadius : Real := source.radius a
  let outputRadius : Real := min localRadius starRadius
  have houtput_pos : 0 < outputRadius := by
    exact lt_min (source.radius_pos a) hstarSpec.1
  refine
    { left := source.left a
      right := source.right a
      left_edge := source.left_edge a
      right_edge := source.right_edge a
      heads_ne := source.heads_ne a
      local_two_germ := ?_ }
  refine ⟨outputRadius, houtput_pos, ?_⟩
  intro q hqball hqfrontier
  by_cases hqcenter : q = (canonicalGraph C).point a.1
  · left
    rw [hqcenter]
    exact
      ⟨by
          simpa [Metric.mem_ball] using houtput_pos,
        left_mem_closedSegment _ _⟩
  have hqstar :
      q ∈ Metric.ball ((canonicalGraph C).point a.1) starRadius := by
    rw [Metric.mem_ball] at hqball ⊢
    exact
      lt_of_lt_of_le hqball
        (by simp [outputRadius])
  have hqlocal :
      q ∈ Metric.ball ((canonicalGraph C).point a.1) (source.radius a) := by
    rw [Metric.mem_ball] at hqball ⊢
    exact
      lt_of_lt_of_le hqball
        (by simp [outputRadius, localRadius])
  rcases hstarSpec.2 q hqstar hqfrontier with ⟨x, hadj, hgerm⟩
  by_cases hx_left : x = source.left a
  · left
    rcases hgerm with ⟨_hgerm_ball, hgerm_segment⟩
    exact ⟨hqball, by simpa [hx_left] using hgerm_segment⟩
  by_cases hx_right : x = source.right a
  · right
    rcases hgerm with ⟨_hgerm_ball, hgerm_segment⟩
    exact ⟨hqball, by simpa [hx_right] using hgerm_segment⟩
  exact False.elim
    (source.local_no_third_germ a starRadius q x hqlocal hqstar hqfrontier
      hadj hgerm hqcenter hx_left hx_right)

/-- Local no-third-germ rows give the concrete carrier local-sector rows. -/
noncomputable def toLocalSectorRows
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_localTwoGermRows source.toLocalTwoGermRows

/-- Local no-third-germ rows give the concrete carrier neighbour-pair rows,
with no adjacent endpoint classification. -/
noncomputable def toNeighborPairRows
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a :=
  fun a => (source.toLocalSectorRows a).toNeighborPairAt

/-- Local no-third-germ rows force degree two of the actual frontier carrier.

The proof first forgets the local exterior-star/no-third-germ source to the
checked concrete neighbour-pair rows, then applies the existing degree-two
reducer for `unboundedFrontierCarrierGraph`. -/
theorem toNeighborFinsetCardTwo
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
      unboundedFrontierCarrierGraph_decidableAdj C inputs
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
        2 := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    S2LocalTwoGermAssembly.unboundedFrontierCarrierGraph_neighborFinset_card_two_of_neighborPairRows
      (C := C) inputs source.toNeighborPairRows

/-- Local no-third-germ rows fill the current deleted-neighbour source through
the local-sector eraser, without using endpoint-only/no-chord rows. -/
noncomputable def toUnreachableAfterDeleteInputSource
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  unboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource_of_localSectorRows
    source.toLocalSectorRows

/-- Local no-third-germ rows are exactly the structured version of the
selected-edge/no-third-germ local leaf.

This eraser keeps the two selected heads and their actual
`unboundedFrontierEdgeSet` incidences unchanged; it only repackages the local
radius/no-third-germ row into the existential pointwise source used by the
carrier reducers. -/
noncomputable def toLocalSelectedNoThirdGermSource
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs := by
  intro a
  exact
    Exists.intro (source.left a) <|
      Exists.intro (source.right a) <|
        And.intro (source.left_edge a) <|
          And.intro (source.right_edge a) <|
            And.intro (source.heads_ne a) <|
              Exists.intro (source.radius a) <|
                And.intro (source.radius_pos a)
                  (source.local_no_third_germ a)

/-- Local no-third-germ rows supply the selected-edge incidence row at every
unbounded-frontier graph vertex, through the honest local-sector eraser. -/
noncomputable def toFrontierVertexIncidentSource
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
  frontierVertexIncidentSource_of_neighborPairRows
    (C := C) (inputs := inputs) source.toNeighborPairRows

/-- Edge-chain connectivity plus local no-third-germ rows fill the
component-topology source package without passing through the global
closed-germ source. -/
noncomputable def toComponentTopologyRowsFromEdgeChain
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  unboundedExteriorFrontierComponentTopologySourceRows_of_edgeChain_localSectorRows_fixedSide
    (C := C) inputs edge_segment_chain source.toLocalSectorRows

/-- Edge-chain connectivity plus local no-third-germ rows fill the
input-facing component-topology package used by W32. -/
noncomputable def toComponentTopologyInputRowsFromEdgeChain
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs where
  frontier_preconnected :=
    (source.toComponentTopologyRowsFromEdgeChain edge_segment_chain).frontier_preconnected
  frontier_vertex_incident := source.toFrontierVertexIncidentSource

end BoundaryFreeLocalNoThirdGermSourceRows

set_option linter.style.longLine false in
/-- Claim `S2-current-carrier-degree-two-source-20260520b`.

The actual `unboundedFrontierCarrierGraph` degree-two source is reduced to the
honest local exterior-star/no-third-germ rows.  The selected heads remain
actual `unboundedFrontierEdgeSet` incidences throughout; no induced frontier
graph, arbitrary cycle, endpoint-all-adjacent closure, or synthetic row is
introduced. -/
theorem S2_current_carrier_degree_two_source_20260520b
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
      unboundedFrontierCarrierGraph_decidableAdj C inputs
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
        2 := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    BoundaryFreeLocalNoThirdGermSourceRows.toNeighborFinsetCardTwo
      (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of `S2_current_carrier_degree_two_source_20260520b`. -/
theorem S2_current_carrier_degree_two_source_family_20260520b
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
          unboundedFrontierCarrierGraph_decidableAdj C inputs
        ∀ a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
            2 := by
  intro m C inputs
  exact
    S2_current_carrier_degree_two_source_20260520b
      (C := C) inputs (source C inputs)

/-- Claim `S2-codex-20260520-boundaryfree-local-germ-source`.

The live boundary-free route now reduces to the honest local no-third-germ
source: two selected unbounded-frontier carrier edges at each frontier vertex,
plus a local-radius proof that no nearby frontier point in an incident germ is
carried by a third head.  This deliberately does not classify arbitrary
adjacent frontier endpoint chords. -/
noncomputable def S2_codex_20260520_boundaryfree_local_germ_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
  source.toLocalTwoGermRows

/-- Claim `S2-agent-ct-neighbor-pair-input-source`.

Strict local-star reduction of the concrete carrier neighbour-pair source.
The exact remaining input is the selected exterior carrier-germ source
`BoundaryFreeLocalNoThirdGermSourceRows inputs`: at every actual unbounded
frontier carrier vertex it names two real selected `unboundedFrontierEdgeSet`
edges and supplies a local-radius no-third-germ row.  The proof then uses the
local star-isolation eraser in
`BoundaryFreeLocalNoThirdGermSourceRows.toLocalTwoGermRows`, not an
all-adjacent endpoint/incident source and not the global closed-germ
`BoundaryFreeNoThirdGermSource` as a bare premise. -/
noncomputable def S2_agent_ct_neighbor_pair_input_source_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a :=
  source.toNeighborPairRows

/-- Nonempty form of `S2_agent_ct_neighbor_pair_input_source_20260520`.

This is the exact theorem-shape reduction from `FinitePlanarOuterComponentInputs
C`: it remains only to inhabit the selected local carrier-germ source for that
input package. -/
noncomputable def S2_agent_ct_neighbor_pair_input_source_nonempty_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : Nonempty (BoundaryFreeLocalNoThirdGermSourceRows inputs)) :
    Nonempty
      (∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :=
  ⟨S2_agent_ct_neighbor_pair_input_source_20260520
    (C := C) (inputs := inputs) (Classical.choice source)⟩

/-- Family form of the CT neighbour-pair source reduction. -/
noncomputable def S2_agent_ct_neighbor_pair_input_source_family_20260520
    (source :
      ∀ {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    ∀ {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ∀ a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierNeighborPairAt inputs a := by
  intro m C inputs
  exact
    S2_agent_ct_neighbor_pair_input_source_20260520
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Strict local exterior-topology reduction for the boundary-free no-third
source.

The residual is the selected incident exterior-edge pair row: at each actual
unbounded-frontier vertex it names two genuine incident
`unboundedFrontierEdgeSet` heads and proves every selected incident head is one
of them.  The radius/no-third-germ part is derived from the checked local
incident-germ membership theorem, so this route does not use
unreachable-after-delete, deleted-neighbour separation, or final boundary-cycle
rows as a source. -/
noncomputable def boundaryFreeLocalNoThirdGermSourceRows_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
        inputs) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs := by
  classical
  let localMembership :=
    S2LocalTwoGermAssembly.localIncidentGermFrontierEdgeMembershipRows_of_inputs
      (C := C) inputs
  let radius :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Real :=
    Classical.choose localMembership
  have radiusSpec :
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        0 < radius a) ∧
        forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
            (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
          q ∈ Metric.ball ((canonicalGraph C).point a.1) (radius a) ->
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
    Classical.choose_spec localMembership
  refine
    { left := source.left
      right := source.right
      left_edge := source.left_edge
      right_edge := source.right_edge
      heads_ne := source.heads_ne
      radius := radius
      radius_pos := radiusSpec.1
      local_no_third_germ := ?_ }
  intro a ε q x hq_local hq_eps hq_frontier hadj hgerm hq_center
    hx_left hx_right
  have hedge :
      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
    radiusSpec.2 a ε q x hq_local hq_eps hq_frontier hadj hgerm hq_center
  rcases source.only_selected_incident a x hedge with hx | hx
  · exact hx_left hx
  · exact hx_right hx

set_option linter.style.longLine false in
/-- Selected carrier/geometric-order rows plus the local incident-germ
membership row directly fill the honest local no-third-germ source.

The two named heads and their `unboundedFrontierEdgeSet` incidences are read
from the selected carrier rows.  The no-third-germ field is exactly the
local-radius no-third-germ row obtained from local incident-germ membership,
so this constructor does not pass through all-adjacent endpoint closure,
global closed-germ membership, or an induced frontier graph. -/
noncomputable def
    boundaryFreeLocalNoThirdGermSourceRows_of_selectedNeighborGeometricOrder_localIncident_20260521k6
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (localIncidentRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs := by
  classical
  let localNoThird :
      S2LocalTwoGermAssembly.SelectedNeighborGeometricOrderLocalNoThirdGermRows
        (C := C) (inputs := inputs) selectedRows :=
    S2LocalTwoGermAssembly.selectedNeighborGeometricOrderLocalNoThirdGermRows_of_localIncidentGermMembership
      (C := C) (inputs := inputs) selectedRows localIncidentRows
  let radius :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Real :=
    Classical.choose localNoThird
  have radiusSpec :
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        0 < radius a) ∧
        forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
            (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
          q ∈ Metric.ball ((canonicalGraph C).point a.1) (radius a) ->
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      x ≠ (selectedRows.selectedNeighborRows a).left ->
                        x ≠ (selectedRows.selectedNeighborRows a).right ->
                          False :=
    Classical.choose_spec localNoThird
  refine
    { left := fun a => (selectedRows.selectedNeighborRows a).left
      right := fun a => (selectedRows.selectedNeighborRows a).right
      left_edge := fun a => (selectedRows.selectedNeighborRows a).left_edge
      right_edge := fun a => (selectedRows.selectedNeighborRows a).right_edge
      heads_ne := fun a => (selectedRows.selectedNeighborRows a).heads_ne
      radius := radius
      radius_pos := radiusSpec.1
      local_no_third_germ := ?_ }
  intro a ε q x hq_local hq_eps hq_frontier hadj hgerm hq_center
    hx_left hx_right
  exact
    radiusSpec.2 a ε q x hq_local hq_eps hq_frontier hadj hgerm
      hq_center hx_left hx_right

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeLocalNoThirdGermSourceRows_of_selectedNeighborGeometricOrder_localIncident_20260521k6`. -/
noncomputable def
    boundaryFreeLocalNoThirdGermSourceRowsFamily_of_selectedNeighborGeometricOrder_localIncident_20260521k6
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (localIncidentRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalNoThirdGermSourceRows inputs := by
  intro m C inputs
  exact
    boundaryFreeLocalNoThirdGermSourceRows_of_selectedNeighborGeometricOrder_localIncident_20260521k6
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (localIncidentRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-k6c-local-selected-geometric-source`.

The local boundary-free no-third-germ source is reduced to the selected
carrier/geometric-order rows and the safe local incident-germ membership row.
The selected carrier rows provide the two actual `unboundedFrontierEdgeSet`
heads; the incident-germ row provides the local-radius membership needed to
exclude any third incident germ. -/
noncomputable def S2_k6c_local_selected_geometric_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (localIncidentRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs :=
  boundaryFreeLocalNoThirdGermSourceRows_of_selectedNeighborGeometricOrder_localIncident_20260521k6
    (C := C) (inputs := inputs) selectedRows localIncidentRows

set_option linter.style.longLine false in
/-- Family form of `S2_k6c_local_selected_geometric_source`. -/
noncomputable def S2_k6c_local_selected_geometric_source_family
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (localIncidentRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalNoThirdGermSourceRows inputs := by
  intro m C inputs
  exact
    S2_k6c_local_selected_geometric_source
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (localIncidentRows C inputs)

set_option linter.style.longLine false in
/-- Geometric-selection rows alone fill the honest local no-third-germ source.

The selected-neighbour rows are extracted from the actual geometric-selection
input, and the local incident-germ membership row is the finite-drawing local
isolation theorem.  This is the compact local-source endpoint for the k6
boundary-free branch. -/
noncomputable def
    boundaryFreeLocalNoThirdGermSourceRows_of_geometricSelection_localIncident_20260521k6
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs := by
  let selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs :=
    S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) geometricSelection
  exact
    boundaryFreeLocalNoThirdGermSourceRows_of_selectedNeighborGeometricOrder_localIncident_20260521k6
      (C := C) (inputs := inputs) selectedRows
      (S2LocalTwoGermAssembly.S2_dyn_20260520_incident_germ_global_source_reduced_to_local_radius
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource)

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeLocalNoThirdGermSourceRows_of_geometricSelection_localIncident_20260521k6`. -/
noncomputable def
    boundaryFreeLocalNoThirdGermSourceRowsFamily_of_geometricSelection_localIncident_20260521k6
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalNoThirdGermSourceRows inputs := by
  intro m C inputs
  exact
    boundaryFreeLocalNoThirdGermSourceRows_of_geometricSelection_localIncident_20260521k6
      (C := C) (inputs := inputs) (geometricSelection C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-local-sector-input-source-worker`, sharpened leaf.

The live S2-A source now reduces to the selected incident exterior-edge pair
row.  Composing this theorem with
`BoundaryFreeLocalNoThirdGermSourceRows.toLocalTwoGermRows` and
`localSectorRows_of_localTwoGermRows` gives the scout-confirmed shortest
non-circular local-sector chain. -/
noncomputable def
    S2_dyn_20260520_boundaryFreeLocalNoThirdGermSource_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
        inputs) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs :=
  boundaryFreeLocalNoThirdGermSourceRows_of_selectedIncidentEdgePairRows
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-boundaryfree-local-no-third-germ-source`.

The local boundary-free no-third-germ source reduces to the selected incident
`unboundedFrontierEdgeSet` pair row.  The local radius and incident-germ
frontier-edge membership are supplied internally by
`localIncidentGermFrontierEdgeMembershipRows_of_inputs`, so this does not use
an all-adjacent endpoint closure or endpoint-only no-chord shortcut. -/
noncomputable def
    S2_codex_current_20260520_boundaryfree_local_no_third_germ_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
        inputs) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs :=
  boundaryFreeLocalNoThirdGermSourceRows_of_selectedIncidentEdgePairRows
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_current_20260520_boundaryfree_local_no_third_germ_source`. -/
noncomputable def
    S2_codex_current_20260520_boundaryfree_local_no_third_germ_source_family
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalNoThirdGermSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_current_20260520_boundaryfree_local_no_third_germ_source
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Strict incident-germ reducer for the global boundary-free source.

The selected pair row names the two actual `unboundedFrontierEdgeSet` heads at
each frontier vertex.  The only remaining frontier-topology input is the exact
closed-germ membership row: whenever a noncenter frontier point lies in an
incident W3 germ, that germ's head is joined to the center by an actual
selected frontier edge.  No endpoint-only all-adjacent no-chord classifier,
cycle row, induced frontier graph, or synthetic enclosure is used. -/
def boundaryFreeNoThirdGermSource_of_selectedIncidentEdgePairRows_incidentGermFrontierEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
        inputs)
    (incident_germ_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                    (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeNoThirdGermSource inputs where
  left := source.left
  right := source.right
  left_edge := source.left_edge
  right_edge := source.right_edge
  heads_ne := source.heads_ne
  no_third_germ := by
    intro a ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
    have hedge :
        (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
      incident_germ_frontier_edge a ε q x hqball hqfrontier hadj hgerm
        hqcenter
    rcases source.only_selected_incident a x hedge with hx | hx
    · exact hx_left hx
    · exact hx_right hx

/-- Strict reducer for the bare-input local source leaf.

The direct `FinitePlanarOuterComponentInputs C` theorem is reduced to the
existing cut-partition neighbour-pair input source.  That source is the exact
local-topology payload still missing here: two genuine incident
`unboundedFrontierEdgeSet` edges at each actual unbounded-frontier vertex, plus
the checked no-cut/cut-partition branch for any third carrier neighbour. -/
noncomputable def boundaryFreeLocalNoThirdGermSourceRows_of_neighborPairCutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs :=
  BoundaryFreeLocalNoThirdGermSourceRows.ofNeighborPairRows
    (C := C) (inputs := inputs)
    (S2_agent_frontier_neighbor_pair_input_20260520ax_neighborPairRows
      (C := C) (inputs := inputs) source)

/-- Family source reducer for the local no-third-germ leaf.

The remaining family source is the sharp cut-partition input package: it
selects two actual incident `unboundedFrontierEdgeSet` heads at each frontier
carrier vertex and supplies the no-cut/cut-partition contradiction for every
third carrier neighbour. -/
noncomputable def
    boundaryFreeLocalNoThirdGermSourceRows_family_of_neighborPairCutPartitionInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalNoThirdGermSourceRows inputs := by
  intro m C inputs
  exact
    boundaryFreeLocalNoThirdGermSourceRows_of_neighborPairCutPartitionInputSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q1-boundary-free-no-third-germ-source-20260521q1`,
local source form.

For the source-side local no-third-germ branch, the honest remaining input
leaf is exactly the sharp carrier neighbour cut-partition source: choose two
actual incident `unboundedFrontierEdgeSet` heads at every actual unbounded
frontier vertex, and turn every third concrete carrier neighbour into a
`CutVertexInterface.CutVertexPartition`.  The reverse direction uses the
existing local-sector/deleted-neighbour eraser, so no endpoint-all-adjacent,
induced frontier graph, arbitrary cycle, synthetic enclosure, or W32 facade is
introduced. -/
theorem
    S2_q1_boundary_free_no_third_germ_source_20260521q1_local_nonempty_iff_cutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty (BoundaryFreeLocalNoThirdGermSourceRows inputs) ↔
      Nonempty (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
        C inputs) := by
  constructor
  · rintro ⟨localRows⟩
    exact
      ⟨S2_agent_cutpartition_source_construction_worker_20260521e4
        (C := C) (inputs := inputs)
        localRows.toUnreachableAfterDeleteInputSource⟩
  · rintro ⟨source⟩
    exact
      ⟨boundaryFreeLocalNoThirdGermSourceRows_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- Forward q1 reducer from the sharp neighbour-cut input source to the local
boundary-free no-third-germ source rows. -/
noncomputable def
    S2_q1_boundary_free_no_third_germ_source_20260521q1_local_of_cutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs :=
  boundaryFreeLocalNoThirdGermSourceRows_of_neighborPairCutPartitionInputSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of
`S2_q1_boundary_free_no_third_germ_source_20260521q1_local_of_cutPartitionInputSource`.

The first remaining real input-only theorem is
`forall {m : Nat} (C : _root_.UDConfig m)
  (inputs : FinitePlanarOuterComponentInputs C),
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs`. -/
noncomputable def
    S2_q1_boundary_free_no_third_germ_source_20260521q1_local_family_of_cutPartitionInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalNoThirdGermSourceRows inputs := by
  intro m C inputs
  exact
    S2_q1_boundary_free_no_third_germ_source_20260521q1_local_of_cutPartitionInputSource
      (C := C) (inputs := inputs) (source C inputs)

/-- Family source reducer for the selected-edge/no-third-germ local leaf.

This is the same strict lower cut-partition residual as
`boundaryFreeLocalNoThirdGermSourceRows_family_of_neighborPairCutPartitionInputSource`,
followed only by the structured existential eraser. -/
noncomputable def
    unboundedFrontierCarrierLocalSelectedNoThirdGermSource_family_of_neighborPairCutPartitionInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs := by
  intro m C inputs
  exact
    (boundaryFreeLocalNoThirdGermSourceRows_of_neighborPairCutPartitionInputSource
      (C := C) (inputs := inputs) (source C inputs)).toLocalSelectedNoThirdGermSource

/-- Claim `S2-dyn-20260520-boundaryfree-localTwoGerm-bridge`.

The pointwise boundary-free local two-germ family reduces to the local
no-third-germ source by first packaging it as the existing cut-partition
neighbour-pair input source, then reusing the local source reducer above. -/
noncomputable def S2_dyn_20260520_boundaryfree_localTwoGerm_bridge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs :=
  boundaryFreeLocalNoThirdGermSourceRows_of_neighborPairCutPartitionInputSource
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierNeighborPairCutPartitionInputSource_of_localTwoGermRows
      (C := C) (inputs := inputs) localTwoGermRows)

/-! ### Pointwise local-sector source reductions -/

/-- Claim `S2-codex-20260520-local-sector-source`, local two-germ form.

The requested pointwise local-sector source reduces directly to the honest
boundary-free local two-germ rows at every actual unbounded-frontier carrier
vertex. -/
noncomputable def S2_codex_20260520_local_sector_source_of_localTwoGermRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_localTwoGermRows
    (C := C) (inputs := inputs) localTwoGermRows

/-- Family form of
`S2_codex_20260520_local_sector_source_of_localTwoGermRows`. -/
noncomputable def
    S2_codex_20260520_local_sector_source_family_of_localTwoGermRows
    (localTwoGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    S2_codex_20260520_local_sector_source_of_localTwoGermRows
      (C := C) (inputs := inputs) (localTwoGermRows C inputs)

/-- Claim `S2-codex-20260520-local-sector-source`, neighbour-pair form.

Exact actual-carrier neighbour-pair rows strictly reduce to the pointwise
local-sector source via the checked carrier degree-two/local-sector handoff.
No final boundary cycle, induced frontier graph shortcut, arbitrary cycle,
identity angular-order row, or endpoint all-adjacent closure is used. -/
noncomputable def S2_codex_20260520_local_sector_source_of_neighborPairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2LocalTwoGermAssembly.localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
    (C := C) inputs neighborRows

/-- Family form of
`S2_codex_20260520_local_sector_source_of_neighborPairRows`. -/
noncomputable def
    S2_codex_20260520_local_sector_source_family_of_neighborPairRows
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    S2_codex_20260520_local_sector_source_of_neighborPairRows
      (C := C) (inputs := inputs) (neighborRows C inputs)

/-- Claim `S2-codex-20260520-local-sector-source`, cut-partition row form.

The no-cut cut-partition rows first erase to the exact actual carrier
neighbour-pair rows, then to the pointwise local-sector source.  The only
separation input is the checked third-neighbour cut-partition branch. -/
noncomputable def S2_codex_20260520_local_sector_source_of_cutPartitionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2_codex_20260520_local_sector_source_of_neighborPairRows
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierNeighborPairRows_of_noCutVertex_cutPartitionRows
      (C := C) (inputs := inputs) cutRows)

/-- Family form of
`S2_codex_20260520_local_sector_source_of_cutPartitionRows`. -/
noncomputable def
    S2_codex_20260520_local_sector_source_family_of_cutPartitionRows
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    S2_codex_20260520_local_sector_source_of_cutPartitionRows
      (C := C) (inputs := inputs) (cutRows C inputs)

/-- Claim `S2-codex-20260520-local-sector-source`, cut-partition input form.

This is the object-level strict reduction from a finite-planar input package:
it remains only to produce the sharp actual carrier cut-partition input source
for that same `FinitePlanarOuterComponentInputs C`. -/
noncomputable def
    S2_codex_20260520_local_sector_source_of_cutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2_codex_20260520_local_sector_source_of_cutPartitionRows
    (C := C) (inputs := inputs)
    (S2_agent_frontier_neighbor_pair_input_20260520ax_cutPartitionRows
      (C := C) (inputs := inputs) source)

/-- Claim `S2-codex-20260520-local-sector-source`.

Family-level source reduction for the live pointwise local-sector leaf.  For
every `FinitePlanarOuterComponentInputs C`, the local-sector source is reduced
to the same-input sharp cut-partition carrier source. -/
noncomputable def S2_codex_20260520_local_sector_source
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    S2_codex_20260520_local_sector_source_of_cutPartitionInputSource
      (C := C) (inputs := inputs) (source C inputs)

/-- Deleted-neighbour source form of
`S2_codex_20260520_boundaryfree_local_germ_source`. -/
noncomputable def
    S2_codex_20260520_unreachableAfterDeleteInputSource_of_boundaryfree_local_germ_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  source.toUnreachableAfterDeleteInputSource

/-! ### Honest carrier rows to concrete carrier connectedness -/

/-- An honest exterior-frontier carrier maps into the concrete
`unboundedFrontierCarrierGraph`: its vertex-image row puts every mapped vertex
on the actual unbounded frontier, and its edge-frontier row upgrades every
carrier edge to a selected concrete frontier edge. -/
noncomputable def
    unboundedFrontierCarrierGraphHom_of_exteriorFrontierCarrierRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (K : ExteriorFrontierCarrierRows.{u} C inputs) :
    K.F →g unboundedFrontierCarrierGraph C inputs where
  toFun x :=
    ⟨K.phi x,
      mem_unboundedFrontierVertexSet_iff.2
        ((K.vertex_image_iff_frontier (K.phi x)).2 ⟨x, rfl⟩)⟩
  map_rel' := by
    intro x y hxy
    have hcanonical :
        (canonicalGraph C).Adj (K.phi x) (K.phi y) := by
      exact
        ((canonicalGraph C).adj_iff_unitDistanceAdj (K.phi x) (K.phi y)).2
          (by
            simpa [GraphBridge.UnitDistanceAdj] using K.phi.map_adj hxy)
    rcases hcanonical with hxy_edge | hyx_edge
    · exact
        unboundedFrontierCarrierGraph_adj_of_ordered_edge
          (mem_unboundedFrontierEdgeSet_of_edge_openSegment_frontier
            (C := C) (inputs := inputs) (e := (K.phi x, K.phi y))
            hxy_edge
            (fun p hp => K.edge_openSegment_frontier hxy p hp))
    · exact
        unboundedFrontierCarrierGraph_adj_of_ordered_edge_symm
          (mem_unboundedFrontierEdgeSet_of_edge_openSegment_frontier
            (C := C) (inputs := inputs) (e := (K.phi y, K.phi x))
            hyx_edge
            (fun p hp =>
              K.edge_openSegment_frontier (K.F.symm hxy) p hp))

/-- The honest exterior-frontier carrier map is onto the concrete carrier
vertices because the carrier records exact graph-vertex frontier coverage. -/
theorem unboundedFrontierCarrierGraphHom_of_exteriorFrontierCarrierRows_surjective
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (K : ExteriorFrontierCarrierRows.{u} C inputs) :
    Function.Surjective
      (unboundedFrontierCarrierGraphHom_of_exteriorFrontierCarrierRows
        (C := C) (inputs := inputs) K) := by
  intro a
  have hfrontier :
      (canonicalGraph C).point a.1 ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior :=
    mem_unboundedFrontierVertexSet_iff.1 a.2
  rcases (K.vertex_image_iff_frontier a.1).1 hfrontier with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact Subtype.ext hx

/-- Direct connectedness transfer from genuine exterior-frontier carrier data
to the concrete `unboundedFrontierCarrierGraph`.

This uses no cyclic coverage, no induced graph on all frontier vertices, and no
spanning-cycle extraction: it is just `SimpleGraph.Connected.map` applied to
the honest carrier hom above. -/
theorem unboundedFrontierCarrierGraph_connected_of_exteriorFrontierCarrierRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (K : ExteriorFrontierCarrierRows.{u} C inputs) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  K.connected.map
    (unboundedFrontierCarrierGraphHom_of_exteriorFrontierCarrierRows
      (C := C) (inputs := inputs) K)
    (unboundedFrontierCarrierGraphHom_of_exteriorFrontierCarrierRows_surjective
      (C := C) (inputs := inputs) K)

/-- Nonempty source-row variant of
`unboundedFrontierCarrierGraph_connected_of_exteriorFrontierCarrierRows`. -/
theorem unboundedFrontierCarrierGraph_connected_of_exteriorFrontierCarrierRows_nonempty
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : Nonempty (ExteriorFrontierCarrierRows.{u} C inputs)) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_exteriorFrontierCarrierRows
    (C := C) (inputs := inputs) (Classical.choice rows)

/-- Input-facing incident-only source for the boundary-free no-third-germ row.

This splits the `no_third_germ` obligation into the two concrete ways a point
can lie in a closed incident germ away from the center: either it is the far
endpoint graph vertex, or it lies in the relative interior of that incident
edge.  No boundary cycle or synthetic enclosure is part of this source shape. -/
structure BoundaryFreeIncidentOnlySourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  left :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Fin n
  right :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Fin n
  left_edge :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs
  right_edge :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs
  heads_ne :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      left a ≠ right a
  endpoint_frontier_only :
    ∀ (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (x : Fin n),
      (canonicalGraph C).Adj a.1 x →
        (canonicalGraph C).point x ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior →
          x = left a ∨ x = right a
  openSegment_frontier_only :
    ∀ (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (x : Fin n) (q : PlanarInterface.Point),
      (canonicalGraph C).Adj a.1 x →
        PlanarInterface.InOpenSegment q
          ((canonicalGraph C).point a.1)
          ((canonicalGraph C).point x) →
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
            x = left a ∨ x = right a

namespace BoundaryFreeIncidentOnlySourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- Incident-only endpoint/interior rows erase to the original boundary-free
no-third-germ source. -/
def toBoundaryFreeNoThirdGermSource
    (rows : BoundaryFreeIncidentOnlySourceRows inputs) :
    BoundaryFreeNoThirdGermSource inputs where
  left := rows.left
  right := rows.right
  left_edge := rows.left_edge
  right_edge := rows.right_edge
  heads_ne := rows.heads_ne
  no_third_germ := by
    intro a ε q x _hqball hqfrontier hadj hgerm hqne hx_left hx_right
    rcases hgerm with ⟨_hqball_germ, hqclosed⟩
    rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hqclosed with
      hq_center | hq_endpoint | hq_open
    · exact hqne hq_center
    · rcases
        rows.endpoint_frontier_only a x hadj
          (by simpa [hq_endpoint] using hqfrontier) with
        hx | hx
      · exact hx_left hx
      · exact hx_right hx
    · rcases
        rows.openSegment_frontier_only a x q hadj hq_open hqfrontier with
        hx | hx
      · exact hx_left hx
      · exact hx_right hx

/-- Nonempty wrapper for the incident-only source eraser. -/
def nonemptyBoundaryFreeNoThirdGermSource
    (rows : BoundaryFreeIncidentOnlySourceRows inputs) :
    Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  ⟨rows.toBoundaryFreeNoThirdGermSource⟩

end BoundaryFreeIncidentOnlySourceRows

/-- Standalone eraser from incident-only rows to the boundary-free
no-third-germ source. -/
def boundaryFreeNoThirdGermSource_of_incidentOnlyRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeIncidentOnlySourceRows inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  rows.toBoundaryFreeNoThirdGermSource

/-- Standalone nonempty eraser from incident-only rows to the source shape used
by the S2 boundary-free route. -/
def nonempty_boundaryFreeNoThirdGermSource_of_incidentOnlyRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeIncidentOnlySourceRows inputs) :
    Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  rows.nonemptyBoundaryFreeNoThirdGermSource

/-- Source rows reducing the incident-only local source to the already-used
local-sector row plus the endpoint case.

The open-segment case is automatic from the definition of
`unboundedFrontierEdgeSet`; only a unit neighbor whose endpoint itself lies on
the unbounded frontier remains as an explicit local source row. -/
structure BoundaryFreeEndpointIncidentSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  localSectorRows :
    ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a
  endpoint_frontier_edge :
    ∀ (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (x : Fin n),
      (canonicalGraph C).Adj a.1 x ->
        (canonicalGraph C).point x ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ->
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
            (x, a.1) ∈ unboundedFrontierEdgeSet C inputs

namespace BoundaryFreeEndpointIncidentSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- Constructor form for the endpoint-incident row from the genuinely local
sector family plus the explicit far-endpoint edge-membership residual. -/
def ofLocalSectorRows
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeEndpointIncidentSourceRows inputs where
  localSectorRows := localSectorRows
  endpoint_frontier_edge := endpoint_frontier_edge

/-- Actual-boundary/local-exterior topology supplies exactly the local-sector
part of `BoundaryFreeEndpointIncidentSourceRows`.

The remaining field is intentionally explicit: proving a frontier far endpoint
adjacent to `a` is itself joined to `a` by a selected
`unboundedFrontierEdgeSet` edge is stronger than the local sector theorem. -/
noncomputable def of_actualBoundary_geometricLocalExteriorSector_source
    (source :
      Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
        (forall v : Fin n,
          (canonicalGraph C).point v ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ↔
            Exists fun k : Fin B.length => B.vertex k = v) ∧
        (forall k : Fin B.length,
          forall p : PlanarInterface.Point,
            PlanarInterface.InOpenSegment p
              ((canonicalGraph C).point (B.vertex k))
              ((canonicalGraph C).point
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) ->
            p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) ∧
        (forall k : Fin B.length,
          GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k) ∧
        (forall (k : Fin B.length) (eps : Real) (q : PlanarInterface.Point)
            (x : Fin n),
          q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) eps ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
              (canonicalGraph C).Adj (B.vertex k) x ->
                q ∈ vertexIncidentGermW3 C (B.vertex k) x eps ->
                  q ≠ (canonicalGraph C).point (B.vertex k) ->
                    x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
                      x ≠
                          B.vertex
                            (PlanarInterface.cyclicSucc B.length_pos k) ->
                        BoundaryPredSuccPointAngularBetween C B k q))
    (endpoint_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeEndpointIncidentSourceRows inputs :=
  ofLocalSectorRows
    (C := C) (inputs := inputs)
    (S2LocalTwoGermAssembly.localSectorRows_of_actualBoundary_geometricLocalExteriorSector_source
      (C := C) (inputs := inputs) source)
    endpoint_frontier_edge

/-- An actual boundary cycle plus the endpoint-only no-chord row closes the
far-endpoint frontier-edge field in `BoundaryFreeEndpointIncidentSourceRows`.

The proof first identifies the frontier vertex `a` with a boundary index.  If
the adjacent frontier endpoint is the predecessor or successor supplied by the
endpoint-only row, the corresponding consecutive boundary side is already an
actual selected edge of `unboundedFrontierEdgeSet` by
`ActualBoundaryCycleFrontierEquivalenceRows`. -/
theorem endpoint_frontier_edge_of_actualBoundaryRows_endpointIncidentOnly
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
        actualRows.boundary) :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (x : Fin n),
      (canonicalGraph C).Adj a.1 x ->
        (canonicalGraph C).point x ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ->
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
            (x, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
  intro a x hadj hxfrontier
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    actualRows.boundary
  have ha_frontier :
      (canonicalGraph C).point a.1 ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior :=
    mem_unboundedFrontierVertexSet_iff.1 a.2
  rcases (actualRows.frontier_iff_cycle_vertex a.1).1 ha_frontier with
    ⟨k, hk⟩
  have hadj_boundary :
      (canonicalGraph C).Adj (B.vertex k) x := by
    simpa [B, hk] using hadj
  rcases endpoint_incident_only k x hxfrontier hadj_boundary with
    hx_pred | hx_succ
  · let pred : Fin B.length := PlanarInterface.cyclicPred B.length_pos k
    have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
      dsimp [pred]
      exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
    have hedge := actualRows.cycle_edge_mem_unboundedFrontierEdgeSet_or_symm pred
    rcases hedge with hforward | hbackward
    · right
      simpa [B, pred, hsucc_pred, hk, hx_pred] using hforward
    · left
      simpa [B, pred, hsucc_pred, hk, hx_pred] using hbackward
  · have hedge := actualRows.cycle_edge_mem_unboundedFrontierEdgeSet_or_symm k
    rcases hedge with hforward | hbackward
    · left
      simpa [B, hk, hx_succ] using hforward
    · right
      simpa [B, hk, hx_succ] using hbackward

/-- Actual boundary-cycle rows plus the endpoint-only no-chord row give the
primitive incident selected-edge source for adjacent exterior-frontier
endpoints. -/
theorem adjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource_of_actualBoundaryRows_endpointIncidentOnly
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
        actualRows.boundary) :
    AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs := by
  intro i j hij hifrontier hjfrontier
  let a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨i, mem_unboundedFrontierVertexSet_iff.2 hifrontier⟩
  exact
    endpoint_frontier_edge_of_actualBoundaryRows_endpointIncidentOnly
      (C := C) (inputs := inputs) actualRows endpoint_incident_only
      a j hij hjfrontier

/-- Actual boundary-cycle rows plus the endpoint-only no-chord row give the
endpoint closed-segment closure source via the primitive incident selected
edge source. -/
theorem closedSegmentEndpointClosureSource_of_actualBoundaryRows_endpointIncidentOnly
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
        actualRows.boundary) :
    AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs :=
  closedSegmentEndpointClosureSource_of_incidentUnboundedFrontierEdgeSource
    (C := C) (inputs := inputs)
    (adjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource_of_actualBoundaryRows_endpointIncidentOnly
      (C := C) (inputs := inputs) actualRows endpoint_incident_only)

/-- Actual boundary-cycle rows, primitive boundary-sector rows, and the
endpoint-only no-chord row fill the endpoint-incident source package.

This is the owner-file reducer for the current S2-B target: the local-sector
field comes from the supplied boundary-sector rows, and the endpoint closure is
the theorem above. -/
noncomputable def of_actualBoundaryRows_endpointIncidentOnly
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (sectorRows :
      forall k : Fin actualRows.boundary.length,
        BoundaryVertexExteriorSectorRowsAt inputs actualRows.boundary k)
    (endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
        actualRows.boundary) :
    BoundaryFreeEndpointIncidentSourceRows inputs :=
  ofLocalSectorRows
    (C := C) (inputs := inputs)
    (S2LocalTwoGermAssembly.localSectorRows_of_boundaryVertexExteriorSectorRows
      (C := C) (inputs := inputs)
      actualRows.boundary actualRows.frontier_iff_cycle_vertex sectorRows)
    (endpoint_frontier_edge_of_actualBoundaryRows_endpointIncidentOnly
      (C := C) (inputs := inputs) actualRows endpoint_incident_only)

/-- Actual boundary-cycle rows, pointwise local-sector rows, and the
endpoint-only no-chord row fill the endpoint-incident source package.

This is the input-facing local-sector form: once another source has already
proved the concrete carrier local-sector rows, `actualRows` and the
endpoint-only row supply exactly the remaining far-endpoint frontier-edge
closure through the checked endpoint reducer. -/
noncomputable def of_actualBoundaryRows_localSector_endpointIncidentOnly
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
        actualRows.boundary) :
    BoundaryFreeEndpointIncidentSourceRows inputs :=
  ofLocalSectorRows
    (C := C) (inputs := inputs)
    localSectorRows
    (endpoint_frontier_edge_of_actualBoundaryRows_endpointIncidentOnly
      (C := C) (inputs := inputs) actualRows endpoint_incident_only)

/-- Nonempty wrapper for the actual-boundary/local-sector endpoint-incident
source reducer. -/
def nonempty_of_actualBoundaryRows_localSector_endpointIncidentOnly
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
        actualRows.boundary) :
    Nonempty (BoundaryFreeEndpointIncidentSourceRows inputs) :=
  ⟨of_actualBoundaryRows_localSector_endpointIncidentOnly
    (C := C) (inputs := inputs)
    actualRows localSectorRows endpoint_incident_only⟩

/-- Endpoint-incident rows plus local-sector rows give the incident-only
source package. -/
def toIncidentOnlyRows
    (rows : BoundaryFreeEndpointIncidentSourceRows inputs) :
    BoundaryFreeIncidentOnlySourceRows inputs where
  left := fun a => (rows.localSectorRows a).left
  right := fun a => (rows.localSectorRows a).right
  left_edge := fun a => (rows.localSectorRows a).left_edge
  right_edge := fun a => (rows.localSectorRows a).right_edge
  heads_ne := fun a => (rows.localSectorRows a).heads_ne
  endpoint_frontier_only := by
    intro a x hadj hxfrontier
    let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
      ⟨x, mem_unboundedFrontierVertexSet_iff.2 hxfrontier⟩
    have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
      exact (unboundedFrontierCarrierGraph_adj_iff).2
        (rows.endpoint_frontier_edge a x hadj hxfrontier)
    exact (rows.localSectorRows a).only b hadjCarrier
  openSegment_frontier_only := by
    intro a x q hadj hqopen hqfrontier
    have hsource :
        InteriorFrontierEdgeCarrierMembershipSource C inputs :=
      interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
    rcases hadj with hadj_uv | hadj_vu
    · have hmem :
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs :=
        hsource (e := (a.1, x)) (p := q) hadj_uv hqopen hqfrontier
      have hx :
          x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
          hmem).2
      let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} := ⟨x, hx⟩
      have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
        exact (unboundedFrontierCarrierGraph_adj_iff).2 (Or.inl hmem)
      exact (rows.localSectorRows a).only b hadjCarrier
    · have hmem :
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
        hsource (e := (x, a.1)) (p := q)
          hadj_vu (inOpenSegment_symm hqopen) hqfrontier
      have hx :
          x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
          hmem).1
      let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} := ⟨x, hx⟩
      have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
        exact (unboundedFrontierCarrierGraph_adj_iff).2 (Or.inr hmem)
      exact (rows.localSectorRows a).only b hadjCarrier

/-- Endpoint-incident rows erase to the boundary-free no-third-germ source. -/
def toBoundaryFreeNoThirdGermSource
    (rows : BoundaryFreeEndpointIncidentSourceRows inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  rows.toIncidentOnlyRows.toBoundaryFreeNoThirdGermSource

/-- Endpoint-incident rows erase to the incident-only source using an explicit
interior-edge carrier membership source for the open-segment branch.

This variant is useful for input-level routes that want to keep the local
edge-side topology source visible instead of using the fixed-side theorem
hidden in `toIncidentOnlyRows`. -/
def toIncidentOnlyRowsWithInteriorEdgeMem
    (rows : BoundaryFreeEndpointIncidentSourceRows inputs)
    (interior_edge_mem :
      InteriorFrontierEdgeCarrierMembershipSource C inputs) :
    BoundaryFreeIncidentOnlySourceRows inputs where
  left := fun a => (rows.localSectorRows a).left
  right := fun a => (rows.localSectorRows a).right
  left_edge := fun a => (rows.localSectorRows a).left_edge
  right_edge := fun a => (rows.localSectorRows a).right_edge
  heads_ne := fun a => (rows.localSectorRows a).heads_ne
  endpoint_frontier_only := by
    intro a x hadj hxfrontier
    let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
      ⟨x, mem_unboundedFrontierVertexSet_iff.2 hxfrontier⟩
    have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
      exact (unboundedFrontierCarrierGraph_adj_iff).2
        (rows.endpoint_frontier_edge a x hadj hxfrontier)
    exact (rows.localSectorRows a).only b hadjCarrier
  openSegment_frontier_only := by
    intro a x q hadj hqopen hqfrontier
    rcases hadj with hadj_uv | hadj_vu
    · have hmem :
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs :=
        interior_edge_mem (e := (a.1, x)) (p := q)
          hadj_uv hqopen hqfrontier
      have hx :
          x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
          hmem).2
      let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} := ⟨x, hx⟩
      have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
        exact (unboundedFrontierCarrierGraph_adj_iff).2 (Or.inl hmem)
      exact (rows.localSectorRows a).only b hadjCarrier
    · have hmem :
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
        interior_edge_mem (e := (x, a.1)) (p := q)
          hadj_vu (inOpenSegment_symm hqopen) hqfrontier
      have hx :
          x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
          hmem).1
      let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} := ⟨x, hx⟩
      have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
        exact (unboundedFrontierCarrierGraph_adj_iff).2 (Or.inr hmem)
      exact (rows.localSectorRows a).only b hadjCarrier

/-- Endpoint-incident rows erase to the boundary-free no-third-germ source
through a caller-supplied interior-edge carrier source. -/
def toBoundaryFreeNoThirdGermSourceWithInteriorEdgeMem
    (rows : BoundaryFreeEndpointIncidentSourceRows inputs)
    (interior_edge_mem :
      InteriorFrontierEdgeCarrierMembershipSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  (rows.toIncidentOnlyRowsWithInteriorEdgeMem
    (C := C) (inputs := inputs) interior_edge_mem).toBoundaryFreeNoThirdGermSource

/-- Actual boundary-sector rows plus the endpoint-frontier incident closure
give the boundary-free no-third-germ source.

This is only the bridge: sector rows supply the local-sector family, endpoint
closure completes `BoundaryFreeEndpointIncidentSourceRows`, and the existing
eraser gives the final no-third-germ source. -/
noncomputable def
    boundaryFreeNoThirdGermSource_of_boundaryVertexExteriorSectorRows_endpointFrontier
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k)
    (endpoint_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  (BoundaryFreeEndpointIncidentSourceRows.ofLocalSectorRows
    (C := C) (inputs := inputs)
    (S2LocalTwoGermAssembly.localSectorRows_of_boundaryVertexExteriorSectorRows
      (C := C) (inputs := inputs) B frontier_iff_cycle_vertex sectorRows)
    endpoint_frontier_edge).toBoundaryFreeNoThirdGermSource

set_option linter.style.longLine false in
/-- Boundary-sector rows plus the honest adjacent-endpoint selected-edge
source give the boundary-free no-third-germ source.

The sector rows supply the two local exterior carrier germs at each frontier
vertex.  The adjacent-endpoint source supplies exactly the endpoint branch:
if a graph neighbour is itself on the unbounded exterior frontier, then the
edge between the two frontier vertices is a selected unbounded-frontier edge.
-/
noncomputable def
    boundaryFreeNoThirdGermSource_of_boundaryVertexExteriorSectorRows_adjacentIncident
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k)
    (adjacent_incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_boundaryVertexExteriorSectorRows_endpointFrontier
    (C := C) (inputs := inputs) B frontier_iff_cycle_vertex sectorRows
    (fun a _x hadj hxfrontier =>
      adjacent_incident_edge hadj
        (mem_unboundedFrontierVertexSet_iff.1 a.2) hxfrontier)

/-- Nonempty wrapper for the endpoint-incident source eraser. -/
def nonemptyBoundaryFreeNoThirdGermSource
    (rows : BoundaryFreeEndpointIncidentSourceRows inputs) :
    Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  ⟨rows.toBoundaryFreeNoThirdGermSource⟩

end BoundaryFreeEndpointIncidentSourceRows

/-- Nonempty endpoint-incident rows erase to the boundary-free no-third-germ
source. -/
def nonempty_boundaryFreeNoThirdGermSource_of_nonempty_endpointIncidentRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : Nonempty (BoundaryFreeEndpointIncidentSourceRows inputs)) :
    Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  (Classical.choice rows).nonemptyBoundaryFreeNoThirdGermSource

set_option linter.style.longLine false in
/-- Input-facing endpoint/local-sector row from actual-boundary rows.

The three source rows are intentionally primitive and non-duplicated:
`actualRows` identifies the concrete boundary cycle, `localSectorRows` supplies
the pointwise carrier local-sector row, and `endpoint_incident_only` closes the
far-endpoint branch.  The result is exactly the endpoint-incident source
consumed by the selected raw-orbit reducers. -/
def endpointIncidentSourceRows_nonempty_of_actualBoundaryRows_localSector_endpointIncidentOnly
    (actualRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_incident_only :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
            (actualRows C inputs).boundary) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Nonempty (BoundaryFreeEndpointIncidentSourceRows inputs) :=
  fun C inputs =>
    BoundaryFreeEndpointIncidentSourceRows.nonempty_of_actualBoundaryRows_localSector_endpointIncidentOnly
      (C := C) (inputs := inputs)
      (actualRows C inputs)
      (localSectorRows C inputs)
      (endpoint_incident_only C inputs)

/-- Input-facing family reducer for the S2-B local source.

The remaining proof obligation is exactly the endpoint-incident source row:
local-sector rows at each unbounded-frontier vertex, plus the far-endpoint
frontier-edge closure. -/
def boundaryFreeNoThirdGermSource_nonempty_of_endpointIncidentRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeEndpointIncidentSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  fun C inputs =>
    (rows C inputs).nonemptyBoundaryFreeNoThirdGermSource

/-- Input-facing family reducer exposing the two primitive local rows still
needed for `BoundaryFreeNoThirdGermSource`.

The open-segment branch is discharged by the existing local-sector eraser and
frontier-edge membership source; only local sectors and endpoint frontier-edge
closure remain as inputs. -/
def boundaryFreeNoThirdGermSource_nonempty_of_localSectorRows_endpointFrontier
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_frontier_edge :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs})
            (x : Fin m),
            (canonicalGraph C).Adj a.1 x ->
              (canonicalGraph C).point x ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                  (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  boundaryFreeNoThirdGermSource_nonempty_of_endpointIncidentRows
    (fun C inputs =>
      BoundaryFreeEndpointIncidentSourceRows.ofLocalSectorRows
        (C := C) (inputs := inputs)
        (localSectorRows C inputs)
        (endpoint_frontier_edge C inputs))

/-- Object-level local reducer for the boundary-free no-third-germ source.

This is the direct local-star/two-germ route: pointwise local-sector rows rule
out third open-segment germs via the checked carrier-local eraser, while the
endpoint frontier-edge row closes the far-endpoint branch.  It does not
construct actual boundary-cycle rows, exterior cycle rows, carrier rows, or a
W32 target. -/
def boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
    (BoundaryFreeEndpointIncidentSourceRows.ofLocalSectorRows
    (C := C) (inputs := inputs)
    localSectorRows endpoint_frontier_edge).toBoundaryFreeNoThirdGermSource

set_option linter.style.longLine false in
/-- Correct selected-edge-only residual for pointwise local-sector rows.

This row only talks about actual selected `unboundedFrontierEdgeSet` incidences.
It is therefore insensitive to boundary chords whose endpoints happen to lie on
the exterior frontier but whose open edge is not part of the selected exterior
frontier carrier. -/
abbrev BoundaryFreeSelectedEdgeOnlyForLocalSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    Prop :=
  forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
    (x : Fin n),
    (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs →
      x = (localSectorRows a).left ∨
        x = (localSectorRows a).right

set_option linter.style.longLine false in
/-- Local-sector rows already prove the corrected selected-edge-only residual.

The proof converts the selected edge to an adjacency in the concrete
`unboundedFrontierCarrierGraph`; the local-sector `only` field then identifies
the head with one of the two selected carrier neighbours. -/
theorem boundaryFreeSelectedEdgeOnlyForLocalSectorRows_of_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    BoundaryFreeSelectedEdgeOnlyForLocalSectorRows
      (C := C) (inputs := inputs) localSectorRows := by
  intro a x hedge
  have hxmem : x ∈ unboundedFrontierVertexSet C inputs := by
    let hwhole :
        UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
      unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
    rcases hedge with hedge | hedge
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole hedge).2
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole hedge).1
  let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨x, hxmem⟩
  have hab : (unboundedFrontierCarrierGraph C inputs).Adj a b :=
    (unboundedFrontierCarrierGraph_adj_iff).2 hedge
  simpa [b] using (localSectorRows a).only b hab

set_option linter.style.longLine false in
/-- Forget local-sector rows to the pure selected incident-edge pair source.

This is the corrected source row for the endpoint audit: it asks only about
actual selected carrier edges, and leaves arbitrary adjacent frontier endpoints
out of the local proof obligation. -/
def localSelectedIncidentEdgePairSourceRows_of_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
      inputs where
  left := fun a => (localSectorRows a).left
  right := fun a => (localSectorRows a).right
  left_edge := fun a => (localSectorRows a).left_edge
  right_edge := fun a => (localSectorRows a).right_edge
  heads_ne := fun a => (localSectorRows a).heads_ne
  only_selected_incident :=
    boundaryFreeSelectedEdgeOnlyForLocalSectorRows_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows

set_option linter.style.longLine false in
/-- Local-sector rows plus actual incident-germ selected-edge membership close
the global boundary-free source.

This is the source leaf for the boundary-free route: local-sector rows name the
two selected carrier heads, and the incident-germ row proves that any noncenter
frontier point in a closed incident germ is carried by an actual selected
`unboundedFrontierEdgeSet` edge.  No all-adjacent frontier endpoint classifier
or endpoint-closure shortcut is used. -/
def boundaryFreeNoThirdGermSource_of_localSectorRows_incidentGermFrontierEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (incident_germ_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                    (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_selectedIncidentEdgePairRows_incidentGermFrontierEdge
    (C := C) (inputs := inputs)
    (localSelectedIncidentEdgePairSourceRows_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows)
    incident_germ_frontier_edge

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-boundaryfree-source-leaf`.

The current boundary-free source is reduced to selected carrier local-sector
rows plus the honest incident-germ frontier-edge membership row.  The selected
edge completeness used in the proof comes only from the actual local-sector
carrier data. -/
def S2_codex_current_20260520_boundaryfree_source_leaf
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (incident_germ_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                    (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_localSectorRows_incidentGermFrontierEdge
    (C := C) (inputs := inputs) localSectorRows incident_germ_frontier_edge

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_current_20260520_boundaryfree_source_leaf`. -/
def S2_codex_current_20260520_boundaryfree_source_leaf_family
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (incident_germ_frontier_edge :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin m),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeNoThirdGermSource inputs := by
  intro m C inputs
  exact
    S2_codex_current_20260520_boundaryfree_source_leaf
      (C := C) (inputs := inputs)
      (localSectorRows C inputs) (incident_germ_frontier_edge C inputs)

set_option linter.style.longLine false in
/-- Local-sector rows give the honest local no-third-germ source.

The global closed-germ endpoint case is deliberately not produced here.  The
local-radius theorem first shrinks away far endpoints; inside that radius,
frontier points in incident germs are promoted only through actual selected
`unboundedFrontierEdgeSet` membership or open-segment frontier witnesses. -/
noncomputable def boundaryFreeLocalNoThirdGermSourceRows_of_localSectorRows_selectedEdges
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    BoundaryFreeLocalNoThirdGermSourceRows inputs :=
  boundaryFreeLocalNoThirdGermSourceRows_of_selectedIncidentEdgePairRows
    (C := C) (inputs := inputs)
    (localSelectedIncidentEdgePairSourceRows_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows)

set_option linter.style.longLine false in
/-- Endpoint-only/no-chord implies the honest endpoint-frontier selected-edge
row, but the endpoint-only premise itself is not a finite-input theorem in the
presence of boundary chords. -/
theorem endpoint_frontier_edge_of_localSectorRows_endpointOnly
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x = (localSectorRows a).left ∨
              x = (localSectorRows a).right) :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (x : Fin n),
      (canonicalGraph C).Adj a.1 x ->
        (canonicalGraph C).point x ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ->
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
            (x, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
  intro a x hadj hxfrontier
  rcases endpoint_only a x hadj hxfrontier with hx | hx
  · simpa [hx] using (localSectorRows a).left_edge
  · simpa [hx] using (localSectorRows a).right_edge

/- The local-sector/endpoint-only reducers below are retained as compatibility
bridges.  Their endpoint premise is a no-chord statement for all adjacent
frontier endpoints, so it is too strong to use as a bare
`FinitePlanarOuterComponentInputs` residual when boundary chords are allowed.
Use `boundaryFreeLocalNoThirdGermSourceRows_of_localSectorRows_selectedEdges`
for the endpoint-free local route, or the endpoint-frontier selected-edge row
when a global `BoundaryFreeNoThirdGermSource` is genuinely needed. -/
def boundaryFreeIncidentOnlyRows_of_localSectorRows_endpointOnly
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x = (localSectorRows a).left ∨
              x = (localSectorRows a).right) :
    BoundaryFreeIncidentOnlySourceRows inputs where
  left := fun a => (localSectorRows a).left
  right := fun a => (localSectorRows a).right
  left_edge := fun a => (localSectorRows a).left_edge
  right_edge := fun a => (localSectorRows a).right_edge
  heads_ne := fun a => (localSectorRows a).heads_ne
  endpoint_frontier_only := endpoint_only
  openSegment_frontier_only := by
    intro a x q hadj hqopen hqfrontier
    have hsource :
        InteriorFrontierEdgeCarrierMembershipSource C inputs :=
      interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
    rcases hadj with hadj_uv | hadj_vu
    · have hmem :
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs :=
        hsource (e := (a.1, x)) (p := q) hadj_uv hqopen hqfrontier
      have hx :
          x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
          hmem).2
      let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} := ⟨x, hx⟩
      have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
        exact (unboundedFrontierCarrierGraph_adj_iff).2 (Or.inl hmem)
      simpa [b] using (localSectorRows a).only b hadjCarrier
    · have hmem :
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
        hsource (e := (x, a.1)) (p := q)
          hadj_vu (inOpenSegment_symm hqopen) hqfrontier
      have hx :
          x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
          hmem).1
      let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} := ⟨x, hx⟩
      have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
        exact (unboundedFrontierCarrierGraph_adj_iff).2 (Or.inr hmem)
      simpa [b] using (localSectorRows a).only b hadjCarrier

/-- Compatibility bridge from local-sector rows plus endpoint-only/no-chord to
the boundary-free no-third-germ source.

The endpoint-only premise is too strong as a bare finite-input residual when
boundary chords are allowed.  The proof first converts that premise to the
honest endpoint selected-edge row and then uses the endpoint-frontier reducer. -/
def boundaryFreeNoThirdGermSource_of_localSectorRows_endpointOnly
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x = (localSectorRows a).left ∨
              x = (localSectorRows a).right) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier
    (C := C) (inputs := inputs)
    localSectorRows
    (endpoint_frontier_edge_of_localSectorRows_endpointOnly
      (C := C) (inputs := inputs) localSectorRows endpoint_only)

/-- Compatibility selected-local-source reducer for
`BoundaryFreeNoThirdGermSource`.

The local selected no-third-germ source supplies the actual local-sector rows,
including the two selected `unboundedFrontierEdgeSet` heads.  The endpoint-only
premise is not claimed from `FinitePlanarOuterComponentInputs`; use the local
selected-edge source above for the endpoint-free local route. -/
noncomputable def
    S2_boundaryFreeNoThirdGermSource_of_localSelectedNoThirdGermSource_endpointOnly_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSource :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs)
    (endpoint_only :
      let localSectorRows :=
        unboundedFrontierCarrierLocalSectorRows_of_localSelectedNoThirdGermSource
          (C := C) (inputs := inputs) localSource
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x = (localSectorRows a).left ∨
              x = (localSectorRows a).right) :
    BoundaryFreeNoThirdGermSource inputs := by
  let localSectorRows :=
    unboundedFrontierCarrierLocalSectorRows_of_localSelectedNoThirdGermSource
      (C := C) (inputs := inputs) localSource
  exact
    boundaryFreeNoThirdGermSource_of_localSectorRows_endpointOnly
      (C := C) (inputs := inputs) localSectorRows endpoint_only

/-- Nonempty wrapper for the selected-local-source endpoint-only reducer. -/
noncomputable def
    nonempty_boundaryFreeNoThirdGermSource_of_localSelectedNoThirdGermSource_endpointOnly_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSource :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs)
    (endpoint_only :
      let localSectorRows :=
        unboundedFrontierCarrierLocalSectorRows_of_localSelectedNoThirdGermSource
          (C := C) (inputs := inputs) localSource
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x = (localSectorRows a).left ∨
              x = (localSectorRows a).right) :
    Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  ⟨S2_boundaryFreeNoThirdGermSource_of_localSelectedNoThirdGermSource_endpointOnly_20260520
    (C := C) (inputs := inputs) localSource endpoint_only⟩

/-- Local two-germ rows plus endpoint selected-edge closure erase directly to
the boundary-free no-third-germ source.

This is the local-two-germ companion to
`boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier`: the
two-germ rows already contain the local-sector row after forgetting the
smaller germ witness, while the endpoint row closes the far-endpoint branch. -/
def boundaryFreeNoThirdGermSource_of_localTwoGermRows_endpointFrontier
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a)
    (endpoint_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier
    (C := C) (inputs := inputs)
    (localSectorRows_of_localTwoGermRows localTwoGermRows)
    endpoint_frontier_edge

/-- Adjacent endpoint incident selected-edge rows close the endpoint branch of
the local-two-germ boundary-free source. -/
def boundaryFreeNoThirdGermSource_of_localTwoGermRows_incidentEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_localTwoGermRows_endpointFrontier
    (C := C) (inputs := inputs)
    localTwoGermRows
    (fun a _x hadj hxfrontier =>
      incident_edge hadj (mem_unboundedFrontierVertexSet_iff.1 a.2) hxfrontier)

/-- Local-sector rows plus endpoint frontier-edge closure erase to the
boundary-free source, with the open-edge branch supplied by an explicit
interior carrier-membership row. -/
def boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier_interiorEdgeMem
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (interior_edge_mem :
      InteriorFrontierEdgeCarrierMembershipSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  (BoundaryFreeEndpointIncidentSourceRows.ofLocalSectorRows
    (C := C) (inputs := inputs)
    localSectorRows endpoint_frontier_edge).toBoundaryFreeNoThirdGermSourceWithInteriorEdgeMem
      (C := C) (inputs := inputs) interior_edge_mem

/-- Concrete carrier neighbour-pair rows plus endpoint selected-edge closure
give the boundary-free no-third-germ source.

This is the neighbour-pair version of
`boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier`: the local
sector family is recovered from the two actual carrier neighbours at each
unbounded-frontier vertex, while the endpoint row handles adjacent frontier
endpoints. -/
def boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointFrontier
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (endpoint_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier
    (C := C) (inputs := inputs)
    (S2LocalTwoGermAssembly.localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
      (C := C) inputs neighborRows)
    endpoint_frontier_edge

/-- Incident selected frontier-edge rows are enough for the endpoint branch of
the neighbour-pair boundary-free source. -/
def boundaryFreeNoThirdGermSource_of_neighborPairRows_incidentEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointFrontier
    (C := C) (inputs := inputs)
    neighborRows
    (fun a _x hadj hxfrontier =>
      incident_edge hadj (mem_unboundedFrontierVertexSet_iff.1 a.2) hxfrontier)

/-- Incident-only rows from the concrete carrier neighbour-pair source and a
sharp endpoint-only row.

The endpoint row is deliberately not the universal adjacent-endpoint incident
edge shortcut: it says only that an adjacent frontier endpoint is one of the
two selected concrete carrier neighbours.  The open-segment branch is then
forced by `interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point`,
so boundary chords between frontier vertices are not silently promoted to
exterior-frontier carrier edges. -/
def boundaryFreeIncidentOnlyRows_of_neighborPairRows_endpointOnly
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x = (neighborRows a).left.1 ∨
              x = (neighborRows a).right.1) :
    BoundaryFreeIncidentOnlySourceRows inputs where
  left := fun a => (neighborRows a).left.1
  right := fun a => (neighborRows a).right.1
  left_edge := by
    intro a
    let P : UnboundedFrontierCarrierNeighborPairAt inputs a := neighborRows a
    have hleft_adj : (unboundedFrontierCarrierGraph C inputs).Adj a P.left :=
      (P.neighbor_iff P.left).2 (Or.inl rfl)
    simpa [P] using (unboundedFrontierCarrierGraph_adj_iff).1 hleft_adj
  right_edge := by
    intro a
    let P : UnboundedFrontierCarrierNeighborPairAt inputs a := neighborRows a
    have hright_adj : (unboundedFrontierCarrierGraph C inputs).Adj a P.right :=
      (P.neighbor_iff P.right).2 (Or.inr rfl)
    simpa [P] using (unboundedFrontierCarrierGraph_adj_iff).1 hright_adj
  heads_ne := by
    intro a h
    exact (neighborRows a).left_ne_right (Subtype.ext h)
  endpoint_frontier_only := by
    intro a x hadj hxfrontier
    exact endpoint_only a x hadj hxfrontier
  openSegment_frontier_only := by
    intro a x q hadj hqopen hqfrontier
    have hsource :
        InteriorFrontierEdgeCarrierMembershipSource C inputs :=
      interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
    have hcarrier :
        (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
      rcases hadj with hadj_uv | hadj_vu
      · left
        exact hsource (e := (a.1, x)) (p := q)
          hadj_uv hqopen hqfrontier
      · right
        exact hsource (e := (x, a.1)) (p := q)
          hadj_vu (inOpenSegment_symm hqopen) hqfrontier
    have hxmem : x ∈ unboundedFrontierVertexSet C inputs := by
      let hwhole :
          UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
        unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
      rcases hcarrier with hcarrier | hcarrier
      · exact
          (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
            hwhole hcarrier).2
      · exact
          (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
            hwhole hcarrier).1
    let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
      ⟨x, hxmem⟩
    have hab : (unboundedFrontierCarrierGraph C inputs).Adj a b :=
      (unboundedFrontierCarrierGraph_adj_iff).2 hcarrier
    have hb : b = (neighborRows a).left ∨ b = (neighborRows a).right :=
      ((neighborRows a).neighbor_iff b).1 hab
    rcases hb with hb | hb
    · left
      simpa [b] using congrArg Subtype.val hb
    · right
      simpa [b] using congrArg Subtype.val hb

/-- Boundary-free no-third-germ source from concrete carrier neighbour-pair
rows plus the sharp endpoint-only row.

This is the current CH local-germ cut: the local/open branch is proved from
actual frontier-edge carrier membership; the only remaining endpoint theorem
is the no-chord-style statement that an adjacent frontier endpoint is one of
the two selected carrier neighbours. -/
def boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointOnly
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x = (neighborRows a).left.1 ∨
              x = (neighborRows a).right.1) :
    BoundaryFreeNoThirdGermSource inputs :=
  BoundaryFreeIncidentOnlySourceRows.toBoundaryFreeNoThirdGermSource
    (boundaryFreeIncidentOnlyRows_of_neighborPairRows_endpointOnly
      (C := C) (inputs := inputs) neighborRows endpoint_only)

/-- Nonempty wrapper for
`boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointOnly`. -/
def nonempty_boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointOnly
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x = (neighborRows a).left.1 ∨
              x = (neighborRows a).right.1) :
    Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  ⟨boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointOnly
    (C := C) (inputs := inputs) neighborRows endpoint_only⟩

/-- Pointwise no-chord/two-neighbour source feeding the boundary-free local
no-third-germ row.

The `neighborRows` field supplies the two concrete neighbours of each actual
unbounded-frontier carrier vertex.  The `endpoint_only` field is the remaining
endpoint no-chord statement: an adjacent graph vertex whose point also lies on
the unbounded exterior frontier must be one of those two concrete neighbours.
Open-edge frontier points are handled separately by the existing
interior-frontier carrier membership theorem. -/
structure BoundaryFreeNeighborPairEndpointOnlySourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  neighborRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a
  endpoint_only :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (x : Fin n),
      (canonicalGraph C).Adj a.1 x ->
        (canonicalGraph C).point x ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ->
          x = (neighborRows a).left.1 ∨
            x = (neighborRows a).right.1

namespace BoundaryFreeNeighborPairEndpointOnlySourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- The packaged no-chord/two-neighbour source gives the incident-only local
source rows used by the boundary-free no-third-germ eraser. -/
def toIncidentOnlyRows
    (rows : BoundaryFreeNeighborPairEndpointOnlySourceRows inputs) :
    BoundaryFreeIncidentOnlySourceRows inputs :=
  boundaryFreeIncidentOnlyRows_of_neighborPairRows_endpointOnly
    (C := C) (inputs := inputs)
    rows.neighborRows rows.endpoint_only

/-- The packaged no-chord/two-neighbour source gives
`BoundaryFreeNoThirdGermSource` without any endpoint incident shortcut. -/
def toBoundaryFreeNoThirdGermSource
    (rows : BoundaryFreeNeighborPairEndpointOnlySourceRows inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  rows.toIncidentOnlyRows.toBoundaryFreeNoThirdGermSource

/-- The packaged no-chord/two-neighbour source also discharges the current
deleted-neighbour source by first erasing to the boundary-free local row. -/
def toUnreachableAfterDeleteInputSource
    (rows : BoundaryFreeNeighborPairEndpointOnlySourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  rows.toBoundaryFreeNoThirdGermSource.toUnreachableAfterDeleteInputSource

end BoundaryFreeNeighborPairEndpointOnlySourceRows

/-- The concrete neighbour-pair family erased from the selected geometric
carrier-neighbour source. -/
abbrev selectedCarrierNeighborRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedNeighbors :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a :=
  S2LocalTwoGermAssembly.unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
    selectedNeighbors

/-- Package the endpoint-only source rows from the actual selected carrier
neighbour source.

The selected heads are the two concrete unbounded-frontier carrier neighbours
chosen by the geometric-selection source in `S2LocalTwoGermAssembly`; the
endpoint row is only the sharp no-chord statement for those same two heads. -/
def boundaryFreeNeighborPairEndpointOnlySourceRows_of_selectedCarrierNeighborPairSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedNeighbors :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x =
                (selectedCarrierNeighborRows selectedNeighbors a).left.1 ∨
              x =
                (selectedCarrierNeighborRows selectedNeighbors a).right.1) :
    BoundaryFreeNeighborPairEndpointOnlySourceRows inputs where
  neighborRows := selectedCarrierNeighborRows selectedNeighbors
  endpoint_only := by
    intro a x hadj hxfrontier
    exact endpoint_only a x hadj hxfrontier

/-- Claim `S2-dyn-20260520-selected-carrier-neighbor-pair-source`.

The actual selected-carrier neighbour source feeds Volta's endpoint-only row
shape.  This does not prove a blanket adjacent-endpoint incident/closure row:
the only endpoint premise says that an adjacent frontier endpoint is one of
the two selected carrier heads chosen by the same geometric-selection source. -/
def S2_dyn_20260520_selected_carrier_neighbor_pair_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedNeighbors :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x =
                (selectedCarrierNeighborRows selectedNeighbors a).left.1 ∨
              x =
                (selectedCarrierNeighborRows selectedNeighbors a).right.1) :
    BoundaryFreeNeighborPairEndpointOnlySourceRows inputs :=
  boundaryFreeNeighborPairEndpointOnlySourceRows_of_selectedCarrierNeighborPairSource
    (C := C) (inputs := inputs) selectedNeighbors endpoint_only

/-- Family form of
`S2_dyn_20260520_selected_carrier_neighbor_pair_source`. -/
def S2_dyn_20260520_selected_carrier_neighbor_pair_source_family
    (selectedNeighbors :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (endpoint_only :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs})
            (x : Fin m),
            (canonicalGraph C).Adj a.1 x ->
              (canonicalGraph C).point x ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ->
                x =
                    (selectedCarrierNeighborRows
                      (selectedNeighbors C inputs) a).left.1 ∨
                  x =
                    (selectedCarrierNeighborRows
                      (selectedNeighbors C inputs) a).right.1) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeNeighborPairEndpointOnlySourceRows inputs :=
  fun C inputs =>
    S2_dyn_20260520_selected_carrier_neighbor_pair_source
      (C := C) (inputs := inputs)
      (selectedNeighbors C inputs) (endpoint_only C inputs)

set_option linter.style.longLine false in
/-- Corrected boundary-free local input reduction.

The positive local two-germ field is paired with the honest local-radius
no-third-germ source.  This package is the finite-input-safe replacement for
using an endpoint-only/no-chord row to manufacture the global closed-germ
`BoundaryFreeNoThirdGermSource`. -/
structure BoundaryFreeLocalInputSourceReduction
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  localTwoGermRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a
  localNoThirdGermSource :
    BoundaryFreeLocalNoThirdGermSourceRows inputs

set_option linter.style.longLine false in
/-- Local two-germ rows fill the corrected boundary-free local input package.

The same pointwise local two-germ rows supply the positive local field and,
through the checked cut-partition eraser, the local no-third-germ source.  This
keeps the live local leaf on actual selected `unboundedFrontierEdgeSet` germs
instead of all-adjacent endpoint or outgoing-list shortcuts. -/
noncomputable def boundaryFreeLocalInputSourceReduction_of_localTwoGermRows_20260521h1
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    BoundaryFreeLocalInputSourceReduction inputs where
  localTwoGermRows := localTwoGermRows
  localNoThirdGermSource :=
    S2_dyn_20260520_boundaryfree_localTwoGerm_bridge
      (C := C) (inputs := inputs) localTwoGermRows

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeLocalInputSourceReduction_of_localTwoGermRows_20260521h1`. -/
noncomputable def boundaryFreeLocalInputSourceReductionFamily_of_localTwoGermRows_20260521h1
    (localTwoGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeLocalInputSourceReduction_of_localTwoGermRows_20260521h1
      (C := C) (inputs := inputs) (localTwoGermRows C inputs)

set_option linter.style.longLine false in
/-- Sharp cut-partition source for the corrected boundary-free local input.

This is the source-level form of the live local S2 reduction: the same actual
carrier cut-partition package first supplies the local no-third-germ rows, and
those rows provide both fields of `BoundaryFreeLocalInputSourceReduction`. -/
noncomputable def
    boundaryFreeLocalInputSourceReduction_of_neighborPairCutPartitionInputSource_20260521h2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    BoundaryFreeLocalInputSourceReduction inputs := by
  let localSource :
      BoundaryFreeLocalNoThirdGermSourceRows inputs :=
    boundaryFreeLocalNoThirdGermSourceRows_of_neighborPairCutPartitionInputSource
      (C := C) (inputs := inputs) source
  exact
    { localTwoGermRows := localSource.toLocalTwoGermRows
      localNoThirdGermSource := localSource }

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeLocalInputSourceReduction_of_neighborPairCutPartitionInputSource_20260521h2`. -/
noncomputable def
    boundaryFreeLocalInputSourceReductionFamily_of_neighborPairCutPartitionInputSource_20260521h2
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeLocalInputSourceReduction_of_neighborPairCutPartitionInputSource_20260521h2
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Pointwise concrete neighbour-pair rows fill the corrected boundary-free
local input package.

This is the selected-edge local leaf in its smallest current form: the
neighbour rows are already about the actual `unboundedFrontierCarrierGraph`,
and the local two-germ proof comes from finite vertex-star isolation plus the
fixed-side interior-frontier edge-membership theorem. -/
noncomputable def
    boundaryFreeLocalInputSourceReduction_of_neighborPairRows_20260521h4
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    BoundaryFreeLocalInputSourceReduction inputs :=
  boundaryFreeLocalInputSourceReduction_of_localTwoGermRows_20260521h1
    (C := C) (inputs := inputs)
    (S2LocalTwoGermAssembly.localTwoGermRows_of_neighborPairRows
      (C := C) (inputs := inputs) neighborRows)

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeLocalInputSourceReduction_of_neighborPairRows_20260521h4`. -/
noncomputable def
    boundaryFreeLocalInputSourceReductionFamily_of_neighborPairRows_20260521h4
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeLocalInputSourceReduction_of_neighborPairRows_20260521h4
      (C := C) (inputs := inputs) (neighborRows C inputs)

set_option linter.style.longLine false in
/-- The corrected boundary-free local input package is equivalent to the
pointwise actual carrier-neighbour rows.

The forward direction erases the local two-germ field to local-sector rows and
then to neighbour-pair rows; the reverse direction is the h4 constructor above.
This keeps the local S2 source in the selected-edge carrier graph rather than
an induced frontier graph or all-adjacent endpoint statement. -/
theorem
    nonempty_boundaryFreeLocalInputSourceReduction_iff_neighborPairRows_20260521h5
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty (BoundaryFreeLocalInputSourceReduction inputs) ↔
      Nonempty
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierNeighborPairAt inputs a) := by
  constructor
  · rintro ⟨source⟩
    exact
      ⟨unboundedFrontierCarrierNeighborPairRows_of_localTwoGermRows
        (C := C) (inputs := inputs) source.localTwoGermRows⟩
  · rintro ⟨neighborRows⟩
    exact
      ⟨boundaryFreeLocalInputSourceReduction_of_neighborPairRows_20260521h4
        (C := C) (inputs := inputs) neighborRows⟩

set_option linter.style.longLine false in
/-- Explicit cycle-row handoff for the current live two-leaf S2 route. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_janiszewskiSubcontinuumPointsBetween_localTwoGermRows_20260521h3
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween)
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_localSectorRows
    inputs
    (planarContinuumUnboundedComplementFrontierPreconnected_of_janiszewskiSubcontinuumPointsBetween
      points_between)
    (localSectorRows_of_localTwoGermRows
      (C := C) (inputs := inputs) localTwoGermRows)

set_option linter.style.longLine false in
/-- Smaller topology-surface handoff for the local two-germ S2 branch.

This factors the h3 route through the primitive planar-continuum
preconnectedness source, avoiding the broader Janiszewski point-between leaf
whenever the actual unbounded exterior frontier preconnectedness theorem is
available directly. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_localTwoGermRows_20260521i1
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_localSectorRows
    inputs frontier_preconnected
    (localSectorRows_of_localTwoGermRows
      (C := C) (inputs := inputs) localTwoGermRows)

set_option linter.style.longLine false in
/-- Family form of the smaller topology-surface local two-germ handoff. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_localTwoGermRows_20260521i1
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (localTwoGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs := by
  intro m C inputs
  exact
    unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_localTwoGermRows_20260521i1
      (C := C) inputs frontier_preconnected (localTwoGermRows C inputs)

set_option linter.style.longLine false in
/-- Finite planar outer-component theorem handoff for the smaller
preconnected-topology local two-germ route. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_planarContinuumPreconnected_localTwoGermRows_20260521i1
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (localTwoGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_localTwoGermRows_20260521i1
      frontier_preconnected localTwoGermRows)

set_option linter.style.longLine false in
/-- Family form of the explicit h3 cycle-row handoff. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_janiszewskiSubcontinuumPointsBetween_localTwoGermRows_20260521h3
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween)
    (localTwoGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs := by
  intro m C inputs
  exact
    unboundedExteriorFrontierCycleRows_of_janiszewskiSubcontinuumPointsBetween_localTwoGermRows_20260521h3
      (C := C) inputs points_between (localTwoGermRows C inputs)

set_option linter.style.longLine false in
/-- Finite planar outer-component theorem handoff for the current live two-leaf S2 route. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_janiszewskiSubcontinuumPointsBetween_localTwoGermRows_20260521h3
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween)
    (localTwoGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_janiszewskiSubcontinuumPointsBetween_localTwoGermRows_20260521h3
      points_between localTwoGermRows)

namespace BoundaryFreeLocalInputSourceReduction

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- A local no-third-germ source fills the corrected local input package
without a separate local two-germ premise. -/
noncomputable def ofLocalNoThirdGermSource
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    BoundaryFreeLocalInputSourceReduction inputs where
  localTwoGermRows := source.toLocalTwoGermRows
  localNoThirdGermSource := source

/-- The corrected input reduction exposes local-sector rows through the
local no-third-germ source. -/
noncomputable def toLocalSectorRows
    (rows : BoundaryFreeLocalInputSourceReduction inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  rows.localNoThirdGermSource.toLocalSectorRows

/-- The corrected input reduction supplies concrete carrier neighbour-pair
rows without any adjacent-endpoint no-chord premise. -/
noncomputable def toNeighborPairRows
    (rows : BoundaryFreeLocalInputSourceReduction inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a :=
  rows.localNoThirdGermSource.toNeighborPairRows

/-- The corrected local input package supplies the connected-carrier input
rows from the planar-continuum frontier-preconnected source. -/
noncomputable def toConnectedInputSourceRows
    (rows : BoundaryFreeLocalInputSourceReduction inputs)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected) :
    UnboundedFrontierCarrierConnectedInputSourceRows inputs where
  planar_continuum_frontier_preconnected := frontier_preconnected
  localSectorRows := rows.toLocalSectorRows

/-- Carrier connectedness from the corrected local input package and the
planar-continuum frontier theorem. -/
theorem connected_of_planarContinuum
    (rows : BoundaryFreeLocalInputSourceReduction inputs)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_inputs
    inputs (rows.toConnectedInputSourceRows frontier_preconnected)

/-- Actual-frontier preconnectedness plus the corrected local input package
fill the component-topology source rows with the same selected carrier edges. -/
noncomputable def toComponentTopologyRowsFromFrontierPreconnected
    (rows : BoundaryFreeLocalInputSourceReduction inputs)
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior)) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  componentTopologySourceRows_of_frontierPreconnected_localSectorRows
    inputs frontier_preconnected rows.toLocalSectorRows

end BoundaryFreeLocalInputSourceReduction

set_option linter.style.longLine false in
/-- Local no-third-germ rows directly supply carrier connectedness once the
planar-continuum frontier-preconnected source is available.

This removes the separate local two-germ field from this connected-carrier
lane; the local-sector rows are derived from the same actual selected
`unboundedFrontierEdgeSet` heads in `BoundaryFreeLocalNoThirdGermSourceRows`. -/
theorem unboundedFrontierCarrierGraph_connected_of_planarContinuum_localNoThirdGermSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  (BoundaryFreeLocalInputSourceReduction.ofLocalNoThirdGermSource
    (C := C) (inputs := inputs) source).connected_of_planarContinuum
      frontier_preconnected

set_option linter.style.longLine false in
/-- Actual-frontier preconnectedness plus local no-third-germ rows fill the
component-topology source rows without manufacturing a global closed-germ
source. -/
noncomputable def componentTopologyRows_of_frontierPreconnected_localNoThirdGermSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  (BoundaryFreeLocalInputSourceReduction.ofLocalNoThirdGermSource
    (C := C) (inputs := inputs) source).toComponentTopologyRowsFromFrontierPreconnected
      frontier_preconnected

set_option linter.style.longLine false in
/-- No-compact-crossing topology plus boundary-free local no-third-germ rows
fill the component-topology source rows for the actual unbounded exterior
frontier.

The topology leaf supplies only actual frontier preconnectedness; the
boundary-free local rows supply the selected `unboundedFrontierEdgeSet` cover
through the fixed-side local-sector eraser.  No final boundary cycle,
actual-sector package, induced frontier graph, or arbitrary cycle is used. -/
noncomputable def
    componentTopologyRows_of_noCompactCrossing_localNoThirdGermSource_20260521r5i
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing)
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  componentTopologyRows_of_frontierPreconnected_localNoThirdGermSource
    (C := C) (inputs := inputs)
    (by
      simpa [UnboundedExteriorActualFrontierPreconnectedSource] using
        unboundedExteriorFrontier_frontierPreconnected_of_inputs
          (C := C) inputs no_crossing)
    source

set_option linter.style.longLine false in
/-- Claim `S2-r5i-component-topology-source-reduction-20260521r5i`.

Family-level strict reducer from the current topology leaf and the
boundary-free local no-third-germ rows to
`UnboundedExteriorFrontierComponentTopologySourceRows`.  The only global
mathematical source theorem left in this route is
`PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`;
the local rows are used solely to recover the selected frontier-edge cover. -/
theorem S2_r5i_component_topology_source_reduction_20260521r5i
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologySourceRows inputs := by
  intro m C inputs
  exact
    componentTopologyRows_of_noCompactCrossing_localNoThirdGermSource_20260521r5i
      (C := C) inputs no_crossing (source C inputs)

set_option linter.style.longLine false in
/-- Local selected-neighbour rows reduce to the corrected boundary-free local
input package using only actual selected edge incidences. -/
noncomputable def
    boundaryFreeLocalInputSourceReduction_of_localSelectedNeighborRows_selectedEdges_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localRows :
      S2LocalTwoGermAssembly.LocalSelectedNeighborSourceRows inputs) :
    BoundaryFreeLocalInputSourceReduction inputs where
  localTwoGermRows := localRows.localTwoGermRows
  localNoThirdGermSource :=
    boundaryFreeLocalNoThirdGermSourceRows_of_localSectorRows_selectedEdges
      (C := C) (inputs := inputs) localRows.localSectorRows

set_option linter.style.longLine false in
/-- Family form of the corrected local input reduction. -/
noncomputable def
    boundaryFreeLocalInputSourceReductionFamily_of_localSelectedNeighborRows_selectedEdges_20260520
    (localRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.LocalSelectedNeighborSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeLocalInputSourceReduction_of_localSelectedNeighborRows_selectedEdges_20260520
      (C := C) (inputs := inputs) (localRows C inputs)

set_option linter.style.longLine false in
/-- Selected-neighbour geometric-order rows plus the local-radius incident-germ
row reduce to the corrected local input package.

This is the local-radius-safe replacement for consumers that previously asked
for the arbitrary-radius
`SelectedNeighborIncidentGermFrontierEdgeMembershipRows` leaf. -/
noncomputable def
    boundaryFreeLocalInputSourceReduction_of_selectedNeighborGeometricOrder_localIncident_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (localIncidentRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    BoundaryFreeLocalInputSourceReduction inputs := by
  let localSource :
      BoundaryFreeLocalNoThirdGermSourceRows inputs :=
    boundaryFreeLocalNoThirdGermSourceRows_of_selectedNeighborGeometricOrder_localIncident_20260521k6
      (C := C) (inputs := inputs) selectedRows localIncidentRows
  exact
    { localTwoGermRows := localSource.toLocalTwoGermRows
      localNoThirdGermSource := localSource }

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeLocalInputSourceReduction_of_selectedNeighborGeometricOrder_localIncident_20260520`. -/
noncomputable def
    boundaryFreeLocalInputSourceReductionFamily_of_selectedNeighborGeometricOrder_localIncident_20260520
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (localIncidentRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeLocalInputSourceReduction_of_selectedNeighborGeometricOrder_localIncident_20260520
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (localIncidentRows C inputs)

set_option linter.style.longLine false in
/-- Geometric-selection rows reduce to the corrected local input package by
using the checked local-radius selected incident-germ row. -/
noncomputable def
    boundaryFreeLocalInputSourceReduction_of_geometricSelection_localIncident_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    BoundaryFreeLocalInputSourceReduction inputs := by
  let localSource :
      BoundaryFreeLocalNoThirdGermSourceRows inputs :=
    boundaryFreeLocalNoThirdGermSourceRows_of_geometricSelection_localIncident_20260521k6
      (C := C) (inputs := inputs) geometricSelection
  exact
    { localTwoGermRows := localSource.toLocalTwoGermRows
      localNoThirdGermSource := localSource }

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeLocalInputSourceReduction_of_geometricSelection_localIncident_20260520`. -/
noncomputable def
    boundaryFreeLocalInputSourceReductionFamily_of_geometricSelection_localIncident_20260520
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeLocalInputSourceReduction_of_geometricSelection_localIncident_20260520
      (C := C) (inputs := inputs) (geometricSelection C inputs)

set_option linter.style.longLine false in
/-- Compact geometric-neighbour rows reduce to the corrected local input
package through their geometric-selection erasure. -/
noncomputable def
    boundaryFreeLocalInputSourceReduction_of_geometricNeighborSelection_localIncident_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
        inputs) :
    BoundaryFreeLocalInputSourceReduction inputs :=
  boundaryFreeLocalInputSourceReduction_of_geometricSelection_localIncident_20260520
    (C := C) (inputs := inputs) rows.toGeometricSelectionInputSource

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeLocalInputSourceReduction_of_geometricNeighborSelection_localIncident_20260520`. -/
noncomputable def
    boundaryFreeLocalInputSourceReductionFamily_of_geometricNeighborSelection_localIncident_20260520
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeLocalInputSourceReduction_of_geometricNeighborSelection_localIncident_20260520
      (C := C) (inputs := inputs) (rows C inputs)

/-- Output bundle for the sharp boundary-free input-source cut.

The `localTwoGermRows` field is the positive endpoint-free local result: it
uses only the concrete carrier-neighbour pairs.  The full
`BoundaryFreeNoThirdGermSource` field is the global closed-germ source; it must
come from an honest endpoint selected-edge row (or another source of the same
strength), not from a bare finite-input no-chord claim about all adjacent
frontier endpoints. -/
structure BoundaryFreeInputSourceReduction
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  localTwoGermRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a
  boundaryFreeNoThirdGermSource :
    BoundaryFreeNoThirdGermSource inputs

namespace BoundaryFreeInputSourceReduction

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- A global boundary-free no-third-germ source fills the full input package
without a separate local two-germ premise. -/
noncomputable def ofBoundaryFreeNoThirdGermSource
    (source : BoundaryFreeNoThirdGermSource inputs) :
    BoundaryFreeInputSourceReduction inputs where
  localTwoGermRows := source.toLocalTwoGermRows
  boundaryFreeNoThirdGermSource := source

/-- The boundary-free input reduction already contains the exact local-sector
family needed by the connected-carrier source: erase its positive local
two-germ rows pointwise. -/
noncomputable def toLocalSectorRows
    (rows : BoundaryFreeInputSourceReduction inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_localTwoGermRows rows.localTwoGermRows

/-- Boundary-free input rows plus the planar-continuum frontier theorem fill
Einstein's compact connected-carrier input source. -/
noncomputable def toConnectedInputSourceRows
    (rows : BoundaryFreeInputSourceReduction inputs)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected) :
    UnboundedFrontierCarrierConnectedInputSourceRows inputs where
  planar_continuum_frontier_preconnected := frontier_preconnected
  localSectorRows := rows.toLocalSectorRows

/-- Carrier connectedness from the boundary-free input reduction and the
planar-continuum frontier theorem. -/
theorem connected_of_planarContinuum
    (rows : BoundaryFreeInputSourceReduction inputs)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_inputs
    inputs (rows.toConnectedInputSourceRows frontier_preconnected)

end BoundaryFreeInputSourceReduction

/-- Claim `S2-dyn-20260520-fixed-side-local-sector-source`.

Strict source reduction for Einstein's connected-carrier input surface: the
fixed-side local-sector rows are supplied by the positive local two-germ field
of `BoundaryFreeInputSourceReduction`; the only global topology input remains
the planar-continuum frontier-preconnectedness theorem. -/
theorem unboundedFrontierCarrierGraph_connected_of_planarContinuum_boundaryFreeInputSourceReduction
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (rows : BoundaryFreeInputSourceReduction inputs) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  rows.connected_of_planarContinuum frontier_preconnected

set_option linter.style.longLine false in
/-- A global boundary-free no-third-germ source gives the full boundary-free
input package; the local two-germ field is projected from the same source. -/
noncomputable def
    S2_codex_current_20260520_boundaryfree_input_reduction_of_no_third_germ_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeNoThirdGermSource inputs) :
    BoundaryFreeInputSourceReduction inputs :=
  BoundaryFreeInputSourceReduction.ofBoundaryFreeNoThirdGermSource
    (C := C) (inputs := inputs) source

/-- Geometric-angular local rows supply the local-sector half of Einstein's
connected-carrier input source. -/
theorem unboundedFrontierCarrierGraph_connected_of_planarContinuum_boundaryFreeGeometricAngularSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (source :
      S2LocalTwoGermAssembly.BoundaryFreeLocalSectorGeometricAngularSource
        inputs) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_planarContinuum_localSectorRows
    inputs frontier_preconnected
    (S2LocalTwoGermAssembly.localSectorRows_of_boundaryFree_geometricAngularSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-boundaryfree-input-reduction-leaf`.

Selected carrier local-sector rows plus honest incident-germ selected-edge
membership fill the full boundary-free input package.  The local two-germ
field is the direct local-sector erasure, while the global no-third-germ field
is exactly the current checked source leaf; no all-adjacent frontier endpoint
shortcut is introduced. -/
noncomputable def
    S2_codex_current_20260520_boundaryfree_input_reduction_leaf
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (incident_germ_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε →
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
            (canonicalGraph C).Adj a.1 x →
              q ∈ vertexIncidentGermW3 C a.1 x ε →
                q ≠ (canonicalGraph C).point a.1 →
                  (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                    (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeInputSourceReduction inputs where
  localTwoGermRows :=
    S2LocalTwoGermAssembly.localTwoGermRows_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows
  boundaryFreeNoThirdGermSource :=
    S2_codex_current_20260520_boundaryfree_source_leaf
      (C := C) (inputs := inputs)
      localSectorRows incident_germ_frontier_edge

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_current_20260520_boundaryfree_input_reduction_leaf`. -/
noncomputable def
    S2_codex_current_20260520_boundaryfree_input_reduction_leaf_family
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (incident_germ_frontier_edge :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin m),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε →
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
                (canonicalGraph C).Adj a.1 x →
                  q ∈ vertexIncidentGermW3 C a.1 x ε →
                    q ≠ (canonicalGraph C).point a.1 →
                      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeInputSourceReduction inputs := by
  intro m C inputs
  exact
    S2_codex_current_20260520_boundaryfree_input_reduction_leaf
      (C := C) (inputs := inputs)
      (localSectorRows C inputs) (incident_germ_frontier_edge C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundary-free-input-source-worker-20260520r5`,
selected-edge endpoint support.

A local no-third-germ source already names two actual selected
`unboundedFrontierEdgeSet` edges at each frontier vertex.  The endpoint closure
needed along those two selected edges is therefore discharged by the selected
frontier-edge endpoint API, not by an all-adjacent frontier-endpoint closure
source. -/
theorem
    selectedIncidentEndpointClosureRows_of_boundaryFreeLocalNoThirdGermSource_20260520r5
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      ((Exists fun r : Real =>
        0 < r ∧
          forall z : PlanarInterface.Point,
            z ∈ Metric.ball ((canonicalGraph C).point a.1) r ->
            z ∈ closedSegment
              ((canonicalGraph C).point a.1)
              ((canonicalGraph C).point (source.left a)) ->
            z ∈ closure
              (unboundedExteriorComponentRows C inputs).exterior) ∧
      (Exists fun r : Real =>
        0 < r ∧
          forall z : PlanarInterface.Point,
            z ∈ Metric.ball ((canonicalGraph C).point (source.left a)) r ->
            z ∈ closedSegment
              ((canonicalGraph C).point a.1)
              ((canonicalGraph C).point (source.left a)) ->
            z ∈ closure
              (unboundedExteriorComponentRows C inputs).exterior)) ∧
      ((Exists fun r : Real =>
        0 < r ∧
          forall z : PlanarInterface.Point,
            z ∈ Metric.ball ((canonicalGraph C).point a.1) r ->
            z ∈ closedSegment
              ((canonicalGraph C).point a.1)
              ((canonicalGraph C).point (source.right a)) ->
            z ∈ closure
              (unboundedExteriorComponentRows C inputs).exterior) ∧
      (Exists fun r : Real =>
        0 < r ∧
          forall z : PlanarInterface.Point,
            z ∈ Metric.ball ((canonicalGraph C).point (source.right a)) r ->
            z ∈ closedSegment
              ((canonicalGraph C).point a.1)
              ((canonicalGraph C).point (source.right a)) ->
            z ∈ closure
              (unboundedExteriorComponentRows C inputs).exterior)) := by
  intro a
  have hleft :=
    selectedUnboundedFrontierEdgeEndpointClosureSource_of_selectedIncidentEdge
      (C := C) (inputs := inputs)
      selectedUnboundedFrontierEdgeEndpointClosureSource_of_definition
      (source.left_edge a)
  have hright :=
    selectedUnboundedFrontierEdgeEndpointClosureSource_of_selectedIncidentEdge
      (C := C) (inputs := inputs)
      selectedUnboundedFrontierEdgeEndpointClosureSource_of_definition
      (source.right_edge a)
  exact ⟨hleft, hright⟩

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundary-free-input-source-worker-20260520r5`.

Strict input-source reduction from the honest local no-third-germ source plus
the genuine closed incident-germ frontier-edge membership row.  The positive
local field is read from `BoundaryFreeLocalNoThirdGermSourceRows`; the global
closed-germ field is produced by the existing boundary-free no-third-germ
selected-edge eraser.  Endpoint support for the selected edges is available
from
`selectedIncidentEndpointClosureRows_of_boundaryFreeLocalNoThirdGermSource_20260520r5`.
-/
noncomputable def
    boundaryFreeInputSourceReduction_of_localNoThirdGermSource_incidentGermFrontierEdge_20260520r5
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSource : BoundaryFreeLocalNoThirdGermSourceRows inputs)
    (incident_germ_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                    (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeInputSourceReduction inputs where
  localTwoGermRows := localSource.toLocalTwoGermRows
  boundaryFreeNoThirdGermSource :=
    boundaryFreeNoThirdGermSource_of_localSectorRows_incidentGermFrontierEdge
      (C := C) (inputs := inputs)
      localSource.toLocalSectorRows incident_germ_frontier_edge

set_option linter.style.longLine false in
/-- Selected incident-edge version of the r5 boundary-free input-source
reducer.

This preserves the selected heads from
`LocalSelectedIncidentEdgePairSourceRows`: those rows build the local
no-third-germ source for the positive local field, and the same selected rows
feed the global boundary-free no-third-germ eraser. -/
noncomputable def
    S2_agent_boundary_free_input_source_worker_20260520r5_of_selectedIncidentEdgePairRows_incidentGermFrontierEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdges :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs)
    (incident_germ_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                    (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeInputSourceReduction inputs := by
  let localSource :
      BoundaryFreeLocalNoThirdGermSourceRows inputs :=
    boundaryFreeLocalNoThirdGermSourceRows_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdges
  exact
    { localTwoGermRows := localSource.toLocalTwoGermRows
      boundaryFreeNoThirdGermSource :=
        boundaryFreeNoThirdGermSource_of_selectedIncidentEdgePairRows_incidentGermFrontierEdge
          (C := C) (inputs := inputs)
          selectedEdges incident_germ_frontier_edge }

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_boundary_free_input_source_worker_20260520r5_of_selectedIncidentEdgePairRows_incidentGermFrontierEdge`.
-/
noncomputable def
    S2_agent_boundary_free_input_source_worker_family_20260520r5_of_selectedIncidentEdgePairRows_incidentGermFrontierEdge
    (selectedEdges :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs)
    (incident_germ_frontier_edge :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin m),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeInputSourceReduction inputs := by
  intro m C inputs
  exact
    S2_agent_boundary_free_input_source_worker_20260520r5_of_selectedIncidentEdgePairRows_incidentGermFrontierEdge
      (C := C) (inputs := inputs)
      (selectedEdges C inputs)
      (incident_germ_frontier_edge C inputs)

set_option linter.style.longLine false in
/-- Selected incident-germ membership row for the boundary-free input cut.

This is the exact global closed-germ source still needed after the local
finite-drawing radius theorem: every noncenter frontier point in an incident
W3 germ must certify the germ head by an actual selected
`unboundedFrontierEdgeSet` edge.  It does not classify all adjacent frontier
endpoints or pass through a boundary cycle, induced frontier graph, outgoing
no-between facade, or synthetic enclosure. -/
abbrev BoundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
    q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
      q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
        (canonicalGraph C).Adj a.1 x ->
          q ∈ vertexIncidentGermW3 C a.1 x ε ->
            q ≠ (canonicalGraph C).point a.1 ->
              (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                (x, a.1) ∈ unboundedFrontierEdgeSet C inputs

set_option linter.style.longLine false in
/-- Endpoint branch of the genuine incident-germ selected-edge source.

This is narrower than an all-adjacent endpoint row: it only asks for selected
`unboundedFrontierEdgeSet` membership when the far endpoint itself occurs as
the noncenter frontier point in the same closed incident germ. -/
abbrev BoundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (ε : Real) (x : Fin n),
    (canonicalGraph C).point x ∈
        Metric.ball ((canonicalGraph C).point a.1) ε ->
      (canonicalGraph C).point x ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior ->
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈ vertexIncidentGermW3 C a.1 x ε ->
            (canonicalGraph C).point x ≠ (canonicalGraph C).point a.1 ->
              (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                (x, a.1) ∈ unboundedFrontierEdgeSet C inputs

set_option linter.style.longLine false in
/-- Reduce the global incident-germ selected-edge membership row to its only
unproved closed-germ branch.

The relative-interior branch is discharged by the pointwise interior frontier
edge carrier theorem; the center branch contradicts the noncenter hypothesis.
Thus the residual is exactly the far endpoint of the same incident germ, not
an all-adjacent endpoint closure or incident-row source. -/
theorem boundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows_of_endpoint_20260521c3
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (endpointRows :
      BoundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows inputs) :
    BoundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows inputs := by
  intro a ε q x hqball hqfrontier hadj hgerm hqne
  rcases hgerm with ⟨_hqball_germ, hqclosed⟩
  rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hqclosed with
    hq_center | hq_endpoint | hq_open
  · exact False.elim (hqne hq_center)
  · have hxball :
        (canonicalGraph C).point x ∈
          Metric.ball ((canonicalGraph C).point a.1) ε := by
      simpa [hq_endpoint] using hqball
    have hxfrontier :
        (canonicalGraph C).point x ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior := by
      simpa [hq_endpoint] using hqfrontier
    have hxgerm :
        (canonicalGraph C).point x ∈ vertexIncidentGermW3 C a.1 x ε := by
      exact ⟨hxball, right_mem_closedSegment _ _⟩
    have hxne :
        (canonicalGraph C).point x ≠ (canonicalGraph C).point a.1 := by
      intro hx
      exact hqne (by simp [hq_endpoint, hx])
    exact endpointRows a ε x hxball hxfrontier hadj hxgerm hxne
  · have hsource :
        InteriorFrontierEdgeCarrierMembershipSource C inputs :=
      interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
    rcases hadj with hforward | hreverse
    · exact Or.inl
        (hsource (e := (a.1, x)) (p := q)
          hforward hq_open hqfrontier)
    · exact Or.inr
        (hsource (e := (x, a.1)) (p := q)
          hreverse (inOpenSegment_symm hq_open) hqfrontier)

set_option linter.style.longLine false in
/-- Smallest selected-edge source bundle for
`BoundaryFreeInputSourceReduction`.

The first field names the two actual selected incident carrier edges at each
unbounded-frontier vertex and proves selected incident-edge completeness.  The
second field is the remaining global closed-germ membership row, also stated
only as actual `unboundedFrontierEdgeSet` membership. -/
structure BoundaryFreeSelectedEdgeInputSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  selectedIncidentEdges :
    S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs
  incidentGermFrontierEdge :
    BoundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows inputs

set_option linter.style.longLine false in
/-- Sharper selected-edge input bundle whose only global residual is the
far-endpoint branch of a closed incident germ.

The open-segment branch of the old incident-germ membership row is proved by
`boundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows_of_endpoint_20260521c3`,
so this source keeps the remaining work tied to the same selected incident
germ instead of asking for an all-adjacent endpoint row. -/
structure BoundaryFreeSelectedEdgeEndpointInputSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  selectedIncidentEdges :
    S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs
  incidentGermEndpointFrontierEdge :
    BoundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows inputs

namespace BoundaryFreeSelectedEdgeInputSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- Erase the selected-edge input bundle to the boundary-free input reduction.

This is just the checked r5 selected-edge reducer with its two selected-edge
premises packaged into one source row. -/
noncomputable def toBoundaryFreeInputSourceReduction
    (rows : BoundaryFreeSelectedEdgeInputSourceRows inputs) :
    BoundaryFreeInputSourceReduction inputs :=
  S2_agent_boundary_free_input_source_worker_20260520r5_of_selectedIncidentEdgePairRows_incidentGermFrontierEdge
    (C := C) (inputs := inputs)
    rows.selectedIncidentEdges rows.incidentGermFrontierEdge

end BoundaryFreeSelectedEdgeInputSourceRows

namespace BoundaryFreeSelectedEdgeEndpointInputSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- Erase the endpoint-branch selected-edge bundle to the previous selected
input rows by proving the open-segment incident-germ branch directly. -/
noncomputable def toSelectedEdgeInputSourceRows
    (rows : BoundaryFreeSelectedEdgeEndpointInputSourceRows inputs) :
    BoundaryFreeSelectedEdgeInputSourceRows inputs where
  selectedIncidentEdges := rows.selectedIncidentEdges
  incidentGermFrontierEdge :=
    boundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows_of_endpoint_20260521c3
      (C := C) (inputs := inputs)
      rows.incidentGermEndpointFrontierEdge

end BoundaryFreeSelectedEdgeEndpointInputSourceRows

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundaryfree-selected-edge-input-worker-20260521c3`.

Strict reducer for `BoundaryFreeSelectedEdgeInputSourceRows`: selected
incident-edge pairs plus the genuine far-endpoint incident-germ selected-edge
row imply the former global incident-germ membership source. -/
noncomputable def
    S2_agent_boundaryfree_selected_edge_input_worker_20260521c3
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeSelectedEdgeEndpointInputSourceRows inputs) :
    BoundaryFreeSelectedEdgeInputSourceRows inputs :=
  rows.toSelectedEdgeInputSourceRows

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_boundaryfree_selected_edge_input_worker_20260521c3`. -/
noncomputable def
    S2_agent_boundaryfree_selected_edge_input_worker_family_20260521c3
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeSelectedEdgeEndpointInputSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeSelectedEdgeInputSourceRows inputs := by
  intro m C inputs
  exact
    S2_agent_boundaryfree_selected_edge_input_worker_20260521c3
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundaryfree-input-source-worker-20260521a2`.

Strict non-circular reducer for `BoundaryFreeInputSourceReduction inputs` from
the selected-edge input row.  The only live leaf is
`BoundaryFreeSelectedEdgeInputSourceRows`: actual selected incident
`unboundedFrontierEdgeSet` pairs plus actual selected closed-germ membership. -/
noncomputable def
    S2_agent_boundaryfree_input_source_worker_20260521a2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeSelectedEdgeInputSourceRows inputs) :
    BoundaryFreeInputSourceReduction inputs :=
  rows.toBoundaryFreeInputSourceReduction

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_boundaryfree_input_source_worker_20260521a2`. -/
noncomputable def
    S2_agent_boundaryfree_input_source_worker_family_20260521a2
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeSelectedEdgeInputSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeInputSourceReduction inputs := by
  intro m C inputs
  exact
    S2_agent_boundaryfree_input_source_worker_20260521a2
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Endpoint selected-head rows imply the endpoint membership row used by
`BoundaryFreeSelectedEdgeInputSourceRows`.

The endpoint residual remains tied to the same selected incident-edge pair:
once the closed-germ endpoint is one of the two selected heads, the stored
actual `unboundedFrontierEdgeSet` incidence supplies membership. -/
theorem
    boundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows_of_selectedHeadRows_20260521k18
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs)
    (endpointRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadRows
        selectedRows) :
    BoundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows inputs := by
  intro a ε x hxball hxfrontier hadj hxgerm hxne
  rcases endpointRows a ε x hxball hxfrontier hadj hxgerm hxne with
    hx_left | hx_right
  · simpa [hx_left] using selectedRows.left_edge a
  · simpa [hx_right] using selectedRows.right_edge a

set_option linter.style.longLine false in
/-- Same-germ endpoint no-third rows imply the endpoint membership row needed
by the global boundary-free source.

The source stays attached to the selected actual carrier heads: it only rules
out a closed-germ far endpoint distinct from the two selected
`unboundedFrontierEdgeSet` heads, and the stored selected-edge incidences then
provide the required frontier-edge membership. -/
theorem
    boundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows_of_selectedEdgeNoThirdRows_20260521r61
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs)
    (endpointRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointSelectedEdgeNoThirdRows
        selectedRows) :
    BoundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows inputs :=
  boundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows_of_selectedHeadRows_20260521k18
    (C := C) (inputs := inputs) selectedRows
    (S2LocalTwoGermAssembly.incidentGermEndpointSelectedHeadRows_of_selectedEdgeNoThirdRows_20260521k6j
      (C := C) (inputs := inputs) selectedRows endpointRows)

set_option linter.style.longLine false in
/-- Selected incident-edge rows plus the same-germ endpoint no-third residual
fill the selected-edge source bundle for the global boundary-free input.

The open-segment branch is discharged by the existing incident-germ splitter;
the only remaining global source is the closed-germ endpoint no-third row for
the same selected actual carrier heads. -/
noncomputable def
    boundaryFreeSelectedEdgeInputSourceRows_of_selectedIncidentEdgePairRows_endpointNoThird_20260521r61
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs)
    (endpointRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointSelectedEdgeNoThirdRows
        selectedRows) :
    BoundaryFreeSelectedEdgeInputSourceRows inputs where
  selectedIncidentEdges := selectedRows
  incidentGermFrontierEdge :=
    boundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows_of_endpoint_20260521c3
      (C := C) (inputs := inputs)
      (boundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows_of_selectedEdgeNoThirdRows_20260521r61
        (C := C) (inputs := inputs) selectedRows endpointRows)

set_option linter.style.longLine false in
/-- Global `BoundaryFreeNoThirdGermSource` from selected actual carrier heads
and the sharp same-germ endpoint no-third residual.

This is the direct global counterpart of the local-radius source: local
frontier-germ membership handles nearby points, while this theorem records
that the full arbitrary-radius source still needs exactly the endpoint
no-third row. -/
noncomputable def
    boundaryFreeNoThirdGermSource_of_selectedIncidentEdgePairRows_endpointNoThird_20260521r61
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs)
    (endpointRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointSelectedEdgeNoThirdRows
        selectedRows) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_selectedIncidentEdgePairRows_incidentGermFrontierEdge
    (C := C) (inputs := inputs) selectedRows
    (boundaryFreeSelectedEdgeInputSourceRows_of_selectedIncidentEdgePairRows_endpointNoThird_20260521r61
      (C := C) (inputs := inputs) selectedRows endpointRows).incidentGermFrontierEdge

set_option linter.style.longLine false in
/-- Actual carrier-neighbour rows reduce the global boundary-free no-third
source to the same-germ endpoint no-third residual for the selected neighbour
heads.

The two selected heads are projected from the actual
`UnboundedFrontierCarrierNeighborPairAt` rows.  No boundary cycle, actual
sector package, W32 facade, or all-adjacent endpoint shortcut is used. -/
noncomputable def
    boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointNoThird_20260521r61
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (endpointRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointSelectedEdgeNoThirdRows
        (S2LocalTwoGermAssembly.S2_agent_selected_incident_edge_source_20260520c_of_neighborPairRows
          (C := C) (inputs := inputs) neighborRows)) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_selectedIncidentEdgePairRows_endpointNoThird_20260521r61
    (C := C) (inputs := inputs)
    (S2LocalTwoGermAssembly.S2_agent_selected_incident_edge_source_20260520c_of_neighborPairRows
      (C := C) (inputs := inputs) neighborRows)
    endpointRows

set_option linter.style.longLine false in
/-- Claim `S2-r21-local-no-third-germ-source`, local selected-germ form.

The r20 minimal local no-third-germ source is strictly lowered to the selected
frontier carrier/cut input package.  The cut package selects the two actual
frontier-carrier heads; the checked local star isolation inside
`BoundaryFreeLocalNoThirdGermSourceRows.toLocalSelectedNoThirdGermSource`
turns those selected heads into the local-radius no-third-germ source.  No
final boundary cycle, actual exterior-sector row, W32 facade, or global
endpoint classifier is used. -/
noncomputable def
    S2_r21_local_no_third_germ_source_of_cutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs :=
  (boundaryFreeLocalNoThirdGermSourceRows_of_neighborPairCutPartitionInputSource
    (C := C) (inputs := inputs) source).toLocalSelectedNoThirdGermSource

set_option linter.style.longLine false in
/-- Family form of
`S2_r21_local_no_third_germ_source_of_cutPartitionInputSource`. -/
noncomputable def
    S2_r21_local_no_third_germ_source_family_of_cutPartitionInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs := by
  intro m C inputs
  exact
    S2_r21_local_no_third_germ_source_of_cutPartitionInputSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-r21-local-no-third-germ-source`, global boundary-free form.

The global arbitrary-radius `BoundaryFreeNoThirdGermSource` is lowered to the
same selected frontier carrier/cut input package plus the exact remaining
closed-germ endpoint row for the selected heads produced from that package.
The local star part is handled by the selected cut data; the only residual is
the endpoint branch needed to promote the local source to the global
arbitrary-radius source. -/
noncomputable def
    S2_r21_boundaryFreeNoThirdGermSource_of_cutPartitionInputSource_endpointSelectedHeadRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (endpointRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadRows
        (S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
          (C := C) (inputs := inputs) source)) :
    BoundaryFreeNoThirdGermSource inputs := by
  let selectedRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
        inputs :=
    S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
      (C := C) (inputs := inputs) source
  exact
    boundaryFreeNoThirdGermSource_of_selectedIncidentEdgePairRows_endpointNoThird_20260521r61
      (C := C) (inputs := inputs) selectedRows
      (S2LocalTwoGermAssembly.incidentGermEndpointSelectedEdgeNoThirdRows_of_selectedHeadRows_20260521k6k
        (C := C) (inputs := inputs) selectedRows
        (by
          simpa [selectedRows] using endpointRows))

set_option linter.style.longLine false in
/-- Family form of
`S2_r21_boundaryFreeNoThirdGermSource_of_cutPartitionInputSource_endpointSelectedHeadRows`. -/
noncomputable def
    S2_r21_boundaryFreeNoThirdGermSource_family_of_cutPartitionInputSource_endpointSelectedHeadRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadRows
            (S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
              (C := C) (inputs := inputs) (source C inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeNoThirdGermSource inputs := by
  intro m C inputs
  exact
    S2_r21_boundaryFreeNoThirdGermSource_of_cutPartitionInputSource_endpointSelectedHeadRows
      (C := C) (inputs := inputs)
      (source C inputs) (endpointRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-r22-endpoint-selected-head-rows`, selected-edge endpoint
closure support.

For the same selected incident pair projected from the k9 cut input source,
the two stored `unboundedFrontierEdgeSet` incidences give the local
closed-segment endpoint closure rows for both selected heads.  This is
selected-edge gated: it uses only actual selected frontier edges, not an
all-adjacent endpoint closure theorem. -/
theorem
    S2_r22_selectedIncidentEndpointClosureRows_of_cutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    let selectedRows :
        S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs :=
      S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
        (C := C) (inputs := inputs) source
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      ((Exists fun r : Real =>
        0 < r ∧
          forall z : PlanarInterface.Point,
            z ∈ Metric.ball ((canonicalGraph C).point a.1) r ->
            z ∈ closedSegment
              ((canonicalGraph C).point a.1)
              ((canonicalGraph C).point (selectedRows.left a)) ->
            z ∈ closure
              (unboundedExteriorComponentRows C inputs).exterior) ∧
      (Exists fun r : Real =>
        0 < r ∧
          forall z : PlanarInterface.Point,
            z ∈ Metric.ball
              ((canonicalGraph C).point (selectedRows.left a)) r ->
            z ∈ closedSegment
              ((canonicalGraph C).point a.1)
              ((canonicalGraph C).point (selectedRows.left a)) ->
            z ∈ closure
              (unboundedExteriorComponentRows C inputs).exterior)) ∧
      ((Exists fun r : Real =>
        0 < r ∧
          forall z : PlanarInterface.Point,
            z ∈ Metric.ball ((canonicalGraph C).point a.1) r ->
            z ∈ closedSegment
              ((canonicalGraph C).point a.1)
              ((canonicalGraph C).point (selectedRows.right a)) ->
            z ∈ closure
              (unboundedExteriorComponentRows C inputs).exterior) ∧
      (Exists fun r : Real =>
        0 < r ∧
          forall z : PlanarInterface.Point,
            z ∈ Metric.ball
              ((canonicalGraph C).point (selectedRows.right a)) r ->
            z ∈ closedSegment
              ((canonicalGraph C).point a.1)
              ((canonicalGraph C).point (selectedRows.right a)) ->
            z ∈ closure
              (unboundedExteriorComponentRows C inputs).exterior)) := by
  dsimp
  intro a
  let selectedRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs :=
    S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
      (C := C) (inputs := inputs) source
  have hleft :=
    selectedUnboundedFrontierEdgeEndpointClosureSource_of_selectedIncidentEdge
      (C := C) (inputs := inputs)
      selectedUnboundedFrontierEdgeEndpointClosureSource_of_definition
      (selectedRows.left_edge a)
  have hright :=
    selectedUnboundedFrontierEdgeEndpointClosureSource_of_selectedIncidentEdge
      (C := C) (inputs := inputs)
      selectedUnboundedFrontierEdgeEndpointClosureSource_of_definition
      (selectedRows.right_edge a)
  exact
    ⟨by simpa [selectedRows] using hleft,
      by simpa [selectedRows] using hright⟩

set_option linter.style.longLine false in
/-- Claim `S2-r22-endpoint-selected-head-rows`, global boundary-free form.

The r21 global boundary-free residual is lowered one step: for the selected
pair projected by
`localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9`,
it is enough to supply the explicit local-radius coverage row for the bounded
selected-head endpoint theorem.  The selected endpoint closure rows for those
same two actual frontier edges are available from
`S2_r22_selectedIncidentEndpointClosureRows_of_cutPartitionInputSource`. -/
noncomputable def
    S2_r22_boundaryFreeNoThirdGermSource_of_cutPartitionInputSource_endpointLocalRadiusCovers
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (endpointLocalRadiusCovers :
      let selectedRows :
          S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs :=
        S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
          (C := C) (inputs := inputs) source
      let localRows :
          S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadLocalRows
            selectedRows :=
        S2LocalTwoGermAssembly.S2_r22_incidentGerm_endpoint_selectedHeadLocalRows_of_cutPartitionInputSource
          (C := C) (inputs := inputs) source
      S2LocalTwoGermAssembly.IncidentGermEndpointLocalRadiusCoversRows
        (C := C) (inputs := inputs) (selectedRows := selectedRows)
        localRows) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_r21_boundaryFreeNoThirdGermSource_of_cutPartitionInputSource_endpointSelectedHeadRows
    (C := C) (inputs := inputs) source
    (S2LocalTwoGermAssembly.S2_r22_incidentGerm_endpoint_selectedHeadRows_of_cutPartitionInputSource_endpointLocalRadiusCovers
      (C := C) (inputs := inputs) source endpointLocalRadiusCovers)

set_option linter.style.longLine false in
/-- Claim `S2-boundary-free-no-third-source`.

The global boundary-free no-third package is reduced to concrete selected
neighbour data plus the two endpoint-local leaves.  The selected neighbours
come from the cut-partition input source.  The remaining endpoint work is
exactly:

* `IncidentGermEndpointFrontierEdgeMembershipRows inputs`, identifying an
  incident same-germ endpoint as an actual unbounded-frontier edge;
* `IncidentGermSelectedEndpointLocalRadiusContainsAt`, saying the two selected
  endpoint points lie in the local endpoint radius.

No final boundary cycle, actual-sector row, W32 facade, induced frontier graph,
all-adjacent endpoint theorem, identity angular row, or global all-outgoing
no-between source is used. -/
noncomputable def
    S2_boundaryFreeNoThirdGermSource_of_cutPartitionInputSource_endpointFrontierEdge_endpointRadiusContains_20260522
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (endpointRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointFrontierEdgeMembershipRows
        inputs)
    (endpointRadiusContains :
      let selectedRows :
          S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs :=
        S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
          (C := C) (inputs := inputs) source
      let localRows :
          S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadLocalRows
            selectedRows :=
        S2LocalTwoGermAssembly.S2_r22_incidentGerm_endpoint_selectedHeadLocalRows_of_cutPartitionInputSource
          (C := C) (inputs := inputs) source
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (canonicalGraph C).point (selectedRows.left a) ∈
            Metric.ball ((canonicalGraph C).point a.1)
              ((Classical.choose localRows) a) ∧
          (canonicalGraph C).point (selectedRows.right a) ∈
            Metric.ball ((canonicalGraph C).point a.1)
              ((Classical.choose localRows) a)) :
    BoundaryFreeNoThirdGermSource inputs := by
  let selectedRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs :=
    S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
      (C := C) (inputs := inputs) source
  let localRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadLocalRows
        selectedRows :=
    S2LocalTwoGermAssembly.S2_r22_incidentGerm_endpoint_selectedHeadLocalRows_of_cutPartitionInputSource
      (C := C) (inputs := inputs) source
  exact
    S2_r22_boundaryFreeNoThirdGermSource_of_cutPartitionInputSource_endpointLocalRadiusCovers
      (C := C) (inputs := inputs) source
      (by
        dsimp [S2LocalTwoGermAssembly.IncidentGermEndpointLocalRadiusCoversRows]
        intro a ε x hxball hxfrontier hadj hxgerm hxne
        have hedge :
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
          endpointRows a ε x hxball hxfrontier hadj hxgerm hxne
        rcases selectedRows.only_selected_incident a x hedge with
          hx_left | hx_right
        · exact
            (by
              simpa [selectedRows, localRows, hx_left]
                using (endpointRadiusContains a).1)
        · exact
            (by
              simpa [selectedRows, localRows, hx_right]
                using (endpointRadiusContains a).2))

set_option linter.style.longLine false in
/-- Family form of the r22 global boundary-free lowering. -/
noncomputable def
    S2_r22_boundaryFreeNoThirdGermSource_family_of_cutPartitionInputSource_endpointLocalRadiusCovers
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs)
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
                inputs :=
            S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
              (C := C) (inputs := inputs) (source C inputs)
          let localRows :
              S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadLocalRows
                selectedRows :=
            S2LocalTwoGermAssembly.S2_r22_incidentGerm_endpoint_selectedHeadLocalRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (source C inputs)
          S2LocalTwoGermAssembly.IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeNoThirdGermSource inputs := by
  intro m C inputs
  exact
    S2_r22_boundaryFreeNoThirdGermSource_of_cutPartitionInputSource_endpointLocalRadiusCovers
      (C := C) (inputs := inputs)
      (source C inputs) (endpointLocalRadiusCovers C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundaryfree-selected-edge-input-source-20260521k18`.

Selected-neighbour geometric-order rows plus the same-germ endpoint selected
head residual fill `BoundaryFreeSelectedEdgeInputSourceRows`.  The selected
incident pair is projected from the real carrier rows; the arbitrary-radius
incident-germ membership field is obtained through the checked endpoint/open
segment splitter, with the endpoint case discharged by selected heads. -/
noncomputable def
    boundaryFreeSelectedEdgeInputSourceRows_of_selectedNeighborGeometricOrder_selectedHeadRows_20260521k18
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (endpointRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadRows
        (S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_selectedNeighborGeometricOrderSourceRows_20260521k6h
          (C := C) (inputs := inputs) selectedRows)) :
    BoundaryFreeSelectedEdgeInputSourceRows inputs := by
  let selectedEdgeRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs :=
    S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_selectedNeighborGeometricOrderSourceRows_20260521k6h
      (C := C) (inputs := inputs) selectedRows
  exact
    { selectedIncidentEdges := selectedEdgeRows
      incidentGermFrontierEdge :=
        boundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows_of_endpoint_20260521c3
          (C := C) (inputs := inputs)
          (boundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows_of_selectedHeadRows_20260521k18
            (C := C) (inputs := inputs)
            selectedEdgeRows
            (by
              simpa [selectedEdgeRows] using endpointRows)) }

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeSelectedEdgeInputSourceRows_of_selectedNeighborGeometricOrder_selectedHeadRows_20260521k18`. -/
noncomputable def
    boundaryFreeSelectedEdgeInputSourceRows_family_of_selectedNeighborGeometricOrder_selectedHeadRows_20260521k18
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadRows
            (S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_selectedNeighborGeometricOrderSourceRows_20260521k6h
              (C := C) (inputs := inputs) (selectedRows C inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeSelectedEdgeInputSourceRows inputs := by
  intro m C inputs
  exact
    boundaryFreeSelectedEdgeInputSourceRows_of_selectedNeighborGeometricOrder_selectedHeadRows_20260521k18
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (endpointRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-p2j-boundary-free-selected-edge-source-20260521p3`.

Selected-neighbour/geometric-order rows supply the selected incident-edge field
of `BoundaryFreeSelectedEdgeInputSourceRows`; the remaining global
incident-germ field is kept as the genuine selected-frontier-edge membership
source.  This is a strict source-field reduction only: it does not use
all-adjacent endpoint closure, final boundary-cycle rows, or a W32 composer. -/
noncomputable def
    boundaryFreeSelectedEdgeInputSourceRows_of_selectedNeighborGeometricOrder_incidentGermFrontierEdge_20260521p3
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (incidentGermRows :
      BoundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows inputs) :
    BoundaryFreeSelectedEdgeInputSourceRows inputs where
  selectedIncidentEdges :=
    S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_selectedNeighborGeometricOrderSourceRows_20260521k6h
      (C := C) (inputs := inputs) selectedRows
  incidentGermFrontierEdge := incidentGermRows

set_option linter.style.longLine false in
/-- Selected-neighbour incident-germ membership rows are exactly the
boundary-free selected-frontier-edge membership field, with the selected
geometric row retained only to align the source route. -/
theorem
    boundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows_of_selectedNeighborIncidentGermRows_20260521p3
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (incidentGermRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    BoundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows inputs := by
  simpa [BoundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows,
    S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows]
    using incidentGermRows

set_option linter.style.longLine false in
/-- Same p3 source-field reduction, stated with the existing selected-neighbour
incident-germ row from `S2LocalTwoGermAssembly`.

The local-radius incident-germ rows already in the project remain the sharp
local support theorem; the global arbitrary-radius membership row is still the
honest residual for this selected-edge input package. -/
noncomputable def
    boundaryFreeSelectedEdgeInputSourceRows_of_selectedNeighborGeometricOrder_selectedIncidentGermRows_20260521p3
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (incidentGermRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    BoundaryFreeSelectedEdgeInputSourceRows inputs :=
  boundaryFreeSelectedEdgeInputSourceRows_of_selectedNeighborGeometricOrder_incidentGermFrontierEdge_20260521p3
    (C := C) (inputs := inputs) selectedRows
    (boundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows_of_selectedNeighborIncidentGermRows_20260521p3
      (C := C) (inputs := inputs) selectedRows incidentGermRows)

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeSelectedEdgeInputSourceRows_of_selectedNeighborGeometricOrder_selectedIncidentGermRows_20260521p3`. -/
noncomputable def
    boundaryFreeSelectedEdgeInputSourceRows_family_of_selectedNeighborGeometricOrder_selectedIncidentGermRows_20260521p3
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (incidentGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeSelectedEdgeInputSourceRows inputs := by
  intro m C inputs
  exact
    boundaryFreeSelectedEdgeInputSourceRows_of_selectedNeighborGeometricOrder_selectedIncidentGermRows_20260521p3
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (incidentGermRows C inputs)

set_option linter.style.longLine false in
/-- Component-topology rows from the same selected-neighbour geometric-order
carrier source used by the boundary-free selected-edge input row.

The planar-continuum theorem supplies actual frontier preconnectedness, while
the selected carrier rows supply the fixed-side selected-edge cover through the
checked local-sector eraser. -/
noncomputable def
    componentTopologyRows_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_20260521k18
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs := by
  let selectedEdgeRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs :=
    S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_selectedNeighborGeometricOrderSourceRows_20260521k6h
      (C := C) (inputs := inputs) selectedRows
  exact
    componentTopologySourceRows_of_frontierPreconnected_localSectorRows
      (C := C) inputs
      (by
        simpa [UnboundedExteriorActualFrontierPreconnectedSource] using
          S2_dyn_20260520_frontier_preconnected_source_of_planarContinuum
            (C := C) inputs frontier_preconnected)
      (S2LocalTwoGermAssembly.localSectorRows_of_selectedIncidentEdgePairSourceRows
        (C := C) (inputs := inputs) selectedEdgeRows)

set_option linter.style.longLine false in
/-- Family form of
`componentTopologyRows_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_20260521k18`. -/
noncomputable def
    componentTopologyRows_family_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_20260521k18
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologySourceRows inputs := by
  intro m C inputs
  exact
    componentTopologyRows_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_20260521k18
      (C := C) inputs frontier_preconnected (selectedRows C inputs)

set_option linter.style.longLine false in
/-- Paired source package for the S2 raw-orbit route.

This packages the two rows consumed together downstream: selected-edge
boundary-free input rows and component topology rows.  Both are built from the
same selected-neighbour carrier/geometric-order rows, so the selected
`unboundedFrontierEdgeSet` heads stay aligned across the local and topology
lanes. -/
noncomputable def
    boundaryFreeSelectedEdgeInputComponentTopologyRows_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_selectedHeadRows_20260521k18
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (endpointRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadRows
        (S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_selectedNeighborGeometricOrderSourceRows_20260521k6h
          (C := C) (inputs := inputs) selectedRows)) :
    Subtype
      (fun _ : BoundaryFreeSelectedEdgeInputSourceRows inputs =>
        UnboundedExteriorFrontierComponentTopologySourceRows inputs) :=
  ⟨boundaryFreeSelectedEdgeInputSourceRows_of_selectedNeighborGeometricOrder_selectedHeadRows_20260521k18
      (C := C) (inputs := inputs) selectedRows endpointRows,
    componentTopologyRows_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_20260521k18
      (C := C) inputs frontier_preconnected selectedRows⟩

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeSelectedEdgeInputComponentTopologyRows_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_selectedHeadRows_20260521k18`. -/
noncomputable def
    boundaryFreeSelectedEdgeInputComponentTopologyRows_family_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_selectedHeadRows_20260521k18
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadRows
            (S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_selectedNeighborGeometricOrderSourceRows_20260521k6h
              (C := C) (inputs := inputs) (selectedRows C inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Subtype
          (fun _ : BoundaryFreeSelectedEdgeInputSourceRows inputs =>
            UnboundedExteriorFrontierComponentTopologySourceRows inputs) := by
  intro m C inputs
  exact
    boundaryFreeSelectedEdgeInputComponentTopologyRows_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_selectedHeadRows_20260521k18
      (C := C) inputs frontier_preconnected
      (selectedRows C inputs) (endpointRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-boundary-free-raw-source-20260521o6`.

Selected-neighbour geometric-order rows, the local-radius incident-germ row,
and the same-germ endpoint selected-head row give the exact pair consumed by
the connected raw-orbit source worker: selected-edge boundary-free input rows
and component-topology rows.  The component side is built through
`BoundaryFreeLocalInputSourceReduction`, so only the local-radius
no-third-germ eraser is used there; the arbitrary-radius closed-germ branch
stays confined to the selected-edge input row. -/
noncomputable def
    boundaryFreeSelectedEdgeInputComponentTopologyRows_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_localIncident_selectedHeadRows_20260521o6
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (localIncidentRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource)
    (endpointRows :
      S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadRows
        (S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_selectedNeighborGeometricOrderSourceRows_20260521k6h
          (C := C) (inputs := inputs) selectedRows)) :
    Subtype
      (fun _ : BoundaryFreeSelectedEdgeInputSourceRows inputs =>
        UnboundedExteriorFrontierComponentTopologySourceRows inputs) := by
  let selectedEdgeRows :
      BoundaryFreeSelectedEdgeInputSourceRows inputs :=
    boundaryFreeSelectedEdgeInputSourceRows_of_selectedNeighborGeometricOrder_selectedHeadRows_20260521k18
      (C := C) (inputs := inputs) selectedRows endpointRows
  let localInput :
      BoundaryFreeLocalInputSourceReduction inputs :=
    boundaryFreeLocalInputSourceReduction_of_selectedNeighborGeometricOrder_localIncident_20260520
      (C := C) (inputs := inputs) selectedRows localIncidentRows
  let actualFrontierPreconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior) := by
    simpa [UnboundedExteriorActualFrontierPreconnectedSource] using
      S2_dyn_20260520_frontier_preconnected_source_of_planarContinuum
        (C := C) inputs frontier_preconnected
  exact
    ⟨selectedEdgeRows,
      localInput.toComponentTopologyRowsFromFrontierPreconnected
        (C := C) (inputs := inputs) actualFrontierPreconnected⟩

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeSelectedEdgeInputComponentTopologyRows_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_localIncident_selectedHeadRows_20260521o6`. -/
noncomputable def
    boundaryFreeSelectedEdgeInputComponentTopologyRows_family_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_localIncident_selectedHeadRows_20260521o6
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (localIncidentRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.IncidentGermEndpointSelectedHeadRows
            (S2LocalTwoGermAssembly.localSelectedIncidentEdgePairSourceRows_of_selectedNeighborGeometricOrderSourceRows_20260521k6h
              (C := C) (inputs := inputs) (selectedRows C inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Subtype
          (fun _ : BoundaryFreeSelectedEdgeInputSourceRows inputs =>
            UnboundedExteriorFrontierComponentTopologySourceRows inputs) := by
  intro m C inputs
  exact
    boundaryFreeSelectedEdgeInputComponentTopologyRows_of_planarContinuumPreconnected_selectedNeighborGeometricOrder_localIncident_selectedHeadRows_20260521o6
      (C := C) inputs frontier_preconnected
      (selectedRows C inputs) (localIncidentRows C inputs)
      (endpointRows C inputs)

set_option linter.style.longLine false in
/-- Current selected-carrier reduction of the local-sector residual.

The source is the actual selected carrier/geometric-selection package: its
two heads are genuine incident `unboundedFrontierEdgeSet` carrier edges, and
the local incident-germ branch is discharged by the checked local-radius
drawing-isolation theorem. -/
noncomputable def
    S2_codex_current_20260520_local_sector_residual_of_geometricSelection
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2LocalTwoGermAssembly.S2_codex_main_20260520_local_sector_close
    (C := C) (inputs := inputs) geometricSelection

set_option linter.style.longLine false in
/-- Current honest reduction of the incident-germ frontier-edge residual.

For arbitrary radii the closed-germ far endpoint branch would amount to a
no-chord assertion.  The finite drawing facts prove the sharp local-radius
form instead: after shrinking around the frontier vertex, any noncenter
frontier point in an incident W3 germ lies on an actual selected
`unboundedFrontierEdgeSet` edge. -/
theorem
    S2_codex_current_20260520_incident_germ_residual_reduced_to_local_radius
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
      (C := C) (inputs := inputs) geometricSelection :=
  S2LocalTwoGermAssembly.S2_dyn_20260520_incident_germ_global_source_reduced_to_local_radius
    (C := C) (inputs := inputs) geometricSelection

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-local-sector-incident-germ-leaf`.

Strict local-radius replacement for the two residuals exposed by
`S2_codex_current_20260520_boundaryfree_input_reduction_leaf`: selected
carrier local-sector rows are projected from actual selected carrier/geometric
data, and the incident-germ selected-edge membership is reduced to the local
radius row proved from finite drawing isolation.  This produces the corrected
local input package, not the stronger global closed-germ package that would
need a separate endpoint selected-edge source. -/
noncomputable def
    S2_codex_current_20260520_local_sector_incident_germ_leaf
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    BoundaryFreeLocalInputSourceReduction inputs :=
  boundaryFreeLocalInputSourceReduction_of_geometricSelection_localIncident_20260520
    (C := C) (inputs := inputs) geometricSelection

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_current_20260520_local_sector_incident_germ_leaf`. -/
noncomputable def
    S2_codex_current_20260520_local_sector_incident_germ_leaf_family
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalInputSourceReduction inputs := by
  intro m C inputs
  exact
    S2_codex_current_20260520_local_sector_incident_germ_leaf
      (C := C) (inputs := inputs) (geometricSelection C inputs)

set_option linter.style.longLine false in
/-- Local selected-neighbour rows plus the honest endpoint selected-edge row
reduce the global boundary-free input source.

This is the valid global closed-germ route: endpoint cases are handled only
after the adjacent graph edge has been proved to be an actual selected
`unboundedFrontierEdgeSet` edge. -/
noncomputable def
    boundaryFreeInputSourceReduction_of_localSelectedNeighborRows_endpointFrontier_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localRows :
      S2LocalTwoGermAssembly.LocalSelectedNeighborSourceRows inputs)
    (endpoint_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeInputSourceReduction inputs where
  localTwoGermRows := localRows.localTwoGermRows
  boundaryFreeNoThirdGermSource :=
    boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier
      (C := C) (inputs := inputs)
      localRows.localSectorRows endpoint_frontier_edge

set_option linter.style.longLine false in
/-- Family form of the selected-edge endpoint-frontier global input reducer. -/
noncomputable def
    boundaryFreeInputSourceReductionFamily_of_localSelectedNeighborRows_endpointFrontier_20260520
    (localRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.LocalSelectedNeighborSourceRows inputs)
    (endpoint_frontier_edge :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs})
            (x : Fin m),
            (canonicalGraph C).Adj a.1 x ->
              (canonicalGraph C).point x ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                  (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeInputSourceReduction_of_localSelectedNeighborRows_endpointFrontier_20260520
      (C := C) (inputs := inputs)
      (localRows C inputs) (endpoint_frontier_edge C inputs)

set_option linter.style.longLine false in
/-- Geometric-selection rows plus the honest incident-germ selected-edge row
fill the global boundary-free input package.

This is the selected-edge-gated replacement for endpoint-only/no-chord
reducers: the selected carrier heads are projected from the geometric-selection
source, and the closed-germ branch is discharged only by proving the incident
germ lies on an actual selected `unboundedFrontierEdgeSet` edge. -/
noncomputable def
    boundaryFreeInputSourceReduction_of_geometricSelection_incidentGermFrontierEdge_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (incidentGermFrontierEdgeRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs) geometricSelection) :
    BoundaryFreeInputSourceReduction inputs := by
  let localRows :
      S2LocalTwoGermAssembly.LocalSelectedNeighborSourceRows inputs :=
    S2LocalTwoGermAssembly.localSelectedNeighborRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) geometricSelection
  let selectedEdgeRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs :=
    S2LocalTwoGermAssembly.S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) geometricSelection
  exact
    { localTwoGermRows := localRows.localTwoGermRows
      boundaryFreeNoThirdGermSource :=
        boundaryFreeNoThirdGermSource_of_selectedIncidentEdgePairRows_incidentGermFrontierEdge
          (C := C) (inputs := inputs)
          selectedEdgeRows incidentGermFrontierEdgeRows }

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeInputSourceReduction_of_geometricSelection_incidentGermFrontierEdge_20260520`. -/
noncomputable def
    boundaryFreeInputSourceReductionFamily_of_geometricSelection_incidentGermFrontierEdge_20260520
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeInputSourceReduction_of_geometricSelection_incidentGermFrontierEdge_20260520
      (C := C) (inputs := inputs)
      (geometricSelection C inputs) (incidentGermFrontierEdgeRows C inputs)

set_option linter.style.longLine false in
/-- Compact geometric-neighbour row form of the selected-edge-gated
boundary-free input package. -/
noncomputable def
    boundaryFreeInputSourceReduction_of_geometricNeighborSelection_incidentGermFrontierEdge_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
        inputs)
    (incidentGermFrontierEdgeRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs) rows.toGeometricSelectionInputSource) :
    BoundaryFreeInputSourceReduction inputs :=
  boundaryFreeInputSourceReduction_of_geometricSelection_incidentGermFrontierEdge_20260520
    (C := C) (inputs := inputs)
    rows.toGeometricSelectionInputSource incidentGermFrontierEdgeRows

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeInputSourceReduction_of_geometricNeighborSelection_incidentGermFrontierEdge_20260520`. -/
noncomputable def
    boundaryFreeInputSourceReductionFamily_of_geometricNeighborSelection_incidentGermFrontierEdge_20260520
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
            inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (rows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeInputSourceReduction_of_geometricNeighborSelection_incidentGermFrontierEdge_20260520
      (C := C) (inputs := inputs)
      (rows C inputs) (incidentGermFrontierEdgeRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-main-20260520-boundaryfree-no-third-source`.

The global closed-germ no-third source is projected from the selected-edge
gated boundary-free input package.  Its only source rows are actual selected
geometric carrier neighbours and the matching incident-germ membership in
`unboundedFrontierEdgeSet`; no all-adjacent endpoint/chord classifier is used.
-/
noncomputable def
    S2_codex_main_20260520_boundaryfree_no_third_source_of_geometricSelection_incidentGermFrontierEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (incidentGermFrontierEdgeRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs) geometricSelection) :
    BoundaryFreeNoThirdGermSource inputs :=
  (boundaryFreeInputSourceReduction_of_geometricSelection_incidentGermFrontierEdge_20260520
    (C := C) (inputs := inputs) geometricSelection
    incidentGermFrontierEdgeRows).boundaryFreeNoThirdGermSource

set_option linter.style.longLine false in
/-- Selected-neighbour geometric-order form of the boundary-free no-third
source reduction.

The selected heads used by the no-third source are exactly the heads supplied
by `selectedRows.toGeometricSelectionInputSource`; the incident-germ row is
therefore aligned to the same actual carrier neighbours. -/
noncomputable def
    S2_codex_main_20260520_boundaryfree_no_third_source_of_selectedNeighborGeometricOrder_incidentGermFrontierEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (incidentGermFrontierEdgeRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_codex_main_20260520_boundaryfree_no_third_source_of_geometricSelection_incidentGermFrontierEdge
    (C := C) (inputs := inputs)
    selectedRows.toGeometricSelectionInputSource
    incidentGermFrontierEdgeRows

set_option linter.style.longLine false in
/-- Family form of the selected-neighbour boundary-free no-third source
reduction. -/
noncomputable def
    S2_codex_main_20260520_boundaryfree_no_third_source_family_of_selectedNeighborGeometricOrder_incidentGermFrontierEdge
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeNoThirdGermSource inputs := by
  intro m C inputs
  exact
    S2_codex_main_20260520_boundaryfree_no_third_source_of_selectedNeighborGeometricOrder_incidentGermFrontierEdge
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (incidentGermFrontierEdgeRows C inputs)

set_option linter.style.longLine false in
/-- The safe local-radius selected-neighbour point-sector row is enough for the
fixed-side local-sector input needed by carrier connectedness.  This avoids the
too-strong global local-angular source. -/
theorem unboundedFrontierCarrierGraph_connected_of_planarContinuum_geometricSelection_localThirdGerm
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (localThirdGermRows :
      S2LocalTwoGermAssembly.SelectedNeighborThirdGermLocalExteriorPointSectorRows
        (C := C) (inputs := inputs) geometricSelection) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_planarContinuum_localSectorRows
    inputs frontier_preconnected
    (S2LocalTwoGermAssembly.localSectorRows_of_selectedNeighborThirdGermLocalExteriorPointSectorRows
      (C := C) (inputs := inputs) geometricSelection localThirdGermRows)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-boundaryfree-local-sector-hardening`.

Primitive local-sector reducer from actual selected carrier/geometric rows and
the local-radius incident-germ membership row.  The source consumed here is
the honest finite-drawing row saying that a sufficiently local frontier point
in an incident W3 germ lies on an actual selected `unboundedFrontierEdgeSet`
edge; the selected neighbours and geometric no-between order then supply the
local sector. -/
noncomputable def localSectorRows_of_geometricSelection_localIncident
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (localIncidentRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs) geometricSelection) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2LocalTwoGermAssembly.localSectorRows_of_selectedNeighborThirdGermLocalExteriorPointSectorRows
    (C := C) (inputs := inputs) geometricSelection
    (S2LocalTwoGermAssembly.selectedNeighborThirdGermLocalExteriorPointSectorRows_of_localIncidentGermMembership
      (C := C) (inputs := inputs) geometricSelection localIncidentRows)

set_option linter.style.longLine false in
/-- Family form of `localSectorRows_of_geometricSelection_localIncident`. -/
noncomputable def
    localSectorRowsFamily_of_geometricSelection_localIncident_20260520
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (localIncidentRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    localSectorRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) (geometricSelection C inputs)
      (localIncidentRows C inputs)

set_option linter.style.longLine false in
/-- Endpoint-only compatibility residual aligned with a local selected-neighbour
bundle.

This is a no-chord statement for callers that have separately ruled out
boundary chords.  It should not be treated as a theorem of
`FinitePlanarOuterComponentInputs` alone. -/
abbrev BoundaryFreeEndpointOnlyForLocalSelectedNeighborRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localRows :
      S2LocalTwoGermAssembly.LocalSelectedNeighborSourceRows inputs) :
    Prop :=
  forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
    (x : Fin n),
    (canonicalGraph C).Adj a.1 x →
      (canonicalGraph C).point x ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior →
        x = (localRows.localSectorRows a).left ∨
          x = (localRows.localSectorRows a).right

set_option linter.style.longLine false in
/-- Local selected-neighbour rows reduce the boundary-free input source.

The pointwise local two-germ field is taken directly from the same local
selected-neighbour bundle, while the stronger global no-third-germ field is
first routed through the honest endpoint selected-edge row.  The endpoint-only
premise below is retained only as a compatibility source for callers that have
already ruled out boundary chords by some stronger argument. -/
noncomputable def
    boundaryFreeInputSourceReduction_of_localSelectedNeighborRows_endpointOnly_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localRows :
      S2LocalTwoGermAssembly.LocalSelectedNeighborSourceRows inputs)
    (endpoint_only :
      BoundaryFreeEndpointOnlyForLocalSelectedNeighborRows
        (C := C) (inputs := inputs) localRows) :
    BoundaryFreeInputSourceReduction inputs where
  localTwoGermRows := localRows.localTwoGermRows
  boundaryFreeNoThirdGermSource :=
    (boundaryFreeInputSourceReduction_of_localSelectedNeighborRows_endpointFrontier_20260520
      (C := C) (inputs := inputs)
      localRows
      (endpoint_frontier_edge_of_localSectorRows_endpointOnly
        (C := C) (inputs := inputs)
        localRows.localSectorRows endpoint_only)).boundaryFreeNoThirdGermSource

set_option linter.style.longLine false in
/-- Endpoint-only compatibility residual for the compact geometric-selection
source, after it has been reduced to the local selected-neighbour bundle by the
local-sector closer. -/
abbrev BoundaryFreeEndpointOnlyForGeometricSelectionLocalIncident
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    Prop :=
  BoundaryFreeEndpointOnlyForLocalSelectedNeighborRows
    (C := C) (inputs := inputs)
    (S2LocalTwoGermAssembly.localSelectedNeighborRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) geometricSelection)

set_option linter.style.longLine false in
/-- Compact selected-neighbour geometric rows reduce the boundary-free input
source consumed by the connected raw-orbit package.

The local sector/two-germ fields are closed from actual selected
`unboundedFrontierEdgeSet` neighbour rows and genuine geometric order.  The
endpoint-only argument is a compatibility no-chord premise; the proof routes it
through the selected-edge endpoint-frontier reducer. -/
noncomputable def
    boundaryFreeInputSourceReduction_of_geometricSelection_endpointOnly_localIncident_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (endpoint_only :
      BoundaryFreeEndpointOnlyForGeometricSelectionLocalIncident
        (C := C) (inputs := inputs) geometricSelection) :
    BoundaryFreeInputSourceReduction inputs :=
  boundaryFreeInputSourceReduction_of_localSelectedNeighborRows_endpointOnly_20260520
    (C := C) (inputs := inputs)
    (S2LocalTwoGermAssembly.localSelectedNeighborRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) geometricSelection)
    endpoint_only

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeInputSourceReduction_of_geometricSelection_endpointOnly_localIncident_20260520`. -/
noncomputable def
    boundaryFreeInputSourceReductionFamily_of_geometricSelection_endpointOnly_localIncident_20260520
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (endpoint_only :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeEndpointOnlyForGeometricSelectionLocalIncident
            (C := C) (inputs := inputs) (geometricSelection C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeInputSourceReduction_of_geometricSelection_endpointOnly_localIncident_20260520
      (C := C) (inputs := inputs)
      (geometricSelection C inputs) (endpoint_only C inputs)

set_option linter.style.longLine false in
/-- Endpoint-only compatibility residual for selected-neighbour geometric-order
source rows, phrased through their compact geometric-selection erasure. -/
abbrev BoundaryFreeEndpointOnlyForSelectedNeighborGeometricOrderLocalIncident
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs) :
    Prop :=
  BoundaryFreeEndpointOnlyForGeometricSelectionLocalIncident
    (C := C) (inputs := inputs)
    selectedRows.toGeometricSelectionInputSource

set_option linter.style.longLine false in
/-- Selected-neighbour geometric-order rows reduce the boundary-free input
source used by the connected raw-orbit route.

This is the selected-order-facing form of the geometric-selection reducer:
the local rows come from the same selected carrier heads and genuine outgoing
geometric order, while the endpoint-only argument remains a compatibility
no-chord premise for callers that can justify it. -/
noncomputable def
    boundaryFreeInputSourceReduction_of_selectedNeighborGeometricOrder_endpointOnly_localIncident_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (endpoint_only :
      BoundaryFreeEndpointOnlyForSelectedNeighborGeometricOrderLocalIncident
        (C := C) (inputs := inputs) selectedRows) :
    BoundaryFreeInputSourceReduction inputs :=
  boundaryFreeInputSourceReduction_of_geometricSelection_endpointOnly_localIncident_20260520
    (C := C) (inputs := inputs)
    selectedRows.toGeometricSelectionInputSource endpoint_only

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeInputSourceReduction_of_selectedNeighborGeometricOrder_endpointOnly_localIncident_20260520`. -/
noncomputable def
    boundaryFreeInputSourceReductionFamily_of_selectedNeighborGeometricOrder_endpointOnly_localIncident_20260520
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (endpoint_only :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeEndpointOnlyForSelectedNeighborGeometricOrderLocalIncident
            (C := C) (inputs := inputs) (selectedRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeInputSourceReduction inputs := by
  intro m C inputs
  exact
    boundaryFreeInputSourceReduction_of_selectedNeighborGeometricOrder_endpointOnly_localIncident_20260520
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (endpoint_only C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-boundaryfree-cycle-composer`.

Preconnected frontier topology plus the bundled geometric selected-neighbour
source gives the final exterior frontier cycle rows in one owner-file handoff.
The local branch is exactly the current local-incident geometric-selection
reducer; no additional source package is introduced. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_geometricSelectionInputSource_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_localSectorRows
    (C := C) inputs frontier_preconnected
    (localSectorRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) geometricSelection
      (S2LocalTwoGermAssembly.selectedNeighborIncidentGermLocalFrontierEdgeMembershipRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection))

set_option linter.style.longLine false in
/-- Family-level composer for the current shortest checked S2 source leaves.

The topology leaf is the Janiszewski no-subcontinuum obstruction; the local
leaf is the bundled actual carrier geometric-selection input source.  The
result is the input-level `UnboundedExteriorFrontierCycleRows` family consumed
by W32, with no additional source package. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_janiszewskiNoSubcontinuum_geometricSelectionInputSource_20260520
    (janiszewski_no_subcontinuum :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs := by
  intro m C inputs
  exact
    unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_geometricSelectionInputSource_20260520
      (C := C) inputs
      (planarContinuumUnboundedComplementFrontierPreconnected_of_janiszewskiNoSubcontinuumObstruction
        janiszewski_no_subcontinuum)
      (geometricSelection C inputs)

set_option linter.style.longLine false in
/-- No-closed-separation topology plus bundled actual carrier/geometric
selection rows give the unbounded exterior cycle rows.

This is a compact local-source variant of the direct S2 route: the
geometric-selection rows supply the pointwise local-sector family, and the
topology theorem supplies actual frontier preconnectedness. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_planarContinuumNoClosedSeparation_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      PlanarContinuumUnboundedComplementFrontierNoClosedSeparation)
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_planarContinuumNoClosedSeparation_localSectorRows
    (C := C) inputs frontier_noClosedSeparation
    (localSectorRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) geometricSelection
      (S2LocalTwoGermAssembly.selectedNeighborIncidentGermLocalFrontierEdgeMembershipRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection))

set_option linter.style.longLine false in
/-- Family-level no-closed-separation/geometric-selection S2 route.

This is the direct family consumed by W32: topology is the checked
no-closed-separation surface, and the local leaf is the existing bundled
geometric-selection input source. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumNoClosedSeparation_geometricSelectionInputSource_20260520
    (frontier_noClosedSeparation :
      PlanarContinuumUnboundedComplementFrontierNoClosedSeparation)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs := by
  intro m C inputs
  exact
    unboundedExteriorFrontierCycleRows_of_planarContinuumNoClosedSeparation_geometricSelectionInputSource
      (C := C) inputs frontier_noClosedSeparation (geometricSelection C inputs)

set_option linter.style.longLine false in
/-- Compact geometric-neighbour family form of the direct no-closed-separation
S2 route. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumNoClosedSeparation_geometricNeighborSelectionRows_20260520
    (frontier_noClosedSeparation :
      PlanarContinuumUnboundedComplementFrontierNoClosedSeparation)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumNoClosedSeparation_geometricSelectionInputSource_20260520
    frontier_noClosedSeparation
    (fun C inputs =>
      (geometricRows C inputs).toGeometricSelectionInputSource)

set_option linter.style.longLine false in
/-- Finite no-closed-separation topology plus bundled actual
carrier/geometric-selection rows give the unbounded exterior cycle rows.

This is the finite-topology variant of the direct no-closed-separation S2
route: the topology leaf is the actual finite drawing source, and the local
leaf is the existing bundled geometric-selection input source. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_localSectorRows
    (C := C) inputs frontier_noClosedSeparation
    (localSectorRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) geometricSelection
      (S2LocalTwoGermAssembly.selectedNeighborIncidentGermLocalFrontierEdgeMembershipRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection))

set_option linter.style.longLine false in
/-- Family-level finite no-closed-separation/geometric-selection S2 route. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_finiteDrawingNoClosedSeparation_geometricSelectionInputSource_20260520
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs := by
  intro m C inputs
  exact
    unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_geometricSelectionInputSource
      (C := C) inputs frontier_noClosedSeparation (geometricSelection C inputs)

set_option linter.style.longLine false in
/-- Compact geometric-neighbour family form of the finite no-closed-separation
S2 route. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_finiteDrawingNoClosedSeparation_geometricNeighborSelectionRows_20260520
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsFamily_of_finiteDrawingNoClosedSeparation_geometricSelectionInputSource_20260520
    frontier_noClosedSeparation
    (fun C inputs =>
      (geometricRows C inputs).toGeometricSelectionInputSource)

set_option linter.style.longLine false in
/-- Selected-edge route form of the local-sector reducer.

The remaining rows are the selected incident-edge pair package for the input
and the matching genuine outgoing-list no-between source for those same
selected heads.  They are first reduced to the actual carrier geometric
selection input, then passed to
`localSectorRows_of_geometricSelection_localIncident` with the primitive
local-radius incident-germ membership row. -/
noncomputable def
    localSectorRows_of_selectedEdgePairRoute_geometricOutgoingListNoBetween_localIncident_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  let geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2LocalTwoGermAssembly.S2_agent_20260520_geometricSelectionInputSource_of_selectedEdgePairRoute_geometricOutgoingListNoBetween
      (C := C) (inputs := inputs) selectedEdgeRows listRows
  exact
    localSectorRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) geometricSelection
      (S2LocalTwoGermAssembly.selectedNeighborIncidentGermLocalFrontierEdgeMembershipRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection)

set_option linter.style.longLine false in
/-- Family form of
`localSectorRows_of_selectedEdgePairRoute_geometricOutgoingListNoBetween_localIncident_20260520`.

This is the selected-edge-route version of the current local-sector leaf:
from each input's selected edge-pair rows and selected-head outgoing-list
no-between rows, it yields the pointwise local-sector family. -/
noncomputable def
    localSectorRowsFamily_of_selectedEdgePairRoute_geometricOutgoingListNoBetween_localIncident_20260520
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    localSectorRows_of_selectedEdgePairRoute_geometricOutgoingListNoBetween_localIncident_20260520
      (C := C) (inputs := inputs)
      (selectedEdgeRows C inputs) (listRows C inputs)

set_option linter.style.longLine false in
/-- Preconnected topology plus the current selected-edge outgoing-list route
give the final exterior frontier cycle rows directly.

This is the shortest checked owner-file handoff for the selected-edge route:
selected incident carrier edges and selected-head geometric no-between rows
first erase to pointwise local-sector rows, then the preconnected topology
reducer constructs `UnboundedExteriorFrontierCycleRows`. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_selectedEdgePair_geometricOutgoingListNoBetween_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedEdgeRows :
      S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_localSectorRows
    (C := C) inputs frontier_preconnected
    (localSectorRows_of_selectedEdgePairRoute_geometricOutgoingListNoBetween_localIncident_20260520
      (C := C) (inputs := inputs) selectedEdgeRows listRows)

set_option linter.style.longLine false in
/-- Family form of
`unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_selectedEdgePair_geometricOutgoingListNoBetween_20260520`. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_selectedEdgePair_geometricOutgoingListNoBetween_20260520
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs := by
  intro m C inputs
  exact
    unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_selectedEdgePair_geometricOutgoingListNoBetween_20260520
      (C := C) inputs frontier_preconnected
      (selectedEdgeRows C inputs) (listRows C inputs)

set_option linter.style.longLine false in
/-- The carrier-connectedness reducer no longer needs a separate
`localThirdGermRows` premise when the selected geometric-neighbour source is
available.

The local-sector branch is now fed through the primitive local-radius
incident-germ membership row, so the live residual is the selected
`unboundedFrontierEdgeSet` neighbour/geometric-selection source plus planar
frontier preconnectedness. -/
theorem unboundedFrontierCarrierGraph_connected_of_planarContinuum_geometricSelection_localIncident
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_planarContinuum_localSectorRows
    inputs frontier_preconnected
    (localSectorRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) geometricSelection
      (S2LocalTwoGermAssembly.selectedNeighborIncidentGermLocalFrontierEdgeMembershipRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection))

set_option linter.style.longLine false in
/-- Geometric neighbour selection plus the aligned endpoint-only row reduce the
fixed-side local-sector input needed for carrier connectedness. -/
theorem unboundedFrontierCarrierGraph_connected_of_planarContinuum_geometricSelection_endpointOnly
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (geometricSelection :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x =
                (S2LocalTwoGermAssembly.unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                  geometricSelection a).left.1 ∨
              x =
                (S2LocalTwoGermAssembly.unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                  geometricSelection a).right.1) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_planarContinuum_boundaryFreeGeometricAngularSource
    (C := C) inputs frontier_preconnected
    (S2LocalTwoGermAssembly.S2_dyn_20260520_local_angular_source_of_inputs
      (C := C) (inputs := inputs) geometricSelection endpoint_only)

/-- Claim `S2-dyn-20260520-boundaryfree-input-source`.

The remaining boundary-free local source is split at the input level.  The
local two-germ/no-third behavior is proved positively and endpoint-free from
the actual concrete carrier neighbour-pair rows, via the checked local reducer
in `S2LocalTwoGermAssembly`.  The stronger global
`BoundaryFreeNoThirdGermSource` is strictly reduced to the sharp endpoint
no-chord/two-neighbour row, using the existing incident-only eraser and no
all-adjacent endpoint incident/closure source, final boundary-cycle rows,
induced frontier graph, arbitrary carrier, or synthetic enclosure. -/
def S2_dyn_20260520_boundaryfree_input_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeNeighborPairEndpointOnlySourceRows inputs) :
    BoundaryFreeInputSourceReduction inputs where
  localTwoGermRows :=
    S2LocalTwoGermAssembly.localTwoGermRows_of_neighborPairRows
      (C := C) (inputs := inputs) rows.neighborRows
  boundaryFreeNoThirdGermSource :=
    rows.toBoundaryFreeNoThirdGermSource

/-- Family form of `S2_dyn_20260520_boundaryfree_input_source`. -/
def S2_dyn_20260520_boundaryfree_input_source_family
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeNeighborPairEndpointOnlySourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeInputSourceReduction inputs :=
  fun C inputs =>
    S2_dyn_20260520_boundaryfree_input_source
      (C := C) (inputs := inputs) (rows C inputs)

/-- Claim `S2-dyn-20260520-neighbor-pair-endpoint-only-source`.

Named form of the sharp boundary-free input cut.  The positive
`localTwoGermRows` field is proved from the selected concrete carrier
neighbour pairs alone; the stronger `BoundaryFreeNoThirdGermSource` field is
strictly reduced to `BoundaryFreeNeighborPairEndpointOnlySourceRows`, whose
endpoint branch says only that an adjacent frontier endpoint is one of those
two selected carrier neighbours. -/
def S2_dyn_20260520_neighbor_pair_endpoint_only_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeNeighborPairEndpointOnlySourceRows inputs) :
    BoundaryFreeInputSourceReduction inputs :=
  S2_dyn_20260520_boundaryfree_input_source
    (C := C) (inputs := inputs) rows

/-- Volta's endpoint-only wrapper fed by the actual selected-carrier neighbour
source above. -/
def S2_dyn_20260520_neighbor_pair_endpoint_only_source_of_selectedCarrierNeighborPairSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedNeighbors :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x =
                (selectedCarrierNeighborRows selectedNeighbors a).left.1 ∨
              x =
                (selectedCarrierNeighborRows selectedNeighbors a).right.1) :
    BoundaryFreeInputSourceReduction inputs :=
  S2_dyn_20260520_neighbor_pair_endpoint_only_source
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_carrier_neighbor_pair_source
      (C := C) (inputs := inputs) selectedNeighbors endpoint_only)

/-- Family form of
`S2_dyn_20260520_neighbor_pair_endpoint_only_source`. -/
def S2_dyn_20260520_neighbor_pair_endpoint_only_source_family
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeNeighborPairEndpointOnlySourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeInputSourceReduction inputs :=
  fun C inputs =>
    S2_dyn_20260520_neighbor_pair_endpoint_only_source
      (C := C) (inputs := inputs) (rows C inputs)

/-- Claim `S2-pool-cx-local-two-germ-source`.

The current deleted-neighbour source is strictly reduced to the pointwise
no-chord/two-neighbour source that feeds `BoundaryFreeNoThirdGermSource`.
This uses the already checked open-edge carrier-membership branch and does not
assume adjacent-frontier endpoint incident/closure rows, final boundary-cycle
rows, actual-boundary equivalence rows, induced frontier graphs, arbitrary
cycles, or synthetic enclosures. -/
def S2_pool_cx_unreachableAfterDeleteInputSource_of_neighborPairEndpointOnlyRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeNeighborPairEndpointOnlySourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  rows.toUnreachableAfterDeleteInputSource

/-- Family form of
`S2_pool_cx_unreachableAfterDeleteInputSource_of_neighborPairEndpointOnlyRows`. -/
def S2_pool_cx_unreachableAfterDeleteInputSource_family_of_neighborPairEndpointOnlyRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeNeighborPairEndpointOnlySourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_pool_cx_unreachableAfterDeleteInputSource_of_neighborPairEndpointOnlyRows
      (C := C) (inputs := inputs) (rows C inputs)

/-- Honest local endpoint-topology source for the remaining endpoint branch.

When two adjacent graph vertices both lie on the unbounded exterior frontier,
the source asks only for one frontier point in the relative interior of that
canonical edge.  The already checked pointwise frontier-edge topology then
promotes that edge to `unboundedFrontierEdgeSet`. -/
abbrev AdjacentFrontierEndpointsInteriorFrontierPointSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
    (x : Fin n),
    (canonicalGraph C).Adj a.1 x ->
      (canonicalGraph C).point x ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior ->
        Exists fun p : PlanarInterface.Point =>
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point a.1)
            ((canonicalGraph C).point x) ∧
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior

/-- Claim `S2-agent-adjacent-frontier-endpoints-interior-point-20260520z`.

The remaining endpoint-to-interior step is reduced to the smallest local
component-frontier interval row needed here: an adjacent pair of frontier
endpoints has some open-edge point in the closure of the same unbounded
exterior component.  Since canonical edge interiors are in the drawing, they
are not in the exterior component itself, so closure membership is exactly
frontier membership for the witness. -/
theorem S2_agent_adjacent_frontier_endpoints_interior_point_20260520z
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (interior_closure_point :
      AdjacentFrontierEndpointsInteriorClosurePointSource C inputs) :
    AdjacentFrontierEndpointsInteriorFrontierPointSource inputs := by
  intro a x hadj hxfrontier
  have hafrontier :
      (canonicalGraph C).point a.1 ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior :=
    mem_unboundedFrontierVertexSet_iff.1 a.2
  rcases interior_closure_point hadj hafrontier hxfrontier with
    ⟨p, hpopen, hpclosure⟩
  refine ⟨p, hpopen, ?_⟩
  rw [(unboundedExteriorComponentRows C inputs).exterior_open.frontier_eq]
  refine ⟨hpclosure, ?_⟩
  rcases hadj with hforward | hreverse
  · exact
      canonicalEdge_inOpenSegment_not_mem_unboundedExterior
        inputs hforward hpopen
  · exact
      canonicalEdge_inOpenSegment_not_mem_unboundedExterior
        inputs hreverse (inOpenSegment_symm hpopen)

/-- Reduce the endpoint frontier-edge closure to the local endpoint-interior
frontier source plus the pointwise interior-edge carrier membership row. -/
theorem endpoint_frontier_edge_of_adjacentFrontierEndpointsInteriorFrontierPointSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (endpoint_interior_frontier :
      AdjacentFrontierEndpointsInteriorFrontierPointSource inputs)
    (interior_edge_mem :
      InteriorFrontierEdgeCarrierMembershipSource C inputs) :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (x : Fin n),
      (canonicalGraph C).Adj a.1 x ->
        (canonicalGraph C).point x ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ->
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
            (x, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
  intro a x hadj hxfrontier
  rcases endpoint_interior_frontier a x hadj hxfrontier with
    ⟨p, hpopen, hpfrontier⟩
  rcases hadj with hforward | hreverse
  · exact Or.inl
      (interior_edge_mem (e := (a.1, x)) (p := p)
        hforward hpopen hpfrontier)
  · exact Or.inr
      (interior_edge_mem (e := (x, a.1)) (p := p)
        hreverse (inOpenSegment_symm hpopen) hpfrontier)

/-- An interior frontier point on the edge between adjacent frontier endpoints
selects that adjacent edge in `unboundedFrontierEdgeSet`.

This is the object-level version of
`endpoint_frontier_edge_of_adjacentFrontierEndpointsInteriorFrontierPointSource`:
it discharges the primitive
`AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource` without using a
boundary cycle or an induced frontier graph. -/
theorem adjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource_of_interiorFrontierPoint
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (endpoint_interior_frontier :
      AdjacentFrontierEndpointsInteriorFrontierPointSource inputs) :
    AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs := by
  intro i j hij hifrontier hjfrontier
  let a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨i, mem_unboundedFrontierVertexSet_iff.2 hifrontier⟩
  simpa [a] using
    endpoint_frontier_edge_of_adjacentFrontierEndpointsInteriorFrontierPointSource
      (C := C) (inputs := inputs)
      endpoint_interior_frontier
      interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
      a j hij hjfrontier

/-- Closed-segment relative-openness supplies the incident selected-edge
source for adjacent frontier endpoints.

The proof goes through the midpoint/interior-frontier-point reducer and then
promotes that point to concrete `unboundedFrontierEdgeSet` membership. -/
theorem adjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource_of_closedSegmentClosure
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (closure_locus_relative_open :
      AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
        C inputs) :
    AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs :=
  adjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource_of_interiorFrontierPoint
    (C := C) (inputs := inputs)
    (S2_agent_adjacent_frontier_endpoints_interior_point_20260520z
      (C := C) (inputs := inputs)
      (S2_agent_adjacent_frontier_endpoints_interior_closure_real_source_20260520ac
        (C := C) (inputs := inputs)
        closure_locus_relative_open))

/-- Selected endpoint-frontier edges supply the endpoint-side closure row for
the closed-segment relative-openness route.

At an endpoint, choose a radius smaller than the canonical edge length.  A
closed-segment point in that radius is either the endpoint itself, hence in
the exterior closure by frontier membership, or a relative-interior point of a
selected `unboundedFrontierEdgeSet` edge, hence on the exterior frontier. -/
theorem adjacentFrontierEndpointsClosedSegmentEndpointClosureSource_of_endpointFrontierEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (endpoint_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs := by
  intro i j hij hifrontier hjfrontier
  let a : PlanarInterface.Point := (canonicalGraph C).point i
  let b : PlanarInterface.Point := (canonicalGraph C).point j
  let vi : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨i, mem_unboundedFrontierVertexSet_iff.2 hifrontier⟩
  have hedge :
      (i, j) ∈ unboundedFrontierEdgeSet C inputs ∨
        (j, i) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [vi] using endpoint_frontier_edge vi j hij hjfrontier
  have hdist_pos : 0 < dist a b := by
    exact dist_pos.mpr (by simpa [a, b] using canonical_adj_point_ne hij)
  let r : Real := dist a b / 2
  have hrpos : 0 < r := half_pos hdist_pos
  have hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  constructor
  · refine ⟨r, hrpos, ?_⟩
    intro z hzball hzseg
    rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hzseg with
      hz_left | hz_right | hz_open
    · simpa [a, hz_left] using frontier_subset_closure hifrontier
    · have hlt : dist a b < dist a b / 2 := by
        simpa [Metric.mem_ball, a, b, r, hz_right, dist_comm] using hzball
      exact False.elim (by linarith)
    · have hzfrontier :
          z ∈ frontier (unboundedExteriorComponentRows C inputs).exterior := by
        rcases hedge with hedge | hedge
        · exact hwhole (i, j) hedge z (by simpa [a, b] using hz_open)
        · exact hwhole (j, i) hedge z
            (by simpa [a, b] using inOpenSegment_symm hz_open)
      exact frontier_subset_closure hzfrontier
  · refine ⟨r, hrpos, ?_⟩
    intro z hzball hzseg
    rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hzseg with
      hz_left | hz_right | hz_open
    · have hlt : dist a b < dist a b / 2 := by
        simpa [Metric.mem_ball, a, b, r, hz_left] using hzball
      exact False.elim (by linarith)
    · simpa [b, hz_right] using frontier_subset_closure hjfrontier
    · have hzfrontier :
          z ∈ frontier (unboundedExteriorComponentRows C inputs).exterior := by
        rcases hedge with hedge | hedge
        · exact hwhole (i, j) hedge z (by simpa [a, b] using hz_open)
        · exact hwhole (j, i) hedge z
            (by simpa [a, b] using inOpenSegment_symm hz_open)
      exact frontier_subset_closure hzfrontier

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundaryfree-selected-endpoint-route-20260520g2`.

Selected-edge endpoint closure for the boundary-free local route.

This theorem is deliberately stated for an already selected
`unboundedFrontierEdgeSet` edge, in either orientation.  It exposes the safe
endpoint reducer used by the local route without assuming the all-adjacent
frontier-endpoint source that would also classify possible frontier chords. -/
theorem S2_agent_boundaryfree_selected_endpoint_closure_of_unboundedFrontierEdgeSet_20260520g2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {i j : Fin n}
    (hselected :
      (i, j) ∈ unboundedFrontierEdgeSet C inputs ∨
        (j, i) ∈ unboundedFrontierEdgeSet C inputs) :
    (Exists fun r : Real =>
      0 < r ∧
        forall z : PlanarInterface.Point,
          z ∈ Metric.ball ((canonicalGraph C).point i) r →
          z ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) →
          z ∈ closure
            (unboundedExteriorComponentRows C inputs).exterior) ∧
    (Exists fun r : Real =>
      0 < r ∧
        forall z : PlanarInterface.Point,
          z ∈ Metric.ball ((canonicalGraph C).point j) r →
          z ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) →
          z ∈ closure
            (unboundedExteriorComponentRows C inputs).exterior) :=
  selectedUnboundedFrontierEdgeEndpointClosureSource_of_selectedIncidentEdge
    (C := C) (inputs := inputs)
    selectedUnboundedFrontierEdgeEndpointClosureSource_of_definition
    hselected

/-- Endpoint-frontier edge membership closes the closed-segment
relative-openness source used by the endpoint branch of the boundary-free S2
route. -/
theorem adjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource_of_endpointFrontierEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (endpoint_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
      C inputs :=
  AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource_of_endpointClosure
    (adjacentFrontierEndpointsClosedSegmentEndpointClosureSource_of_endpointFrontierEdge
      (C := C) (inputs := inputs) endpoint_frontier_edge)

/-- Object-level producer for the local-sector/endpoint-frontier subtype.

This is the sharp local reduction of the remaining endpoint source: local
sector rows provide the subtype carrier, while the finite-plane endpoint
topology row is converted to concrete selected frontier-edge membership by the
interior-edge carrier membership source. -/
def localSectorEndpointFrontierInputSource_of_endpointInteriorFrontierPoint
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_interior_frontier :
      AdjacentFrontierEndpointsInteriorFrontierPointSource inputs)
    (interior_edge_mem :
      InteriorFrontierEdgeCarrierMembershipSource C inputs) :
    Subtype fun _ :
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a) =>
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
  ⟨localSectorRows,
    endpoint_frontier_edge_of_adjacentFrontierEndpointsInteriorFrontierPointSource
      (C := C) (inputs := inputs)
      endpoint_interior_frontier interior_edge_mem⟩

/-- Claim `S2-agent-local-sector-endpoint-frontier-input-source-20260520y`.

Input-facing subtype producer after the pointwise frontier-edge local topology
has been discharged.  The only remaining source row says that adjacent
frontier endpoints contain an actual frontier point in the open edge between
them; no boundary cycle, final S2 row, induced frontier graph, spanning cycle,
or synthetic enclosure is used. -/
def S2_agent_local_sector_endpoint_frontier_input_source_20260520y
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_interior_frontier :
      AdjacentFrontierEndpointsInteriorFrontierPointSource inputs) :
    Subtype fun _ :
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a) =>
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
  localSectorEndpointFrontierInputSource_of_endpointInteriorFrontierPoint
    (C := C) (inputs := inputs)
  localSectorRows endpoint_interior_frontier
  interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point

/-- Closed-segment relative openness is the current non-circular local
endpoint source for the endpoint-frontier branch.

This theorem wires that primitive source through the checked closure-point and
interior-frontier reducers, producing the exact subtype consumed by
`S2_agent_boundaryfree_local_source_input_20260520x`. -/
def S2_agent_local_sector_endpoint_frontier_input_source_of_closedSegmentClosure_20260520ae
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (closure_locus_relative_open :
      AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
        C inputs) :
    Subtype fun _ :
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a) =>
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
              (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
  S2_agent_local_sector_endpoint_frontier_input_source_20260520y
    (C := C) (inputs := inputs)
    localSectorRows
    (S2_agent_adjacent_frontier_endpoints_interior_point_20260520z
      (C := C) (inputs := inputs)
      (S2_agent_adjacent_frontier_endpoints_interior_closure_real_source_20260520ac
        (C := C) (inputs := inputs)
        closure_locus_relative_open))

/-- Boundary-free source from the current primitive local-sector and
closed-segment endpoint topology rows. -/
def S2_boundaryFreeNoThirdGermSource_of_localSectorRows_closedSegmentClosure_20260520ae
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (closure_locus_relative_open :
      AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
        C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier
    (C := C) (inputs := inputs)
    (S2_agent_local_sector_endpoint_frontier_input_source_of_closedSegmentClosure_20260520ae
      (C := C) (inputs := inputs)
      localSectorRows closure_locus_relative_open).1
    (S2_agent_local_sector_endpoint_frontier_input_source_of_closedSegmentClosure_20260520ae
      (C := C) (inputs := inputs)
      localSectorRows closure_locus_relative_open).2

/-- Endpoint one-sided closure is enough for the boundary-free no-third-germ
source once the local-sector family has been supplied. -/
def S2_boundaryFreeNoThirdGermSource_of_localSectorRows_endpointClosure_20260520af
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_closure :
      AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_boundaryFreeNoThirdGermSource_of_localSectorRows_closedSegmentClosure_20260520ae
    (C := C) (inputs := inputs)
    localSectorRows
    (S2_agent_closed_segment_closure_relative_open_source_20260520ae
      (C := C) (inputs := inputs) endpoint_closure)

/-- Incident selected frontier-edge source is enough for the boundary-free
no-third-germ source once local sectors have been supplied. -/
def S2_boundaryFreeNoThirdGermSource_of_localSectorRows_incidentEdge_20260520af
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_boundaryFreeNoThirdGermSource_of_localSectorRows_endpointClosure_20260520af
    (C := C) (inputs := inputs)
    localSectorRows
    (closedSegmentEndpointClosureSource_of_incidentUnboundedFrontierEdgeSource
      (C := C) (inputs := inputs) incident_edge)

/-- Final-row eraser through the edge-chain/local-sector S2 source route.

This is the same primitive endpoint source as above, but it avoids the raw
face-successor orbit route: connectedness of the concrete carrier gives the
edge-chain source, local sectors give the two-germ boundary source, and the
closed-segment endpoint source supplies endpoint incident closure. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_localSectorRows_closedSegmentClosure_carrierConnected
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (closure_locus_relative_open :
      AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
        C inputs)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_of_edgeChain_localSector_endpointIncidentRows
    (C := C) (inputs := inputs)
    (unboundedFrontierEdgeCarrierSegmentChainConnected_of_unboundedFrontierCarrierGraph_connected
      (C := C) (inputs := inputs) carrier_connected)
    localSectorRows
    (S2_agent_local_sector_endpoint_frontier_input_source_of_closedSegmentClosure_20260520ae
      (C := C) (inputs := inputs)
      localSectorRows closure_locus_relative_open).2

/-- Endpoint-closure form of the edge-chain/local-sector S2 eraser. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_localSectorRows_endpointClosure_carrierConnected
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_closure :
      AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_localSectorRows_closedSegmentClosure_carrierConnected
    (C := C) (inputs := inputs)
    localSectorRows
    (S2_agent_closed_segment_closure_relative_open_source_20260520ae
      (C := C) (inputs := inputs) endpoint_closure)
    carrier_connected

/-- Incident-edge form of the edge-chain/local-sector S2 eraser. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_localSectorRows_incidentEdge_carrierConnected
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_localSectorRows_endpointClosure_carrierConnected
    (C := C) (inputs := inputs)
    localSectorRows
    (closedSegmentEndpointClosureSource_of_incidentUnboundedFrontierEdgeSource
      (C := C) (inputs := inputs) incident_edge)
    carrier_connected

/-- Neighbour-pair form of the connected-carrier / incident-edge S2 eraser.

The two local sector heads are obtained from the actual carrier neighbour-pair
row, while the endpoint branch is still the honest incident selected-edge
source. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_neighborPairRows_incidentEdge_carrierConnected
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_localSectorRows_incidentEdge_carrierConnected
    (C := C) (inputs := inputs)
    (S2LocalTwoGermAssembly.localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
      (C := C) inputs neighborRows)
    incident_edge
    carrier_connected

/-- Component-topology connectedness plus neighbour-pair and incident-edge
sources close the boundary-free concrete-carrier S2 route. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_componentTopology_neighborPairRows_incidentEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (componentTopologyRows :
      UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_neighborPairRows_incidentEdge_carrierConnected
    (C := C) (inputs := inputs)
    neighborRows
    incident_edge
    (unboundedFrontierCarrierGraph_connected_of_componentTopologySourceRows
      inputs componentTopologyRows)

/-- Edge-chain form of the neighbour-pair / incident-edge S2 eraser.

The neighbour-pair rows now supply both the local sector family and the
frontier-vertex incident source for the component-topology package. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_edgeChain_neighborPairRows_incidentEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_componentTopology_neighborPairRows_incidentEdge
    (C := C) (inputs := inputs)
    (unboundedExteriorFrontierComponentTopologySourceRows_of_edgeChain_vertexIncident
      (C := C) inputs edge_segment_chain
      (frontierVertexIncidentSource_of_neighborPairRows
        (C := C) (inputs := inputs) neighborRows))
    neighborRows
    incident_edge

/-- No-cut cut-partition form of the component-topology / incident-edge S2
eraser.

The cut-partition rows are the source-facing way to produce the two concrete
carrier neighbours: any third carrier neighbour would give a real cut vertex,
contradicting `inputs.noCutVertex`. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_componentTopology_neighborPairCutRows_incidentEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (componentTopologyRows :
      UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_componentTopology_neighborPairRows_incidentEdge
    (C := C) (inputs := inputs)
    componentTopologyRows
    (unboundedFrontierCarrierNeighborPairRows_of_noCutVertex_cutPartitionRows
      cutRows)
    incident_edge

/-- Edge-chain and no-cut cut-partition form of the neighbour-pair /
incident-edge S2 eraser. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_edgeChain_neighborPairCutRows_incidentEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_edgeChain_neighborPairRows_incidentEdge
    (C := C) (inputs := inputs)
    edge_segment_chain
    (unboundedFrontierCarrierNeighborPairRows_of_noCutVertex_cutPartitionRows
      cutRows)
    incident_edge

/-- Claim `S2-agent-boundaryfree-local-source-input-20260520x`, reduced to
one local theorem statement.

The exact remaining input is the subtype below: carrier local-sector rows at
each unbounded-frontier vertex, with endpoint frontier-edge closure for any
adjacent frontier endpoint. -/
def S2_agent_boundaryfree_local_source_input_20260520x
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (local_endpoint_source :
      Subtype fun _ :
          (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) =>
        forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (x : Fin n),
          (canonicalGraph C).Adj a.1 x ->
            (canonicalGraph C).point x ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ->
              (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier
    (C := C) (inputs := inputs)
    local_endpoint_source.1 local_endpoint_source.2

/-- The fixed-side half-ball topology supplies the strongest open-segment
component source behind the local exterior-side row.

For any open point `z` on an edge whose relative interior has one exterior
frontier point, the checked carrier-membership theorem first promotes the
whole edge to `unboundedFrontierEdgeSet`; hence `z` is itself a frontier point.
The existing fixed-side half-ball lemma then supplies one of the two local
exterior sides at every scale. -/
theorem interiorEdgeOpenSegmentLocalExteriorSideComponentSource_of_fixed_side_halfballs
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    InteriorEdgeOpenSegmentLocalExteriorSideComponentSource C inputs := by
  refine
    interiorEdgeOpenSegmentLocalExteriorSideComponentSource_of_signedSideBall_exterior_points
      (C := C) (inputs := inputs) ?_
  intro e p he hpEdge hpFrontier z hzEdge
  have hedge : e ∈ unboundedFrontierEdgeSet C inputs :=
    interior_frontier_edge_carrier_membership_source_of_fixed_side_halfballs
      (C := C) (inputs := inputs) he hpEdge hpFrontier
  have hzFrontier :
      z ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
    (mem_unboundedFrontierEdgeSet_iff.1 hedge).2 z hzEdge
  exact
    fixed_side_exterior_points_of_frontier_edge_point
      (C := C) (inputs := inputs) he hzEdge hzFrontier

/-- Claim `S2-agent-interior-edge-local-exterior-side-source-20260520bl`.

Input-level local exterior-side source for open canonical edges.  This is the
patch-shaped row consumed by `S2_agent_boundary_free_local_source_20260520bk`;
it is obtained from the stronger all-scale local component source above. -/
theorem S2_agent_interior_edge_local_exterior_side_source_20260520bl
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    InteriorEdgeLocalExteriorSideSource C inputs :=
  interiorEdgeLocalExteriorSideSource_of_component_source
    (C := C) (inputs := inputs)
    (interiorEdgeLocalExteriorSideComponentSource_of_openSegment_component_source
      (C := C) (inputs := inputs)
      (interiorEdgeOpenSegmentLocalExteriorSideComponentSource_of_fixed_side_halfballs
        (C := C) (inputs := inputs)))

/-- Claim `S2-agent-endpoint-closure-source-of-incident-edge-20260520bl`.

The sharper adjacent-frontier-endpoint incident-edge source erases to the
one-sided closed-segment endpoint-closure row.  This is a reducer from an
explicit selected-edge premise, not an input-level endpoint source. -/
theorem S2_agent_endpoint_closure_source_of_incident_edge_20260520bl
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs :=
  closedSegmentEndpointClosureSource_of_incidentUnboundedFrontierEdgeSource
    (C := C) (inputs := inputs) incident_edge

/-- Claim `S2-agent-boundary-free-local-source-20260520bk`.

Input-level boundary-free local source from the currently exposed local rows:
pointwise concrete carrier local sectors, the local exterior-side source for
open-edge carrier membership, and the endpoint one-sided closure row for
adjacent frontier endpoints.  No actual boundary cycle, raw orbit, or
synthetic enclosure predicate is used. -/
def S2_agent_boundary_free_local_source_20260520bk
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (local_exterior_side :
      InteriorEdgeLocalExteriorSideSource C inputs)
    (endpoint_closure :
      AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  boundaryFreeNoThirdGermSource_of_localSectorRows_endpointFrontier_interiorEdgeMem
    (C := C) (inputs := inputs)
    localSectorRows
    (fun a _x hadj hxfrontier =>
      incidentUnboundedFrontierEdgeSource_of_endpointClosure
        (C := C) (inputs := inputs) endpoint_closure
        hadj (mem_unboundedFrontierVertexSet_iff.1 a.2) hxfrontier)
    (interior_frontier_edge_carrier_membership_source_of_relative_ball_closure
      (C := C) (inputs := inputs)
      (S2_agent_interior_relative_ball_closure_source
        (C := C) (inputs := inputs)
        (S2_agent_interior_edge_nearby_exterior_point_source
          (C := C) (inputs := inputs) local_exterior_side)))

/-- Boundary-free local source with the interior-edge side row discharged by
the fixed-side half-ball topology.  The only remaining endpoint input is the
one-sided closed-segment closure source. -/
def S2_agent_boundary_free_local_source_of_endpointClosure_20260520bl
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpoint_closure :
      AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_agent_boundary_free_local_source_20260520bk
    (C := C) (inputs := inputs)
    localSectorRows
    (S2_agent_interior_edge_local_exterior_side_source_20260520bl
      (C := C) (inputs := inputs))
    endpoint_closure

/-- Boundary-free local source from the sharper adjacent-endpoint incident-edge
primitive; the endpoint-closure row and the interior-edge side row are both
erased internally. -/
def S2_agent_boundary_free_local_source_of_incidentEdge_20260520bl
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_agent_boundary_free_local_source_of_endpointClosure_20260520bl
    (C := C) (inputs := inputs)
    localSectorRows
    (S2_agent_endpoint_closure_source_of_incident_edge_20260520bl
      (C := C) (inputs := inputs) incident_edge)

/-- Claim `S2-agent-boundary-free-no-third-input-source-20260520bu`.

The current endpoint/source rows already give the boundary-free no-third-germ
input source.  The residual rows are exactly the pointwise concrete carrier
local-sector family and the honest selected adjacent-edge carrier source.
Endpoint one-sided closure is not an extra assumption here: it is obtained by
the checked `20260520bt` endpoint reducer from that selected-edge carrier row. -/
def S2_agent_boundary_free_no_third_input_source_20260520bu
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_agent_boundary_free_local_source_of_endpointClosure_20260520bl
    (C := C) (inputs := inputs)
    localSectorRows
    (S2_agent_endpoint_one_sided_closure_source_20260520bt
      (C := C) (inputs := inputs) incident_edge)

/-- Family form of `S2_agent_boundary_free_no_third_input_source_20260520bu`.

This is the minimal checked residual theorem for the boundary-free local S2
source: prove local-sector rows and the selected adjacent-edge carrier row for
each input instance. -/
def S2_agent_boundary_free_no_third_input_source_family_20260520bu
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (incident_edge :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  fun C inputs =>
    ⟨S2_agent_boundary_free_no_third_input_source_20260520bu
      (C := C) (inputs := inputs)
      (localSectorRows C inputs) (incident_edge C inputs)⟩

/-- Claim `S2-agent-incident-edge-closedSegmentClosure-cut-20260520bm`.

Closed-segment relative-openness is the current input-level local topology
source for the adjacent-frontier endpoint incident-edge row.  This names the
exact source cut used by the BL endpoint-closure eraser, without passing
through actual boundary-cycle or unbounded-frontier-cycle rows. -/
theorem S2_agent_adjacent_frontier_endpoints_incident_edge_source_of_closedSegmentClosure_20260520bm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (closure_locus_relative_open :
      AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
        C inputs) :
    AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs :=
  adjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource_of_closedSegmentClosure
    (C := C) (inputs := inputs) closure_locus_relative_open

/-- Boundary-free local source from local sectors plus the closed-segment
relative-openness endpoint source, routed through the explicit BL incident-edge
and endpoint-closure cuts. -/
def S2_agent_boundary_free_local_source_of_closedSegmentClosure_20260520bm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (closure_locus_relative_open :
      AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
        C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_agent_boundary_free_local_source_of_incidentEdge_20260520bl
    (C := C) (inputs := inputs)
    localSectorRows
    (S2_agent_adjacent_frontier_endpoints_incident_edge_source_of_closedSegmentClosure_20260520bm
      (C := C) (inputs := inputs) closure_locus_relative_open)

/-- Endpoint-incident source rows from the same input-level closed-segment
relative-openness source used by the `20260520bm` boundary-free local source.

This keeps the endpoint-incident lane explicit: local sector rows provide the
two selected carrier neighbours, and the closed-segment source is erased only
to adjacent-endpoint selected-edge incidence. -/
def S2_agent_endpoint_incident_source_rows_of_closedSegmentClosure_20260520bp
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (closure_locus_relative_open :
      AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
        C inputs) :
    BoundaryFreeEndpointIncidentSourceRows inputs :=
  BoundaryFreeEndpointIncidentSourceRows.ofLocalSectorRows
    (C := C) (inputs := inputs)
    localSectorRows
    (by
      intro a x hadj hxfrontier
      exact
        S2_agent_adjacent_frontier_endpoints_incident_edge_source_of_closedSegmentClosure_20260520bm
          (C := C) (inputs := inputs)
          closure_locus_relative_open
          hadj
          (mem_unboundedFrontierVertexSet_iff.1 a.2)
          hxfrontier)

/-- Claim `S2-agent-boundary-free-no-third-source-20260520bq`.

The shortest checked local-topology source for
`BoundaryFreeNoThirdGermSource` is the endpoint-incident package: it already
contains the pointwise local-sector rows and the adjacent-frontier endpoint
selected-edge row.  The open-segment branch is discharged by the existing
frontier-edge carrier membership theorem inside the endpoint-row eraser.

No final cycle rows, raw orbit rows, or actual boundary equivalence rows are
used here. -/
def S2_agent_boundaryFreeNoThirdGermSource_of_endpointIncidentRows_20260520bq
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (endpointRows : BoundaryFreeEndpointIncidentSourceRows inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  endpointRows.toBoundaryFreeNoThirdGermSource

/-- Nonempty wrapper for the shortest endpoint-incident local source. -/
def S2_agent_boundaryFreeNoThirdGermSource_nonempty_of_endpointIncidentRows_20260520bq
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (endpointRows : BoundaryFreeEndpointIncidentSourceRows inputs) :
    Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  endpointRows.nonemptyBoundaryFreeNoThirdGermSource

/-- Boundary-free no-third-germ source from the checked local-sector rows and
closed-segment adjacent-endpoint source.

This is the explicit composition of the currently checked source rows:
closed-segment relative-openness first gives the endpoint-incident package
from `S2_agent_endpoint_incident_source_rows_of_closedSegmentClosure_20260520bp`,
and the endpoint package is then erased to
`BoundaryFreeNoThirdGermSource`. -/
def S2_agent_boundaryFreeNoThirdGermSource_of_localSectorRows_closedSegmentClosure_20260520bq
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (closure_locus_relative_open :
      AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
        C inputs) :
    BoundaryFreeNoThirdGermSource inputs :=
  S2_agent_boundaryFreeNoThirdGermSource_of_endpointIncidentRows_20260520bq
    (C := C) (inputs := inputs)
    (S2_agent_endpoint_incident_source_rows_of_closedSegmentClosure_20260520bp
      (C := C) (inputs := inputs)
      localSectorRows closure_locus_relative_open)

/-- Nonempty form of the checked local-sector/closed-segment source
composition. -/
def S2_agent_boundaryFreeNoThird_nonempty_of_localSector_closedSegment_20260520bq
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (closure_locus_relative_open :
      AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
        C inputs) :
    Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  S2_agent_boundaryFreeNoThirdGermSource_nonempty_of_endpointIncidentRows_20260520bq
    (C := C) (inputs := inputs)
    (S2_agent_endpoint_incident_source_rows_of_closedSegmentClosure_20260520bp
      (C := C) (inputs := inputs)
      localSectorRows closure_locus_relative_open)

namespace BoundaryFreeNoThirdGermSource

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- The boundary-free no-third-germ source also supplies the endpoint-incident
closure.  If an adjacent far endpoint lies on the unbounded exterior frontier,
use that endpoint itself as the noncenter point in the incident germ; the
no-third row then forces the adjacent endpoint to be one of the two selected
exterior carrier neighbors. -/
theorem endpoint_frontier_edge_of_noThirdGermSource
    (source : BoundaryFreeNoThirdGermSource inputs) :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (x : Fin n),
      (canonicalGraph C).Adj a.1 x ->
        (canonicalGraph C).point x ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ->
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
            (x, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
  intro a x hadj hxfrontier
  have hx_left_or_right : x = source.left a ∨ x = source.right a := by
    by_cases hx_left : x = source.left a
    · exact Or.inl hx_left
    · by_cases hx_right : x = source.right a
      · exact Or.inr hx_right
      · exfalso
        let eps : Real :=
          dist ((canonicalGraph C).point a.1)
            ((canonicalGraph C).point x) + 1
        have hqball :
            (canonicalGraph C).point x ∈
              Metric.ball ((canonicalGraph C).point a.1) eps := by
          rw [Metric.mem_ball]
          have hdist_nonneg :
              0 <=
                dist ((canonicalGraph C).point a.1)
                  ((canonicalGraph C).point x) :=
            dist_nonneg
          rw [dist_comm]
          dsimp [eps]
          linarith
        have hqseg :
            (canonicalGraph C).point x ∈
              closedSegment
                ((canonicalGraph C).point a.1)
                ((canonicalGraph C).point x) :=
          right_mem_closedSegment _ _
        have hgerm :
            (canonicalGraph C).point x ∈
              vertexIncidentGermW3 C a.1 x eps := by
          exact ⟨hqball, hqseg⟩
        have hqne :
            (canonicalGraph C).point x ≠
              (canonicalGraph C).point a.1 := by
          intro hpoints
          have hdist :
              Geometry.Distance.eucDist
                ((canonicalGraph C).point a.1)
                ((canonicalGraph C).point x) = 1 :=
            (canonicalGraph C).adj_geometry_dist_eq_one hadj
          have hzero :
              Geometry.Distance.eucDist
                ((canonicalGraph C).point a.1)
                ((canonicalGraph C).point x) = 0 := by
            simp [hpoints]
          linarith
        exact
          source.no_third_germ a eps ((canonicalGraph C).point x) x
            hqball hxfrontier hadj hgerm hqne hx_left hx_right
  rcases hx_left_or_right with hx_left | hx_right
  · simpa [hx_left] using source.left_edge a
  · simpa [hx_right] using source.right_edge a

/-- The boundary-free no-third-germ source supplies the endpoint-incident row
by combining its local-sector eraser with the named endpoint closure above. -/
def toEndpointIncidentSourceRows
    (source : BoundaryFreeNoThirdGermSource inputs) :
    BoundaryFreeEndpointIncidentSourceRows inputs :=
  BoundaryFreeEndpointIncidentSourceRows.ofLocalSectorRows
    (C := C) (inputs := inputs)
    source.toLocalSectorRows
    (endpoint_frontier_edge_of_noThirdGermSource
      (C := C) (inputs := inputs) source)

/-- Nonempty wrapper for the no-third-germ to endpoint-incident eraser. -/
def nonemptyEndpointIncidentSourceRows
    (source : BoundaryFreeNoThirdGermSource inputs) :
    Nonempty (BoundaryFreeEndpointIncidentSourceRows inputs) :=
  ⟨source.toEndpointIncidentSourceRows⟩

/-- Actual boundary-cycle rows plus a boundary-free two-germ/no-third source
force incident frontier-edge completeness for that same boundary cycle.

The local source chooses two abstract carrier neighbours at each exterior
frontier vertex.  Since the actual boundary predecessor and successor are
also carrier neighbours, the two chosen neighbours must be exactly those
boundary neighbours, so every selected incident frontier edge is one of the
two boundary sides. -/
theorem boundaryCycleIncidentFrontierEdgeCompleteness_of_actualBoundaryRows
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs) :
    BoundaryCycleIncidentFrontierEdgeCompleteness inputs
      actualRows.boundary := by
  intro k x hedge
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    actualRows.boundary
  let pred : Fin n :=
    B.vertex (PlanarInterface.cyclicPred B.length_pos k)
  let succ : Fin n :=
    B.vertex (PlanarInterface.cyclicSucc B.length_pos k)
  have hcenter_frontier :
      (canonicalGraph C).point (B.vertex k) ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior := by
    simpa [B] using actualRows.cycle_vertices_frontier k
  let a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨B.vertex k, mem_unboundedFrontierVertexSet_iff.2 hcenter_frontier⟩
  let rows : UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    source.toLocalSectorRows a
  have hpred_edge :
      (B.vertex k, pred) ∈ unboundedFrontierEdgeSet C inputs ∨
        (pred, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
    let kp : Fin B.length := PlanarInterface.cyclicPred B.length_pos k
    have hsucc_kp :
        PlanarInterface.cyclicSucc B.length_pos kp = k := by
      simp [kp]
    have h :=
      actualRows.cycle_edge_mem_unboundedFrontierEdgeSet_or_symm kp
    rcases h with h | h
    · right
      simpa [B, pred, kp, hsucc_kp] using h
    · left
      simpa [B, pred, kp, hsucc_kp] using h
  have hsucc_edge :
      (B.vertex k, succ) ∈ unboundedFrontierEdgeSet C inputs ∨
        (succ, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [B, succ] using
      actualRows.cycle_edge_mem_unboundedFrontierEdgeSet_or_symm k
  have hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  have hpred_mem : pred ∈ unboundedFrontierVertexSet C inputs := by
    rcases hpred_edge with h | h
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).2
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).1
  have hsucc_mem : succ ∈ unboundedFrontierVertexSet C inputs := by
    rcases hsucc_edge with h | h
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).2
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).1
  let bpred : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨pred, hpred_mem⟩
  let bsucc : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨succ, hsucc_mem⟩
  have hpred_adj :
      (unboundedFrontierCarrierGraph C inputs).Adj a bpred := by
    rcases hpred_edge with h | h
    · exact unboundedFrontierCarrierGraph_adj_of_ordered_edge h
    · exact unboundedFrontierCarrierGraph_adj_of_ordered_edge_symm h
  have hsucc_adj :
      (unboundedFrontierCarrierGraph C inputs).Adj a bsucc := by
    rcases hsucc_edge with h | h
    · exact unboundedFrontierCarrierGraph_adj_of_ordered_edge h
    · exact unboundedFrontierCarrierGraph_adj_of_ordered_edge_symm h
  have hpred_lr : pred = rows.left ∨ pred = rows.right := by
    simpa [bpred] using rows.only bpred hpred_adj
  have hsucc_lr : succ = rows.left ∨ succ = rows.right := by
    simpa [bsucc] using rows.only bsucc hsucc_adj
  have hpred_ne_succ : pred ≠ succ := by
    intro hps
    have hidx :
        PlanarInterface.cyclicPred B.length_pos k =
          PlanarInterface.cyclicSucc B.length_pos k := by
      exact B.simple (by simpa [pred, succ] using hps)
    exact
      (PlanarInterface.cyclicPred_ne_cyclicSucc_of_three_le
        B.length_pos B.length_ge_three k) hidx
  have left_or_right_to_pred_succ :
      ∀ y : Fin n, y = rows.left ∨ y = rows.right →
        y = pred ∨ y = succ := by
    intro y hy
    rcases hpred_lr with hpred_left | hpred_right
    · rcases hsucc_lr with hsucc_left | hsucc_right
      · exfalso
        exact hpred_ne_succ (hpred_left.trans hsucc_left.symm)
      · rcases hy with hy_left | hy_right
        · exact Or.inl (hy_left.trans hpred_left.symm)
        · exact Or.inr (hy_right.trans hsucc_right.symm)
    · rcases hsucc_lr with hsucc_left | hsucc_right
      · rcases hy with hy_left | hy_right
        · exact Or.inr (hy_left.trans hsucc_left.symm)
        · exact Or.inl (hy_right.trans hpred_right.symm)
      · exfalso
        exact hpred_ne_succ (hpred_right.trans hsucc_right.symm)
  have hx_mem : x ∈ unboundedFrontierVertexSet C inputs := by
    rcases hedge with h | h
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).2
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).1
  let bx : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨x, hx_mem⟩
  have hx_adj : (unboundedFrontierCarrierGraph C inputs).Adj a bx := by
    rcases hedge with h | h
    · exact unboundedFrontierCarrierGraph_adj_of_ordered_edge h
    · exact unboundedFrontierCarrierGraph_adj_of_ordered_edge_symm h
  have hx_lr : x = rows.left ∨ x = rows.right := by
    simpa [bx] using rows.only bx hx_adj
  rcases left_or_right_to_pred_succ x hx_lr with hx_pred | hx_succ
  · left
    simpa [B, pred] using hx_pred
  · right
    simpa [B, succ] using hx_succ

/-- Actual boundary-cycle rows plus the boundary-free local source also give
the honest selected-edge segment chain for the concrete unbounded frontier
carrier.

The boundary rows provide the real cycle edges and frontier-vertex
equivalence; the local no-third-germ source supplies incident-edge
completeness, preventing selected frontier chords from disconnecting the
carrier-chain argument. -/
noncomputable def edgeCarrierSegmentChainConnected_of_actualBoundaryRows
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedFrontierEdgeCarrierSegmentChainConnected inputs :=
  unboundedFrontierEdgeCarrierSegmentChainConnected_of_boundaryCycle_complete
    (C := C) (inputs := inputs) actualRows.boundary
    actualRows.frontier_iff_cycle_vertex
    (fun k => actualRows.cycle_edge_mem_unboundedFrontierEdgeSet_or_symm k)
    (boundaryCycleIncidentFrontierEdgeCompleteness_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows source)

/-- Actual boundary-cycle rows plus the boundary-free local source give
connectedness of the concrete unbounded-frontier carrier graph.

This is the graph-connected version of
`edgeCarrierSegmentChainConnected_of_actualBoundaryRows`, using the existing
fixed-side frontier-cover route to pass from selected-edge chains to carrier
connectedness. -/
theorem unboundedFrontierCarrierGraph_connected_of_actualBoundaryRows
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_edgeChain_localSectorRows_fixedSide
    (C := C) (inputs := inputs)
    (edgeCarrierSegmentChainConnected_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows source)
    source.toLocalSectorRows

/-- Actual boundary-cycle rows plus a boundary-free two-germ/no-third source
also give the endpoint-only form needed by the W3 local exterior-sector
reducers. -/
theorem endpointIncidentOnlyPredSucc_of_actualBoundaryRows
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs) :
    BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
      actualRows.boundary := by
  intro k other hfrontier hadj
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    actualRows.boundary
  have hsource :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs B :=
    boundaryCycleIncidentFrontierEdgeCompleteness_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows source
  have hedge :
      (B.vertex k, other) ∈ unboundedFrontierEdgeSet C inputs ∨
        (other, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
    exact source.endpoint_frontier_edge_of_noThirdGermSource
      ⟨B.vertex k,
        mem_unboundedFrontierVertexSet_iff.2
          (by simpa [B] using actualRows.cycle_vertices_frontier k)⟩
      other hadj hfrontier
  simpa [B] using hsource k other hedge

/-- Actual boundary-cycle rows, adjacent frontier-endpoint selected-edge
incidence, and boundary-cycle incident completeness give the endpoint-only
row needed by the W3 local exterior-sector reducer.

This is the non-circular source form: the adjacent-endpoint source promotes
the graph edge to the actual unbounded-frontier carrier, and incident
completeness then identifies the endpoint as the predecessor or successor
boundary neighbour. -/
theorem endpointIncidentOnlyPredSucc_of_actualBoundaryRows_incidentEdge_complete
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (hcomplete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary) :
    BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
      actualRows.boundary := by
  intro k other hfrontier hadj
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    actualRows.boundary
  have hkfrontier :
      (canonicalGraph C).point (B.vertex k) ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior := by
    simpa [B] using actualRows.cycle_vertices_frontier k
  have hedge :
      (B.vertex k, other) ∈ unboundedFrontierEdgeSet C inputs ∨
        (other, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs :=
    incident_edge (by simpa [B] using hadj) hkfrontier hfrontier
  simpa [B] using hcomplete k other hedge

/-- Actual boundary-cycle rows plus the boundary-free local source expose the
primitive boundary-sector rows, once the same boundary has been oriented as a
geometric face cycle.

This is a compact non-W facade handoff: raw/orbit work can produce
`actualRows`, `faceSuccRows`, and `boundary_orientation`; the local source then
supplies both incident completeness and endpoint-only rows, and the existing
fixed-side local-sector reducers fill the primitive sector package. -/
noncomputable def boundaryVertexExteriorSectorRows_of_actualBoundaryRows
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary)
    (boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k))) :
    forall k : Fin actualRows.boundary.length,
      BoundaryVertexExteriorSectorRowsAt inputs actualRows.boundary k := by
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    actualRows.boundary
  let cycle_edge_mem :
      forall k : Fin B.length,
        (B.vertex k,
            B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) ∈
            unboundedFrontierEdgeSet C inputs ∨
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k),
            B.vertex k) ∈
            unboundedFrontierEdgeSet C inputs :=
    fun k => actualRows.cycle_edge_mem_unboundedFrontierEdgeSet_or_symm k
  let hcomplete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs B :=
    boundaryCycleIncidentFrontierEdgeCompleteness_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows source
  let endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs B :=
    endpointIncidentOnlyPredSucc_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows source
  let actualSector :
      ActualExteriorSectorInputSourceRows inputs B :=
    S2_agent_actual_exterior_sector_input_source_2_from_faceSuccRows_orientation_local_exterior_sector_source
      (C := C) (inputs := inputs) B
      actualRows.frontier_iff_cycle_vertex
      actualRows.cycle_edge_openSegment_frontier
      (by simpa [B] using faceSuccRows)
      (by simpa [B] using boundary_orientation)
      (S2_agent_local_exterior_point_sector_source_of_boundaryCycleIncidentFrontierEdgeCompleteness
      (C := C) (inputs := inputs) (B := B)
      hcomplete endpoint_incident_only)
  exact actualSector.sectorRows

set_option linter.style.longLine false in
/-- Actual boundary rows plus the boundary-free local source construct the
honest face-orbit exterior carrier rows.

This packages the existing carrier object directly.  The local source supplies
the incident-edge completeness/no-third-germ rows used to obtain primitive
exterior-sector rows; the stored boundary face-successor and orientation rows
identify the geometric orbit without using the broad adjacent-endpoint source. -/
noncomputable def faceDartOrbitExteriorCarrierRows_of_actualBoundaryRows
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary)
    (boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k))) :
    FaceDartOrbitExteriorCarrierRows C inputs :=
  faceDartOrbitExteriorCarrierRows_of_boundaryVertexExteriorSectorRows
    (C := C) (inputs := inputs)
    actualRows.boundary
    actualRows.frontier_iff_cycle_vertex
    (boundaryVertexExteriorSectorRows_of_actualBoundaryRows
      (C := C) (inputs := inputs)
      actualRows source faceSuccRows boundary_orientation)

/-- Actual boundary-cycle rows plus the boundary-free local source fill the
endpoint-incident source package once the same boundary is oriented as a
geometric face cycle.

This packages the two endpoint-row fields together: sector rows are obtained
from the actual boundary, source, face-successor rows, and orientation, while
the far-endpoint closure is the endpoint-only row derived from the same local
source. -/
noncomputable def endpointIncidentSourceRows_of_actualBoundaryRows
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary)
    (boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k))) :
    BoundaryFreeEndpointIncidentSourceRows inputs :=
  BoundaryFreeEndpointIncidentSourceRows.of_actualBoundaryRows_endpointIncidentOnly
    (C := C) (inputs := inputs)
    actualRows
    (boundaryVertexExteriorSectorRows_of_actualBoundaryRows
      (C := C) (inputs := inputs)
      actualRows source faceSuccRows boundary_orientation)
    (endpointIncidentOnlyPredSucc_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows source)

/-- Actual boundary-cycle rows plus the boundary-free local source close the
final S2 exterior frontier-cycle rows once the boundary is oriented as a
geometric face cycle. -/
noncomputable def unboundedExteriorFrontierCycleRows_of_actualBoundaryRows
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary)
    (boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k))) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_boundaryVertexExteriorSectorRows
    actualRows.boundary actualRows.frontier_iff_cycle_vertex
    (boundaryVertexExteriorSectorRows_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows source faceSuccRows
      boundary_orientation)

/-- Actual boundary-cycle rows plus the boundary-free local source expose the
exact source package required by
`S2ExteriorBoundarySource.boundaryVertexExteriorSectorRows_of_inputs`, once
the boundary is oriented as a genuine geometric face cycle.

This is the non-final handoff form of
`unboundedExteriorFrontierCycleRows_of_actualBoundaryRows`: it preserves the
concrete boundary cycle and the primitive per-boundary-vertex sector rows for
the W32 consumer instead of immediately erasing them to cycle rows. -/
noncomputable def boundaryVertexExteriorSectorRows_source_of_actualBoundaryRows
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary)
    (boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k))) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k := by
  refine ⟨actualRows.boundary, actualRows.frontier_iff_cycle_vertex, ?_⟩
  exact
    boundaryVertexExteriorSectorRows_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows source faceSuccRows
      boundary_orientation

set_option linter.style.longLine false in
/-- Actual boundary rows plus the boundary-free local source expose the
boundary-sector source through the incident-completeness handoff.

The local source is used only to prove that every selected incident frontier
edge at a boundary vertex is one of the two boundary sides.  The source-owner
theorem then derives the open-segment local sector internally. -/
noncomputable def
    boundaryVertexExteriorSectorRows_source_of_actualBoundaryRows_faceSuccIncidentComplete
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary)
    (boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k))) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
  S2_boundaryVertexExteriorSectorRows_source_of_actualBoundaryRows_faceSuccIncidentComplete
    (C := C) (inputs := inputs)
    actualRows faceSuccRows boundary_orientation
    (boundaryCycleIncidentFrontierEdgeCompleteness_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows source)

set_option linter.style.longLine false in
/-- Boundary-free local topology plus actual boundary `faceSucc` rows close
the compressed geometric neighbour-pair selection source.

The boundary-free source is used only to prove incident completeness for the
same actual boundary cycle.  The actual-boundary source theorem then derives
sector rows and the geometric-selection payload without introducing a
separate geometric-order premise. -/
noncomputable def
    geometricSelectionInputSource_of_actualBoundaryRows_faceSuccIncidentComplete
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (source : BoundaryFreeNoThirdGermSource inputs)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary)
    (boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k))) :
    S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_geometricSelectionInputSource_of_actualBoundaryRows_faceSuccIncidentComplete_20260520cc
    (C := C) (inputs := inputs)
    actualRows faceSuccRows boundary_orientation
    (boundaryCycleIncidentFrontierEdgeCompleteness_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows source)

set_option linter.style.longLine false in
/-- Face-successor rows, ordinary boundary orientation, open-segment local
exterior sectors, and endpoint-only incidence expose the boundary-sector
source package directly.

This is the source-preserving version of the compact open-segment route: the
face-successor/orientation rows first provide the angular no-between payload,
the open-segment and endpoint rows package the boundary-free no-third-germ
source, and the existing actual-boundary reducer keeps the concrete boundary
cycle visible for the S2-G consumer. -/
noncomputable def
    boundaryVertexExteriorSectorRows_source_of_actualBoundaryRows_faceSuccOpenSegmentEndpoint
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary)
    (boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k)))
    (local_exterior_sector :
      BoundaryFrontierOpenSegmentLocalExteriorSector inputs
        actualRows.boundary)
    (endpoint_incident_only :
      BoundaryFrontierEndpointIncidentOnlyPredSucc inputs
        actualRows.boundary) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
  let angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k :=
    GeometricRotationSystem.boundaryVertexAngularNoBetweenRows_of_faceSuccRows_pred_arg_lt_succ_arg
      C actualRows.boundary faceSuccRows boundary_orientation
  let source : BoundaryFreeNoThirdGermSource inputs :=
    ofActualBoundaryRowsAngularOpenSegmentEndpoint
      (C := C) (inputs := inputs)
      actualRows angularRows local_exterior_sector endpoint_incident_only
  boundaryVertexExteriorSectorRows_source_of_actualBoundaryRows
    (C := C) (inputs := inputs)
    actualRows source faceSuccRows boundary_orientation

/-- Raw exterior face-walk source, retaining the real boundary cycle before
erasing it to the final S2 row.

The raw orbit and cut rows construct `actualRows`; the same raw orbit supplies
the geometric face-successor rows for that constructed boundary via
`rawFaceSuccOrbit_unitDistanceCycleFaceSuccRows_of_tail_eq`.  The only
remaining orientation input is the ordinary predecessor/successor argument
inequality for the constructed boundary. -/
noncomputable def actualBoundaryRowsWithFaceSucc_of_rawFaceSuccOrbit
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (localSource : BoundaryFreeNoThirdGermSource inputs)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j) :
    Exists fun actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs =>
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary := by
  let edge_openSegment_frontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
    rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier
      (inputs := inputs) O dart_edge_openSegment_frontier
  let frontier_iff_tail :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin O.period => (O.dart k).tail = v :=
    rawFaceSuccOrbit_frontier_iff_tail_of_frontier_vertex_tail_coverage
      O edge_openSegment_frontier frontier_vertex_tail_coverage
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSource.toLocalSectorRows
  let period_ge_three : 3 <= O.period :=
    rawFaceSuccOrbit_period_three_le_of_edge_openSegment_frontier_tail_coverage_localSectorRows
      (inputs := inputs) O edge_openSegment_frontier
      frontier_vertex_tail_coverage localSectorRows
  let hB :=
    exists_unitDistanceCycleBoundary_of_rawFaceSuccOrbit_tail_injective
      O period_ge_three
      (rawFaceSuccOrbit_tail_injective_of_repeatedTailExteriorCutRows
        (inputs := inputs) O cutRows)
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose hB
  let hperiod : B.length = O.period :=
    Classical.choose (Classical.choose_spec hB)
  let tail_eq :
      forall k : Fin B.length,
        (O.dart (Fin.cast hperiod k)).tail = B.vertex k :=
    Classical.choose_spec (Classical.choose_spec hB)
  let actualRows :
      ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
    ActualBoundaryCycleFrontierEquivalenceRows.ofRawFaceSuccOrbitBoundaryRows
      (inputs := inputs) O B hperiod tail_eq frontier_iff_tail
      edge_openSegment_frontier
  let faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary := by
    simpa [actualRows] using
      rawFaceSuccOrbit_unitDistanceCycleFaceSuccRows_of_tail_eq
        (C := C)
        (R := GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        O B hperiod tail_eq
  exact ⟨actualRows, faceSuccRows⟩

/-- Raw exterior face-walk route to the final S2 cycle rows without any
principal-argument orientation side condition.

The sector-row strengthening below still needs an ordinary nonwrap angular
orientation.  The final S2 cycle row does not: once the raw orbit and no-cut
rows have produced `ActualBoundaryCycleFrontierEquivalenceRows`, the checked
cycle eraser only uses the concrete boundary cycle and its frontier
equivalence. -/
noncomputable def unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit_noOrientation
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (localSource : BoundaryFreeNoThirdGermSource inputs)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j) :
    UnboundedExteriorFrontierCycleRows C inputs := by
  let h :=
    actualBoundaryRowsWithFaceSucc_of_rawFaceSuccOrbit
      (C := C) (inputs := inputs) O localSource
      frontier_vertex_tail_coverage dart_edge_openSegment_frontier cutRows
  exact
    unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
      (Classical.choose h)

/-- Raw exterior face-walk source, retaining the real boundary cycle together
with the transported ordinary predecessor/successor orientation row.

The new input is the sharp raw-orbit form of the same row: at each raw tail,
the previous raw tail has smaller principal argument than the next raw tail.
All frontier and cycle-boundary bookkeeping is shared with
`actualBoundaryRowsWithFaceSucc_of_rawFaceSuccOrbit`. -/
noncomputable def actualBoundaryRowsWithFaceSuccAndOrientation_of_rawFaceSuccOrbit
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (localSource : BoundaryFreeNoThirdGermSource inputs)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j)
    (raw_orientation :
      forall k : Fin O.period,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (O.dart k).tail
            (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (O.dart k).tail
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    Exists fun actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs =>
      UnitDistanceCycleFaceSuccRows C
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          actualRows.boundary ∧
        forall k : Fin actualRows.boundary.length,
          GeometricRotationSystem.graphDartArg
              (GeometricRotationSystem.canonicalGeometricGraph C)
              (actualRows.boundary.vertex k)
              (actualRows.boundary.vertex
                (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
            GeometricRotationSystem.graphDartArg
              (GeometricRotationSystem.canonicalGeometricGraph C)
              (actualRows.boundary.vertex k)
              (actualRows.boundary.vertex
                (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k)) := by
  let edge_openSegment_frontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
    rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier
      (inputs := inputs) O dart_edge_openSegment_frontier
  let frontier_iff_tail :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin O.period => (O.dart k).tail = v :=
    rawFaceSuccOrbit_frontier_iff_tail_of_frontier_vertex_tail_coverage
      O edge_openSegment_frontier frontier_vertex_tail_coverage
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSource.toLocalSectorRows
  let period_ge_three : 3 <= O.period :=
    rawFaceSuccOrbit_period_three_le_of_edge_openSegment_frontier_tail_coverage_localSectorRows
      (inputs := inputs) O edge_openSegment_frontier
      frontier_vertex_tail_coverage localSectorRows
  let hB :=
    exists_unitDistanceCycleBoundary_of_rawFaceSuccOrbit_tail_injective
      O period_ge_three
      (rawFaceSuccOrbit_tail_injective_of_repeatedTailExteriorCutRows
        (inputs := inputs) O cutRows)
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose hB
  let hperiod : B.length = O.period :=
    Classical.choose (Classical.choose_spec hB)
  let tail_eq :
      forall k : Fin B.length,
        (O.dart (Fin.cast hperiod k)).tail = B.vertex k :=
    Classical.choose_spec (Classical.choose_spec hB)
  let actualRows :
      ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
    ActualBoundaryCycleFrontierEquivalenceRows.ofRawFaceSuccOrbitBoundaryRows
      (inputs := inputs) O B hperiod tail_eq frontier_iff_tail
      edge_openSegment_frontier
  let faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary := by
    simpa [actualRows] using
      rawFaceSuccOrbit_unitDistanceCycleFaceSuccRows_of_tail_eq
        (C := C)
        (R := GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        O B hperiod tail_eq
  let boundary_orientation :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k)) :=
    ActualBoundaryCycleFrontierEquivalenceRows.boundary_orientation_of_rawFaceSuccOrbitBoundaryRows
      (inputs := inputs) O B hperiod tail_eq frontier_iff_tail
      edge_openSegment_frontier raw_orientation
  exact ⟨actualRows, faceSuccRows, boundary_orientation⟩

set_option linter.style.longLine false in
/-- Raw exterior face-walk route to the exact boundary-sector source package,
with the orientation row stated directly on the raw orbit.

This keeps the next S2 source obligation at the raw exterior face-walk level:
prove that every raw tail sees the previous raw tail before the next raw tail
in the concrete geometric argument order.  The transported boundary cycle,
face-successor rows, and primitive sector rows are then produced by the
checked raw-orbit machinery above. -/
noncomputable def boundaryVertexExteriorSectorRows_source_of_rawFaceSuccOrbit_rawOrientation
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (localSource : BoundaryFreeNoThirdGermSource inputs)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j)
    (raw_orientation :
      forall k : Fin O.period,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (O.dart k).tail
            (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (O.dart k).tail
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k := by
  let h :=
    actualBoundaryRowsWithFaceSuccAndOrientation_of_rawFaceSuccOrbit
      (C := C) (inputs := inputs) O localSource
      frontier_vertex_tail_coverage dart_edge_openSegment_frontier cutRows
      raw_orientation
  let actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
    Classical.choose h
  let hrows := Classical.choose_spec h
  exact
    boundaryVertexExteriorSectorRows_source_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows localSource hrows.1
      hrows.2

/-- Raw exterior face-walk route to the exact boundary-sector source package.

This is the source-preserving version of
`unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit`: it constructs the
actual boundary cycle from the raw orbit, keeps the matching geometric
face-successor rows, and uses the boundary-free local source to produce
primitive `BoundaryVertexExteriorSectorRowsAt` rows. -/
noncomputable def boundaryVertexExteriorSectorRows_source_of_rawFaceSuccOrbit
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (localSource : BoundaryFreeNoThirdGermSource inputs)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j)
    (boundary_orientation :
      forall (actualRows :
          ActualBoundaryCycleFrontierEquivalenceRows C inputs),
        UnitDistanceCycleFaceSuccRows C
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            actualRows.boundary ->
          forall k : Fin actualRows.boundary.length,
            GeometricRotationSystem.graphDartArg
                (GeometricRotationSystem.canonicalGeometricGraph C)
                (actualRows.boundary.vertex k)
                (actualRows.boundary.vertex
                  (PlanarInterface.cyclicPred
                    actualRows.boundary.length_pos k)) <
              GeometricRotationSystem.graphDartArg
                (GeometricRotationSystem.canonicalGeometricGraph C)
                (actualRows.boundary.vertex k)
                (actualRows.boundary.vertex
                  (PlanarInterface.cyclicSucc
                    actualRows.boundary.length_pos k))) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k := by
  let h :=
    actualBoundaryRowsWithFaceSucc_of_rawFaceSuccOrbit
      (C := C) (inputs := inputs) O localSource
      frontier_vertex_tail_coverage dart_edge_openSegment_frontier cutRows
  let actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
    Classical.choose h
  let faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary :=
    Classical.choose_spec h
  exact
    boundaryVertexExteriorSectorRows_source_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows localSource faceSuccRows
      (boundary_orientation actualRows faceSuccRows)

/-- Raw exterior face-walk route to the final S2 cycle rows, with the only
extra geometric input being the ordinary orientation inequality for the
boundary cycle constructed from the raw orbit. -/
noncomputable def unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (localSource : BoundaryFreeNoThirdGermSource inputs)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j)
    (boundary_orientation :
      forall (actualRows :
          ActualBoundaryCycleFrontierEquivalenceRows C inputs),
        UnitDistanceCycleFaceSuccRows C
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            actualRows.boundary ->
          forall k : Fin actualRows.boundary.length,
            GeometricRotationSystem.graphDartArg
                (GeometricRotationSystem.canonicalGeometricGraph C)
                (actualRows.boundary.vertex k)
                (actualRows.boundary.vertex
                  (PlanarInterface.cyclicPred
                    actualRows.boundary.length_pos k)) <
              GeometricRotationSystem.graphDartArg
                (GeometricRotationSystem.canonicalGeometricGraph C)
                (actualRows.boundary.vertex k)
                (actualRows.boundary.vertex
                  (PlanarInterface.cyclicSucc
                    actualRows.boundary.length_pos k))) :
    UnboundedExteriorFrontierCycleRows C inputs := by
  let h :=
    actualBoundaryRowsWithFaceSucc_of_rawFaceSuccOrbit
      (C := C) (inputs := inputs) O localSource
      frontier_vertex_tail_coverage dart_edge_openSegment_frontier cutRows
  let actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
    Classical.choose h
  let faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary :=
    Classical.choose_spec h
  exact
    unboundedExteriorFrontierCycleRows_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows localSource faceSuccRows
      (boundary_orientation actualRows faceSuccRows)

end BoundaryFreeNoThirdGermSource

/-- A selected raw face-successor orbit whose dart edges are actual exterior
frontier edges and whose consecutive tails cover every selected frontier edge. -/
structure RawOrbitCoverageSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start) where
  dart_edge_openSegment_frontier :
    ∀ k : Fin O.period,
      ∀ p : PlanarInterface.Point,
        PlanarInterface.InOpenSegment p
          ((canonicalGraph C).point (O.dart k).tail)
          ((canonicalGraph C).point (O.dart k).head) →
        p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior
  edge_coverage :
    ∀ e : {e : PlanarInterface.Edge n //
        e ∈ unboundedFrontierEdgeSet C inputs},
      Exists fun k : Fin O.period =>
        e.1 =
            ((O.dart k).tail,
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
          e.1 =
            ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
              (O.dart k).tail)

namespace RawOrbitCoverageSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {R : UnitDistanceRotationSystem C}
variable {start : UnitDistanceDart C}
variable {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}

/-- Raw-orbit coverage supplies connectedness of the actual frontier carrier
as an edge-segment chain. -/
def toEdgeCarrierSegmentChainConnected
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O) :
    UnboundedFrontierEdgeCarrierSegmentChainConnected inputs :=
  S2_edgeCarrierSegmentChainConnected_of_rawFaceSuccOrbit_dartFrontier_edgeCoverage
    (C := C) (inputs := inputs) O
    rows.dart_edge_openSegment_frontier rows.edge_coverage

/-- Raw coverage plus pointwise local-sector rows produce the
preconnected-source package for the honest selected-edge route. -/
def toFrontierPreconnectedSourceRowsFromLocalSectorRows
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierPreconnectedSourceRows inputs :=
  S2_frontierPreconnectedSourceRows_of_edgeChain_localSectorRows_fixedSide
    (C := C) (inputs := inputs)
    rows.toEdgeCarrierSegmentChainConnected
    localSectorRows

/-- Raw coverage plus pointwise local-sector rows fill the component-topology
source package for the actual unbounded exterior frontier. -/
def toComponentTopologyRowsFromLocalSectorRows
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  unboundedExteriorFrontierComponentTopologySourceRows_of_frontierPreconnectedSourceRows
    (C := C) inputs
    (rows.toFrontierPreconnectedSourceRowsFromLocalSectorRows localSectorRows)

/-- Raw coverage plus pointwise local-sector rows fill the input-facing
component-topology package used by W32. -/
def toComponentTopologyInputRowsFromLocalSectorRows
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs where
  frontier_preconnected :=
    (rows.toComponentTopologyRowsFromLocalSectorRows localSectorRows).frontier_preconnected
  frontier_vertex_incident :=
    frontierVertexIncidentSource_of_neighborPairRows
      (C := C) (inputs := inputs)
      (fun a => (localSectorRows a).toNeighborPairAt)

/-- Raw coverage plus pointwise local-sector rows prove connectedness of the
actual unbounded-frontier carrier through the selected-edge route. -/
def toCarrierGraphConnectedFromLocalSectorRows
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_componentTopologySourceRows
    (C := C) inputs
    (rows.toComponentTopologyRowsFromLocalSectorRows localSectorRows)

/-- Raw coverage plus boundary-free local rows produce the preconnected-source
package for the honest carrier route. -/
def toFrontierPreconnectedSourceRows
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierPreconnectedSourceRows inputs :=
  S2_frontierPreconnectedSourceRows_of_edgeChain_localSectorRows_fixedSide
    (C := C) (inputs := inputs)
    rows.toEdgeCarrierSegmentChainConnected
    localSource.toLocalSectorRows

/-- Raw coverage plus boundary-free local rows are exactly the two current
carrier-source families for the displayed S2 edge-chain/neighbour-pair route. -/
def toEdgeChainNeighborPairRows
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedFrontierEdgeCarrierSegmentChainConnected inputs ∧
      Nonempty
        (∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierNeighborPairAt inputs a) :=
  ⟨rows.toEdgeCarrierSegmentChainConnected, ⟨localSource.toNeighborPairRows⟩⟩

/-- Raw coverage plus boundary-free local rows fill the component-topology
source package for the actual unbounded exterior frontier. -/
def toComponentTopologyRows
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  localSource.toComponentTopologyRowsFromEdgeChain
    rows.toEdgeCarrierSegmentChainConnected

/-- Raw coverage plus boundary-free local rows fill the input-facing
component-topology source rows. -/
def toComponentTopologyInputRows
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  localSource.toComponentTopologyInputRowsFromEdgeChain
    rows.toEdgeCarrierSegmentChainConnected

/-- Raw coverage plus boundary-free local rows prove connectedness of the
actual unbounded-frontier carrier through the frontier-preconnected source
route.

This is an eraser for independently supplied raw coverage; it does not obtain
raw coverage from carrier connectedness, so it is safe to use before the final
cycle rows are assembled. -/
def toCarrierGraphConnected
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_frontierPreconnectedSourceRows
    (C := C) inputs
    (rows.toFrontierPreconnectedSourceRows localSource)

/-- Raw edge coverage plus the honest local incident-edge source proves that
every concrete unbounded-frontier vertex is hit as a raw orbit tail.

This uses only the selected incident edge contained in the local source.  It
does not promote the local row to the stronger global no-third-germ classifier. -/
def frontierVertexTailCoverageFromLocalSource
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Exists fun k : Fin O.period => (O.dart k).tail = a.1 := by
  classical
  intro a
  rcases localSource.left_edge a with hleft | hleft
  · let e : {e : PlanarInterface.Edge n //
        e ∈ unboundedFrontierEdgeSet C inputs} := ⟨(a.1, localSource.left a), hleft⟩
    rcases rows.edge_coverage e with ⟨k, hk⟩
    rcases hk with hk | hk
    · refine ⟨k, ?_⟩
      have hfst : e.1.1 = (O.dart k).tail := congrArg Prod.fst hk
      simpa [e] using hfst.symm
    · refine ⟨PlanarInterface.cyclicSucc O.period_pos k, ?_⟩
      have hfst :
          e.1.1 =
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
        congrArg Prod.fst hk
      simpa [e] using hfst.symm
  · let e : {e : PlanarInterface.Edge n //
        e ∈ unboundedFrontierEdgeSet C inputs} := ⟨(localSource.left a, a.1), hleft⟩
    rcases rows.edge_coverage e with ⟨k, hk⟩
    rcases hk with hk | hk
    · refine ⟨PlanarInterface.cyclicSucc O.period_pos k, ?_⟩
      have hsnd :
          e.1.2 =
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
        congrArg Prod.snd hk
      simpa [e] using hsnd.symm
    · refine ⟨k, ?_⟩
      have hsnd : e.1.2 = (O.dart k).tail := congrArg Prod.snd hk
      simpa [e] using hsnd.symm

/-- Raw coverage plus local incident-edge rows gives the exact frontier-iff-tail
row for the same raw orbit. -/
def frontierIffTailFromLocalSource
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior ↔
        Exists fun k : Fin O.period => (O.dart k).tail = v :=
  rawFaceSuccOrbit_frontier_iff_tail_of_frontier_vertex_tail_coverage
    O
    (rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier
      (inputs := inputs) O rows.dart_edge_openSegment_frontier)
    (rows.frontierVertexTailCoverageFromLocalSource localSource)

/- Direct raw-row projections used by the local S2 route.  These stay below
the global `BoundaryFreeNoThirdGermSource`: raw coverage supplies the orbit
edge rows, the local no-third source supplies tail coverage, and pointwise
local-sector rows supply the geometric predecessor/successor separation. -/

/-- Consecutive raw-tail open segments lie on the exterior frontier. -/
def edge_openSegment_frontier
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O) :
    forall k : Fin O.period,
      forall p : PlanarInterface.Point,
        PlanarInterface.InOpenSegment p
          ((canonicalGraph C).point (O.dart k).tail)
          ((canonicalGraph C).point
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
        p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
  rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier
    (inputs := inputs) O rows.dart_edge_openSegment_frontier

/-- At each raw tail, the predecessor and successor raw tails are distinct. -/
def raw_pred_succ_tail_ne
    {start : UnitDistanceDart C}
    {O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start}
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall k : Fin O.period,
      (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
        (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
  rawFaceSuccOrbit_pred_succ_tail_ne_of_geometric_localSectorRows
    (C := C) (inputs := inputs) O
    (rows.edge_openSegment_frontier) localSectorRows

/-- Raw coverage, local no-third-germ rows, and local sectors force period at
least three. -/
def period_ge_three
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeLocalNoThirdGermSourceRows inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    3 <= O.period :=
  rawFaceSuccOrbit_period_three_le_of_edge_openSegment_frontier_tail_coverage_localSectorRows
    (inputs := inputs) O
    (rows.edge_openSegment_frontier)
    (rows.frontierVertexTailCoverageFromLocalSource localSource)
    localSectorRows

/-- Raw coverage, local no-third-germ rows, and local sectors produce cyclic
coverage of the concrete unbounded-frontier carrier. -/
def cyclicCarrierCoverage
    (rows : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeLocalNoThirdGermSourceRows inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedFrontierCarrierCyclicCoverageRows C inputs :=
  unboundedFrontierCarrierCyclicCoverageRows_of_rawFaceSuccOrbit_tail_coverage
    O
    (rows.period_ge_three localSource localSectorRows)
    (rows.edge_openSegment_frontier)
    (rows.frontierVertexTailCoverageFromLocalSource localSource)

end RawOrbitCoverageSourceRows

/-- Direct theorem form of
`RawOrbitCoverageSourceRows.toCarrierGraphConnected`. -/
theorem unboundedFrontierCarrierGraph_connected_of_rawCoverage_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  coverage.toCarrierGraphConnected localSource

/-- Existential row form of the raw-coverage connected-carrier reducer.

This is the pointwise version of the source shape used by the family-level
raw-coverage route: raw coverage of one selected orbit, plus a nonempty
boundary-free local source, already closes the concrete carrier-connectedness
row. -/
theorem unboundedFrontierCarrierGraph_connected_of_rawCoverage_boundaryFreeRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      Exists fun R : UnitDistanceRotationSystem C =>
        Exists fun start : UnitDistanceDart C =>
          Exists fun O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
            RawOrbitCoverageSourceRows (inputs := inputs) O ∧
              Nonempty (BoundaryFreeNoThirdGermSource inputs)) :
    (unboundedFrontierCarrierGraph C inputs).Connected := by
  rcases rows with ⟨_R, _start, _O, coverage, localRows⟩
  rcases localRows with ⟨localSource⟩
  exact
    unboundedFrontierCarrierGraph_connected_of_rawCoverage_boundaryFreeSource
      (C := C) (inputs := inputs) coverage localSource

/-- Raw-orbit edge coverage plus endpoint-incident local rows prove the current
edge-chain/boundary-free source pair.

The remaining source row is explicit: raw coverage supplies the selected-edge
segment chain, while endpoint-incident rows erase to the boundary-free
no-third-germ source through the existing local reducer. -/
theorem S2_edgeChain_boundaryFreeNoThirdGermSource_of_rawCoverage_endpointIncidentRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      (Exists fun R : UnitDistanceRotationSystem C =>
        Exists fun start : UnitDistanceDart C =>
          Exists fun O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
            RawOrbitCoverageSourceRows (inputs := inputs) O) ∧
        Nonempty (BoundaryFreeEndpointIncidentSourceRows inputs)) :
    UnboundedFrontierEdgeCarrierSegmentChainConnected inputs ∧
      Nonempty (BoundaryFreeNoThirdGermSource inputs) := by
  rcases rows.1 with ⟨_R, _start, _O, coverage⟩
  rcases rows.2 with ⟨localRows⟩
  exact
    ⟨coverage.toEdgeCarrierSegmentChainConnected,
      localRows.nonemptyBoundaryFreeNoThirdGermSource⟩

/-- Selected carrier edges whose closed segments share a concrete carrier
vertex have intersecting closed segments. -/
theorem unboundedFrontierEdgeCarrierSegmentsMeet_of_common_carrier_vertex
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {e f :
      {e : PlanarInterface.Edge n // e ∈ unboundedFrontierEdgeSet C inputs}}
    {a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}
    (he : e.1.1 = a.1 ∨ e.1.2 = a.1)
    (hf : f.1.1 = a.1 ∨ f.1.2 = a.1) :
    unboundedFrontierEdgeCarrierSegmentsMeet inputs e f := by
  refine
    unboundedFrontierEdgeCarrierSegmentsMeet_of_common_endpoint
      (C := C) (inputs := inputs) (e := e) (f := f) ?_
  rcases he with he | he <;> rcases hf with hf | hf
  · left
    exact he.trans hf.symm
  · right
    left
    exact he.trans hf.symm
  · right
    right
    left
    exact he.trans hf.symm
  · right
    right
    right
    exact he.trans hf.symm

/-- A concrete carrier-graph adjacency is represented by an actual selected
frontier edge incident to the two adjacent carrier vertices. -/
theorem exists_unboundedFrontierEdgeCarrierEdge_of_carrierGraph_adj
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {a b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}
    (hab : (unboundedFrontierCarrierGraph C inputs).Adj a b) :
    Exists fun e :
        {e : PlanarInterface.Edge n // e ∈ unboundedFrontierEdgeSet C inputs} =>
      (e.1.1 = a.1 ∨ e.1.2 = a.1) ∧
        (e.1.1 = b.1 ∨ e.1.2 = b.1) := by
  rcases (unboundedFrontierCarrierGraph_adj_iff).1 hab with hab | hba
  · exact ⟨⟨(a.1, b.1), hab⟩, Or.inl rfl, Or.inr rfl⟩
  · exact ⟨⟨(b.1, a.1), hba⟩, Or.inr rfl, Or.inl rfl⟩

/-- A walk in the concrete carrier graph lifts to a chain of selected
frontier-edge carrier segments between any selected edge incident to the start
vertex and any selected edge incident to the terminal vertex. -/
theorem unboundedFrontierEdgeCarrierSegmentChain_of_carrierGraph_walk
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {a b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}
    (walk : (unboundedFrontierCarrierGraph C inputs).Walk a b) :
    forall e f :
        {e : PlanarInterface.Edge n // e ∈ unboundedFrontierEdgeSet C inputs},
      (e.1.1 = a.1 ∨ e.1.2 = a.1) ->
        (f.1.1 = b.1 ∨ f.1.2 = b.1) ->
          Relation.ReflTransGen
            (unboundedFrontierEdgeCarrierSegmentsMeet inputs) e f := by
  induction walk with
  | nil =>
      intro e f he hf
      exact
        Relation.ReflTransGen.single
          (unboundedFrontierEdgeCarrierSegmentsMeet_of_common_carrier_vertex
            (C := C) (inputs := inputs) he hf)
  | cons hab rest ih =>
      intro e f he hf
      rcases
          exists_unboundedFrontierEdgeCarrierEdge_of_carrierGraph_adj
            (C := C) (inputs := inputs) hab with
        ⟨g, hg_start, hg_finish⟩
      exact
        (Relation.ReflTransGen.single
          (unboundedFrontierEdgeCarrierSegmentsMeet_of_common_carrier_vertex
            (C := C) (inputs := inputs) he hg_start)).trans
          (ih g f hg_finish hf)

/-- Connectedness of the concrete unbounded-frontier carrier graph gives the
selected-edge closed-segment chain directly, using only graph walks and shared
endpoints of the actual selected frontier edges. -/
theorem unboundedFrontierEdgeCarrierSegmentChainConnected_of_carrierGraph_connected
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected) :
    UnboundedFrontierEdgeCarrierSegmentChainConnected inputs := by
  intro e f
  let hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  have he_end :
      e.1.1 ∈ unboundedFrontierVertexSet C inputs ∧
        e.1.2 ∈ unboundedFrontierVertexSet C inputs :=
    endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
      hwhole e.2
  have hf_end :
      f.1.1 ∈ unboundedFrontierVertexSet C inputs ∧
        f.1.2 ∈ unboundedFrontierVertexSet C inputs :=
    endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
      hwhole f.2
  let a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨e.1.1, he_end.1⟩
  let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨f.1.1, hf_end.1⟩
  have hreach : (unboundedFrontierCarrierGraph C inputs).Reachable a b :=
    carrier_connected.preconnected a b
  exact
    hreach.elim fun walk =>
      unboundedFrontierEdgeCarrierSegmentChain_of_carrierGraph_walk
        (C := C) (inputs := inputs) walk e f
        (by
          left
          rfl)
        (by
          left
          rfl)

/-- Concrete carrier connectedness and boundary-free local two-germ rows give
the actual-boundary-cycle frontier-equivalence rows through the edge-chain
route. -/
noncomputable def actualBoundaryCycleRows_of_carrierGraphConnected_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
    (C := C) (inputs := inputs)
    (unboundedFrontierEdgeCarrierSegmentChainConnected_of_carrierGraph_connected
      (C := C) (inputs := inputs) carrier_connected)
    localSource.toExistsSource

/-- Final S2 cycle rows from concrete carrier connectedness and the
boundary-free local two-germ/no-third-germ source. -/
noncomputable def unboundedExteriorCycleRows_of_carrierGraphConnected_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
    (C := C) (inputs := inputs)
    (unboundedFrontierEdgeCarrierSegmentChainConnected_of_carrierGraph_connected
      (C := C) (inputs := inputs) carrier_connected)
    localSource.toExistsSource

/-- Final S2 cycle rows from the compact current carrier route: selected-edge
chain connectivity plus the boundary-free two-neighbour/no-third-germ source.

This is the shortest non-circular eraser after the BP route audit.  It keeps
the two remaining proof obligations explicit and does not pass through a final
cycle row as an assumption. -/
noncomputable def unboundedExteriorCycleRows_of_edgeChain_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
    (C := C) (inputs := inputs)
    edge_segment_chain
    localSource.toExistsSource

/-- Final S2 cycle rows from the honest local-sector route.

The selected-edge chain gives the global carrier connectivity, while
`UnboundedFrontierCarrierLocalSectorRowsAt` gives the two real selected
incident carrier edges at each frontier vertex. -/
noncomputable def unboundedExteriorCycleRows_of_edgeChain_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_of_edgeChain_localSectorRows_fixedSide
    (C := C) (inputs := inputs)
    edge_segment_chain localSectorRows

/-- Final S2 cycle rows from edge-chain connectivity plus the local-radius
no-third source, without first manufacturing the global closed-germ source. -/
noncomputable def
    unboundedExteriorCycleRows_of_edgeChain_localNoThirdGermSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (localSource : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_edgeChain_localSectorRows
    (C := C) (inputs := inputs)
    edge_segment_chain localSource.toLocalSectorRows

/-- Final S2 cycle rows from edge-chain connectivity and concrete carrier
neighbour-pair rows, via the honest local-radius no-third source. -/
noncomputable def unboundedExteriorCycleRows_of_edgeChain_neighborPairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_edgeChain_localNoThirdGermSource
    (C := C) (inputs := inputs)
    edge_segment_chain
    (BoundaryFreeLocalNoThirdGermSourceRows.ofNeighborPairRows
      (C := C) (inputs := inputs) neighborRows)

/-- Family-level finite-plane theorem from the compact current carrier route:
edge-chain connectivity and boundary-free no-third-germ rows for every input
package. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_boundaryFreeSource
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs ∧
            Nonempty (BoundaryFreeNoThirdGermSource inputs)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_edgeChain_boundaryFreeSource
        (C := C) (inputs := inputs)
        (rows C inputs).1
        (Classical.choice (rows C inputs).2))

/-- Family-level finite-plane theorem from edge-chain connectivity and honest
pointwise local-sector rows. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_localSectorRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs ∧
            Nonempty
              (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      let localRows := rows C inputs
      unboundedExteriorCycleRows_of_edgeChain_localSectorRows
        (C := C) (inputs := inputs)
        localRows.1 (Classical.choice localRows.2))

/-- Family-level finite-plane theorem from edge-chain connectivity and the
local-radius no-third-germ source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_localNoThirdGermSource
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs ∧
            Nonempty (BoundaryFreeLocalNoThirdGermSourceRows inputs)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_localSectorRows
    (fun C inputs =>
      let localRows := rows C inputs
      ⟨localRows.1, ⟨(Classical.choice localRows.2).toLocalSectorRows⟩⟩)

/-- Family-level finite-plane theorem from edge-chain connectivity and concrete
carrier neighbour-pair rows, routed through the honest local-radius no-third
source rather than endpoint-only rows. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_neighborPairRows_paired
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs ∧
            Nonempty
              (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierNeighborPairAt inputs a)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      let localRows := rows C inputs
      unboundedExteriorCycleRows_of_edgeChain_neighborPairRows
        (C := C) (inputs := inputs)
        localRows.1 (Classical.choice localRows.2))

/-- Concrete carrier connectedness plus endpoint-incident local rows close the
boundary-free S2 route.

This is the endpoint-row version of
`unboundedExteriorCycleRows_of_carrierGraphConnected_boundaryFreeSource`: the
endpoint package stays visible as the source object until this final eraser. -/
noncomputable def unboundedExteriorCycleRows_of_carrierGraphConnected_endpointIncidentSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    (localRows : BoundaryFreeEndpointIncidentSourceRows inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_carrierGraphConnected_boundaryFreeSource
    (C := C) (inputs := inputs)
    carrier_connected localRows.toBoundaryFreeNoThirdGermSource

/-- Cyclic coverage of the concrete carrier closes the connected-carrier input
for the boundary-free final-row route.

This avoids the generic carrier-graph degree-two/local-sector source surface
when the boundary-free no-third-germ source is already the local S2 input. -/
noncomputable def unboundedExteriorCycleRows_of_cyclicCoverage_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (coverage : UnboundedFrontierCarrierCyclicCoverageRows C inputs)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_carrierGraphConnected_boundaryFreeSource
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierGraph_connected_of_cyclicCoverageRows coverage)
    localSource

/-- Frontier preconnectedness plus boundary-free local two-germ rows close the
carrier-connected source route. -/
noncomputable def unboundedExteriorCycleRows_of_frontierPreconnected_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_carrierGraphConnected_boundaryFreeSource
    (C := C) (inputs := inputs)
    (S2_agent_frontier_cover_to_connected_carrier_integration_of_frontier_edge_point
      (C := C) inputs frontier_preconnected
      localSource.toLocalSectorRows)
    localSource

/-- Component-topology rows plus the boundary-free local source close the
concrete-carrier S2 route directly.

This is the component-topology owner-side eraser: the component rows source
connectedness of the actual unbounded-frontier carrier, while the local source
supplies degree two through the already checked local-sector row. -/
noncomputable def unboundedExteriorCycleRows_of_componentTopology_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (componentTopologyRows :
      UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_carrierGraphConnected_boundaryFreeSource
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierGraph_connected_of_componentTopologySourceRows
      inputs componentTopologyRows)
    localSource

/-- Genuine exterior-carrier rows plus boundary-free local rows close the
current concrete-carrier S2 route.

The carrier rows source connectedness of the actual carrier; the boundary-free
rows source degree two through the local-sector eraser. -/
noncomputable def unboundedExteriorCycleRows_of_exteriorCarrier_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (carrierRows : Nonempty (ExteriorFrontierCarrierRows.{u} C inputs))
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_carrierGraphConnected_boundaryFreeSource
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierGraph_connected_of_exteriorFrontierCarrierRows_nonempty
      (C := C) (inputs := inputs) carrierRows)
    localSource

/-- Incident-only local rows are enough for the boundary-free local source in
the genuine exterior-carrier route. -/
noncomputable def unboundedExteriorCycleRows_of_exteriorCarrier_incidentOnlySource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (carrierRows : Nonempty (ExteriorFrontierCarrierRows.{u} C inputs))
    (localRows : BoundaryFreeIncidentOnlySourceRows inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_exteriorCarrier_boundaryFreeSource
    (C := C) (inputs := inputs) carrierRows
    (localRows.toBoundaryFreeNoThirdGermSource)

/-- Endpoint-incident local rows are enough for the boundary-free local source
in the genuine exterior-carrier route. -/
noncomputable def unboundedExteriorCycleRows_of_exteriorCarrier_endpointIncidentSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (carrierRows : Nonempty (ExteriorFrontierCarrierRows.{u} C inputs))
    (localRows : BoundaryFreeEndpointIncidentSourceRows inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_exteriorCarrier_incidentOnlySource
    (C := C) (inputs := inputs) carrierRows
    localRows.toIncidentOnlyRows

/-- Family-level S2 theorem from the two remaining concrete-carrier
certificates: connectedness of the actual unbounded-frontier carrier graph and
the boundary-free local two-germ/no-third-germ source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_carrierGraphConnected_boundaryFreeSource
    (rows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          (unboundedFrontierCarrierGraph C inputs).Connected ∧
            Nonempty (BoundaryFreeNoThirdGermSource inputs)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_carrierGraphConnected_boundaryFreeSource
        (C := C) (inputs := inputs)
        (rows C inputs).1 (Classical.choice (rows C inputs).2))

/-- Family-level S2 theorem from concrete carrier connectedness and
endpoint-incident local source rows. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_carrierGraphConnected_endpointIncidentSource
    (rows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          (unboundedFrontierCarrierGraph C inputs).Connected ∧
            Nonempty (BoundaryFreeEndpointIncidentSourceRows inputs)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_carrierGraphConnected_endpointIncidentSource
        (C := C) (inputs := inputs)
        (rows C inputs).1 (Classical.choice (rows C inputs).2))

/-- Family-level S2 theorem from frontier preconnectedness of the unbounded
exterior component and the boundary-free local two-germ/no-third-germ source.
-/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_frontierPreconnected_boundaryFreeSource
    (rows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          IsPreconnected
            (frontier (unboundedExteriorComponentRows C inputs).exterior) ∧
            Nonempty (BoundaryFreeNoThirdGermSource inputs)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_frontierPreconnected_boundaryFreeSource
        (C := C) (inputs := inputs)
        (rows C inputs).1 (Classical.choice (rows C inputs).2))

/-- Family-level S2 theorem from component-topology source rows and the
boundary-free local two-germ/no-third-germ source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_componentTopology_boundaryFreeSource
    (rows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          And
            (UnboundedExteriorFrontierComponentTopologySourceRows inputs)
            (Nonempty (BoundaryFreeNoThirdGermSource inputs))) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_componentTopology_boundaryFreeSource
        (C := C) (inputs := inputs)
        (rows C inputs).1 (Classical.choice (rows C inputs).2))

/-- Family-level S2 theorem from component-topology rows, pointwise concrete
carrier neighbour-pair rows, and the incident selected-edge endpoint source.

This is the current neighbour-pair source surface: the component rows supply
carrier connectedness, the neighbour-pair rows supply local sectors, and the
incident-edge row closes adjacent frontier endpoints. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_componentTopology_neighborPairRows_incidentEdge
    (componentTopologyRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (neighborRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (incident_edge :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorFrontierCycleRows_of_componentTopology_neighborPairRows_incidentEdge
        (C := C) (inputs := inputs)
        (componentTopologyRows C inputs)
        (neighborRows C inputs)
        (incident_edge C inputs))

/-- Family-level no-cut source surface for the component-topology /
incident-edge S2 route.

This replaces the already-erased neighbour-pair input with the concrete
cut-partition source row at every frontier vertex. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_componentTopology_neighborPairCutRows_incidentEdge
    (componentTopologyRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (cutRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a)
    (incident_edge :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorFrontierCycleRows_of_componentTopology_neighborPairCutRows_incidentEdge
        (C := C) (inputs := inputs)
        (componentTopologyRows C inputs)
        (cutRows C inputs)
        (incident_edge C inputs))

/-- Family-level edge-chain / neighbour-pair / incident-edge S2 route. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_neighborPairRows_incidentEdge
    (edgeChainRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (neighborRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (incident_edge :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorFrontierCycleRows_of_edgeChain_neighborPairRows_incidentEdge
        (C := C) (inputs := inputs)
        (edgeChainRows C inputs)
        (neighborRows C inputs)
        (incident_edge C inputs))

/-- Family-level edge-chain / no-cut cut-row / incident-edge S2 route. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_neighborPairCutRows_incidentEdge
    (edgeChainRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (cutRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a)
    (incident_edge :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorFrontierCycleRows_of_edgeChain_neighborPairCutRows_incidentEdge
        (C := C) (inputs := inputs)
        (edgeChainRows C inputs)
        (cutRows C inputs)
        (incident_edge C inputs))

/-- Family-level S2 theorem from genuine exterior-carrier rows and the
boundary-free local no-third-germ source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_exteriorCarrier_boundaryFreeSource
    (rows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Nonempty (ExteriorFrontierCarrierRows.{0} C inputs) ∧
            Nonempty (BoundaryFreeNoThirdGermSource inputs)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_exteriorCarrier_boundaryFreeSource
        (C := C) (inputs := inputs)
        (rows C inputs).1 (Classical.choice (rows C inputs).2))

/-- Family-level S2 theorem from genuine exterior-carrier rows and
incident-only local source rows. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_exteriorCarrier_incidentOnlySource
    (rows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Nonempty (ExteriorFrontierCarrierRows.{0} C inputs) ∧
            Nonempty (BoundaryFreeIncidentOnlySourceRows inputs)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_exteriorCarrier_incidentOnlySource
        (C := C) (inputs := inputs)
        (rows C inputs).1 (Classical.choice (rows C inputs).2))

/-- Family-level S2 theorem from genuine exterior-carrier rows and endpoint
incident local source rows. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_exteriorCarrier_endpointIncidentSource
    (carrierRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Nonempty (ExteriorFrontierCarrierRows.{0} C inputs))
    (endpointRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeEndpointIncidentSourceRows inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_exteriorCarrier_endpointIncidentSource
        (C := C) (inputs := inputs)
        (carrierRows C inputs) (endpointRows C inputs))

/-- Raw-tail coverage plus pointwise local-sector rows gives the raw-orbit
coverage certificate.

This is the local-sector version of the raw coverage eraser: every selected
carrier edge is recovered from the two honest local selected-edge rows at a
raw tail, not from a global closed-germ boundary-free source. -/
def rawOrbitCoverageSourceRows_of_tailCoverage_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    RawOrbitCoverageSourceRows (inputs := inputs) O where
  dart_edge_openSegment_frontier := dart_edge_openSegment_frontier
  edge_coverage := by
    let edge_openSegment_frontier :
        forall k : Fin O.period,
          forall p : PlanarInterface.Point,
            PlanarInterface.InOpenSegment p
              ((canonicalGraph C).point (O.dart k).tail)
              ((canonicalGraph C).point
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
            p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
      rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier
        (inputs := inputs) O dart_edge_openSegment_frontier
    let raw_pred_succ_tail_ne :
        forall k : Fin O.period,
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
      rawFaceSuccOrbit_pred_succ_tail_ne_of_geometric_localSectorRows
        (C := C) (inputs := inputs) O
        edge_openSegment_frontier localSectorRows
    exact
      rawFaceSuccOrbit_edge_coverage_of_tail_coverage_localSectorRows
        (C := C) (inputs := inputs) O
        edge_openSegment_frontier frontier_vertex_tail_coverage
        localSectorRows raw_pred_succ_tail_ne

/-- Raw-tail coverage plus boundary-free local rows gives the raw-orbit
coverage certificate.

This moves the global edge-coverage obligation down to the more natural source
row: every actual unbounded-frontier carrier vertex is hit by a raw tail.  The
pointwise local two-germ rows then force each selected carrier edge to be one
of the predecessor/successor raw edges at that tail. -/
def rawOrbitCoverageSourceRows_of_tailCoverage_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      ∀ k : Fin O.period,
        ∀ p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) →
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    RawOrbitCoverageSourceRows (inputs := inputs) O where
  dart_edge_openSegment_frontier := dart_edge_openSegment_frontier
  edge_coverage := by
    let edge_openSegment_frontier :
        ∀ k : Fin O.period,
          ∀ p : PlanarInterface.Point,
            PlanarInterface.InOpenSegment p
              ((canonicalGraph C).point (O.dart k).tail)
              ((canonicalGraph C).point
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) →
            p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
      rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier
        (inputs := inputs) O dart_edge_openSegment_frontier
    let localSectorRows := localSource.toLocalSectorRows
    let raw_pred_succ_tail_ne :
        ∀ k : Fin O.period,
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
      rawFaceSuccOrbit_pred_succ_tail_ne_of_geometric_localSectorRows
        (C := C) (inputs := inputs) O
        edge_openSegment_frontier localSectorRows
    exact
      rawFaceSuccOrbit_edge_coverage_of_tail_coverage_localSectorRows
        (C := C) (inputs := inputs) O
        edge_openSegment_frontier frontier_vertex_tail_coverage
        localSectorRows raw_pred_succ_tail_ne

/-- Claim `S2-agent-edge-chain-real-proof-20260520ay`, raw-coverage eraser.

The selected raw-orbit frontier-edge coverage rows directly source the two
upstream rows used by the component-topology route: the closed-segment
selected-edge chain and the actual unbounded-frontier component-topology
source.  This does not pass through completed S2 cycle rows or an auxiliary
frontier graph. -/
theorem S2_agent_edge_chain_componentTopology_of_rawCoverage_boundaryFreeSource_20260520ay
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    And
      (UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
      (UnboundedExteriorFrontierComponentTopologySourceRows inputs) :=
  And.intro
    coverage.toEdgeCarrierSegmentChainConnected
    (coverage.toComponentTopologyRows localSource)

/-- Raw-tail coverage and boundary-free local rows source the selected
edge-chain/component-topology pair.

This is the non-circular raw exterior face-walk form: tail coverage plus the
pointwise boundary-free source first gives the checked raw coverage row, then
the raw-coverage eraser above gives the actual selected-edge/component rows. -/
theorem S2_agent_edge_chain_componentTopology_of_rawTailCoverage_boundaryFreeSource_20260520ay
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    And
      (UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
      (UnboundedExteriorFrontierComponentTopologySourceRows inputs) :=
  S2_agent_edge_chain_componentTopology_of_rawCoverage_boundaryFreeSource_20260520ay
    (C := C) (inputs := inputs)
    (rawOrbitCoverageSourceRows_of_tailCoverage_boundaryFreeSource
      (C := C) (inputs := inputs) O
      dart_edge_openSegment_frontier frontier_vertex_tail_coverage
      localSource)
    localSource

/-- Endpoint-incident local rows version of claim
`S2-agent-edge-chain-real-proof-20260520ay`.

The endpoint package is erased only to the boundary-free no-third-germ source
already used by the raw-tail-coverage reducer; the conclusion remains the
upstream selected edge-chain/component-topology pair. -/
theorem S2_agent_edge_chain_componentTopology_real_proof_20260520ay
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (localRows : BoundaryFreeEndpointIncidentSourceRows inputs) :
    And
      (UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
      (UnboundedExteriorFrontierComponentTopologySourceRows inputs) :=
  S2_agent_edge_chain_componentTopology_of_rawTailCoverage_boundaryFreeSource_20260520ay
    (C := C) (inputs := inputs) O
    dart_edge_openSegment_frontier frontier_vertex_tail_coverage
    localRows.toBoundaryFreeNoThirdGermSource

/-- Connected-carrier version of
`rawOrbitCoverageSourceRows_of_tailCoverage_localSectorRows`.

The concrete carrier connectedness is used only to source raw-tail coverage;
edge coverage itself is still derived from the pointwise local-sector rows. -/
def rawOrbitCoverageSourceRows_of_connectedCarrier_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    RawOrbitCoverageSourceRows (inputs := inputs) O := by
  let edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
    rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier
      (inputs := inputs) O dart_edge_openSegment_frontier
  let raw_pred_succ_tail_ne :
      forall k : Fin O.period,
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
    rawFaceSuccOrbit_pred_succ_tail_ne_of_geometric_localSectorRows
      (C := C) (inputs := inputs) O
      edge_openSegment_frontier localSectorRows
  let frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1 :=
    S2_agent_tail_coverage_from_connected_carrier
      (C := C) (inputs := inputs) O
      dart_edge_openSegment_frontier carrier_connected
      localSectorRows raw_pred_succ_tail_ne
  exact
    rawOrbitCoverageSourceRows_of_tailCoverage_localSectorRows
      (C := C) (inputs := inputs) O
      dart_edge_openSegment_frontier frontier_vertex_tail_coverage
      localSectorRows

/-- Connected-carrier version of
`rawOrbitCoverageSourceRows_of_tailCoverage_boundaryFreeSource`.

The concrete carrier connectedness is used only to source raw-tail coverage;
edge coverage itself is still derived from the pointwise local two-germ rows. -/
def rawOrbitCoverageSourceRows_of_connectedCarrier_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      ∀ k : Fin O.period,
        ∀ p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) →
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    RawOrbitCoverageSourceRows (inputs := inputs) O := by
  let edge_openSegment_frontier :
      ∀ k : Fin O.period,
        ∀ p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) →
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
    rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier
      (inputs := inputs) O dart_edge_openSegment_frontier
  let localSectorRows := localSource.toLocalSectorRows
  let raw_pred_succ_tail_ne :
      ∀ k : Fin O.period,
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
    rawFaceSuccOrbit_pred_succ_tail_ne_of_geometric_localSectorRows
      (C := C) (inputs := inputs) O
      edge_openSegment_frontier localSectorRows
  let frontier_vertex_tail_coverage :
      ∀ a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1 :=
    S2_agent_tail_coverage_from_connected_carrier
      (C := C) (inputs := inputs) O
      dart_edge_openSegment_frontier carrier_connected
      localSectorRows raw_pred_succ_tail_ne
  exact
    rawOrbitCoverageSourceRows_of_tailCoverage_boundaryFreeSource
      (C := C) (inputs := inputs) O
      dart_edge_openSegment_frontier frontier_vertex_tail_coverage localSource

/-- Actual-boundary-cycle rows from raw-orbit coverage and boundary-free local
two-germ source rows. -/
noncomputable def
    actualBoundaryCycleRows_of_rawCoverage_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_rawOrbitCoverage_boundaryFree_noThirdGerm
    (C := C) (inputs := inputs) O
    coverage.dart_edge_openSegment_frontier
    coverage.edge_coverage
    localSource.toExistsSource

set_option linter.style.longLine false in
/-- Raw coverage plus boundary-free local rows and raw orientation produce the
exact boundary-sector source package.

This is the coverage-level companion to the raw-orbit orientation theorem:
coverage gives raw-tail coverage of every selected frontier carrier vertex,
while the remaining cut and orientation rows stay stated on the selected raw
face orbit. -/
noncomputable def
    boundaryVertexExteriorSectorRows_source_of_rawCoverage_boundaryFreeSource_rawOrientation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start)
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs)
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j)
    (raw_orientation :
      forall k : Fin O.period,
        graphDartArg (canonicalGeometricGraph C)
            (O.dart k).tail
            (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
          graphDartArg (canonicalGeometricGraph C)
            (O.dart k).tail
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
  BoundaryFreeNoThirdGermSource.boundaryVertexExteriorSectorRows_source_of_rawFaceSuccOrbit_rawOrientation
    (C := C) (inputs := inputs) O localSource
    (S2_frontier_vertex_tail_coverage_of_edgeCoverage_boundaryFree_source
      (C := C) (inputs := inputs) O coverage.edge_coverage
      localSource.toExistsSource)
    coverage.dart_edge_openSegment_frontier cutRows raw_orientation

/-- Final S2 cycle rows from raw-orbit coverage and boundary-free local
two-germ source rows. -/
noncomputable def
    unboundedExteriorCycleRows_of_rawCoverage_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
    (actualBoundaryCycleRows_of_rawCoverage_boundaryFreeSource
      (C := C) (inputs := inputs) O coverage localSource)

/-- Raw-orbit coverage plus endpoint-incident local rows give the final
unbounded exterior cycle rows directly. -/
noncomputable def unboundedExteriorCycleRows_of_rawCoverage_endpointIncidentRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rawRows :
      Exists fun R : UnitDistanceRotationSystem C =>
        Exists fun start : UnitDistanceDart C =>
          Exists fun O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
            RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localRows : BoundaryFreeEndpointIncidentSourceRows inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  let R : UnitDistanceRotationSystem C := Classical.choose rawRows
  let hstart := Classical.choose_spec rawRows
  let start : UnitDistanceDart C := Classical.choose hstart
  let hO := Classical.choose_spec hstart
  let O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start :=
    Classical.choose hO
  let coverage : RawOrbitCoverageSourceRows (inputs := inputs) O :=
    Classical.choose_spec hO
  S2_unboundedExteriorFrontierCycleRows_of_rawOrbitCoverage_boundaryFree_noThirdGerm
    (C := C) (inputs := inputs) O
    coverage.dart_edge_openSegment_frontier
    coverage.edge_coverage
    localRows.toBoundaryFreeNoThirdGermSource.toExistsSource

/-- Raw-orbit coverage plus pointwise local-sector rows give the final S2
cycle rows through the selected-edge route.

The raw coverage supplies the selected-edge segment chain; the local-sector
family supplies the two honest selected carrier heads at each frontier vertex.
No global closed-germ source or all-adjacent endpoint row is used. -/
noncomputable def unboundedExteriorCycleRows_of_rawCoverage_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rawRows :
      Exists fun R : UnitDistanceRotationSystem C =>
        Exists fun start : UnitDistanceDart C =>
          Exists fun O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
            RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs := by
  let R : UnitDistanceRotationSystem C := Classical.choose rawRows
  let hstart := Classical.choose_spec rawRows
  let start : UnitDistanceDart C := Classical.choose hstart
  let hO := Classical.choose_spec hstart
  let O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start :=
    Classical.choose hO
  let coverage : RawOrbitCoverageSourceRows (inputs := inputs) O :=
    Classical.choose_spec hO
  exact
    S2_unboundedExteriorFrontierCycleRows_of_edgeChain_localSectorRows_fixedSide
      (C := C) (inputs := inputs)
      coverage.toEdgeCarrierSegmentChainConnected
      localSectorRows

set_option linter.style.longLine false in
/-- Local boundary-free raw-orbit source row.

This is the local-radius/raw-coverage package: the orbit covers the actual
selected `unboundedFrontierEdgeSet`, and the local source supplies the
pointwise selected-germ/local-sector rows.  It intentionally does not contain
the global arbitrary-radius closed-germ source. -/
abbrev BoundaryFreeLocalRawOrbitSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  Exists fun R : UnitDistanceRotationSystem C =>
    Exists fun start : UnitDistanceDart C =>
      Exists fun O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
        RawOrbitCoverageSourceRows (inputs := inputs) O ∧
          Nonempty (BoundaryFreeLocalNoThirdGermSourceRows inputs)

set_option linter.style.longLine false in
/-- Raw coverage plus local selected-germ rows fill the local boundary-free
raw-orbit source row. -/
def boundaryFreeLocalRawOrbitSourceRows_of_rawCoverage_localNoThirdGermSource_20260522s2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    BoundaryFreeLocalRawOrbitSourceRows inputs :=
  ⟨R, start, O, coverage, ⟨localSource⟩⟩

set_option linter.style.longLine false in
/-- Raw coverage plus pointwise local-sector rows fill the local
boundary-free raw-orbit source row. -/
def boundaryFreeLocalRawOrbitSourceRows_of_rawCoverage_localSectorRows_20260522s2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    BoundaryFreeLocalRawOrbitSourceRows inputs :=
  boundaryFreeLocalRawOrbitSourceRows_of_rawCoverage_localNoThirdGermSource_20260522s2
    (C := C) (inputs := inputs) coverage
    (boundaryFreeLocalNoThirdGermSourceRows_of_localSectorRows_selectedEdges
      (C := C) (inputs := inputs) localSectorRows)

set_option linter.style.longLine false in
/-- Raw-tail coverage plus pointwise local-sector rows fill the local
boundary-free raw-orbit source row. -/
def boundaryFreeLocalRawOrbitSourceRows_of_rawTailCoverage_localSectorRows_20260522s2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    BoundaryFreeLocalRawOrbitSourceRows inputs :=
  boundaryFreeLocalRawOrbitSourceRows_of_rawCoverage_localSectorRows_20260522s2
    (C := C) (inputs := inputs)
    (rawOrbitCoverageSourceRows_of_tailCoverage_localSectorRows
      (C := C) (inputs := inputs) O
      dart_edge_openSegment_frontier frontier_vertex_tail_coverage
      localSectorRows)
    localSectorRows

set_option linter.style.longLine false in
/-- Claim `S2-q16-exterior-seed-raw-orbit`.

Input-facing selected seed/raw-orbit source reducer.  The finite outer-component
input first supplies a genuine unbounded exterior frontier seed; local-sector
rows orient it to a selected geometric raw face-successor start dart.  The two
remaining orbit-tracing rows are stated only for that selected local edge and
raw orbit, and are immediately erased to the checked raw-coverage plus local
boundary-free package. -/
theorem S2_q16_selected_seed_rawCoverage_boundaryFreeLocalRawOrbitSourceRows_of_inputs_localSectorRows_rawTailCoverage_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (dart_edge_openSegment_frontier :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
          start.tail = e.1 ->
            start.head = e.2 ->
              forall O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit
                  (geometricUnitDistanceRotationSystem C)
                  start,
                forall k : Fin O.period,
                  forall q : PlanarInterface.Point,
                    PlanarInterface.InOpenSegment q
                      ((canonicalGraph C).point (O.dart k).tail)
                      ((canonicalGraph C).point (O.dart k).head) ->
                    q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
          start.tail = e.1 ->
            start.head = e.2 ->
              forall O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit
                  (geometricUnitDistanceRotationSystem C)
                  start,
                forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
                  Exists fun k : Fin O.period => (O.dart k).tail = a.1) :
    Exists fun _seed : UnboundedExteriorFrontierSeed inputs =>
      Exists fun e : PlanarInterface.Edge n =>
        Exists fun p : PlanarInterface.Point =>
          Exists fun start : UnitDistanceDart C =>
            e ∈ unboundedFrontierEdgeSet C inputs ∧
              UnboundedExteriorFrontierEdgeLocalRows C inputs e p ∧
                start.tail = e.1 ∧
                  start.head = e.2 ∧
                    Exists fun O :
                      UnitDistanceRotationSystem.RawFaceSuccOrbit
                        (geometricUnitDistanceRotationSystem C)
                        start =>
                      RawOrbitCoverageSourceRows (inputs := inputs) O ∧
                        BoundaryFreeLocalRawOrbitSourceRows inputs := by
  rcases unboundedExteriorFrontierSeed_nonempty inputs with ⟨seed⟩
  rcases
      S2_r57_selected_geometricRawFaceSuccOrbitSeed_of_unboundedExteriorFrontierSeed_localSectorRows_20260521r57
        (C := C) (inputs := inputs) localSectorRows seed with
    ⟨e, p, start, hselected, edgeRows, htail, hhead, horbit⟩
  rcases horbit with ⟨O⟩
  let coverage : RawOrbitCoverageSourceRows (inputs := inputs) O :=
    rawOrbitCoverageSourceRows_of_tailCoverage_localSectorRows
      (C := C) (inputs := inputs) O
      (dart_edge_openSegment_frontier edgeRows htail hhead O)
      (frontier_vertex_tail_coverage edgeRows htail hhead O)
      localSectorRows
  exact
    ⟨seed, e, p, start, hselected, edgeRows, htail, hhead, O, coverage,
      boundaryFreeLocalRawOrbitSourceRows_of_rawCoverage_localSectorRows_20260522s2
        (C := C) (inputs := inputs) coverage localSectorRows⟩

set_option linter.style.longLine false in
/-- Claim `S2-q17-raw-tail-coverage-source`.

Strict q17 lowering of the two raw-tail inputs used by q16.  Actual component
topology rows give connectedness of the concrete unbounded-frontier carrier;
local-sector rows give neighbour closure of the raw-tail set; therefore the
positive `frontier_vertex_tail_coverage` callback is derived internally from
the remaining primitive
`dart_edge_openSegment_frontier`.

No completed boundary cycle, actual-sector rows, cyclic carrier coverage, or
actual-sector-row source is used. -/
theorem S2_q17_selected_seed_rawCoverage_boundaryFreeLocalRawOrbitSourceRows_of_inputs_componentTopology_localSectorRows_dartEdgeFrontier_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (componentRows :
      UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (dart_edge_openSegment_frontier :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
          start.tail = e.1 ->
            start.head = e.2 ->
              forall O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit
                  (geometricUnitDistanceRotationSystem C)
                  start,
                forall k : Fin O.period,
                  forall q : PlanarInterface.Point,
                    PlanarInterface.InOpenSegment q
                      ((canonicalGraph C).point (O.dart k).tail)
                      ((canonicalGraph C).point (O.dart k).head) ->
                    q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) :
    Exists fun _seed : UnboundedExteriorFrontierSeed inputs =>
      Exists fun e : PlanarInterface.Edge n =>
        Exists fun p : PlanarInterface.Point =>
          Exists fun start : UnitDistanceDart C =>
            e ∈ unboundedFrontierEdgeSet C inputs ∧
              UnboundedExteriorFrontierEdgeLocalRows C inputs e p ∧
                start.tail = e.1 ∧
                  start.head = e.2 ∧
                    Exists fun O :
                      UnitDistanceRotationSystem.RawFaceSuccOrbit
                        (geometricUnitDistanceRotationSystem C)
                        start =>
                      RawOrbitCoverageSourceRows (inputs := inputs) O ∧
                        BoundaryFreeLocalRawOrbitSourceRows inputs := by
  refine
    S2_q16_selected_seed_rawCoverage_boundaryFreeLocalRawOrbitSourceRows_of_inputs_localSectorRows_rawTailCoverage_20260522
      (C := C) inputs localSectorRows dart_edge_openSegment_frontier ?_
  intro e p start edgeRows htail hhead O
  let dartFrontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
    dart_edge_openSegment_frontier edgeRows htail hhead O
  let edgeFrontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
    rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier
      (inputs := inputs) O dartFrontier
  let raw_pred_succ_tail_ne :
      forall k : Fin O.period,
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
    rawFaceSuccOrbit_pred_succ_tail_ne_of_geometric_localSectorRows
      (C := C) (inputs := inputs) O edgeFrontier localSectorRows
  exact
    S2_q13_raw_tail_hit_from_component_frontier_rows
      (C := C) (inputs := inputs) O dartFrontier componentRows
      localSectorRows raw_pred_succ_tail_ne

set_option linter.style.longLine false in
/-- Raw coverage plus selected-neighbour geometric rows and the safe local
incident-germ row fill the local boundary-free raw-orbit source row. -/
noncomputable def
    boundaryFreeLocalRawOrbitSourceRows_of_rawCoverage_selectedNeighborGeometricOrder_localIncident_20260522s2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (localIncidentRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    BoundaryFreeLocalRawOrbitSourceRows inputs :=
  boundaryFreeLocalRawOrbitSourceRows_of_rawCoverage_localNoThirdGermSource_20260522s2
    (C := C) (inputs := inputs) coverage
    (boundaryFreeLocalNoThirdGermSourceRows_of_selectedNeighborGeometricOrder_localIncident_20260521k6
      (C := C) (inputs := inputs) selectedRows localIncidentRows)

set_option linter.style.longLine false in
/-- Raw-tail coverage plus selected-neighbour geometric rows and the safe local
incident-germ row fill the local boundary-free raw-orbit source row. -/
noncomputable def
    boundaryFreeLocalRawOrbitSourceRows_of_rawTailCoverage_selectedNeighborGeometricOrder_localIncident_20260522s2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (selectedRows :
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (localIncidentRows :
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    BoundaryFreeLocalRawOrbitSourceRows inputs := by
  let localSource :
      BoundaryFreeLocalNoThirdGermSourceRows inputs :=
    boundaryFreeLocalNoThirdGermSourceRows_of_selectedNeighborGeometricOrder_localIncident_20260521k6
      (C := C) (inputs := inputs) selectedRows localIncidentRows
  exact
    boundaryFreeLocalRawOrbitSourceRows_of_rawCoverage_localNoThirdGermSource_20260522s2
      (C := C) (inputs := inputs)
      (rawOrbitCoverageSourceRows_of_tailCoverage_localSectorRows
        (C := C) (inputs := inputs) O
        dart_edge_openSegment_frontier frontier_vertex_tail_coverage
        localSource.toLocalSectorRows)
      localSource

set_option linter.style.longLine false in
/-- The local boundary-free raw-orbit source row is enough for the selected
edge-chain/local-sector final S2 eraser. -/
noncomputable def unboundedExteriorCycleRows_of_boundaryFreeLocalRawOrbitSourceRows_20260522s2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeLocalRawOrbitSourceRows inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  let R : UnitDistanceRotationSystem C := Classical.choose rows
  let hstart := Classical.choose_spec rows
  let start : UnitDistanceDart C := Classical.choose hstart
  let hO := Classical.choose_spec hstart
  let O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start :=
    Classical.choose hO
  let hrows := Classical.choose_spec hO
  unboundedExteriorCycleRows_of_rawCoverage_localSectorRows
    (C := C) (inputs := inputs)
    ⟨R, start, O, hrows.1⟩
    (Classical.choice hrows.2).toLocalSectorRows

set_option linter.style.longLine false in
/-- Family-level S2 handoff from the local boundary-free raw-orbit source row. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_boundaryFreeLocalRawOrbitSourceRows_20260522s2
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeLocalRawOrbitSourceRows inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_boundaryFreeLocalRawOrbitSourceRows_20260522s2
        (C := C) (inputs := inputs) (rows C inputs))

set_option linter.style.longLine false in
/-- When the genuine selected incident-germ frontier-edge row is supplied, the
local boundary-free raw-orbit source row upgrades to the existing global
boundary-free raw-coverage row. -/
noncomputable def
    boundaryFreeRawOrbitSourceRows_of_boundaryFreeLocalRawOrbitSourceRows_incidentGermFrontierEdge_20260522s2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeLocalRawOrbitSourceRows inputs)
    (incident_germ_frontier_edge :
      BoundaryFreeIncidentGermSelectedFrontierEdgeMembershipRows inputs) :
    Exists fun R : UnitDistanceRotationSystem C =>
      Exists fun start : UnitDistanceDart C =>
        Exists fun O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
          RawOrbitCoverageSourceRows (inputs := inputs) O ∧
            Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  let R : UnitDistanceRotationSystem C := Classical.choose rows
  let hstart := Classical.choose_spec rows
  let start : UnitDistanceDart C := Classical.choose hstart
  let hO := Classical.choose_spec hstart
  let O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start :=
    Classical.choose hO
  let hrows := Classical.choose_spec hO
  let localSource : BoundaryFreeLocalNoThirdGermSourceRows inputs :=
    Classical.choice hrows.2
  ⟨R, start, O, hrows.1,
    ⟨boundaryFreeNoThirdGermSource_of_localSectorRows_incidentGermFrontierEdge
      (C := C) (inputs := inputs)
      localSource.toLocalSectorRows incident_germ_frontier_edge⟩⟩

set_option linter.style.longLine false in
/-- Raw coverage plus selected-edge input rows directly fill the existing
global boundary-free raw-coverage row. -/
noncomputable def
    boundaryFreeRawOrbitSourceRows_of_rawCoverage_selectedEdgeInputSourceRows_20260522s2
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (rows : BoundaryFreeSelectedEdgeInputSourceRows inputs) :
    Exists fun R : UnitDistanceRotationSystem C =>
      Exists fun start : UnitDistanceDart C =>
        Exists fun O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
          RawOrbitCoverageSourceRows (inputs := inputs) O ∧
            Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  ⟨R, start, O, coverage,
    ⟨rows.toBoundaryFreeInputSourceReduction.boundaryFreeNoThirdGermSource⟩⟩

/-- Raw-orbit coverage plus pointwise cut-partition rows give the final S2
cycle rows through the current non-circular carrier split.

Coverage supplies the selected-edge segment chain; cut rows erase through the
checked no-cut interface to the two-neighbour rows for the concrete carrier.
This route deliberately avoids component-topology connectedness as a source
premise. -/
noncomputable def unboundedExteriorCycleRows_of_rawCoverage_cutPartitionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rawRows :
      Exists fun R : UnitDistanceRotationSystem C =>
        Exists fun start : UnitDistanceDart C =>
          Exists fun O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
            RawOrbitCoverageSourceRows (inputs := inputs) O)
    (cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs := by
  let R : UnitDistanceRotationSystem C := Classical.choose rawRows
  let hstart := Classical.choose_spec rawRows
  let start : UnitDistanceDart C := Classical.choose hstart
  let hO := Classical.choose_spec hstart
  let O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start :=
    Classical.choose hO
  let coverage : RawOrbitCoverageSourceRows (inputs := inputs) O :=
    Classical.choose_spec hO
  exact
    S2_unboundedExteriorFrontierCycleRows_of_edgeChain_neighborPairRows_fixedSide
      (C := C) (inputs := inputs)
      coverage.toEdgeCarrierSegmentChainConnected
      (unboundedFrontierCarrierNeighborPairRows_of_noCutVertex_cutPartitionRows
        (C := C) (inputs := inputs) cutRows)

/-- Raw-orbit coverage plus the ambient deleted-graph local source gives the
final S2 cycle rows through the current carrier split.

This is the object-level eraser for the current two remaining S2 sources:
raw coverage supplies the selected edge-chain, and the deleted-graph source
erases to the no-cut cut-partition rows used for pointwise two-neighbour
carrier rows. -/
noncomputable def unboundedExteriorCycleRows_of_rawCoverage_unreachableAfterDeleteInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rawRows :
      Exists fun R : UnitDistanceRotationSystem C =>
        Exists fun start : UnitDistanceDart C =>
          Exists fun O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
            RawOrbitCoverageSourceRows (inputs := inputs) O)
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_rawCoverage_cutPartitionRows
    (C := C) (inputs := inputs)
    rawRows
    (unboundedFrontierCarrierNeighborPairCutPartitionRows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) source)

/-- Family-level S2 theorem from the two non-circular source families singled
out by the current S2 route: raw-orbit coverage for the selected exterior
frontier and pointwise cut-partition rows for third carrier neighbours. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_rawCoverage_cutPartitionRows
    (rawRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                RawOrbitCoverageSourceRows (inputs := inputs) O)
    (cutRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_rawCoverage_cutPartitionRows
        (C := C) (inputs := inputs)
        (rawRows C inputs) (cutRows C inputs))

/-- Family-level S2 theorem from raw-orbit coverage and honest pointwise
local-sector rows.

This is the local-sector source surface for the live branch: the only local
input is `forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a`. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_rawCoverage_localSectorRows
    (rawRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSectorRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_rawCoverage_localSectorRows
        (C := C) (inputs := inputs)
        (rawRows C inputs) (localSectorRows C inputs))

/-- Family-level S2 theorem from raw-orbit coverage and the ambient
deleted-graph local source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_rawCoverage_unreachableAfterDeleteInputSource
    (rawRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                RawOrbitCoverageSourceRows (inputs := inputs) O)
    (source :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_rawCoverage_unreachableAfterDeleteInputSource
        (C := C) (inputs := inputs)
        (rawRows C inputs) (source C inputs))

/-- Final S2 cycle rows from independently connected carrier rows, a selected
geometric raw orbit whose dart edges lie on the exterior frontier, and the
boundary-free local two-germ source. -/
noncomputable def
    unboundedExteriorCycleRows_of_connectedCarrier_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      ∀ k : Fin O.period,
        ∀ p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) →
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorCycleRows_of_rawCoverage_boundaryFreeSource
    (C := C) (inputs := inputs) O
    (rawOrbitCoverageSourceRows_of_connectedCarrier_boundaryFreeSource
      (C := C) (inputs := inputs) O
      dart_edge_openSegment_frontier carrier_connected localSource)
    localSource

/-- Family-level S2 theorem from the two remaining source certificates:
raw-orbit coverage of the actual frontier carrier and boundary-free local
two-germ rows. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_rawCoverage_boundaryFreeSource
    (rows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                RawOrbitCoverageSourceRows (inputs := inputs) O ∧
                  Nonempty (BoundaryFreeNoThirdGermSource inputs)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      let hR := rows C inputs
      let R : UnitDistanceRotationSystem C := Classical.choose hR
      let hstart := Classical.choose_spec hR
      let start : UnitDistanceDart C := Classical.choose hstart
      let hO := Classical.choose_spec hstart
      let O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start :=
        Classical.choose hO
      let hrows := Classical.choose_spec hO
      unboundedExteriorCycleRows_of_rawCoverage_boundaryFreeSource
        (C := C) (inputs := inputs) O hrows.1 (Classical.choice hrows.2))

/-- Family-level S2 theorem from raw-orbit coverage and endpoint-incident
local rows. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_rawCoverage_endpointIncidentRows
    (rawRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localRows :
      ∀ {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeEndpointIncidentSourceRows inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      unboundedExteriorCycleRows_of_rawCoverage_endpointIncidentRows
        (C := C) (inputs := inputs)
        (rawRows C inputs)
        (localRows C inputs))

/-- Claim `S2-agent-boundaryfree-carrier-connected-source-20260520w`,
component-avoidance reducer.

This packages the two fields consumed by the connected raw-orbit source:
the boundary-free no-third-germ local source and connectedness of the concrete
unbounded-frontier carrier.  The connectedness half is reduced to the
Janiszewski component-avoidance row plus the local carrier realization already
contained in `BoundaryFreeNoThirdGermSource`. -/
noncomputable def
    boundaryFreeCarrierConnected_source_of_janiszewskiComponentAvoidance
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (component_avoidance :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        (unboundedFrontierCarrierGraph C inputs).Connected) :=
  ⟨localSource,
    localSource.connected_of_janiszewskiComponentAvoidance
      (C := C) (inputs := inputs) component_avoidance⟩

/-- Claim `S2-agent-boundaryfree-carrier-connected-source-20260520w`,
actual-boundary reducer.

This packages the exact two rows consumed by the selected actual-arc route:
the boundary-free no-third-germ local source and connectedness of the concrete
unbounded-frontier carrier.  The connectedness half is not a new assumption;
it is the checked actual-boundary/local-source reducer.

The package is a subtype rather than `And`: the local source is data in
`Type`, while carrier connectedness is a proposition. -/
noncomputable def
    boundaryFreeCarrierConnected_source_of_actualBoundaryRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        (unboundedFrontierCarrierGraph C inputs).Connected) :=
  ⟨localSource,
    BoundaryFreeNoThirdGermSource.unboundedFrontierCarrierGraph_connected_of_actualBoundaryRows
      (C := C) (inputs := inputs) actualRows localSource⟩

/-- Nonempty local-source variant of
`boundaryFreeCarrierConnected_source_of_actualBoundaryRows`. -/
noncomputable def
    boundaryFreeCarrierConnected_source_of_actualBoundaryRows_nonempty
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (localSource : Nonempty (BoundaryFreeNoThirdGermSource inputs)) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        (unboundedFrontierCarrierGraph C inputs).Connected) :=
  boundaryFreeCarrierConnected_source_of_actualBoundaryRows
    (C := C) (inputs := inputs) actualRows (Classical.choice localSource)

/-- Endpoint-incident row variant of the boundary-free/carrier-connected
package.  This is often the most input-facing local reducer: endpoint rows
erase to `BoundaryFreeNoThirdGermSource`, while actual-boundary rows provide
carrier connectedness for that same source. -/
noncomputable def
    boundaryFreeCarrierConnected_source_of_actualBoundaryRows_endpointIncidentRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (endpointRows : BoundaryFreeEndpointIncidentSourceRows inputs) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        (unboundedFrontierCarrierGraph C inputs).Connected) :=
  boundaryFreeCarrierConnected_source_of_actualBoundaryRows
    (C := C) (inputs := inputs) actualRows
    endpointRows.toBoundaryFreeNoThirdGermSource

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundaryfree-connected-raw-orbit-source-20260520c`,
actual carrier/local-sector reduction.

This is the write-scope handoff below the downstream connected raw-orbit
constructor: an honest face-dart exterior carrier supplies both the pointwise
local-sector rows and the component-topology rows, while the incident-germ
frontier-edge row upgrades those same selected carrier heads to the global
boundary-free no-third-germ source.  The output is exactly the pair of fields
that the seeded raw-orbit layer combines with its raw dart-frontier source;
no adjacent-endpoint chord classification, induced frontier graph, arbitrary
cycle, or synthetic enclosure is introduced. -/
noncomputable def
    boundaryFreeLocalComponentRows_of_faceDartOrbitExteriorCarrierRows_incidentGermFrontierEdge_20260520c
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (carrierRows : FaceDartOrbitExteriorCarrierRows C inputs)
    (incident_germ_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε →
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
            (canonicalGraph C).Adj a.1 x →
              q ∈ vertexIncidentGermW3 C a.1 x ε →
                q ≠ (canonicalGraph C).point a.1 →
                  (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                    (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        UnboundedExteriorFrontierComponentTopologySourceRows inputs) :=
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    carrierRows.toLocalSectorRowsAt
  let localSource : BoundaryFreeNoThirdGermSource inputs :=
    boundaryFreeNoThirdGermSource_of_localSectorRows_incidentGermFrontierEdge
      (C := C) (inputs := inputs) localSectorRows
      incident_germ_frontier_edge
  ⟨localSource,
    componentTopologySourceRows_of_faceDartOrbitExteriorCarrierRows
      (C := C) (inputs := inputs) carrierRows⟩

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundaryfree-connected-raw-source-20260520d`,
local/component projection.

The current downstream connected raw-orbit package needs the same
boundary-free local source together with connectedness of the concrete
unbounded-frontier carrier.  A packaged local/component row is enough:
component topology supplies connectedness, while the subtype preserves the
exact local source that will be paired with the raw dart-frontier row in the
seeded raw-orbit layer. -/
noncomputable def
    boundaryFreeCarrierConnected_source_of_localComponentRows_20260520d
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localComponentRows :
      Subtype
        (fun _ : BoundaryFreeNoThirdGermSource inputs =>
          UnboundedExteriorFrontierComponentTopologySourceRows inputs)) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        (unboundedFrontierCarrierGraph C inputs).Connected) :=
  ⟨localComponentRows.1,
    unboundedFrontierCarrierGraph_connected_of_componentTopologySourceRows
      inputs localComponentRows.2⟩

set_option linter.style.longLine false in
/-- Carrier-connected projection of
`boundaryFreeLocalComponentRows_of_faceDartOrbitExteriorCarrierRows_incidentGermFrontierEdge_20260520c`.

This is the exact local/connected pair needed before the raw dart-frontier row
is supplied by the seeded raw-orbit owner. -/
noncomputable def
    boundaryFreeCarrierConnected_source_of_faceDartOrbitExteriorCarrierRows_incidentGermFrontierEdge_20260520c
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (carrierRows : FaceDartOrbitExteriorCarrierRows C inputs)
    (incident_germ_frontier_edge :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε →
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
            (canonicalGraph C).Adj a.1 x →
              q ∈ vertexIncidentGermW3 C a.1 x ε →
                q ≠ (canonicalGraph C).point a.1 →
                  (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                    (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        (unboundedFrontierCarrierGraph C inputs).Connected) := by
  exact
    boundaryFreeCarrierConnected_source_of_localComponentRows_20260520d
      (C := C) (inputs := inputs)
      (boundaryFreeLocalComponentRows_of_faceDartOrbitExteriorCarrierRows_incidentGermFrontierEdge_20260520c
        (C := C) (inputs := inputs) carrierRows incident_germ_frontier_edge)

set_option linter.style.longLine false in
/-- Family-level local/component handoff for claim
`S2-agent-boundaryfree-connected-raw-orbit-source-20260520c`. -/
noncomputable def
    boundaryFreeLocalComponentRows_family_of_faceDartOrbitExteriorCarrierRows_incidentGermFrontierEdge_20260520c
    (carrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FaceDartOrbitExteriorCarrierRows C inputs)
    (incident_germ_frontier_edge :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin m),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε →
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior →
                (canonicalGraph C).Adj a.1 x →
                  q ∈ vertexIncidentGermW3 C a.1 x ε →
                    q ≠ (canonicalGraph C).point a.1 →
                      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Subtype
          (fun _ : BoundaryFreeNoThirdGermSource inputs =>
            UnboundedExteriorFrontierComponentTopologySourceRows inputs) := by
  intro m C inputs
  exact
    boundaryFreeLocalComponentRows_of_faceDartOrbitExteriorCarrierRows_incidentGermFrontierEdge_20260520c
      (C := C) (inputs := inputs) (carrierRows C inputs)
      (incident_germ_frontier_edge C inputs)

set_option linter.style.longLine false in
/-- Family form of
`boundaryFreeCarrierConnected_source_of_localComponentRows_20260520d`. -/
noncomputable def
    boundaryFreeCarrierConnected_source_family_of_localComponentRows_20260520d
    (localComponentRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Subtype
            (fun _ : BoundaryFreeNoThirdGermSource inputs =>
              UnboundedExteriorFrontierComponentTopologySourceRows inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Subtype
          (fun _ : BoundaryFreeNoThirdGermSource inputs =>
            (unboundedFrontierCarrierGraph C inputs).Connected) := by
  intro m C inputs
  exact
    boundaryFreeCarrierConnected_source_of_localComponentRows_20260520d
      (C := C) (inputs := inputs) (localComponentRows C inputs)

set_option linter.style.longLine false in
/-- Raw-coverage/local-component packaging for the same 20260520d handoff.

When the raw-orbit layer has already supplied a selected raw coverage row, the
local/component package preserves the matching boundary-free local source as
the only local input needed by the raw-coverage erasers.  This is the
import-safe upstream form of the connected raw-orbit source cut: this file
owns raw coverage and local/component rows, while the seeded raw-orbit file
owns `RawOrbitDartEdgeFrontierSource` and
`BoundaryFreeConnectedRawOrbitSourceRows`. -/
def rawCoverage_boundaryFreeRows_of_rawCoverage_localComponentRows_20260520d
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localComponentRows :
      Subtype
        (fun _ : BoundaryFreeNoThirdGermSource inputs =>
          UnboundedExteriorFrontierComponentTopologySourceRows inputs)) :
    RawOrbitCoverageSourceRows (inputs := inputs) O ∧
      Nonempty (BoundaryFreeNoThirdGermSource inputs) :=
  ⟨coverage, ⟨localComponentRows.1⟩⟩

set_option linter.style.longLine false in
/-- Claim `S2-q18-dart-edge-frontier-source`.

Selected unbounded-frontier edge local rows supply the start dart's whole
open-segment frontier row.  A one-step geometric `faceSucc` propagation
callback then gives the q17 primitive for every dart in the selected raw
geometric face-successor orbit, using the existing pure orbit induction and no
completed boundary cycle. -/
theorem S2_q18_dart_edge_openSegment_frontier_of_selectedEdgeLocalRows_faceSuccPropagation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {e : PlanarInterface.Edge n}
    {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (faceSucc_preserves_openSegment_frontier :
      forall d : UnitDistanceDart C,
        (forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point d.tail)
            ((canonicalGraph C).point d.head) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) ->
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point
              ((geometricUnitDistanceRotationSystem C).faceSucc d).tail)
            ((canonicalGraph C).point
              ((geometricUnitDistanceRotationSystem C).faceSucc d).head) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) :
    forall k : Fin O.period,
      forall q : PlanarInterface.Point,
        PlanarInterface.InOpenSegment q
          ((canonicalGraph C).point (O.dart k).tail)
          ((canonicalGraph C).point (O.dart k).head) ->
        q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior := by
  let start_openSegment_frontier :
      forall q : PlanarInterface.Point,
        PlanarInterface.InOpenSegment q
          ((canonicalGraph C).point start.tail)
          ((canonicalGraph C).point start.head) ->
        q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior := by
    intro q hq
    have hcarrier :
        e ∈ unboundedFrontierEdgeSet C inputs :=
      interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
        edgeRows.edge_mem edgeRows.center_in_openSegment
        edgeRows.center_frontier
    have hq_edge :
        PlanarInterface.InOpenSegment q
          ((canonicalGraph C).point e.1)
          ((canonicalGraph C).point e.2) := by
      simpa [htail, hhead] using hq
    exact (mem_unboundedFrontierEdgeSet_iff.1 hcarrier).2 q hq_edge
  exact
    rawFaceSuccOrbit_dart_edge_openSegment_frontier_of_start_and_faceSucc_step
      (C := C) (inputs := inputs)
      (R := geometricUnitDistanceRotationSystem C) (start := start) O
      start_openSegment_frontier
      faceSucc_preserves_openSegment_frontier

/-- Raw-coverage reducer for the boundary-free/carrier-connected package.

Raw orbit coverage first gives the already checked actual-boundary rows, and
the actual-boundary reducer above then supplies carrier connectedness. -/
noncomputable def
    boundaryFreeCarrierConnected_source_of_rawCoverage_boundaryFreeSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : BoundaryFreeNoThirdGermSource inputs) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        (unboundedFrontierCarrierGraph C inputs).Connected) :=
  boundaryFreeCarrierConnected_source_of_actualBoundaryRows
    (C := C) (inputs := inputs)
    (actualBoundaryCycleRows_of_rawCoverage_boundaryFreeSource
      (C := C) (inputs := inputs) O coverage localSource)
    localSource

/-- Nonempty local-source variant of the raw-coverage reducer. -/
noncomputable def
    boundaryFreeCarrierConnected_source_of_rawCoverage_boundaryFreeSource_nonempty
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (coverage : RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localSource : Nonempty (BoundaryFreeNoThirdGermSource inputs)) :
    Subtype
      (fun _ : BoundaryFreeNoThirdGermSource inputs =>
        (unboundedFrontierCarrierGraph C inputs).Connected) :=
  boundaryFreeCarrierConnected_source_of_rawCoverage_boundaryFreeSource
    (C := C) (inputs := inputs) O coverage (Classical.choice localSource)

/-- Family-level eraser from the already checked raw-coverage plus nonempty
boundary-free source row family to the exact pair used by the selected
actual-arc route. -/
noncomputable def
    boundaryFreeCarrierConnected_source_family_of_rawCoverage_boundaryFreeSource
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                RawOrbitCoverageSourceRows (inputs := inputs) O ∧
                  Nonempty (BoundaryFreeNoThirdGermSource inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Subtype
          (fun _ : BoundaryFreeNoThirdGermSource inputs =>
            (unboundedFrontierCarrierGraph C inputs).Connected) :=
  fun C inputs =>
    let hR := rows C inputs
    let R : UnitDistanceRotationSystem C := Classical.choose hR
    let hstart := Classical.choose_spec hR
    let start : UnitDistanceDart C := Classical.choose hstart
    let hO := Classical.choose_spec hstart
    let O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start :=
      Classical.choose hO
    let hrows := Classical.choose_spec hO
    boundaryFreeCarrierConnected_source_of_rawCoverage_boundaryFreeSource_nonempty
      (C := C) (inputs := inputs) O hrows.1 hrows.2

end ExteriorComponentTopology
end Swanepoel
end ErdosProblems1066
