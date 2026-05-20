import ErdosProblems1066.Swanepoel.ExteriorComponentTopology

set_option autoImplicit false

/-!
# Local two-germ S2 assembly

This file keeps source-facing S2 reducers that consume the boundary-free
local two-germ row out of the main exterior-component topology file.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace S2LocalTwoGermAssembly

open JordanTopologyFactsConcrete
open JordanTopologyFactsConcrete.MinimalFailureTopology
open ExteriorComponentTopology
open FinitePlaneDrawing

noncomputable section

variable {n : Nat}

/-- Boundary-free selected-edge/no-third-germ rows give the pointwise local
two-germ family used by S2.

This is the input-facing local source: it uses the local star isolation already
packaged in `unboundedFrontierCarrierLocalTwoGermRowsAt_of_no_third_germ` and
does not assume a downstream boundary cycle. -/
noncomputable def localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun left : Fin n =>
          Exists fun right : Fin n =>
            ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                  (canonicalGraph C).Adj a.1 x ->
                    q ∈ vertexIncidentGermW3 C a.1 x ε ->
                      q ≠ (canonicalGraph C).point a.1 ->
                        x ≠ left ->
                          x ≠ right ->
                            False) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  classical
  intro a
  let left : Fin n := Classical.choose (source a)
  let right : Fin n := Classical.choose (Classical.choose_spec (source a))
  have hsource :
      ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
        ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
        left ≠ right ∧
        forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
          q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
              (canonicalGraph C).Adj a.1 x ->
                q ∈ vertexIncidentGermW3 C a.1 x ε ->
                  q ≠ (canonicalGraph C).point a.1 ->
                    x ≠ left ->
                      x ≠ right ->
                        False :=
    Classical.choose_spec (Classical.choose_spec (source a))
  exact
    unboundedFrontierCarrierLocalTwoGermRowsAt_of_no_third_germ
      hsource.1 hsource.2.1 hsource.2.2.1 hsource.2.2.2

/-- A concrete two-regular unbounded-frontier carrier supplies the pointwise
local-sector rows by taking the two neighbours in the actual carrier graph. -/
noncomputable def localSectorRows_of_unboundedFrontierCarrierGraph_degree_two
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  classical
  let G := unboundedFrontierCarrierGraph C inputs
  intro a
  have hcard : (G.neighborFinset a).card = 2 := by
    simpa [G] using hdegree a
  have hpair_exists := Finset.card_eq_two.mp hcard
  let leftB := Classical.choose hpair_exists
  let rightB := Classical.choose (Classical.choose_spec hpair_exists)
  have hpair_spec :
      leftB ≠ rightB ∧ G.neighborFinset a = {leftB, rightB} :=
    Classical.choose_spec (Classical.choose_spec hpair_exists)
  have hsub_ne : leftB ≠ rightB := hpair_spec.1
  have hpair : G.neighborFinset a = {leftB, rightB} := hpair_spec.2
  have hleft_adj : G.Adj a leftB := by
    have hmem : leftB ∈ G.neighborFinset a := by
      rw [hpair]
      simp
    simpa [SimpleGraph.mem_neighborFinset] using hmem
  have hright_adj : G.Adj a rightB := by
    have hmem : rightB ∈ G.neighborFinset a := by
      rw [hpair]
      simp
    simpa [SimpleGraph.mem_neighborFinset] using hmem
  refine
    { left := leftB.1
      right := rightB.1
      left_edge := ?_
      right_edge := ?_
      heads_ne := ?_
      only := ?_ }
  · exact (unboundedFrontierCarrierGraph_adj_iff).1 (by simpa [G] using hleft_adj)
  · exact (unboundedFrontierCarrierGraph_adj_iff).1 (by simpa [G] using hright_adj)
  · intro hheads
    apply hsub_ne
    apply Subtype.ext
    exact hheads
  · intro b hb
    have hbmem : b ∈ G.neighborFinset a := by
      simpa [G, SimpleGraph.mem_neighborFinset] using hb
    have hbpair : b = leftB ∨ b = rightB := by
      simpa [hpair] using hbmem
    rcases hbpair with hb_left | hb_right
    · left
      exact congrArg Subtype.val hb_left
    · right
      exact congrArg Subtype.val hb_right

/-- Convert the concrete carrier's ordinary `SimpleGraph.degree = 2` row into
the `neighborFinset.card = 2` source consumed by
`localSectorRows_of_unboundedFrontierCarrierGraph_degree_two`.

This is only finite-graph bookkeeping for the actual
`unboundedFrontierCarrierGraph`; it does not introduce a cycle row or replace
the carrier by an induced graph. -/
theorem unboundedFrontierCarrierGraph_neighborFinset_card_two_of_degree_two
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        @SimpleGraph.degree _
          (unboundedFrontierCarrierGraph C inputs) a
          ((unboundedFrontierCarrierGraph C inputs).neighborSetFintype a) =
            2) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
        2 := by
  intro a
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  exact hdegree a

/-- Explicit neighbour-pair rows prove that the actual concrete carrier has
exactly two neighbours at every unbounded-frontier vertex, in the precise
`neighborFinset.card = 2` form used by the local-sector constructor.

This is the smallest non-circular pointwise source left by this file: for each
frontier vertex, exhibit the two real carrier neighbours and prove every
carrier edge incident to the vertex goes to one of them. -/
theorem
    unboundedFrontierCarrierGraph_neighborFinset_card_two_of_neighborPairRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (rows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
        2 :=
  unboundedFrontierCarrierGraph_neighborFinset_card_two_of_degree_two
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierGraph_degree_two_of_neighborPairRows
      inputs rows)

/-- Simple-degree source form of the concrete-carrier local-sector handoff. -/
noncomputable def
    localSectorRows_of_unboundedFrontierCarrierGraph_simple_degree_two
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        @SimpleGraph.degree _
          (unboundedFrontierCarrierGraph C inputs) a
          ((unboundedFrontierCarrierGraph C inputs).neighborSetFintype a) =
            2) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_unboundedFrontierCarrierGraph_degree_two
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_degree_two
      (C := C) (inputs := inputs) hdegree)

/-- Neighbour-pair source form of the concrete-carrier local-sector handoff.

The proof deliberately factors through
`localSectorRows_of_unboundedFrontierCarrierGraph_degree_two`, so downstream
users can target the honest carrier-neighbour statement instead of restating
the local-sector row. -/
noncomputable def localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (rows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_unboundedFrontierCarrierGraph_degree_two
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_neighborPairRows
      (C := C) inputs rows)

/-- Input-facing neighbour-pair handoff with decidability discharged by the
actual concrete carrier graph. -/
noncomputable def
    localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (rows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows
      (C := C) inputs rows

/-- Carrier local-sector rows give the pointwise local two-germ rows by
shrinking to the local vertex-star isolation ball.

The two germs are the actual carrier neighbours already selected by the
local-sector row.  Any noncenter nearby frontier point lies in the open
segment of an incident canonical edge; the pointwise frontier-edge carrier
membership source turns that edge into a carrier edge, so `only` rules out
every third head. -/
noncomputable def localTwoGermRows_of_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  classical
  intro a
  let sector := rows a
  refine
    { left := sector.left
      right := sector.right
      left_edge := sector.left_edge
      right_edge := sector.right_edge
      heads_ne := sector.heads_ne
      local_two_germ := ?_ }
  rcases
      exists_ball_forall_unboundedExterior_frontier_mem_incident_inOpenSegment_of_vertex_ne
        C inputs a.1 with
    ⟨ε, hεpos, hstar⟩
  refine ⟨ε, hεpos, ?_⟩
  intro q hqball hqfrontier
  by_cases hcenter : q = (canonicalGraph C).point a.1
  · left
    rw [hcenter]
    exact ⟨by simpa [Metric.mem_ball] using hεpos, left_mem_closedSegment _ _⟩
  · rcases hstar q hqball hcenter hqfrontier with ⟨x, hadj, hqopen⟩
    have hsource :
        InteriorFrontierEdgeCarrierMembershipSource C inputs :=
      interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
    have hx_only : x = sector.left ∨ x = sector.right := by
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
        simpa [b, sector] using (sector.only b hadjCarrier)
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
        simpa [b, sector] using (sector.only b hadjCarrier)
    rcases hx_only with hx_left | hx_right
    · left
      exact
        ⟨hqball,
          by simpa [hx_left, sector] using inOpenSegment_mem_closedSegment hqopen⟩
    · right
      exact
        ⟨hqball,
          by simpa [hx_right, sector] using inOpenSegment_mem_closedSegment hqopen⟩

/-- Claim `S2-agent-co-local-two-germ-source-20260520co`.

Checked source reduction for the pointwise local two-germ family from the
completed local-sector/geometric-order rows.  This composes the co-worker
local-sector source with the local vertex-star two-germ contraction in this
file; it does not assume boundary-cycle completeness. -/
noncomputable def S2_agent_co_local_two_germ_source_20260520co
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_edge_openSegment_frontier :
      forall k : Fin B.length,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (B.vertex k))
            ((canonicalGraph C).point
              (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (geometric_order :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C B k)
    (local_exterior_sector :
      forall (k : Fin B.length) (eps : Real) (q : PlanarInterface.Point)
          (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) eps ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj (B.vertex k) x ->
              q ∈ vertexIncidentGermW3 C (B.vertex k) x eps ->
                q ≠ (canonicalGraph C).point (B.vertex k) ->
                x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
                  x ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
                    BoundaryPredSuccPointAngularBetween C B k q) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
  localTwoGermRows_of_localSectorRows
    (S2_agent_co_local_sector_source_20260520co
      (C := C) (inputs := inputs) B
      frontier_iff_cycle_vertex
      cycle_edge_openSegment_frontier
      geometric_order
      local_exterior_sector)

/-- Input-facing neighbour-pair handoff for the local two-germ rows.

This is the local analogue of
`localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source`:
the honest pointwise neighbour-pair rows first give the local-sector rows,
and the vertex-star isolation reducer then turns those into the two-germ
frontier source. -/
noncomputable def
    localTwoGermRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (rows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
  localTwoGermRows_of_localSectorRows
    (localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
      (C := C) inputs rows)

/-- Component-topology rows plus pointwise neighbour-pair rows package the
three local outputs used by the S2 source route.

The component rows prove connectedness of the actual unbounded-frontier carrier
graph.  The neighbour-pair rows independently give the pointwise local-sector
family, and therefore the pointwise local two-germ family, without asking
downstream consumers to repeat those erasures. -/
noncomputable def
    componentTopologyLocalSectorTwoGermRows_of_neighborPairRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (componentTopologyRows :
      UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    And
      ((unboundedFrontierCarrierGraph C inputs).Connected)
      (Nonempty
        ((forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a) ×
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a))) := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
      (C := C) inputs neighborRows
  let localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
    localTwoGermRows_of_localSectorRows localSectorRows
  exact
    ⟨unboundedFrontierCarrierGraph_connected_of_componentTopologySourceRows
        inputs componentTopologyRows,
      ⟨localSectorRows, localTwoGermRows⟩⟩

/-- A concrete two-regular unbounded-frontier carrier gives the pointwise
local two-germ rows after local drawing isolation. -/
noncomputable def localTwoGermRows_of_unboundedFrontierCarrierGraph_degree_two
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
  localTwoGermRows_of_localSectorRows
    (localSectorRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs) hdegree)

/-- Frontier preconnectedness plus a concrete two-regular carrier row proves
connectedness of the actual unbounded-frontier carrier graph.

The degree hypothesis is kept in the current `neighborFinset.card = 2` form;
the only pointwise local input used by the connectedness reducer is the
local-sector row extracted from that concrete neighbour shape. -/
theorem frontier_cover_to_connected_carrier_of_frontier_edge_point_degree_two
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  S2_agent_frontier_cover_to_connected_carrier_integration_of_frontier_edge_point
    inputs frontier_preconnected
    (localSectorRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs) hdegree)

/-- Concrete carrier degree two, together with frontier preconnectedness,
produces cyclic coverage rows for the actual unbounded-frontier carrier.

This packages the non-circular graph output of the degree-two route: a cyclic
coverage row for the concrete carrier and no boundary-cycle input. -/
noncomputable def
    unboundedFrontierCarrierCyclicCoverageRows_of_frontierPreconnectedCarrierGraph_degree_two
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2) :
    UnboundedFrontierCarrierCyclicCoverageRows C inputs :=
  unboundedFrontierCarrierCyclicCoverageRows_of_connected_localSectorRows
    inputs
    (frontier_cover_to_connected_carrier_of_frontier_edge_point_degree_two
      (C := C) (inputs := inputs) frontier_preconnected hdegree)
    (localSectorRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs) hdegree)

/-- Pair form of the degree-two carrier handoff expected by the existing
cyclic-coverage/local-sector exterior reducer. -/
noncomputable def
    cyclicCoverageLocalSectorRows_of_frontierPreconnectedCarrierGraph_degree_two
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2) :
    Nonempty
      (UnboundedFrontierCarrierCyclicCoverageRows C inputs ×
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a)) := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs) hdegree
  let carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected :=
    S2_agent_frontier_cover_to_connected_carrier_integration_of_frontier_edge_point
      inputs frontier_preconnected localSectorRows
  exact
    ⟨⟨unboundedFrontierCarrierCyclicCoverageRows_of_connected_localSectorRows
        inputs carrier_connected localSectorRows,
      localSectorRows⟩⟩

/-- Pointwise exterior-cycle reducer from frontier preconnectedness and the
concrete `neighborFinset.card = 2` carrier row.

The proof factors through the already-owned cyclic-coverage/local-sector
handoff, so the degree-two route does not assume any final boundary cycle
rows. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_frontierPreconnectedCarrierGraph_degree_two
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_pointwise_cyclicCoverageLocalSectorRows
    inputs
    (cyclicCoverageLocalSectorRows_of_frontierPreconnectedCarrierGraph_degree_two
      (C := C) (inputs := inputs) frontier_preconnected hdegree)

/-- Boundary-free selected-edge/no-third-germ rows give the pointwise
local-sector family consumed by the carrier and raw-orbit S2 reducers. -/
noncomputable def localSectorRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun left : Fin n =>
          Exists fun right : Fin n =>
            ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                  (canonicalGraph C).Adj a.1 x ->
                    q ∈ vertexIncidentGermW3 C a.1 x ε ->
                      q ≠ (canonicalGraph C).point a.1 ->
                        x ≠ left ->
                          x ≠ right ->
                            False) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_localTwoGermRows
    (localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
      (C := C) (inputs := inputs) source)

/-- Boundary-free selected-edge/no-third-germ rows fill the explicit local
Boolean side-separation package for the deleted-neighbour route.

This factors through the genuine local-sector eraser: once every concrete
carrier neighbour is one of the two selected heads, every requested
third-neighbour side-separation row is vacuous. -/
noncomputable def
    deletedNeighborLocalSeparationInputSource_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun left : Fin n =>
          Exists fun right : Fin n =>
            ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                  (canonicalGraph C).Adj a.1 x ->
                    q ∈ vertexIncidentGermW3 C a.1 x ε ->
                      q ≠ (canonicalGraph C).point a.1 ->
                        x ≠ left ->
                          x ≠ right ->
                            False) :
    UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
      C inputs :=
  unboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource_of_localSectorRows
    (localSectorRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
      (C := C) (inputs := inputs) source)

/-- Claim `S2-dyn-20260520-deleted-neighbor-local-separation-source`.

S2Local form of the local Boolean side-separation source.  The remaining
input is precisely the boundary-free two-selected-edge/no-third-germ family,
and the Boolean deleted-neighbour package is obtained by local erasure. -/
noncomputable def
    S2_dyn_20260520_deleted_neighbor_local_separation_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun left : Fin n =>
          Exists fun right : Fin n =>
            ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                  (canonicalGraph C).Adj a.1 x ->
                    q ∈ vertexIncidentGermW3 C a.1 x ε ->
                      q ≠ (canonicalGraph C).point a.1 ->
                        x ≠ left ->
                          x ≠ right ->
                            False) :
    UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
      C inputs :=
  deletedNeighborLocalSeparationInputSource_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-actual-carrier-degree-two-final-source`.

Boundary-free two-selected-edge/no-third-germ rows strictly reduce the current
actual-carrier two-regularity source.  The proof goes through the checked
deleted-neighbour local-separation package for the same concrete
`unboundedFrontierEdgeSet` carrier, then uses the actual carrier graph's
neighbour-finset degree reducer. -/
theorem
    S2_codex_current_20260520_actual_carrier_degree_two_final_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun left : Fin n =>
          Exists fun right : Fin n =>
            ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                  (canonicalGraph C).Adj a.1 x ->
                    q ∈ vertexIncidentGermW3 C a.1 x ε ->
                      q ≠ (canonicalGraph C).point a.1 ->
                        x ≠ left ->
                          x ≠ right ->
                            False) :
    letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
      unboundedFrontierCarrierGraph_decidableAdj C inputs
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
        2 := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    unboundedFrontierCarrierGraph_neighborFinset_card_two_of_deletedNeighborLocalSeparationInputSource
      (C := C) inputs
      (deletedNeighborLocalSeparationInputSource_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
        (C := C) (inputs := inputs) source)

/-- Claim `S2-dyn-20260520-local-sector-source-at-frontier-vertex`.

Strict pointwise reduction of the local-sector family to a local-radius
selected-edge source at each actual unbounded-frontier carrier vertex.  For
each `a`, the source names two real incident `unboundedFrontierEdgeSet` edges
and gives a neighbourhood in which no nearby frontier point in an incident
germ can be carried by a third head.  The proof shrinks that neighbourhood by
the standard local vertex-star radius and then uses the checked local two-germ
to local-sector eraser. -/
noncomputable def
    S2_dyn_20260520_local_sector_source_at_frontier_vertex
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun left : Fin n =>
          Exists fun right : Fin n =>
            ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            Exists fun radius : Real =>
              0 < radius ∧
              forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
                q ∈ Metric.ball ((canonicalGraph C).point a.1) radius ->
                  q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                    q ∈ frontier
                        (unboundedExteriorComponentRows C inputs).exterior ->
                      (canonicalGraph C).Adj a.1 x ->
                        q ∈ vertexIncidentGermW3 C a.1 x ε ->
                          q ≠ (canonicalGraph C).point a.1 ->
                            x ≠ left ->
                              x ≠ right ->
                                False) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_localTwoGermRows
    (by
      classical
      intro a
      let left : Fin n := Classical.choose (source a)
      let right : Fin n :=
        Classical.choose (Classical.choose_spec (source a))
      have hsource :
          ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            Exists fun radius : Real =>
              0 < radius ∧
              forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
                q ∈ Metric.ball ((canonicalGraph C).point a.1) radius ->
                  q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                    q ∈ frontier
                        (unboundedExteriorComponentRows C inputs).exterior ->
                      (canonicalGraph C).Adj a.1 x ->
                        q ∈ vertexIncidentGermW3 C a.1 x ε ->
                          q ≠ (canonicalGraph C).point a.1 ->
                            x ≠ left ->
                              x ≠ right ->
                                False :=
        Classical.choose_spec (Classical.choose_spec (source a))
      let radius : Real := Classical.choose hsource.2.2.2
      have hradiusSpec :
          0 < radius ∧
            forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) radius ->
                q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                  q ∈ frontier
                      (unboundedExteriorComponentRows C inputs).exterior ->
                    (canonicalGraph C).Adj a.1 x ->
                      q ∈ vertexIncidentGermW3 C a.1 x ε ->
                        q ≠ (canonicalGraph C).point a.1 ->
                          x ≠ left ->
                            x ≠ right ->
                              False :=
        Classical.choose_spec hsource.2.2.2
      let starRadius : Real :=
        Classical.choose
          (exists_ball_forall_unboundedExterior_frontier_mem_vertexIncidentGermW3
            C inputs a.1)
      have hstarSpec :
          0 < starRadius ∧
            ∀ q : PlanarInterface.Point,
              q ∈ Metric.ball ((canonicalGraph C).point a.1) starRadius →
                q ∈ frontier
                    (unboundedExteriorComponentRows C inputs).exterior →
                  Exists fun x : Fin n =>
                    (canonicalGraph C).Adj a.1 x ∧
                      q ∈ vertexIncidentGermW3 C a.1 x starRadius :=
        Classical.choose_spec
          (exists_ball_forall_unboundedExterior_frontier_mem_vertexIncidentGermW3
            C inputs a.1)
      let outputRadius : Real := min radius starRadius
      have houtput_pos : 0 < outputRadius := by
        exact lt_min hradiusSpec.1 hstarSpec.1
      refine
        { left := left
          right := right
          left_edge := hsource.1
          right_edge := hsource.2.1
          heads_ne := hsource.2.2.1
          local_two_germ := ?_ }
      refine ⟨outputRadius, houtput_pos, ?_⟩
      intro q hqball hqfrontier
      by_cases hqcenter : q = (canonicalGraph C).point a.1
      · left
        rw [hqcenter]
        exact
          ⟨by simpa [Metric.mem_ball] using houtput_pos,
            left_mem_closedSegment _ _⟩
      have hqstar :
          q ∈ Metric.ball ((canonicalGraph C).point a.1) starRadius := by
        rw [Metric.mem_ball] at hqball ⊢
        exact lt_of_lt_of_le hqball (by simp [outputRadius])
      have hqlocal :
          q ∈ Metric.ball ((canonicalGraph C).point a.1) radius := by
        rw [Metric.mem_ball] at hqball ⊢
        exact lt_of_lt_of_le hqball (by simp [outputRadius])
      rcases hstarSpec.2 q hqstar hqfrontier with ⟨x, hadj, hgerm⟩
      by_cases hx_left : x = left
      · left
        rcases hgerm with ⟨_hgerm_ball, hgerm_segment⟩
        exact ⟨hqball, by simpa [hx_left] using hgerm_segment⟩
      by_cases hx_right : x = right
      · right
        rcases hgerm with ⟨_hgerm_ball, hgerm_segment⟩
        exact ⟨hqball, by simpa [hx_right] using hgerm_segment⟩
      exact False.elim
        (hradiusSpec.2 starRadius q x hqlocal hqstar hqfrontier
          hadj hgerm hqcenter hx_left hx_right))

/-- Structured form of the local-radius selected-edge source.

At every actual unbounded-frontier carrier vertex it names two distinct
incident selected `unboundedFrontierEdgeSet` heads and a positive radius on
which no nearby frontier point in an incident germ is carried by a third head.
This is the explicit residual feeding
`S2_dyn_20260520_local_sector_source_at_frontier_vertex`. -/
structure LocalRadiusSelectedEdgeSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  left :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Fin n
  right :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Fin n
  left_edge :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs
  right_edge :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs
  heads_ne :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      left a ≠ right a
  radius :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Real
  radius_pos :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      0 < radius a
  local_no_third_germ :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
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

namespace LocalRadiusSelectedEdgeSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- Forget the structured local-radius source to the pointwise existential
source consumed by
`S2_dyn_20260520_local_sector_source_at_frontier_vertex`. -/
def toExistsSource
    (source : LocalRadiusSelectedEdgeSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Exists fun left : Fin n =>
        Exists fun right : Fin n =>
          ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
            (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
          ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
            (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
          left ≠ right ∧
          Exists fun radius : Real =>
            0 < radius ∧
            forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) radius →
                q ∈ Metric.ball ((canonicalGraph C).point a.1) ε →
                  q ∈ frontier
                      (unboundedExteriorComponentRows C inputs).exterior →
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
      ⟨source.radius a, source.radius_pos a,
        source.local_no_third_germ a⟩⟩

/-- Local-radius selected-edge rows erase to the carrier local-sector rows. -/
noncomputable def toLocalSectorRows
    (source : LocalRadiusSelectedEdgeSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2_dyn_20260520_local_sector_source_at_frontier_vertex
    (C := C) (inputs := inputs) source.toExistsSource

/-- Local-radius selected-edge rows also fill the sharp cut-partition input
source.  The third-neighbour branch is discharged only after the existing
local-star-to-sector eraser proves every concrete carrier neighbour is one of
the two selected `unboundedFrontierEdgeSet` heads. -/
noncomputable def toNeighborPairCutPartitionInputSource
    (source : LocalRadiusSelectedEdgeSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  unboundedFrontierCarrierNeighborPairCutPartitionInputSource_of_localSectorRows
    (C := C) (inputs := inputs) source.toLocalSectorRows

end LocalRadiusSelectedEdgeSourceRows

/-- Claim `S2-dyn-20260520-local-radius-selected-edge-source`.

The structured local-radius selected-edge source is exactly enough to feed the
pointwise local-sector reducer.  The remaining source is still pointwise and
local: choose the two actual incident `unboundedFrontierEdgeSet` edges and the
positive no-third-germ radius at each frontier vertex. -/
noncomputable def S2_dyn_20260520_local_radius_selected_edge_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalRadiusSelectedEdgeSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  source.toLocalSectorRows

set_option linter.style.longLine false in
/-- Claim `S2-codex-cont-20260520-carrier-degree-cutpartition-source`.

The honest selected exterior-star/local-radius source closes the sharp
cut-partition input source for the actual unbounded-frontier carrier.  The
two selected heads are the genuine `unboundedFrontierEdgeSet` incidences from
the local source; the local no-third-germ row is first erased to the concrete
local-sector `only` row, so any third carrier-neighbour branch is impossible.
-/
noncomputable def
    S2_codex_cont_20260520_carrier_degree_cutpartition_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalRadiusSelectedEdgeSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  source.toNeighborPairCutPartitionInputSource

set_option linter.style.longLine false in
/-- Claim `S2-codex-cont-20260520-carrier-degree-cutpartition-source`,
deleted-neighbour form.

The same local selected exterior-star rows also close
`UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource`: after
erasing to local-sector rows, a requested third carrier neighbour contradicts
the actual carrier `only` field before any ambient deleted-graph path can be
used. -/
noncomputable def
    S2_codex_cont_20260520_carrier_degree_unreachableAfterDelete_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalRadiusSelectedEdgeSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  unboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource_of_localSectorRows
    (C := C) (inputs := inputs)
    (source.toLocalSectorRows)

set_option linter.style.longLine false in
/-- Carrier degree-two consequence of the same local source.

This is the point where the existing no-cut eraser in
`FinitePlanarOuterComponentInputs.noCutVertex` is consumed: deleted-neighbour
rows erase to cut partitions, then to the exact neighbour-pair rows used by
the carrier degree calculation. -/
theorem S2_codex_cont_20260520_carrier_degree_two_of_local_radius_source
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (source : LocalRadiusSelectedEdgeSourceRows inputs) :
    letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
      unboundedFrontierCarrierGraph_decidableAdj C inputs
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
        2 := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    unboundedFrontierCarrierGraph_neighborFinset_card_two_of_unreachableAfterDeleteInputSource
      (C := C) inputs
      (S2_codex_cont_20260520_carrier_degree_unreachableAfterDelete_source
        (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Local closed-germ membership promotes to an actual selected frontier edge.

This is the bare-input local-star fact behind the local two-germ source: after
shrinking to the graph-vertex isolation radius at `a`, a noncenter point of the
unbounded exterior frontier lying in an incident W3 germ cannot be the far
endpoint of a different graph edge.  The remaining relative-interior branch is
promoted by the checked interior-frontier carrier-membership row. -/
theorem unboundedFrontierEdgeSet_or_symm_of_local_incident_frontier_germ
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
    (ε : Real) (q : PlanarInterface.Point) (x : Fin n)
    (hqradius :
      q ∈ Metric.ball ((canonicalGraph C).point a.1)
        (Classical.choose
          (exists_ball_forall_graph_vertex_eq_of_mem_ball (C := C) a.1)))
    (_hqeps : q ∈ Metric.ball ((canonicalGraph C).point a.1) ε)
    (hqfrontier :
      q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (hadj : (canonicalGraph C).Adj a.1 x)
    (hgerm : q ∈ vertexIncidentGermW3 C a.1 x ε)
    (hqcenter : q ≠ (canonicalGraph C).point a.1) :
    (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
      (x, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
  have hvertexRadius :
      forall w : Fin n,
        (canonicalGraph C).point w ∈
            Metric.ball ((canonicalGraph C).point a.1)
              (Classical.choose
                (exists_ball_forall_graph_vertex_eq_of_mem_ball
                  (C := C) a.1)) ->
          w = a.1 :=
    (Classical.choose_spec
      (exists_ball_forall_graph_vertex_eq_of_mem_ball (C := C) a.1)).2
  rcases hgerm with ⟨_hgerm_ball, hqseg⟩
  rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hqseg with
    hq_left | hq_right | hq_open
  · exact False.elim (hqcenter hq_left)
  · have hx_eq_a : x = a.1 :=
      hvertexRadius x (by simpa [hq_right] using hqradius)
    exact False.elim
      ((canonical_adj_point_ne hadj) (by simp [hx_eq_a]))
  · have hsource : InteriorFrontierEdgeCarrierMembershipSource C inputs :=
      interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
    rcases hadj with hadj_forward | hadj_backward
    · exact Or.inl
        (hsource (e := (a.1, x)) (p := q)
          hadj_forward hq_open hqfrontier)
    · exact Or.inr
        (hsource (e := (x, a.1)) (p := q)
          hadj_backward (inOpenSegment_symm hq_open) hqfrontier)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-local-incident-germ-frontier-edge-membership`.

Bare `FinitePlanarOuterComponentInputs` already give the local drawing part of
the two-selected-edge source: a positive vertex-isolation radius at every
unbounded-frontier vertex such that every noncenter nearby frontier point in an
incident W3 germ lies on an actual selected `unboundedFrontierEdgeSet` edge. -/
theorem localIncidentGermFrontierEdgeMembershipRows_of_inputs
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    Exists fun radius :
        {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Real =>
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
                        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
  classical
  refine
    ⟨fun a =>
        Classical.choose
          (exists_ball_forall_graph_vertex_eq_of_mem_ball (C := C) a.1),
      ?_, ?_⟩
  · intro a
    exact
      (Classical.choose_spec
        (exists_ball_forall_graph_vertex_eq_of_mem_ball (C := C) a.1)).1
  · intro a ε q x hqradius hqeps hqfrontier hadj hgerm hqcenter
    exact
      unboundedFrontierEdgeSet_or_symm_of_local_incident_frontier_germ
        (C := C) (inputs := inputs) a ε q x hqradius hqeps hqfrontier
        hadj hgerm hqcenter

/-- Pure selected-edge source for the local-radius rows.

At every actual unbounded-frontier vertex it chooses two selected incident
`unboundedFrontierEdgeSet` heads and asserts that every other selected
incident head is one of those two.  The metric radius/no-third-germ part is
not part of this source; it is derived from finite drawing isolation below. -/
structure LocalSelectedIncidentEdgePairSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  left :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Fin n
  right :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Fin n
  left_edge :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs
  right_edge :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs
  heads_ne :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      left a ≠ right a
  only_selected_incident :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs →
        x = left a ∨ x = right a

set_option linter.style.longLine false in
/-- Direct eraser from selected incident-edge pairs to concrete carrier
neighbour-pair rows.

The source already states that every selected incident
`unboundedFrontierEdgeSet` edge at `a` has one of the two named heads.  Since
the concrete carrier adjacency is exactly selected-edge incidence up to
orientation, no local-radius or cut-partition detour is needed for this
bookkeeping step. -/
noncomputable def
    unboundedFrontierCarrierNeighborPairRows_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a := by
  classical
  intro a
  let hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  have hleft_mem :
      source.left a ∈ unboundedFrontierVertexSet C inputs := by
    rcases source.left_edge a with h | h
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).2
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).1
  have hright_mem :
      source.right a ∈ unboundedFrontierVertexSet C inputs := by
    rcases source.right_edge a with h | h
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).2
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).1
  let leftV : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨source.left a, hleft_mem⟩
  let rightV : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨source.right a, hright_mem⟩
  refine
    { left := leftV
      right := rightV
      left_ne_right := ?_
      neighbor_iff := ?_ }
  · intro h
    exact source.heads_ne a (congrArg Subtype.val h)
  · intro b
    constructor
    · intro hb
      have hedge :
          (a.1, b.1) ∈ unboundedFrontierEdgeSet C inputs ∨
            (b.1, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
        (unboundedFrontierCarrierGraph_adj_iff).1 hb
      rcases source.only_selected_incident a b.1 hedge with hb_left | hb_right
      · exact Or.inl (Subtype.ext (by simpa [leftV] using hb_left))
      · exact Or.inr (Subtype.ext (by simpa [rightV] using hb_right))
    · intro hb
      rcases hb with hb | hb
      · rw [hb]
        exact (unboundedFrontierCarrierGraph_adj_iff).2 (source.left_edge a)
      · rw [hb]
        exact (unboundedFrontierCarrierGraph_adj_iff).2 (source.right_edge a)

set_option linter.style.longLine false in
/-- Claim `S2-codex-main-20260520-selected-edge-pair-neighbor-eraser`.

Pointwise selected-edge-pair rows give the exact concrete carrier
neighbour-pair rows directly.  This keeps the local S2 source on actual
selected exterior-boundary edges and avoids the longer local-radius
cut-partition route when only carrier neighbour rows are needed. -/
noncomputable def
    S2_codex_main_20260520_selected_edge_pair_neighbor_eraser
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a :=
  unboundedFrontierCarrierNeighborPairRows_of_selectedIncidentEdgePairRows
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Actual carrier degree two supplies the pure selected incident-edge source.

This is the strict graph-theoretic residual for
`LocalSelectedIncidentEdgePairSourceRows`: at each actual unbounded-frontier
vertex, take the two neighbours of the concrete
`unboundedFrontierCarrierGraph`.  Since carrier adjacency is definitionally the
same as selected incident `unboundedFrontierEdgeSet` membership up to
orientation, every selected incident head is one of these two neighbours. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2) :
    LocalSelectedIncidentEdgePairSourceRows inputs := by
  classical
  let G := unboundedFrontierCarrierGraph C inputs
  let leftV :
      (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}) →
        {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    fun a => Classical.choose (Finset.card_eq_two.mp (hdegree a))
  let rightV :
      (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}) →
        {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    fun a =>
      Classical.choose
        (Classical.choose_spec (Finset.card_eq_two.mp (hdegree a)))
  have pairSpec :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        leftV a ≠ rightV a ∧
          G.neighborFinset a = {leftV a, rightV a} := by
    intro a
    exact
      Classical.choose_spec
        (Classical.choose_spec (Finset.card_eq_two.mp (hdegree a)))
  refine
    { left := fun a => (leftV a).1
      right := fun a => (rightV a).1
      left_edge := ?_
      right_edge := ?_
      heads_ne := ?_
      only_selected_incident := ?_ }
  · intro a
    have hmem : leftV a ∈ G.neighborFinset a := by
      rw [(pairSpec a).2]
      simp
    have hadj : G.Adj a (leftV a) := by
      simpa [G, SimpleGraph.mem_neighborFinset] using hmem
    exact (unboundedFrontierCarrierGraph_adj_iff).1 (by simpa [G] using hadj)
  · intro a
    have hmem : rightV a ∈ G.neighborFinset a := by
      rw [(pairSpec a).2]
      simp
    have hadj : G.Adj a (rightV a) := by
      simpa [G, SimpleGraph.mem_neighborFinset] using hmem
    exact (unboundedFrontierCarrierGraph_adj_iff).1 (by simpa [G] using hadj)
  · intro a hheads
    exact (pairSpec a).1 (Subtype.ext hheads)
  · intro a x hedge
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
    have hbAdj : G.Adj a b := by
      exact (unboundedFrontierCarrierGraph_adj_iff).2 hedge
    have hbmem : b ∈ G.neighborFinset a := by
      simpa [G, SimpleGraph.mem_neighborFinset] using hbAdj
    have hbpair : b = leftV a ∨ b = rightV a := by
      simpa [(pairSpec a).2] using hbmem
    rcases hbpair with hb_left | hb_right
    · left
      exact congrArg Subtype.val hb_left
    · right
      exact congrArg Subtype.val hb_right

set_option linter.style.longLine false in
/-- Selected incident-edge pair rows force concrete carrier degree two.

This is the reverse direction to
`localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two`.
It uses only the actual `unboundedFrontierCarrierGraph` adjacency/edge-set
equivalence and the selected-incident completeness field of
`LocalSelectedIncidentEdgePairSourceRows`; it does not pass through
neighbour-pair, local-selected, or geometric-selection packages. -/
theorem
    unboundedFrontierCarrierGraph_neighborFinset_card_two_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
        2 := by
  classical
  intro a
  let G := unboundedFrontierCarrierGraph C inputs
  let hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  have hleft_mem :
      source.left a ∈ unboundedFrontierVertexSet C inputs := by
    rcases source.left_edge a with h | h
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).2
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).1
  have hright_mem :
      source.right a ∈ unboundedFrontierVertexSet C inputs := by
    rcases source.right_edge a with h | h
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).2
    · exact
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole h).1
  let leftV : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨source.left a, hleft_mem⟩
  let rightV : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨source.right a, hright_mem⟩
  have hleft_ne_right : leftV ≠ rightV := by
    intro h
    exact source.heads_ne a (congrArg Subtype.val h)
  have hneighbors :
      G.neighborFinset a = ({leftV, rightV} :
        Finset {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}) := by
    ext b
    constructor
    · intro hb
      have hbAdj : G.Adj a b := by
        simpa [G, SimpleGraph.mem_neighborFinset] using hb
      have hedge :
          (a.1, b.1) ∈ unboundedFrontierEdgeSet C inputs ∨
            (b.1, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
        (unboundedFrontierCarrierGraph_adj_iff).1 (by simpa [G] using hbAdj)
      rcases source.only_selected_incident a b.1 hedge with hb_left | hb_right
      · have hb_sub : b = leftV := by
          apply Subtype.ext
          change b.1 = source.left a
          exact hb_left
        exact by
          simpa using (Or.inl hb_sub : b = leftV ∨ b = rightV)
      · have hb_sub : b = rightV := by
          apply Subtype.ext
          change b.1 = source.right a
          exact hb_right
        exact by
          simpa using (Or.inr hb_sub : b = leftV ∨ b = rightV)
    · intro hb
      have hb_cases : b = leftV ∨ b = rightV := by
        simpa using hb
      rcases hb_cases with hb_left | hb_right
      · subst b
        have hadj : G.Adj a leftV :=
          (unboundedFrontierCarrierGraph_adj_iff).2 (source.left_edge a)
        simpa [G, SimpleGraph.mem_neighborFinset] using hadj
      · subst b
        have hadj : G.Adj a rightV :=
          (unboundedFrontierCarrierGraph_adj_iff).2 (source.right_edge a)
        simpa [G, SimpleGraph.mem_neighborFinset] using hadj
  calc
    (G.neighborFinset a).card =
        ({leftV, rightV} :
          Finset {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}).card := by
      rw [hneighbors]
    _ = 2 := by
      simp [hleft_ne_right]

set_option linter.style.longLine false in
/-- Exact carrier-degree characterization of the selected incident-edge source.

Workbook note for the S2-A local selected source lane: after erasing the
metric/no-third-germ material, the remaining data in
`LocalSelectedIncidentEdgePairSourceRows inputs` is equivalent to actual
degree two of the concrete selected carrier graph
`unboundedFrontierCarrierGraph C inputs`.  This file can strictly reduce the
row to that carrier degree statement and prove the converse from the row
itself.  Closing the degree-two statement requires the exterior-topology
carrier theorem; it is not a local S2 assembly consequence. -/
theorem
    nonempty_localSelectedIncidentEdgePairSourceRows_iff_unboundedFrontierCarrierGraph_neighborFinset_card_two
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj] :
    Nonempty (LocalSelectedIncidentEdgePairSourceRows inputs) ↔
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2 := by
  constructor
  · intro hsource
    rcases hsource with ⟨source⟩
    exact
      unboundedFrontierCarrierGraph_neighborFinset_card_two_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) source
  · intro hdegree
    exact
      ⟨localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two
        (C := C) (inputs := inputs) hdegree⟩

set_option linter.style.longLine false in
/-- Simple-degree form of the selected incident-edge pair source.

The remaining source is exactly two-regularity of the actual selected exterior
carrier graph; the two selected incident heads are chosen from its neighbour
finset. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_simple_degree_two
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        @SimpleGraph.degree _
          (unboundedFrontierCarrierGraph C inputs) a
          ((unboundedFrontierCarrierGraph C inputs).neighborSetFintype a) =
            2) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_degree_two
      (C := C) (inputs := inputs) hdegree)

set_option linter.style.longLine false in
/-- Neighbour-pair form of the selected incident-edge pair source.

This erases the existing actual-carrier neighbour-pair rows to the pure
selected incident-edge pair surface consumed by
`S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows`. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_neighborPairRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    LocalSelectedIncidentEdgePairSourceRows inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs)
      (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_neighborPairRows
        (C := C) inputs neighborRows)

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-selected-edge-pair-source`, degree-two reduction.

To produce `LocalSelectedIncidentEdgePairSourceRows` it is enough to prove that
the actual selected exterior carrier graph has exactly two neighbours at each
unbounded-frontier vertex. -/
noncomputable def
    S2_agent_20260520_selected_edge_pair_source_of_carrierGraph_degree_two
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two
    (C := C) (inputs := inputs) hdegree

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-actual-carrier-degree-two-source`.

Route-specific wrapper for the current S2 source leaf: actual two-regularity
of `unboundedFrontierCarrierGraph C inputs`, in `neighborFinset.card = 2`
form, directly supplies `LocalSelectedIncidentEdgePairSourceRows inputs` via
`localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two`.
The decidability instance is the actual carrier graph's own decidable
adjacency. -/
noncomputable def
    S2_codex_current_20260520_actual_carrier_degree_two_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (hdegree :
      letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
        unboundedFrontierCarrierGraph_decidableAdj C inputs
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2) :
    LocalSelectedIncidentEdgePairSourceRows inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs) (by simpa using hdegree)

set_option linter.style.longLine false in
/-- Boundary-free two-selected-edge/no-third-germ rows feed the existing
actual-carrier degree-two selected incident-edge source through
`S2_codex_current_20260520_actual_carrier_degree_two_final_source`. -/
noncomputable def
    S2_codex_current_20260520_actual_carrier_degree_two_source_of_final_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun left : Fin n =>
          Exists fun right : Fin n =>
            ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                  (canonicalGraph C).Adj a.1 x ->
                    q ∈ vertexIncidentGermW3 C a.1 x ε ->
                      q ≠ (canonicalGraph C).point a.1 ->
                        x ≠ left ->
                          x ≠ right ->
                            False) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_codex_current_20260520_actual_carrier_degree_two_source
    (C := C) (inputs := inputs)
    (S2_codex_current_20260520_actual_carrier_degree_two_final_source
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-selected-edge-pair-degree-worker`.

Simple degree two of the actual selected exterior carrier graph is enough for
the pure selected incident-edge pair source.  The worker uses the neighbour
finset of that same graph; it does not pass through local-radius rows or any
final boundary cycle surface. -/
noncomputable def S2_dyn_20260520_selected_edge_pair_degree_worker
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    [DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj]
    (hdegree :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        @SimpleGraph.degree _
          (unboundedFrontierCarrierGraph C inputs) a
          ((unboundedFrontierCarrierGraph C inputs).neighborSetFintype a) =
            2) :
    LocalSelectedIncidentEdgePairSourceRows inputs := by
  exact
    localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs)
      (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_degree_two
        (C := C) (inputs := inputs) hdegree)

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-selected-edge-pair-source`, neighbour-row
reduction.

The existing actual-carrier neighbour-pair row is a smaller honest source for
the selected incident-edge pair rows: its two neighbours are backed by real
`unboundedFrontierEdgeSet` incidences, and its `neighbor_iff` field proves
selected incident completeness. -/
noncomputable def
    S2_agent_20260520_selected_edge_pair_source_of_neighborPairRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_neighborPairRows
    (C := C) inputs neighborRows

set_option linter.style.longLine false in
/-- Local-sector rows erase to the pure selected incident-edge pair source.

This keeps the selected heads tied to the actual concrete carrier neighbours:
the local-sector rows first give `UnboundedFrontierCarrierNeighborPairAt`, and
the existing neighbour-pair eraser then supplies the selected
`unboundedFrontierEdgeSet` incidences and incident completeness. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_neighborPairRows
    (C := C) inputs
    (unboundedFrontierCarrierNeighborPairRows_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows)

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-selected-edge-source`, carrier-neighbour form.

The pure selected incident-edge source is reduced to the honest actual
unbounded-frontier carrier neighbour-pair rows.  The chosen heads are the two
carrier neighbours, and selected incident completeness is the carrier
`neighbor_iff` field, not an all-adjacent endpoint closure shortcut. -/
noncomputable def
    S2_codex_20260520_selected_edge_source_of_neighborPairRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_neighborPairRows
    (C := C) inputs neighborRows

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-selected-edge-source`, local-sector form.

Actual local-sector rows strictly reduce to
`LocalSelectedIncidentEdgePairSourceRows`: they first erase to the concrete
unbounded-frontier carrier neighbour-pair rows and then choose the two selected
incident `unboundedFrontierEdgeSet` heads from that carrier data. -/
noncomputable def S2_codex_20260520_selected_edge_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_codex_20260520_selected_edge_source_of_neighborPairRows
    (C := C) inputs
    (unboundedFrontierCarrierNeighborPairRows_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_20260520_selected_edge_source_of_neighborPairRows`. -/
noncomputable def
    S2_codex_20260520_selected_edge_source_family_of_neighborPairRows
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_selected_edge_source_of_neighborPairRows
      (C := C) inputs (neighborRows C inputs)

set_option linter.style.longLine false in
/-- Family form of `S2_codex_20260520_selected_edge_source`. -/
noncomputable def
    S2_codex_20260520_selected_edge_source_family_of_localSectorRows
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_selected_edge_source
      (C := C) (inputs := inputs) (localSectorRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-local-selected-incident-source`,
actual carrier degree-two form.

This is the family-level version of
`localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two`.
It reduces the pure selected incident-edge source to degree two of the actual
`unboundedFrontierCarrierGraph`, with the decidable carrier adjacency supplied
locally for each input. -/
noncomputable def
    S2_codex_current_20260520_local_selected_incident_source_of_carrierGraph_degree_two
    (degreeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          letI : DecidableRel
            (unboundedFrontierCarrierGraph C inputs).Adj :=
            unboundedFrontierCarrierGraph_decidableAdj C inputs
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
              2) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs)
      (by
        simpa using (degreeRows C inputs))

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-local-selected-incident-source`,
actual carrier neighbour-row form.

This family wrapper is exactly the checked neighbour-pair eraser
`localSelectedIncidentEdgePairSourceRows_of_neighborPairRows`: the selected
heads are the two actual carrier neighbours, and incident completeness is the
carrier `neighbor_iff` row. -/
noncomputable def
    S2_codex_current_20260520_local_selected_incident_source_of_neighborPairRows
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_codex_20260520_selected_edge_source_family_of_neighborPairRows
    neighborRows

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-local-selected-incident-source`,
actual local-sector form.

This is the preferred local-sector reduction of the requested family.  It uses
`S2_codex_20260520_selected_edge_source`, so the selected incident heads are
still read from actual `unboundedFrontierEdgeSet` local-sector rows. -/
noncomputable def
    S2_codex_current_20260520_local_selected_incident_source_of_localSectorRows
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_codex_20260520_selected_edge_source_family_of_localSectorRows
    localSectorRows

set_option linter.style.longLine false in
/-- Local selected-edge/no-third-germ rows source the pure selected
incident-edge pair rows for the sharp W32 handoff.

The route is the honest local one: local selected/no-third-germ rows erase to
local-sector rows, local-sector rows erase to actual carrier neighbour-pair
rows, and those rows choose the two selected incident carrier edges. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_localSelectedNoThirdGermSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_localSectorRows
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierLocalSectorRows_of_localSelectedNoThirdGermSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-selected-edge-pair-source`.

The sharp selected-edge-pair source needed by the W32 handoff is sourced from
the current local selected-edge/no-third-germ family, through actual
local-sector and selected-carrier neighbour-pair rows.  No final boundary
cycle, induced frontier graph, endpoint all-adjacent closure, identity angular
order, or synthetic row is introduced. -/
noncomputable def S2_dyn_20260520_selected_edge_pair_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_localSelectedNoThirdGermSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of `S2_dyn_20260520-selected-edge-pair-source`. -/
noncomputable def S2_dyn_20260520_selected_edge_pair_source_family
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_dyn_20260520_selected_edge_pair_source
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-local-selected-edge-pair-source`.

Family reduction of the pure selected incident-edge pair source to the actual
two-neighbour rows of the concrete unbounded-frontier carrier graph.  The
selected heads are obtained from genuine `unboundedFrontierEdgeSet` carrier
incidences via `UnboundedFrontierCarrierNeighborPairAt`; no
unreachable-after-delete, final boundary cycle, induced frontier graph,
endpoint-only all-adjacent claim, or identity angular order is used. -/
noncomputable def
    S2_dyn_20260520_local_selected_edge_pair_source_family_of_neighborPairRows
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_selected_edge_pair_source_of_neighborPairRows
      (C := C) inputs (neighborRows C inputs)

set_option linter.style.longLine false in
/-- Local selected incident-edge pairs fill the structured local-radius source.

The remaining metric content is supplied internally by the finite drawing
vertex-isolation radius.  A nearby noncenter frontier germ first promotes to
an actual selected `unboundedFrontierEdgeSet` incidence, and the pointwise
selected-edge source then forces its head to be one of the two chosen heads. -/
noncomputable def localRadiusSelectedEdgeSourceRows_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    LocalRadiusSelectedEdgeSourceRows inputs := by
  classical
  refine
    { left := source.left
      right := source.right
      left_edge := source.left_edge
      right_edge := source.right_edge
      heads_ne := source.heads_ne
      radius := fun a =>
        Classical.choose
          (exists_ball_forall_graph_vertex_eq_of_mem_ball (C := C) a.1)
      radius_pos := ?_
      local_no_third_germ := ?_ }
  · intro a
    exact
      (Classical.choose_spec
        (exists_ball_forall_graph_vertex_eq_of_mem_ball (C := C) a.1)).1
  · intro a ε q x hqradius hqeps hqfrontier hadj hgerm hqcenter hx_left hx_right
    have hedge :
        (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
      unboundedFrontierEdgeSet_or_symm_of_local_incident_frontier_germ
        (C := C) (inputs := inputs) a ε q x hqradius hqeps hqfrontier
        hadj hgerm hqcenter
    rcases source.only_selected_incident a x hedge with hx | hx
    · exact hx_left hx
    · exact hx_right hx

/-- Claim `S2-agent-20260520-local-radius-source`.

Strict reduction of `LocalRadiusSelectedEdgeSourceRows` to the purely local
selected-edge incidence source.  The residual no longer asks for a radius or
third-germ metric proof: those are derived from finite drawing isolation and
selected `unboundedFrontierEdgeSet` membership. -/
noncomputable def S2_agent_20260520_local_radius_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    LocalRadiusSelectedEdgeSourceRows inputs :=
  localRadiusSelectedEdgeSourceRows_of_selectedIncidentEdgePairRows
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Direct selected-edge/local-germ reducer for the local no-third-germ source.

The remaining row is the actual selected incident-edge pair source: two
distinct incident `unboundedFrontierEdgeSet` heads at each concrete
unbounded-frontier carrier vertex, plus completeness for selected incident
frontier edges.  The local finite-star step promotes every nearby noncenter
incident germ to the same honest carrier edge set before the selected-head
completeness row rules out a third head. -/
noncomputable def
    localSelectedNoThirdGermSource_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs :=
  (localRadiusSelectedEdgeSourceRows_of_selectedIncidentEdgePairRows
    (C := C) (inputs := inputs) source).toExistsSource

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-local-selected-source-live`.

The live local selected source is reduced directly to actual selected
`unboundedFrontierEdgeSet` incidence rows.  The proof keeps the concrete
carrier edge set throughout: local germs first produce selected frontier-edge
membership, then the selected incident-edge row excludes any third head. -/
noncomputable def
    S2_codex_20260520_local_selected_source_live_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs :=
  localSelectedNoThirdGermSource_of_selectedIncidentEdgePairRows
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_20260520_local_selected_source_live_of_selectedIncidentEdgePairRows`. -/
noncomputable def
    S2_codex_20260520_local_selected_source_live_family_of_selectedIncidentEdgePairRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_local_selected_source_live_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) (source C inputs)

/-- Cut-partition input handoff from the same strictly local selected-edge
source. -/
noncomputable def
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  (S2_agent_20260520_local_radius_source
    (C := C) (inputs := inputs) source).toNeighborPairCutPartitionInputSource

/-- Actual carrier neighbour-pair rows supply the structured local-radius
selected-edge source.

For each frontier vertex, choose the two concrete carrier neighbours.  The
local radius is the finite graph-vertex isolation radius, so a closed incident
germ cannot hit a third graph vertex inside that ball.  If the germ point is
in the relative interior of its edge, the checked interior-frontier carrier
source promotes that edge to `unboundedFrontierEdgeSet`, and the neighbour-pair
row rules out a third head. -/
noncomputable def localRadiusSelectedEdgeSourceRows_of_neighborPairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    LocalRadiusSelectedEdgeSourceRows inputs := by
  classical
  refine
    { left := fun a => (neighborRows a).left.1
      right := fun a => (neighborRows a).right.1
      left_edge := ?_
      right_edge := ?_
      heads_ne := ?_
      radius := fun a =>
        Classical.choose
          (exists_ball_forall_graph_vertex_eq_of_mem_ball (C := C) a.1)
      radius_pos := ?_
      local_no_third_germ := ?_ }
  · intro a
    have hleft_adj :
        (unboundedFrontierCarrierGraph C inputs).Adj a (neighborRows a).left :=
      ((neighborRows a).neighbor_iff (neighborRows a).left).2 (Or.inl rfl)
    exact (unboundedFrontierCarrierGraph_adj_iff).1 hleft_adj
  · intro a
    have hright_adj :
        (unboundedFrontierCarrierGraph C inputs).Adj a (neighborRows a).right :=
      ((neighborRows a).neighbor_iff (neighborRows a).right).2 (Or.inr rfl)
    exact (unboundedFrontierCarrierGraph_adj_iff).1 hright_adj
  · intro a h
    exact (neighborRows a).left_ne_right (Subtype.ext h)
  · intro a
    exact
      (Classical.choose_spec
        (exists_ball_forall_graph_vertex_eq_of_mem_ball (C := C) a.1)).1
  · intro a ε q x hqradius hqeps hqfrontier hadj hgerm hqcenter hx_left hx_right
    let P : UnboundedFrontierCarrierNeighborPairAt inputs a := neighborRows a
    let left : Fin n := P.left.1
    let right : Fin n := P.right.1
    have hcarrier_head
        (hxmem : x ∈ unboundedFrontierVertexSet C inputs)
        (hedge :
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
            (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
        False := by
      let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
        ⟨x, hxmem⟩
      have hab : (unboundedFrontierCarrierGraph C inputs).Adj a b :=
        (unboundedFrontierCarrierGraph_adj_iff).2 hedge
      have hb : b = P.left ∨ b = P.right := (P.neighbor_iff b).1 hab
      rcases hb with hb | hb
      · exact hx_left (by simpa [P, left, b] using congrArg Subtype.val hb)
      · exact hx_right (by simpa [P, right, b] using congrArg Subtype.val hb)
    have hedge :
        (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
      unboundedFrontierEdgeSet_or_symm_of_local_incident_frontier_germ
        (C := C) (inputs := inputs) a ε q x hqradius hqeps hqfrontier
        hadj hgerm hqcenter
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
    exact hcarrier_head hxmem hedge

/-- Claim `S2-dyn-20260520-inhabit-local-radius-selected-edge-rows`.

Strict reduction of the exact local-radius selected-edge residual to the
actual carrier neighbour-pair family.  The selected heads are the two concrete
carrier neighbours at each frontier vertex, and the positive local radius is
the finite graph-vertex isolation radius. -/
noncomputable def S2_dyn_20260520_inhabit_local_radius_selected_edge_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    LocalRadiusSelectedEdgeSourceRows inputs :=
  localRadiusSelectedEdgeSourceRows_of_neighborPairRows
    (C := C) (inputs := inputs) neighborRows

set_option linter.style.longLine false in
/-- Local-sector rows erase to the current selected-edge/no-third-germ source.

This is only a source-shape eraser: it uses the two actual carrier neighbours
selected by the local-sector row, then reuses the checked local-radius
selected-edge construction.  It should not be used backwards as a proof of
local-sector rows. -/
noncomputable def localSelectedNoThirdGermSource_of_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs :=
  (localRadiusSelectedEdgeSourceRows_of_neighborPairRows
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierNeighborPairRows_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows)).toExistsSource

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-local-selected-source`, local-sector row form.

Actual carrier local-sector rows already name the two incident
`unboundedFrontierEdgeSet` heads and prove every concrete carrier neighbour is
one of them.  The finite local-star reducer supplies the positive no-third-germ
radius, so this closes the selected local source without endpoint-only
incidence, a boundary cycle, an induced frontier graph, identity angular order,
or synthetic rows. -/
noncomputable def S2_dyn_20260520_local_selected_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs :=
  localSelectedNoThirdGermSource_of_localSectorRows
    (C := C) (inputs := inputs) localSectorRows

set_option linter.style.longLine false in
/-- Family form of `S2_dyn_20260520_local_selected_source`. -/
noncomputable def S2_dyn_20260520_local_selected_source_family
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs := by
  intro m C inputs
  exact
    S2_dyn_20260520_local_selected_source
      (C := C) (inputs := inputs) (localSectorRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-neighbor-pair-cutpartition-final`, local-star
leaf form.

The exact remaining leaf is the existing local-radius selected-edge source:
two actual incident `unboundedFrontierEdgeSet` heads at each frontier vertex,
plus the finite local-star no-third-germ row. -/
noncomputable def
    S2_codex_20260520_neighbor_pair_cutpartition_final_of_localRadiusSelectedEdgeSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalRadiusSelectedEdgeSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  source.toNeighborPairCutPartitionInputSource

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-neighbor-pair-cutpartition-final`.

Actual concrete carrier-neighbour rows choose the two selected
`unboundedFrontierEdgeSet` heads.  The checked local-star radius promotes any
nearby incident frontier germ to an actual carrier edge, so the neighbour-pair
row rules out a third head; the resulting local-sector row then fills the sharp
cut-partition input source without any boundary-chord shortcut. -/
noncomputable def S2_codex_20260520_neighbor_pair_cutpartition_final
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_codex_20260520_neighbor_pair_cutpartition_final_of_localRadiusSelectedEdgeSourceRows
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_inhabit_local_radius_selected_edge_rows
      (C := C) (inputs := inputs) neighborRows)

/-- Boundary-free ordinary angular sector at one concrete graph vertex.

The selected `left` and `right` heads are arbitrary input-level carrier
neighbour candidates, not predecessor/successor vertices from a boundary
cycle. -/
abbrev BoundaryFreeGraphVertexAngularBetween
    (C : _root_.UDConfig n)
    (center left right other : Fin n) : Prop :=
  _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
      (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
        C)
      center left <
    _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
      (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
        C)
      center other ∧
  _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
      (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
        C)
      center other <
    _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
      (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
      C)
      center right

/-- Point-ray form of the same boundary-free angular sector.

This keeps the exterior-side local geometry separate from the graph-dart
bookkeeping: a nearby frontier point is between the two selected rays before
we identify its closed-germ ray with the incident dart. -/
abbrev BoundaryFreeGraphVertexPointAngularBetween
    (C : _root_.UDConfig n)
    (center left right : Fin n) (q : PlanarInterface.Point) : Prop :=
  _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
      (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
        C)
      center left <
    _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.dartArg
      ((canonicalGraph C).point center) q ∧
  _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.dartArg
      ((canonicalGraph C).point center) q <
    _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
      (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
        C)
      center right

/-- A noncenter point on an incident W3 germ has the same ray angle as the
incident graph dart, so point-ray sector rows supply graph-dart sector rows. -/
theorem boundaryFreeGraphVertexAngularBetween_of_pointAngularBetween
    {C : _root_.UDConfig n}
    {center left right other : Fin n}
    {ε : Real} {q : PlanarInterface.Point}
    (hpoint :
      BoundaryFreeGraphVertexPointAngularBetween C center left right q)
    (hgerm : q ∈ vertexIncidentGermW3 C center other ε)
    (hqne : q ≠ (canonicalGraph C).point center) :
    BoundaryFreeGraphVertexAngularBetween C center left right other := by
  have harg :
      _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.dartArg
          ((canonicalGraph C).point center) q =
        _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
          (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
            C)
          center other :=
    dartArg_eq_graphDartArg_of_mem_vertexIncidentGermW3_ne_center
      (C := C) (v := center) (other := other)
      (eps := ε) (q := q) hgerm hqne
  exact ⟨by
      simpa [BoundaryFreeGraphVertexPointAngularBetween,
        BoundaryFreeGraphVertexAngularBetween, harg] using hpoint.1,
    by
      simpa [BoundaryFreeGraphVertexPointAngularBetween,
        BoundaryFreeGraphVertexAngularBetween, harg] using hpoint.2⟩

/-- Point-ray third-germ exterior-sector rows imply the graph-dart third-germ
angular rows used by the local angular input package. -/
theorem boundaryFreeThirdGermAngularRows_of_pointAngularRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {left right :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} -> Fin n}
    (pointRows :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ left a ->
                    x ≠ right a ->
                      BoundaryFreeGraphVertexPointAngularBetween
                        C a.1 (left a) (right a) q) :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
      q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
        q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
          (canonicalGraph C).Adj a.1 x ->
            q ∈ vertexIncidentGermW3 C a.1 x ε ->
              q ≠ (canonicalGraph C).point a.1 ->
                x ≠ left a ->
                  x ≠ right a ->
                    BoundaryFreeGraphVertexAngularBetween
                      C a.1 (left a) (right a) x := by
  intro a ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
  exact
    boundaryFreeGraphVertexAngularBetween_of_pointAngularBetween
      (C := C) (center := a.1) (left := left a) (right := right a)
      (other := x) (ε := ε) (q := q)
      (pointRows a ε q x hqball hqfrontier hadj hgerm hqcenter
        hx_left hx_right)
      hgerm hqcenter

/-- Honest angular no-between row at an arbitrary input-level graph vertex. -/
structure BoundaryFreeGraphVertexAngularNoBetweenRows
    (C : _root_.UDConfig n)
    (center left right : Fin n) where
  angle :
    _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
        (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
          C)
        center left <
      _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
        (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
          C)
        center right
  no_between :
    forall other : Fin n,
      GraphBridge.UnitDistanceAdj C center other ->
      other ≠ left ->
      other ≠ right ->
        Not (BoundaryFreeGraphVertexAngularBetween C center left right other)

/-- Generic geometric graph-vertex angular rows erase to the boundary-free
S2 row shape. -/
theorem boundaryFreeGraphVertexAngularNoBetweenRows_of_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (rows :
      GeometricRotationSystem.GraphVertexAngularNoBetweenRows
        C center left right) :
    BoundaryFreeGraphVertexAngularNoBetweenRows C center left right := by
  exact
    { angle := rows.angle
      no_between := by
        intro other hAdj hother_left hother_right hbetween
        exact
          (rows.no_between other hAdj hother_left hother_right)
            (by
              simpa [BoundaryFreeGraphVertexAngularBetween,
                GeometricRotationSystem.GraphVertexAngularBetween]
                using hbetween) }

/-- A non-wrap consecutive pair in the real sorted geometric outgoing-dart
list gives the boundary-free angular no-between row for those two heads. -/
theorem boundaryFreeGraphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (row :
      GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
        C center left right) :
    BoundaryFreeGraphVertexAngularNoBetweenRows C center left right :=
  boundaryFreeGraphVertexAngularNoBetweenRows_of_graphVertexAngularNoBetweenRows
    (GeometricRotationSystem.graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      row)

set_option linter.style.longLine false in
/-- Boundary-free angular no-between rows are the generic graph-vertex angular
rows for the same three heads.

This only changes notation: both sector predicates are stated with the same
`graphDartArg` inequalities. -/
theorem graphVertexAngularNoBetweenRows_of_boundaryFreeGraphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (rows : BoundaryFreeGraphVertexAngularNoBetweenRows C center left right) :
    GeometricRotationSystem.GraphVertexAngularNoBetweenRows C center left right := by
  exact
    { angle := rows.angle
      no_between := by
        intro other hAdj hother_left hother_right hbetween
        exact
          (rows.no_between other hAdj hother_left hother_right)
            (by
              simpa [BoundaryFreeGraphVertexAngularBetween,
                GeometricRotationSystem.GraphVertexAngularBetween]
                using hbetween) }

set_option linter.style.longLine false in
/-- Boundary-free angular no-between rows give the reusable outgoing-list
no-between row over the real `GeometricRotationSystem.geometricOutgoingDartList`.

This is the pointwise local-sector/no-third-germ face of the selected-head
source: the angular row is first read as a generic graph-vertex row, then
restricted to genuine sorted outgoing darts. -/
theorem graphVertexGeometricOutgoingListNoBetweenRows_of_boundaryFreeGraphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (rows : BoundaryFreeGraphVertexAngularNoBetweenRows C center left right) :
    GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
      C center left right :=
  GeometricRotationSystem.graphVertexGeometricOutgoingListNoBetweenRows_of_graphVertexAngularNoBetweenRows
    (graphVertexAngularNoBetweenRows_of_boundaryFreeGraphVertexAngularNoBetweenRows
      rows)

/-- Claim `S2-agent-angular-neighbor-selection-input-20260520ax`.

For each concrete unbounded-frontier carrier vertex, if the two actual carrier
neighbours selected by `neighborRows` are consecutive in the genuine sorted
geometric outgoing-dart list, then they supply the boundary-free angular
no-between rows consumed by the local S2 source. -/
theorem S2_agent_angular_neighbor_selection_input_20260520ax
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (neighborRows a).left.1 (neighborRows a).right.1) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      BoundaryFreeGraphVertexAngularNoBetweenRows C a.1
        (neighborRows a).left.1 (neighborRows a).right.1 := by
  intro a
  exact
    boundaryFreeGraphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      (selectionRows a)

/-- The head of the `i`-th dart in the genuine sorted geometric outgoing list. -/
abbrev geometricOutgoingListHead
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i < (GeometricRotationSystem.geometricOutgoingDartList C center).length) :
    Fin n :=
  (GeometricRotationSystem.dartFromGeometricList C center i hi).head

/-- Pointwise source reducing the neighbour-pair and non-wrap angular-selection
families to one concrete local row.

At a real unbounded-frontier carrier vertex `a`, the row chooses two adjacent
entries of the genuine sorted geometric outgoing-dart list.  The chosen heads
must be actual selected `unboundedFrontierEdgeSet` incidences, and every
concrete carrier neighbour of `a` must be one of those two heads. -/
structure UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}) where
  index : Nat
  index_succ_lt :
    index + 1 <
      (GeometricRotationSystem.geometricOutgoingDartList C a.1).length
  left_edge :
    (a.1,
        geometricOutgoingListHead C a.1 index
          (Nat.lt_trans (Nat.lt_succ_self index) index_succ_lt)) ∈
        unboundedFrontierEdgeSet C inputs ∨
      (geometricOutgoingListHead C a.1 index
          (Nat.lt_trans (Nat.lt_succ_self index) index_succ_lt),
        a.1) ∈ unboundedFrontierEdgeSet C inputs
  right_edge :
    (a.1,
        geometricOutgoingListHead C a.1 (index + 1) index_succ_lt) ∈
        unboundedFrontierEdgeSet C inputs ∨
      (geometricOutgoingListHead C a.1 (index + 1) index_succ_lt,
        a.1) ∈ unboundedFrontierEdgeSet C inputs
  heads_ne :
    geometricOutgoingListHead C a.1 index
        (Nat.lt_trans (Nat.lt_succ_self index) index_succ_lt) ≠
      geometricOutgoingListHead C a.1 (index + 1) index_succ_lt
  only :
    forall b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (unboundedFrontierCarrierGraph C inputs).Adj a b ->
        b.1 =
            geometricOutgoingListHead C a.1 index
              (Nat.lt_trans (Nat.lt_succ_self index) index_succ_lt) ∨
          b.1 = geometricOutgoingListHead C a.1 (index + 1) index_succ_lt

namespace UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}

def leftHead
    (rows : UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
      inputs a) :
    Fin n :=
  geometricOutgoingListHead C a.1 rows.index
    (Nat.lt_trans (Nat.lt_succ_self rows.index) rows.index_succ_lt)

def rightHead
    (rows : UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
      inputs a) :
    Fin n :=
  geometricOutgoingListHead C a.1 (rows.index + 1) rows.index_succ_lt

theorem left_mem
    (rows : UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
      inputs a) :
    rows.leftHead ∈ unboundedFrontierVertexSet C inputs := by
  let hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  rcases rows.left_edge with h | h
  · exact
      (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
        hwhole h).2
  · exact
      (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
        hwhole h).1

theorem right_mem
    (rows : UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
      inputs a) :
    rows.rightHead ∈ unboundedFrontierVertexSet C inputs := by
  let hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  rcases rows.right_edge with h | h
  · exact
      (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
        hwhole h).2
  · exact
      (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
        hwhole h).1

def leftVertex
    (rows : UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
      inputs a) :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
  ⟨rows.leftHead, rows.left_mem⟩

def rightVertex
    (rows : UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
      inputs a) :
    {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
  ⟨rows.rightHead, rows.right_mem⟩

theorem leftVertex_ne_rightVertex
    (rows : UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
      inputs a) :
    rows.leftVertex ≠ rows.rightVertex := by
  intro h
  exact rows.heads_ne (congrArg Subtype.val h)

/-- Erase the concrete local sorted-list source to the ordinary carrier
neighbour-pair row. -/
def toNeighborPairAt
    (rows : UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
      inputs a) :
    UnboundedFrontierCarrierNeighborPairAt inputs a where
  left := rows.leftVertex
  right := rows.rightVertex
  left_ne_right := rows.leftVertex_ne_rightVertex
  neighbor_iff := by
    intro b
    constructor
    · intro hb
      rcases rows.only b hb with hb_left | hb_right
      · exact Or.inl (Subtype.ext hb_left)
      · exact Or.inr (Subtype.ext hb_right)
    · intro hb
      rcases hb with hb | hb
      · subst b
        exact (unboundedFrontierCarrierGraph_adj_iff).2 rows.left_edge
      · subst b
        exact (unboundedFrontierCarrierGraph_adj_iff).2 rows.right_edge

/-- Erase the same concrete local source to the non-wrap consecutive row in
the genuine sorted geometric outgoing-dart list. -/
def toGeometricAngularNeighborSelectionRow
    (rows : UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
      inputs a) :
    GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
      C a.1 rows.leftHead rows.rightHead where
  index := rows.index
  index_succ_lt := rows.index_succ_lt
  left_eq := rfl
  right_eq := rfl

end UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt

set_option linter.style.longLine false in
/-- A concrete carrier neighbour-pair row plus a genuine sorted-list
geometric-selection row fill the combined neighbour/geometric source at one
unbounded-frontier carrier vertex.

This is only an eraser: the two selected heads are still the actual carrier
neighbours, while the geometric row supplies their consecutive non-wrap
positions in the real sorted outgoing-dart list. -/
noncomputable def
    unboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt_of_neighborPair_selectionRow
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}
    (neighborRow : UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRow :
      GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
        C a.1 neighborRow.left.1 neighborRow.right.1) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt inputs a := by
  let leftHead :=
    geometricOutgoingListHead C a.1 selectionRow.index
      (Nat.lt_trans (Nat.lt_succ_self selectionRow.index)
        selectionRow.index_succ_lt)
  let rightHead :=
    geometricOutgoingListHead C a.1 (selectionRow.index + 1)
      selectionRow.index_succ_lt
  have hleft_edge :
      (a.1, neighborRow.left.1) ∈ unboundedFrontierEdgeSet C inputs ∨
        (neighborRow.left.1, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hleft_adj :
        (unboundedFrontierCarrierGraph C inputs).Adj a neighborRow.left :=
      (neighborRow.neighbor_iff neighborRow.left).2 (Or.inl rfl)
    exact (unboundedFrontierCarrierGraph_adj_iff).1 hleft_adj
  have hright_edge :
      (a.1, neighborRow.right.1) ∈ unboundedFrontierEdgeSet C inputs ∨
        (neighborRow.right.1, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hright_adj :
        (unboundedFrontierCarrierGraph C inputs).Adj a neighborRow.right :=
      (neighborRow.neighbor_iff neighborRow.right).2 (Or.inr rfl)
    exact (unboundedFrontierCarrierGraph_adj_iff).1 hright_adj
  refine
    { index := selectionRow.index
      index_succ_lt := selectionRow.index_succ_lt
      left_edge := ?_
      right_edge := ?_
      heads_ne := ?_
      only := ?_ }
  · simpa [geometricOutgoingListHead, selectionRow.left_eq] using hleft_edge
  · simpa [geometricOutgoingListHead, selectionRow.right_eq] using hright_edge
  · intro hheads
    apply neighborRow.left_ne_right
    apply Subtype.ext
    calc
      neighborRow.left.1 = leftHead := by
        simpa [leftHead, geometricOutgoingListHead] using selectionRow.left_eq
      _ = rightHead := hheads
      _ = neighborRow.right.1 := by
        simpa [rightHead, geometricOutgoingListHead] using selectionRow.right_eq.symm
  · intro b hb
    rcases (neighborRow.neighbor_iff b).1 hb with hb_left | hb_right
    · left
      calc
        b.1 = neighborRow.left.1 := congrArg Subtype.val hb_left
        _ =
            geometricOutgoingListHead C a.1 selectionRow.index
              (Nat.lt_trans (Nat.lt_succ_self selectionRow.index)
                selectionRow.index_succ_lt) := by
          simpa [geometricOutgoingListHead] using selectionRow.left_eq
    · right
      calc
        b.1 = neighborRow.right.1 := congrArg Subtype.val hb_right
        _ =
            geometricOutgoingListHead C a.1 (selectionRow.index + 1)
              selectionRow.index_succ_lt := by
          simpa [geometricOutgoingListHead] using selectionRow.right_eq

set_option linter.style.longLine false in
/-- One boundary exterior-sector row plus the genuine geometric outgoing-list
order gives the concrete neighbour-pair/selection row at the corresponding
carrier vertex.

The chosen heads are exactly the predecessor and successor boundary vertices,
read as adjacent entries of the sorted geometric outgoing-dart list.  The
sector row supplies the actual selected frontier edges and the proof that
every selected carrier neighbour is one of those two heads. -/
noncomputable def
    unboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt_of_boundaryVertexExteriorSectorRow_geometricOrder
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C}
    (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
    {k : Fin B.length}
    (ha : a.1 = B.vertex k)
    (geometric_order :
      GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
        C B k)
    (sectorRow : BoundaryVertexExteriorSectorRowsAt inputs B k) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt inputs a := by
  rcases a with ⟨av, hav⟩
  dsimp at ha
  subst av
  let i : Nat := Classical.choose geometric_order
  let hi : i + 1 <
      (GeometricRotationSystem.geometricOutgoingDartList C
        (B.vertex k)).length :=
    Classical.choose (Classical.choose_spec geometric_order)
  let horder := Classical.choose_spec (Classical.choose_spec geometric_order)
  have hleftDart :
      (UnitDistanceDart.ofBoundary B
          (PlanarInterface.cyclicPred B.length_pos k)).reverse =
        GeometricRotationSystem.dartFromGeometricList C (B.vertex k) i
          (Nat.lt_trans (Nat.lt_succ_self i) hi) :=
    horder.1
  have hrightDart :
      UnitDistanceDart.ofBoundary B k =
        GeometricRotationSystem.dartFromGeometricList C (B.vertex k) (i + 1)
          hi :=
    horder.2
  let pred := PlanarInterface.cyclicPred B.length_pos k
  let succ := PlanarInterface.cyclicSucc B.length_pos k
  have hleftHead :
      geometricOutgoingListHead C (B.vertex k) i
          (Nat.lt_trans (Nat.lt_succ_self i) hi) =
        B.vertex pred := by
    have h :=
      congrArg UnitDistanceDart.head hleftDart
    simpa [geometricOutgoingListHead, pred,
      GeometricRotationSystem.dartFromGeometricList_head] using h.symm
  have hrightHead :
      geometricOutgoingListHead C (B.vertex k) (i + 1) hi =
        B.vertex succ := by
    have h :=
      congrArg UnitDistanceDart.head hrightDart
    simpa [geometricOutgoingListHead, succ,
      GeometricRotationSystem.dartFromGeometricList_head] using h.symm
  refine
    { index := i
      index_succ_lt := hi
      left_edge := ?_
      right_edge := ?_
      heads_ne := ?_
      only := ?_ }
  · rw [hleftHead]
    exact sectorRow.pred_edge
  · rw [hrightHead]
    exact sectorRow.succ_edge
  · intro h
    have hleftHead_norm :
        ((GeometricRotationSystem.geometricOutgoingDartList C
            (B.vertex k))[i]'(Nat.lt_trans (Nat.lt_succ_self i) hi)).1.head =
          B.vertex pred := by
      simpa [geometricOutgoingListHead,
        GeometricRotationSystem.dartFromGeometricList_head] using hleftHead
    have hrightHead_norm :
        ((GeometricRotationSystem.geometricOutgoingDartList C
            (B.vertex k))[i + 1]'hi).1.head =
          B.vertex succ := by
      simpa [geometricOutgoingListHead,
        GeometricRotationSystem.dartFromGeometricList_head] using hrightHead
    exact sectorRow.pred_vertex_ne_succ_vertex
      (by
        calc
          B.vertex pred =
              ((GeometricRotationSystem.geometricOutgoingDartList C
                  (B.vertex k))[i]'(Nat.lt_trans (Nat.lt_succ_self i) hi)).1.head :=
            hleftHead_norm.symm
          _ =
              ((GeometricRotationSystem.geometricOutgoingDartList C
                  (B.vertex k))[i + 1]'hi).1.head := h
          _ = B.vertex succ := hrightHead_norm)
  · intro b hb
    have hcarrier :
        (B.vertex k, b.1) ∈ unboundedFrontierEdgeSet C inputs ∨
          (b.1, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
      simpa using
        (unboundedFrontierCarrierGraph_adj_iff).1 hb
    rcases sectorRow.local_two_germ b.1 hcarrier with hpred | hsucc
    · exact Or.inl (hpred.trans hleftHead.symm)
    · exact Or.inr (hsucc.trans hrightHead.symm)

/-- Input source for the paired local carrier-neighbour and geometric
selection obligations. -/
structure UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) where
  rows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt inputs a

set_option linter.style.longLine false in
/-- Carrier-neighbour rows plus genuine sorted-list geometric selection rows
fill the combined geometric-selection input source.

This removes the need to keep the combined source as a separate residual when
the proof route has already produced the actual neighbour-pair row and the
nonempty consecutive row in the genuine geometric outgoing list. -/
noncomputable def
    unboundedFrontierCarrierNeighborPairGeometricSelectionInputSource_of_neighborPair_selectionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (neighborRows a).left.1 (neighborRows a).right.1)) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs where
  rows := fun a =>
    unboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt_of_neighborPair_selectionRow
      (C := C) (inputs := inputs) (a := a)
      (neighborRows a) (Classical.choice (selectionRows a))

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-geometric-selection-neighbor-source`.

The selected-carrier neighbour-pair family and the genuine non-wrap consecutive
geometric outgoing-list row for those two selected neighbours strictly reduce
the combined geometric-selection input source exposed by the local-angular
route.  This lane does not package or use the endpoint-only/no-third wrapper;
that remains a separate consumer of the same selected neighbour heads. -/
noncomputable def S2_dyn_20260520_geometric_selection_neighbor_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (neighborRows a).left.1 (neighborRows a).right.1)) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  unboundedFrontierCarrierNeighborPairGeometricSelectionInputSource_of_neighborPair_selectionRows
    (C := C) (inputs := inputs) neighborRows selectionRows

set_option linter.style.longLine false in
/-- Honest source rows for the geometric-neighbour selection input.

The carrier-neighbour rows are the current real neighbour-pair machinery.  The
extra field is the genuinely geometric residual: the same two selected carrier
heads occur as a non-wrap consecutive pair in the sorted outgoing unit-dart
list at the carrier vertex.  This is not a final boundary-cycle row,
actual-boundary equivalence row, induced frontier graph shortcut, arbitrary
cycle/carrier row, synthetic enclosure row, identity angular-order row, or
all-adjacent endpoint closure/incident shortcut. -/
structure UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  neighborRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a
  consecutiveRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (neighborRows a).left.1 (neighborRows a).right.1)

namespace UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- Erase the honest selected-neighbour/geometric-consecutivity rows to the
combined input source consumed by the shortest local-angular route. -/
noncomputable def toGeometricSelectionInputSource
    (rows :
      UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_dyn_20260520_geometric_selection_neighbor_source
    (C := C) (inputs := inputs) rows.neighborRows rows.consecutiveRows

end UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-geometric-neighbor-selection-source`.

Strict reduction of the combined geometric-selection input source to the
current real carrier-neighbour pair rows plus the one honest geometric
residual for those same selected heads: a non-wrap consecutive row in the real
sorted outgoing-dart list.  In particular, the endpoint-only/no-chord branch is
not part of this source; it remains a separate sharper residual for consumers
that need to rule out closed endpoint germs. -/
noncomputable def S2_dyn_20260520_geometric_neighbor_selection_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  rows.toGeometricSelectionInputSource

set_option linter.style.longLine false in
/-- Family wrapper for
`S2_dyn_20260520_geometric_neighbor_selection_source`. -/
noncomputable def
    S2_dyn_20260520_geometric_neighbor_selection_source_family
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_dyn_20260520_geometric_neighbor_selection_source
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Family form of `S2_dyn_20260520_geometric_selection_neighbor_source`.

The residual family is exactly Arendt's selected-carrier neighbour-pair row
plus the geometric angular ordering/selection row for the same two heads. -/
noncomputable def
    S2_dyn_20260520_geometric_selection_neighbor_source_family
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_dyn_20260520_geometric_selection_neighbor_source
      (C := C) (inputs := inputs)
      (neighborRows C inputs) (selectionRows C inputs)

set_option linter.style.longLine false in
/-- Source rows for the final selected-neighbour geometric source reduction.

The neighbour data is kept on the selected incident-edge/cut-partition surface:
the two heads are backed by genuine `unboundedFrontierEdgeSet` incidences, and
the checked no-cut eraser proves they are exactly the carrier neighbours.  The
geometric field is the genuine non-wrap consecutive row in the sorted outgoing
unit-dart list for those same two selected heads. -/
structure UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  selectedNeighborRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a
  geometricOrderRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (selectedNeighborRows a).left
            (selectedNeighborRows a).right)

/-- The selected incident-edge/cut-partition half of
`UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows`.

Each pointwise row names two actual selected unbounded-frontier incidences at
the carrier vertex and keeps the sharp no-cut residual for any third carrier
neighbour.  No angular order or endpoint-only shortcut is included here. -/
structure UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  selectedNeighborRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a

namespace UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- Build the selected-neighbour source wrapper from the exact pointwise
cut-partition rows. -/
def ofCutPartitionRows
    (rows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs where
  selectedNeighborRows := rows

/-- Erase the selected-neighbour source wrapper to its pointwise
cut-partition row family. -/
def toCutPartitionRows
    (rows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a :=
  rows.selectedNeighborRows

end UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows

/-- The genuine sorted outgoing-dart order theorem for a fixed selected
incident-edge/cut-partition source.

For each carrier vertex this proves that the two selected heads from the
cut-partition source occur as a non-wrap consecutive pair in
`GeometricRotationSystem.geometricOutgoingDartList`. -/
structure UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs) where
  geometricOrderRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right)

set_option linter.style.longLine false in
/-- Primitive sorted outgoing-dart index residual for the selected-neighbour
geometric-order half.

For each selected carrier vertex, the two selected heads from the
cut-partition source must be the heads of entries `index` and `index + 1` in
the genuine `GeometricRotationSystem.geometricOutgoingDartList`.  This is just
the bare list-index content behind
`UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows`; it contains no
boundary-cycle, endpoint/no-chord, induced-carrier, or identity-order shortcut.
-/
def UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs) :
    Prop :=
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    Exists fun index : Nat =>
      Exists fun index_succ_lt :
          index + 1 <
            (GeometricRotationSystem.geometricOutgoingDartList C a.1).length =>
        (selectedRows.selectedNeighborRows a).left =
            (GeometricRotationSystem.dartFromGeometricList C a.1 index
              (Nat.lt_trans (Nat.lt_succ_self index) index_succ_lt)).head ∧
          (selectedRows.selectedNeighborRows a).right =
            (GeometricRotationSystem.dartFromGeometricList C a.1
              (index + 1) index_succ_lt).head

set_option linter.style.longLine false in
/-- The primitive sorted outgoing-dart index residual fills the selected
geometric-order half. -/
noncomputable def
    unboundedFrontierCarrierSelectedNeighborGeometricOrderRows_of_indexRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
      selectedRows where
  geometricOrderRows := by
    intro a
    rcases indexRows a with ⟨index, index_succ_lt, hleft, hright⟩
    exact
      ⟨{ index := index
         index_succ_lt := index_succ_lt
         left_eq := hleft
         right_eq := hright }⟩

set_option linter.style.longLine false in
/-- Genuine selected-neighbour geometric-order rows expose the corresponding
primitive sorted outgoing-dart index rows for the same selected heads. -/
theorem
    unboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows_of_geometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (geometricRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
        selectedRows) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
      selectedRows := by
  intro a
  rcases geometricRows.geometricOrderRows a with ⟨row⟩
  exact
    ⟨row.index, row.index_succ_lt, row.left_eq, row.right_eq⟩

set_option linter.style.longLine false in
/-- Claim `S2-agent-selected-geometric-order-source`.

Strict reducer for the selected-neighbour geometric-order half: it is enough
to prove the real sorted outgoing-dart index residual for the two selected
heads at every actual unbounded-frontier carrier vertex. -/
noncomputable def S2_agent_selected_geometric_order_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
      selectedRows :=
  unboundedFrontierCarrierSelectedNeighborGeometricOrderRows_of_indexRows
    (C := C) (inputs := inputs) indexRows

set_option linter.style.longLine false in
/-- Selected cut-partition heads with a genuine sorted-list geometric-order row
give the exact graph-vertex angular no-between source for those same heads.

The selected heads are not recomputed here: they are the `left` and `right`
heads named by the selected incident-edge/cut-partition source, whose pointwise
rows contain the real `unboundedFrontierEdgeSet` incidences.  The only
geometric input is the non-wrap consecutive row in the genuine sorted
`GeometricRotationSystem.geometricOutgoingDartList`. -/
theorem
    unboundedFrontierCarrierSelectedNeighborGraphVertexAngularNoBetweenRows_of_geometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (geometricRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
        selectedRows) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.GraphVertexAngularNoBetweenRows
        C a.1 (selectedRows.selectedNeighborRows a).left
          (selectedRows.selectedNeighborRows a).right := by
  intro a
  rcases geometricRows.geometricOrderRows a with ⟨row⟩
  exact
    GeometricRotationSystem.graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      row

set_option linter.style.longLine false in
/-- Genuine selected-head outgoing-list no-between rows from the selected
geometric-order source.

This keeps the pointwise residual at the real sorted
`GeometricRotationSystem.geometricOutgoingDartList`: the selected heads are
exactly the left/right heads named by the cut-partition rows, and the
geometric-order row supplies their consecutive non-wrap list positions. -/
theorem
    unboundedFrontierCarrierSelectedNeighborGraphVertexGeometricOutgoingListNoBetweenRows_of_geometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (geometricRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
        selectedRows) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
        C a.1 (selectedRows.selectedNeighborRows a).left
          (selectedRows.selectedNeighborRows a).right := by
  intro a
  rcases geometricRows.geometricOrderRows a with ⟨row⟩
  exact
    GeometricRotationSystem.graphVertexGeometricOutgoingListNoBetweenRows_of_geometricAngularNeighborSelectionRow
      row

set_option linter.style.longLine false in
/-- Claim `S2-codex-main-20260520-selected-head-outgoing-list-source`.

Strict selected-head source reduction: the reusable pointwise
`GraphVertexGeometricOutgoingListNoBetweenRows` rows for the actual selected
carrier heads follow from the same genuine geometric-order rows, without
passing through identity angular order or an arbitrary carrier cycle. -/
theorem
    S2_codex_main_20260520_selected_head_outgoing_list_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (geometricRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
        selectedRows) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
        C a.1 (selectedRows.selectedNeighborRows a).left
          (selectedRows.selectedNeighborRows a).right :=
  unboundedFrontierCarrierSelectedNeighborGraphVertexGeometricOutgoingListNoBetweenRows_of_geometricOrderRows
    (C := C) (inputs := inputs) geometricRows

set_option linter.style.longLine false in
/-- Combined selected-neighbour source rows expose the pointwise outgoing-list
no-between rows for their own actual selected carrier heads. -/
theorem
    S2_codex_main_20260520_selected_head_outgoing_list_source_of_selectedNeighborGeometricOrderSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
        C a.1 (rows.selectedNeighborRows a).left
          (rows.selectedNeighborRows a).right := by
  intro a
  rcases rows.geometricOrderRows a with ⟨row⟩
  exact
    GeometricRotationSystem.graphVertexGeometricOutgoingListNoBetweenRows_of_geometricAngularNeighborSelectionRow
      row

set_option linter.style.longLine false in
/-- Rebuild selected-head geometric-order rows from genuine outgoing-list
no-between rows for the same selected cut-partition heads.

This is the reverse face of
`unboundedFrontierCarrierSelectedNeighborGraphVertexGeometricOutgoingListNoBetweenRows_of_geometricOrderRows`:
the selected `unboundedFrontierEdgeSet` incidences provide the actual
unit-distance adjacencies, and the only angular input is the real
`GeometricRotationSystem.geometricOutgoingDartList` no-between row. -/
theorem
    unboundedFrontierCarrierSelectedNeighborGeometricOrderRows_of_graphVertexGeometricOutgoingListNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (listRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
      selectedRows where
  geometricOrderRows := by
    intro a
    let cutRows := selectedRows.selectedNeighborRows a
    have hleft_canonical : (canonicalGraph C).Adj a.1 cutRows.left := by
      rcases cutRows.left_edge with h | h
      · exact unboundedFrontierEdgeSet_adj h
      · exact canonicalAdj_symm (unboundedFrontierEdgeSet_adj h)
    have hright_canonical : (canonicalGraph C).Adj a.1 cutRows.right := by
      rcases cutRows.right_edge with h | h
      · exact unboundedFrontierEdgeSet_adj h
      · exact canonicalAdj_symm (unboundedFrontierEdgeSet_adj h)
    have hleft_unit : GraphBridge.UnitDistanceAdj C a.1 cutRows.left :=
      ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 cutRows.left).1
        hleft_canonical
    have hright_unit : GraphBridge.UnitDistanceAdj C a.1 cutRows.right :=
      ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 cutRows.right).1
        hright_canonical
    exact
      GeometricRotationSystem.exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingListNoBetweenRows
        hleft_unit hright_unit
        (by simpa [cutRows] using listRows a)

set_option linter.style.longLine false in
/-- Claim `S2-codex-main-20260520-selected-geometric-angular-source`.

Pointwise selected-head geometric angular rows follow from the reusable
genuine outgoing-list no-between rows over
`GeometricRotationSystem.geometricOutgoingDartList` for the same selected
cut-partition heads. -/
theorem S2_codex_main_20260520_selected_geometric_angular_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (listRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :=
  (unboundedFrontierCarrierSelectedNeighborGeometricOrderRows_of_graphVertexGeometricOutgoingListNoBetweenRows
    (C := C) (inputs := inputs) (selectedRows := selectedRows)
    listRows).geometricOrderRows

set_option linter.style.longLine false in
/-- Package form of
`S2_codex_main_20260520_selected_geometric_angular_source`. -/
theorem
    S2_codex_main_20260520_selected_geometric_order_rows_of_outgoing_list_no_between
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (listRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
      selectedRows :=
  unboundedFrontierCarrierSelectedNeighborGeometricOrderRows_of_graphVertexGeometricOutgoingListNoBetweenRows
    (C := C) (inputs := inputs) (selectedRows := selectedRows) listRows

set_option linter.style.longLine false in
/-- Claim `S2-worker-20260520-selected-head-angular-no-between`.

Strict reduction of the selected-head angular source to the primitive genuine
sorted outgoing-dart index rows for the same selected cut-partition heads.  The
cut-partition source supplies the actual selected `unboundedFrontierEdgeSet`
incidences; the index row supplies the real angular order and no identity
order, final boundary row, arbitrary cycle, induced frontier shortcut,
endpoint/no-chord assumption, or synthetic enclosure is used. -/
theorem
    S2_worker_20260520_selected_head_angular_no_between_of_indexRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.GraphVertexAngularNoBetweenRows
        C a.1 (selectedRows.selectedNeighborRows a).left
          (selectedRows.selectedNeighborRows a).right :=
  unboundedFrontierCarrierSelectedNeighborGraphVertexAngularNoBetweenRows_of_geometricOrderRows
    (C := C) (inputs := inputs)
    (S2_agent_selected_geometric_order_source
      (C := C) (inputs := inputs) indexRows)

set_option linter.style.longLine false in
/-- Honest graph-vertex angular no-between rows strictly reduce the primitive
selected-neighbour sorted outgoing-dart index residual.

The selected heads are the same heads named by the cut-partition rows.  Their
actual `unboundedFrontierEdgeSet` incidences supply the unit-distance adjacency
hypotheses needed by the generic geometric sorted-list no-between/index
reducer. -/
theorem
    unboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows_of_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexAngularNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
      selectedRows := by
  intro a
  let cutRows := selectedRows.selectedNeighborRows a
  have hleft_canonical : (canonicalGraph C).Adj a.1 cutRows.left := by
    rcases cutRows.left_edge with h | h
    · exact unboundedFrontierEdgeSet_adj h
    · exact canonicalAdj_symm (unboundedFrontierEdgeSet_adj h)
  have hright_canonical : (canonicalGraph C).Adj a.1 cutRows.right := by
    rcases cutRows.right_edge with h | h
    · exact unboundedFrontierEdgeSet_adj h
    · exact canonicalAdj_symm (unboundedFrontierEdgeSet_adj h)
  have hleft_unit : GraphBridge.UnitDistanceAdj C a.1 cutRows.left :=
    ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 cutRows.left).1
      hleft_canonical
  have hright_unit : GraphBridge.UnitDistanceAdj C a.1 cutRows.right :=
    ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 cutRows.right).1
      hright_canonical
  rcases
    GeometricRotationSystem.exists_graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
      hleft_unit hright_unit
      (by simpa [cutRows] using angularRows a) with
    ⟨selectionRow⟩
  exact
    ⟨selectionRow.index, selectionRow.index_succ_lt,
      by simpa [cutRows] using selectionRow.left_eq,
      by simpa [cutRows] using selectionRow.right_eq⟩

set_option linter.style.longLine false in
/-- Claim `S2-worker-20260520-selected-geometric-index-source`.

Focused source reducer for the selected cut-partition heads: it is enough to
prove the honest graph-vertex angular no-between rows for those exact selected
heads.  The outgoing-dart indices are then obtained from the genuine sorted
`GeometricRotationSystem.geometricOutgoingDartList`. -/
theorem
    S2_worker_20260520_selected_geometric_index_source_of_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs}
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexAngularNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
      selectedRows :=
  unboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows_of_graphVertexAngularNoBetweenRows
    (C := C) (inputs := inputs) angularRows

set_option linter.style.longLine false in
/-- Strict split of
`UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows`.

The combined row follows from two sharper non-final sources: selected
incident-edge/cut-partition rows, and the real geometric theorem that the same
two selected heads are consecutive in the sorted outgoing-dart list. -/
noncomputable def
    unboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows_of_cutPartition_geometricOrder
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs)
    (geometricRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
        selectedRows) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs where
  selectedNeighborRows := selectedRows.selectedNeighborRows
  geometricOrderRows := geometricRows.geometricOrderRows

namespace UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- Project the combined row to its selected incident-edge/cut-partition
source half. -/
def toSelectedNeighborCutPartitionSourceRows
    (rows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs where
  selectedNeighborRows := rows.selectedNeighborRows

/-- Project the combined row to the genuine geometric-order theorem over the
selected incident-edge/cut-partition source half. -/
noncomputable def toSelectedNeighborGeometricOrderRows
    (rows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
      rows.toSelectedNeighborCutPartitionSourceRows where
  geometricOrderRows := by
    intro a
    exact rows.geometricOrderRows a

/-- The selected incident-edge rows erase to the exact carrier-neighbour rows. -/
def toNeighborPairRows
    (rows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a :=
  fun a => (rows.selectedNeighborRows a).toNeighborPairAt

/-- Reindex the geometric rows along the neighbour-pair eraser. -/
noncomputable def toGeometricOrderRows
    (rows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (rows.toNeighborPairRows a).left.1
            (rows.toNeighborPairRows a).right.1) := by
  intro a
  exact
    ⟨by
      simpa [toNeighborPairRows,
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt.toNeighborPairAt,
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt.leftVertex,
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt.rightVertex]
        using Classical.choice (rows.geometricOrderRows a)⟩

/-- Forget selected incident-edge/cut-partition rows to the compact
neighbour-pair plus sorted-list geometric source. -/
noncomputable def toGeometricNeighborSelectionSourceRows
    (rows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs) :
    UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs where
  neighborRows := rows.toNeighborPairRows
  consecutiveRows := rows.toGeometricOrderRows

/-- Erase the selected-neighbour/geometric-order rows to the combined input
source consumed by the local S2 route. -/
noncomputable def toGeometricSelectionInputSource
    (rows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_dyn_20260520_geometric_neighbor_selection_source
    (C := C) (inputs := inputs)
    rows.toGeometricNeighborSelectionSourceRows

end UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-selected-neighbor-geometric-order-source-split`.

Strict reduction of
`UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows` to two
sharper non-final source rows: the selected incident-edge/cut-partition rows
and the genuine sorted outgoing-dart consecutive-order theorem for exactly
the same selected heads. -/
noncomputable def
    S2_codex_20260520_selected_neighbor_geometric_order_source_split
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs)
    (geometricRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
        selectedRows) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs :=
  unboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows_of_cutPartition_geometricOrder
    (C := C) (inputs := inputs) selectedRows geometricRows

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_20260520_selected_neighbor_geometric_order_source_split`. -/
noncomputable def
    S2_codex_20260520_selected_neighbor_geometric_order_source_split_family
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
            (selectedRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_selected_neighbor_geometric_order_source_split
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (geometricRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-selected-carrier-local-source`.

Selected-neighbour cut-partition rows strictly reduce to the pure selected
incident-edge pair source.  The selected heads are projected from the same
pointwise rows, so the `unboundedFrontierEdgeSet` incidences and the concrete
carrier-neighbour completeness proof are preserved. -/
noncomputable def S2_codex_20260520_selected_carrier_local_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
        inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_neighborPairRows
    (C := C) inputs
    (fun a => (selectedRows.selectedNeighborRows a).toNeighborPairAt)

set_option linter.style.longLine false in
/-- Geometric-neighbour source form of
`S2_codex_20260520_selected_carrier_local_source`.

Adding the genuine selected-head geometric order rows packages the compact
selected-carrier geometric-neighbour source; it is only the existing
selected-neighbour split followed by forgetting to carrier-neighbour plus
sorted-list consecutivity rows. -/
noncomputable def
    S2_codex_20260520_selected_carrier_local_source_geometricNeighborSelectionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
        inputs)
    (geometricRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
        selectedRows) :
    UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs :=
  (S2_codex_20260520_selected_neighbor_geometric_order_source_split
    (C := C) (inputs := inputs) selectedRows geometricRows).toGeometricNeighborSelectionSourceRows

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-compact-geometric-neighbor-source-leaf`.

Actual selected carrier cut-partition rows plus honest graph-vertex angular
no-between rows for those same selected heads fill the compact
geometric-neighbour source consumed by the short W32 route.  The angular rows
are converted to genuine non-wrap adjacent entries in
`GeometricRotationSystem.geometricOutgoingDartList`; no identity cyclic order,
induced frontier graph, carrier cycle, or endpoint all-adjacent shortcut is
introduced. -/
noncomputable def
    S2_codex_current_20260520_compact_geometric_neighbor_source_leaf
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
        inputs)
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexAngularNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs :=
  S2_codex_20260520_selected_carrier_local_source_geometricNeighborSelectionRows
    (C := C) (inputs := inputs) selectedRows
    (S2_agent_selected_geometric_order_source
      (C := C) (inputs := inputs) (selectedRows := selectedRows)
      (S2_worker_20260520_selected_geometric_index_source_of_graphVertexAngularNoBetweenRows
        (C := C) (inputs := inputs) (selectedRows := selectedRows)
        angularRows))

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-actual-carrier-neighbor-selection`.

Strict reducer from the two honest local halves to the combined carrier
neighbour/geometric-selection source: the selected cut-partition rows carry
the actual `unboundedFrontierEdgeSet` incidences, while the index rows say
those same selected heads occur consecutively in the genuine sorted outgoing
dart list. -/
noncomputable def
    S2_agent_20260520_actual_carrier_neighbor_selection_of_cutPartition_indexRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs)
    (indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  (S2_codex_20260520_selected_neighbor_geometric_order_source_split
    (C := C) (inputs := inputs) selectedRows
    (S2_agent_selected_geometric_order_source
      (C := C) (inputs := inputs) indexRows)).toGeometricSelectionInputSource

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_20260520_actual_carrier_neighbor_selection_of_cutPartition_indexRows`. -/
noncomputable def
    S2_agent_20260520_actual_carrier_neighbor_selection_family_of_cutPartition_indexRows
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
            (selectedRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_actual_carrier_neighbor_selection_of_cutPartition_indexRows
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (indexRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-geometric-selection-source`.

The local geometric-selection leaf is sourced from actual selected
unbounded-frontier carrier rows and genuine sorted outgoing-list order.  The
selected rows carry the `unboundedFrontierEdgeSet` incidences; the index rows
say those same selected heads occur at consecutive positions in
`GeometricRotationSystem.geometricOutgoingDartList`. -/
noncomputable def S2_codex_20260520_geometric_selection_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs)
    (indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_agent_20260520_actual_carrier_neighbor_selection_of_cutPartition_indexRows
    (C := C) (inputs := inputs) selectedRows indexRows

set_option linter.style.longLine false in
/-- Family form of `S2_codex_20260520_geometric_selection_source`. -/
noncomputable def S2_codex_20260520_geometric_selection_source_family
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
            (selectedRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_geometric_selection_source
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (indexRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-selected-cutpartition-source`.

Strict wrapper reduction of the selected incident-edge/cut-partition source to
the existing pointwise cut-partition rows.  This adds no geometric or boundary
payload: the selected-neighbour source is just the named selected-edge surface
used by the geometric-order split. -/
def S2_agent_selected_cutpartition_source_of_cutPartitionRows_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows.ofCutPartitionRows
    rows

set_option linter.style.longLine false in
/-- Actual carrier/geometric-selection rows give the pure selected incident
edge-pair source.

This is just the selected-edge projection of the concrete carrier source:
each pointwise row names two real `unboundedFrontierEdgeSet` incidences and
proves every carrier neighbour is one of them.  The geometric consecutive row
is ignored here; no endpoint-only or all-adjacent shortcut is used. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_neighborPairRows
    (C := C) inputs
    (fun a => (source.rows a).toNeighborPairAt)

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-selected-edge-pair-source`, actual carrier-row
form.

The selected incident-edge source follows directly from the concrete
carrier/geometric-selection rows, whose chosen heads are backed by actual
`unboundedFrontierEdgeSet` membership. -/
noncomputable def
    S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_geometricSelectionInputSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Compact carrier-neighbour/geometric rows give the selected incident-edge
pair source by projecting to their actual neighbour rows. -/
noncomputable def
    S2_agent_20260520_selected_edge_pair_source_of_geometricNeighborSelectionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_agent_20260520_selected_edge_pair_source_of_neighborPairRows
    (C := C) inputs rows.neighborRows

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-local-selected-edge-pair-source`, selected
carrier-data form.

The combined geometric-selection source contains the same actual carrier
neighbour-pair rows, plus geometric order data that is irrelevant for this
pure incident-edge projection.  This keeps the family source on selected
exterior carrier data rather than on endpoint-only adjacency or a boundary
cycle. -/
noncomputable def
    S2_dyn_20260520_local_selected_edge_pair_source_family_of_geometricSelectionInputSource
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) (geometricSelection C inputs)

set_option linter.style.longLine false in
/-- Compact selected-carrier row form of
`S2_dyn_20260520_local_selected_edge_pair_source_family_of_geometricSelectionInputSource`.

Callers that already package actual carrier-neighbour rows together with the
real sorted outgoing-dart consecutive row can project the selected incident
edge-pair family directly. -/
noncomputable def
    S2_dyn_20260520_local_selected_edge_pair_source_family_of_geometricNeighborSelectionRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_selected_edge_pair_source_of_geometricNeighborSelectionRows
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Geometric-selection source form of
`S2_dyn_20260520_local_selected_source`.

The selected heads are projected from the existing actual
carrier/geometric-selection rows, then the local finite-star reducer supplies
the no-third-germ radius.  The geometric order field is preserved as honest
source data but is not needed to build this existential selected local source. -/
noncomputable def
    S2_dyn_20260520_local_selected_source_of_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs :=
  (S2_agent_20260520_local_radius_source
    (C := C) (inputs := inputs)
    (S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) source)).toExistsSource

set_option linter.style.longLine false in
/-- Compact geometric-neighbour row form of
`S2_dyn_20260520_local_selected_source_of_geometricSelectionInputSource`. -/
noncomputable def
    S2_dyn_20260520_local_selected_source_of_geometricNeighborSelectionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs :=
  (S2_agent_20260520_local_radius_source
    (C := C) (inputs := inputs)
    (S2_agent_20260520_selected_edge_pair_source_of_geometricNeighborSelectionRows
      (C := C) (inputs := inputs) rows)).toExistsSource

set_option linter.style.longLine false in
/-- Family form of
`S2_dyn_20260520_local_selected_source_of_geometricSelectionInputSource`. -/
noncomputable def
    S2_dyn_20260520_local_selected_source_family_of_geometricSelectionInputSource
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs := by
  intro m C inputs
  exact
    S2_dyn_20260520_local_selected_source_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) (geometricSelection C inputs)

set_option linter.style.longLine false in
/-- Family form of
`S2_dyn_20260520_local_selected_source_of_geometricNeighborSelectionRows`. -/
noncomputable def
    S2_dyn_20260520_local_selected_source_family_of_geometricNeighborSelectionRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs := by
  intro m C inputs
  exact
    S2_dyn_20260520_local_selected_source_of_geometricNeighborSelectionRows
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-worker-20260520-selected-cutpartition-source`.

Strict reduction of the selected cut-partition source to the local two-germ
rows.  The local two-germ rows choose the two actual selected
`unboundedFrontierEdgeSet` incident heads at each frontier vertex; the existing
local-sector eraser proves any third carrier-neighbour branch impossible, so
the checked cut-partition row is filled without endpoint-only shortcuts,
boundary-cycle rows, induced frontier graphs, arbitrary cycles, identity
angular order, or synthetic enclosure rows. -/
noncomputable def
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  S2_agent_selected_cutpartition_source_of_cutPartitionRows_20260520
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierNeighborPairCutPartitionRows_of_localSectorRows
      (C := C) (inputs := inputs)
      (localSectorRows_of_localTwoGermRows
        (C := C) (inputs := inputs) localTwoGermRows))

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-selected-edge-pair-source`, selected cut-row
actual carrier form.

Concrete carrier/geometric-selection rows first project to the honest carrier
neighbour-pair rows.  The existing local-star reducer then promotes nearby
frontier points through actual `unboundedFrontierEdgeSet` membership and fills
the selected neighbour-pair cut rows. -/
noncomputable def
    S2_agent_selected_cutpartition_source_of_geometricSelectionInputSource_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
    (C := C) (inputs := inputs)
    (localTwoGermRows_of_localSectorRows
      (C := C) (inputs := inputs)
      ((localRadiusSelectedEdgeSourceRows_of_neighborPairRows
        (C := C) (inputs := inputs)
        (fun a => (source.rows a).toNeighborPairAt)).toLocalSectorRows))

set_option linter.style.longLine false in
/-- Deleted-neighbour residual for
`S2_agent_selected_cutpartition_source_of_cutPartitionRows_20260520`.

The remaining honest source is the ambient deleted-graph row: choose the two
actual selected incident `unboundedFrontierEdgeSet` heads at each frontier
vertex, and prove every third concrete carrier neighbour is unreachable from
the selected left head after deleting that vertex. -/
noncomputable def
    S2_agent_selected_cutpartition_source_of_unreachableAfterDelete_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  S2_agent_selected_cutpartition_source_of_cutPartitionRows_20260520
    (C := C) (inputs := inputs)
    (S2_agent_cu_neighbor_cutpartition_source_of_unreachableAfterDelete_20260520
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Strict local-planar residual for
`UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows`.

This composes the existing local Boolean side-separation eraser with the
ambient deleted-graph and cut-partition erasers, then wraps the resulting
pointwise selected incident-edge rows.  No boundary cycle, actual-boundary
equivalence, induced frontier graph shortcut, arbitrary carrier/cycle,
synthetic enclosure, identity angular order, or endpoint/no-chord shortcut is
introduced. -/
noncomputable def
    S2_agent_selected_cutpartition_source_of_localSeparation_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
        C inputs) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  S2_agent_selected_cutpartition_source_of_unreachableAfterDelete_20260520
    (C := C) (inputs := inputs)
    (S2_agent_cv_deleted_neighbor_source_of_localSeparation_20260520
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_selected_cutpartition_source_of_localSeparation_20260520`. -/
noncomputable def
    S2_agent_selected_cutpartition_source_family_of_localSeparation_20260520
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
          inputs := by
  intro m C inputs
  exact
    S2_agent_selected_cutpartition_source_of_localSeparation_20260520
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Dependent-pair source form for selected carrier neighbours and their
genuine geometric order.

This is the next input-level source shape: the selected edge rows and sorted
outgoing-dart order rows are produced together, so the two selected heads
cannot drift apart between independent source families. -/
def SelectedNeighborCutPartitionGeometricOrderSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  Exists fun selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
        inputs =>
    Nonempty
      (UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
        selectedRows)

set_option linter.style.longLine false in
/-- Pointwise honest input row for the selected-neighbour cut-partition and
geometric-order source.

At a real unbounded-frontier carrier vertex, the row names two actual selected
`unboundedFrontierEdgeSet` incidences, gives the sharp cut-partition residual
for every third concrete carrier neighbour, and proves that the same two heads
are adjacent non-wrap entries of the genuine
`GeometricRotationSystem.geometricOutgoingDartList`. -/
structure SelectedNeighborCutPartitionGeometricOrderInputRowsAt
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}) where
  left : Fin n
  right : Fin n
  left_edge :
    (a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
      (left, a.1) ∈ unboundedFrontierEdgeSet C inputs
  right_edge :
    (a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
      (right, a.1) ∈ unboundedFrontierEdgeSet C inputs
  heads_ne : left ≠ right
  third_neighbor_cutPartitions :
    forall b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (unboundedFrontierCarrierGraph C inputs).Adj a b ->
        b.1 ≠ left ->
          b.1 ≠ right ->
            Nonempty (CutVertexInterface.CutVertexPartition C)
  index : Nat
  index_succ_lt :
    index + 1 <
      (GeometricRotationSystem.geometricOutgoingDartList C a.1).length
  left_eq :
    left =
      (GeometricRotationSystem.dartFromGeometricList C a.1 index
        (Nat.lt_trans (Nat.lt_succ_self index) index_succ_lt)).head
  right_eq :
    right =
      (GeometricRotationSystem.dartFromGeometricList C a.1 (index + 1)
        index_succ_lt).head

namespace SelectedNeighborCutPartitionGeometricOrderInputRowsAt

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}

/-- Forget the pointwise honest source to the selected incident-edge
cut-partition row. -/
def toCutPartitionRowsAt
    (rows :
      SelectedNeighborCutPartitionGeometricOrderInputRowsAt inputs a) :
    UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a where
  left := rows.left
  right := rows.right
  left_edge := rows.left_edge
  right_edge := rows.right_edge
  heads_ne := rows.heads_ne
  third_neighbor_cutPartitions := rows.third_neighbor_cutPartitions

/-- Read the genuine non-wrap sorted-list order row from the same pointwise
honest source. -/
def toGeometricAngularNeighborSelectionRow
    (rows :
      SelectedNeighborCutPartitionGeometricOrderInputRowsAt inputs a) :
    GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
      C a.1 rows.left rows.right where
  index := rows.index
  index_succ_lt := rows.index_succ_lt
  left_eq := rows.left_eq
  right_eq := rows.right_eq

end SelectedNeighborCutPartitionGeometricOrderInputRowsAt

set_option linter.style.longLine false in
/-- Pointwise bridge from selected incident-edge/cut-partition rows plus an
honest geometric angular no-between row to the combined selected-neighbour
geometric-order input row.

The two selected `unboundedFrontierEdgeSet` incidences provide the actual
unit-distance adjacency hypotheses; the geometric no-between row then forces
adjacent positions in `GeometricRotationSystem.geometricOutgoingDartList`. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderInputRowsAt_of_cutPartitionRowsAt_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}
    (cutRows :
      UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a)
    (angularRows :
      GeometricRotationSystem.GraphVertexAngularNoBetweenRows
        C a.1 cutRows.left cutRows.right) :
    SelectedNeighborCutPartitionGeometricOrderInputRowsAt inputs a := by
  classical
  have hleft_canonical : (canonicalGraph C).Adj a.1 cutRows.left := by
    rcases cutRows.left_edge with h | h
    · exact unboundedFrontierEdgeSet_adj h
    · exact canonicalAdj_symm (unboundedFrontierEdgeSet_adj h)
  have hright_canonical : (canonicalGraph C).Adj a.1 cutRows.right := by
    rcases cutRows.right_edge with h | h
    · exact unboundedFrontierEdgeSet_adj h
    · exact canonicalAdj_symm (unboundedFrontierEdgeSet_adj h)
  have hleft_unit : GraphBridge.UnitDistanceAdj C a.1 cutRows.left :=
    ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 cutRows.left).1
      hleft_canonical
  have hright_unit : GraphBridge.UnitDistanceAdj C a.1 cutRows.right :=
    ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 cutRows.right).1
      hright_canonical
  let selectionRow :
      GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
        C a.1 cutRows.left cutRows.right :=
    GeometricRotationSystem.graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
      hleft_unit hright_unit angularRows
  exact
    { left := cutRows.left
      right := cutRows.right
      left_edge := cutRows.left_edge
      right_edge := cutRows.right_edge
      heads_ne := cutRows.heads_ne
      third_neighbor_cutPartitions := cutRows.third_neighbor_cutPartitions
      index := selectionRow.index
      index_succ_lt := selectionRow.index_succ_lt
      left_eq := selectionRow.left_eq
      right_eq := selectionRow.right_eq }

set_option linter.style.longLine false in
/-- Strict smaller source for
`SelectedNeighborCutPartitionGeometricOrderSource`.

This source is pointwise and constructor-free from the downstream dependent
package: each row directly exposes the two actual selected frontier incidences,
the cut-partition residual for third carrier neighbours, and the real adjacent
positions in `geometricOutgoingDartList` for the same two heads. -/
structure SelectedNeighborCutPartitionGeometricOrderInputSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  rows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (SelectedNeighborCutPartitionGeometricOrderInputRowsAt inputs a)

set_option linter.style.longLine false in
/-- Project the pointwise selected-neighbour/cut/geometric input source to the
selected incident-edge/cut-partition rows it names.

The selected heads are not recomputed here: they are the `left` and `right`
heads carried by each pointwise input row. -/
noncomputable def
    selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      SelectedNeighborCutPartitionGeometricOrderInputSource inputs) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
      inputs where
  selectedNeighborRows := fun a =>
    (Classical.choice (source.rows a)).toCutPartitionRowsAt

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-indexrows-from-selected-neighbor`.

The pointwise honest selected-neighbour/cut/geometric input source gives the
primitive sorted outgoing-dart index rows for the exact selected cut rows it
names.  This is a direct projection of the genuine non-wrap
`geometricOutgoingDartList` indices; it introduces no identity order, boundary
cycle, endpoint/no-chord, induced-frontier graph, synthetic enclosure, or
all-adjacent endpoint shortcut. -/
noncomputable def
    S2_agent_20260520_indexrows_from_selected_neighbor_inputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      SelectedNeighborCutPartitionGeometricOrderInputSource inputs) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
      (selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
        (C := C) (inputs := inputs) source) := by
  intro a
  let rows :
      SelectedNeighborCutPartitionGeometricOrderInputRowsAt inputs a :=
    Classical.choice (source.rows a)
  exact
    ⟨rows.index, rows.index_succ_lt,
      by
        simpa [selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource,
          rows, SelectedNeighborCutPartitionGeometricOrderInputRowsAt.toCutPartitionRowsAt]
          using rows.left_eq,
      by
        simpa [selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource,
          rows, SelectedNeighborCutPartitionGeometricOrderInputRowsAt.toCutPartitionRowsAt]
          using rows.right_eq⟩

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_20260520_indexrows_from_selected_neighbor_inputSource`. -/
noncomputable def
    S2_agent_20260520_indexrows_family_from_selected_neighbor_inputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborCutPartitionGeometricOrderInputSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
          (selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
            (C := C) (inputs := inputs) (source C inputs)) := by
  intro m C inputs
  exact
    S2_agent_20260520_indexrows_from_selected_neighbor_inputSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of
`selectedNeighborCutPartitionGeometricOrderInputRowsAt_of_cutPartitionRowsAt_graphVertexAngularNoBetweenRows`. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderInputSource_of_cutPartitionRows_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a)
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexAngularNoBetweenRows
          C a.1 (cutRows a).left (cutRows a).right) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs where
  rows := fun a =>
    ⟨selectedNeighborCutPartitionGeometricOrderInputRowsAt_of_cutPartitionRowsAt_graphVertexAngularNoBetweenRows
      (C := C) (inputs := inputs) (a := a) (cutRows a) (angularRows a)⟩

set_option linter.style.longLine false in
/-- The pointwise honest selected-neighbour/cut-partition/geometric-order
source immediately gives the dependent source theorem.

This is the reduced source statement for the selected-neighbour lane: no
all-adjacent endpoint row, induced frontier graph shortcut, identity angular
order, completed boundary cycle, or synthetic enclosure is used. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderSource_of_inputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      SelectedNeighborCutPartitionGeometricOrderInputSource inputs) :
    SelectedNeighborCutPartitionGeometricOrderSource (C := C) inputs := by
  classical
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
        (C := C) inputs :=
    selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
      (C := C) (inputs := inputs) source
  let indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows := by
    simpa [selectedRows] using
      S2_agent_20260520_indexrows_from_selected_neighbor_inputSource
        (C := C) (inputs := inputs) source
  exact
    ⟨selectedRows,
      ⟨S2_agent_selected_geometric_order_source
        (C := C) (inputs := inputs)
        (selectedRows := selectedRows) indexRows⟩⟩

set_option linter.style.longLine false in
/-- Family form of
`selectedNeighborCutPartitionGeometricOrderSource_of_inputSource`. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderSource_family_of_inputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborCutPartitionGeometricOrderInputSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderSource
          (C := C) inputs := by
  intro m C inputs
  exact
    selectedNeighborCutPartitionGeometricOrderSource_of_inputSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-main-20260520-selected-neighbor-source-inputs`, pointwise
input-source form.

The compact selected carrier-neighbour/geometric-selection source reduces to
the strict pointwise selected-neighbour input rows for the same
`FinitePlanarOuterComponentInputs C`.  Those rows keep the actual
`unboundedFrontierEdgeSet` incidences and the genuine consecutive
`geometricOutgoingDartList` indices together. -/
noncomputable def
    S2_codex_main_20260520_selected_neighbor_source_inputs_of_inputSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (source :
      SelectedNeighborCutPartitionGeometricOrderInputSource inputs) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_agent_20260520_actual_carrier_neighbor_selection_of_cutPartition_indexRows
    (C := C) (inputs := inputs)
    (selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
      (C := C) (inputs := inputs) source)
    (S2_agent_20260520_indexrows_from_selected_neighbor_inputSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Claim `S2-codex-main-20260520-selected-neighbor-source-inputs`.

Same-input strict reduction of the selected actual
`unboundedFrontierEdgeSet` neighbour/geometric-selection source.  The residuals
are exactly the selected cut rows carrying the two real carrier-edge premises,
and honest graph-vertex angular no-between rows for those same heads. -/
noncomputable def S2_codex_main_20260520_selected_neighbor_source_inputs
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a)
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexAngularNoBetweenRows
          C a.1 (cutRows a).left (cutRows a).right) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_codex_main_20260520_selected_neighbor_source_inputs_of_inputSource
    (C := C) inputs
    (selectedNeighborCutPartitionGeometricOrderInputSource_of_cutPartitionRows_graphVertexAngularNoBetweenRows
      (C := C) (inputs := inputs) cutRows angularRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_main_20260520_selected_neighbor_source_inputs`. -/
noncomputable def
    S2_codex_main_20260520_selected_neighbor_source_inputs_family
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 ((cutRows C inputs) a).left
                ((cutRows C inputs) a).right) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_codex_main_20260520_selected_neighbor_source_inputs
      (C := C) inputs (cutRows C inputs) (angularRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-narrow-selected-neighbor-cutpartition-reducer`.

Deleted-neighbour local separation gives the selected cut-partition rows; if
those same selected heads also satisfy genuine graph-vertex angular no-between
rows, the existing pointwise bridge and eraser produce the dependent
selected-neighbour cut-partition/geometric-order source. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderSource_of_localSeparation_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
        C inputs)
    (angularRows :
      let cutRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a :=
        (S2_agent_selected_cutpartition_source_of_localSeparation_20260520
          (C := C) (inputs := inputs) source).selectedNeighborRows
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexAngularNoBetweenRows
          C a.1 (cutRows a).left (cutRows a).right) :
    SelectedNeighborCutPartitionGeometricOrderSource (C := C) inputs := by
  classical
  let cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a :=
    (S2_agent_selected_cutpartition_source_of_localSeparation_20260520
      (C := C) (inputs := inputs) source).selectedNeighborRows
  exact
    selectedNeighborCutPartitionGeometricOrderSource_of_inputSource
      (C := C) (inputs := inputs)
      (selectedNeighborCutPartitionGeometricOrderInputSource_of_cutPartitionRows_graphVertexAngularNoBetweenRows
        (C := C) (inputs := inputs) cutRows
        (by
          intro a
          simpa [cutRows] using angularRows a))

set_option linter.style.longLine false in
/-- A concrete selected carrier-neighbour geometric-selection row fills the
pointwise strict input source.

This is the local eraser from the already honest selected-edge/geometric-order
row: the cut-partition residual is obtained by contradiction from the `only`
field, so no all-adjacent endpoint or induced-frontier graph statement is
introduced. -/
def selectedNeighborCutPartitionGeometricOrderInputRowsAt_of_geometricSelectionRowsAt
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}
    (rows :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
        inputs a) :
    SelectedNeighborCutPartitionGeometricOrderInputRowsAt inputs a where
  left := rows.leftHead
  right := rows.rightHead
  left_edge := rows.left_edge
  right_edge := rows.right_edge
  heads_ne := rows.heads_ne
  third_neighbor_cutPartitions := by
    intro b hb hleft hright
    exact
      False.elim
        (by
          rcases rows.only b hb with hb_left | hb_right
          · exact hleft hb_left
          · exact hright hb_right)
  index := rows.index
  index_succ_lt := rows.index_succ_lt
  left_eq := rfl
  right_eq := rfl

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-selected-neighbor-input-from-carrier`.

The actual selected unbounded-frontier carrier/geometric-selection source fills
the strict pointwise selected-neighbour cut/geometric input source.  The two
selected heads, the selected frontier-edge incidences, the no-third-carrier
cut-partition residual, and the genuine consecutive sorted outgoing-dart
indices are all read from the same carrier row, so the selected heads cannot
drift between independent source families. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs where
  rows := fun a =>
    ⟨selectedNeighborCutPartitionGeometricOrderInputRowsAt_of_geometricSelectionRowsAt
      (C := C) (inputs := inputs) (a := a) (source.rows a)⟩

set_option linter.style.longLine false in
/-- Same reduction, with the selected neighbour rows exposed as the compact
actual-carrier source row. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricNeighborSelectionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs :=
  selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricSelectionInputSource
    (C := C) (inputs := inputs) rows.toGeometricSelectionInputSource

set_option linter.style.longLine false in
/-- Actual local-sector carrier rows plus genuine selected-neighbour geometric
order fill the selected cut/geometric input source.

This is the honest replacement for the too-strong arbitrary-radius local
point-sector leaf: the local-sector rows provide the selected
`unboundedFrontierEdgeSet` heads and the no-third-carrier eraser, while the
geometric rows provide the real consecutive order in
`GeometricRotationSystem.geometricOutgoingDartList` for those same heads. -/
noncomputable def
    S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_localSectorRows_geometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (geometricRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right)) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs :=
  selectedNeighborCutPartitionGeometricOrderInputSource_of_cutPartitionRows_graphVertexAngularNoBetweenRows
    (C := C) (inputs := inputs)
    (fun a => (localSectorRows a).toNeighborPairCutPartitionRowsAt)
    (by
      intro a
      exact
        GeometricRotationSystem.graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
          (Classical.choice (geometricRows a)))

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_localSectorRows_geometricOrderRows`. -/
noncomputable def
    S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_family_of_localSectorRows_geometricOrderRows
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((localSectorRows C inputs) a).left
                  ((localSectorRows C inputs) a).right)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_localSectorRows_geometricOrderRows
      (C := C) (inputs := inputs)
      (localSectorRows C inputs) (geometricRows C inputs)

set_option linter.style.longLine false in
/-- Selected neighbour cut/geometric source directly from the bundled selected
geometric-order rows.

The old local-point-sector consumer is therefore not a source leaf for the
selected input rows: once the actual selected carrier rows and genuine sorted
geometric order are bundled in `selectedRows`, the input source follows
without an arbitrary endpoint/no-chord or global point-sector premise. -/
noncomputable def
    S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs :=
  selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricSelectionInputSource
    (C := C) (inputs := inputs)
    selectedRows.toGeometricSelectionInputSource

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrderRows`. -/
noncomputable def
    S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_family_of_selectedNeighborGeometricOrderRows
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrderRows
      (C := C) (inputs := inputs) (selectedRows C inputs)

set_option linter.style.longLine false in
/-- Family form of
`selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricSelectionInputSource`. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderInputSource_family_of_geometricSelectionInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  intro m C inputs
  exact
    selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of
`selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricNeighborSelectionRows`. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderInputSource_family_of_geometricNeighborSelectionRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  intro m C inputs
  exact
    selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricNeighborSelectionRows
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Actual carrier-neighbour rows fill the selected cut-partition row
pointwise, with the third-neighbour cut residual discharged vacuously.

The two selected heads are obtained from genuine adjacencies in
`unboundedFrontierCarrierGraph C inputs`, hence from actual
`unboundedFrontierEdgeSet` incidences rather than an induced frontier graph or
endpoint-only row. -/
noncomputable def
    unboundedFrontierCarrierNeighborPairCutPartitionRowsAt_of_neighborPairAt
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}
    (rows : UnboundedFrontierCarrierNeighborPairAt inputs a) :
    UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a := by
  have hleft_adj :
      (unboundedFrontierCarrierGraph C inputs).Adj a rows.left :=
    (rows.neighbor_iff rows.left).2 (Or.inl rfl)
  have hright_adj :
      (unboundedFrontierCarrierGraph C inputs).Adj a rows.right :=
    (rows.neighbor_iff rows.right).2 (Or.inr rfl)
  refine
    { left := rows.left.1
      right := rows.right.1
      left_edge := ?_
      right_edge := ?_
      heads_ne := ?_
      third_neighbor_cutPartitions := ?_ }
  · exact (unboundedFrontierCarrierGraph_adj_iff).1 hleft_adj
  · exact (unboundedFrontierCarrierGraph_adj_iff).1 hright_adj
  · intro h
    exact rows.left_ne_right (Subtype.ext h)
  · intro b hb hleft hright
    rcases (rows.neighbor_iff b).1 hb with hb_left | hb_right
    · exact False.elim (hleft (congrArg Subtype.val hb_left))
    · exact False.elim (hright (congrArg Subtype.val hb_right))

set_option linter.style.longLine false in
/-- Family form of
`unboundedFrontierCarrierNeighborPairCutPartitionRowsAt_of_neighborPairAt`. -/
noncomputable def
    unboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows_of_neighborPairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs where
  selectedNeighborRows := fun a =>
    unboundedFrontierCarrierNeighborPairCutPartitionRowsAt_of_neighborPairAt
      (C := C) (inputs := inputs) (a := a) (neighborRows a)

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-selected-cut-partition-source-leaf`.

The selected cut-partition source is reduced to the pure selected incident-edge
pair rows.  Those rows first erase to the exact two neighbours of the actual
`unboundedFrontierCarrierGraph`; the existing neighbour-pair cut-partition
eraser then discharges every third carrier-neighbour branch by contradiction.
No boundary cycle, induced frontier graph, arbitrary cycle, identity angular
order, or endpoint-only all-adjacent shortcut is introduced. -/
noncomputable def
    S2_codex_current_20260520_selected_cut_partition_source_leaf
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  unboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows_of_neighborPairRows
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierNeighborPairRows_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_current_20260520_selected_cut_partition_source_leaf`. -/
noncomputable def
    S2_codex_current_20260520_selected_cut_partition_source_leaf_family
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
          inputs := by
  intro m C inputs
  exact
    S2_codex_current_20260520_selected_cut_partition_source_leaf
      (C := C) (inputs := inputs) (selectedEdgeRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-main-20260520-selected-cutpartition-source`.

Boundary-free two-selected-edge/no-third-germ rows close the selected
cut-partition source for the actual unbounded-frontier carrier.  The selected
heads are backed by real `unboundedFrontierEdgeSet` incidences; the no-third
local germ row is first erased to actual carrier degree two and then to the
selected incident-edge pair rows consumed by the cut-partition source. -/
noncomputable def
    S2_codex_main_20260520_selected_cutpartition_source_of_boundaryFree_twoSelectedEdges_noThirdGerm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun left : Fin n =>
          Exists fun right : Fin n =>
            ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                  (canonicalGraph C).Adj a.1 x ->
                    q ∈ vertexIncidentGermW3 C a.1 x ε ->
                      q ≠ (canonicalGraph C).point a.1 ->
                        x ≠ left ->
                          x ≠ right ->
                            False) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  S2_codex_current_20260520_selected_cut_partition_source_leaf
    (C := C) (inputs := inputs)
    (S2_codex_current_20260520_actual_carrier_degree_two_source_of_final_source
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Claim `S2-agent-selected-cutpartition-source-20260520c`,
neighbour-pair form.

Actual concrete carrier neighbour-pair rows fill the selected-neighbour
cut-partition source directly.  The selected heads are read from actual carrier
adjacencies, hence from genuine `unboundedFrontierEdgeSet` incidences, and the
third-neighbour cut branch is impossible by the same neighbour-pair row. -/
noncomputable def
    S2_agent_selected_cutpartition_source_20260520c_of_neighborPairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  unboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows_of_neighborPairRows
    (C := C) (inputs := inputs) neighborRows

set_option linter.style.longLine false in
/-- Claim `S2-agent-selected-cutpartition-source-20260520c`,
actual carrier degree-two form.

The only input is degree two of the actual
`unboundedFrontierCarrierGraph C inputs`, stated as `neighborFinset.card = 2`.
The existing degree-two selected-edge reducer chooses the two concrete carrier
neighbours and the selected cut-partition wrapper keeps those actual
`unboundedFrontierEdgeSet` incidences. -/
noncomputable def
    S2_agent_selected_cutpartition_source_20260520c_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (hdegree :
      letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
        unboundedFrontierCarrierGraph_decidableAdj C inputs
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  S2_codex_current_20260520_selected_cut_partition_source_leaf
    (C := C) (inputs := inputs)
    (S2_codex_current_20260520_actual_carrier_degree_two_source
      (C := C) (inputs := inputs) hdegree)

set_option linter.style.longLine false in
/-- Claim `S2-agent-selected-cutpartition-source-20260520c`,
local two-germ form.

Pointwise local two-germ rows already name two selected
`unboundedFrontierEdgeSet` incidences at each carrier vertex.  The checked
local-topology-to-cut-row reducer turns those same selected heads into the
pointwise cut-partition rows, then this definition only wraps that family as
the selected-neighbour source. -/
noncomputable def
    S2_agent_selected_cutpartition_source_20260520c_of_localTwoGermRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows.ofCutPartitionRows
    (C := C) (inputs := inputs)
    (S2_agent_cutrows_from_local_topology_20260520av
      (C := C) (inputs := inputs) localTwoGermRows)

set_option linter.style.longLine false in
/-- Claim `S2-agent-selected-cutpartition-source-20260520c`,
local selected-edge/no-third-germ form.

This is the strict local no-third-germ reduction: the source first becomes the
checked local two-germ row, preserving the same actual selected
`unboundedFrontierEdgeSet` heads, and then the local-two-germ cut-partition
wrapper above supplies
`UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs`. -/
noncomputable def
    S2_agent_selected_cutpartition_source_20260520c_of_localSelectedNoThirdGermSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  S2_agent_selected_cutpartition_source_20260520c_of_localTwoGermRows
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_local_two_germ_rows_of_selected_no_third_germ_source
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_main_20260520_selected_cutpartition_source_of_boundaryFree_twoSelectedEdges_noThirdGerm`. -/
noncomputable def
    S2_codex_main_20260520_selected_cutpartition_source_family_of_boundaryFree_twoSelectedEdges_noThirdGerm
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          Exists fun left : Fin m =>
            Exists fun right : Fin m =>
              ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
                (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
              ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
                (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
              left ≠ right ∧
              forall (ε : Real) (q : PlanarInterface.Point) (x : Fin m),
                q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                  q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                    (canonicalGraph C).Adj a.1 x ->
                      q ∈ vertexIncidentGermW3 C a.1 x ε ->
                        q ≠ (canonicalGraph C).point a.1 ->
                          x ≠ left ->
                            x ≠ right ->
                              False) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
          inputs := by
  intro m C inputs
  exact
    S2_codex_main_20260520_selected_cutpartition_source_of_boundaryFree_twoSelectedEdges_noThirdGerm
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Actual carrier-neighbour rows plus honest angular no-between rows produce
the compact geometric-neighbour source rows.

The angular rows are converted to non-wrap neighbouring entries of the genuine
sorted `GeometricRotationSystem.geometricOutgoingDartList`; the required
unit-distance hypotheses are read from actual carrier adjacencies. -/
noncomputable def
    unboundedFrontierCarrierGeometricNeighborSelectionSourceRows_of_neighborPair_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexAngularNoBetweenRows
          C a.1 (neighborRows a).left.1 (neighborRows a).right.1) :
    UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs where
  neighborRows := neighborRows
  consecutiveRows := by
    intro a
    let rows := neighborRows a
    have hleft_carrier :
        (unboundedFrontierCarrierGraph C inputs).Adj a rows.left :=
      (rows.neighbor_iff rows.left).2 (Or.inl rfl)
    have hright_carrier :
        (unboundedFrontierCarrierGraph C inputs).Adj a rows.right :=
      (rows.neighbor_iff rows.right).2 (Or.inr rfl)
    have hleft_canonical :
        (canonicalGraph C).Adj a.1 rows.left.1 :=
      unboundedFrontierCarrierGraph_adj_canonicalAdj hleft_carrier
    have hright_canonical :
        (canonicalGraph C).Adj a.1 rows.right.1 :=
      unboundedFrontierCarrierGraph_adj_canonicalAdj hright_carrier
    have hleft_unit : GraphBridge.UnitDistanceAdj C a.1 rows.left.1 :=
      ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 rows.left.1).1
        hleft_canonical
    have hright_unit : GraphBridge.UnitDistanceAdj C a.1 rows.right.1 :=
      ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 rows.right.1).1
        hright_canonical
    exact
      GeometricRotationSystem.exists_graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
        hleft_unit hright_unit
        (by simpa [rows] using angularRows a)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-geometric-neighbor-rows-current-source`.

Family-level strict reduction of
`UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs` to the
actual carrier neighbour-pair rows plus honest graph-vertex angular no-between
rows for those same two selected heads. -/
noncomputable def
    S2_dyn_20260520_geometric_neighbor_rows_current_source_family
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
          inputs := by
  intro m C inputs
  exact
    unboundedFrontierCarrierGeometricNeighborSelectionSourceRows_of_neighborPair_graphVertexAngularNoBetweenRows
      (C := C) (inputs := inputs)
      (neighborRows C inputs) (angularRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-geometric-selection-source-now`.

Strict reduction of the selected carrier neighbour/geometric-order leaf to
actual carrier-neighbour rows plus honest graph-vertex angular no-between rows
for the same selected heads. -/
noncomputable def
    S2_codex_20260520_geometric_selection_source_now
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexAngularNoBetweenRows
          C a.1 (neighborRows a).left.1 (neighborRows a).right.1) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_dyn_20260520_geometric_neighbor_selection_source
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierGeometricNeighborSelectionSourceRows_of_neighborPair_graphVertexAngularNoBetweenRows
      (C := C) (inputs := inputs) neighborRows angularRows)

set_option linter.style.longLine false in
/-- Same strict source reduction, ending at the selected cut/geometric input
surface consumed by the downstream selected-neighbour route. -/
noncomputable def
    S2_codex_20260520_selected_geometric_order_input_source_now
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexAngularNoBetweenRows
          C a.1 (neighborRows a).left.1 (neighborRows a).right.1) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs :=
  selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricNeighborSelectionRows
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierGeometricNeighborSelectionSourceRows_of_neighborPair_graphVertexAngularNoBetweenRows
      (C := C) (inputs := inputs) neighborRows angularRows)

set_option linter.style.longLine false in
/-- Family form of `S2_codex_20260520_geometric_selection_source_now`. -/
noncomputable def
    S2_codex_20260520_geometric_selection_source_now_family
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_geometric_selection_source_now
      (C := C) (inputs := inputs)
      (neighborRows C inputs) (angularRows C inputs)

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_20260520_selected_geometric_order_input_source_now`. -/
noncomputable def
    S2_codex_20260520_selected_geometric_order_input_source_now_family
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_selected_geometric_order_input_source_now
      (C := C) (inputs := inputs)
      (neighborRows C inputs) (angularRows C inputs)

set_option linter.style.longLine false in
/-- Actual selected carrier-neighbour/geometric-selection rows give the
dependent selected-neighbour source directly.

This is the input-facing eraser for the bundled carrier source: the selected
cut data and the genuine sorted outgoing-list consecutive indices are read
from the same pointwise rows, so callers do not have to separately rebuild a
selected-edge family and then re-align its geometric index rows. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderSource_of_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    SelectedNeighborCutPartitionGeometricOrderSource
      (C := C) inputs :=
  selectedNeighborCutPartitionGeometricOrderSource_of_inputSource
    (C := C) (inputs := inputs)
    (selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Compact carrier-neighbour/geometric rows give the dependent
selected-neighbour source directly. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderSource_of_geometricNeighborSelectionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    SelectedNeighborCutPartitionGeometricOrderSource
      (C := C) inputs :=
  selectedNeighborCutPartitionGeometricOrderSource_of_geometricSelectionInputSource
    (C := C) (inputs := inputs) rows.toGeometricSelectionInputSource

set_option linter.style.longLine false in
/-- Family form of
`selectedNeighborCutPartitionGeometricOrderSource_of_geometricSelectionInputSource`. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderSource_family_of_geometricSelectionInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderSource
          (C := C) inputs := by
  intro m C inputs
  exact
    selectedNeighborCutPartitionGeometricOrderSource_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of
`selectedNeighborCutPartitionGeometricOrderSource_of_geometricNeighborSelectionRows`. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderSource_family_of_geometricNeighborSelectionRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderSource
          (C := C) inputs := by
  intro m C inputs
  exact
    selectedNeighborCutPartitionGeometricOrderSource_of_geometricNeighborSelectionRows
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Actual boundary-sector rows produce the strict pointwise selected-neighbour
input source.

For each carrier vertex, the frontier equivalence selects its boundary index;
the boundary-sector row and genuine geometric order at that same index provide
the two selected frontier-edge incidences and their consecutive non-wrap
positions in the real geometric outgoing list. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderInputSource_of_boundaryVertexExteriorSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C}
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (geometric_order :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C B k)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs where
  rows := by
    intro a
    have hfrontier :
        (canonicalGraph C).point a.1 ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior :=
      mem_unboundedFrontierVertexSet_iff.1 a.2
    let k : Fin B.length :=
      Classical.choose ((frontier_iff_cycle_vertex a.1).1 hfrontier)
    have hk : B.vertex k = a.1 :=
      Classical.choose_spec ((frontier_iff_cycle_vertex a.1).1 hfrontier)
    exact
      ⟨selectedNeighborCutPartitionGeometricOrderInputRowsAt_of_geometricSelectionRowsAt
        (unboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt_of_boundaryVertexExteriorSectorRow_geometricOrder
          (C := C) (inputs := inputs) (B := B) a hk.symm
          (geometric_order k) (sectorRows k))⟩

set_option linter.style.longLine false in
/-- Erase the dependent-pair source form to the selected-neighbour geometric
order source rows consumed by the safe S2 local route. -/
noncomputable def
    selectedNeighborGeometricOrderSourceRows_of_dependentSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : SelectedNeighborCutPartitionGeometricOrderSource
      (C := C) inputs) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
      inputs := by
  classical
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
        inputs := Classical.choose source
  have geometricRows :
      Nonempty
        (UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
          selectedRows) := Classical.choose_spec source
  exact
    S2_codex_20260520_selected_neighbor_geometric_order_source_split
      (C := C) (inputs := inputs) selectedRows
      (Classical.choice geometricRows)

set_option linter.style.longLine false in
/-- Family eraser for the dependent-pair selected-neighbour source form. -/
noncomputable def
    selectedNeighborGeometricOrderSourceRows_family_of_dependentSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborCutPartitionGeometricOrderSource
            (C := C) inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs := by
  intro m C inputs
  exact
    selectedNeighborGeometricOrderSourceRows_of_dependentSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Actual selected carrier-neighbour/geometric-selection rows give the
selected-neighbour geometric-order source rows consumed by the local route.

The proof factors through the dependent selected-neighbour source above, so the
cut rows and sorted-list index rows stay tied to the same pointwise selected
heads. -/
noncomputable def
    selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
      inputs :=
  selectedNeighborGeometricOrderSourceRows_of_dependentSource
    (C := C) (inputs := inputs)
    (selectedNeighborCutPartitionGeometricOrderSource_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Compact carrier-neighbour/geometric rows give the selected-neighbour
geometric-order source rows consumed by the local route. -/
noncomputable def
    selectedNeighborGeometricOrderSourceRows_of_geometricNeighborSelectionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
      inputs :=
  selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
    (C := C) (inputs := inputs) rows.toGeometricSelectionInputSource

set_option linter.style.longLine false in
/-- Family form of
`selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource`. -/
noncomputable def
    selectedNeighborGeometricOrderSourceRows_family_of_geometricSelectionInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs := by
  intro m C inputs
  exact
    selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of
`selectedNeighborGeometricOrderSourceRows_of_geometricNeighborSelectionRows`. -/
noncomputable def
    selectedNeighborGeometricOrderSourceRows_family_of_geometricNeighborSelectionRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs := by
  intro m C inputs
  exact
    selectedNeighborGeometricOrderSourceRows_of_geometricNeighborSelectionRows
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Actual boundary-sector rows produce the dependent selected-neighbour source.

This keeps the selected carrier-neighbour heads and their real geometric
outgoing-list order tied to the same boundary vertex.  The cut-partition row is
filled by contradiction from the boundary-sector `only` field, so no separate
all-adjacent endpoint or induced frontier graph statement is used. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderSource_of_boundaryVertexExteriorSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C}
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (geometric_order :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C B k)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :
    SelectedNeighborCutPartitionGeometricOrderSource
      (C := C) inputs := by
  classical
  let selectedCutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a := by
    intro a
    have hfrontier :
        (canonicalGraph C).point a.1 ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior :=
      mem_unboundedFrontierVertexSet_iff.1 a.2
    let k : Fin B.length :=
      Classical.choose ((frontier_iff_cycle_vertex a.1).1 hfrontier)
    have hk : B.vertex k = a.1 :=
      Classical.choose_spec ((frontier_iff_cycle_vertex a.1).1 hfrontier)
    let rows :
        UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
          inputs a :=
      unboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt_of_boundaryVertexExteriorSectorRow_geometricOrder
        (C := C) (inputs := inputs) (B := B) a hk.symm
        (geometric_order k) (sectorRows k)
    refine
      { left := rows.leftHead
        right := rows.rightHead
        left_edge := rows.left_edge
        right_edge := rows.right_edge
        heads_ne := rows.heads_ne
        third_neighbor_cutPartitions := ?_ }
    intro b hb hleft hright
    exact
      False.elim
        (by
          rcases rows.only b hb with hb_left | hb_right
          · exact hleft hb_left
          · exact hright hb_right)
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
        inputs :=
    { selectedNeighborRows := selectedCutRows }
  refine ⟨selectedRows, ⟨?_⟩⟩
  refine
    { geometricOrderRows := ?_ }
  intro a
  have hfrontier :
      (canonicalGraph C).point a.1 ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior :=
    mem_unboundedFrontierVertexSet_iff.1 a.2
  let k : Fin B.length :=
    Classical.choose ((frontier_iff_cycle_vertex a.1).1 hfrontier)
  have hk : B.vertex k = a.1 :=
    Classical.choose_spec ((frontier_iff_cycle_vertex a.1).1 hfrontier)
  let rows :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt
        inputs a :=
    unboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt_of_boundaryVertexExteriorSectorRow_geometricOrder
      (C := C) (inputs := inputs) (B := B) a hk.symm
      (geometric_order k) (sectorRows k)
  exact
    ⟨by
      simpa [selectedRows, selectedCutRows]
        using rows.toGeometricAngularNeighborSelectionRow⟩

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-boundary-geometric-to-selected-geometric`,
combined source-row form.

Same-boundary actual exterior-sector rows and genuine boundary geometric
rotation-order rows give the selected-neighbour geometric-order source rows.
The pointwise constructor underneath reads the predecessor/successor darts as
adjacent entries of `GeometricRotationSystem.geometricOutgoingDartList`; this
adapter only keeps the actual boundary, frontier equivalence, sector rows, and
geometric rotation rows tied to that same boundary. -/
noncomputable def
    S2_dyn_20260520_boundary_geometric_to_selected_geometric_source_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (geometric_order :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C actualRows.boundary k)
    (sectorRows :
      forall k : Fin actualRows.boundary.length,
        BoundaryVertexExteriorSectorRowsAt inputs actualRows.boundary k) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
      inputs :=
  selectedNeighborGeometricOrderSourceRows_of_dependentSource
    (C := C) (inputs := inputs)
    (selectedNeighborCutPartitionGeometricOrderSource_of_boundaryVertexExteriorSectorRows
      (C := C) (inputs := inputs) (B := actualRows.boundary)
      actualRows.frontier_iff_cycle_vertex geometric_order sectorRows)

set_option linter.style.longLine false in
/-- Pointwise `GraphVertexGeometricAngularNeighborSelectionRow` projection of
`S2_dyn_20260520_boundary_geometric_to_selected_geometric_source_rows`. -/
noncomputable def
    S2_dyn_20260520_boundary_geometric_to_graphVertex_selected_geometric
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (geometric_order :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C actualRows.boundary k)
    (sectorRows :
      forall k : Fin actualRows.boundary.length,
        BoundaryVertexExteriorSectorRowsAt inputs actualRows.boundary k) :
    let sourceRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      S2_dyn_20260520_boundary_geometric_to_selected_geometric_source_rows
        (C := C) (inputs := inputs) actualRows geometric_order sectorRows
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (sourceRows.selectedNeighborRows a).left
            (sourceRows.selectedNeighborRows a).right) := by
  let sourceRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs :=
    S2_dyn_20260520_boundary_geometric_to_selected_geometric_source_rows
      (C := C) (inputs := inputs) actualRows geometric_order sectorRows
  exact sourceRows.geometricOrderRows

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-boundary-geometric-to-selected-geometric`.

Same-boundary actual boundary rows, actual exterior-sector rows, and genuine
boundary geometric rotation-order rows produce the
`UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows` package for the
selected cut-partition rows chosen from those same boundary-sector rows. -/
noncomputable def
    S2_dyn_20260520_boundary_geometric_to_selected_geometric
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (geometric_order :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C actualRows.boundary k)
    (sectorRows :
      forall k : Fin actualRows.boundary.length,
        BoundaryVertexExteriorSectorRowsAt inputs actualRows.boundary k) :
    let sourceRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      S2_dyn_20260520_boundary_geometric_to_selected_geometric_source_rows
        (C := C) (inputs := inputs) actualRows geometric_order sectorRows
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
      sourceRows.toSelectedNeighborCutPartitionSourceRows := by
  let sourceRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs :=
    S2_dyn_20260520_boundary_geometric_to_selected_geometric_source_rows
      (C := C) (inputs := inputs) actualRows geometric_order sectorRows
  exact sourceRows.toSelectedNeighborGeometricOrderRows

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-selected-neighbor-geometric-source-replacement`.

Strict reduction of
`UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource C inputs`
to actual selected unbounded-frontier carrier neighbours and genuine sorted
geometric outgoing-dart order.  It uses the selected incident-edge
cut-partition rows for the carrier neighbours and a real non-wrap consecutive
row in `geometricOutgoingDartList` for those same two heads; it does not use
all-adjacent endpoint/no-chord shortcuts or an identity angular order. -/
noncomputable def
    S2_agent_20260520_selected_neighbor_geometric_source_replacement
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  rows.toGeometricSelectionInputSource

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_20260520_selected_neighbor_geometric_source_replacement`. -/
noncomputable def
    S2_agent_20260520_selected_neighbor_geometric_source_replacement_family
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_selected_neighbor_geometric_source_replacement
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Compatibility name for the pruned Epicurus lane; use
`S2_agent_20260520_selected_neighbor_geometric_source_replacement` for new
source work. -/
noncomputable def
    S2_agent_20260520_selected_neighbor_geometric_source_final
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_agent_20260520_selected_neighbor_geometric_source_replacement
    (C := C) (inputs := inputs) rows

set_option linter.style.longLine false in
/-- Compatibility family form for the pruned Epicurus lane. -/
noncomputable def
    S2_agent_20260520_selected_neighbor_geometric_source_final_family
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_selected_neighbor_geometric_source_replacement
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Boundary-indexed exterior-sector rows and genuine geometric order supply
the carrier neighbour-pair/geometric-selection input source.

For a carrier vertex, the exact frontier equivalence chooses its boundary
index.  The local row at that index then selects the predecessor/successor
boundary darts as consecutive entries in the genuine geometric outgoing list. -/
noncomputable def S2_agent_neighbor_selection_input_20260520ca
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (geometric_order :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow C B k)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs where
  rows := by
    intro a
    have hafrontier :
        (canonicalGraph C).point a.1 ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior :=
      mem_unboundedFrontierVertexSet_iff.1 a.2
    let hk_ex := (frontier_iff_cycle_vertex a.1).1 hafrontier
    let k : Fin B.length := Classical.choose hk_ex
    have hk : B.vertex k = a.1 := Classical.choose_spec hk_ex
    exact
      unboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt_of_boundaryVertexExteriorSectorRow_geometricOrder
        (C := C) (inputs := inputs) (B := B) a (k := k) hk.symm
        (geometric_order k) (sectorRows k)

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-local-selected-source`.

Vertex-star local exterior-sector data plus genuine sorted geometric rotation
order supply the actual selected exterior-neighbour/geometric source.

The local exterior-sector row first builds the primitive boundary-sector rows:
the predecessor/successor edges are promoted to actual
`unboundedFrontierEdgeSet` incidences from the open-segment frontier row, and
the vertex-star/no-between argument gives the local two-germ exclusion.  The
selected source is then read from those same rows, so the carrier-neighbour
heads and their consecutive positions in `geometricOutgoingDartList` remain
pointwise aligned. -/
noncomputable def
    S2_agent_20260520_local_selected_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_edge_openSegment_frontier :
      forall k : Fin B.length,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (B.vertex k))
            ((canonicalGraph C).point
              (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (geometric_order :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C B k)
    (local_exterior_sector :
      forall (k : Fin B.length) (eps : Real) (q : PlanarInterface.Point)
          (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) eps ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj (B.vertex k) x ->
              q ∈ vertexIncidentGermW3 C (B.vertex k) x eps ->
                q ≠ (canonicalGraph C).point (B.vertex k) ->
                x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
                  x ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
                    BoundaryPredSuccPointAngularBetween C B k q) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs := by
  let angularRows :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C B k :=
    S2_agent_angle_order_from_geometric_rotation
      (C := C) (B := B) geometric_order
  let sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
    boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_local_exterior_sector
      (C := C) (inputs := inputs) (B := B)
      angularRows cycle_edge_openSegment_frontier local_exterior_sector
  exact
    S2_agent_neighbor_selection_input_20260520ca
      (C := C) (inputs := inputs) B
      frontier_iff_cycle_vertex geometric_order sectorRows

set_option linter.style.longLine false in
/-- Selected-neighbour geometric-order source rows from the same local
vertex-star exterior-sector data as
`S2_agent_20260520_local_selected_geometricSelectionInputSource`. -/
noncomputable def
    S2_agent_20260520_local_selected_geometricOrderSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_edge_openSegment_frontier :
      forall k : Fin B.length,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (B.vertex k))
            ((canonicalGraph C).point
              (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (geometric_order :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C B k)
    (local_exterior_sector :
      forall (k : Fin B.length) (eps : Real) (q : PlanarInterface.Point)
          (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) eps ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj (B.vertex k) x ->
              q ∈ vertexIncidentGermW3 C (B.vertex k) x eps ->
                q ≠ (canonicalGraph C).point (B.vertex k) ->
                x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
                  x ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
                    BoundaryPredSuccPointAngularBetween C B k q) :
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
      inputs :=
  selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
    (C := C) (inputs := inputs)
    (S2_agent_20260520_local_selected_geometricSelectionInputSource
      (C := C) (inputs := inputs) B frontier_iff_cycle_vertex
      cycle_edge_openSegment_frontier geometric_order local_exterior_sector)

set_option linter.style.longLine false in
/-- Dependent selected-neighbour cut/geometric input source from local
vertex-star exterior-sector data. -/
noncomputable def
    S2_agent_20260520_local_selected_cutPartitionGeometricInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_edge_openSegment_frontier :
      forall k : Fin B.length,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (B.vertex k))
            ((canonicalGraph C).point
              (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (geometric_order :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C B k)
    (local_exterior_sector :
      forall (k : Fin B.length) (eps : Real) (q : PlanarInterface.Point)
          (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) eps ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj (B.vertex k) x ->
              q ∈ vertexIncidentGermW3 C (B.vertex k) x eps ->
                q ≠ (canonicalGraph C).point (B.vertex k) ->
                x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
                  x ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
                    BoundaryPredSuccPointAngularBetween C B k q) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs :=
  selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricSelectionInputSource
    (C := C) (inputs := inputs)
    (S2_agent_20260520_local_selected_geometricSelectionInputSource
      (C := C) (inputs := inputs) B frontier_iff_cycle_vertex
      cycle_edge_openSegment_frontier geometric_order local_exterior_sector)

set_option linter.style.longLine false in
/-- Boundary-sector rows plus actual geometric face-successor rows supply the
compressed carrier-neighbour/geometric-selection source.

The sector row already contains the predecessor/successor angular no-between
payload.  Together with actual `faceSucc` rows, this proves the ordinary
non-wrap geometric rotation order, so callers no longer need to pass a separate
geometric-order source. -/
noncomputable def
    S2_main_geometricSelectionInputSource_of_faceSucc_sectorRows_20260520cb
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C) B)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_agent_neighbor_selection_input_20260520ca
    (C := C) (inputs := inputs) B frontier_iff_cycle_vertex
    (GeometricRotationSystem.S2_agent_geometric_boundary_order_source_of_boundaryVertexAngularNoBetweenRows
      C B faceSuccRows
      (fun k =>
        BoundaryVertexExteriorSectorRowsAt.toBoundaryVertexAngularNoBetweenRows
          (sectorRows k)))
    sectorRows

/-- The geometric-selection input source gives the requested carrier
neighbour-pair family. -/
def unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a :=
  fun a => (source.rows a).toNeighborPairAt

/-- The same geometric-selection input source gives the requested nonempty
geometric angular neighbour-selection family, with left/right read from the
neighbour-pair eraser above. -/
def graphVertexGeometricAngularNeighborSelectionRows_of_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1
          ((unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
            source) a).left.1
          ((unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
            source) a).right.1) := by
  intro a
  exact
    ⟨by
      simpa [unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource,
        UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt.toNeighborPairAt,
        UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt.leftVertex,
        UnboundedFrontierCarrierNeighborPairGeometricSelectionRowsAt.rightVertex]
        using
          (source.rows a).toGeometricAngularNeighborSelectionRow⟩

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-nonwrap-angular-neighbor-row-source`.

The genuine non-wrap consecutive angular-neighbour row for the two selected
carrier-neighbour heads is already contained in the strict geometric-selection
source.  This is the residual exposed by
`S2_dyn_20260520_geometric_selection_neighbor_source`, projected without using
boundary-cycle rows, actual-boundary equivalence rows, an induced-frontier
graph shortcut, arbitrary carrier/cycle data, synthetic enclosure data,
endpoint shortcuts, or identity angular-order shortcuts. -/
noncomputable def S2_dyn_20260520_nonwrap_angular_neighbor_row_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedNeighbors :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1
          ((unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
            selectedNeighbors) a).left.1
          ((unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
            selectedNeighbors) a).right.1) :=
  graphVertexGeometricAngularNeighborSelectionRows_of_geometricSelectionInputSource
    selectedNeighbors

set_option linter.style.longLine false in
/-- Family form of
`S2_dyn_20260520_nonwrap_angular_neighbor_row_source`. -/
noncomputable def
    S2_dyn_20260520_nonwrap_angular_neighbor_row_source_family
    (selectedNeighbors :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          Nonempty
            (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
              C a.1
              ((unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                (selectedNeighbors C inputs)) a).left.1
              ((unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                (selectedNeighbors C inputs)) a).right.1) := by
  intro m C inputs
  exact
    S2_dyn_20260520_nonwrap_angular_neighbor_row_source
      (C := C) (inputs := inputs) (selectedNeighbors C inputs)

set_option linter.style.longLine false in
/-- Dalton's geometric-selection source with the non-wrap angular-neighbour
residual discharged by the selected carrier-neighbour geometric source itself.

This names the exact handoff: the neighbour-pair heads and the consecutive
non-wrap angular row are both projected from the same strict local source. -/
noncomputable def
    S2_dyn_20260520_geometric_selection_neighbor_source_of_nonwrap_angular_neighbor_row_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedNeighbors :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_dyn_20260520_geometric_selection_neighbor_source
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
      selectedNeighbors)
    (S2_dyn_20260520_nonwrap_angular_neighbor_row_source
      (C := C) (inputs := inputs) selectedNeighbors)

/-- Bundled output for the paired neighbour-pair and geometric-selection
families.  The first field is data, while the second is proposition-valued, so
using a structure avoids coercing the pair through `And` or `Prod`. -/
structure UnboundedFrontierCarrierNeighborPairGeometricSelectionFamilies
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  neighborRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a
  selectionRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (neighborRows a).left.1 (neighborRows a).right.1)

/-- Claim `S2-agent-neighbor-pair-selection-source-20260520by`.

The pair of residual families is reduced to one strict local source: at each
unbounded-frontier carrier vertex, choose two actual selected carrier edges
whose heads are adjacent in the genuine sorted geometric outgoing-dart list,
and prove that every actual carrier neighbour is one of those two heads. -/
def S2_agent_neighbor_pair_selection_source_20260520by
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionFamilies
      inputs := by
  exact
    { neighborRows :=
        unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
          source
      selectionRows :=
        graphVertexGeometricAngularNeighborSelectionRows_of_geometricSelectionInputSource
          source }

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-neighbor-pair-selection-source`.

Actual local-sector rows for the concrete unbounded-frontier carrier, together
with genuine non-wrap sorted-list selection rows for those same selected heads,
strictly reduce the combined neighbour-pair/geometric-selection input source.

The neighbour-pair half is the existing local-sector eraser, so the selected
heads remain backed by actual `unboundedFrontierEdgeSet` incidences and the
`only` field of the local-sector rows.  The only additional residual is the
real geometric consecutive row in `geometricOutgoingDartList` for those same
heads. -/
noncomputable def S2_dyn_20260520_neighbor_pair_selection_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right)) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_dyn_20260520_geometric_selection_neighbor_source
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierNeighborPairRows_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows)
    (by
      intro a
      exact
        ⟨by
          simpa [
            unboundedFrontierCarrierNeighborPairRows_of_localSectorRows,
            UnboundedFrontierCarrierLocalSectorRowsAt.toNeighborPairAt,
            UnboundedFrontierCarrierLocalSectorRowsAt.leftVertex,
            UnboundedFrontierCarrierLocalSectorRowsAt.rightVertex]
            using Classical.choice (selectionRows a)⟩)

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-geometric-selection-input-source`.

Strict reduction of the bundled geometric-selection input source to actual
carrier-neighbour rows plus the genuine non-wrap consecutive row in
`GeometricRotationSystem.geometricOutgoingDartList` for those same selected
heads. -/
noncomputable def
    S2_codex_20260520_geometric_selection_input_source_of_neighborRows_geometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (geometricRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (neighborRows a).left.1 (neighborRows a).right.1)) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_dyn_20260520_geometric_selection_neighbor_source
    (C := C) (inputs := inputs) neighborRows geometricRows

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_20260520_geometric_selection_input_source_of_neighborRows_geometricOrderRows`. -/
noncomputable def
    S2_codex_20260520_geometric_selection_input_source_family_of_neighborRows_geometricOrderRows
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((neighborRows C inputs) a).left.1
                  ((neighborRows C inputs) a).right.1)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_geometric_selection_input_source_of_neighborRows_geometricOrderRows
      (C := C) (inputs := inputs)
      (neighborRows C inputs) (geometricRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-geometric-selection-input-source`.

Actual local-sector rows for the unbounded-frontier carrier plus the genuine
sorted-list consecutive row for their two selected heads strictly reduce the
bundled geometric-selection input source. -/
noncomputable def
    S2_codex_20260520_geometric_selection_input_source_of_localSectorRows_geometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (geometricRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right)) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_dyn_20260520_neighbor_pair_selection_source
    (C := C) (inputs := inputs) localSectorRows geometricRows

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_20260520_geometric_selection_input_source_of_localSectorRows_geometricOrderRows`. -/
noncomputable def
    S2_codex_20260520_geometric_selection_input_source_family_of_localSectorRows_geometricOrderRows
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((localSectorRows C inputs) a).left
                  ((localSectorRows C inputs) a).right)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_geometric_selection_input_source_of_localSectorRows_geometricOrderRows
      (C := C) (inputs := inputs)
      (localSectorRows C inputs) (geometricRows C inputs)

/-- A concrete neighbour-pair row rules out every third nearby frontier germ
once adjacent frontier endpoints are known to be actual
`unboundedFrontierEdgeSet` edges.

The closed-germ endpoint case is handled by the endpoint incident-edge source;
the relative-interior case is handled by the checked
`InteriorFrontierEdgeCarrierMembershipSource`.  In both cases the germ edge
becomes an actual carrier edge, and the neighbour-pair row forces its head to
be one of the two selected carrier neighbours. -/
theorem boundaryFree_third_frontier_germ_impossible_of_neighborPair_incidentEdge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
    (P : UnboundedFrontierCarrierNeighborPairAt inputs a)
    {ε : Real} {q : PlanarInterface.Point} {x : Fin n}
    (_hqball : q ∈ Metric.ball ((canonicalGraph C).point a.1) ε)
    (hqfrontier :
      q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (hadj : (canonicalGraph C).Adj a.1 x)
    (hgerm : q ∈ vertexIncidentGermW3 C a.1 x ε)
    (hqcenter : q ≠ (canonicalGraph C).point a.1)
    (hx_left : x ≠ P.left.1)
    (hx_right : x ≠ P.right.1) :
    False := by
  let hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  have hsource : InteriorFrontierEdgeCarrierMembershipSource C inputs :=
    interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
  have hfrontier_a :
      (canonicalGraph C).point a.1 ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior :=
    mem_unboundedFrontierVertexSet_iff.1 a.2
  have hcarrier_head
      (hxmem : x ∈ unboundedFrontierVertexSet C inputs)
      (hedge :
        (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
      False := by
    let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
      ⟨x, hxmem⟩
    have hab : (unboundedFrontierCarrierGraph C inputs).Adj a b :=
      (unboundedFrontierCarrierGraph_adj_iff).2 hedge
    have hb : b = P.left ∨ b = P.right := (P.neighbor_iff b).1 hab
    rcases hb with hb | hb
    · exact hx_left (congrArg Subtype.val hb)
    · exact hx_right (congrArg Subtype.val hb)
  rcases hgerm with ⟨_hqball, hqseg⟩
  rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hqseg with
    hq_left | hq_right | hq_open
  · exact hqcenter hq_left
  · have hxfrontier :
        (canonicalGraph C).point x ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior := by
      simpa [hq_right] using hqfrontier
    exact
      hcarrier_head
        (mem_unboundedFrontierVertexSet_iff.2 hxfrontier)
        (incident_edge hadj hfrontier_a hxfrontier)
  · rcases hadj with hadj_forward | hadj_backward
    · have hedge_ordered :
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs :=
        hsource (e := (a.1, x)) (p := q)
          hadj_forward hq_open hqfrontier
      have hxmem : x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole hedge_ordered).2
      exact hcarrier_head hxmem (Or.inl hedge_ordered)
    · have hedge_ordered :
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
        hsource (e := (x, a.1)) (p := q)
          hadj_backward (inOpenSegment_symm hq_open) hqfrontier
      have hxmem : x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole hedge_ordered).1
      exact hcarrier_head hxmem (Or.inr hedge_ordered)

/-- Point-ray third-germ source from the actual incident-edge and carrier
neighbour-pair rows.

Any noncenter frontier point in a third incident germ would make that germ an
actual unbounded-frontier carrier edge.  The neighbour-pair row then forces its
head to be one of the two selected carrier heads, contradicting the
third-germ hypotheses; the requested point-sector conclusion follows from the
empty case. -/
theorem boundaryFreePointThirdGermRows_of_neighborPair_incidentEdge_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
      q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
        q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
          (canonicalGraph C).Adj a.1 x ->
            q ∈ vertexIncidentGermW3 C a.1 x ε ->
              q ≠ (canonicalGraph C).point a.1 ->
                x ≠ (neighborRows a).left.1 ->
                  x ≠ (neighborRows a).right.1 ->
                    BoundaryFreeGraphVertexPointAngularBetween C a.1
                      (neighborRows a).left.1 (neighborRows a).right.1 q := by
  intro a ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
  exact False.elim
    (boundaryFree_third_frontier_germ_impossible_of_neighborPair_incidentEdge
      (C := C) (inputs := inputs) incident_edge a (neighborRows a)
      hqball hqfrontier hadj hgerm hqcenter hx_left hx_right)

set_option linter.style.longLine false in
/-- A concrete neighbour-pair row rules out every third nearby frontier germ
from the sharper endpoint-only/no-chord row.

The relative-interior branch is still promoted to the actual
`unboundedFrontierEdgeSet` by the checked interior-frontier-edge source.  The
closed endpoint branch does not promote arbitrary adjacent frontier endpoints
to frontier edges; it only uses the no-chord statement that such an endpoint
must be one of the two selected carrier neighbours. -/
theorem boundaryFree_third_frontier_germ_impossible_of_neighborPair_endpointOnly
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
    (P : UnboundedFrontierCarrierNeighborPairAt inputs a)
    (endpoint_only :
      forall (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x = P.left.1 ∨ x = P.right.1)
    {ε : Real} {q : PlanarInterface.Point} {x : Fin n}
    (_hqball : q ∈ Metric.ball ((canonicalGraph C).point a.1) ε)
    (hqfrontier :
      q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (hadj : (canonicalGraph C).Adj a.1 x)
    (hgerm : q ∈ vertexIncidentGermW3 C a.1 x ε)
    (hqcenter : q ≠ (canonicalGraph C).point a.1)
    (hx_left : x ≠ P.left.1)
    (hx_right : x ≠ P.right.1) :
    False := by
  let hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  have hsource : InteriorFrontierEdgeCarrierMembershipSource C inputs :=
    interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
  have hcarrier_head
      (hxmem : x ∈ unboundedFrontierVertexSet C inputs)
      (hedge :
        (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
      False := by
    let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
      ⟨x, hxmem⟩
    have hab : (unboundedFrontierCarrierGraph C inputs).Adj a b :=
      (unboundedFrontierCarrierGraph_adj_iff).2 hedge
    have hb : b = P.left ∨ b = P.right := (P.neighbor_iff b).1 hab
    rcases hb with hb | hb
    · exact hx_left (congrArg Subtype.val hb)
    · exact hx_right (congrArg Subtype.val hb)
  rcases hgerm with ⟨_hqball, hqseg⟩
  rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hqseg with
    hq_left | hq_right | hq_open
  · exact hqcenter hq_left
  · have hxfrontier :
        (canonicalGraph C).point x ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior := by
      simpa [hq_right] using hqfrontier
    rcases endpoint_only x hadj hxfrontier with hx | hx
    · exact hx_left hx
    · exact hx_right hx
  · rcases hadj with hadj_forward | hadj_backward
    · have hedge_ordered :
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs :=
        hsource (e := (a.1, x)) (p := q)
          hadj_forward hq_open hqfrontier
      have hxmem : x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole hedge_ordered).2
      exact hcarrier_head hxmem (Or.inl hedge_ordered)
    · have hedge_ordered :
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
        hsource (e := (x, a.1)) (p := q)
          hadj_backward (inOpenSegment_symm hq_open) hqfrontier
      have hxmem : x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          hwhole hedge_ordered).1
      exact hcarrier_head hxmem (Or.inr hedge_ordered)

set_option linter.style.longLine false in
/-- Point-ray third-germ source from the actual carrier-neighbour pairs and
the endpoint-only/no-chord row.

This is the replacement for the older adjacent-frontier-endpoint incident
source on the local-angular route. -/
theorem boundaryFreePointThirdGermRows_of_neighborPair_endpointOnly_source
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
            x = (neighborRows a).left.1 ∨ x = (neighborRows a).right.1) :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
      q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
        q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
          (canonicalGraph C).Adj a.1 x ->
            q ∈ vertexIncidentGermW3 C a.1 x ε ->
              q ≠ (canonicalGraph C).point a.1 ->
                x ≠ (neighborRows a).left.1 ->
                  x ≠ (neighborRows a).right.1 ->
                    BoundaryFreeGraphVertexPointAngularBetween C a.1
                      (neighborRows a).left.1 (neighborRows a).right.1 q := by
  intro a ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
  exact False.elim
    (boundaryFree_third_frontier_germ_impossible_of_neighborPair_endpointOnly
      (C := C) (inputs := inputs) a (neighborRows a)
      (endpoint_only a) hqball hqfrontier hadj hgerm hqcenter
      hx_left hx_right)

/-- Claim `S2-agent-point-third-germ-source-20260520by`.

Family-level source for the point-ray third-germ row consumed by
`minimalFailureExactActualTopologyFieldsTarget_of_bx_pointThirdGerm_successorPoint`.
It reduces that row to the adjacent-endpoint incident-edge source and the
actual carrier neighbour-pair rows, using only local frontier/carrier
incidence. -/
theorem S2_agent_point_third_germ_source_of_neighborPair_incidentEdge_20260520by
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
            (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
          q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
              (canonicalGraph C).Adj a.1 x ->
                q ∈ vertexIncidentGermW3 C a.1 x ε ->
                  q ≠ (canonicalGraph C).point a.1 ->
                    x ≠ ((neighborRows C inputs) a).left.1 ->
                      x ≠ ((neighborRows C inputs) a).right.1 ->
                        BoundaryFreeGraphVertexPointAngularBetween C a.1
                          ((neighborRows C inputs) a).left.1
                          ((neighborRows C inputs) a).right.1 q := by
  intro n C inputs
  exact
    boundaryFreePointThirdGermRows_of_neighborPair_incidentEdge_source
      (C := C) (inputs := inputs) (incident_edge C inputs)
      (neighborRows C inputs)

/-- Pointwise local two-germ rows from actual carrier-neighbour pairs and the
finite-plane incident-edge source.

The proof uses the real `unboundedFrontierEdgeSet` edges selected by the
carrier graph.  The only local topology step is the vertex-star isolation
inside `unboundedFrontierCarrierLocalTwoGermRowsAt_of_no_third_germ`: every
nearby frontier point is first assigned to an incident unit-edge germ, and a
third germ is impossible because it would select a third concrete carrier
neighbour. -/
noncomputable def localTwoGermRows_of_neighborPairRows_incidentEdge_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  classical
  intro a
  let P : UnboundedFrontierCarrierNeighborPairAt inputs a := neighborRows a
  let left : Fin n := P.left.1
  let right : Fin n := P.right.1
  have hleft_adj : (unboundedFrontierCarrierGraph C inputs).Adj a P.left :=
    (P.neighbor_iff P.left).2 (Or.inl rfl)
  have hright_adj : (unboundedFrontierCarrierGraph C inputs).Adj a P.right :=
    (P.neighbor_iff P.right).2 (Or.inr rfl)
  have hleft_edge :
      (a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [left] using (unboundedFrontierCarrierGraph_adj_iff).1 hleft_adj
  have hright_edge :
      (a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [right] using (unboundedFrontierCarrierGraph_adj_iff).1 hright_adj
  have hheads_ne : left ≠ right := by
    intro h
    exact P.left_ne_right (Subtype.ext h)
  exact
    unboundedFrontierCarrierLocalTwoGermRowsAt_of_no_third_germ
      hleft_edge hright_edge hheads_ne
      (by
        intro ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
        exact
          boundaryFree_third_frontier_germ_impossible_of_neighborPair_incidentEdge
            (C := C) (inputs := inputs) incident_edge a P
            hqball hqfrontier hadj hgerm hqcenter
            (by simpa [left] using hx_left)
            (by simpa [right] using hx_right))

/-- Claim `S2-agent-local-two-germ-from-inputs-20260520aw`.

This is the named boundary-free source for Popper's reduced target
`forall a, UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a`.  It avoids
completed cycle rows, actual-boundary rows, induced/arbitrary cycles, convex
hulls, identity angular order, and synthetic enclosure: the residual inputs
are exactly the concrete incident `unboundedFrontierEdgeSet` endpoint row and
the actual carrier neighbour-pair row. -/
noncomputable def S2_agent_local_two_germ_from_inputs_20260520aw
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
  localTwoGermRows_of_neighborPairRows_incidentEdge_source
    (C := C) (inputs := inputs) incident_edge neighborRows

set_option linter.style.longLine false in
/-- Boundary-free local two-germ rows from the actual carrier neighbour-pair
source alone.

The local ball is chosen using the pointwise vertex-star isolation theorem,
which gives an open-segment incident edge for every non-centre frontier point
near the carrier vertex.  The fixed-side interior-edge theorem then promotes
that open segment to an actual `unboundedFrontierEdgeSet` edge, so the concrete
carrier neighbour-pair row forces the edge head to be one of the two selected
neighbours.  This avoids the stronger adjacent-frontier-endpoint incident-edge
source used by the older closed-germ reducer. -/
noncomputable def localTwoGermRows_of_neighborPairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  classical
  intro a
  let P : UnboundedFrontierCarrierNeighborPairAt inputs a := neighborRows a
  let left : Fin n := P.left.1
  let right : Fin n := P.right.1
  have hleft_adj : (unboundedFrontierCarrierGraph C inputs).Adj a P.left :=
    (P.neighbor_iff P.left).2 (Or.inl rfl)
  have hright_adj : (unboundedFrontierCarrierGraph C inputs).Adj a P.right :=
    (P.neighbor_iff P.right).2 (Or.inr rfl)
  have hleft_edge :
      (a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [left] using (unboundedFrontierCarrierGraph_adj_iff).1 hleft_adj
  have hright_edge :
      (a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [right] using (unboundedFrontierCarrierGraph_adj_iff).1 hright_adj
  have hheads_ne : left ≠ right := by
    intro h
    exact P.left_ne_right (Subtype.ext h)
  let eps : Real :=
    Classical.choose
      (exists_ball_forall_unboundedExterior_frontier_mem_incident_inOpenSegment_of_vertex_ne
        C inputs a.1)
  have heps_spec :
      0 < eps ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball ((canonicalGraph C).point a.1) eps ->
            q ≠ (canonicalGraph C).point a.1 ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                Exists fun w : Fin n =>
                  (canonicalGraph C).Adj a.1 w ∧
                    PlanarInterface.InOpenSegment q
                      ((canonicalGraph C).point a.1)
                      ((canonicalGraph C).point w) :=
    Classical.choose_spec
      (exists_ball_forall_unboundedExterior_frontier_mem_incident_inOpenSegment_of_vertex_ne
        C inputs a.1)
  have hstar :
      forall q : PlanarInterface.Point,
        q ∈ Metric.ball ((canonicalGraph C).point a.1) eps ->
          q ≠ (canonicalGraph C).point a.1 ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
              Exists fun w : Fin n =>
                (canonicalGraph C).Adj a.1 w ∧
                  PlanarInterface.InOpenSegment q
                    ((canonicalGraph C).point a.1)
                    ((canonicalGraph C).point w) :=
    heps_spec.2
  refine
    { left := left
      right := right
      left_edge := hleft_edge
      right_edge := hright_edge
      heads_ne := hheads_ne
      local_two_germ := ?_ }
  refine ⟨eps, heps_spec.1, ?_⟩
  intro q hqball hqfrontier
  by_cases hqcenter : q = (canonicalGraph C).point a.1
  · left
    rw [hqcenter]
    exact
      ⟨by simpa [Metric.mem_ball] using heps_spec.1,
        left_mem_closedSegment _ _⟩
  rcases hstar q hqball hqcenter hqfrontier with ⟨x, hadj, hqopen⟩
  have hsource : InteriorFrontierEdgeCarrierMembershipSource C inputs :=
    interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
  have hcarrier :
      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    rcases hadj with hadj_forward | hadj_backward
    · left
      exact hsource (e := (a.1, x)) (p := q)
        hadj_forward hqopen hqfrontier
    · right
      exact hsource (e := (x, a.1)) (p := q)
        hadj_backward (inOpenSegment_symm hqopen) hqfrontier
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
  have hb : b = P.left ∨ b = P.right := (P.neighbor_iff b).1 hab
  rcases hb with hb | hb
  · left
    have hx_left : x = left := by
      simpa [b, left] using congrArg Subtype.val hb
    exact ⟨hqball, by simpa [hx_left] using inOpenSegment_mem_closedSegment hqopen⟩
  · right
    have hx_right : x = right := by
      simpa [b, right] using congrArg Subtype.val hb
    exact ⟨hqball, by simpa [hx_right] using inOpenSegment_mem_closedSegment hqopen⟩

/-- Claim `S2-agent-local-two-germ-neighbor-only-20260520ax`.

Concrete carrier neighbour-pair rows alone provide the pointwise local
two-germ source used by S2. -/
noncomputable def S2_agent_local_two_germ_neighbor_only_20260520ax
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
  localTwoGermRows_of_neighborPairRows
    (C := C) (inputs := inputs) neighborRows

/-- Claim `S2-worker-20260520-local-two-germ-source`.

Strict reduction of the pointwise local two-germ source to the sharp
cut-partition input surface for the actual unbounded-frontier carrier.  The
input source first gives the concrete carrier-neighbour pair rows via the
checked no-cut eraser, and the existing local-star isolation argument then
promotes nearby frontier germs to the two selected `unboundedFrontierEdgeSet`
carrier heads. -/
noncomputable def
    S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
  localTwoGermRows_of_neighborPairRows
    (C := C) (inputs := inputs)
    (S2_agent_frontier_neighbor_pair_input_20260520ax_neighborPairRows
      source)

/-- Claim `S2-agent-local-angular-real-source-20260520at`.

The real pointwise local angular source consumed by
`S2_agent_local_sector_family_from_inputs_20260520ae`: at each concrete
unbounded-frontier carrier vertex, take the two actual neighbours from the
carrier neighbour-pair row, recover their actual incident
`unboundedFrontierEdgeSet` edges, attach the honest boundary-free angular
no-between row, and discharge every third nearby frontier germ by showing it is
impossible. -/
noncomputable def S2_agent_local_angular_real_source_20260520at
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        BoundaryFreeGraphVertexAngularNoBetweenRows C a.1
          (neighborRows a).left.1 (neighborRows a).right.1) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Exists fun left : Fin n =>
        Exists fun right : Fin n =>
          ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
            (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
          ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
            (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
          left ≠ right ∧
          BoundaryFreeGraphVertexAngularNoBetweenRows C a.1 left right ∧
          forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      x ≠ left ->
                        x ≠ right ->
                          BoundaryFreeGraphVertexAngularBetween
                            C a.1 left right x := by
  intro a
  let P : UnboundedFrontierCarrierNeighborPairAt inputs a := neighborRows a
  let left : Fin n := P.left.1
  let right : Fin n := P.right.1
  have hleft_adj : (unboundedFrontierCarrierGraph C inputs).Adj a P.left :=
    (P.neighbor_iff P.left).2 (Or.inl rfl)
  have hright_adj : (unboundedFrontierCarrierGraph C inputs).Adj a P.right :=
    (P.neighbor_iff P.right).2 (Or.inr rfl)
  have hleft_edge :
      (a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [left] using (unboundedFrontierCarrierGraph_adj_iff).1 hleft_adj
  have hright_edge :
      (a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [right] using (unboundedFrontierCarrierGraph_adj_iff).1 hright_adj
  have hheads_ne : left ≠ right := by
    intro h
    exact P.left_ne_right (Subtype.ext h)
  refine ⟨left, right, hleft_edge, hright_edge, hheads_ne, ?_, ?_⟩
  · simpa [P, left, right] using angularRows a
  · intro ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
    exact False.elim
      (boundaryFree_third_frontier_germ_impossible_of_neighborPair_incidentEdge
        (C := C) (inputs := inputs) incident_edge a P
        hqball hqfrontier hadj hgerm hqcenter
        (by simpa [left] using hx_left)
        (by simpa [right] using hx_right))

/-- Claim `S2-agent-local-sector-family-from-inputs-20260520ae`.

Input-only pointwise local-sector family from finite-plane local
star/angular sector rows.  The source chooses the two actual incident
unbounded-frontier edges at each carrier vertex, supplies the honest local
angular no-between row for those two darts, and proves that any third nearby
frontier germ points into that open angular sector.

No actual-boundary rows, final S2 rows, arbitrary cycles, or synthetic
enclosure are used in this eraser; the remaining primitive is exactly the
pointwise graph-vertex angular source row. -/
noncomputable def S2_agent_local_sector_family_from_inputs_20260520ae
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun left : Fin n =>
          Exists fun right : Fin n =>
            ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
              (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
            BoundaryFreeGraphVertexAngularNoBetweenRows C a.1 left right ∧
            forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
              q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
                q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                  (canonicalGraph C).Adj a.1 x ->
                    q ∈ vertexIncidentGermW3 C a.1 x ε ->
                      q ≠ (canonicalGraph C).point a.1 ->
                        x ≠ left ->
                          x ≠ right ->
                            BoundaryFreeGraphVertexAngularBetween
                              C a.1 left right x) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  classical
  intro a
  let left : Fin n := Classical.choose (source a)
  let right : Fin n := Classical.choose (Classical.choose_spec (source a))
  have hsource :
      ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
        ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
        left ≠ right ∧
        BoundaryFreeGraphVertexAngularNoBetweenRows C a.1 left right ∧
        forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
          q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
              (canonicalGraph C).Adj a.1 x ->
                q ∈ vertexIncidentGermW3 C a.1 x ε ->
                  q ≠ (canonicalGraph C).point a.1 ->
                    x ≠ left ->
                      x ≠ right ->
                        BoundaryFreeGraphVertexAngularBetween
                          C a.1 left right x :=
    Classical.choose_spec (Classical.choose_spec (source a))
  exact
    (unboundedFrontierCarrierLocalTwoGermRowsAt_of_no_third_germ
      hsource.1 hsource.2.1 hsource.2.2.1
      (by
        intro ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
        have hx_unit : GraphBridge.UnitDistanceAdj C a.1 x :=
          ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 x).1 hadj
        exact
            (hsource.2.2.2.1.no_between x hx_unit hx_left hx_right)
            (hsource.2.2.2.2 ε q x hqball hqfrontier hadj hgerm
              hqcenter hx_left hx_right))).toLocalSectorRowsAt

/-- Boundary-free local-sector source in the sharp geometric-angular form.

For each actual unbounded-frontier vertex, the row chooses two selected
incident `unboundedFrontierEdgeSet` edges, proves that their heads occur as a
consecutive non-wrap pair in the genuine sorted geometric outgoing-dart list,
and proves the local third-germ angular row for nearby frontier points. -/
abbrev BoundaryFreeLocalSectorGeometricAngularSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    Exists fun left : Fin n =>
      Exists fun right : Fin n =>
        ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
        ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
        left ≠ right ∧
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 left right) ∧
          forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      x ≠ left ->
                        x ≠ right ->
                          BoundaryFreeGraphVertexAngularBetween
                            C a.1 left right x

/-- Skolemized input rows for the sharp boundary-free local angular source.

This is the local-star/angular/frontier-germ residual in constructor form:
for every unbounded-frontier vertex it names two actual incident
`unboundedFrontierEdgeSet` heads, supplies a nonempty consecutive non-wrap row
in the genuine sorted geometric outgoing-dart list, and supplies the local
third-germ angular row for nearby frontier points. -/
abbrev BoundaryFreeLocalSectorGeometricAngularInputRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  Exists fun left :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} -> Fin n =>
    Exists fun right :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} -> Fin n =>
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        left a ≠ right a) ∧
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (left a) (right a))) ∧
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ left a ->
                    x ≠ right a ->
                      BoundaryFreeGraphVertexAngularBetween
                        C a.1 (left a) (right a) x

/-- The Skolemized local-star/angular/frontier-germ rows erase to the sharp
boundary-free local angular source. -/
noncomputable def boundaryFreeLocalSectorGeometricAngularSource_of_inputRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeLocalSectorGeometricAngularInputRows inputs) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  classical
  intro a
  let left :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} -> Fin n :=
    Classical.choose rows
  let right :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} -> Fin n :=
    Classical.choose (Classical.choose_spec rows)
  have hrows :
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        left a ≠ right a) ∧
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (left a) (right a))) ∧
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ left a ->
                    x ≠ right a ->
                      BoundaryFreeGraphVertexAngularBetween
                        C a.1 (left a) (right a) x :=
    Classical.choose_spec (Classical.choose_spec rows)
  exact
    ⟨left a, right a, hrows.1 a, hrows.2.1 a, hrows.2.2.1 a,
      hrows.2.2.2.1 a, hrows.2.2.2.2 a⟩

/-- Carrier-neighbour rows, together with the actual sorted-list angular
selection row and local third-germ angular row, supply the Skolemized input
rows.  The produced heads are still discharged as concrete
`unboundedFrontierEdgeSet` incidences via `unboundedFrontierCarrierGraph_adj_iff`. -/
noncomputable def
    boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_thirdGerm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (neighborRows a).left.1 (neighborRows a).right.1))
    (thirdGermRows :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ (neighborRows a).left.1 ->
                    x ≠ (neighborRows a).right.1 ->
                      BoundaryFreeGraphVertexAngularBetween C a.1
                        (neighborRows a).left.1 (neighborRows a).right.1 x) :
    BoundaryFreeLocalSectorGeometricAngularInputRows inputs := by
  classical
  refine
    ⟨fun a => (neighborRows a).left.1,
      fun a => (neighborRows a).right.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    have hleft_adj :
        (unboundedFrontierCarrierGraph C inputs).Adj a (neighborRows a).left :=
      ((neighborRows a).neighbor_iff (neighborRows a).left).2 (Or.inl rfl)
    exact (unboundedFrontierCarrierGraph_adj_iff).1 hleft_adj
  · intro a
    have hright_adj :
        (unboundedFrontierCarrierGraph C inputs).Adj a (neighborRows a).right :=
      ((neighborRows a).neighbor_iff (neighborRows a).right).2 (Or.inr rfl)
    exact (unboundedFrontierCarrierGraph_adj_iff).1 hright_adj
  · intro a h
    exact (neighborRows a).left_ne_right (Subtype.ext h)
  · intro a
    exact selectionRows a
  · intro a ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
    exact
      thirdGermRows a ε q x hqball hqfrontier hadj hgerm hqcenter
        hx_left hx_right

/-- Variant of
`boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_thirdGerm`
where the third-germ input is the geometric point-ray exterior-sector row.
The graph-dart angular row is recovered from the incident-germ angle equality. -/
noncomputable def
    boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_pointThirdGerm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (neighborRows a).left.1 (neighborRows a).right.1))
    (pointThirdGermRows :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ (neighborRows a).left.1 ->
                    x ≠ (neighborRows a).right.1 ->
                      BoundaryFreeGraphVertexPointAngularBetween C a.1
                        (neighborRows a).left.1 (neighborRows a).right.1 q) :
    BoundaryFreeLocalSectorGeometricAngularInputRows inputs := by
  exact
    boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_thirdGerm
      (C := C) (inputs := inputs) neighborRows selectionRows
      (boundaryFreeThirdGermAngularRows_of_pointAngularRows
        (C := C) (inputs := inputs)
        (left := fun a => (neighborRows a).left.1)
        (right := fun a => (neighborRows a).right.1)
        pointThirdGermRows)

set_option linter.style.longLine false in
/-- Claim `S2-agent-ci-local-angular-neighbor-source`.

Pointwise reducer for the current CI route.  The residual source is exactly a
concrete carrier-neighbour/geometric-selection row at each actual
unbounded-frontier vertex, plus the adjacent-frontier endpoint selected-edge
row needed to rule out the closed-germ endpoint case.  The selected local heads
therefore come from genuine `unboundedFrontierEdgeSet` neighbours and the
angular-selection witness is a non-wrap consecutive pair in the real sorted
geometric outgoing-dart list. -/
noncomputable def S2_agent_ci_local_angular_neighbor_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  let neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a :=
    unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
      geometricSelection
  let selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (neighborRows a).left.1 (neighborRows a).right.1) :=
    graphVertexGeometricAngularNeighborSelectionRows_of_geometricSelectionInputSource
      geometricSelection
  let pointThirdRows :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ (neighborRows a).left.1 ->
                    x ≠ (neighborRows a).right.1 ->
                      BoundaryFreeGraphVertexPointAngularBetween C a.1
                        (neighborRows a).left.1 (neighborRows a).right.1 q :=
    boundaryFreePointThirdGermRows_of_neighborPair_incidentEdge_source
      (C := C) (inputs := inputs) incident_edge neighborRows
  exact
    boundaryFreeLocalSectorGeometricAngularSource_of_inputRows
      (C := C) (inputs := inputs)
      (boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_pointThirdGerm
        (C := C) (inputs := inputs) neighborRows selectionRows pointThirdRows)

set_option linter.style.longLine false in
/-- Family wrapper for claim `S2-agent-ci-local-angular-neighbor-source`. -/
noncomputable def S2_agent_ci_local_angular_neighbor_source_family
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (geometricSelection :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro n C inputs
  exact
    S2_agent_ci_local_angular_neighbor_source
      (C := C) (inputs := inputs) (incident_edge C inputs)
      (geometricSelection C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-cj-endpoint-and-geometric-selection-source`.

Local-angular source from the combined geometric-selection row and the sharp
endpoint-only/no-chord row.  This avoids the bare adjacent-frontier-endpoint
incident-edge source: when a closed germ lands at another frontier vertex, the
endpoint-only row proves that endpoint is one of the two selected carrier
neighbours; relative-interior germ points are still handled by the existing
interior frontier-edge carrier theorem. -/
noncomputable def S2_agent_cj_local_angular_neighbor_source_endpointOnly
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x =
                (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                  geometricSelection a).left.1 ∨
              x =
                (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                  geometricSelection a).right.1) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  let neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a :=
    unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
      geometricSelection
  let selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (neighborRows a).left.1 (neighborRows a).right.1) :=
    graphVertexGeometricAngularNeighborSelectionRows_of_geometricSelectionInputSource
      geometricSelection
  let pointThirdRows :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ (neighborRows a).left.1 ->
                    x ≠ (neighborRows a).right.1 ->
                      BoundaryFreeGraphVertexPointAngularBetween C a.1
                        (neighborRows a).left.1 (neighborRows a).right.1 q :=
    boundaryFreePointThirdGermRows_of_neighborPair_endpointOnly_source
      (C := C) (inputs := inputs) neighborRows
      (by
        intro a x hadj hxfrontier
        simpa [neighborRows] using endpoint_only a x hadj hxfrontier)
  exact
    boundaryFreeLocalSectorGeometricAngularSource_of_inputRows
      (C := C) (inputs := inputs)
      (boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_pointThirdGerm
        (C := C) (inputs := inputs) neighborRows selectionRows pointThirdRows)

set_option linter.style.longLine false in
/-- Same `cj` local-angular reducer, with the combined geometric-selection
source split into its primitive neighbour-pair and genuine sorted-list
selection rows. -/
noncomputable def
    S2_agent_cj_local_angular_neighbor_source_from_neighborPair_selection_endpointOnly
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (neighborRows a).left.1 (neighborRows a).right.1))
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x = (neighborRows a).left.1 ∨ x = (neighborRows a).right.1) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs :=
  boundaryFreeLocalSectorGeometricAngularSource_of_inputRows
    (C := C) (inputs := inputs)
    (boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_pointThirdGerm
      (C := C) (inputs := inputs) neighborRows selectionRows
      (boundaryFreePointThirdGermRows_of_neighborPair_endpointOnly_source
        (C := C) (inputs := inputs) neighborRows endpoint_only))

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-endpoint-only-honesty-replacement`.

Honest selected-neighbour replacement for the endpoint-only local-angular
composer.  The selected heads still come from the concrete carrier-neighbour
geometric-selection source, but the third-germ branch is now an explicit
local point-angular source rather than a classification of arbitrary adjacent
frontier endpoints.

This is the source row the selected-neighbour route should target if the
endpoint-only/no-chord premise cannot be proved from the finite planar input
package. -/
noncomputable def
    S2_dyn_20260520_local_angular_source_of_selectedNeighbor_pointThirdGerm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (pointThirdGermRows :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠
                      (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                        geometricSelection a).left.1 ->
                    x ≠
                        (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                          geometricSelection a).right.1 ->
                      BoundaryFreeGraphVertexPointAngularBetween C a.1
                        (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                          geometricSelection a).left.1
                        (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                          geometricSelection a).right.1 q) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  let neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a :=
    unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
      geometricSelection
  let selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (neighborRows a).left.1 (neighborRows a).right.1) :=
    graphVertexGeometricAngularNeighborSelectionRows_of_geometricSelectionInputSource
      geometricSelection
  exact
    boundaryFreeLocalSectorGeometricAngularSource_of_inputRows
      (C := C) (inputs := inputs)
      (boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_pointThirdGerm
        (C := C) (inputs := inputs) neighborRows selectionRows
        (by
          intro a ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
          exact
            pointThirdGermRows a ε q x hqball hqfrontier hadj hgerm
              hqcenter
              (by simpa [neighborRows] using hx_left)
              (by simpa [neighborRows] using hx_right)))

set_option linter.style.longLine false in
/-- Family wrapper for
`S2_dyn_20260520_local_angular_source_of_selectedNeighbor_pointThirdGerm`.

The residual family is the honest local point-third-germ source aligned to the
same selected carrier neighbours, not an endpoint-only/no-chord row. -/
noncomputable def
    S2_dyn_20260520_local_angular_source_family_of_selectedNeighbor_pointThirdGerm
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (pointThirdGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs})
            (ε : Real) (q : PlanarInterface.Point) (x : Fin m),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier
                  (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      x ≠
                          (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                            (geometricSelection C inputs) a).left.1 ->
                        x ≠
                            (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                              (geometricSelection C inputs) a).right.1 ->
                          BoundaryFreeGraphVertexPointAngularBetween C a.1
                            (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                              (geometricSelection C inputs) a).left.1
                            (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                              (geometricSelection C inputs) a).right.1 q) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro m C inputs
  exact
    S2_dyn_20260520_local_angular_source_of_selectedNeighbor_pointThirdGerm
      (C := C) (inputs := inputs)
      (geometricSelection C inputs) (pointThirdGermRows C inputs)

set_option linter.style.longLine false in
/-- Selected-neighbour incident-germ frontier-edge membership rows.

This is the local drawing-isolation residual for the point-third-germ source:
for a frontier point already localized to an incident W3 germ at the same
frontier vertex, prove that the germ's head is connected to that vertex by an
actual selected `unboundedFrontierEdgeSet` edge.  It is deliberately pointwise:
no completed boundary cycle, arbitrary endpoint classifier, induced frontier
graph, synthetic enclosure, or identity angular order is used. -/
abbrev SelectedNeighborIncidentGermFrontierEdgeMembershipRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (_geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) : Prop :=
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
/-- Local-radius form of selected-neighbour incident-germ frontier-edge
membership.

This is the sharp local source available from the drawing facts: after
shrinking around each frontier vertex, a noncenter frontier point in an
incident closed germ cannot be the far endpoint of a third edge, and the
relative-interior branch is promoted by the checked interior-frontier carrier
membership theorem.  Unlike
`SelectedNeighborIncidentGermFrontierEdgeMembershipRows`, this row deliberately
does not classify arbitrary adjacent frontier endpoints at large radii. -/
abbrev SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (_geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) : Prop :=
  Exists fun radius :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Real =>
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
                      (x, a.1) ∈ unboundedFrontierEdgeSet C inputs

set_option linter.style.longLine false in
/-- The local-radius incident-germ membership row is a direct consequence of
the existing local drawing isolation and interior-frontier carrier-membership
theorem.

The geometric-selection argument is present only to align this row with the
selected-neighbour route; the proof itself is purely local and does not use
final boundary/cycle data or endpoint-only closure. -/
theorem
    selectedNeighborIncidentGermLocalFrontierEdgeMembershipRows_of_geometricSelectionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
      (C := C) (inputs := inputs) geometricSelection := by
  simpa [SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows] using
    (localIncidentGermFrontierEdgeMembershipRows_of_inputs
      (C := C) inputs)

set_option linter.style.longLine false in
/-- Claim
`S2-codex-20260520-selected-incident-germ-membership-local-radius`.

Strict reduction of the selected-neighbour incident-germ frontier-edge
membership frontier to the local-radius row actually proved by the current
drawing API.  This closes the relative-interior and sufficiently-local endpoint
branches while leaving no final boundary-cycle, endpoint-only/no-chord, induced
frontier graph, or identity-angular-order premise. -/
theorem
    S2_codex_20260520_selected_incident_germ_membership_local_radius
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
      (C := C) (inputs := inputs) geometricSelection :=
  selectedNeighborIncidentGermLocalFrontierEdgeMembershipRows_of_geometricSelectionInputSource
    (C := C) (inputs := inputs) geometricSelection

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-incident-germ-global-source`.

The selected incident-germ source available from the finite drawing inputs is
the local-radius row.  This is the strict replacement source for consumers of
the older arbitrary-radius
`SelectedNeighborIncidentGermFrontierEdgeMembershipRows` leaf. -/
theorem
    S2_dyn_20260520_incident_germ_global_source_reduced_to_local_radius
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
      (C := C) (inputs := inputs) geometricSelection :=
  S2_codex_20260520_selected_incident_germ_membership_local_radius
    (C := C) (inputs := inputs) geometricSelection

set_option linter.style.longLine false in
/-- Local-radius third-germ point-sector rows.

This is the safe local version of the point-third-germ residual: after
shrinking around the frontier vertex, a frontier point lying in an incident
closed germ for a non-selected neighbour is impossible because the germ edge is
forced into the selected unbounded-frontier carrier and hence its head is one of
the two selected neighbours. -/
abbrev SelectedNeighborThirdGermLocalExteriorPointSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) : Prop :=
  Exists fun radius :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Real =>
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
                    x ≠
                        (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                          geometricSelection a).left.1 ->
                      x ≠
                          (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                            geometricSelection a).right.1 ->
                        BoundaryFreeGraphVertexPointAngularBetween C a.1
                          (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                            geometricSelection a).left.1
                          (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                            geometricSelection a).right.1 q

set_option linter.style.longLine false in
/-- Local-radius incident-germ membership gives the safe local third-germ
sector row. -/
theorem
    selectedNeighborThirdGermLocalExteriorPointSectorRows_of_localIncidentGermMembership
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (localIncidentRows :
      SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs) geometricSelection) :
    SelectedNeighborThirdGermLocalExteriorPointSectorRows
      (C := C) (inputs := inputs) geometricSelection := by
  classical
  rcases localIncidentRows with ⟨radius, hpos, hmem⟩
  refine ⟨radius, hpos, ?_⟩
  intro a ε q x hqsmall hqball hqfrontier hadj hgerm hqcenter hx_left
    hx_right
  let neighborRows :=
    unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
      geometricSelection
  let P : UnboundedFrontierCarrierNeighborPairAt inputs a := neighborRows a
  let hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  have hedge :
      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
    hmem a ε q x hqsmall hqball hqfrontier hadj hgerm hqcenter
  have hxmem : x ∈ unboundedFrontierVertexSet C inputs := by
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
  have hb : b = P.left ∨ b = P.right := (P.neighbor_iff b).1 hab
  exact False.elim
    (by
      rcases hb with hb | hb
      · have hx : x = P.left.1 := by
          calc
            x = b.1 := rfl
            _ = P.left.1 := congrArg (fun y => y.1) hb
        exact hx_left (by simpa [neighborRows, P] using hx)
      · have hx : x = P.right.1 := by
          calc
            x = b.1 := rfl
            _ = P.right.1 := congrArg (fun y => y.1) hb
        exact hx_right (by simpa [neighborRows, P] using hx))

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-selected-third-germ-local-sector`.

The local-radius incident-germ membership row gives the safe local third-germ
sector source directly from the selected geometric-neighbour input. -/
theorem S2_codex_20260520_selected_third_germ_local_sector
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    SelectedNeighborThirdGermLocalExteriorPointSectorRows
      (C := C) (inputs := inputs) geometricSelection :=
  selectedNeighborThirdGermLocalExteriorPointSectorRows_of_localIncidentGermMembership
    (C := C) (inputs := inputs) geometricSelection
    (S2_codex_20260520_selected_incident_germ_membership_local_radius
      (C := C) (inputs := inputs) geometricSelection)

set_option linter.style.longLine false in
/-- Local two-germ rows from the safe selected-neighbour local point-sector row.

This is the sharp local-radius replacement for the older global
`BoundaryFreeLocalSectorGeometricAngularSource` adapter: the radius carried by
`SelectedNeighborThirdGermLocalExteriorPointSectorRows` is intersected with the
ordinary vertex-star radius before proving the two-germ row. -/
noncomputable def
    localTwoGermRows_of_selectedNeighborThirdGermLocalExteriorPointSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (localThirdGermRows :
      SelectedNeighborThirdGermLocalExteriorPointSectorRows
        (C := C) (inputs := inputs) geometricSelection) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  classical
  let radius :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Real :=
    Classical.choose localThirdGermRows
  have hlocal :
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
                      x ≠
                          (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                            geometricSelection a).left.1 ->
                        x ≠
                            (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                              geometricSelection a).right.1 ->
                          BoundaryFreeGraphVertexPointAngularBetween C a.1
                            (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                              geometricSelection a).left.1
                            (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                              geometricSelection a).right.1 q :=
    Classical.choose_spec localThirdGermRows
  intro a
  let neighborRows :=
    unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
      geometricSelection
  let P : UnboundedFrontierCarrierNeighborPairAt inputs a := neighborRows a
  let left : Fin n := P.left.1
  let right : Fin n := P.right.1
  have hleft_adj : (unboundedFrontierCarrierGraph C inputs).Adj a P.left :=
    (P.neighbor_iff P.left).2 (Or.inl rfl)
  have hright_adj : (unboundedFrontierCarrierGraph C inputs).Adj a P.right :=
    (P.neighbor_iff P.right).2 (Or.inr rfl)
  have hleft_edge :
      (a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [left] using (unboundedFrontierCarrierGraph_adj_iff).1 hleft_adj
  have hright_edge :
      (a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [right] using (unboundedFrontierCarrierGraph_adj_iff).1 hright_adj
  have hheads_ne : left ≠ right := by
    intro h
    exact P.left_ne_right (Subtype.ext h)
  have hselection :
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 left right) := by
    simpa [neighborRows, P, left, right] using
      graphVertexGeometricAngularNeighborSelectionRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection a
  have hangular :
      BoundaryFreeGraphVertexAngularNoBetweenRows C a.1 left right :=
    boundaryFreeGraphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      (Classical.choice hselection)
  refine
    { left := left
      right := right
      left_edge := hleft_edge
      right_edge := hright_edge
      heads_ne := hheads_ne
      local_two_germ := ?_ }
  rcases
      exists_ball_forall_unboundedExterior_frontier_mem_vertexIncidentGermW3
        C inputs a.1 with
    ⟨starRadius, hstar_pos, hstar⟩
  let η : Real := min (radius a) starRadius
  have hη_pos : 0 < η := lt_min (hlocal.1 a) hstar_pos
  refine ⟨η, hη_pos, ?_⟩
  intro q hqball hqfrontier
  by_cases hqcenter : q = (canonicalGraph C).point a.1
  · left
    rw [hqcenter]
    exact
      ⟨by simpa [Metric.mem_ball] using hη_pos,
        left_mem_closedSegment _ _⟩
  have hq_radius :
      q ∈ Metric.ball ((canonicalGraph C).point a.1) (radius a) := by
    have hdη :
        dist q ((canonicalGraph C).point a.1) < η := by
      simpa [Metric.mem_ball] using hqball
    have hd : dist q ((canonicalGraph C).point a.1) < radius a :=
      lt_of_lt_of_le hdη (by
        dsimp [η]
        exact min_le_left (radius a) starRadius)
    simpa [Metric.mem_ball] using hd
  have hq_star :
      q ∈ Metric.ball ((canonicalGraph C).point a.1) starRadius := by
    have hdη :
        dist q ((canonicalGraph C).point a.1) < η := by
      simpa [Metric.mem_ball] using hqball
    have hd : dist q ((canonicalGraph C).point a.1) < starRadius :=
      lt_of_lt_of_le hdη (by
        dsimp [η]
        exact min_le_right (radius a) starRadius)
    simpa [Metric.mem_ball] using hd
  rcases hstar q hq_star hqfrontier with ⟨x, hvx, hqxstar⟩
  by_cases hx_left : x = left
  · left
    exact
      ⟨hqball, by
        simpa [vertexIncidentGermW3, hx_left] using hqxstar.2⟩
  by_cases hx_right : x = right
  · right
    exact
      ⟨hqball, by
        simpa [vertexIncidentGermW3, hx_right] using hqxstar.2⟩
  exact False.elim
    (by
      have hpoint :
          BoundaryFreeGraphVertexPointAngularBetween C a.1 left right q := by
        simpa [neighborRows, P, left, right] using
          hlocal.2 a starRadius q x hq_radius hq_star hqfrontier hvx hqxstar
            hqcenter
            (by simpa [left] using hx_left)
            (by simpa [right] using hx_right)
      have hbetween :
          BoundaryFreeGraphVertexAngularBetween C a.1 left right x :=
        boundaryFreeGraphVertexAngularBetween_of_pointAngularBetween
          (C := C) (center := a.1) (left := left) (right := right)
          (other := x) (ε := starRadius) (q := q)
          hpoint hqxstar hqcenter
      have hx_unit : GraphBridge.UnitDistanceAdj C a.1 x :=
        ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 x).1 hvx
      exact (hangular.no_between x hx_unit hx_left hx_right) hbetween)

set_option linter.style.longLine false in
/-- Local-sector rows from the safe selected-neighbour local point-sector row. -/
noncomputable def
    localSectorRows_of_selectedNeighborThirdGermLocalExteriorPointSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (localThirdGermRows :
      SelectedNeighborThirdGermLocalExteriorPointSectorRows
        (C := C) (inputs := inputs) geometricSelection) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_localTwoGermRows
    (localTwoGermRows_of_selectedNeighborThirdGermLocalExteriorPointSectorRows
      (C := C) (inputs := inputs) geometricSelection localThirdGermRows)

set_option linter.style.longLine false in
/-- Safe local no-third-germ row aligned to the selected carrier-neighbour
rows.

The radius is part of the source, so this avoids the false global statement
that every adjacent exterior-frontier endpoint pair is an exterior edge. -/
abbrev SelectedNeighborGeometricOrderLocalNoThirdGermRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs) :
    Prop :=
  Exists fun radius :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Real =>
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
                        False

set_option linter.style.longLine false in
/-- Local incident-germ membership proves the safe no-third-germ row for the
same selected carrier-neighbour data. -/
theorem
    selectedNeighborGeometricOrderLocalNoThirdGermRows_of_localIncidentGermMembership
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs)
    (localIncidentRows :
      SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    SelectedNeighborGeometricOrderLocalNoThirdGermRows
      (C := C) (inputs := inputs) selectedRows := by
  classical
  rcases localIncidentRows with ⟨radius, hpos, hmem⟩
  refine ⟨radius, hpos, ?_⟩
  intro a ε q x hqsmall hqball hqfrontier hadj hgerm hqcenter
    hx_left hx_right
  let selected := selectedRows.selectedNeighborRows a
  let P : UnboundedFrontierCarrierNeighborPairAt inputs a :=
    selected.toNeighborPairAt
  let hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  have hedge :
      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
    hmem a ε q x hqsmall hqball hqfrontier hadj hgerm hqcenter
  have hxmem : x ∈ unboundedFrontierVertexSet C inputs := by
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
  have hb : b = P.left ∨ b = P.right := (P.neighbor_iff b).1 hab
  rcases hb with hb | hb
  · have hx : x = selected.left := by
      calc
        x = b.1 := rfl
        _ = P.left.1 := congrArg (fun y => y.1) hb
        _ = selected.left := by
          simp [P, selected,
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt.toNeighborPairAt,
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt.leftVertex]
    exact hx_left hx
  · have hx : x = selected.right := by
      calc
        x = b.1 := rfl
        _ = P.right.1 := congrArg (fun y => y.1) hb
        _ = selected.right := by
          simp [P, selected,
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt.toNeighborPairAt,
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt.rightVertex]
    exact hx_right hx

set_option linter.style.longLine false in
/-- Build local two-germ rows from selected carrier neighbours and the safe
local no-third-germ source. -/
noncomputable def localTwoGermRows_of_selectedNeighborGeometricOrder_localNoThirdGerm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs)
    (localNoThird :
      SelectedNeighborGeometricOrderLocalNoThirdGermRows
        (C := C) (inputs := inputs) selectedRows) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  classical
  let radius :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} → Real :=
    Classical.choose localNoThird
  have hlocalNoThird := Classical.choose_spec localNoThird
  have hradius_pos :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        0 < radius a := hlocalNoThird.1
  have hnoThird :
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
                        False := hlocalNoThird.2
  intro a
  let selected := selectedRows.selectedNeighborRows a
  refine
    { left := selected.left
      right := selected.right
      left_edge := selected.left_edge
      right_edge := selected.right_edge
      heads_ne := selected.heads_ne
      local_two_germ := ?_ }
  rcases
      exists_ball_forall_unboundedExterior_frontier_mem_vertexIncidentGermW3
        C inputs a.1 with
    ⟨starRadius, hstar_pos, hstar⟩
  let η : Real := min (radius a) starRadius
  have hη_pos : 0 < η := lt_min (hradius_pos a) hstar_pos
  refine ⟨η, hη_pos, ?_⟩
  intro q hqball hqfrontier
  by_cases hqcenter : q = (canonicalGraph C).point a.1
  · left
    rw [hqcenter]
    exact
      ⟨by simpa [Metric.mem_ball] using hη_pos,
        left_mem_closedSegment _ _⟩
  have hq_radius :
      q ∈ Metric.ball ((canonicalGraph C).point a.1) (radius a) := by
    have hqball_lt :
        dist q ((canonicalGraph C).point a.1) < η := by
      exact Metric.mem_ball.mp hqball
    exact Metric.mem_ball.mpr
      (lt_of_lt_of_le hqball_lt (min_le_left _ _))
  have hq_star :
      q ∈ Metric.ball ((canonicalGraph C).point a.1) starRadius := by
    have hqball_lt :
        dist q ((canonicalGraph C).point a.1) < η := by
      exact Metric.mem_ball.mp hqball
    exact Metric.mem_ball.mpr
      (lt_of_lt_of_le hqball_lt (min_le_right _ _))
  rcases hstar q hq_star hqfrontier with ⟨x, hvx, hqxstar⟩
  by_cases hx_left : x = selected.left
  · left
    exact
      ⟨hqball, by
        simpa [vertexIncidentGermW3, hx_left] using hqxstar.2⟩
  by_cases hx_right : x = selected.right
  · right
    exact
      ⟨hqball, by
        simpa [vertexIncidentGermW3, hx_right] using hqxstar.2⟩
  exact False.elim
    (hnoThird a starRadius q x hq_radius hq_star hqfrontier hvx hqxstar
      hqcenter hx_left hx_right)

set_option linter.style.longLine false in
/-- Local-sector rows from selected carrier neighbours and the safe
local-radius incident-germ membership row. -/
noncomputable def
    localSectorRows_of_selectedNeighborGeometricOrder_localIncidentGermMembership
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs)
    (localIncidentRows :
      SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_localTwoGermRows
    (localTwoGermRows_of_selectedNeighborGeometricOrder_localNoThirdGerm
      (C := C) (inputs := inputs) selectedRows
      (selectedNeighborGeometricOrderLocalNoThirdGermRows_of_localIncidentGermMembership
        (C := C) (inputs := inputs) selectedRows localIncidentRows))

set_option linter.style.longLine false in
/-- The selected-neighbour point-third-germ angular row reduces to genuine
incident-germ frontier-edge membership.

Once the localized germ is known to be an actual selected frontier edge, the
neighbour-pair part of the geometric-selection source says its head is one of
the two selected carrier neighbours.  Hence a third head is impossible, and the
requested point-sector conclusion follows from the empty case. -/
theorem
    S2_agent_20260520_pointThirdGerm_source_of_selectedNeighbor_incidentGermFrontierEdgeMembership
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (incidentGermFrontierEdgeRows :
      SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs) geometricSelection) :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
      q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
        q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
          (canonicalGraph C).Adj a.1 x ->
            q ∈ vertexIncidentGermW3 C a.1 x ε ->
              q ≠ (canonicalGraph C).point a.1 ->
                x ≠
                    (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                      geometricSelection a).left.1 ->
                  x ≠
                      (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                        geometricSelection a).right.1 ->
                    BoundaryFreeGraphVertexPointAngularBetween C a.1
                      (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                        geometricSelection a).left.1
                      (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                        geometricSelection a).right.1 q := by
  intro a ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
  let neighborRows :=
    unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
      geometricSelection
  let P : UnboundedFrontierCarrierNeighborPairAt inputs a := neighborRows a
  let hwhole :
      UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
    unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
  have hedge :
      (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
        (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
    incidentGermFrontierEdgeRows a ε q x hqball hqfrontier hadj hgerm
      hqcenter
  have hxmem : x ∈ unboundedFrontierVertexSet C inputs := by
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
  have hb : b = P.left ∨ b = P.right := (P.neighbor_iff b).1 hab
  exact False.elim
    (by
      rcases hb with hb | hb
      · have hx : x = P.left.1 := by
          calc
            x = b.1 := rfl
            _ = P.left.1 := congrArg (fun y => y.1) hb
        exact hx_left (by simpa [neighborRows, P] using hx)
      · have hx : x = P.right.1 := by
          calc
            x = b.1 := rfl
            _ = P.right.1 := congrArg (fun y => y.1) hb
        exact hx_right (by simpa [neighborRows, P] using hx))

set_option linter.style.longLine false in
/-- Local-angular source with the point-third-germ residual reduced to
pointwise incident-germ frontier-edge membership for the selected neighbours. -/
noncomputable def
    S2_agent_20260520_local_angular_source_of_selectedNeighbor_incidentGermFrontierEdgeMembership
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (incidentGermFrontierEdgeRows :
      SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs) geometricSelection) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs :=
  S2_dyn_20260520_local_angular_source_of_selectedNeighbor_pointThirdGerm
    (C := C) (inputs := inputs) geometricSelection
    (S2_agent_20260520_pointThirdGerm_source_of_selectedNeighbor_incidentGermFrontierEdgeMembership
      (C := C) (inputs := inputs) geometricSelection
      incidentGermFrontierEdgeRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_20260520_local_angular_source_of_selectedNeighbor_incidentGermFrontierEdgeMembership`. -/
noncomputable def
    S2_agent_20260520_local_angular_source_family_of_selectedNeighbor_incidentGermFrontierEdgeMembership
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_local_angular_source_of_selectedNeighbor_incidentGermFrontierEdgeMembership
      (C := C) (inputs := inputs)
      (geometricSelection C inputs) (incidentGermFrontierEdgeRows C inputs)

set_option linter.style.longLine false in
/-- Selected-neighbour geometric-order rows plus genuine incident-germ
frontier-edge membership source the boundary-free local angular family.

This is the selected-head version of the angular source: the carrier heads,
their cut-partition/no-cut eraser, and their sorted outgoing-dart consecutive
row all come from the same selected-neighbour package.  The remaining local
input is the honest incident-germ frontier-edge membership row for that same
package, not an endpoint-only classifier or boundary-cycle shortcut. -/
noncomputable def
    S2_codex_20260520_boundaryFreeAngularSource_of_selectedNeighborGeometricOrder_incidentGermMembership
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (incidentGermFrontierEdgeRows :
      SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs :=
  S2_agent_20260520_local_angular_source_of_selectedNeighbor_incidentGermFrontierEdgeMembership
    (C := C) (inputs := inputs)
    selectedRows.toGeometricSelectionInputSource
    incidentGermFrontierEdgeRows

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_20260520_boundaryFreeAngularSource_of_selectedNeighborGeometricOrder_incidentGermMembership`. -/
noncomputable def
    S2_codex_20260520_boundaryFreeAngularSource_family_of_selectedNeighborGeometricOrder_incidentGermMembership
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_boundaryFreeAngularSource_of_selectedNeighborGeometricOrder_incidentGermMembership
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (incidentGermFrontierEdgeRows C inputs)

set_option linter.style.longLine false in
/-- Selected-neighbour local point-sector rows.

This is the strict local geometric residual for the point-third-germ source:
once the selected carrier neighbours have been fixed by the real
geometric-selection row, every noncenter exterior-frontier point near the
selected frontier vertex lies in the open point-sector between those two rays.
It deliberately contains no arbitrary adjacent endpoint classification, final
cycle rows, actual-boundary rows, induced frontier graph, arbitrary
carrier/cycle, synthetic enclosure, or identity angular-order shortcut. -/
abbrev SelectedNeighborLocalExteriorPointSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) : Prop :=
  forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
      (ε : Real) (q : PlanarInterface.Point),
    q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
      q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
        q ≠ (canonicalGraph C).point a.1 ->
          BoundaryFreeGraphVertexPointAngularBetween C a.1
            (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
              geometricSelection a).left.1
            (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
              geometricSelection a).right.1 q

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-point-third-germ-source`.

The point-third-germ row consumed by
`S2_dyn_20260520_local_angular_source_of_selectedNeighbor_pointThirdGerm`
strictly reduces to the selected-neighbour local exterior point-sector row.
The incident germ, adjacency, and "not either selected head" hypotheses are
kept only to match the existing consumer; the actual geometric content is the
local point-sector fact for the same frontier point `q`. -/
theorem
    S2_dyn_20260520_pointThirdGerm_source_of_selectedNeighbor_localPointSector
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (pointSectorRows :
      SelectedNeighborLocalExteriorPointSectorRows
        (C := C) (inputs := inputs) geometricSelection) :
    forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
      q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
        q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
          (canonicalGraph C).Adj a.1 x ->
            q ∈ vertexIncidentGermW3 C a.1 x ε ->
              q ≠ (canonicalGraph C).point a.1 ->
                x ≠
                    (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                      geometricSelection a).left.1 ->
                  x ≠
                      (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                        geometricSelection a).right.1 ->
                    BoundaryFreeGraphVertexPointAngularBetween C a.1
                      (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                        geometricSelection a).left.1
                      (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                        geometricSelection a).right.1 q := by
  intro a ε q _x hqball hqfrontier _hadj _hgerm hqcenter _hx_left _hx_right
  exact pointSectorRows a ε q hqball hqfrontier hqcenter

set_option linter.style.longLine false in
/-- Local-angular source with the point-third-germ residual reduced to the
selected-neighbour local exterior point-sector row. -/
noncomputable def
    S2_dyn_20260520_local_angular_source_of_selectedNeighbor_localPointSector
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (pointSectorRows :
      SelectedNeighborLocalExteriorPointSectorRows
        (C := C) (inputs := inputs) geometricSelection) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs :=
  S2_dyn_20260520_local_angular_source_of_selectedNeighbor_pointThirdGerm
    (C := C) (inputs := inputs) geometricSelection
    (S2_dyn_20260520_pointThirdGerm_source_of_selectedNeighbor_localPointSector
      (C := C) (inputs := inputs) geometricSelection pointSectorRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_dyn_20260520_local_angular_source_of_selectedNeighbor_localPointSector`. -/
noncomputable def
    S2_dyn_20260520_local_angular_source_family_of_selectedNeighbor_localPointSector
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (pointSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborLocalExteriorPointSectorRows
            (C := C) (inputs := inputs) (geometricSelection C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro m C inputs
  exact
    S2_dyn_20260520_local_angular_source_of_selectedNeighbor_localPointSector
      (C := C) (inputs := inputs)
      (geometricSelection C inputs) (pointSectorRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-boundaryfree-angular-input-source`.

Selected-neighbour geometric-order rows plus the local exterior point-sector
theorem fill the strict boundary-free angular source.

The two selected heads are exactly the heads carried by
`UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows`: actual
`unboundedFrontierEdgeSet` incidences, their cut-partition/no-cut eraser, and
their genuine consecutive non-wrap positions in
`GeometricRotationSystem.geometricOutgoingDartList`.  The only remaining
geometric input is the pointwise exterior-sector theorem for those same
selected heads. -/
noncomputable def
    S2_agent_20260520_boundaryFreeAngularSource_of_selectedNeighborGeometricOrder_localPointSector
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (pointSectorRows :
      SelectedNeighborLocalExteriorPointSectorRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs :=
  S2_dyn_20260520_local_angular_source_of_selectedNeighbor_localPointSector
    (C := C) (inputs := inputs)
    selectedRows.toGeometricSelectionInputSource pointSectorRows

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_20260520_boundaryFreeAngularSource_of_selectedNeighborGeometricOrder_localPointSector`. -/
noncomputable def
    S2_agent_20260520_boundaryFreeAngularSource_family_of_selectedNeighborGeometricOrder_localPointSector
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (pointSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborLocalExteriorPointSectorRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_boundaryFreeAngularSource_of_selectedNeighborGeometricOrder_localPointSector
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (pointSectorRows C inputs)

set_option linter.style.longLine false in
/-- Family wrapper for
`S2_agent_cj_local_angular_neighbor_source_from_neighborPair_selection_endpointOnly`.
The exact residuals are the actual carrier neighbour-pair row, the genuine
geometric consecutive-selection row for those two neighbours, and the
endpoint-only/no-chord row. -/
noncomputable def
    S2_agent_cj_local_angular_neighbor_source_family_endpointOnly
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1))
    (endpoint_only :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
            (x : Fin n),
            (canonicalGraph C).Adj a.1 x ->
              (canonicalGraph C).point x ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ->
                x = ((neighborRows C inputs) a).left.1 ∨
                  x = ((neighborRows C inputs) a).right.1) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro n C inputs
  exact
    S2_agent_cj_local_angular_neighbor_source_from_neighborPair_selection_endpointOnly
      (C := C) (inputs := inputs)
      (neighborRows C inputs) (selectionRows C inputs)
      (endpoint_only C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-local-angular-source-of-inputs`.

The local angular source consumed before Planck's selected head-between theorem
reduces to the actual geometric neighbour-selection source plus the sharp
endpoint-only row for those same selected neighbours.  The endpoint branch does
not assert selected-edge membership for all adjacent frontier endpoints; it
only says that any frontier endpoint in a closed germ at `a` is one of the two
carrier neighbours chosen by the geometric-selection row. -/
noncomputable def S2_dyn_20260520_local_angular_source_of_inputs
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (endpoint_only :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
        (canonicalGraph C).Adj a.1 x ->
          (canonicalGraph C).point x ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ->
            x =
                (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                  geometricSelection a).left.1 ∨
              x =
                (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                  geometricSelection a).right.1) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs :=
  S2_agent_cj_local_angular_neighbor_source_endpointOnly
    (C := C) (inputs := inputs) geometricSelection endpoint_only

set_option linter.style.longLine false in
/-- Family wrapper for `S2_dyn_20260520_local_angular_source_of_inputs`.

This is the input-level source row to pass to the selected raw-orbit
head-between lane: for every input, provide the local geometric-selection row
and the endpoint-only/no-third-neighbour row aligned to that selection. -/
noncomputable def S2_dyn_20260520_local_angular_source_of_inputs_family
    (geometricSelection :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (endpoint_only :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
            (x : Fin n),
            (canonicalGraph C).Adj a.1 x ->
              (canonicalGraph C).point x ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ->
                x =
                    (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                      (geometricSelection C inputs) a).left.1 ∨
                  x =
                    (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                      (geometricSelection C inputs) a).right.1) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro n C inputs
  exact
    S2_dyn_20260520_local_angular_source_of_inputs
      (C := C) (inputs := inputs)
      (geometricSelection C inputs) (endpoint_only C inputs)

/-- Claim `S2-agent-local-angular-source-20260520bw`.

Family-level reducer for the strict residual source.  It does not use final
cycle rows, actual-boundary equivalence rows, induced frontier graph shortcut
rows, arbitrary cycles, convex hulls, synthetic enclosures, or identity angular
orders; all residual content is the local Skolemized star/angular/frontier-germ
row above. -/
noncomputable def S2_agent_local_angular_source_20260520bw
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeLocalSectorGeometricAngularInputRows inputs) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro n C inputs
  exact
    boundaryFreeLocalSectorGeometricAngularSource_of_inputRows
      (C := C) (inputs := inputs) (rows C inputs)

/-- Claim `S2-agent-local-angular-input-source-20260520bx`.

Family-level input-row reducer for the strict local angular source.  The exact
residuals are the concrete carrier neighbour-pair row, the nonempty
consecutive non-wrap row in the genuine geometric outgoing-dart list, and the
third-germ graph-dart angular row. -/
noncomputable def
    S2_agent_local_angular_input_source_of_neighborPair_selection_thirdGerm_20260520bx
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1))
    (thirdGermRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      x ≠ ((neighborRows C inputs) a).left.1 ->
                        x ≠ ((neighborRows C inputs) a).right.1 ->
                          BoundaryFreeGraphVertexAngularBetween C a.1
                            ((neighborRows C inputs) a).left.1
                            ((neighborRows C inputs) a).right.1 x) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularInputRows inputs := by
  intro n C inputs
  exact
    boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_thirdGerm
      (C := C) (inputs := inputs) (neighborRows C inputs)
      (selectionRows C inputs) (thirdGermRows C inputs)

/-- Same BX input-row reducer with the third-germ residual in point-ray
exterior-sector form, before converting through the incident-germ angle
equality. -/
noncomputable def
    S2_agent_local_angular_input_source_of_neighborPair_selection_pointThirdGerm_20260520bx
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1))
    (pointThirdGermRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      x ≠ ((neighborRows C inputs) a).left.1 ->
                        x ≠ ((neighborRows C inputs) a).right.1 ->
                          BoundaryFreeGraphVertexPointAngularBetween C a.1
                            ((neighborRows C inputs) a).left.1
                            ((neighborRows C inputs) a).right.1 q) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularInputRows inputs := by
  intro n C inputs
  exact
    boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_pointThirdGerm
      (C := C) (inputs := inputs) (neighborRows C inputs)
      (selectionRows C inputs) (pointThirdGermRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-main-by-source-compression-20260520bz`.

The geometric-selection source already contains both the actual carrier
neighbour-pair row and the consecutive sorted outgoing-dart selection row.
Together with adjacent-endpoint incident edges it also sources the point-ray
third-germ row, so the sharp local angular source no longer needs those three
families as separate inputs. -/
noncomputable def
    S2_main_local_angular_source_of_geometricSelection_incidentEdge_20260520bz
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (geometricSelection :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro n C inputs
  let source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    geometricSelection C inputs
  let neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a :=
    unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
      source
  let selectionRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (neighborRows a).left.1 (neighborRows a).right.1) :=
    graphVertexGeometricAngularNeighborSelectionRows_of_geometricSelectionInputSource
      source
  let pointThirdRows :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ (neighborRows a).left.1 ->
                    x ≠ (neighborRows a).right.1 ->
                      BoundaryFreeGraphVertexPointAngularBetween C a.1
                        (neighborRows a).left.1 (neighborRows a).right.1 q :=
    boundaryFreePointThirdGermRows_of_neighborPair_incidentEdge_source
      (C := C) (inputs := inputs) (incident_edge C inputs) neighborRows
  exact
    boundaryFreeLocalSectorGeometricAngularSource_of_inputRows
      (C := C) (inputs := inputs)
      (boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_pointThirdGerm
        (C := C) (inputs := inputs) neighborRows selectionRows pointThirdRows)

/-- Convenience family reducer from carrier-neighbour, sorted-list selection,
and third-germ angular rows. -/
noncomputable def
    S2_agent_local_angular_source_of_neighborPair_selection_thirdGerm_20260520bw
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1))
    (thirdGermRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      x ≠ ((neighborRows C inputs) a).left.1 ->
                        x ≠ ((neighborRows C inputs) a).right.1 ->
                          BoundaryFreeGraphVertexAngularBetween C a.1
                            ((neighborRows C inputs) a).left.1
                            ((neighborRows C inputs) a).right.1 x) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro n C inputs
  exact
    boundaryFreeLocalSectorGeometricAngularSource_of_inputRows
      (C := C) (inputs := inputs)
      (boundaryFreeLocalSectorGeometricAngularInputRows_of_neighborPair_selection_thirdGerm
        (C := C) (inputs := inputs) (neighborRows C inputs)
        (selectionRows C inputs) (thirdGermRows C inputs))

/-- The sharp boundary-free geometric-angular source erases to the pointwise
local-sector family.

This is the strict non-circular reducer for claim
`S2-agent-local-sector-input-source-20260520bv`: it uses no final cycle rows,
actual-boundary equivalence rows, induced frontier graph shortcut, arbitrary
cycle, convex hull shortcut, synthetic enclosure predicate, or identity angular
order shortcut.  The angular no-between row is read from the actual sorted
geometric outgoing-dart list. -/
noncomputable def localSectorRows_of_boundaryFree_geometricAngularSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalSectorGeometricAngularSource inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  refine
    S2_agent_local_sector_family_from_inputs_20260520ae
      (C := C) (inputs := inputs) ?_
  intro a
  rcases source a with
    ⟨left, right, hleft, hright, hne, hselection, hthird⟩
  refine ⟨left, right, hleft, hright, hne, ?_, hthird⟩
  exact
    boundaryFreeGraphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      (Classical.choice hselection)

/-- The sharp boundary-free geometric-angular source gives the requested
pointwise local two-germ family directly.

For each unbounded-frontier carrier vertex, the source chooses two actual
`unboundedFrontierEdgeSet` germs.  The genuine sorted geometric outgoing-dart
selection row supplies the angular no-between exclusion, while the local
third-germ row puts any other nearby frontier germ into that excluded sector. -/
noncomputable def localTwoGermRows_of_boundaryFree_geometricAngularSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalSectorGeometricAngularSource inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  classical
  intro a
  let left : Fin n := Classical.choose (source a)
  let right : Fin n := Classical.choose (Classical.choose_spec (source a))
  have hsource :
      ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
        ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
        left ≠ right ∧
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 left right) ∧
        forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
          q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
              (canonicalGraph C).Adj a.1 x ->
                q ∈ vertexIncidentGermW3 C a.1 x ε ->
                  q ≠ (canonicalGraph C).point a.1 ->
                    x ≠ left ->
                      x ≠ right ->
                        BoundaryFreeGraphVertexAngularBetween C a.1 left right x :=
    Classical.choose_spec (Classical.choose_spec (source a))
  have hangular :
      BoundaryFreeGraphVertexAngularNoBetweenRows C a.1 left right :=
    boundaryFreeGraphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      (Classical.choice hsource.2.2.2.1)
  exact
    unboundedFrontierCarrierLocalTwoGermRowsAt_of_no_third_germ
      hsource.1 hsource.2.1 hsource.2.2.1
      (by
        intro ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
        have hx_unit : GraphBridge.UnitDistanceAdj C a.1 x :=
          ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 x).1 hadj
        exact
          (hangular.no_between x hx_unit hx_left hx_right)
            (hsource.2.2.2.2 ε q x hqball hqfrontier hadj hgerm hqcenter
              hx_left hx_right))

/-- Claim `S2-agent-20260520-cp-local-two-germ-input`.

Family-level strict reduction of the S2-A pointwise local two-germ target.
The remaining source is exactly the boundary-free geometric-angular row for
the actual selected unbounded-frontier germs: no final boundary cycle rows,
induced frontier graph shortcut, arbitrary adjacent-endpoint closure, identity
angular-order shortcut, or synthetic enclosure is used. -/
noncomputable def S2_agent_cp_local_two_germ_input_source_20260520
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeLocalSectorGeometricAngularSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  intro m C inputs
  exact
    localTwoGermRows_of_boundaryFree_geometricAngularSource
      (C := C) (inputs := inputs) (source C inputs)

/-- Skolemized-row form of
`S2_agent_cp_local_two_germ_input_source_20260520`.

This is the narrowest input-row handoff for S2-A currently exposed in this
file: callers provide the two selected frontier germs, their real geometric
consecutive non-wrap selection rows, and the pointwise third-germ angular row. -/
noncomputable def
    S2_agent_cp_local_two_germ_inputRows_source_20260520
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeLocalSectorGeometricAngularInputRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
  S2_agent_cp_local_two_germ_input_source_20260520
    (fun C inputs =>
      boundaryFreeLocalSectorGeometricAngularSource_of_inputRows
        (C := C) (inputs := inputs) (rows C inputs))

/-- The strict boundary-free geometric-angular source also gives the concrete
carrier neighbour-pair rows.

This projection goes through the local-sector row, so the selected heads remain
the actual `unboundedFrontierEdgeSet` carrier heads chosen by the local source;
no induced frontier graph, completed cycle, or global closed-germ row is used. -/
noncomputable def neighborPairRows_of_boundaryFree_geometricAngularSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalSectorGeometricAngularSource inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_boundaryFree_geometricAngularSource
      (C := C) (inputs := inputs) source
  exact fun a => (localSectorRows a).toNeighborPairAt

set_option linter.style.longLine false in
/-- Pointwise selected-neighbour cut-partition/geometric-order input row from
the sharp boundary-free geometric-angular source.

The two selected heads are the same heads named by the source.  The geometric
order is read directly from its non-wrap sorted-list row, while the
cut-partition residual is vacuous because the same angular no-between and
local third-germ data first give a local-sector row whose `only` field rules
out any third concrete carrier neighbour. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderInputRowsAt_of_boundaryFree_geometricAngularSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalSectorGeometricAngularSource inputs)
    (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}) :
    SelectedNeighborCutPartitionGeometricOrderInputRowsAt inputs a := by
  classical
  let left : Fin n := Classical.choose (source a)
  let right : Fin n := Classical.choose (Classical.choose_spec (source a))
  have hsource :
      ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
        ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
        left ≠ right ∧
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 left right) ∧
        forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
          q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
              (canonicalGraph C).Adj a.1 x ->
                q ∈ vertexIncidentGermW3 C a.1 x ε ->
                  q ≠ (canonicalGraph C).point a.1 ->
                    x ≠ left ->
                      x ≠ right ->
                        BoundaryFreeGraphVertexAngularBetween C a.1 left right x :=
    Classical.choose_spec (Classical.choose_spec (source a))
  have hangular :
      BoundaryFreeGraphVertexAngularNoBetweenRows C a.1 left right :=
    boundaryFreeGraphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      (Classical.choice hsource.2.2.2.1)
  let twoGermRows :
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
    unboundedFrontierCarrierLocalTwoGermRowsAt_of_no_third_germ
      hsource.1 hsource.2.1 hsource.2.2.1
      (by
        intro ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
        have hx_unit : GraphBridge.UnitDistanceAdj C a.1 x :=
          ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 x).1 hadj
        exact
          (hangular.no_between x hx_unit hx_left hx_right)
            (hsource.2.2.2.2 ε q x hqball hqfrontier hadj hgerm
              hqcenter hx_left hx_right))
  let sectorRows :
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    twoGermRows.toLocalSectorRowsAt
  let selectionRow :
      GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
        C a.1 left right :=
    Classical.choice hsource.2.2.2.1
  exact
    { left := left
      right := right
      left_edge := hsource.1
      right_edge := hsource.2.1
      heads_ne := hsource.2.2.1
      third_neighbor_cutPartitions := by
        intro b hb hleft hright
        exact
          False.elim
            (by
              rcases sectorRows.only b hb with hb_left | hb_right
              · exact hleft (by simpa [sectorRows, twoGermRows] using hb_left)
              · exact hright (by simpa [sectorRows, twoGermRows] using hb_right))
      index := selectionRow.index
      index_succ_lt := selectionRow.index_succ_lt
      left_eq := selectionRow.left_eq
      right_eq := selectionRow.right_eq }

set_option linter.style.longLine false in
/-- The sharp boundary-free geometric-angular source fills the strict
selected-neighbour cut-partition/geometric-order input source.

This is stronger than first projecting to independent local-sector and
neighbour-pair rows: each pointwise output row keeps the selected incident
edges, the vacuous third-neighbour cut-partition residual, and the genuine
geometric consecutive row tied to the same source heads. -/
noncomputable def
    selectedNeighborCutPartitionGeometricOrderInputSource_of_boundaryFree_geometricAngularSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalSectorGeometricAngularSource inputs) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs where
  rows := fun a =>
    ⟨selectedNeighborCutPartitionGeometricOrderInputRowsAt_of_boundaryFree_geometricAngularSource
      (C := C) (inputs := inputs) source a⟩

set_option linter.style.longLine false in
/-- Strict selected-neighbour route to the input-facing cut/geometric source.

This replaces the stale endpoint-only/no-chord row with the actual selected
`unboundedFrontierEdgeSet` heads carried by `selectedRows` and the honest
local point-sector theorem for those same heads.  The geometric order is still
read from the genuine sorted outgoing-dart row in `selectedRows`. -/
noncomputable def
    S2_codex_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrder_localPointSector
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (pointSectorRows :
      SelectedNeighborLocalExteriorPointSectorRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs :=
  selectedNeighborCutPartitionGeometricOrderInputSource_of_boundaryFree_geometricAngularSource
    (C := C) (inputs := inputs)
    (S2_agent_20260520_boundaryFreeAngularSource_of_selectedNeighborGeometricOrder_localPointSector
      (C := C) (inputs := inputs) selectedRows pointSectorRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrder_localPointSector`. -/
noncomputable def
    S2_codex_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_family_of_selectedNeighborGeometricOrder_localPointSector
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (pointSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborLocalExteriorPointSectorRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrder_localPointSector
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (pointSectorRows C inputs)

set_option linter.style.longLine false in
/-- Safe selected-neighbour cut/geometric input source with the local-radius
third-germ row checked at the same selected heads.

This is the narrow replacement for the older local-point-sector source leaf:
`SelectedNeighborThirdGermLocalExteriorPointSectorRows` is enough to recover
the actual local-sector rows, while the selected input source itself is read
from the bundled selected `unboundedFrontierEdgeSet` cut rows and genuine
geometric order.  Thus the proof avoids the false arbitrary-radius
`SelectedNeighborLocalExteriorPointSectorRows` premise. -/
noncomputable def
    S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrder_safeLocalThirdGerm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (localThirdGermRows :
      SelectedNeighborThirdGermLocalExteriorPointSectorRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  have _localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_selectedNeighborThirdGermLocalExteriorPointSectorRows
      (C := C) (inputs := inputs)
      selectedRows.toGeometricSelectionInputSource localThirdGermRows
  exact
    S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrderRows
      (C := C) (inputs := inputs) selectedRows

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrder_safeLocalThirdGerm`. -/
noncomputable def
    S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_family_of_selectedNeighborGeometricOrder_safeLocalThirdGerm
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (localThirdGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborThirdGermLocalExteriorPointSectorRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrder_safeLocalThirdGerm
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (localThirdGermRows C inputs)

/-- Bundled local output of the selected-neighbour source.

The first two fields are the requested pointwise carrier-neighbour and
local-sector families; the third records the local two-germ consequence from
the same selected carrier heads. -/
structure LocalSelectedNeighborSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  neighborRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a
  localSectorRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a
  localTwoGermRows :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a

/-- Claim `S2-agent-local-selected-neighbor-source`.

Selected exterior carrier germs plus the local star/geometric angular row
strictly reduce both live local targets:
`forall a, UnboundedFrontierCarrierNeighborPairAt inputs a` and
`forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a`.

The source is the honest boundary-free geometric-angular one: for each
unbounded-frontier vertex it chooses two actual selected carrier edges, proves
they are a non-wrap consecutive pair in the real geometric outgoing list, and
handles third nearby frontier germs locally. -/
noncomputable def S2_agent_local_selected_neighbor_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalSectorGeometricAngularSource inputs) :
    LocalSelectedNeighborSourceRows inputs := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_boundaryFree_geometricAngularSource
      (C := C) (inputs := inputs) source
  exact
    { neighborRows := fun a => (localSectorRows a).toNeighborPairAt
      localSectorRows := localSectorRows
      localTwoGermRows := localTwoGermRows_of_localSectorRows localSectorRows }

/-- Family form of `S2_agent_local_selected_neighbor_source`. -/
noncomputable def S2_agent_local_selected_neighbor_source_family
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeLocalSectorGeometricAngularSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedNeighborSourceRows inputs := by
  intro m C inputs
  exact
    S2_agent_local_selected_neighbor_source
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- The selected-neighbour geometric-order plus point-sector source also gives
the local selected-neighbour bundle used by the carrier route. -/
noncomputable def
    S2_agent_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localPointSector
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (pointSectorRows :
      SelectedNeighborLocalExteriorPointSectorRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    LocalSelectedNeighborSourceRows inputs :=
  S2_agent_local_selected_neighbor_source
    (C := C) (inputs := inputs)
    (S2_agent_20260520_boundaryFreeAngularSource_of_selectedNeighborGeometricOrder_localPointSector
      (C := C) (inputs := inputs) selectedRows pointSectorRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localPointSector`. -/
noncomputable def
    S2_agent_20260520_localSelectedNeighborRows_family_of_selectedNeighborGeometricOrder_localPointSector
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (pointSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborLocalExteriorPointSectorRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedNeighborSourceRows inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localPointSector
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (pointSectorRows C inputs)

set_option linter.style.longLine false in
/-- Immediate selected-neighbour output from the reduced boundary-free angular
source.

The selected carrier-neighbour, local-sector, and local two-germ rows are all
projected from the same selected-neighbour geometric-order package plus the
honest incident-germ frontier-edge membership row. -/
noncomputable def
    S2_codex_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_incidentGermMembership
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (incidentGermFrontierEdgeRows :
      SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    LocalSelectedNeighborSourceRows inputs :=
  S2_agent_local_selected_neighbor_source
    (C := C) (inputs := inputs)
    (S2_codex_20260520_boundaryFreeAngularSource_of_selectedNeighborGeometricOrder_incidentGermMembership
      (C := C) (inputs := inputs)
      selectedRows incidentGermFrontierEdgeRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_incidentGermMembership`. -/
noncomputable def
    S2_codex_20260520_localSelectedNeighborRows_family_of_selectedNeighborGeometricOrder_incidentGermMembership
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedNeighborSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_incidentGermMembership
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (incidentGermFrontierEdgeRows C inputs)

set_option linter.style.longLine false in
/-- Local-radius selected-neighbour output from selected geometric-order rows
and an explicit local incident-germ membership row.

This is the local-safe replacement consumer for the older
`SelectedNeighborIncidentGermFrontierEdgeMembershipRows` source.  It keeps the
selected carrier heads and geometric order from `selectedRows`, and uses only
the local-radius incident-germ membership row to build the local two-germ and
local-sector outputs. -/
noncomputable def
    localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localIncidentGermMembership
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs)
    (localIncidentRows :
      SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :
    LocalSelectedNeighborSourceRows inputs := by
  let localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
    localTwoGermRows_of_selectedNeighborGeometricOrder_localNoThirdGerm
      (C := C) (inputs := inputs) selectedRows
      (selectedNeighborGeometricOrderLocalNoThirdGermRows_of_localIncidentGermMembership
        (C := C) (inputs := inputs) selectedRows localIncidentRows)
  exact
    { neighborRows := selectedRows.toNeighborPairRows
      localSectorRows := localSectorRows_of_localTwoGermRows localTwoGermRows
      localTwoGermRows := localTwoGermRows }

set_option linter.style.longLine false in
/-- Family form of
`localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localIncidentGermMembership`. -/
noncomputable def
    localSelectedNeighborRowsFamily_of_selectedNeighborGeometricOrder_localIncidentGermMembership_20260520
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (localIncidentRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (selectedRows C inputs).toGeometricSelectionInputSource) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedNeighborSourceRows inputs := by
  intro m C inputs
  exact
    localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localIncidentGermMembership
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (localIncidentRows C inputs)

set_option linter.style.longLine false in
/-- Local-radius selected-neighbour output from the selected geometric-order
rows alone.

This is the strict local replacement for the stronger
`SelectedNeighborIncidentGermFrontierEdgeMembershipRows` premise: the incident
germ membership used here is the local drawing-isolation row already proved
from the inputs, and the two heads/geometric order still come from the same
selected `unboundedFrontierEdgeSet` package. -/
noncomputable def
    S2_codex_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localIncident
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs) :
    LocalSelectedNeighborSourceRows inputs :=
  localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localIncidentGermMembership
    (C := C) (inputs := inputs) selectedRows
    (S2_dyn_20260520_incident_germ_global_source_reduced_to_local_radius
      (C := C) (inputs := inputs)
      selectedRows.toGeometricSelectionInputSource)

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localIncident`. -/
noncomputable def
    S2_codex_20260520_localSelectedNeighborRows_family_of_selectedNeighborGeometricOrder_localIncident
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedNeighborSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localIncident
      (C := C) (inputs := inputs) (selectedRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-main-20260520-local-sector-close`.

Actual selected carrier-neighbour/geometric-selection rows close the pointwise
local-sector source leaf.  The proof projects the checked local selected-
neighbour bundle built from the same selected `unboundedFrontierEdgeSet` heads
and the genuine non-wrap sorted outgoing-list row; the local incident-germ
membership is discharged internally from finite drawing isolation. -/
noncomputable def localSectorRows_of_geometricSelection_localIncident
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  (S2_codex_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localIncident
    (C := C) (inputs := inputs)
    (selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) source)).localSectorRows

set_option linter.style.longLine false in
/-- Named claim wrapper for
`localSectorRows_of_geometricSelection_localIncident`. -/
noncomputable def S2_codex_main_20260520_local_sector_close
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_geometricSelection_localIncident
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Compact selected-neighbour geometric rows supply the full local output
bundle used by the raw-orbit source reducers.

The local-sector rows come from the checked local-incident reducer, and the
local two-germ rows are just the local-sector eraser.  Thus all three outputs
use the same two actual selected `unboundedFrontierEdgeSet` heads. -/
noncomputable def localSelectedNeighborRows_of_geometricSelection_localIncident
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs) :
    LocalSelectedNeighborSourceRows inputs := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) source
  exact
    { neighborRows :=
        unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
          source
      localSectorRows := localSectorRows
      localTwoGermRows := localTwoGermRows_of_localSectorRows localSectorRows }

set_option linter.style.longLine false in
/-- Family form of
`localSelectedNeighborRows_of_geometricSelection_localIncident`. -/
noncomputable def
    localSelectedNeighborRowsFamily_of_geometricSelection_localIncident_20260520
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedNeighborSourceRows inputs := by
  intro m C inputs
  exact
    localSelectedNeighborRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of
`localSectorRows_of_geometricSelection_localIncident`. -/
noncomputable def localSectorRowsFamily_of_geometricSelection_localIncident_20260520
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    localSectorRows_of_geometricSelection_localIncident
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Same-boundary actual sector/geometric rows close the pointwise local-sector
leaf through the actual carrier/geometric-selection reducer. -/
noncomputable def
    S2_codex_main_20260520_local_sector_close_of_faceSucc_sectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C) B)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2_codex_main_20260520_local_sector_close
    (C := C) (inputs := inputs)
    (S2_main_geometricSelectionInputSource_of_faceSucc_sectorRows_20260520cb
      (C := C) (inputs := inputs) B
      frontier_iff_cycle_vertex faceSuccRows sectorRows)

set_option linter.style.longLine false in
/-- Fully split local selected-neighbour source.

The remaining non-input residuals are now exactly selected
incident-edge/cut-partition rows and the genuine sorted outgoing-dart index row
for those same selected heads.  The local incident-germ membership row is
proved internally from the drawing inputs. -/
noncomputable def
    S2_codex_20260520_localSelectedNeighborRows_of_cutPartition_indexRows_localIncident
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs)
    (indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows) :
    LocalSelectedNeighborSourceRows inputs :=
  S2_codex_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localIncident
    (C := C) (inputs := inputs)
    (S2_codex_20260520_selected_neighbor_geometric_order_source_split
      (C := C) (inputs := inputs)
      selectedRows
      (S2_agent_selected_geometric_order_source
        (C := C) (inputs := inputs) indexRows))

set_option linter.style.longLine false in
/-- Family form of the fully split local selected-neighbour source. -/
noncomputable def
    S2_codex_20260520_localSelectedNeighborRows_family_of_cutPartition_indexRows_localIncident
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
            (selectedRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedNeighborSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_localSelectedNeighborRows_of_cutPartition_indexRows_localIncident
      (C := C) (inputs := inputs)
      (selectedRows C inputs) (indexRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-cont-20260520-local-selected-source`.

The strict selected-neighbour cut/geometric input source simultaneously
supplies the selected cut-partition rows and the local selected-neighbour
bundle.  The selected `unboundedFrontierEdgeSet` heads are projected once from
the input source; the genuine sorted-list index rows are projected from the
same pointwise rows; the local incident-germ membership used by the local
sector/two-germ branch is discharged internally by the local-radius finite
drawing row. -/
noncomputable def S2_codex_cont_20260520_local_selected_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      SelectedNeighborCutPartitionGeometricOrderInputSource inputs) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs ×
      LocalSelectedNeighborSourceRows inputs := by
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
      (C := C) (inputs := inputs) source
  let indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows := by
    simpa [selectedRows] using
      S2_agent_20260520_indexrows_from_selected_neighbor_inputSource
        (C := C) (inputs := inputs) source
  exact
    ⟨selectedRows,
      S2_codex_20260520_localSelectedNeighborRows_of_cutPartition_indexRows_localIncident
        (C := C) (inputs := inputs) selectedRows indexRows⟩

set_option linter.style.longLine false in
/-- Local-sector projection of
`S2_codex_cont_20260520_local_selected_source`. -/
noncomputable def
    S2_codex_cont_20260520_local_sector_rows_of_selected_input_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      SelectedNeighborCutPartitionGeometricOrderInputSource inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  (S2_codex_cont_20260520_local_selected_source
    (C := C) (inputs := inputs) source).2.localSectorRows

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_cont_20260520_local_selected_source`. -/
noncomputable def S2_codex_cont_20260520_local_selected_source_family
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborCutPartitionGeometricOrderInputSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs ×
          LocalSelectedNeighborSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_cont_20260520_local_selected_source
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Smaller route-specific source for
`S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute`.

For the exact selected rows produced from the local selected-edge pair route,
it asks only for the honest graph-vertex angular no-between rows for those
same selected heads.  The sorted-list index row is then supplied by the
existing selected-head geometric-index reducer. -/
def S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs) :
    Prop :=
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    GeometricRotationSystem.GraphVertexAngularNoBetweenRows
      C a.1 (selectedRows.selectedNeighborRows a).left
        (selectedRows.selectedNeighborRows a).right

set_option linter.style.longLine false in
/-- Smaller route-specific residual for Carver's selected-head angular source.

The selected heads are still the exact heads produced by the
`LocalSelectedIncidentEdgePairSourceRows` route.  This source only asks for
the direct geometric fact that no outgoing unit-distance dart at the selected
carrier vertex has principal argument strictly between those two selected
heads. -/
def S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs) :
    Prop :=
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    GeometricRotationSystem.graphDartArg
        (GeometricRotationSystem.canonicalGeometricGraph C)
        a.1 (selectedRows.selectedNeighborRows a).left <
      GeometricRotationSystem.graphDartArg
        (GeometricRotationSystem.canonicalGeometricGraph C)
        a.1 (selectedRows.selectedNeighborRows a).right ∧
    forall outgoing : OutgoingUnitDistanceDart C a.1,
      outgoing.1.head ≠ (selectedRows.selectedNeighborRows a).left ->
      outgoing.1.head ≠ (selectedRows.selectedNeighborRows a).right ->
        Not
          (GeometricRotationSystem.GraphVertexAngularBetween
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right outgoing.1.head)

set_option linter.style.longLine false in
/-- Genuine-list form of the selected-head no-intervening source.

The selected heads are still the exact heads produced by the selected-edge-pair
route.  The only change from
`S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute`
is that the no-between row is stated on entries of the real
`GeometricRotationSystem.geometricOutgoingDartList`, making the primitive
principal-argument order explicit. -/
def S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs) :
    Prop :=
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    GeometricRotationSystem.graphDartArg
        (GeometricRotationSystem.canonicalGeometricGraph C)
        a.1 (selectedRows.selectedNeighborRows a).left <
      GeometricRotationSystem.graphDartArg
        (GeometricRotationSystem.canonicalGeometricGraph C)
        a.1 (selectedRows.selectedNeighborRows a).right ∧
    forall outgoing : OutgoingUnitDistanceDart C a.1,
      outgoing ∈ GeometricRotationSystem.geometricOutgoingDartList C a.1 ->
      outgoing.1.head ≠ (selectedRows.selectedNeighborRows a).left ->
      outgoing.1.head ≠ (selectedRows.selectedNeighborRows a).right ->
        Not
          (GeometricRotationSystem.GraphVertexAngularBetween
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right outgoing.1.head)

set_option linter.style.longLine false in
/-- Consecutive genuine sorted-list index rows supply the selected-head
outgoing-list no-between source for the exact selected-edge-pair route.

This is the list-level version of the angular/index reducer: the only
ordering input is that the selected heads are entries `index` and `index + 1`
of `GeometricRotationSystem.geometricOutgoingDartList`, whose strict
principal-argument ordering gives the no-between row. -/
theorem
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_of_selected_index_rows_for_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (indexRows :
      let cutSource :
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
        S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedEdgeRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows) :
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  have indexRows' :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows := by
    simpa [selectedRows, cutSource] using indexRows
  change
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.graphDartArg
          (GeometricRotationSystem.canonicalGeometricGraph C)
          a.1 (selectedRows.selectedNeighborRows a).left <
        GeometricRotationSystem.graphDartArg
          (GeometricRotationSystem.canonicalGeometricGraph C)
          a.1 (selectedRows.selectedNeighborRows a).right ∧
      forall outgoing : OutgoingUnitDistanceDart C a.1,
        outgoing ∈ GeometricRotationSystem.geometricOutgoingDartList C a.1 ->
        outgoing.1.head ≠ (selectedRows.selectedNeighborRows a).left ->
        outgoing.1.head ≠ (selectedRows.selectedNeighborRows a).right ->
          Not
            (GeometricRotationSystem.GraphVertexAngularBetween
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right outgoing.1.head)
  intro a
  rcases indexRows' a with ⟨index, index_succ_lt, hleft, hright⟩
  let L := GeometricRotationSystem.geometricOutgoingDartList C a.1
  let first : OutgoingUnitDistanceDart C a.1 :=
    L[index]'(Nat.lt_trans (Nat.lt_succ_self index) index_succ_lt)
  let second : OutgoingUnitDistanceDart C a.1 := L[index + 1]'index_succ_lt
  have hfirst_head :
      first.1.head = (selectedRows.selectedNeighborRows a).left := by
    symm
    simpa [first, L] using hleft
  have hsecond_head :
      second.1.head = (selectedRows.selectedNeighborRows a).right := by
    symm
    simpa [second, L] using hright
  have hangle_list :
      GeometricRotationSystem.graphDartArg
          (GeometricRotationSystem.canonicalGeometricGraph C)
          a.1 first.1.head <
        GeometricRotationSystem.graphDartArg
          (GeometricRotationSystem.canonicalGeometricGraph C)
          a.1 second.1.head := by
    have hrel :=
      (GeometricRotationSystem.geometricOutgoingDartList_pairwise_graphDartArg_lt
        C a.1).rel_get_of_lt
        (a := ⟨index,
          Nat.lt_trans (Nat.lt_succ_self index) index_succ_lt⟩)
        (b := ⟨index + 1, index_succ_lt⟩)
        (by simp)
    simpa [first, second, L] using hrel
  refine
    ⟨by
      simpa [hfirst_head, hsecond_head] using hangle_list, ?_⟩
  intro outgoing houtgoing hleft_ne hright_ne hbetween
  have houtgoing_ne_first : outgoing ≠ first := by
    intro h
    have hhead : outgoing.1.head = first.1.head := by
      exact congrArg (fun d : OutgoingUnitDistanceDart C a.1 => d.1.head) h
    exact hleft_ne (by simpa [hfirst_head] using hhead)
  have houtgoing_ne_second : outgoing ≠ second := by
    intro h
    have hhead : outgoing.1.head = second.1.head := by
      exact congrArg (fun d : OutgoingUnitDistanceDart C a.1 => d.1.head) h
    exact hright_ne (by simpa [hsecond_head] using hhead)
  have hno_list :
      ∀ other ∈ L, other ≠ first -> other ≠ second ->
        ¬ (GeometricRotationSystem.graphDartArg
              (GeometricRotationSystem.canonicalGeometricGraph C)
              a.1 first.1.head <
            GeometricRotationSystem.graphDartArg
              (GeometricRotationSystem.canonicalGeometricGraph C)
              a.1 other.1.head ∧
            GeometricRotationSystem.graphDartArg
              (GeometricRotationSystem.canonicalGeometricGraph C)
              a.1 other.1.head <
            GeometricRotationSystem.graphDartArg
              (GeometricRotationSystem.canonicalGeometricGraph C)
              a.1 second.1.head) := by
    simpa [first, second, L] using
      List.no_between_of_getElem_succ_pairwise_real_lt
        (xs := L)
        (weight := fun outgoing : OutgoingUnitDistanceDart C a.1 =>
          GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            a.1 outgoing.1.head)
        (hsorted :=
          GeometricRotationSystem.geometricOutgoingDartList_pairwise_graphDartArg_lt
            C a.1)
        index index_succ_lt rfl rfl
  exact
    hno_list outgoing houtgoing houtgoing_ne_first houtgoing_ne_second
      (by
        simpa [GeometricRotationSystem.GraphVertexAngularBetween,
          hfirst_head, hsecond_head] using hbetween)

set_option linter.style.longLine false in
/-- The genuine-list no-between source fills the assigned outgoing-dart source.

Every outgoing unit-distance dart is a member of the sorted geometric outgoing
list, so the reducer introduces no new angular order and keeps the selected
route heads unchanged. -/
theorem
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows := by
  dsimp [
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute,
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute]
    at listRows ⊢
  intro a
  refine ⟨(listRows a).1, ?_⟩
  intro outgoing hleft hright
  exact
    (listRows a).2 outgoing
      (GeometricRotationSystem.mem_geometricOutgoingDartList C a.1 outgoing)
      hleft hright

set_option linter.style.longLine false in
/-- Route-specific angular no-between rows fill the no-intervening
outgoing-dart source for the same selected heads.

This is the reverse eraser to Carver's outgoing-to-angular reducer below: an
arbitrary outgoing unit-distance dart already supplies the unit-distance
adjacency required by `GraphVertexAngularNoBetweenRows`. -/
theorem
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_angular_no_between_source_for_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (angularRows :
      S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows := by
  dsimp [
    S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute,
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute]
    at angularRows ⊢
  intro a
  refine ⟨(angularRows a).angle, ?_⟩
  intro outgoing hleft hright hbetween
  have hAdj :
      GraphBridge.UnitDistanceAdj C a.1 outgoing.1.head := by
    exact (GraphBridge.unitDistanceSimpleGraph_adj C a.1 outgoing.1.head).1
      (by simpa [outgoing.2] using outgoing.1.adj)
  exact (angularRows a).no_between outgoing.1.head hAdj hleft hright hbetween

set_option linter.style.longLine false in
/-- Genuine selected index rows fill the no-intervening outgoing-dart source
for the exact selected-edge-pair route.

The proof keeps the selected rows computed from `selectedEdgeRows` fixed.  The
only geometric input is the existing non-wrap consecutive index row in
`GeometricRotationSystem.geometricOutgoingDartList`; the outgoing-dart source
is obtained through the checked `GraphVertexAngularNoBetweenRows` eraser. -/
theorem
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_selected_index_rows_for_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (indexRows :
      let cutSource :
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
        S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedEdgeRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows) :
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows := by
  refine
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_angular_no_between_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows ?_
  dsimp [
    S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute]
    at indexRows ⊢
  exact
    S2_worker_20260520_selected_head_angular_no_between_of_indexRows
      (C := C) (inputs := inputs) indexRows

set_option linter.style.longLine false in
/-- The selected-edge-pair rows used by the live deleted-neighbour route. -/
noncomputable def
    S2_dyn_20260520_selected_edge_pair_rows_of_unreachableAfterDeleteInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (unreachableRows :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_agent_20260520_selected_edge_pair_source_of_neighborPairRows
    (C := C) inputs
    (unboundedFrontierCarrierNeighborPairRows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) unreachableRows)

set_option linter.style.longLine false in
/-- Live-route version of the genuine-list no-between residual.

This is pinned to the selected incident-edge pair rows produced from
`UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource`, the
current S2-A source used by the W32 handoff. -/
def S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (unreachableRows :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    Prop :=
  S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_edge_pair_rows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) unreachableRows)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-selected-outgoing-list-no-between-worker`.

The live deleted-neighbour route's selected-head outgoing-list no-between
source strictly reduces to the genuine consecutive index rows for those same
route-selected heads in `GeometricRotationSystem.geometricOutgoingDartList`. -/
theorem
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute_of_selected_index_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (unreachableRows :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs)
    (indexRows :
      let selectedEdgeRows :
          LocalSelectedIncidentEdgePairSourceRows inputs :=
        S2_dyn_20260520_selected_edge_pair_rows_of_unreachableAfterDeleteInputSource
          (C := C) (inputs := inputs) unreachableRows
      let cutSource :
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
        S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedEdgeRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows) :
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute
      (C := C) (inputs := inputs) unreachableRows :=
  S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_of_selected_index_rows_for_selectedEdgePairRoute
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_edge_pair_rows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) unreachableRows)
    indexRows

set_option linter.style.longLine false in
/-- Checked live-route reducer for claim
`S2-dyn-20260520-no-intervening-outgoing-worker`.

It keeps the selected heads from the deleted-neighbour route fixed and reduces
the assigned source to the explicit genuine `geometricOutgoingDartList`
no-between source for those same heads. -/
theorem
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_unreachableAfterDeleteRoute_of_geometric_outgoing_list_no_between_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (unreachableRows :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs)
    (listRows :
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute
        (C := C) (inputs := inputs) unreachableRows) :
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs)
      (S2_dyn_20260520_selected_edge_pair_rows_of_unreachableAfterDeleteInputSource
        (C := C) (inputs := inputs) unreachableRows) :=
  S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_edge_pair_rows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) unreachableRows)
    listRows

set_option linter.style.longLine false in
/-- No-intervening outgoing-dart rows fill Carver's selected-head angular
source for the exact selected-edge-pair route.

This is a strict reducer: the proof keeps the selected rows computed from
`selectedEdgeRows` unchanged and merely turns an arbitrary unit-distance
adjacent head into its outgoing dart at the same carrier vertex. -/
theorem
    S2_dyn_20260520_selected_head_angular_no_between_source_of_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (outgoingRows :
      S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows := by
  dsimp [
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute,
    S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute]
    at outgoingRows ⊢
  intro a
  refine
    { angle := (outgoingRows a).1
      no_between := ?_ }
  intro other hAdj hother_left hother_right hbetween
  let otherDart : UnitDistanceDart C := {
    tail := a.1
    head := other
    adj := (GraphBridge.unitDistanceSimpleGraph_adj C a.1 other).2 hAdj }
  let otherOutgoing : OutgoingUnitDistanceDart C a.1 := ⟨otherDart, rfl⟩
  exact
    (outgoingRows a).2 otherOutgoing
      (by simpa [otherOutgoing, otherDart] using hother_left)
      (by simpa [otherOutgoing, otherDart] using hother_right)
      (by simpa [otherOutgoing, otherDart] using hbetween)

set_option linter.style.longLine false in
/-- Genuine outgoing-list no-between rows directly fill the selected-edge
route's angular no-between source for the same selected heads.

This is only a composition of the checked outgoing-list and outgoing-dart
erasers; the selected rows remain those computed from `selectedEdgeRows`. -/
theorem
    S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute_of_geometric_outgoing_list_no_between_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows :=
  S2_dyn_20260520_selected_head_angular_no_between_source_of_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
    (C := C) (inputs := inputs) selectedEdgeRows
    (S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows listRows)

set_option linter.style.longLine false in
/-- Route-specific primitive selected-index reducer from genuine geometric
outgoing-list order rows.

This is the lower S2-C source surface for the selected-edge-pair route: once
the exact `selectedRows` computed from `selectedEdgeRows` have genuine
non-wrap consecutive rows in
`GeometricRotationSystem.geometricOutgoingDartList`, the primitive selected
index rows follow directly. -/
theorem
    S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_geometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (geometricRows :
      let cutSource :
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
        S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedEdgeRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
        selectedRows) :
    let cutSource :
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
      S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedEdgeRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
      selectedRows := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  have geometricRows' :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
        selectedRows := by
    simpa [selectedRows, cutSource] using geometricRows
  exact
    unboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows_of_geometricOrderRows
      (C := C) (inputs := inputs) geometricRows'

set_option linter.style.longLine false in
/-- Pointwise genuine sorted-list geometric order source for the selected heads
produced by the current selected-edge-pair route.

The selected rows are exactly the rows obtained from
`LocalSelectedIncidentEdgePairSourceRows` through the cut-partition/local
two-germ reducer.  This source asks only for a non-wrap consecutive row in
`GeometricRotationSystem.geometricOutgoingDartList` for those same selected
heads. -/
def S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs) :
    Prop :=
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    Nonempty
      (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
        C a.1 (selectedRows.selectedNeighborRows a).left
          (selectedRows.selectedNeighborRows a).right)

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-geometric-order-source-family`.

Pointwise genuine selected-head geometric order rows directly supply the
selected-edge-pair route's outgoing-list no-between source.  This uses the
real `GeometricRotationSystem.geometricOutgoingDartList` no-between API and
does not pass through identity cyclic order or an induced frontier graph. -/
theorem
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (geometricRows :
      S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  have geometricRows' :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) := by
    simpa [S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute,
      selectedRows, cutSource] using geometricRows
  change
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.graphDartArg
          (GeometricRotationSystem.canonicalGeometricGraph C)
          a.1 (selectedRows.selectedNeighborRows a).left <
        GeometricRotationSystem.graphDartArg
          (GeometricRotationSystem.canonicalGeometricGraph C)
          a.1 (selectedRows.selectedNeighborRows a).right ∧
      forall outgoing : OutgoingUnitDistanceDart C a.1,
        outgoing ∈ GeometricRotationSystem.geometricOutgoingDartList C a.1 ->
        outgoing.1.head ≠ (selectedRows.selectedNeighborRows a).left ->
        outgoing.1.head ≠ (selectedRows.selectedNeighborRows a).right ->
          Not
            (GeometricRotationSystem.GraphVertexAngularBetween
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right outgoing.1.head)
  intro a
  rcases geometricRows' a with ⟨row⟩
  simpa using
    GeometricRotationSystem.geometricOutgoingDartList_no_between_of_graphVertexGeometricAngularNeighborSelectionRow
      row

set_option linter.style.longLine false in
/-- Family form of the selected-edge route outgoing-list no-between reducer.

For each finite drawing input, the selected heads are still those computed from
the supplied `LocalSelectedIncidentEdgePairSourceRows`; the lower source is
only a genuine non-wrap neighbour row in the sorted
`GeometricRotationSystem.geometricOutgoingDartList` at those heads. -/
theorem
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_family_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
          (C := C) (inputs := inputs) (selectedEdgeRows C inputs) := by
  intro m C inputs
  exact
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows
      (C := C) (inputs := inputs)
      (selectedEdgeRows C inputs) (geometricRows C inputs)

set_option linter.style.longLine false in
/-- Pointwise genuine geometric neighbour rows directly fill the selected-edge
route's angular no-between source for the same selected heads.

The lower source is a real non-wrap consecutive row in
`GeometricRotationSystem.geometricOutgoingDartList` at each selected carrier
vertex. -/
theorem
    S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (geometricRows :
      S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  have geometricRows' :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) := by
    simpa [S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute,
      selectedRows, cutSource] using geometricRows
  change
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.GraphVertexAngularNoBetweenRows
        C a.1 (selectedRows.selectedNeighborRows a).left
          (selectedRows.selectedNeighborRows a).right
  intro a
  exact
    Nonempty.elim (geometricRows' a) fun row =>
      GeometricRotationSystem.graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
        row

set_option linter.style.longLine false in
/-- Live deleted-neighbour route form of
`S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows`.

The selected heads are exactly those obtained from the
`UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource`
route; the remaining input is only the pointwise genuine geometric-neighbour
selection row for those heads. -/
theorem
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute_of_graph_vertex_geometric_order_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (unreachableRows :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs)
    (geometricRows :
      S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs)
        (S2_dyn_20260520_selected_edge_pair_rows_of_unreachableAfterDeleteInputSource
          (C := C) (inputs := inputs) unreachableRows)) :
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute
      (C := C) (inputs := inputs) unreachableRows :=
  S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_edge_pair_rows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) unreachableRows)
    geometricRows

set_option linter.style.longLine false in
/-- Family form for the live deleted-neighbour route. -/
theorem
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_family_for_unreachableAfterDeleteRoute_of_graph_vertex_geometric_order_rows
    (unreachableRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs)
            (S2_dyn_20260520_selected_edge_pair_rows_of_unreachableAfterDeleteInputSource
              (C := C) (inputs := inputs) (unreachableRows C inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute
          (C := C) (inputs := inputs) (unreachableRows C inputs) := by
  intro m C inputs
  exact
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute_of_graph_vertex_geometric_order_rows
      (C := C) (inputs := inputs) (unreachableRows C inputs)
      (geometricRows C inputs)

set_option linter.style.longLine false in
/-- The route-specific graph-vertex geometric row source follows from the
strictly lower honest angular no-between rows for the same selected heads.

The selected rows remain exactly those produced from `selectedEdgeRows`; the
proof only uses the real selected carrier incidences to discharge the
unit-distance hypotheses of the generic
`GeometricRotationSystem.geometricOutgoingDartList` reducer. -/
theorem
    S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_angular_no_between
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (angularRows :
      S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  have angularRows' :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexAngularNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right := by
    simpa [
      S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute,
      selectedRows, cutSource] using angularRows
  change
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right)
  intro a
  let cutRows := selectedRows.selectedNeighborRows a
  have hleft_canonical : (canonicalGraph C).Adj a.1 cutRows.left := by
    rcases cutRows.left_edge with h | h
    · exact unboundedFrontierEdgeSet_adj h
    · exact canonicalAdj_symm (unboundedFrontierEdgeSet_adj h)
  have hright_canonical : (canonicalGraph C).Adj a.1 cutRows.right := by
    rcases cutRows.right_edge with h | h
    · exact unboundedFrontierEdgeSet_adj h
    · exact canonicalAdj_symm (unboundedFrontierEdgeSet_adj h)
  have hleft_unit : GraphBridge.UnitDistanceAdj C a.1 cutRows.left :=
    ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 cutRows.left).1
      hleft_canonical
  have hright_unit : GraphBridge.UnitDistanceAdj C a.1 cutRows.right :=
    ((canonicalGraph C).adj_iff_unitDistanceAdj a.1 cutRows.right).1
      hright_canonical
  exact
    GeometricRotationSystem.exists_graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
      hleft_unit hright_unit
      (by simpa [cutRows] using angularRows' a)

set_option linter.style.longLine false in
/-- The route-specific graph-vertex geometric row source follows directly
from the genuine outgoing-list no-between source for the same selected heads.

This is the sorted-list face of
`S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_angular_no_between`:
the only order input is the real
`GeometricRotationSystem.geometricOutgoingDartList` no-between row, which is
erased to the angular row before the adjacent-index row is recovered. -/
theorem
    S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_geometric_outgoing_list_no_between_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows :=
  S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_angular_no_between
    (C := C) (inputs := inputs) selectedEdgeRows
    (S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute_of_geometric_outgoing_list_no_between_source
      (C := C) (inputs := inputs) selectedEdgeRows listRows)

set_option linter.style.longLine false in
/-- Existing genuine outgoing-list no-between rows, stated with the reusable
`GraphVertexGeometricOutgoingListNoBetweenRows` structure, strictly reduce the
selected-edge-pair geometric order source.

The selected heads are still computed from `selectedEdgeRows`; the proof only
forgets the existing sorted-list row to `GraphVertexAngularNoBetweenRows`, then
uses the checked angular-to-index reducer. -/
theorem
    S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_geometric_outgoing_list_no_between_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      let cutSource :
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
        S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedEdgeRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows := by
  refine
    S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_angular_no_between
      (C := C) (inputs := inputs) selectedEdgeRows ?_
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  have listRows' :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right := by
    simpa [selectedRows, cutSource] using listRows
  change
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.GraphVertexAngularNoBetweenRows
        C a.1 (selectedRows.selectedNeighborRows a).left
          (selectedRows.selectedNeighborRows a).right
  intro a
  exact (listRows' a).toGraphVertexAngularNoBetweenRows

set_option linter.style.longLine false in
/-- Selected incident-edge route: boundary-free angular no-between rows for the
same selected heads produce the reusable outgoing-list no-between structure.

The selected rows are exactly those computed from `selectedEdgeRows` by the
current cut-partition/local-two-germ route.  The proof only converts the local
angular row to `GraphVertexAngularNoBetweenRows` and then restricts it to the
real sorted `GeometricRotationSystem.geometricOutgoingDartList`. -/
theorem
    S2_codex_cont_20260520_selected_head_graphVertexGeometricOutgoingListNoBetweenRows_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (angularRows :
      let cutSource :
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
        S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedEdgeRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        BoundaryFreeGraphVertexAngularNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    let cutSource :
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
      S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedEdgeRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
        C a.1 (selectedRows.selectedNeighborRows a).left
          (selectedRows.selectedNeighborRows a).right := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  have angularRows' :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        BoundaryFreeGraphVertexAngularNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right := by
    simpa [selectedRows, cutSource] using angularRows
  change
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
        C a.1 (selectedRows.selectedNeighborRows a).left
          (selectedRows.selectedNeighborRows a).right
  intro a
  exact
    GeometricRotationSystem.graphVertexGeometricOutgoingListNoBetweenRows_of_graphVertexAngularNoBetweenRows
      (graphVertexAngularNoBetweenRows_of_boundaryFreeGraphVertexAngularNoBetweenRows
        (angularRows' a))

set_option linter.style.longLine false in
/-- Selected incident-edge route: the existing selected-head outgoing-list
no-between source follows from boundary-free angular no-between rows for the
same selected heads. -/
theorem
    S2_codex_cont_20260520_selected_head_geometricOutgoingListNoBetween_source_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (angularRows :
      let cutSource :
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
        S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedEdgeRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        BoundaryFreeGraphVertexAngularNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  have listRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right := by
    simpa [selectedRows, cutSource] using
      S2_codex_cont_20260520_selected_head_graphVertexGeometricOutgoingListNoBetweenRows_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
        (C := C) (inputs := inputs) selectedEdgeRows angularRows
  dsimp [
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute]
  intro a
  exact ⟨(listRows a).angle, (listRows a).no_between⟩

set_option linter.style.longLine false in
/-- The exact lower angular residual for the local selected-edge/no-third-germ
route used to produce the selected edge rows. -/
def S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSource :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    Prop :=
  S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_edge_pair_source
      (C := C) (inputs := inputs) localSource)

set_option linter.style.longLine false in
/-- Exact local-route source asking for genuine geometric neighbour rows at the
selected heads produced from `localSource`. -/
def
    S2_dyn_20260520_selected_head_geometric_order_row_source_for_localSelectedNoThirdGermRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSource :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    Prop :=
  S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_edge_pair_source
      (C := C) (inputs := inputs) localSource)

set_option linter.style.longLine false in
/-- Genuine selected-head geometric neighbour rows fill the local selected-head
angular no-between source.

The selected heads are exactly those obtained by
`S2_dyn_20260520_selected_edge_pair_source localSource`. -/
theorem
    S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute_of_graph_vertex_geometric_order_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSource :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs)
    (geometricRows :
      S2_dyn_20260520_selected_head_geometric_order_row_source_for_localSelectedNoThirdGermRoute
        (C := C) (inputs := inputs) localSource) :
    S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute
      (C := C) (inputs := inputs) localSource :=
  S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_edge_pair_source
      (C := C) (inputs := inputs) localSource)
    geometricRows

set_option linter.style.longLine false in
/-- The exact lower no-intervening residual for the local selected-edge route.

This keeps the selected heads fixed by
`S2_dyn_20260520_selected_edge_pair_source localSource`; the only remaining
claim is that no outgoing unit-distance dart lies strictly between those two
heads in the genuine geometric order. -/
def
    S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_localSelectedNoThirdGermRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSource :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    Prop :=
  S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_edge_pair_source
      (C := C) (inputs := inputs) localSource)

set_option linter.style.longLine false in
/-- No-intervening outgoing-dart rows supply the local selected-head angular
source used by the current W32 route.

The proof is just the selected-edge route eraser applied to the selected edge
pairs computed from `localSource`; no endpoint or boundary-cycle rows are
introduced. -/
theorem
    S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute_of_no_intervening_outgoing_dart
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSource :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs)
    (outgoingRows :
      S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_localSelectedNoThirdGermRoute
        (C := C) (inputs := inputs) localSource) :
    S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute
      (C := C) (inputs := inputs) localSource :=
  S2_dyn_20260520_selected_head_angular_no_between_source_of_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_edge_pair_source
      (C := C) (inputs := inputs) localSource)
    outgoingRows

set_option linter.style.longLine false in
/-- Genuine outgoing-list no-between rows are enough for the local
selected-head angular source.

This is the practical local leaf for downstream workers: prove the
no-between row on `GeometricRotationSystem.geometricOutgoingDartList` for the
selected heads from `localSource`, and the existing erasers produce the
angular source consumed by W32. -/
theorem
    S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute_of_geometric_outgoing_list_no_between
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSource :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs)
    (listRows :
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs)
        (S2_dyn_20260520_selected_edge_pair_source
          (C := C) (inputs := inputs) localSource)) :
    S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute
      (C := C) (inputs := inputs) localSource :=
  S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute_of_no_intervening_outgoing_dart
    (C := C) (inputs := inputs) localSource
    (S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs)
      (S2_dyn_20260520_selected_edge_pair_source
        (C := C) (inputs := inputs) localSource)
      listRows)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-selected-head-geometric-order-source`.

For the selected heads produced by
`S2_dyn_20260520_selected_edge_pair_source localSource`, honest angular
no-between rows supply genuine non-wrap consecutive rows in
`GeometricRotationSystem.geometricOutgoingDartList`. -/
theorem S2_dyn_20260520_selected_head_geometric_order_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSource :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs)
    (angularRows :
      S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute
        (C := C) (inputs := inputs) localSource) :
    S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs)
      (S2_dyn_20260520_selected_edge_pair_source
        (C := C) (inputs := inputs) localSource) :=
  S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_angular_no_between
    (C := C) (inputs := inputs)
    (S2_dyn_20260520_selected_edge_pair_source
      (C := C) (inputs := inputs) localSource)
    angularRows

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-geometric-order-source-rows`.

After the selected-edge-pair route has produced its selected cut-partition
rows, it is enough to prove the pointwise genuine geometric angular-neighbour
selection row for those exact selected heads.  The result is the selected
neighbour geometric-order package, with no identity angular order, final cycle
shortcut, induced frontier graph, or endpoint chord shortcut. -/
noncomputable def S2_dyn_20260520_geometric_order_source_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (geometricRows :
      S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    let cutSource :
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
      S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedEdgeRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
      selectedRows := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  have geometricRows' :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) := by
    simpa [S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute,
      selectedRows, cutSource] using geometricRows
  exact
    { geometricOrderRows := geometricRows' }

set_option linter.style.longLine false in
/-- Claim `S2-codex-cont-20260520-selected-geometric-order-source`.

Actual selected `unboundedFrontierEdgeSet` incidences determine the selected
cut rows, and genuine pointwise outgoing-list no-between rows for those same
selected heads supply the selected geometric-order rows.  The order input is
the reusable `GraphVertexGeometricOutgoingListNoBetweenRows` row over
`GeometricRotationSystem.geometricOutgoingDartList`; it is first converted to
the non-wrap geometric neighbour-selection rows and then packaged into the
selected carrier source. -/
noncomputable def
    S2_codex_cont_20260520_selected_geometric_order_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      let cutSource :
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
        S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedEdgeRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    let cutSource :
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
      S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedEdgeRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
      selectedRows := by
  exact
    S2_dyn_20260520_geometric_order_source_rows
      (C := C) (inputs := inputs) selectedEdgeRows
      (S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_geometric_outgoing_list_no_between_rows
        (C := C) (inputs := inputs) selectedEdgeRows listRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_cont_20260520_selected_geometric_order_source`.

For every finite drawing input, the selected heads come from the supplied
actual selected incident-edge source, while the order source is the genuine
pointwise `GraphVertexGeometricOutgoingListNoBetweenRows` family for exactly
those heads. -/
noncomputable def
    S2_codex_cont_20260520_selected_geometric_order_source_family
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
          selectedRows := by
  intro m C inputs
  exact
    S2_codex_cont_20260520_selected_geometric_order_source
      (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
      (by
        simpa using listRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-selected-index-route-worker`.

Strict reduction for the selected-index route.  The local selected-edge pair
rows determine the cut-partition rows through the existing local two-germ
route; the remaining smaller source is the honest selected-head graph-vertex
angular no-between family for those exact route-selected heads. -/
theorem S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (angularRows :
      S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    let cutSource :
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
      S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedEdgeRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
      selectedRows := by
  dsimp [
    S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute]
    at angularRows ⊢
  exact
    S2_worker_20260520_selected_geometric_index_source_of_graphVertexAngularNoBetweenRows
      (C := C) (inputs := inputs) angularRows

set_option linter.style.longLine false in
/-- The honest angular no-between source is a smaller route-specific source
for `S2_dyn_20260520_geometric_order_source_rows`.

The existing angular/index reducer first finds adjacent entries in the genuine
`GeometricRotationSystem.geometricOutgoingDartList`; those primitive indices
are then packaged as the selected-neighbour geometric-order rows. -/
noncomputable def
    S2_dyn_20260520_geometric_order_source_rows_of_angular_no_between
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (angularRows :
      S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    let cutSource :
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
      S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedEdgeRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
      selectedRows := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  have indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows := by
    simpa [selectedRows, cutSource] using
      S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows angularRows
  exact
    S2_agent_selected_geometric_order_source
      (C := C) (inputs := inputs) (selectedRows := selectedRows) indexRows

set_option linter.style.longLine false in
/-- Selected-index route using the smaller no-intervening outgoing-dart
residual for the exact selected-edge-pair heads. -/
theorem S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_no_intervening_outgoing_dart
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (outgoingRows :
      S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    let cutSource :
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
      S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedEdgeRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
      selectedRows :=
  S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute
    (C := C) (inputs := inputs) selectedEdgeRows
    (S2_dyn_20260520_selected_head_angular_no_between_source_of_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows outgoingRows)

set_option linter.style.longLine false in
/-- Selected-index route from the genuine outgoing-list no-between residual.

This keeps the selected rows derived from `LocalSelectedIncidentEdgePairSourceRows`
fixed.  The only order input is the ordinary non-wrap no-between row on entries
of `GeometricRotationSystem.geometricOutgoingDartList`; the existing erasers
then turn that row into Carver's selected-head angular source and finally into
the primitive selected index rows. -/
theorem S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_geometric_outgoing_list_no_between
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    let cutSource :
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
      S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedEdgeRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
      selectedRows :=
  S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_no_intervening_outgoing_dart
    (C := C) (inputs := inputs) selectedEdgeRows
    (S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
      (C := C) (inputs := inputs) selectedEdgeRows listRows)

set_option linter.style.longLine false in
/-- Selected-edge-route source for the actual carrier geometric-selection
input row.

The selected cut-partition rows are still computed from
`LocalSelectedIncidentEdgePairSourceRows`, so their `left` and `right` heads
are backed by actual `unboundedFrontierEdgeSet` incidences.  The only extra
order input is the genuine outgoing-list no-between row for those same heads;
it is erased to primitive indices and then to the compact geometric-selection
input source. -/
noncomputable def
    S2_agent_20260520_geometricSelectionInputSource_of_selectedEdgePairRoute_geometricOutgoingListNoBetween
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  let indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows := by
    simpa [selectedRows, cutSource] using
      S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_geometric_outgoing_list_no_between
        (C := C) (inputs := inputs) selectedEdgeRows listRows
  exact
    S2_agent_20260520_actual_carrier_neighbor_selection_of_cutPartition_indexRows
      (C := C) (inputs := inputs) selectedRows indexRows

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-local-geometric-assembly`.

Route-specific row-level assembly from selected carrier neighbours and honest
angular no-between rows.  The selected incident-edge route first supplies the
actual carrier cut-partition rows; the angular rows are reduced by the existing
sorted-outgoing-list index reducer, then the established selected-neighbour
split forgets back to the compact geometric-neighbour source rows. -/
noncomputable def
    S2_codex_current_20260520_local_geometric_assembly_of_selectedEdgePairRoute_angularNoBetween
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (angularRows :
      S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  let indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows := by
    simpa [selectedRows, cutSource] using
      S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows angularRows
  exact
    S2_codex_20260520_selected_carrier_local_source_geometricNeighborSelectionRows
      (C := C) (inputs := inputs) selectedRows
      (S2_agent_selected_geometric_order_source
        (C := C) (inputs := inputs) (selectedRows := selectedRows) indexRows)

set_option linter.style.longLine false in
/-- Genuine outgoing-list no-between rows are the sharp order input for the
same local geometric assembly.

This is the outgoing-list face of the claim above: the existing eraser first
turns the genuine `GeometricRotationSystem.geometricOutgoingDartList`
no-between rows into the selected-head angular source, then the row-level
assembly returns `UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows`
without adding a new wrapper surface. -/
noncomputable def
    S2_codex_current_20260520_local_geometric_assembly_of_selectedEdgePairRoute_geometricOutgoingListNoBetween
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs :=
  S2_codex_current_20260520_local_geometric_assembly_of_selectedEdgePairRoute_angularNoBetween
    (C := C) (inputs := inputs) selectedEdgeRows
    (S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute_of_geometric_outgoing_list_no_between_source
      (C := C) (inputs := inputs) selectedEdgeRows listRows)

set_option linter.style.longLine false in
/-- Claim `S2-codex-cont-20260520-geometric-neighbor-family-source`.

Family-level source for the compact geometric-neighbour rows from actual
selected incident `unboundedFrontierEdgeSet` rows and genuine selected-head
outgoing-list no-between rows.  The pointwise assembly keeps the selected
heads tied to `LocalSelectedIncidentEdgePairSourceRows`; the only geometric
input is the no-between row over the real
`GeometricRotationSystem.geometricOutgoingDartList` for those same heads. -/
noncomputable def
    S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_geometricOutgoingListNoBetween
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_current_20260520_local_geometric_assembly_of_selectedEdgePairRoute_geometricOutgoingListNoBetween
      (C := C) (inputs := inputs)
      (selectedEdgeRows C inputs) (listRows C inputs)

set_option linter.style.longLine false in
/-- Structured outgoing-list row face of
`S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_geometricOutgoingListNoBetween`.

This version lets callers provide the reusable
`GraphVertexGeometricOutgoingListNoBetweenRows` structure at the selected
heads computed from the same selected incident-edge rows.  It erases those
rows through the checked sorted-list geometric-order reducer and then returns
the compact `UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows`
family. -/
noncomputable def
    S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_graphVertexGeometricOutgoingListNoBetweenRows
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs := by
  refine
    S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_geometricOutgoingListNoBetween
      selectedEdgeRows ?_
  intro m C inputs
  exact
    S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows
      (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
      (S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_geometric_outgoing_list_no_between_rows
        (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        (by
          simpa using listRows C inputs))

set_option linter.style.longLine false in
/-- Family form of the selected incident-edge boundary-free-angular reducer.

This is the exact theorem-shape handoff for the current selected incident-edge
route: selected incident rows plus matching local angular no-between rows
produce the selected-head outgoing-list source used by the compact geometric
neighbour family reducer. -/
theorem
    S2_codex_cont_20260520_selected_head_geometricOutgoingListNoBetween_source_family_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          BoundaryFreeGraphVertexAngularNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
          (C := C) (inputs := inputs) (selectedEdgeRows C inputs) := by
  intro m C inputs
  exact
    S2_codex_cont_20260520_selected_head_geometricOutgoingListNoBetween_source_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
      (C := C) (inputs := inputs)
      (selectedEdgeRows C inputs)
      (by
        simpa using angularRows C inputs)

set_option linter.style.longLine false in
/-- Selected incident-edge rows plus matching boundary-free angular no-between
rows supply the compact geometric-neighbour family.

The remaining source is now the pointwise local angular no-between row for the
same selected heads; the outgoing-list row itself is produced over the genuine
`GeometricRotationSystem.geometricOutgoingDartList`. -/
noncomputable def
    S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          BoundaryFreeGraphVertexAngularNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs :=
  by
    intro m C inputs
    exact
      S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_geometricOutgoingListNoBetween
        selectedEdgeRows
        (S2_codex_cont_20260520_selected_head_geometricOutgoingListNoBetween_source_family_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
          selectedEdgeRows angularRows)
        C inputs

set_option linter.style.longLine false in
/-- Selected-edge-route source for the local selected-neighbour bundle.

This is the row-level handoff behind the boundary-free local-sector projection:
from the same selected incident-edge rows and genuine outgoing-list
no-between rows it obtains the actual carrier neighbour rows, pointwise
local-sector rows, and local two-germ rows.  The local incident-germ
membership needed for the third-germ branch is discharged internally from the
finite drawing input. -/
noncomputable def
    S2_agent_20260520_localSelectedNeighborRows_of_selectedEdgePairRoute_geometricOutgoingListNoBetween
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    LocalSelectedNeighborSourceRows inputs := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  let indexRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows := by
    simpa [selectedRows, cutSource] using
      S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_geometric_outgoing_list_no_between
        (C := C) (inputs := inputs) selectedEdgeRows listRows
  exact
    S2_codex_20260520_localSelectedNeighborRows_of_cutPartition_indexRows_localIncident
      (C := C) (inputs := inputs) selectedRows indexRows

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_20260520_localSelectedNeighborRows_of_selectedEdgePairRoute_geometricOutgoingListNoBetween`. -/
noncomputable def
    S2_agent_20260520_localSelectedNeighborRows_family_of_selectedEdgePairRoute_geometricOutgoingListNoBetween
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedNeighborSourceRows inputs := by
  intro m C inputs
  exact
    S2_agent_20260520_localSelectedNeighborRows_of_selectedEdgePairRoute_geometricOutgoingListNoBetween
      (C := C) (inputs := inputs)
      (selectedEdgeRows C inputs) (listRows C inputs)

set_option linter.style.longLine false in
/-- Family form of
`S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_geometricOrderRows`.

This is the exact selected-index family shape consumed by the W32
`selectedEdgePair_indexRows` theorem, but sourced from genuine selected-head
geometric order rows for the same `LocalSelectedIncidentEdgePairSourceRows`
route. -/
theorem S2_dyn_20260520_selected_edge_index_source_family_of_geometricOrderRows
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
          selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
          selectedRows := by
  intro m C inputs
  exact
    S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_geometricOrderRows
      (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
      (geometricRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-selected-index-geometric-source`.

Pointwise genuine selected-head geometric order rows supply the exact
dependent selected-index family required by the W32
`selectedEdgePair_indexRows` consumer.  The selected rows are still computed
from `LocalSelectedIncidentEdgePairSourceRows`, and the only order input is a
real non-wrap consecutive row in
`GeometricRotationSystem.geometricOutgoingDartList`. -/
theorem S2_dyn_20260520_selected_index_geometric_source
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
          selectedRows := by
  refine
    S2_dyn_20260520_selected_edge_index_source_family_of_geometricOrderRows
      selectedEdgeRows ?_
  intro m C inputs
  exact
    S2_dyn_20260520_geometric_order_source_rows
      (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
      (geometricRows C inputs)

set_option linter.style.longLine false in
/-- Family form of
`S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_geometric_outgoing_list_no_between`.

For every finite drawing input, a local selected-edge pair source plus the
matching genuine outgoing-list no-between rows supply the selected
`UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows` family used by
the sharp S2 handoff. -/
theorem S2_dyn_20260520_selected_edge_index_source_family_of_geometric_outgoing_list_no_between
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
          selectedRows := by
  intro m C inputs
  exact
    S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_geometric_outgoing_list_no_between
      (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
      (listRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-selected-angular-index-source`.

For the selected rows derived from the live local selected incident-edge
source, genuine outgoing-list no-between rows over
`GeometricRotationSystem.geometricOutgoingDartList` strictly reduce the
selected-head index source.  The selected heads are still the route-selected
cut-partition heads; the proof only erases the real sorted-list rows through
the checked graph-vertex geometric-order/index reducers. -/
theorem S2_codex_current_20260520_selected_angular_index_source
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
          selectedRows := by
  refine S2_dyn_20260520_selected_index_geometric_source selectedEdgeRows ?_
  intro m C inputs
  exact
    S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_geometric_outgoing_list_no_between_rows
      (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
      (listRows C inputs)

set_option linter.style.longLine false in
/-- Selected incident-edge rows plus genuine route-specific outgoing-list
no-between rows fill the strict selected-neighbour cut/geometric input source.

The selected cut rows are obtained from the actual selected incident-edge
source, while the geometric order is reduced through the existing sorted
outgoing-list-to-index route for those same selected heads. -/
noncomputable def
    S2_codex_current_20260520_selected_input_from_selectedIncidentEdgeRows_geometricOutgoingListNoBetween
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs :=
  selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricSelectionInputSource
    (C := C) (inputs := inputs)
    (S2_agent_20260520_geometricSelectionInputSource_of_selectedEdgePairRoute_geometricOutgoingListNoBetween
      (C := C) (inputs := inputs) selectedEdgeRows listRows)

set_option linter.style.longLine false in
/-- Selected incident-edge rows plus pointwise reusable genuine outgoing-list
no-between rows fill the strict selected-neighbour cut/geometric input source.

This is the `GraphVertexGeometricOutgoingListNoBetweenRows` face of the same
composition: the reusable pointwise rows are first erased to the route's
sorted-list no-between source, then Popper's selected outgoing-list/index
reducer supplies the geometric indices used by the input row. -/
noncomputable def
    S2_codex_current_20260520_selected_input_from_selectedIncidentEdgeRows_graphVertexGeometricOutgoingListNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      let cutSource :
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
        S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedEdgeRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs :=
  S2_codex_current_20260520_selected_input_from_selectedIncidentEdgeRows_geometricOutgoingListNoBetween
    (C := C) (inputs := inputs) selectedEdgeRows
    (S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows
      (C := C) (inputs := inputs) selectedEdgeRows
      (S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute_of_geometric_outgoing_list_no_between_rows
        (C := C) (inputs := inputs) selectedEdgeRows listRows))

set_option linter.style.longLine false in
/-- Claim `S2-codex-cont-20260520-selected-neighbor-input-source`.

Family-level strict reducer for the selected-neighbour input source from
actual selected `unboundedFrontierEdgeSet` incidences and genuine outgoing-list
order rows.  The selected incident-edge family supplies the two real carrier
heads at each frontier vertex; the pointwise no-between rows are read at the
selected cut rows produced from those same heads. -/
noncomputable def
    S2_codex_cont_20260520_selected_neighbor_input_source_family
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  intro m C inputs
  exact
    S2_codex_current_20260520_selected_input_from_selectedIncidentEdgeRows_graphVertexGeometricOutgoingListNoBetweenRows
      (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
      (by
        simpa using listRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-current-selected-neighbor-input-source-20260520a`.

Family-level strict reducer from actual selected incident
`unboundedFrontierEdgeSet` rows plus genuine selected-head geometric order
rows to the selected-neighbour cut/geometric input source.

The selected heads are those produced by the existing selected incident-edge
route, and the order input is the real non-wrap neighbour row in
`GeometricRotationSystem.geometricOutgoingDartList` for those same heads. -/
noncomputable def
    S2_current_selected_neighbor_input_source_20260520a_family_of_selectedIncidentEdgeRows_geometricOrderRows
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  intro m C inputs
  exact
    S2_codex_current_20260520_selected_input_from_selectedIncidentEdgeRows_geometricOutgoingListNoBetween
      (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
      (S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows
        (C := C) (inputs := inputs)
        (selectedEdgeRows C inputs) (geometricRows C inputs))

set_option linter.style.longLine false in
/-- Actual carrier degree two plus route-specific genuine outgoing-list
no-between rows fill `SelectedNeighborCutPartitionGeometricOrderInputSource`.

The selected incident-edge rows are exactly the existing
`S2_codex_current_20260520_actual_carrier_degree_two_source`; the order rows
are then reduced through the same selected-edge outgoing-list/index assembly,
so the source stays on the actual carrier-degree and genuine sorted-list
residuals. -/
noncomputable def
    S2_codex_current_20260520_selected_input_from_degree_order_of_geometricOutgoingListNoBetween
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (hdegree :
      letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
        unboundedFrontierCarrierGraph_decidableAdj C inputs
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2)
    (listRows :
      let selectedEdgeRows :
          LocalSelectedIncidentEdgePairSourceRows inputs :=
        S2_codex_current_20260520_actual_carrier_degree_two_source
          (C := C) (inputs := inputs) hdegree
      S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) selectedEdgeRows) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  let selectedEdgeRows :
      LocalSelectedIncidentEdgePairSourceRows inputs :=
    S2_codex_current_20260520_actual_carrier_degree_two_source
      (C := C) (inputs := inputs) hdegree
  exact
    S2_codex_current_20260520_selected_input_from_selectedIncidentEdgeRows_geometricOutgoingListNoBetween
      (C := C) (inputs := inputs) selectedEdgeRows
      (by
        simpa [selectedEdgeRows] using listRows)

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-selected-input-from-degree-order`.

Actual carrier degree two plus genuine pointwise
`GraphVertexGeometricOutgoingListNoBetweenRows` for the selected carrier heads
compose the strict `SelectedNeighborCutPartitionGeometricOrderInputSource`.
The degree source is the existing actual-carrier selected incident-edge source,
and the outgoing-list rows are routed through the checked selected
outgoing-list-to-index reducer. -/
noncomputable def
    S2_codex_current_20260520_selected_input_from_degree_order
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (hdegree :
      letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
        unboundedFrontierCarrierGraph_decidableAdj C inputs
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
          2)
    (listRows :
      let selectedEdgeRows :
          LocalSelectedIncidentEdgePairSourceRows inputs :=
        S2_codex_current_20260520_actual_carrier_degree_two_source
          (C := C) (inputs := inputs) hdegree
      let cutSource :
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
        S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedEdgeRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right) :
    SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  let selectedEdgeRows :
      LocalSelectedIncidentEdgePairSourceRows inputs :=
    S2_codex_current_20260520_actual_carrier_degree_two_source
      (C := C) (inputs := inputs) hdegree
  exact
    S2_codex_current_20260520_selected_input_from_selectedIncidentEdgeRows_graphVertexGeometricOutgoingListNoBetweenRows
      (C := C) (inputs := inputs) selectedEdgeRows
      (by
        simpa [selectedEdgeRows] using listRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_current_20260520_selected_input_from_degree_order`.

Actual carrier degree two supplies the selected incident
`unboundedFrontierEdgeSet` rows; the remaining source is the genuine
`GraphVertexGeometricOutgoingListNoBetweenRows` family for the selected heads
derived from those same degree-two rows. -/
noncomputable def
    S2_current_selected_neighbor_input_source_20260520a_family_of_actualCarrierDegreeTwo_geometricOutgoingListNoBetweenRows
    (hdegree :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
            unboundedFrontierCarrierGraph_decidableAdj C inputs
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
              2)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let selectedEdgeRows :
            LocalSelectedIncidentEdgePairSourceRows inputs :=
          S2_codex_current_20260520_actual_carrier_degree_two_source
            (C := C) (inputs := inputs) (hdegree C inputs)
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) selectedEdgeRows
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborCutPartitionGeometricOrderInputSource inputs := by
  intro m C inputs
  exact
    S2_codex_current_20260520_selected_input_from_degree_order
      (C := C) (inputs := inputs) (hdegree C inputs)
      (by
        simpa using listRows C inputs)

/-- Claim `S2-agent-local-sector-input-source-20260520bv`.

Global family-level handoff for the current S2 route: once every input carries
the sharp boundary-free geometric-angular local source, it supplies the
pointwise `UnboundedFrontierCarrierLocalSectorRowsAt` family required by the
selected-successor local-two-germ final cycle-row reducer. -/
noncomputable def S2_agent_local_sector_input_source_20260520bv
    (source :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeLocalSectorGeometricAngularSource inputs) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro n C inputs
  exact
    localSectorRows_of_boundaryFree_geometricAngularSource
      (C := C) (inputs := inputs) (source C inputs)

/-- Local-sector family obtained from the real pointwise local angular source
of claim `S2-agent-local-angular-real-source-20260520at`. -/
noncomputable def localSectorRows_of_local_angular_real_source_20260520at
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        BoundaryFreeGraphVertexAngularNoBetweenRows C a.1
          (neighborRows a).left.1 (neighborRows a).right.1) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2_agent_local_sector_family_from_inputs_20260520ae
    (C := C) (inputs := inputs)
    (S2_agent_local_angular_real_source_20260520at
      (C := C) (inputs := inputs) incident_edge neighborRows angularRows)

/-- Claim `S2-agent-local-sector-from-inputs-20260520au`.

Pointwise local-sector rows from the checked input-side cut-partition source
and the honest boundary-free angular no-between rows.

The cut-partition rows are first erased, using `inputs.noCutVertex`, to the
actual concrete carrier neighbour-pair rows.  The existing real angular source
then supplies the pointwise local-sector family through
`S2_agent_local_sector_family_from_inputs_20260520ae`. -/
noncomputable def S2_agent_local_sector_from_inputs_20260520au
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (incident_edge :
      AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs)
    (cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a)
    (angularRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        BoundaryFreeGraphVertexAngularNoBetweenRows C a.1
          (cutRows a).left (cutRows a).right) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  classical
  let neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a :=
    unboundedFrontierCarrierNeighborPairRows_of_noCutVertex_cutPartitionRows
      cutRows
  exact
    localSectorRows_of_local_angular_real_source_20260520at
      (C := C) (inputs := inputs) incident_edge neighborRows
      (by
        intro a
        simpa [neighborRows,
          unboundedFrontierCarrierNeighborPairRows_of_noCutVertex_cutPartitionRows,
          UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt.toNeighborPairAt,
          UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt.leftVertex,
          UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt.rightVertex]
        using angularRows a)

/-- Claim `S2-agent-ct-local-two-germ-input-source`.

Pointwise cut-partition rows alone give the carrier local-sector family.  This
strictly narrows `S2_agent_local_sector_from_inputs_20260520au`: the adjacent
endpoint incident-edge source and the separate angular no-between family are
not needed for `UnboundedFrontierCarrierLocalSectorRowsAt`, because the
cut-partition rows erase through `inputs.noCutVertex` to the actual concrete
carrier neighbour-pair rows, and those rows already determine the two local
carrier sectors. -/
noncomputable def
    S2_agent_ct_local_sector_from_cutPartitionRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
    (C := C) inputs
    (unboundedFrontierCarrierNeighborPairRows_of_noCutVertex_cutPartitionRows
      cutRows)

/-- Family form of
`S2_agent_ct_local_sector_from_cutPartitionRows_20260520`. -/
noncomputable def
    S2_agent_ct_local_sector_input_source_family_of_cutPartitionRows_20260520
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
    S2_agent_ct_local_sector_from_cutPartitionRows_20260520
      (C := C) inputs (cutRows C inputs)

set_option linter.style.longLine false in
/-- Cut-partition form of claim
`S2-codex-20260520-selected-edge-source`.

Pointwise cut-partition rows for the actual unbounded-frontier carrier erase
through the checked local-sector reducer and then to the pure selected
incident-edge source.  This keeps the selected heads tied to the same concrete
carrier rows and uses no arbitrary adjacent-frontier endpoint closure. -/
noncomputable def
    S2_codex_20260520_selected_edge_source_of_cutPartitionRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_codex_20260520_selected_edge_source
    (C := C) (inputs := inputs)
    (S2_agent_ct_local_sector_from_cutPartitionRows_20260520
      (C := C) inputs cutRows)

set_option linter.style.longLine false in
/-- Family cut-partition form of claim
`S2-codex-20260520-selected-edge-source`. -/
noncomputable def
    S2_codex_20260520_selected_edge_source_family_of_cutPartitionRows
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_20260520_selected_edge_source_of_cutPartitionRows
      (C := C) inputs (cutRows C inputs)

/-- Claim `S2-agent-cw-boundaryfree-from-deleted-neighbor`.

Compose the completed Averroes deleted-neighbour-to-cut-partition reducer with
the Lovelace cut-partition-to-local-sector reducer.  This is only the local
carrier-neighbour handoff; it does not use adjacent-endpoint incident or
closure rows, boundary cycles, selected successor rows, induced frontier
graphs, arbitrary cycles, or synthetic enclosures. -/
noncomputable def
    S2_agent_cw_local_sector_from_unreachableAfterDelete_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2_agent_ct_local_sector_from_cutPartitionRows_20260520
    (C := C) inputs
    (S2_agent_cu_neighbor_cutpartition_source_of_unreachableAfterDelete_20260520
      (C := C) (inputs := inputs) source)

/-- Family form of
`S2_agent_cw_local_sector_from_unreachableAfterDelete_20260520`. -/
noncomputable def
    S2_agent_cw_local_sector_input_source_family_of_unreachableAfterDelete_20260520
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    S2_agent_cw_local_sector_from_unreachableAfterDelete_20260520
      (C := C) inputs (source C inputs)

/-- Boundary predecessor/successor no-between rows are the boundary-free
angular rows for the same two concrete incident heads. -/
theorem boundaryFreeGraphVertexAngularNoBetweenRows_of_boundaryVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C}
    {k : Fin B.length}
    (rows :
      GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k) :
    BoundaryFreeGraphVertexAngularNoBetweenRows C (B.vertex k)
      (B.vertex (PlanarInterface.cyclicPred B.length_pos k))
      (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) := by
  exact
    { angle := rows.angle
      no_between := by
        intro other hAdj hother_pred hother_succ
        exact rows.no_between other hAdj hother_pred hother_succ }

/-- Actual boundary rows supply the precise boundary-free local angular source
consumed by `S2_agent_local_sector_family_from_inputs_20260520ae`.

For each actual unbounded-frontier carrier vertex, this chooses the predecessor
and successor boundary sides as the two concrete incident
`unboundedFrontierEdgeSet` edges, translates the honest boundary angular
no-between row to the boundary-free shape, and transports the third-germ
between row across the chosen boundary index. -/
noncomputable def
    S2_agent_local_angular_source_of_actualBoundary_thirdGermNoBetween_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
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
            B.vertex k) ∈ unboundedFrontierEdgeSet C inputs)
    (angularRows :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k)
    (third_germ_between :
      forall (k : Fin B.length) (ε : Real) (q : PlanarInterface.Point)
          (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj (B.vertex k) x ->
              q ∈ vertexIncidentGermW3 C (B.vertex k) x ε ->
                q ≠ (canonicalGraph C).point (B.vertex k) ->
                x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
                  x ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
                    GeometricRotationSystem.BoundaryPredSuccAngularBetween
                      C B k x) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Exists fun left : Fin n =>
        Exists fun right : Fin n =>
          ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
            (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
          ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
            (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
          left ≠ right ∧
          BoundaryFreeGraphVertexAngularNoBetweenRows C a.1 left right ∧
          forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      x ≠ left ->
                        x ≠ right ->
                          BoundaryFreeGraphVertexAngularBetween
                            C a.1 left right x := by
  classical
  intro a
  have hfrontier :
      (canonicalGraph C).point a.1 ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior :=
    mem_unboundedFrontierVertexSet_iff.1 a.2
  let k : Fin B.length :=
    Classical.choose ((frontier_iff_cycle_vertex a.1).1 hfrontier)
  have hk : B.vertex k = a.1 :=
    Classical.choose_spec ((frontier_iff_cycle_vertex a.1).1 hfrontier)
  let pred := PlanarInterface.cyclicPred B.length_pos k
  let succ := PlanarInterface.cyclicSucc B.length_pos k
  refine ⟨B.vertex pred, B.vertex succ, ?_, ?_, ?_, ?_, ?_⟩
  · have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
      dsimp [pred]
      exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
    have hpred_cycle_edge :
        (B.vertex pred, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs ∨
          (B.vertex k, B.vertex pred) ∈
            unboundedFrontierEdgeSet C inputs := by
      simpa [pred, hsucc_pred] using cycle_edge_mem pred
    have hpred_edge :
        (B.vertex k, B.vertex pred) ∈ unboundedFrontierEdgeSet C inputs ∨
          (B.vertex pred, B.vertex k) ∈
            unboundedFrontierEdgeSet C inputs := by
      rcases hpred_cycle_edge with h | h
      · exact Or.inr h
      · exact Or.inl h
    simpa [pred, hk] using hpred_edge
  · have hsucc_edge :
        (B.vertex k, B.vertex succ) ∈ unboundedFrontierEdgeSet C inputs ∨
          (B.vertex succ, B.vertex k) ∈
            unboundedFrontierEdgeSet C inputs := by
      simpa [succ] using cycle_edge_mem k
    simpa [succ, hk] using hsucc_edge
  · intro h
    have hidx : pred = succ := by
      exact B.simple (by simpa [pred, succ] using h)
    exact
      (PlanarInterface.cyclicPred_ne_cyclicSucc_of_three_le
        B.length_pos B.length_ge_three k) hidx
  · have hangular :
        BoundaryFreeGraphVertexAngularNoBetweenRows C (B.vertex k)
          (B.vertex pred) (B.vertex succ) := by
      simpa [pred, succ] using
        boundaryFreeGraphVertexAngularNoBetweenRows_of_boundaryVertexAngularNoBetweenRows
          (C := C) (B := B) (k := k) (angularRows k)
    simpa [hk] using hangular
  · intro ε q x hqball hqfrontier hadj hgerm hqcenter hx_pred hx_succ
    have hbetween :
        GeometricRotationSystem.BoundaryPredSuccAngularBetween C B k x :=
      third_germ_between k ε q x
        (by simpa [hk] using hqball)
        hqfrontier
        (by simpa [hk] using hadj)
        (by simpa [hk] using hgerm)
        (by simpa [hk] using hqcenter)
        (by simpa [pred] using hx_pred)
        (by simpa [succ] using hx_succ)
    simpa [BoundaryFreeGraphVertexAngularBetween,
      GeometricRotationSystem.BoundaryPredSuccAngularBetween,
      pred, succ, hk] using hbetween

/-- Local-sector family obtained by feeding the actual-boundary local angular
source into `S2_agent_local_sector_family_from_inputs_20260520ae`. -/
noncomputable def localSectorRows_of_actualBoundary_boundaryFreeAngularSource_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
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
            B.vertex k) ∈ unboundedFrontierEdgeSet C inputs)
    (angularRows :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k)
    (third_germ_between :
      forall (k : Fin B.length) (ε : Real) (q : PlanarInterface.Point)
          (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj (B.vertex k) x ->
              q ∈ vertexIncidentGermW3 C (B.vertex k) x ε ->
                q ≠ (canonicalGraph C).point (B.vertex k) ->
                x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
                  x ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
                    GeometricRotationSystem.BoundaryPredSuccAngularBetween
                      C B k x) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2_agent_local_sector_family_from_inputs_20260520ae
    (C := C) (inputs := inputs)
    (S2_agent_local_angular_source_of_actualBoundary_thirdGermNoBetween_rows
      (C := C) (inputs := inputs) B frontier_iff_cycle_vertex cycle_edge_mem
      angularRows third_germ_between)

/-- Primitive boundary-vertex exterior-sector rows erase to the carrier
local-sector rows used by the raw-orbit S2 assembly.

This belongs in the assembly layer: the heavy topology file proves the
pointwise sector rows, while this theorem only transports them across the
frontier-vertex/boundary-index equivalence. -/
noncomputable def localSectorRows_of_boundaryVertexExteriorSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  classical
  intro a
  have hfrontier :
      (canonicalGraph C).point a.1 ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior :=
    mem_unboundedFrontierVertexSet_iff.1 a.2
  let k : Fin B.length :=
    Classical.choose ((frontier_iff_cycle_vertex a.1).1 hfrontier)
  have hk : B.vertex k = a.1 :=
    Classical.choose_spec ((frontier_iff_cycle_vertex a.1).1 hfrontier)
  exact
    (sectorRows k).toLocalSectorRowsAt (a := a) (ha := hk.symm)

set_option linter.style.longLine false in
/-- Primitive boundary-vertex exterior-sector rows give the pure selected
incident-edge pair source at every actual unbounded-frontier vertex.

For each frontier vertex the boundary equivalence chooses its actual boundary
index, and the two selected heads are precisely the predecessor and successor
germs bounding the exterior sector.  The `only_selected_incident` field is read
directly from the primitive sector row's `local_two_germ` field, so this does
not pass through carrier degree or any endpoint-only closure row. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_boundaryVertexExteriorSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :
    LocalSelectedIncidentEdgePairSourceRows inputs := by
  classical
  let kOf :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} →
        Fin B.length :=
    fun a =>
      Classical.choose
        ((frontier_iff_cycle_vertex a.1).1
          (mem_unboundedFrontierVertexSet_iff.1 a.2))
  have hkOf :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        B.vertex (kOf a) = a.1 := by
    intro a
    exact
      Classical.choose_spec
        ((frontier_iff_cycle_vertex a.1).1
          (mem_unboundedFrontierVertexSet_iff.1 a.2))
  refine
    { left := fun a =>
        B.vertex (PlanarInterface.cyclicPred B.length_pos (kOf a))
      right := fun a =>
        B.vertex (PlanarInterface.cyclicSucc B.length_pos (kOf a))
      left_edge := ?_
      right_edge := ?_
      heads_ne := ?_
      only_selected_incident := ?_ }
  · intro a
    let k : Fin B.length := kOf a
    have hk : B.vertex k = a.1 := hkOf a
    change
      (a.1, B.vertex (PlanarInterface.cyclicPred B.length_pos k)) ∈
          unboundedFrontierEdgeSet C inputs ∨
        (B.vertex (PlanarInterface.cyclicPred B.length_pos k), a.1) ∈
          unboundedFrontierEdgeSet C inputs
    simpa [hk] using (sectorRows k).pred_edge
  · intro a
    let k : Fin B.length := kOf a
    have hk : B.vertex k = a.1 := hkOf a
    change
      (a.1, B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) ∈
          unboundedFrontierEdgeSet C inputs ∨
        (B.vertex (PlanarInterface.cyclicSucc B.length_pos k), a.1) ∈
          unboundedFrontierEdgeSet C inputs
    simpa [hk] using (sectorRows k).succ_edge
  · intro a h
    let k : Fin B.length := kOf a
    exact
      (sectorRows k).pred_vertex_ne_succ_vertex
        (by simpa [k] using h)
  · intro a x hedge
    let k : Fin B.length := kOf a
    have hk : B.vertex k = a.1 := hkOf a
    have hedge' :
        (B.vertex k, x) ∈ unboundedFrontierEdgeSet C inputs ∨
          (x, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
      simpa [hk] using hedge
    have hx := (sectorRows k).local_two_germ x hedge'
    rcases hx with hx | hx
    · left
      simpa [k] using hx
    · right
      simpa [k] using hx

set_option linter.style.longLine false in
/-- Family-level boundary-sector source for selected incident-edge pairs.

This is the reusable source shape for claim
`S2-codex-cont-20260520-selected-incident-edge-family`: for each input it asks
only for one actual exterior boundary cycle, the exact frontier-vertex
equivalence for that same cycle, and primitive
`BoundaryVertexExteriorSectorRowsAt` rows.  The selected heads and incident
completeness are then read directly from those actual boundary-sector rows. -/
noncomputable def
    S2_codex_cont_20260520_selected_incident_edge_family_source_of_boundaryVertexExteriorSectorRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin m,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            forall k : Fin B.length,
              BoundaryVertexExteriorSectorRowsAt inputs B k) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  classical
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose (source C inputs)
  have hsource :
      (forall v : Fin m,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
    Classical.choose_spec (source C inputs)
  exact
    localSelectedIncidentEdgePairSourceRows_of_boundaryVertexExteriorSectorRows
      (C := C) (inputs := inputs) B hsource.1 hsource.2

set_option linter.style.longLine false in
/-- Boundary-sector selected-edge rows feed the existing geometric-neighbour
family route.

This is only a composition wrapper around
`S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_graphVertexGeometricOutgoingListNoBetweenRows`.
The selected incident-edge family is produced from the actual boundary-sector
source above; the remaining order input is still the route-specific genuine
`GraphVertexGeometricOutgoingListNoBetweenRows` row for those same selected
heads. -/
noncomputable def
    S2_codex_cont_20260520_geometric_neighbor_family_source_of_boundaryVertexExteriorSectorRows_graphVertexGeometricOutgoingListNoBetweenRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin m,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            forall k : Fin B.length,
              BoundaryVertexExteriorSectorRowsAt inputs B k)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let selectedEdgeRows :
            LocalSelectedIncidentEdgePairSourceRows inputs :=
          S2_codex_cont_20260520_selected_incident_edge_family_source_of_boundaryVertexExteriorSectorRows
            source C inputs
        let cutSource :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
          S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) selectedEdgeRows
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
          S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_graphVertexGeometricOutgoingListNoBetweenRows
      (S2_codex_cont_20260520_selected_incident_edge_family_source_of_boundaryVertexExteriorSectorRows
        source)
      (by
        intro m C inputs
        simpa using listRows C inputs)
      C inputs

set_option linter.style.longLine false in
/-- Primitive boundary-sector rows also close the local frontier-star source.

The selected germs are the same actual predecessor/successor
`unboundedFrontierEdgeSet` incidences as in
`localSelectedIncidentEdgePairSourceRows_of_boundaryVertexExteriorSectorRows`.
The local radius is the finite vertex-isolation radius: a nearby noncenter
frontier point carried by an incident W3 germ first promotes to an actual
`unboundedFrontierEdgeSet` incidence, and the primitive sector row forces that
incident head to be one of the two exterior-sector germs. -/
noncomputable def
    localFrontierStarSourceRows_of_boundaryVertexExteriorSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :
    LocalRadiusSelectedEdgeSourceRows inputs := by
  classical
  refine
    localRadiusSelectedEdgeSourceRows_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs)
      (localSelectedIncidentEdgePairSourceRows_of_boundaryVertexExteriorSectorRows
        (C := C) (inputs := inputs) B frontier_iff_cycle_vertex sectorRows)

set_option linter.style.longLine false in
/-- Family wrapper for the local frontier-star source from primitive actual
boundary-sector rows. -/
noncomputable def
    S2_codex_cont_20260520_local_frontier_star_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :
    LocalRadiusSelectedEdgeSourceRows inputs :=
  localFrontierStarSourceRows_of_boundaryVertexExteriorSectorRows
    (C := C) (inputs := inputs) B frontier_iff_cycle_vertex sectorRows

/-- Reduce the input-only carrier local-sector family to the actual exterior
boundary cycle, genuine angular no-between rows, and the local exterior
point-sector row.

This keeps the residual source honest: the angular rows are the concrete
geometric rotation rows, and the local sector row is the noncenter
point-sector statement consumed by the vertex-star isolation reducer. -/
noncomputable def localSectorRows_of_actualBoundary_geometricLocalExteriorSector_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
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
          _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
            C B k) ∧
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
                        BoundaryPredSuccPointAngularBetween C B k q)) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  classical
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose source
  have hsource :=
    Classical.choose_spec source
  exact
    S2_agent_actual_exterior_sector_source
      (C := C) (inputs := inputs) B
      hsource.1
      hsource.2.1
      hsource.2.2.1
      hsource.2.2.2

/-- Point-sector/no-between rows for an actual exterior boundary cycle erase to
the input-level local-sector family.

This is the narrow local-sector handoff after the vertex-star isolation
argument has already produced the bundled `PointSectorNoBetweenSourceRows`:
the only global data still used here is the actual frontier/boundary
identification and the fact that each consecutive boundary side is an
unbounded-frontier edge. -/
noncomputable def localSectorRows_of_actualBoundary_pointSectorNoBetween_rows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_edge_openSegment_frontier :
      forall k : Fin B.length,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (B.vertex k))
            ((canonicalGraph C).point
              (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (rows : PointSectorNoBetweenSourceRows inputs B) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  classical
  intro a
  have hfrontier :
      (canonicalGraph C).point a.1 ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior :=
    mem_unboundedFrontierVertexSet_iff.1 a.2
  let k : Fin B.length :=
    Classical.choose ((frontier_iff_cycle_vertex a.1).1 hfrontier)
  have hk : B.vertex k = a.1 :=
    Classical.choose_spec ((frontier_iff_cycle_vertex a.1).1 hfrontier)
  let pred := PlanarInterface.cyclicPred B.length_pos k
  let succ := PlanarInterface.cyclicSucc B.length_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
    dsimp [pred]
    exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
  have hpred_cycle_edge :
      (B.vertex pred, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs ∨
        (B.vertex k, B.vertex pred) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [pred, hsucc_pred] using
      cycle_edge_mem_unboundedFrontierEdgeSet_or_symm_of_openSegment_frontier
        (C := C) (inputs := inputs) (B := B)
        cycle_edge_openSegment_frontier pred
  have hpred_edge :
      (B.vertex k, B.vertex pred) ∈ unboundedFrontierEdgeSet C inputs ∨
        (B.vertex pred, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
    rcases hpred_cycle_edge with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hsucc_edge :
      (B.vertex k, B.vertex succ) ∈ unboundedFrontierEdgeSet C inputs ∨
        (B.vertex succ, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [succ] using
      cycle_edge_mem_unboundedFrontierEdgeSet_or_symm_of_openSegment_frontier
        (C := C) (inputs := inputs) (B := B)
        cycle_edge_openSegment_frontier k
  exact
    unboundedFrontierCarrierLocalSectorRowsAt_of_boundary_vertex_local_frontier_germ_two
      (C := C) (inputs := inputs) (B := B) (k := k) (a := a)
      hk.symm
      (by simpa [pred] using hpred_edge)
      (by simpa [succ] using hsucc_edge)
      (rows.local_frontier_germ_two k)

/-- Existential source form of
`localSectorRows_of_actualBoundary_pointSectorNoBetween_rows`.

The output is exactly the input-level pointwise local-sector row used by the
carrier and raw-orbit reducers; the source names only the actual exterior
boundary cycle plus the checked point-sector/no-between contraction. -/
noncomputable def localSectorRows_of_actualBoundary_pointSectorNoBetween_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
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
        PointSectorNoBetweenSourceRows inputs B) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  classical
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose source
  have hsource := Classical.choose_spec source
  exact
    localSectorRows_of_actualBoundary_pointSectorNoBetween_rows
      (C := C) (inputs := inputs) B
      hsource.1 hsource.2.1 hsource.2.2

/-- Local-sector source from the explicit third-germ angular row and the
geometric no-between row on an actual exterior boundary cycle.

This composes the existing vertex-star/point-sector contraction with the
pointwise local-sector eraser above, leaving the remaining proof obligation in
the concrete geometric form: prove that any third germ lies in the
pred/succ angular sector, and prove that no unit neighbour lies strictly in
that sector. -/
noncomputable def localSectorRows_of_actualBoundary_thirdGermNoBetween_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
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
                        _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.BoundaryPredSuccAngularBetween
                          C B k x) ∧
        (forall (k : Fin B.length) (x : Fin n),
          GraphBridge.UnitDistanceAdj C (B.vertex k) x ->
            x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
              x ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
                ¬
                  _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.BoundaryPredSuccAngularBetween
                    C B k x)) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  classical
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose source
  have hsource := Classical.choose_spec source
  let rows : PointSectorNoBetweenSourceRows inputs B :=
    S2_agent_point_sector_no_between_source
      (C := C) (inputs := inputs) (B := B)
      hsource.2.2.1 hsource.2.2.2
  exact
    localSectorRows_of_actualBoundary_pointSectorNoBetween_rows
      (C := C) (inputs := inputs) B
      hsource.1 hsource.2.1 rows

/-- Connected-carrier integration with the pointwise local-sector row sourced
from boundary-free local two-germ rows. -/
theorem frontier_cover_to_connected_carrier_of_frontier_edge_point_localTwoGermRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  S2_agent_frontier_cover_to_connected_carrier_integration_of_frontier_edge_point
    inputs frontier_preconnected
    (localSectorRows_of_localTwoGermRows localTwoGermRows)

/-- Frontier-preconnected local-two-germ version of the selected raw-orbit S2
assembly using minimal repeated-tail cut rows.

This keeps the live source surface at the pointwise local topology row rather
than the already-erased local-sector family. -/
def rawOrbitCutRows_of_frontierPreconnectedLocalTwoGermRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
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
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_localTwoGermRows localTwoGermRows
  let carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected :=
    frontier_cover_to_connected_carrier_of_frontier_edge_point_localTwoGermRows
      inputs frontier_preconnected localTwoGermRows
  exact
    S2_agent_input_s2_assembly_gap_reducer_rawOrbitCutRows_of_carrierConnected
      inputs localSectorRows carrier_connected edgeRows htail hhead O
      dart_edge_openSegment_frontier cutRows

/-- Carrier-connected local-two-germ version of the selected raw-orbit S2
assembly using minimal repeated-tail cut rows.

This is the narrowest cut-row source surface once connectedness of the actual
unbounded-frontier carrier has been proved independently of cyclic coverage. -/
def rawOrbitCutRows_of_carrierConnectedLocalTwoGermRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
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
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_agent_input_s2_assembly_gap_reducer_rawOrbitCutRows_of_carrierConnected
    inputs (localSectorRows_of_localTwoGermRows localTwoGermRows)
    carrier_connected edgeRows htail hhead O dart_edge_openSegment_frontier
    cutRows

/-- Actual-exterior-arc version of
`rawOrbitCutRows_of_frontierPreconnectedLocalTwoGermRows`.

The actual-arc package supplies both the selected dart-edge frontier row and
the minimal repeated-tail cut rows through checked erasers. -/
def actualArcRows_of_frontierPreconnectedLocalTwoGermRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (actualArcRows :
      RawFaceSuccOrbitActualExteriorArcSeparationRows
        (inputs := inputs) O) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  rawOrbitCutRows_of_frontierPreconnectedLocalTwoGermRows
    inputs frontier_preconnected localTwoGermRows edgeRows htail hhead O
    (rawFaceSuccOrbit_dart_edge_openSegment_frontier_of_actualExteriorArcSeparationRows
      (inputs := inputs) O actualArcRows)
    (rawFaceSuccOrbitRepeatedTailExteriorCutRows_of_actualExteriorArcSeparationRows
      (inputs := inputs) O actualArcRows)

end

end S2LocalTwoGermAssembly
end Swanepoel
end ErdosProblems1066
