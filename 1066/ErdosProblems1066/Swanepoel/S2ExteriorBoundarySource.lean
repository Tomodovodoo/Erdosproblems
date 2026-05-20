import ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly

set_option autoImplicit false

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace ExteriorComponentTopology

open JordanTopologyFactsConcrete
open JordanTopologyFactsConcrete.MinimalFailureTopology
open FinitePlaneDrawing
open S2LocalTwoGermAssembly

variable {n : Nat}

/-! ### Strict local-sector source from actual boundary incident rows -/

set_option linter.style.longLine false in
/-- The part of `BoundaryVertexExteriorSectorRowsAt` actually needed to build
pointwise carrier local-sector rows.

The row records only the real selected predecessor/successor
`unboundedFrontierEdgeSet` fields at the boundary vertex and the corresponding
incident-edge completeness row.  It deliberately omits angular no-between and
local exterior-sector data, since those are needed for face-successor/orientation
work but not for `UnboundedFrontierCarrierLocalSectorRowsAt`. -/
structure BoundaryVertexFrontierIncidentSectorRowsAt
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) where
  pred_edge :
    (B.vertex k, B.vertex (PlanarInterface.cyclicPred B.length_pos k)) ∈
        unboundedFrontierEdgeSet C inputs ∨
      (B.vertex (PlanarInterface.cyclicPred B.length_pos k), B.vertex k) ∈
        unboundedFrontierEdgeSet C inputs
  succ_edge :
    (B.vertex k, B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) ∈
        unboundedFrontierEdgeSet C inputs ∨
      (B.vertex (PlanarInterface.cyclicSucc B.length_pos k), B.vertex k) ∈
        unboundedFrontierEdgeSet C inputs
  incident_complete :
    forall x : Fin n,
      ((B.vertex k, x) ∈ unboundedFrontierEdgeSet C inputs ∨
        (x, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs) ->
        x = B.vertex (PlanarInterface.cyclicPred B.length_pos k) ∨
          x = B.vertex (PlanarInterface.cyclicSucc B.length_pos k)

namespace BoundaryVertexFrontierIncidentSectorRowsAt

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C}
variable {k : Fin B.length}

/-- The predecessor and successor heads selected by an incident-sector row are
distinct because the boundary cycle is simple and has length at least three. -/
theorem pred_vertex_ne_succ_vertex
    (_rows : BoundaryVertexFrontierIncidentSectorRowsAt inputs B k) :
    B.vertex (PlanarInterface.cyclicPred B.length_pos k) ≠
      B.vertex (PlanarInterface.cyclicSucc B.length_pos k) := by
  intro h
  have hidx :
      PlanarInterface.cyclicPred B.length_pos k =
        PlanarInterface.cyclicSucc B.length_pos k :=
    B.simple h
  exact
    (PlanarInterface.cyclicPred_ne_cyclicSucc_of_three_le
      B.length_pos B.length_ge_three k) hidx

/-- The reduced incident-sector row erases directly to the concrete carrier
local-sector row at the matching boundary vertex. -/
def toLocalSectorRowsAt
    (rows : BoundaryVertexFrontierIncidentSectorRowsAt inputs B k)
    {a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}
    (ha : a.1 = B.vertex k) :
    UnboundedFrontierCarrierLocalSectorRowsAt inputs a where
  left := B.vertex (PlanarInterface.cyclicPred B.length_pos k)
  right := B.vertex (PlanarInterface.cyclicSucc B.length_pos k)
  left_edge := by
    rcases rows.pred_edge with h | h
    · left
      simpa [ha] using h
    · right
      simpa [ha] using h
  right_edge := by
    rcases rows.succ_edge with h | h
    · left
      simpa [ha] using h
    · right
      simpa [ha] using h
  heads_ne := rows.pred_vertex_ne_succ_vertex
  only := by
    intro b hab
    have hedge :
        (B.vertex k, b.1) ∈ unboundedFrontierEdgeSet C inputs ∨
          (b.1, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
      rcases (unboundedFrontierCarrierGraph_adj_iff).1 hab with h | h
      · left
        simpa [ha] using h
      · right
        simpa [ha] using h
    exact rows.incident_complete b.1 hedge

/-- Primitive exterior-sector rows reduce to the smaller incident-sector rows
needed for local-sector construction. -/
def ofBoundaryVertexExteriorSectorRows
    (rows : BoundaryVertexExteriorSectorRowsAt inputs B k) :
    BoundaryVertexFrontierIncidentSectorRowsAt inputs B k where
  pred_edge := rows.pred_edge
  succ_edge := rows.succ_edge
  incident_complete := rows.local_two_germ

end BoundaryVertexFrontierIncidentSectorRowsAt

set_option linter.style.longLine false in
/-- Boundary incident-sector rows give pointwise local-sector rows for every
actual unbounded-frontier carrier vertex on the same boundary cycle. -/
noncomputable def localSectorRows_of_boundaryVertexFrontierIncidentSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (rows :
      forall k : Fin B.length,
        BoundaryVertexFrontierIncidentSectorRowsAt inputs B k) :
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
  exact (rows k).toLocalSectorRowsAt (a := a) hk.symm

set_option linter.style.longLine false in
/-- Actual boundary rows plus real boundary-cycle incident frontier-edge
completeness produce the reduced incident-sector rows.

The predecessor and successor edge fields are obtained from the actual boundary
edge frontier rows as concrete `unboundedFrontierEdgeSet` memberships; the
incident-completeness field is used unchanged. -/
noncomputable def
    boundaryVertexFrontierIncidentSectorRows_of_actualBoundaryRows_incidentComplete
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary) :
    forall k : Fin actualRows.boundary.length,
      BoundaryVertexFrontierIncidentSectorRowsAt inputs actualRows.boundary k := by
  intro k
  let B := actualRows.boundary
  let pred := PlanarInterface.cyclicPred B.length_pos k
  let succ := PlanarInterface.cyclicSucc B.length_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
    dsimp [pred]
    exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
  have hpred_cycle_edge :
      (B.vertex pred, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs ∨
        (B.vertex k, B.vertex pred) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [B, pred, hsucc_pred] using
      cycle_edge_mem_unboundedFrontierEdgeSet_or_symm_of_openSegment_frontier
        (C := C) (inputs := inputs) (B := B)
        actualRows.cycle_edge_openSegment_frontier pred
  have hpred_edge :
      (B.vertex k, B.vertex pred) ∈ unboundedFrontierEdgeSet C inputs ∨
        (B.vertex pred, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
    rcases hpred_cycle_edge with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hsucc_edge :
      (B.vertex k, B.vertex succ) ∈ unboundedFrontierEdgeSet C inputs ∨
        (B.vertex succ, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
    simpa [B, succ] using
      cycle_edge_mem_unboundedFrontierEdgeSet_or_symm_of_openSegment_frontier
        (C := C) (inputs := inputs) (B := B)
        actualRows.cycle_edge_openSegment_frontier k
  exact
    { pred_edge := by simpa [B, pred] using hpred_edge
      succ_edge := by simpa [B, succ] using hsucc_edge
      incident_complete := incident_complete k }

set_option linter.style.longLine false in
/-- Strict reduction of the actual-boundary local-sector source.

To get pointwise `UnboundedFrontierCarrierLocalSectorRowsAt` from an actual
exterior boundary cycle, it is enough to prove boundary-cycle incident
frontier-edge completeness.  No angular row, geometric-selection row, endpoint
closure shortcut, induced frontier graph, or arbitrary carrier cycle is used. -/
noncomputable def
    S2_dyn_20260520_local_sector_source_from_actual_boundary_incident_complete
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_boundaryVertexFrontierIncidentSectorRows
    (C := C) (inputs := inputs)
    actualRows.boundary actualRows.frontier_iff_cycle_vertex
    (boundaryVertexFrontierIncidentSectorRows_of_actualBoundaryRows_incidentComplete
      (C := C) (inputs := inputs) actualRows incident_complete)

set_option linter.style.longLine false in
/-- Same-boundary incident-sector rows source the pure selected incident-edge
pair rows used by the local S2 assembly.

The selected heads are still the predecessor and successor boundary vertices,
and the only completeness input is over actual `unboundedFrontierEdgeSet`
incidences at that boundary vertex. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_boundaryVertexFrontierIncidentSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (rows :
      forall k : Fin B.length,
        BoundaryVertexFrontierIncidentSectorRowsAt inputs B k) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_localSectorRows
    (C := C) (inputs := inputs)
    (localSectorRows_of_boundaryVertexFrontierIncidentSectorRows
      (C := C) (inputs := inputs) B frontier_iff_cycle_vertex rows)

set_option linter.style.longLine false in
/-- Actual boundary/frontier rows reduce the selected incident-edge pair source
to the exact same-boundary selected-edge incident-completeness field. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_actualBoundaryRows_incidentComplete
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_boundaryVertexFrontierIncidentSectorRows
    (C := C) (inputs := inputs)
    actualRows.boundary actualRows.frontier_iff_cycle_vertex
    (boundaryVertexFrontierIncidentSectorRows_of_actualBoundaryRows_incidentComplete
      (C := C) (inputs := inputs) actualRows incident_complete)

set_option linter.style.longLine false in
/-- Honest exterior face-orbit carrier rows source
`LocalSelectedIncidentEdgePairSourceRows`.

This is the selected-carrier/orbit leaf for the local row: the two heads are
read from the actual face-orbit carrier neighbour rows, whose edges are
selected `unboundedFrontierEdgeSet` incidences. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_faceDartOrbitExteriorCarrierRows_direct
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : FaceDartOrbitExteriorCarrierRows C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs := by
  classical
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    fun a => rows.toLocalSectorRowsAt a
  refine
    { left := fun a => (localSectorRows a).left
      right := fun a => (localSectorRows a).right
      left_edge := ?_
      right_edge := ?_
      heads_ne := ?_
      only_selected_incident := ?_ }
  · intro a
    exact (localSectorRows a).left_edge
  · intro a
    exact (localSectorRows a).right_edge
  · intro a
    exact (localSectorRows a).heads_ne
  · intro a x hedge
    let hwhole :
        UnboundedFrontierEdgeSetWholeOpenSegmentFrontier C inputs :=
      unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
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
    have hb :
        (unboundedFrontierCarrierGraph C inputs).Adj a b :=
      (unboundedFrontierCarrierGraph_adj_iff).2 hedge
    simpa [localSectorRows, b] using
      (localSectorRows a).only b hb

set_option linter.style.longLine false in
/-- Honest exterior face-orbit carrier rows source
`LocalSelectedIncidentEdgePairSourceRows`.

This public eraser is deliberately fieldwise through
`FaceDartOrbitExteriorCarrierRows.toLocalSectorRowsAt`: the selected heads are
the actual predecessor/successor orbit heads, and the selected incidences are
the corresponding `unboundedFrontierEdgeSet` rows. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_faceDartOrbitExteriorCarrierRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : FaceDartOrbitExteriorCarrierRows C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_faceDartOrbitExteriorCarrierRows_direct
    (C := C) (inputs := inputs) rows

set_option linter.style.longLine false in
/-- The checked face-dart carrier eraser exports both local selected-edge rows
and concrete carrier neighbour-pair rows.

Both components are read from the same honest `FaceDartOrbitExteriorCarrierRows`
package, whose orbit-edge fields are actual `unboundedFrontierEdgeSet`
incidences. -/
noncomputable def
    faceDartOrbitExteriorCarrierRows_to_selectedIncidentAndNeighborPairRows_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : FaceDartOrbitExteriorCarrierRows C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs ×
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :=
  ⟨localSelectedIncidentEdgePairSourceRows_of_faceDartOrbitExteriorCarrierRows
      (C := C) (inputs := inputs) rows,
    rows.toNeighborPairRows⟩

set_option linter.style.longLine false in
/-- Honest exterior face-dart carrier rows source the component-topology rows
used by the connected raw-orbit package.

The edge-chain field is the one stored in the actual face-dart carrier rows,
and the frontier-edge cover is obtained from the same selected local-sector
rows.  Thus the component package stays tied to actual
`unboundedFrontierEdgeSet` carrier edges. -/
noncomputable def
    componentTopologySourceRows_of_faceDartOrbitExteriorCarrierRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : FaceDartOrbitExteriorCarrierRows C inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  unboundedExteriorFrontierComponentTopologySourceRows_of_faceDartOrbitExteriorCarrierRows_localSectorRows_fixedSide
    (C := C) (inputs := inputs) rows rows.toLocalSectorRowsAt

set_option linter.style.longLine false in
/-- Family form of
`componentTopologySourceRows_of_faceDartOrbitExteriorCarrierRows`. -/
noncomputable def
    componentTopologySourceRows_family_of_faceDartOrbitExteriorCarrierRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FaceDartOrbitExteriorCarrierRows C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologySourceRows inputs := by
  intro m C inputs
  exact
    componentTopologySourceRows_of_faceDartOrbitExteriorCarrierRows
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-selected-carrier-source`.

Checked source reduction of the local selected incident-edge pair source to
the existing honest exterior face-orbit carrier package. -/
noncomputable def S2_codex_current_20260520_selected_carrier_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : FaceDartOrbitExteriorCarrierRows C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_faceDartOrbitExteriorCarrierRows
    (C := C) (inputs := inputs) rows

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-local-selected-incident-source`.

Family-level strict reduction of the pure selected incident-edge source to the
honest exterior face-dart carrier package.  Pointwise, this is the existing
`S2_codex_current_20260520_selected_carrier_source`; no induced frontier graph,
arbitrary boundary cycle, endpoint shortcut, or synthetic enclosure is used. -/
noncomputable def S2_codex_current_20260520_local_selected_incident_source
    (faceRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FaceDartOrbitExteriorCarrierRows C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_codex_current_20260520_selected_carrier_source
      (C := C) (inputs := inputs) (faceRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-local-selected-no-third-source`.

Endpoint-free source eraser for the selected-edge/no-third-germ row.  The
residual is exactly the honest carrier local-sector family; the proof only
uses the existing neighbor-pair/local-radius adapter, and does not use an
endpoint all-adjacent closure, induced frontier graph, arbitrary cycle,
identity angular order, or synthetic rows. -/
noncomputable def S2_dyn_20260520_local_selected_no_third_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs :=
  localSelectedNoThirdGermSource_of_localSectorRows
    (C := C) (inputs := inputs) localSectorRows

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-local-sector-source-from-actual-boundary`.

Actual boundary-sector rows source the pointwise carrier local-sector family
directly.  The selected predecessor/successor carrier edges are the concrete
`unboundedFrontierEdgeSet` fields stored in `BoundaryVertexExteriorSectorRowsAt`;
no geometric-selection row is used to manufacture the local sectors. -/
noncomputable def
    S2_dyn_20260520_local_sector_source_from_actual_boundary
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (sectorRows :
      forall k : Fin actualRows.boundary.length,
        BoundaryVertexExteriorSectorRowsAt inputs actualRows.boundary k) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_boundaryVertexExteriorSectorRows
    (C := C) (inputs := inputs)
    actualRows.boundary actualRows.frontier_iff_cycle_vertex sectorRows

set_option linter.style.longLine false in
/-- Raw-orbit same-boundary form of
`S2_dyn_20260520_local_sector_source_from_actual_boundary`.

The raw orbit supplies only the actual boundary/frontier identification for
the concrete cycle `B`; the local-sector rows still come from the primitive
sector rows on that same boundary, using their selected
`unboundedFrontierEdgeSet` predecessor/successor data. -/
noncomputable def
    S2_dyn_20260520_local_sector_source_from_rawOrbit_boundarySectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hperiod : B.length = O.period)
    (tail_eq : forall k : Fin B.length,
      (O.dart (Fin.cast hperiod k)).tail = B.vertex k)
    (frontier_iff_tail :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin O.period => (O.dart k).tail = v)
    (edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_boundaryVertexExteriorSectorRows
    (C := C) (inputs := inputs) B
    (S2_agent_explicit_B_raw_boundary_route
      (C := C) (inputs := inputs)
      O B hperiod tail_eq frontier_iff_tail edge_openSegment_frontier).1
    sectorRows

set_option linter.style.longLine false in
/-- Boundary-sector residual form of
`S2_dyn_20260520_local_selected_no_third_source`.

The residual is explicit: an actual boundary cycle, exact graph-vertex
frontier coverage for that same cycle, and primitive boundary-sector rows.
Those rows first give the honest carrier local-sector family, then the
endpoint-free selected-no-third eraser above applies. -/
noncomputable def
    S2_dyn_20260520_local_selected_no_third_source_of_boundaryVertexExteriorSectorRows
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
    UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs :=
  S2_dyn_20260520_local_selected_no_third_source
    (C := C) (inputs := inputs)
    ((Classical.choice
      (cyclicCoverageLocalSectorRows_of_boundaryVertexExteriorSectorRows
        (C := C) (inputs := inputs) B frontier_iff_cycle_vertex
        sectorRows)).2)

set_option linter.style.longLine false in
/-- Exact selected-edge boundary-successor source.

This is the honest source row below the seeded raw-orbit
`RawOrbitSelectedEdgeBoundarySuccSource`: every selected local exterior edge is
first recorded as an actual `unboundedFrontierEdgeSet` edge, and its stored
orientation is the forward successor edge of the same concrete boundary cycle.
It contains no all-adjacent endpoint incidence row. -/
def SelectedEdgeBoundarySuccessorSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C) : Prop :=
  forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point},
    UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      e ∈ unboundedFrontierEdgeSet C inputs ∧
        Exists fun j : Fin B.length =>
          e.1 = B.vertex j ∧
            e.2 =
              B.vertex (PlanarInterface.cyclicSucc B.length_pos j)

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-selected-edge-boundary-succ-source`.

Actual boundary rows plus primitive boundary-sector rows reduce the selected
boundary-successor source to the same concrete sector package.  The sector rows
provide the real `unboundedFrontierEdgeSet` predecessor/successor data and the
local two-germ exclusion; the only extra input is the selected-edge storage
orientation excluding the reverse boundary dart.  No all-adjacent endpoint
incidence source is used. -/
theorem selectedEdgeBoundarySuccessorSource_of_actualBoundaryRows_sectorRows_reverseExcluded
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (sectorRows :
      forall j : Fin actualRows.boundary.length,
        BoundaryVertexExteriorSectorRowsAt inputs actualRows.boundary j)
    (not_reverse :
      EdgeLocalRowsBoundaryReverseExcluded inputs actualRows.boundary) :
    SelectedEdgeBoundarySuccessorSource inputs actualRows.boundary := by
  intro e p edgeRows
  have he_frontier : e ∈ unboundedFrontierEdgeSet C inputs :=
    interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
      (C := C) (inputs := inputs)
      edgeRows.edge_mem edgeRows.center_in_openSegment
      edgeRows.center_frontier
  have hsucc :
      Exists fun j : Fin actualRows.boundary.length =>
        e.1 = actualRows.boundary.vertex j ∧
          e.2 =
            actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc
                actualRows.boundary.length_pos j) :=
    edgeRows_boundary_succ_of_actualBoundaryCycleFrontierEquivalenceRows
      (C := C) (inputs := inputs) actualRows
      (BoundaryVertexExteriorSectorRowsAt.boundaryCycleIncidentFrontierEdgeCompleteness
        (C := C) (inputs := inputs) (B := actualRows.boundary) sectorRows)
      (interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
        (C := C) (inputs := inputs))
      not_reverse edgeRows
  exact ⟨he_frontier, hsucc⟩

/-!
This file is the S2 source-assembly surface.  It keeps the input-level
outer-boundary source work out of the already large topology file: the local
two-germ source lives there, while this file routes that source through the
existing carrier-connectedness and raw-orbit reducers.

Live S2 target for this owner file:

`boundaryVertexExteriorSectorRows_of_inputs` should eventually construct,
from only `FinitePlanarOuterComponentInputs C`, an actual unbounded exterior
boundary cycle `B`, the graph-vertex frontier equivalence for `B`, and
`forall k : Fin B.length, BoundaryVertexExteriorSectorRowsAt inputs B k`.
The proof route is orbit-first internally: exterior seed, geometric raw
face-successor orbit, frontier-tail coverage, minimal repeated-tail cut rows,
no-cut tail injectivity, then the boundary cycle and sector rows.
-/

/-- Package a family of carrier-indexed no-third-germ rows as the boundary-free
local two-germ source. -/
noncomputable def S2_localTwoGermRows_of_noThirdGermFamily
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (left right :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} -> Fin n)
    (left_edge :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (right_edge :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (heads_ne :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        left a ≠ right a)
    (no_third_germ :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ left a ->
                    x ≠ right a ->
                      False) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a :=
  fun a =>
    unboundedFrontierCarrierLocalTwoGermRowsAt_of_no_third_germ
      (left_edge a) (right_edge a) (heads_ne a)
      (no_third_germ a)

/-- Existential source-facing form of
`S2_localTwoGermRows_of_noThirdGermFamily`.

This is the boundary-free local two-germ source the current S2 route still has
to prove at every graph vertex on the unbounded exterior frontier: select two
actual unbounded-frontier incident edges and rule out any third incident germ
for nearby frontier points. -/
noncomputable def
    S2_localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
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

/-- Local-sector rows obtained from the boundary-free two-selected-edge /
no-third-germ source.

This is the pointwise local source in the carrier route: once the two exterior
frontier germs and the no-third-germ exclusion are available at every frontier
vertex, the checked local-two-germ adapter supplies the exact local sector
rows used to prove degree two of the honest frontier carrier. -/
noncomputable def
    S2_localSectorRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
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
    (S2_localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
      (C := C) (inputs := inputs) source)

/-- Boundary-cycle predecessor/successor rows provide the boundary-free
two-selected-edge/no-third-germ source expected by the S2 local two-germ
assembly surface.

The theorem is intentionally only a bridge: the honest geometric content is in
`cycle_edge_mem`, the actual frontier/vertex equivalence, the angular
`no_between` rows, and the `third_germ_between` source row. -/
theorem
    S2_boundaryFree_twoSelectedEdges_noThirdGerm_source_of_boundaryCycle_angularRows
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
            B.vertex k) ∈
            unboundedFrontierEdgeSet C inputs)
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
                    x ≠
                        B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
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
          forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      x ≠ left ->
                        x ≠ right ->
                          False := by
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
  have hleft_edge :
      (a.1, B.vertex pred) ∈ unboundedFrontierEdgeSet C inputs ∨
        (B.vertex pred, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hedge :
        (B.vertex pred, B.vertex k) ∈
            unboundedFrontierEdgeSet C inputs ∨
          (B.vertex k, B.vertex pred) ∈
            unboundedFrontierEdgeSet C inputs := by
      simpa [pred, hsucc_pred] using cycle_edge_mem pred
    rcases hedge with hedge | hedge
    · right
      simpa [hk] using hedge
    · left
      simpa [hk] using hedge
  have hright_edge :
      (a.1, B.vertex succ) ∈ unboundedFrontierEdgeSet C inputs ∨
        (B.vertex succ, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hedge :
        (B.vertex k, B.vertex succ) ∈
            unboundedFrontierEdgeSet C inputs ∨
          (B.vertex succ, B.vertex k) ∈
            unboundedFrontierEdgeSet C inputs := by
      simpa [succ] using cycle_edge_mem k
    rcases hedge with hedge | hedge
    · left
      simpa [hk] using hedge
    · right
      simpa [hk] using hedge
  have hpred_ne_succ : B.vertex pred ≠ B.vertex succ := by
    intro h
    have hidx : pred = succ := B.simple h
    exact
      (PlanarInterface.cyclicPred_ne_cyclicSucc_of_three_le
        B.length_pos B.length_ge_three k)
        (by simpa [pred, succ] using hidx)
  refine
    ⟨B.vertex pred, B.vertex succ, hleft_edge, hright_edge,
      hpred_ne_succ, ?_⟩
  intro ε q x hqball hqfrontier hadj hgerm hqne hx_pred hx_succ
  have hx_pred' : x ≠ B.vertex pred := by
    simpa [pred] using hx_pred
  have hx_succ' : x ≠ B.vertex succ := by
    simpa [succ] using hx_succ
  have hbetween :
      GeometricRotationSystem.BoundaryPredSuccAngularBetween C B k x :=
    third_germ_between k ε q x
      (by simpa [hk] using hqball)
      hqfrontier
      (by simpa [hk] using hadj)
      (by simpa [hk] using hgerm)
      (by simpa [hk] using hqne)
      (by simpa [pred] using hx_pred')
      (by simpa [succ] using hx_succ')
  have hx_unit :
      GraphBridge.UnitDistanceAdj C (B.vertex k) x :=
    ((canonicalGraph C).adj_iff_unitDistanceAdj (B.vertex k) x).1
      (by simpa [hk] using hadj)
  exact
    (angularRows k).no_between x hx_unit hx_pred' hx_succ' hbetween

/-- Boundary-cycle local exterior-sector rows supply the stronger
boundary-free local two-germ source.

This is the pointwise local source surface below the local-sector eraser: the
cycle selects predecessor/successor carrier edges, while the open-segment
local exterior-sector row and angular no-between row prove that no third
incident germ can carry nearby exterior-frontier points. -/
noncomputable def S2_localTwoGermRows_of_boundaryCycle_openSegmentSectorRows
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
    (openSegment_local_exterior_sector :
      BoundaryFrontierOpenSegmentLocalExteriorSector inputs B)
    (no_between :
      forall (k : Fin B.length) (x : Fin n),
        GraphBridge.UnitDistanceAdj C (B.vertex k) x ->
          x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
            x ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
              ¬ GeometricRotationSystem.BoundaryPredSuccAngularBetween C B k x) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
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
  have hleft_edge :
      (a.1, B.vertex pred) ∈ unboundedFrontierEdgeSet C inputs ∨
        (B.vertex pred, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    rcases hpred_cycle_edge with h | h
    · right
      simpa [hk] using h
    · left
      simpa [hk] using h
  have hright_edge :
      (a.1, B.vertex succ) ∈ unboundedFrontierEdgeSet C inputs ∨
        (B.vertex succ, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hsucc_cycle_edge :
        (B.vertex k, B.vertex succ) ∈ unboundedFrontierEdgeSet C inputs ∨
          (B.vertex succ, B.vertex k) ∈ unboundedFrontierEdgeSet C inputs := by
      simpa [succ] using
        cycle_edge_mem_unboundedFrontierEdgeSet_or_symm_of_openSegment_frontier
          (C := C) (inputs := inputs) (B := B)
          cycle_edge_openSegment_frontier k
    rcases hsucc_cycle_edge with h | h
    · left
      simpa [hk] using h
    · right
      simpa [hk] using h
  have hheads_ne : B.vertex pred ≠ B.vertex succ := by
    intro h
    have hidx : pred = succ := B.simple h
    exact
      (PlanarInterface.cyclicPred_ne_cyclicSucc_of_three_le
        B.length_pos B.length_ge_three k) hidx
  have hlocal :
      Exists fun ε : Real =>
        0 < ε ∧
          forall q : PlanarInterface.Point,
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                q ∈ vertexIncidentGermW3 C a.1 (B.vertex pred) ε ∨
                  q ∈ vertexIncidentGermW3 C a.1 (B.vertex succ) ε := by
    have hlocalB :
        Exists fun ε : Real =>
          0 < ε ∧
            forall q : PlanarInterface.Point,
              q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) ε ->
                q ∈ frontier
                    (unboundedExteriorComponentRows C inputs).exterior ->
                  q ∈ vertexIncidentGermW3 C (B.vertex k)
                        (B.vertex pred) ε ∨
                    q ∈ vertexIncidentGermW3 C (B.vertex k)
                        (B.vertex succ) ε := by
      simpa [pred, succ] using
        exists_local_frontier_germ_two_of_vertex_star_isolation_openSegment_local_exterior_sector
          (C := C) (inputs := inputs) (B := B) k
          openSegment_local_exterior_sector
          (no_between k)
    simpa [hk, pred, succ] using hlocalB
  exact
    { left := B.vertex pred
      right := B.vertex succ
      left_edge := hleft_edge
      right_edge := hright_edge
      heads_ne := hheads_ne
      local_two_germ := hlocal }

set_option linter.style.longLine false in
/-- Actual boundary-cycle, angular, and open-segment local exterior-sector
rows produce the live S2 boundary-sector source package.

This is the compact input-facing shape consumed by the current S2 closure
route: once the genuine exterior boundary cycle is known, the remaining local
sector row is exactly `BoundaryVertexExteriorSectorRowsAt` at each boundary
vertex. -/
theorem S2_boundaryVertexExteriorSectorRows_source_of_openSegmentSectorRows
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
    (angularRows :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k)
    (openSegment_local_exterior_sector :
      BoundaryFrontierOpenSegmentLocalExteriorSector inputs B) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k := by
  refine ⟨B, frontier_iff_cycle_vertex, ?_⟩
  exact
    boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_openSegment_local_exterior_sector
      (C := C) (inputs := inputs) (B := B)
      angularRows cycle_edge_openSegment_frontier
      openSegment_local_exterior_sector

set_option linter.style.longLine false in
/-- Actual boundary rows plus geometric face-successor/orientation data and
the open-segment exterior-sector source produce the external S2 boundary-sector
package.

This is the source-assembly owner form of the open-segment route: the
face-successor rows and ordinary boundary orientation supply the angular
no-between rows, while the actual boundary rows keep the genuine exterior
cycle and its frontier equivalence visible. -/
theorem S2_boundaryVertexExteriorSectorRows_source_of_actualBoundaryRows_faceSuccOpenSegmentSector
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
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
    (openSegment_local_exterior_sector :
      BoundaryFrontierOpenSegmentLocalExteriorSector inputs
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
  S2_boundaryVertexExteriorSectorRows_source_of_openSegmentSectorRows
    (C := C) (inputs := inputs)
    actualRows.boundary
    actualRows.frontier_iff_cycle_vertex
    actualRows.cycle_edge_openSegment_frontier
    angularRows
    openSegment_local_exterior_sector

set_option linter.style.longLine false in
/-- Actual boundary rows, face-successor rows, ordinary boundary orientation,
and incident frontier-edge completeness produce the external S2 boundary-sector
package.

This is the source-owner version of the incident-completeness route: the
topology layer derives the open-segment local exterior-sector row from
incident completeness, then the actual-boundary/face-successor source theorem
keeps the concrete boundary cycle visible for the S2 consumer. -/
theorem
    S2_boundaryVertexExteriorSectorRows_source_of_actualBoundaryRows_faceSuccIncidentComplete
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
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
    (incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
  S2_boundaryVertexExteriorSectorRows_source_of_actualBoundaryRows_faceSuccOpenSegmentSector
    (C := C) (inputs := inputs)
    actualRows faceSuccRows boundary_orientation
    (boundary_frontier_openSegment_local_exterior_sector_of_boundaryCycleIncidentFrontierEdgeCompleteness
      (C := C) (inputs := inputs) (B := actualRows.boundary)
      incident_complete)

set_option linter.style.longLine false in
/-- Actual boundary rows, actual face-successor rows, boundary orientation,
and incident frontier-edge completeness also close the compressed geometric
neighbour-pair selection source.

This is the strict S2 source-composition form used by the W32-facing route:
incident completeness supplies the exterior-sector rows, and the local
two-germ assembly derives the ordinary non-wrap geometric order from those
sector rows plus the real geometric `faceSucc` rows. -/
noncomputable def
    S2_geometricSelectionInputSource_of_actualBoundaryRows_faceSuccIncidentComplete_20260520cc
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
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
    (incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  let angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k :=
    GeometricRotationSystem.boundaryVertexAngularNoBetweenRows_of_faceSuccRows_pred_arg_lt_succ_arg
      C actualRows.boundary faceSuccRows boundary_orientation
  let sectorRows :
      forall k : Fin actualRows.boundary.length,
        BoundaryVertexExteriorSectorRowsAt inputs actualRows.boundary k :=
    boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_boundaryCycleIncidentFrontierEdgeCompleteness
      (C := C) (inputs := inputs) (B := actualRows.boundary)
      angularRows actualRows.cycle_edge_openSegment_frontier incident_complete
  S2_main_geometricSelectionInputSource_of_faceSucc_sectorRows_20260520cb
    (C := C) (inputs := inputs)
    actualRows.boundary actualRows.frontier_iff_cycle_vertex faceSuccRows
    sectorRows

set_option linter.style.longLine false in
/-- Safe local-sector bridge to the compact geometric-selection input source.

Actual boundary rows and pointwise local-sector rows first prove incident
frontier-edge completeness for the same boundary cycle.  The existing
face-successor constructor then derives the selected carrier neighbour-pair
and genuine geometric-selection source, without using endpoint-chord,
induced-frontier, arbitrary-cycle, or identity-order shortcuts. -/
noncomputable def
    S2_geometricSelectionInputSource_of_actualBoundaryRows_faceSucc_localSectorRows_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
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
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_geometricSelectionInputSource_of_actualBoundaryRows_faceSuccIncidentComplete_20260520cc
    (C := C) (inputs := inputs) actualRows faceSuccRows boundary_orientation
    (S2_agent_local_sector_incident_bridge
      (C := C) (inputs := inputs) actualRows localSectorRows)

set_option linter.style.longLine false in
/-- Direct final-row eraser for the open-segment local exterior-sector route.

The theorem above exposes the live source package; this version immediately
feeds it to the checked unbounded-exterior frontier-cycle consumer. -/
noncomputable def S2_unboundedExteriorFrontierCycleRows_of_openSegmentSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
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
    (angularRows :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k)
    (openSegment_local_exterior_sector :
      BoundaryFrontierOpenSegmentLocalExteriorSector inputs B) :
    UnboundedExteriorFrontierCycleRows C inputs := by
  let sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
    boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_openSegment_local_exterior_sector
      (C := C) (inputs := inputs) (B := B)
      angularRows cycle_edge_openSegment_frontier
      openSegment_local_exterior_sector
  exact
    unboundedExteriorFrontierCycleRows_of_boundaryVertexExteriorSectorRows
      B frontier_iff_cycle_vertex sectorRows

set_option linter.style.longLine false in
/-- Source-facing S2 package from actual boundary-cycle incident completeness.

This keeps the live target on the genuine exterior boundary carrier: once
consecutive boundary edges are proved to lie on the unbounded exterior
frontier and every selected incident frontier edge at a boundary vertex is one
of the two boundary sides, the local sector package is fully inhabited. -/
theorem
    S2_boundaryVertexExteriorSectorRows_source_of_boundaryCycleIncidentFrontierEdgeCompleteness
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
    (angularRows :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k)
    (incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs B) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k := by
  refine ⟨B, frontier_iff_cycle_vertex, ?_⟩
  exact
    boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_boundaryCycleIncidentFrontierEdgeCompleteness
      (C := C) (inputs := inputs) (B := B)
      angularRows cycle_edge_openSegment_frontier incident_complete

set_option linter.style.longLine false in
/-- Claim `S2-main-co-actualSector-boundaryVertex-source-20260520co`.

Actual exterior-sector input rows are already the primitive
`BoundaryVertexExteriorSectorRowsAt` family.  This source-facing eraser keeps
the owner-file residual at the real construction point: build the actual
unbounded exterior boundary cycle, prove its frontier-vertex equivalence, and
prove the actual exterior-sector package for that same cycle. -/
theorem
    S2_boundaryVertexExteriorSectorRows_source_of_actualExteriorSectorInputSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (rows : ActualExteriorSectorInputSourceRows inputs B) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
  ⟨B, frontier_iff_cycle_vertex, rows.sectorRows⟩

set_option linter.style.longLine false in
/-- Actual exterior-sector rows directly source the local selected
incident-edge pair rows.

This is the pointwise actual-sector form of the local source family: the
selected heads and selected `unboundedFrontierEdgeSet` completeness are the
predecessor/successor fields of the same `ActualExteriorSectorInputSourceRows`
package. -/
noncomputable def
    localSelectedIncidentEdgePairSourceRows_of_actualExteriorSectorInputSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (rows : ActualExteriorSectorInputSourceRows inputs B) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_boundaryVertexExteriorSectorRows
    (C := C) (inputs := inputs) B frontier_iff_cycle_vertex rows.sectorRows

set_option linter.style.longLine false in
/-- Family-level selected incident-edge source from actual exterior-sector
rows.

This closes the local source family modulo the actual exterior-sector package:
for every input, construct one concrete exterior boundary cycle, its exact
frontier equivalence, and the same-boundary `ActualExteriorSectorInputSourceRows`.
No endpoint-only all-adjacent row, induced frontier graph, or arbitrary cycle
is introduced. -/
noncomputable def
    S2_codex_cont_20260520_selected_incident_edge_family_source_of_actualExteriorSectorInputSourceRows
    (source :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin n,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B)) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro n C inputs
  classical
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose (source C inputs)
  have hsource :
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) :=
    Classical.choose_spec (source C inputs)
  exact
    localSelectedIncidentEdgePairSourceRows_of_actualExteriorSectorInputSourceRows
      (C := C) (inputs := inputs) B hsource.1
      (Classical.choice hsource.2)

set_option linter.style.longLine false in
/-- Actual exterior-sector selected rows feed the existing geometric-neighbour
family route.

The selected incident-edge family is projected from
`ActualExteriorSectorInputSourceRows`; the remaining geometric input is still
the genuine outgoing-list no-between row for the selected heads computed by
the current selected-edge-pair route. -/
noncomputable def
    S2_codex_cont_20260520_geometric_neighbor_family_source_of_actualExteriorSectorInputSourceRows_graphVertexGeometricOutgoingListNoBetweenRows
    (source :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin n,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B))
    (listRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
        let selectedEdgeRows :
            LocalSelectedIncidentEdgePairSourceRows inputs :=
          S2_codex_cont_20260520_selected_incident_edge_family_source_of_actualExteriorSectorInputSourceRows
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
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs := by
  intro n C inputs
  exact
    S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_graphVertexGeometricOutgoingListNoBetweenRows
      (S2_codex_cont_20260520_selected_incident_edge_family_source_of_actualExteriorSectorInputSourceRows
        source)
      (by
        intro n C inputs
        simpa using listRows C inputs)
      C inputs

set_option linter.style.longLine false in
/-- Claim `S2-main-cs-actualSector-direct-cycle-eraser-20260520cs`.

Same-boundary actual exterior-sector rows erase directly to the live S2 cycle
row.  The primitive sector package already contains the successor frontier-edge
rows and local two-germ rows consumed by
`unboundedExteriorFrontierCycleRows_of_boundaryVertexExteriorSectorRows`, so
the only remaining geometric source data is the actual exterior boundary cycle
and its graph-vertex frontier equivalence. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_actualExteriorSectorInputSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (rows : ActualExteriorSectorInputSourceRows inputs B) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_boundaryVertexExteriorSectorRows
    B frontier_iff_cycle_vertex rows.sectorRows

set_option linter.style.longLine false in
/-- Family-level direct actual-sector S2 eraser.

This is the current shortest source-facing surface: for each input construct
one actual exterior boundary cycle, prove the exact frontier-vertex
equivalence for that cycle, and provide the bundled actual exterior-sector
rows on the same boundary. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_family_of_actualExteriorSectorInputSourceRows
    (source :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin n,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B)) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs := by
  intro n C inputs
  classical
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose (source C inputs)
  have hsource :
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) :=
    Classical.choose_spec (source C inputs)
  exact
    S2_unboundedExteriorFrontierCycleRows_of_actualExteriorSectorInputSourceRows
      (C := C) (inputs := inputs) B hsource.1
      (Classical.choice hsource.2)

set_option linter.style.longLine false in
/-- Direct final-row eraser for the boundary-cycle incident-completeness
route. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_boundaryCycleIncidentFrontierEdgeCompleteness
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
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
    (angularRows :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k)
    (incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs B) :
    UnboundedExteriorFrontierCycleRows C inputs := by
  let sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
    boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_boundaryCycleIncidentFrontierEdgeCompleteness
      (C := C) (inputs := inputs) (B := B)
      angularRows cycle_edge_openSegment_frontier incident_complete
  exact
    unboundedExteriorFrontierCycleRows_of_boundaryVertexExteriorSectorRows
      B frontier_iff_cycle_vertex sectorRows

set_option linter.style.longLine false in
/-- Source-facing S2 package from actual boundary-cycle edge membership,
angular rows, and incident completeness.

This is the compact handoff shape for the current input-only S2 work: the
source proof should construct the actual exterior boundary cycle, prove its
graph-vertex frontier equivalence, prove each consecutive boundary side is an
actual selected unbounded-frontier edge, and provide the geometric angular and
incident-completeness rows.  This adapter turns those rows into the primitive
`BoundaryVertexExteriorSectorRowsAt` family. -/
theorem
    S2_boundaryVertexExteriorSectorRows_source_of_boundaryCycleEdgeMem_angular_complete
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
            B.vertex k) ∈
            unboundedFrontierEdgeSet C inputs)
    (angularRows :
      forall k : Fin B.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k)
    (incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs B) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
  S2_boundaryVertexExteriorSectorRows_source_of_boundaryCycleIncidentFrontierEdgeCompleteness
    (C := C) (inputs := inputs) B frontier_iff_cycle_vertex
    (cycle_edge_openSegment_frontier_of_unboundedFrontierEdgeSet_or_symm
      cycle_edge_mem)
    angularRows incident_complete

set_option linter.style.longLine false in
/-- Family-level finite planar outer-component theorem from the compact
boundary-cycle edge-membership, angular, and incident-completeness handoff.

This is only a consumer: it chooses the supplied exterior boundary cycle for
each input and routes the compact rows through the checked primitive
`BoundaryVertexExteriorSectorRowsAt` source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_boundaryCycleEdgeMem_angular_complete
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin n,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            (forall k : Fin B.length,
              (B.vertex k,
                  B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) ∈
                  unboundedFrontierEdgeSet C inputs ∨
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k),
                  B.vertex k) ∈
                  unboundedFrontierEdgeSet C inputs) ∧
            (forall k : Fin B.length,
              GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
                C B k) ∧
            BoundaryCycleIncidentFrontierEdgeCompleteness inputs B) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_boundaryVertexExteriorSectorRows
    (fun C inputs =>
      let source := rows C inputs
      let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
        Classical.choose source
      let hsource := Classical.choose_spec source
      S2_boundaryVertexExteriorSectorRows_source_of_boundaryCycleEdgeMem_angular_complete
        (C := C) (inputs := inputs) B hsource.1 hsource.2.1
        hsource.2.2.1 hsource.2.2.2)

set_option linter.style.longLine false in
/-- Final S2 cycle rows from the compact boundary-cycle edge-membership
handoff. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_boundaryCycleEdgeMem_angular_complete
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
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
    (incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs B) :
    UnboundedExteriorFrontierCycleRows C inputs := by
  let sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
    boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_boundaryCycleIncidentFrontierEdgeCompleteness
      (C := C) (inputs := inputs) (B := B)
      angularRows
      (cycle_edge_openSegment_frontier_of_unboundedFrontierEdgeSet_or_symm
        cycle_edge_mem)
      incident_complete
  exact
    unboundedExteriorFrontierCycleRows_of_boundaryVertexExteriorSectorRows
      B frontier_iff_cycle_vertex sectorRows

/-- Boundary-vertex exterior-sector rows also expose the actual boundary-cycle
frontier-equivalence package before erasure to the final S2 row.

The sector rows carry the consecutive boundary-edge frontier statement through
`geometricFaceSucc_frontier_step`; the graph-vertex frontier equivalence stays
on the same concrete boundary cycle. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_boundaryVertexExteriorSectorRows
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
    ActualBoundaryCycleFrontierEquivalenceRows C inputs where
  boundary := B
  frontier_iff_cycle_vertex := frontier_iff_cycle_vertex
  cycle_edge_openSegment_frontier := by
    intro k p hp
    exact ((sectorRows k).geometricFaceSucc_frontier_step).2.2 p hp

/-- A selected successor frontier edge supplies the successor-dart interior
frontier point expected by the exterior-oriented raw face-successor route. -/
theorem S2_faceSucc_interior_frontier_point_of_faceSucc_frontier_edge
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    (d : UnitDistanceDart C)
    (hsucc_edge :
      ((R.faceSucc d).tail, (R.faceSucc d).head) ∈
          unboundedFrontierEdgeSet C inputs ∨
        ((R.faceSucc d).head, (R.faceSucc d).tail) ∈
          unboundedFrontierEdgeSet C inputs) :
    Exists fun q : PlanarInterface.Point =>
      PlanarInterface.InOpenSegment q
        ((canonicalGraph C).point (R.faceSucc d).tail)
        ((canonicalGraph C).point (R.faceSucc d).head) ∧
      q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior := by
  let q : PlanarInterface.Point :=
    PlanarInterface.segmentPoint
      ((canonicalGraph C).point (R.faceSucc d).tail)
      ((canonicalGraph C).point (R.faceSucc d).head)
      (1 / 2 : Real)
  have hq :
      PlanarInterface.InOpenSegment q
        ((canonicalGraph C).point (R.faceSucc d).tail)
        ((canonicalGraph C).point (R.faceSucc d).head) := by
    simpa [q] using
      midpoint_inOpenSegment
        ((canonicalGraph C).point (R.faceSucc d).tail)
        ((canonicalGraph C).point (R.faceSucc d).head)
  refine ⟨q, hq, ?_⟩
  rcases hsucc_edge with hsucc_edge | hsucc_edge
  · exact (mem_unboundedFrontierEdgeSet_iff.1 hsucc_edge).2 q hq
  · exact
      (mem_unboundedFrontierEdgeSet_iff.1 hsucc_edge).2 q
        (inOpenSegment_symm hq)

/-- Family form of
`S2_faceSucc_interior_frontier_point_of_faceSucc_frontier_edge`.

This is the reusable source row for
`S2_rawFaceSuccOrbit_dart_frontier_of_successor_interior_points`: local
edge/vertex/exterior-side arguments may prove the successor selected-edge row,
and this theorem supplies the required successor interior frontier point. -/
theorem S2_successor_interior_frontier_point_of_faceSucc_frontier_edge_step
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    (faceSucc_frontier_edge :
      forall d : UnitDistanceDart C,
        (forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point d.tail)
            ((canonicalGraph C).point d.head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) ->
        ((R.faceSucc d).tail, (R.faceSucc d).head) ∈
            unboundedFrontierEdgeSet C inputs ∨
          ((R.faceSucc d).head, (R.faceSucc d).tail) ∈
            unboundedFrontierEdgeSet C inputs) :
    forall d : UnitDistanceDart C,
      (forall p : PlanarInterface.Point,
        PlanarInterface.InOpenSegment p
          ((canonicalGraph C).point d.tail)
          ((canonicalGraph C).point d.head) ->
        p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) ->
      Exists fun q : PlanarInterface.Point =>
        PlanarInterface.InOpenSegment q
          ((canonicalGraph C).point (R.faceSucc d).tail)
          ((canonicalGraph C).point (R.faceSucc d).head) ∧
        q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior := by
  intro d hd
  exact
    S2_faceSucc_interior_frontier_point_of_faceSucc_frontier_edge
      (C := C) (inputs := inputs) (R := R) d
      (faceSucc_frontier_edge d hd)

/-- Promote one successor-dart interior frontier point to whole successor
open-segment frontier membership.

This is the exterior-oriented step isolated by the raw face-successor route:
the theorem does not claim that every `faceSucc` preserves the unbounded
exterior side.  It only erases the local source row that the successor dart has
one relative-interior point on the unbounded exterior frontier. -/
theorem S2_faceSucc_openSegment_frontier_of_faceSucc_interior_frontier_point
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    (d : UnitDistanceDart C)
    (hsucc :
      Exists fun q : PlanarInterface.Point =>
        PlanarInterface.InOpenSegment q
          ((canonicalGraph C).point (R.faceSucc d).tail)
          ((canonicalGraph C).point (R.faceSucc d).head) ∧
        q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) :
    forall p : PlanarInterface.Point,
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point (R.faceSucc d).tail)
        ((canonicalGraph C).point (R.faceSucc d).head) ->
      p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior := by
  rcases hsucc with ⟨q, hqopen, hqfrontier⟩
  have hsource :
      InteriorFrontierEdgeCarrierMembershipSource C inputs :=
    interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
  rcases UnitDistanceDart.canonicalAdj (R.faceSucc d) with he | he
  · have hcarrier :
        ((R.faceSucc d).tail, (R.faceSucc d).head) ∈
          unboundedFrontierEdgeSet C inputs :=
      hsource
        (e := ((R.faceSucc d).tail, (R.faceSucc d).head))
        (p := q) he hqopen hqfrontier
    intro p hp
    exact (mem_unboundedFrontierEdgeSet_iff.1 hcarrier).2 p hp
  · have hcarrier :
        ((R.faceSucc d).head, (R.faceSucc d).tail) ∈
          unboundedFrontierEdgeSet C inputs :=
      hsource
        (e := ((R.faceSucc d).head, (R.faceSucc d).tail))
        (p := q) he (inOpenSegment_symm hqopen) hqfrontier
    intro p hp
    exact
      (mem_unboundedFrontierEdgeSet_iff.1 hcarrier).2 p
        (inOpenSegment_symm hp)

/-- Raw-orbit propagation when every exterior-oriented successor step supplies
one successor-dart interior frontier point.

This isolates the remaining geometric source obligation from the finite orbit
iteration already proved in the topology layer. -/
theorem S2_rawFaceSuccOrbit_dart_frontier_of_successor_interior_points
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (start_openSegment_frontier :
      forall p : PlanarInterface.Point,
        PlanarInterface.InOpenSegment p
          ((canonicalGraph C).point start.tail)
          ((canonicalGraph C).point start.head) ->
        p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (successor_interior_frontier_point :
      forall d : UnitDistanceDart C,
        (forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point d.tail)
            ((canonicalGraph C).point d.head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) ->
        Exists fun q : PlanarInterface.Point =>
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (R.faceSucc d).tail)
            ((canonicalGraph C).point (R.faceSucc d).head) ∧
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) :
    forall k : Fin O.period,
      forall p : PlanarInterface.Point,
        PlanarInterface.InOpenSegment p
          ((canonicalGraph C).point (O.dart k).tail)
          ((canonicalGraph C).point (O.dart k).head) ->
        p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
  rawFaceSuccOrbit_dart_edge_openSegment_frontier_of_start_and_faceSucc_step
    O start_openSegment_frontier
    (fun d hd =>
      S2_faceSucc_openSegment_frontier_of_faceSucc_interior_frontier_point
        (C := C) (inputs := inputs) (R := R) d
        (successor_interior_frontier_point d hd))

/-- Package a raw-orbit source row from a dart-edge frontier row.

The topology layer already proves that dart-edge frontier membership supplies
the consecutive-edge frontier point and nearby-exterior rows.  This constructor
keeps the remaining rows visible: carrier cyclic coverage, period three,
local sectors, and repeated-tail separation. -/
noncomputable def S2_rawFaceSuccOrbitSourceRows_of_dart_frontier_period_cutRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (connectedRows : UnboundedFrontierCarrierCyclicCoverageRows C inputs)
    (period_ge_three : 3 <= O.period)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (repeated_tail_rows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RepeatedExteriorBoundarySeparationRows C
            (fun k : Fin O.period => (O.dart k).tail) i j) :
    RawFaceSuccOrbitSourceRows (inputs := inputs) O := by
  let sourced :=
    rawFaceSuccOrbit_source_inputs_of_dart_edge_openSegment_frontier
      O dart_edge_openSegment_frontier
  exact
    { edge_frontier_point := sourced.1
      nearby_edge_point_exterior_points := sourced.2
      connectedRows := connectedRows
      period_ge_three := period_ge_three
      repeated_tail_rows := repeated_tail_rows
      localSectorRows := localSectorRows }

/-- Source-package constructor using the exterior-oriented successor
interior-point callback.

This is the current narrow S2 handoff for the selected raw exterior orbit:
after the start dart is on the unbounded frontier and each exterior successor
has one interior frontier point, the raw source package is ready for the
existing final erasers. -/
noncomputable def
    S2_rawFaceSuccOrbitSourceRows_of_successor_interior_points_period_cutRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (start_openSegment_frontier :
      forall p : PlanarInterface.Point,
        PlanarInterface.InOpenSegment p
          ((canonicalGraph C).point start.tail)
          ((canonicalGraph C).point start.head) ->
        p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (successor_interior_frontier_point :
      forall d : UnitDistanceDart C,
        (forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point d.tail)
            ((canonicalGraph C).point d.head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) ->
        Exists fun q : PlanarInterface.Point =>
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (R.faceSucc d).tail)
            ((canonicalGraph C).point (R.faceSucc d).head) ∧
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (connectedRows : UnboundedFrontierCarrierCyclicCoverageRows C inputs)
    (period_ge_three : 3 <= O.period)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (repeated_tail_rows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RepeatedExteriorBoundarySeparationRows C
            (fun k : Fin O.period => (O.dart k).tail) i j) :
    RawFaceSuccOrbitSourceRows (inputs := inputs) O :=
  S2_rawFaceSuccOrbitSourceRows_of_dart_frontier_period_cutRows
    (C := C) (inputs := inputs) (R := R) O
    (S2_rawFaceSuccOrbit_dart_frontier_of_successor_interior_points
      (C := C) (inputs := inputs) (R := R) O
      start_openSegment_frontier successor_interior_frontier_point)
    connectedRows period_ge_three localSectorRows repeated_tail_rows

/-- Raw dart-edge frontier plus coverage of all selected frontier edges gives
the edge-chain source for the carrier route.

This is the raw-orbit way to source
`UnboundedFrontierEdgeCarrierSegmentChainConnected`: consecutive raw tails are
selected frontier edges, and the coverage row says every selected carrier edge
is one of those raw edges up to orientation. -/
theorem S2_edgeCarrierSegmentChainConnected_of_rawFaceSuccOrbit_dartFrontier_edgeCoverage
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail)) :
    UnboundedFrontierEdgeCarrierSegmentChainConnected inputs :=
  S2_agent_edge_carrier_segment_chain_source_rawFaceSuccOrbit
    (inputs := inputs) O
    (rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm_of_dart_edge_openSegment_frontier
      (inputs := inputs) O dart_edge_openSegment_frontier)
    edge_coverage

/-- Endpoint-sharing connectivity of the actual selected unbounded-frontier
edges.

This is a sharper source row for
`UnboundedFrontierEdgeCarrierSegmentChainConnected`: it talks only about the
selected edge carrier itself, and each step is another selected frontier edge
sharing an actual endpoint. -/
def UnboundedFrontierSelectedEdgeEndpointChainConnected
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    Prop :=
  forall e f :
      {e : PlanarInterface.Edge n // e ∈ unboundedFrontierEdgeSet C inputs},
    Relation.ReflTransGen
      (fun e f =>
        e.1.1 = f.1.1 ∨ e.1.1 = f.1.2 ∨
          e.1.2 = f.1.1 ∨ e.1.2 = f.1.2)
      e f

/-- Two selected frontier edges that are incident to the same selected carrier
vertex are one endpoint-sharing step apart. -/
theorem unboundedFrontierSelectedEdgeEndpointRelated_of_common_selected_endpoint
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}
    {e f : {e : PlanarInterface.Edge n //
      e ∈ unboundedFrontierEdgeSet C inputs}}
    (he : e.1.1 = a.1 ∨ e.1.2 = a.1)
    (hf : f.1.1 = a.1 ∨ f.1.2 = a.1) :
    (e.1.1 = f.1.1 ∨ e.1.1 = f.1.2 ∨
      e.1.2 = f.1.1 ∨ e.1.2 = f.1.2) := by
  rcases he with he | he <;> rcases hf with hf | hf
  · exact Or.inl (he.trans hf.symm)
  · exact Or.inr (Or.inl (he.trans hf.symm))
  · exact Or.inr (Or.inr (Or.inl (he.trans hf.symm)))
  · exact Or.inr (Or.inr (Or.inr (he.trans hf.symm)))

/-- A walk in the actual unbounded-frontier carrier graph lifts to an
endpoint-sharing selected-edge chain between selected edges incident to the
walk endpoints. -/
theorem unboundedFrontierSelectedEdgeEndpointChain_of_unboundedFrontierCarrierGraph_walk
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {a b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}}
    (walk : (unboundedFrontierCarrierGraph C inputs).Walk a b) :
    forall e f :
        {e : PlanarInterface.Edge n // e ∈ unboundedFrontierEdgeSet C inputs},
      (e.1.1 = a.1 ∨ e.1.2 = a.1) ->
        (f.1.1 = b.1 ∨ f.1.2 = b.1) ->
          Relation.ReflTransGen
            (fun e f =>
              e.1.1 = f.1.1 ∨ e.1.1 = f.1.2 ∨
                e.1.2 = f.1.1 ∨ e.1.2 = f.1.2)
            e f := by
  induction walk with
  | nil =>
      intro e f he hf
      have hstep :
          Relation.ReflTransGen
            (fun x y :
                {e : PlanarInterface.Edge n //
                  e ∈ unboundedFrontierEdgeSet C inputs} =>
              x.1.1 = y.1.1 ∨ x.1.1 = y.1.2 ∨
                x.1.2 = y.1.1 ∨ x.1.2 = y.1.2)
            e f :=
        Relation.ReflTransGen.single
          (unboundedFrontierSelectedEdgeEndpointRelated_of_common_selected_endpoint
            (C := C) (inputs := inputs) he hf)
      exact hstep
  | cons hab rest ih =>
      intro e f he hf
      rcases
          exists_unboundedFrontierCarrierEdge_of_unboundedFrontierCarrierGraph_adj
            (C := C) (inputs := inputs) hab with
        ⟨g, hg_start, hg_finish⟩
      have hstep :
          Relation.ReflTransGen
            (fun x y :
                {e : PlanarInterface.Edge n //
                  e ∈ unboundedFrontierEdgeSet C inputs} =>
              x.1.1 = y.1.1 ∨ x.1.1 = y.1.2 ∨
                x.1.2 = y.1.1 ∨ x.1.2 = y.1.2)
            e g :=
        Relation.ReflTransGen.single
          (unboundedFrontierSelectedEdgeEndpointRelated_of_common_selected_endpoint
            (C := C) (inputs := inputs) he hg_start)
      exact hstep.trans (ih g f hg_finish hf)

/-- Connectedness of the actual unbounded-frontier carrier graph gives
endpoint-sharing connectedness of the selected unbounded-frontier edge
carrier. -/
theorem unboundedFrontierSelectedEdgeEndpointChainConnected_of_unboundedFrontierCarrierGraph_connected
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected) :
    UnboundedFrontierSelectedEdgeEndpointChainConnected inputs := by
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
      unboundedFrontierSelectedEdgeEndpointChain_of_unboundedFrontierCarrierGraph_walk
        (C := C) (inputs := inputs) walk e f
        (by
          left
          rfl)
        (by
          left
          rfl)

/-- Honest topological/source rows for the actual unbounded exterior frontier
source endpoint-sharing connectedness of the selected frontier-edge carrier.

The only bridge is the already checked component-topology route to
connectedness of `unboundedFrontierCarrierGraph`; no arbitrary cycle, induced
frontier graph shortcut, convex hull, synthetic enclosure, or facade row is
introduced. -/
theorem S2_agent_edge_endpoint_chain_real_source_20260520as
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (rows : UnboundedExteriorFrontierComponentTopologySourceRows inputs) :
    UnboundedFrontierSelectedEdgeEndpointChainConnected inputs :=
  unboundedFrontierSelectedEdgeEndpointChainConnected_of_unboundedFrontierCarrierGraph_connected
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierGraph_connected_of_componentTopologySourceRows
      inputs rows)

/-- Claim `S2-agent-edge-chain-source-20260520ar`.

Actual selected frontier-edge endpoint connectivity sources the closed-segment
edge-carrier chain.  The proof only maps a selected endpoint-sharing step to
the existing geometric segment-intersection relation; it does not use induced
frontier graphs, cyclic coverage rows, arbitrary spanning cycles, or downstream
boundary-cycle data. -/
theorem S2_agent_edge_chain_source_20260520ar
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (edge_endpoint_chain :
      UnboundedFrontierSelectedEdgeEndpointChainConnected inputs) :
    UnboundedFrontierEdgeCarrierSegmentChainConnected inputs := by
  intro e f
  exact
    Relation.ReflTransGen.mono
      (fun x y hxy =>
        unboundedFrontierEdgeCarrierSegmentsMeet_of_common_endpoint
          (C := C) (inputs := inputs) (e := x) (f := y) hxy)
      (edge_endpoint_chain e f)

/-- Honest topological/source rows for the actual unbounded exterior frontier
source the selected closed-segment edge-carrier chain via the endpoint-sharing
chain above. -/
theorem S2_agent_edge_carrier_segment_chain_real_source_20260520as
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (rows : UnboundedExteriorFrontierComponentTopologySourceRows inputs) :
    UnboundedFrontierEdgeCarrierSegmentChainConnected inputs :=
  S2_agent_edge_chain_source_20260520ar
    (C := C) (inputs := inputs)
    (S2_agent_edge_endpoint_chain_real_source_20260520as inputs rows)

/-- Paired form of the honest actual-frontier carrier-chain source. -/
theorem S2_agent_edge_endpoint_and_segment_chain_real_source_20260520as
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (rows : UnboundedExteriorFrontierComponentTopologySourceRows inputs) :
    UnboundedFrontierSelectedEdgeEndpointChainConnected inputs ∧
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs := by
  exact
    ⟨S2_agent_edge_endpoint_chain_real_source_20260520as inputs rows,
      S2_agent_edge_carrier_segment_chain_real_source_20260520as inputs rows⟩

/-- Endpoint-sharing relation is symmetric on actual selected frontier edges. -/
theorem unboundedFrontierSelectedEdgeEndpointRelated_symm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {e f : {e : PlanarInterface.Edge n //
      e ∈ unboundedFrontierEdgeSet C inputs}}
    (h :
      e.1.1 = f.1.1 ∨ e.1.1 = f.1.2 ∨
        e.1.2 = f.1.1 ∨ e.1.2 = f.1.2) :
    f.1.1 = e.1.1 ∨ f.1.1 = e.1.2 ∨
      f.1.2 = e.1.1 ∨ f.1.2 = e.1.2 := by
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

/-- Equal or reversed selected edges are one selected endpoint-sharing step. -/
theorem unboundedFrontierSelectedEdgeEndpointRelated_of_eq_or_symm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {e f : {e : PlanarInterface.Edge n //
      e ∈ unboundedFrontierEdgeSet C inputs}}
    (h : e.1 = f.1 ∨ e.1 = (f.1.2, f.1.1)) :
    e.1.1 = f.1.1 ∨ e.1.1 = f.1.2 ∨
      e.1.2 = f.1.1 ∨ e.1.2 = f.1.2 := by
  rcases h with h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (Or.inl (by
      rw [h]))

/-- A selected edge covered by the raw orbit is endpoint-related to the
chosen actual selected raw edge at that orbit index. -/
theorem unboundedFrontierSelectedEdgeEndpointRelated_rawOrbit_selected_of_eq_or_symm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (hedges :
      forall k : Fin O.period,
        ((O.dart k).tail,
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∈
            unboundedFrontierEdgeSet C inputs ∨
          ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
            (O.dart k).tail) ∈ unboundedFrontierEdgeSet C inputs)
    {e : {e : PlanarInterface.Edge n //
        e ∈ unboundedFrontierEdgeSet C inputs}}
    {k : Fin O.period}
    (he :
      e.1 =
          ((O.dart k).tail,
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
        e.1 =
          ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
            (O.dart k).tail)) :
    e.1.1 =
        (rawFaceSuccOrbitSelectedFrontierEdge
          (inputs := inputs) O hedges k).1.1 ∨
      e.1.1 =
        (rawFaceSuccOrbitSelectedFrontierEdge
          (inputs := inputs) O hedges k).1.2 ∨
      e.1.2 =
        (rawFaceSuccOrbitSelectedFrontierEdge
          (inputs := inputs) O hedges k).1.1 ∨
      e.1.2 =
        (rawFaceSuccOrbitSelectedFrontierEdge
          (inputs := inputs) O hedges k).1.2 := by
  rcases rawFaceSuccOrbitSelectedFrontierEdge_eq_or_symm
      (inputs := inputs) O hedges k with hraw | hraw
  · rcases he with he | he
    · exact
        unboundedFrontierSelectedEdgeEndpointRelated_of_eq_or_symm
          (C := C) (inputs := inputs) (e := e)
          (f := rawFaceSuccOrbitSelectedFrontierEdge
            (inputs := inputs) O hedges k)
          (Or.inl (he.trans hraw.symm))
    · exact
        unboundedFrontierSelectedEdgeEndpointRelated_of_eq_or_symm
          (C := C) (inputs := inputs) (e := e)
          (f := rawFaceSuccOrbitSelectedFrontierEdge
            (inputs := inputs) O hedges k)
          (Or.inr (by
            rw [he, hraw]))
  · rcases he with he | he
    · exact
        unboundedFrontierSelectedEdgeEndpointRelated_of_eq_or_symm
          (C := C) (inputs := inputs) (e := e)
          (f := rawFaceSuccOrbitSelectedFrontierEdge
            (inputs := inputs) O hedges k)
          (Or.inr (by
            rw [he, hraw]))
    · exact
        unboundedFrontierSelectedEdgeEndpointRelated_of_eq_or_symm
          (C := C) (inputs := inputs) (e := e)
          (f := rawFaceSuccOrbitSelectedFrontierEdge
            (inputs := inputs) O hedges k)
          (Or.inl (he.trans hraw.symm))

/-- Consecutive actual selected raw-orbit edges share the raw successor tail. -/
theorem rawFaceSuccOrbitSelectedFrontierEdge_endpointRelated_succ
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (hedges :
      forall k : Fin O.period,
        ((O.dart k).tail,
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∈
            unboundedFrontierEdgeSet C inputs ∨
          ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
            (O.dart k).tail) ∈ unboundedFrontierEdgeSet C inputs)
    (k : Fin O.period) :
    let rawEdge :=
      rawFaceSuccOrbitSelectedFrontierEdge (inputs := inputs) O hedges
    (rawEdge k).1.1 =
        (rawEdge (PlanarInterface.cyclicSucc O.period_pos k)).1.1 ∨
      (rawEdge k).1.1 =
        (rawEdge (PlanarInterface.cyclicSucc O.period_pos k)).1.2 ∨
      (rawEdge k).1.2 =
        (rawEdge (PlanarInterface.cyclicSucc O.period_pos k)).1.1 ∨
      (rawEdge k).1.2 =
        (rawEdge (PlanarInterface.cyclicSucc O.period_pos k)).1.2 := by
  let next := PlanarInterface.cyclicSucc O.period_pos k
  rcases rawFaceSuccOrbitSelectedFrontierEdge_eq_or_symm
      (inputs := inputs) O hedges k with h | h
  · rcases rawFaceSuccOrbitSelectedFrontierEdge_eq_or_symm
        (inputs := inputs) O hedges next with hnext | hnext
    · exact Or.inr (Or.inr (Or.inl (by
        rw [h, hnext])))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [h, hnext])))
  · rcases rawFaceSuccOrbitSelectedFrontierEdge_eq_or_symm
        (inputs := inputs) O hedges next with hnext | hnext
    · exact Or.inl (by
        rw [h, hnext])
    · exact Or.inr (Or.inl (by
        rw [h, hnext]))

/-- Raw face-successor coverage of all actual selected frontier edges proves
endpoint-chain connectedness of the selected frontier-edge carrier.

The only source rows are actual raw consecutive-edge membership in
`unboundedFrontierEdgeSet` and coverage of every actual selected frontier edge
by one raw consecutive edge, up to orientation. -/
theorem unboundedFrontierSelectedEdgeEndpointChainConnected_of_rawFaceSuccOrbit_edges
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (hedges :
      forall k : Fin O.period,
        ((O.dart k).tail,
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∈
            unboundedFrontierEdgeSet C inputs ∨
          ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
            (O.dart k).tail) ∈ unboundedFrontierEdgeSet C inputs)
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail)) :
    UnboundedFrontierSelectedEdgeEndpointChainConnected inputs := by
  intro e f
  let rawEdge :=
    rawFaceSuccOrbitSelectedFrontierEdge (inputs := inputs) O hedges
  let step :=
    fun e f : {e : PlanarInterface.Edge n //
        e ∈ unboundedFrontierEdgeSet C inputs} =>
      e.1.1 = f.1.1 ∨ e.1.1 = f.1.2 ∨
        e.1.2 = f.1.1 ∨ e.1.2 = f.1.2
  let root : Fin O.period := ⟨0, O.period_pos⟩
  have raw_step_succ :
      forall k : Fin O.period,
        step (rawEdge k)
          (rawEdge (PlanarInterface.cyclicSucc O.period_pos k)) := by
    intro k
    simpa [step, rawEdge] using
      rawFaceSuccOrbitSelectedFrontierEdge_endpointRelated_succ
        (inputs := inputs) O hedges k
  have reach_nat :
      forall m : Nat,
        forall hm : m < O.period,
          Relation.ReflTransGen step
            (rawEdge root)
            (rawEdge ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hidx : (⟨0, hm⟩ : Fin O.period) = root := Fin.ext rfl
        rw [hidx]
    | succ m ih =>
        intro hm
        have hm_prev : m < O.period := by omega
        have hsucc :
            PlanarInterface.cyclicSucc O.period_pos
                (⟨m, hm_prev⟩ : Fin O.period) =
              (⟨m + 1, hm⟩ : Fin O.period) := by
          exact Fin.ext (by
            simp [PlanarInterface.cyclicSucc, Nat.mod_eq_of_lt hm])
        exact
          (ih hm_prev).tail
            (by
              rw [← hsucc]
              exact raw_step_succ ⟨m, hm_prev⟩)
  have step_symm : Symmetric step := by
    intro x y hxy
    exact
      unboundedFrontierSelectedEdgeEndpointRelated_symm
        (C := C) (inputs := inputs) hxy
  have rtc_symm :
      Symmetric (Relation.ReflTransGen step) :=
    Relation.ReflTransGen.symmetric step_symm
  rcases edge_coverage e with ⟨i, hei⟩
  rcases edge_coverage f with ⟨j, hfj⟩
  have hei_step : step e (rawEdge i) := by
    simpa [step, rawEdge] using
      unboundedFrontierSelectedEdgeEndpointRelated_rawOrbit_selected_of_eq_or_symm
        (inputs := inputs) O hedges (e := e) (k := i) hei
  have hfj_step : step (rawEdge j) f :=
    step_symm (by
      simpa [step, rawEdge] using
        unboundedFrontierSelectedEdgeEndpointRelated_rawOrbit_selected_of_eq_or_symm
          (inputs := inputs) O hedges (e := f) (k := j) hfj)
  have h_i_root :
      Relation.ReflTransGen step (rawEdge i) (rawEdge root) :=
    rtc_symm (by
      simpa using reach_nat i.val i.isLt)
  have h_root_j :
      Relation.ReflTransGen step (rawEdge root) (rawEdge j) := by
    simpa using reach_nat j.val j.isLt
  exact
    (Relation.ReflTransGen.single hei_step).trans
      (h_i_root.trans
        (h_root_j.trans (Relation.ReflTransGen.single hfj_step)))

/-- Raw dart-edge frontier plus selected-edge coverage proves the selected
endpoint chain for the actual `unboundedFrontierEdgeSet` carrier. -/
theorem S2_codex_current_20260520_selected_edge_endpoint_chain_connectivity_leaf
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail)) :
    UnboundedFrontierSelectedEdgeEndpointChainConnected inputs :=
  unboundedFrontierSelectedEdgeEndpointChainConnected_of_rawFaceSuccOrbit_edges
    (C := C) (inputs := inputs) O
    (rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm_of_dart_edge_openSegment_frontier
      (inputs := inputs) O dart_edge_openSegment_frontier)
    edge_coverage

/-- Claim `S2-codex-current-20260520-selected-edge-chain-connectivity-leaf`.

The actual selected-edge endpoint chain and the closed-segment carrier chain
both reduce to the same raw face-successor edge-coverage source. -/
theorem S2_codex_current_20260520_selected_edge_chain_connectivity_leaf
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail)) :
    UnboundedFrontierSelectedEdgeEndpointChainConnected inputs ∧
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs := by
  exact
    ⟨S2_codex_current_20260520_selected_edge_endpoint_chain_connectivity_leaf
        (C := C) (inputs := inputs) O
        dart_edge_openSegment_frontier edge_coverage,
      S2_edgeCarrierSegmentChainConnected_of_rawFaceSuccOrbit_dartFrontier_edgeCoverage
        (C := C) (inputs := inputs) O
        dart_edge_openSegment_frontier edge_coverage⟩

/-- Raw face-successor boundary-edge carrier plus fixed-side local-sector rows
fill the component-topology source rows for the actual unbounded exterior
frontier.

The raw orbit supplies the selected closed-segment chain, while the local
sector rows supply the existing actual frontier-edge cover. -/
def S2_componentTopologySourceRows_of_rawFaceSuccOrbit_dartFrontier_edgeCoverage_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail))
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  unboundedExteriorFrontierComponentTopologySourceRows_of_edgeChain_localSectorRows_fixedSide
    (C := C) inputs
    (S2_edgeCarrierSegmentChainConnected_of_rawFaceSuccOrbit_dartFrontier_edgeCoverage
      (C := C) (inputs := inputs) O dart_edge_openSegment_frontier edge_coverage)
    localSectorRows

set_option linter.style.longLine false in
/-- Claim
`S2-codex-current-20260520-boundary-edge-coverage-local-sector-source`.

Raw dart open-segment frontier, carrier connectedness, and the honest
pointwise local-sector rows cover every selected
`unboundedFrontierEdgeSet` edge by consecutive raw orbit tails.  This removes
the separate `edge_coverage` residual from the raw-orbit/local-sector route;
the proof still quantifies over the actual selected frontier edge carrier. -/
theorem
    S2_codex_current_20260520_rawOrbit_edgeCoverage_of_localSectorRows_carrierConnected
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected) :
    forall e :
        {e : PlanarInterface.Edge n //
          e ∈ unboundedFrontierEdgeSet C inputs},
      Exists fun k : Fin O.period =>
        e.1 =
            ((O.dart k).tail,
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
          e.1 =
            ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
              (O.dart k).tail) := by
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
  let frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1 :=
    (S2_agent_selected_raw_orbit_frontier_and_tail_coverage_source_no_edgeRows
      (C := C) (inputs := inputs) localSectorRows carrier_connected O
      dart_edge_openSegment_frontier).2
  let raw_pred_succ_tail_ne :
      forall k : Fin O.period,
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
    rawFaceSuccOrbit_pred_succ_tail_ne_of_geometric_localSectorRows
      (C := C) (inputs := inputs) O edge_openSegment_frontier localSectorRows
  exact
    rawFaceSuccOrbit_edge_coverage_of_tail_coverage_localSectorRows
      (inputs := inputs) O edge_openSegment_frontier
      frontier_vertex_tail_coverage localSectorRows raw_pred_succ_tail_ne

set_option linter.style.longLine false in
/-- Selected edge-chain connectivity with no standalone `edge_coverage`
source field.

The selected edge coverage used by the existing chain constructor is derived
from the same raw dart frontier and local-sector/carrier-connected rows above. -/
theorem
    S2_codex_current_20260520_selected_edge_chain_connectivity_leaf_of_localSectorRows_carrierConnected
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected) :
    UnboundedFrontierSelectedEdgeEndpointChainConnected inputs ∧
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs :=
  S2_codex_current_20260520_selected_edge_chain_connectivity_leaf
    (C := C) (inputs := inputs) O dart_edge_openSegment_frontier
    (S2_codex_current_20260520_rawOrbit_edgeCoverage_of_localSectorRows_carrierConnected
      (C := C) (inputs := inputs) O dart_edge_openSegment_frontier
      localSectorRows carrier_connected)

set_option linter.style.longLine false in
/-- Component-topology source rows from the raw-orbit/local-sector residual
without an explicit selected-edge coverage input.

The carrier segment chain is sourced through
`S2_codex_current_20260520_rawOrbit_edgeCoverage_of_localSectorRows_carrierConnected`,
so carrier edges remain actual selected `unboundedFrontierEdgeSet` edges. -/
def
    S2_componentTopologySourceRows_of_rawFaceSuccOrbit_dartFrontier_localSectorRows_carrierConnected
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  S2_componentTopologySourceRows_of_rawFaceSuccOrbit_dartFrontier_edgeCoverage_localSectorRows
    (C := C) (inputs := inputs) O dart_edge_openSegment_frontier
    (S2_codex_current_20260520_rawOrbit_edgeCoverage_of_localSectorRows_carrierConnected
      (C := C) (inputs := inputs) O dart_edge_openSegment_frontier
      localSectorRows carrier_connected)
    localSectorRows

/-- Constructor form of the repeated-tail cut source.

This names the exact minimal row: one witness on each cyclic open arc and the
deleted-tail nonreachability proof in the induced unit-distance graph. -/
def S2_repeatedTailExteriorCutRows_of_unreachable_after_delete
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    {i j : Fin O.period}
    (left_index : Fin O.period)
    (left_index_mem : cyclicForwardOpenArc i j left_index)
    (left_index_ne_cut : (O.dart left_index).tail ≠ (O.dart i).tail)
    (right_index : Fin O.period)
    (right_index_mem : cyclicForwardOpenArc j i right_index)
    (right_index_ne_cut : (O.dart right_index).tail ≠ (O.dart i).tail)
    (unreachable_after_delete :
      ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
          ({(O.dart i).tail}ᶜ : Set (Fin n))).Reachable
          ⟨(O.dart left_index).tail, by simpa using left_index_ne_cut⟩
          ⟨(O.dart right_index).tail, by simpa using right_index_ne_cut⟩) :
    RawFaceSuccOrbitRepeatedTailExteriorCutRows
      (inputs := inputs) O i j where
  left_index := left_index
  left_index_mem := left_index_mem
  left_index_ne_cut := left_index_ne_cut
  right_index := right_index
  right_index_mem := right_index_mem
  right_index_ne_cut := right_index_ne_cut
  unreachable_after_delete := unreachable_after_delete

/-- Source package for the finite cyclic arc-separation row for a hypothetical
repeated selected raw-orbit tail.

This is the sharp residual plane-separation obligation: choose a non-cut raw
tail on each open cyclic arc, cover every non-cut graph vertex by one of the
two raw-tail arc images, separate the reverse arc from the forward arc away
from the cut, and prove anticompleteness across the two sides.  The checked
`RepeatedExteriorBoundaryArcSeparationRows` reducer then derives the induced
deleted-tail nonreachability used by the cut-row handoff. -/
structure S2RepeatedBoundaryArcSeparationSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (i j : Fin O.period) where
  repeat_eq : (O.dart i).tail = (O.dart j).tail
  index_ne : i ≠ j
  left_index : Fin O.period
  left_index_mem : cyclicForwardOpenArc i j left_index
  left_index_ne_cut : (O.dart left_index).tail ≠ (O.dart i).tail
  right_index : Fin O.period
  right_index_mem : cyclicForwardOpenArc j i right_index
  right_index_ne_cut : (O.dart right_index).tail ≠ (O.dart i).tail
  cover_noncut :
    forall v : Fin n, v ≠ (O.dart i).tail ->
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j v ∨
        repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i v
  reverse_arc_not_forward_off_cut :
    forall {v : Fin n}, v ≠ (O.dart i).tail ->
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i v ->
        ¬ repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j v
  arcs_anticomplete :
    forall {a b : Fin n},
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j a ->
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i b ->
      a ≠ (O.dart i).tail ->
      b ≠ (O.dart i).tail ->
        ¬ (GraphBridge.unitDistanceSimpleGraph C).Adj a b

namespace S2RepeatedBoundaryArcSeparationSource

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {R : UnitDistanceRotationSystem C}
variable {start : UnitDistanceDart C}
variable {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
variable {i j : Fin O.period}

/-- Erase the explicit S2 source package to the checked finite cyclic
arc-separation row. -/
def toRepeatedExteriorBoundaryArcSeparationRows
    (rows :
      S2RepeatedBoundaryArcSeparationSource (inputs := inputs) O i j) :
    RepeatedExteriorBoundaryArcSeparationRows C
      (fun k : Fin O.period => (O.dart k).tail) i j where
  repeat_eq := rows.repeat_eq
  index_ne := rows.index_ne
  left_index := rows.left_index
  left_index_mem := rows.left_index_mem
  left_index_ne_cut := rows.left_index_ne_cut
  right_index := rows.right_index
  right_index_mem := rows.right_index_mem
  right_index_ne_cut := rows.right_index_ne_cut
  cover_noncut := rows.cover_noncut
  reverse_arc_not_forward_off_cut :=
    rows.reverse_arc_not_forward_off_cut
  arcs_anticomplete := rows.arcs_anticomplete

/-- The concrete cyclic-open-arc separation package for a hypothetical
repeated raw tail forms the cut-vertex partition consumed by the repeated-tail
callback. -/
noncomputable def toCutVertexPartition
    (rows :
      S2RepeatedBoundaryArcSeparationSource (inputs := inputs) O i j) :
    CutVertexInterface.CutVertexPartition C :=
  RepeatedExteriorBoundarySeparationRows.toCutVertexPartition
    (RepeatedExteriorBoundaryArcSeparationRows.toRepeatedExteriorBoundarySeparationRows
      rows.toRepeatedExteriorBoundaryArcSeparationRows)

/-- The arc-separation source gives the deleted-tail nonreachability between
the two selected non-cut open-arc witnesses. -/
theorem unreachable_after_delete
    (rows :
      S2RepeatedBoundaryArcSeparationSource (inputs := inputs) O i j) :
    ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
        ({(O.dart i).tail}ᶜ : Set (Fin n))).Reachable
        ⟨(O.dart rows.left_index).tail, by
          simpa using rows.left_index_ne_cut⟩
        ⟨(O.dart rows.right_index).tail, by
          simpa using rows.right_index_ne_cut⟩ := by
  let arcRows := rows.toRepeatedExteriorBoundaryArcSeparationRows
  simpa using arcRows.unreachable_after_delete

end S2RepeatedBoundaryArcSeparationSource

/-- Index-level source rows for the repeated-boundary arc separation package.

This is the smaller S2 source surface behind
`S2RepeatedBoundaryArcSeparationSource`: it keeps the explicit witnesses on
both open raw arcs, asks for non-cut graph-vertex coverage by raw tails, and
states the only geometric separation content at index level. -/
structure S2RepeatedBoundaryArcSourceWitnessRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (i j : Fin O.period) where
  repeat_eq : (O.dart i).tail = (O.dart j).tail
  index_ne : i ≠ j
  left_index : Fin O.period
  left_index_mem : cyclicForwardOpenArc i j left_index
  left_index_ne_cut : (O.dart left_index).tail ≠ (O.dart i).tail
  right_index : Fin O.period
  right_index_mem : cyclicForwardOpenArc j i right_index
  right_index_ne_cut : (O.dart right_index).tail ≠ (O.dart i).tail
  tail_cover_noncut :
    forall v : Fin n, v ≠ (O.dart i).tail ->
      Exists fun k : Fin O.period => (O.dart k).tail = v
  opposite_arc_same_tail_only_cut :
    forall {a b : Fin O.period},
      cyclicForwardOpenArc j i a ->
      cyclicForwardOpenArc i j b ->
      (O.dart a).tail = (O.dart b).tail ->
        (O.dart a).tail = (O.dart i).tail
  opposite_arcs_anticomplete :
    forall {a b : Fin O.period},
      cyclicForwardOpenArc i j a ->
      cyclicForwardOpenArc j i b ->
      (O.dart a).tail ≠ (O.dart i).tail ->
      (O.dart b).tail ≠ (O.dart i).tail ->
        ¬ (GraphBridge.unitDistanceSimpleGraph C).Adj
          (O.dart a).tail (O.dart b).tail

/-- Primitive real-source rows for the repeated-boundary arc witnesses.

For a hypothetical repeated selected raw tail, the repeat equality and index
inequality are already part of the hypothesis.  The remaining honest
plane-separation/no-crossing content is exactly this row: one non-cut raw-tail
witness on each open cyclic arc, coverage of every non-cut vertex by a raw
tail, equality of opposite open-arc tails only at the repeated tail, and
index-level anticompleteness across the two open arcs. -/
structure S2RepeatedBoundaryArcRealWitnessSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (i j : Fin O.period) where
  left_index : Fin O.period
  left_index_mem : cyclicForwardOpenArc i j left_index
  left_index_ne_cut : (O.dart left_index).tail ≠ (O.dart i).tail
  right_index : Fin O.period
  right_index_mem : cyclicForwardOpenArc j i right_index
  right_index_ne_cut : (O.dart right_index).tail ≠ (O.dart i).tail
  tail_cover_noncut :
    forall v : Fin n, v ≠ (O.dart i).tail ->
      Exists fun k : Fin O.period => (O.dart k).tail = v
  opposite_arc_same_tail_only_cut :
    forall {a b : Fin O.period},
      cyclicForwardOpenArc j i a ->
      cyclicForwardOpenArc i j b ->
      (O.dart a).tail = (O.dart b).tail ->
        (O.dart a).tail = (O.dart i).tail
  opposite_arcs_anticomplete :
    forall {a b : Fin O.period},
      cyclicForwardOpenArc i j a ->
      cyclicForwardOpenArc j i b ->
      (O.dart a).tail ≠ (O.dart i).tail ->
      (O.dart b).tail ≠ (O.dart i).tail ->
        ¬ (GraphBridge.unitDistanceSimpleGraph C).Adj
          (O.dart a).tail (O.dart b).tail

namespace S2RepeatedBoundaryArcRealWitnessSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {R : UnitDistanceRotationSystem C}
variable {start : UnitDistanceDart C}
variable {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
variable {i j : Fin O.period}

/-- Add the hypothetical repeated-tail facts to the real-source row to obtain
the full witness package consumed by the existing arc-separation reducer. -/
def toSourceWitnessRows
    (rows :
      S2RepeatedBoundaryArcRealWitnessSourceRows (inputs := inputs) O i j)
    (hij : i ≠ j)
    (hrepeat : (O.dart i).tail = (O.dart j).tail) :
    S2RepeatedBoundaryArcSourceWitnessRows (inputs := inputs) O i j where
  repeat_eq := hrepeat
  index_ne := hij
  left_index := rows.left_index
  left_index_mem := rows.left_index_mem
  left_index_ne_cut := rows.left_index_ne_cut
  right_index := rows.right_index
  right_index_mem := rows.right_index_mem
  right_index_ne_cut := rows.right_index_ne_cut
  tail_cover_noncut := rows.tail_cover_noncut
  opposite_arc_same_tail_only_cut :=
    rows.opposite_arc_same_tail_only_cut
  opposite_arcs_anticomplete := rows.opposite_arcs_anticomplete

end S2RepeatedBoundaryArcRealWitnessSourceRows

/-- Primitive arc-image source rows for the real repeated-boundary witness.

This keeps the residual source in graph-vertex image language: pick one
non-cut vertex on each open arc image, cover every non-cut graph vertex by a
raw tail, separate the reverse open-arc image from the forward one away from
the repeated tail, and rule out unit-distance graph edges across the two arc
images. -/
structure S2RepeatedBoundaryArcRealWitnessPrimitiveRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (i j : Fin O.period) where
  left_vertex_witness :
    Exists fun v : Fin n =>
      Not (v = (O.dart i).tail) /\
        repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j v
  right_vertex_witness :
    Exists fun v : Fin n =>
      Not (v = (O.dart i).tail) /\
        repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i v
  tail_cover_noncut :
    forall v : Fin n, Not (v = (O.dart i).tail) ->
      Exists fun k : Fin O.period => (O.dart k).tail = v
  opposite_arc_images_disjoint_off_cut :
    forall {v : Fin n}, Not (v = (O.dart i).tail) ->
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i v ->
        Not (repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j v)
  arc_images_anticomplete :
    forall {a b : Fin n},
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j a ->
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i b ->
      Not (a = (O.dart i).tail) ->
      Not (b = (O.dart i).tail) ->
        Not ((GraphBridge.unitDistanceSimpleGraph C).Adj a b)

/-- Claim-level source rows for the primitive repeated-tail witness.

This is the explicit low-level source behind
`S2RepeatedBoundaryArcRealWitnessPrimitiveRows`: it chooses concrete raw indices
on the two cyclic open arcs, proves their tails are not the deleted repeated
tail, and keeps the remaining three facts in raw-tail image language. -/
structure S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (i j : Fin O.period) where
  left_index : Fin O.period
  left_index_mem : cyclicForwardOpenArc i j left_index
  left_index_ne_cut : Not ((O.dart left_index).tail = (O.dart i).tail)
  right_index : Fin O.period
  right_index_mem : cyclicForwardOpenArc j i right_index
  right_index_ne_cut : Not ((O.dart right_index).tail = (O.dart i).tail)
  tail_cover_noncut :
    forall v : Fin n, Not (v = (O.dart i).tail) ->
      Exists fun k : Fin O.period => (O.dart k).tail = v
  opposite_arc_images_disjoint_off_cut :
    forall {v : Fin n}, Not (v = (O.dart i).tail) ->
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i v ->
        Not (repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j v)
  arc_images_anticomplete :
    forall {a b : Fin n},
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j a ->
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i b ->
      Not (a = (O.dart i).tail) ->
      Not (b = (O.dart i).tail) ->
        Not ((GraphBridge.unitDistanceSimpleGraph C).Adj a b)

namespace S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {R : UnitDistanceRotationSystem C}
variable {start : UnitDistanceDart C}
variable {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
variable {i j : Fin O.period}

/-- Index-level repeated-tail witness rows supply the concrete primitive
source row.  This is the raw-index projection: witnesses and coverage are
kept unchanged, while the same-tail-only-at-the-cut row gives image
disjointness and the index-level anticompleteness row gives image
anticompleteness. -/
def ofRealWitnessSourceRows
    (rows :
      S2RepeatedBoundaryArcRealWitnessSourceRows (inputs := inputs) O i j) :
    S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows
      (inputs := inputs) O i j where
  left_index := rows.left_index
  left_index_mem := rows.left_index_mem
  left_index_ne_cut := rows.left_index_ne_cut
  right_index := rows.right_index
  right_index_mem := rows.right_index_mem
  right_index_ne_cut := rows.right_index_ne_cut
  tail_cover_noncut := rows.tail_cover_noncut
  opposite_arc_images_disjoint_off_cut := by
    intro v hv hright hleft
    rcases hright with ⟨a, ha_arc, ha_tail⟩
    rcases hleft with ⟨b, hb_arc, hb_tail⟩
    have hab_tail : (O.dart a).tail = (O.dart b).tail :=
      ha_tail.trans hb_tail.symm
    have hcut : (O.dart a).tail = (O.dart i).tail :=
      rows.opposite_arc_same_tail_only_cut ha_arc hb_arc hab_tail
    exact hv (ha_tail.symm.trans hcut)
  arc_images_anticomplete := by
    intro a b ha hb ha_cut hb_cut hadj
    rcases ha with ⟨ka, hka_arc, hka_tail⟩
    rcases hb with ⟨kb, hkb_arc, hkb_tail⟩
    have hka_ne_cut : (O.dart ka).tail ≠ (O.dart i).tail := by
      intro hcut
      exact ha_cut (hka_tail.symm.trans hcut)
    have hkb_ne_cut : (O.dart kb).tail ≠ (O.dart i).tail := by
      intro hcut
      exact hb_cut (hkb_tail.symm.trans hcut)
    exact
      rows.opposite_arcs_anticomplete
        hka_arc hkb_arc hka_ne_cut hkb_ne_cut
        (by simpa [hka_tail, hkb_tail] using hadj)

/-- The full source-witness row also erases to the primitive source row; the
hypothetical repeat equality and index inequality are unused by this
projection. -/
def ofSourceWitnessRows
    (rows :
      S2RepeatedBoundaryArcSourceWitnessRows (inputs := inputs) O i j) :
    S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows
      (inputs := inputs) O i j :=
  ofRealWitnessSourceRows
    (inputs := inputs)
    ({ left_index := rows.left_index
       left_index_mem := rows.left_index_mem
       left_index_ne_cut := rows.left_index_ne_cut
       right_index := rows.right_index
       right_index_mem := rows.right_index_mem
       right_index_ne_cut := rows.right_index_ne_cut
       tail_cover_noncut := rows.tail_cover_noncut
       opposite_arc_same_tail_only_cut :=
        rows.opposite_arc_same_tail_only_cut
       opposite_arcs_anticomplete := rows.opposite_arcs_anticomplete } :
      S2RepeatedBoundaryArcRealWitnessSourceRows (inputs := inputs) O i j)

/-- Erase the concrete raw-index primitive source to the arc-image primitive
row. -/
def toPrimitiveRows
    (rows :
      S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows
        (inputs := inputs) O i j) :
    S2RepeatedBoundaryArcRealWitnessPrimitiveRows (inputs := inputs) O i j where
  left_vertex_witness :=
    ⟨(O.dart rows.left_index).tail,
      rows.left_index_ne_cut,
      ⟨rows.left_index, rows.left_index_mem, rfl⟩⟩
  right_vertex_witness :=
    ⟨(O.dart rows.right_index).tail,
      rows.right_index_ne_cut,
      ⟨rows.right_index, rows.right_index_mem, rfl⟩⟩
  tail_cover_noncut := rows.tail_cover_noncut
  opposite_arc_images_disjoint_off_cut :=
    rows.opposite_arc_images_disjoint_off_cut
  arc_images_anticomplete := rows.arc_images_anticomplete

/-- Directly promote the concrete primitive raw-index source to the live
real-witness source row.

This keeps the selected open-arc witness indices fixed.  The only derivations
are the index-level same-tail-only-cut row from off-cut image disjointness, and
the index-level anticompleteness row from image anticompleteness. -/
def toRealWitnessSourceRows
    (rows :
      S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows
        (inputs := inputs) O i j) :
    S2RepeatedBoundaryArcRealWitnessSourceRows (inputs := inputs) O i j where
  left_index := rows.left_index
  left_index_mem := rows.left_index_mem
  left_index_ne_cut := rows.left_index_ne_cut
  right_index := rows.right_index
  right_index_mem := rows.right_index_mem
  right_index_ne_cut := rows.right_index_ne_cut
  tail_cover_noncut := rows.tail_cover_noncut
  opposite_arc_same_tail_only_cut := by
    intro a b ha hb hab
    by_contra ha_cut
    exact rows.opposite_arc_images_disjoint_off_cut ha_cut
      (Exists.intro a (And.intro ha rfl))
      (Exists.intro b (And.intro hb hab.symm))
  opposite_arcs_anticomplete := by
    intro a b ha hb ha_cut hb_cut
    exact rows.arc_images_anticomplete
      (Exists.intro a (And.intro ha rfl))
      (Exists.intro b (And.intro hb rfl))
      ha_cut hb_cut

end S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows

namespace S2RepeatedBoundaryArcRealWitnessPrimitiveRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {R : UnitDistanceRotationSystem C}
variable {start : UnitDistanceDart C}
variable {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
variable {i j : Fin O.period}

/-- The selected raw pair-level actual exterior-arc rows supply the exact
primitive arc-image witness row: they already contain non-cut witnesses on the
two cyclic open arcs, non-cut coverage by the two arc images, off-cut
disjointness, and anticompleteness across the two image sides. -/
def ofRepeatedTailActualExteriorArcRows
    (rows :
      RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
        (inputs := inputs) O i j) :
    S2RepeatedBoundaryArcRealWitnessPrimitiveRows (inputs := inputs) O i j where
  left_vertex_witness := by
    exact ⟨(O.dart rows.left_index).tail,
      by simpa using rows.left_index_ne_cut,
      ⟨rows.left_index, rows.left_index_mem, rfl⟩⟩
  right_vertex_witness := by
    exact ⟨(O.dart rows.right_index).tail,
      by simpa using rows.right_index_ne_cut,
      ⟨rows.right_index, rows.right_index_mem, rfl⟩⟩
  tail_cover_noncut := by
    intro v hv
    rcases rows.cover_noncut v hv with hleft | hright
    · rcases hleft with ⟨k, _hk_arc, hk_tail⟩
      exact ⟨k, hk_tail⟩
    · rcases hright with ⟨k, _hk_arc, hk_tail⟩
      exact ⟨k, hk_tail⟩
  opposite_arc_images_disjoint_off_cut := by
    intro v hv hright
    exact rows.reverse_arc_not_forward_off_cut hv hright
  arc_images_anticomplete := by
    intro a b ha hb ha_cut hb_cut
    exact rows.arcs_anticomplete ha hb ha_cut hb_cut

/-- The primitive two-open-arc source also supplies the selected raw
pair-level actual exterior-arc row once the hypothetical repeated-tail facts
are fixed.

This is the claim-level strict reduction for
`S2-dyn-20260520-repeated-tail-actual-exterior-arc-rows`: the residual is the
actual two cyclic exterior arc images after deleting the repeated tail, with a
non-cut witness on each side, raw-tail coverage, off-cut disjointness, and
anticompleteness across the two sides. -/
noncomputable def toRepeatedTailActualExteriorArcRows
    (rows :
      S2RepeatedBoundaryArcRealWitnessPrimitiveRows (inputs := inputs) O i j)
    (hij : i ≠ j)
    (hrepeat : (O.dart i).tail = (O.dart j).tail) :
    RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
      (inputs := inputs) O i j := by
  classical
  let left_v : Fin n := Classical.choose rows.left_vertex_witness
  have hleft_v := Classical.choose_spec rows.left_vertex_witness
  let left_index : Fin O.period := Classical.choose hleft_v.2
  have hleft_index := Classical.choose_spec hleft_v.2
  let right_v : Fin n := Classical.choose rows.right_vertex_witness
  have hright_v := Classical.choose_spec rows.right_vertex_witness
  let right_index : Fin O.period := Classical.choose hright_v.2
  have hright_index := Classical.choose_spec hright_v.2
  refine
    { left_index := left_index
      left_index_mem := hleft_index.1
      left_index_ne_cut := ?_
      right_index := right_index
      right_index_mem := hright_index.1
      right_index_ne_cut := ?_
      cover_noncut := ?_
      reverse_arc_not_forward_off_cut :=
        rows.opposite_arc_images_disjoint_off_cut
      arcs_anticomplete := rows.arc_images_anticomplete }
  · intro hcut
    exact hleft_v.1 (hleft_index.2.symm.trans hcut)
  · intro hcut
    exact hright_v.1 (hright_index.2.symm.trans hcut)
  · intro v hv
    rcases rows.tail_cover_noncut v hv with ⟨k, hk_tail⟩
    have hki : k ≠ i := by
      intro hki
      subst k
      exact hv hk_tail.symm
    have hkj : k ≠ j := by
      intro hkj
      subst k
      exact hv (hk_tail.symm.trans hrepeat.symm)
    rcases cyclicForwardOpenArc_or_reverse_of_ne_endpoints
        hij hki hkj with harc | harc
    · exact Or.inl ⟨k, harc, hk_tail⟩
    · exact Or.inr ⟨k, harc, hk_tail⟩

/-- Erase the primitive arc-image source to the existing index-level real
witness row. -/
noncomputable def toRealWitnessSourceRows
    (rows :
      S2RepeatedBoundaryArcRealWitnessPrimitiveRows (inputs := inputs) O i j) :
    S2RepeatedBoundaryArcRealWitnessSourceRows (inputs := inputs) O i j := by
  classical
  let left_v : Fin n := Classical.choose rows.left_vertex_witness
  have hleft_v := Classical.choose_spec rows.left_vertex_witness
  let left_index : Fin O.period := Classical.choose hleft_v.2
  have hleft_index := Classical.choose_spec hleft_v.2
  let right_v : Fin n := Classical.choose rows.right_vertex_witness
  have hright_v := Classical.choose_spec rows.right_vertex_witness
  let right_index : Fin O.period := Classical.choose hright_v.2
  have hright_index := Classical.choose_spec hright_v.2
  exact {
    left_index := left_index
    left_index_mem := hleft_index.1
    left_index_ne_cut := by
      intro hcut
      exact hleft_v.1 (hleft_index.2.symm.trans hcut)
    right_index := right_index
    right_index_mem := hright_index.1
    right_index_ne_cut := by
      intro hcut
      exact hright_v.1 (hright_index.2.symm.trans hcut)
    tail_cover_noncut := rows.tail_cover_noncut
    opposite_arc_same_tail_only_cut := by
      intro a b ha hb hab
      by_contra ha_cut
      exact rows.opposite_arc_images_disjoint_off_cut ha_cut
        (Exists.intro a (And.intro ha rfl))
        (Exists.intro b (And.intro hb hab.symm))
    opposite_arcs_anticomplete := by
      intro a b ha hb ha_cut hb_cut
      exact rows.arc_images_anticomplete
        (Exists.intro a (And.intro ha rfl))
        (Exists.intro b (And.intro hb rfl))
        ha_cut hb_cut }

end S2RepeatedBoundaryArcRealWitnessPrimitiveRows

namespace S2RepeatedBoundaryArcSourceWitnessRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {R : UnitDistanceRotationSystem C}
variable {start : UnitDistanceDart C}
variable {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
variable {i j : Fin O.period}

/-- Non-cut raw-tail coverage by indices gives coverage by the two cyclic
open arc images cut out by the repeated tail. -/
theorem cover_noncut
    (rows :
      S2RepeatedBoundaryArcSourceWitnessRows (inputs := inputs) O i j) :
    forall v : Fin n, v ≠ (O.dart i).tail ->
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j v ∨
        repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i v := by
  intro v hv
  rcases rows.tail_cover_noncut v hv with ⟨k, hk⟩
  have hki : k ≠ i := by
    intro hki
    subst k
    exact hv hk.symm
  have hkj : k ≠ j := by
    intro hkj
    subst k
    exact hv (rows.repeat_eq.trans hk).symm
  rcases cyclicForwardOpenArc_or_reverse_of_ne_endpoints
      rows.index_ne hki hkj with harc | harc
  · exact Or.inl ⟨k, harc, hk⟩
  · exact Or.inr ⟨k, harc, hk⟩

/-- The index-level "opposite arcs meet only at the repeated tail" row gives
the disjointness field needed by the finite arc-separation package. -/
theorem reverse_arc_not_forward_off_cut
    (rows :
      S2RepeatedBoundaryArcSourceWitnessRows (inputs := inputs) O i j) :
    forall {v : Fin n}, v ≠ (O.dart i).tail ->
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i v ->
        ¬ repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j v := by
  intro v hv hright hleft
  rcases hright with ⟨a, ha_arc, ha_tail⟩
  rcases hleft with ⟨b, hb_arc, hb_tail⟩
  have hab_tail : (O.dart a).tail = (O.dart b).tail :=
    ha_tail.trans hb_tail.symm
  have hcut :
      (O.dart a).tail = (O.dart i).tail :=
    rows.opposite_arc_same_tail_only_cut ha_arc hb_arc hab_tail
  exact hv (ha_tail.symm.trans hcut)

/-- The index-level anticompleteness row erases to anticompleteness of the two
raw arc images. -/
theorem arcs_anticomplete
    (rows :
      S2RepeatedBoundaryArcSourceWitnessRows (inputs := inputs) O i j) :
    forall {a b : Fin n},
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) i j a ->
      repeatedBoundaryArcImage
          (fun k : Fin O.period => (O.dart k).tail) j i b ->
      a ≠ (O.dart i).tail ->
      b ≠ (O.dart i).tail ->
        ¬ (GraphBridge.unitDistanceSimpleGraph C).Adj a b := by
  intro a b ha hb ha_cut hb_cut hadj
  rcases ha with ⟨ka, hka_arc, hka_tail⟩
  rcases hb with ⟨kb, hkb_arc, hkb_tail⟩
  have hka_ne_cut : (O.dart ka).tail ≠ (O.dart i).tail := by
    intro hcut
    exact ha_cut (hka_tail.symm.trans hcut)
  have hkb_ne_cut : (O.dart kb).tail ≠ (O.dart i).tail := by
    intro hcut
    exact hb_cut (hkb_tail.symm.trans hcut)
  exact
    rows.opposite_arcs_anticomplete
      hka_arc hkb_arc hka_ne_cut hkb_ne_cut
      (by simpa [hka_tail, hkb_tail] using hadj)

/-- Erase the smaller witness/index-level source to the explicit
`S2RepeatedBoundaryArcSeparationSource`. -/
def toRepeatedBoundaryArcSeparationSource
    (rows :
      S2RepeatedBoundaryArcSourceWitnessRows (inputs := inputs) O i j) :
    S2RepeatedBoundaryArcSeparationSource (inputs := inputs) O i j where
  repeat_eq := rows.repeat_eq
  index_ne := rows.index_ne
  left_index := rows.left_index
  left_index_mem := rows.left_index_mem
  left_index_ne_cut := rows.left_index_ne_cut
  right_index := rows.right_index
  right_index_mem := rows.right_index_mem
  right_index_ne_cut := rows.right_index_ne_cut
  cover_noncut := rows.cover_noncut
  reverse_arc_not_forward_off_cut :=
    rows.reverse_arc_not_forward_off_cut
  arcs_anticomplete := rows.arcs_anticomplete

end S2RepeatedBoundaryArcSourceWitnessRows

namespace S2RepeatedBoundaryArcRealWitnessPrimitiveRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {R : UnitDistanceRotationSystem C}
variable {start : UnitDistanceDart C}
variable {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
variable {i j : Fin O.period}

/-- Pair-level direct reducer from the primitive two-open-arc source to the
full repeated-boundary arc-separation source.

The primitive row is the smaller residual: after a hypothetical repeated raw
tail is fixed, it asks only for a non-cut vertex on each cyclic open raw arc,
raw-tail coverage away from the deleted tail, off-cut disjointness of the two
arc images, and anticompleteness across those images. -/
noncomputable def toRepeatedBoundaryArcSeparationSource
    (rows :
      S2RepeatedBoundaryArcRealWitnessPrimitiveRows (inputs := inputs) O i j)
    (hij : i ≠ j)
    (hrepeat : (O.dart i).tail = (O.dart j).tail) :
    S2RepeatedBoundaryArcSeparationSource (inputs := inputs) O i j :=
  ((rows.toRealWitnessSourceRows).toSourceWitnessRows hij hrepeat)
    |>.toRepeatedBoundaryArcSeparationSource

end S2RepeatedBoundaryArcRealWitnessPrimitiveRows

/-- Claim `S2-agent-repeated-boundary-arc-source-witnesses-20260520ab`.

Source-facing reducer for hypothetical repeated selected raw-orbit tails.  It
reduces `S2RepeatedBoundaryArcSeparationSource` to explicit open-arc witnesses,
non-cut raw-tail coverage, opposite-arc disjointness away from the repeated
tail, and anticompleteness across the two raw arcs. -/
noncomputable def
    S2_agent_repeated_boundary_arc_source_witnesses_20260520ab
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (witness_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcSourceWitnessRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcSeparationSource
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    (witness_source edgeRows htail hhead O hij hrepeat).toRepeatedBoundaryArcSeparationSource

/-- Claim `S2-agent-repeated-boundary-arc-witnesses-real-source-20260520ac`.

Sharp source reducer for hypothetical repeated selected raw-orbit tails.  The
real source row supplies only the geometric separation data: open-arc
witnesses, non-cut raw-tail coverage, opposite-arc disjointness away from the
repeated tail, and index-level anticompleteness across the two raw arcs.  The
hypothetical repeat itself supplies `i ≠ j` and the repeated-tail equality. -/
def S2_agent_repeated_boundary_arc_witnesses_real_source_20260520ac
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (real_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessSourceRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcSourceWitnessRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    (real_source edgeRows htail hhead O hij hrepeat).toSourceWitnessRows
      hij hrepeat

/-- Claim `S2-agent-repeated-boundary-arc-real-witness-source-20260520ad`.

Sharp reducer from the primitive real-source row for hypothetical repeated
selected raw-orbit tails to the checked finite cyclic boundary-arc separation
row.  The source obligation is exactly
`S2RepeatedBoundaryArcRealWitnessSourceRows`: open-arc witnesses, non-cut
raw-tail coverage, opposite-arc same-tail only at the repeated tail, and
index-level anticompleteness across the two open arcs. -/
noncomputable def
    S2_agent_repeated_boundary_arc_real_witness_source_20260520ad
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (real_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            Not (i = j) ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessSourceRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          Not (i = j) ->
          (O.dart i).tail = (O.dart j).tail ->
            RepeatedExteriorBoundaryArcSeparationRows C
              (fun k : Fin O.period => (O.dart k).tail) i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    (((real_source edgeRows htail hhead O hij hrepeat).toSourceWitnessRows
      hij hrepeat).toRepeatedBoundaryArcSeparationSource).toRepeatedExteriorBoundaryArcSeparationRows

/-- Claim `S2-agent-repeated-boundary-real-witness-primitive-source-20260520ae`.

Primitive callback for hypothetical repeated selected raw-orbit tails.  The
source obligations are only the arc-image witnesses, raw-tail coverage,
off-cut image disjointness, and image anticompleteness; this packages them as
the existing real witness rows consumed by
`S2_agent_repeated_boundary_arc_real_witness_source_20260520ad`. -/
noncomputable def
    S2_agent_repeated_boundary_real_witness_primitive_source_20260520ae
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (primitive_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            Not (i = j) ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessPrimitiveRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          Not (i = j) ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcRealWitnessSourceRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    (primitive_source edgeRows htail hhead O hij hrepeat).toRealWitnessSourceRows

/-- Claim `S2-dyn-20260520-two-arc-separation-source`.

Direct input-shaped reduction of the actual repeated-boundary arc source to
the primitive two-open-arc deleted-tail statement.  The residual is concrete:
for each hypothetical repeated selected raw tail, prove the two cyclic open
raw arc images have non-cut witnesses, cover every non-cut raw tail, are
disjoint away from the deleted tail, and are anticomplete across the induced
unit-distance graph. -/
noncomputable def
    S2_repeatedBoundaryArcSeparationSource_of_primitiveTwoOpenArcRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (primitive_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessPrimitiveRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcSeparationSource
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    (primitive_source edgeRows htail hhead O hij hrepeat)
      |>.toRepeatedBoundaryArcSeparationSource hij hrepeat

/-- Claim `S2-dyn-20260520-repeated-tail-primitive-rows-source`.

Strict source reduction of the exact primitive two-open-arc row to the
selected raw pair-level actual exterior-arc rows.  This stays on the selected
raw orbit and only erases the pair row fields to the primitive arc-image
language consumed by
`S2_repeatedBoundaryArcSeparationSource_of_primitiveTwoOpenArcRows_20260520`. -/
def
    S2_repeatedBoundaryPrimitiveRows_of_repeatedTailActualExteriorArcRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (actual_arc_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcRealWitnessPrimitiveRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    S2RepeatedBoundaryArcRealWitnessPrimitiveRows.ofRepeatedTailActualExteriorArcRows
      (inputs := inputs)
      (actual_arc_source edgeRows htail hhead O hij hrepeat)

/-- Claim `S2-dyn-20260520-repeated-tail-primitive-source`.

Input-shaped reducer for the remaining repeated-tail primitive row.  For each
hypothetical repeated selected raw tail, it reduces
`S2RepeatedBoundaryArcRealWitnessPrimitiveRows` to concrete raw-index witnesses
on the two cyclic open arcs, raw-tail coverage away from the deleted tail,
off-cut image disjointness, and anticompleteness across the two image sides. -/
def
    S2_dyn_20260520_repeated_tail_primitive_source
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (primitive_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcRealWitnessPrimitiveRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    (primitive_source edgeRows htail hhead O hij hrepeat).toPrimitiveRows

/-- Claim `S2-codex-20260520-real-witness-primitive-source-direct`.

Direct strict reduction of the live repeated-tail real-witness row to the
concrete primitive raw-index source.  The residual now consists of the chosen
left/right open-arc indices, non-cut raw-tail coverage, off-cut disjointness of
the two raw-tail arc images, and graph anticompleteness across those image
sides. -/
def
    S2_repeatedBoundaryRealWitnessSourceRows_of_primitiveSourceRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (primitive_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcRealWitnessSourceRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    (primitive_source edgeRows htail hhead O hij hrepeat)
      |>.toRealWitnessSourceRows

/-- Claim `S2-codex-20260520-primitive-source-rows-projection`.

The concrete raw-index real-witness row is a strict source for
`S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows`.  It keeps the chosen
left/right open-arc indices and raw-tail coverage unchanged, deriving only the
image-level disjointness and anticompleteness fields from their raw-index
counterparts. -/
def
    S2_repeatedBoundaryPrimitiveSourceRows_of_realWitnessSourceRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (real_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessSourceRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows.ofRealWitnessSourceRows
      (inputs := inputs)
      (real_source edgeRows htail hhead O hij hrepeat)

/-- The full repeated-boundary source-witness row also supplies the primitive
source rows directly.  This is useful when the repeat equality and `i ≠ j`
are already bundled with the same raw-index witness data. -/
def
    S2_repeatedBoundaryPrimitiveSourceRows_of_sourceWitnessRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (witness_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcSourceWitnessRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows.ofSourceWitnessRows
      (inputs := inputs)
      (witness_source edgeRows htail hhead O hij hrepeat)

/-- Claim `S2-dyn-20260520-repeated-tail-actual-exterior-arc-rows`.

Strict source reduction of the selected raw pair-level actual exterior-arc
rows to the primitive actual two-open-arc rows after deleting a hypothetical
repeated tail.  The source remains on the selected raw face-successor orbit:
no final boundary cycle, actual-boundary equivalence row, induced frontier
graph, arbitrary carrier/cycle, synthetic enclosure, or endpoint shortcut is
introduced. -/
noncomputable def
    S2_repeatedTailActualExteriorArcRows_of_primitiveTwoOpenArcRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (primitive_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessPrimitiveRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    (primitive_source edgeRows htail hhead O hij hrepeat)
      |>.toRepeatedTailActualExteriorArcRows hij hrepeat

/-- Direct separation-source handoff from selected raw pair-level actual
exterior-arc rows, through the primitive two-open-arc row. -/
noncomputable def
    S2_repeatedBoundaryArcSeparationSource_of_repeatedTailActualExteriorArcRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (actual_arc_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcSeparationSource
              (inputs := inputs) O i j :=
  S2_repeatedBoundaryArcSeparationSource_of_primitiveTwoOpenArcRows_20260520
    inputs
    (S2_repeatedBoundaryPrimitiveRows_of_repeatedTailActualExteriorArcRows_20260520
      inputs actual_arc_source)

/-- Claim-level handoff from the primitive actual two-open-arc source, through
the selected raw pair-level actual exterior-arc row, into the checked S2
repeated-boundary arc-separation source. -/
noncomputable def
    S2_repeatedBoundaryArcSeparationSource_of_primitiveTwoOpenArcRows_via_actualExteriorArcRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (primitive_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessPrimitiveRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedBoundaryArcSeparationSource
              (inputs := inputs) O i j :=
  S2_repeatedBoundaryArcSeparationSource_of_repeatedTailActualExteriorArcRows_20260520
    inputs
    (S2_repeatedTailActualExteriorArcRows_of_primitiveTwoOpenArcRows_20260520
      inputs primitive_source)

/-- The witness/index-level source also erases directly to the checked finite
cyclic arc-separation rows. -/
noncomputable def
    S2_repeatedBoundaryArcRows_of_source_witnesses_20260520ab
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (witness_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcSourceWitnessRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            RepeatedExteriorBoundaryArcSeparationRows C
              (fun k : Fin O.period => (O.dart k).tail) i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    ((witness_source edgeRows htail hhead O hij hrepeat).toRepeatedBoundaryArcSeparationSource).toRepeatedExteriorBoundaryArcSeparationRows

/-- Source row for a repeated raw tail: choose one non-cut tail on each
cyclic open arc and prove that those two chosen vertices are not reachable in
the unit-distance graph induced after deleting the repeated tail.

This is the primitive exterior separation content needed before the no-cut
eraser can make a hypothetical repeated tail impossible. -/
structure S2RepeatedTailExteriorCutWitnessSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (i j : Fin O.period) where
  left_index : Fin O.period
  left_index_mem : cyclicForwardOpenArc i j left_index
  left_index_ne_cut : (O.dart left_index).tail ≠ (O.dart i).tail
  right_index : Fin O.period
  right_index_mem : cyclicForwardOpenArc j i right_index
  right_index_ne_cut : (O.dart right_index).tail ≠ (O.dart i).tail
  unreachable_after_delete :
    ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
        ({(O.dart i).tail}ᶜ : Set (Fin n))).Reachable
        ⟨(O.dart left_index).tail, by simpa using left_index_ne_cut⟩
        ⟨(O.dart right_index).tail, by simpa using right_index_ne_cut⟩

namespace S2RepeatedTailExteriorCutWitnessSource

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}
variable {R : UnitDistanceRotationSystem C}
variable {start : UnitDistanceDart C}
variable {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
variable {i j : Fin O.period}

/-- The finite cyclic arc-separation row supplies exactly the repeated-tail
cut witness needed by the source surface: one raw-tail index on each open arc
and nonreachability after deleting the repeated tail. -/
noncomputable def ofRepeatedExteriorBoundaryArcSeparationRows
    (rows :
      RepeatedExteriorBoundaryArcSeparationRows C
        (fun k : Fin O.period => (O.dart k).tail) i j) :
    S2RepeatedTailExteriorCutWitnessSource (inputs := inputs) O i j where
  left_index := rows.left_index
  left_index_mem := rows.left_index_mem
  left_index_ne_cut := rows.left_index_ne_cut
  right_index := rows.right_index
  right_index_mem := rows.right_index_mem
  right_index_ne_cut := rows.right_index_ne_cut
  unreachable_after_delete := by
    simpa using rows.unreachable_after_delete

/-- The explicit S2 repeated-boundary arc source is stronger than the cut
witness source: the checked arc-separation row derives deleted-tail
nonreachability from cover/disjointness and anticompleteness. -/
noncomputable def ofRepeatedBoundaryArcSeparationSource
    (rows :
      S2RepeatedBoundaryArcSeparationSource (inputs := inputs) O i j) :
    S2RepeatedTailExteriorCutWitnessSource (inputs := inputs) O i j where
  left_index := rows.left_index
  left_index_mem := rows.left_index_mem
  left_index_ne_cut := rows.left_index_ne_cut
  right_index := rows.right_index
  right_index_mem := rows.right_index_mem
  right_index_ne_cut := rows.right_index_ne_cut
  unreachable_after_delete := rows.unreachable_after_delete

/-- The pair-level actual exterior-arc residual is stronger than the witness
source: erase it through the checked finite cyclic arc-separation row and keep
only the two witnesses plus deleted-tail nonreachability. -/
noncomputable def ofRepeatedTailActualExteriorArcRows
    (rows :
      RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
        (inputs := inputs) O i j)
    (hij : i ≠ j)
    (htail : (O.dart i).tail = (O.dart j).tail) :
    S2RepeatedTailExteriorCutWitnessSource (inputs := inputs) O i j :=
  ofRepeatedExteriorBoundaryArcSeparationRows (inputs := inputs)
    (rows.toRepeatedExteriorBoundaryArcSeparationRows hij htail)

/-- The witness source erases directly to the minimal repeated-tail cut row. -/
def toRepeatedTailExteriorCutRows
    (rows :
      S2RepeatedTailExteriorCutWitnessSource (inputs := inputs) O i j) :
    RawFaceSuccOrbitRepeatedTailExteriorCutRows
      (inputs := inputs) O i j where
  left_index := rows.left_index
  left_index_mem := rows.left_index_mem
  left_index_ne_cut := rows.left_index_ne_cut
  right_index := rows.right_index
  right_index_mem := rows.right_index_mem
  right_index_ne_cut := rows.right_index_ne_cut
  unreachable_after_delete := rows.unreachable_after_delete

/-- The deleted-tail witness package already gives the concrete cut partition
used by the no-cut interface. -/
noncomputable def toCutVertexPartition
    (rows :
      S2RepeatedTailExteriorCutWitnessSource (inputs := inputs) O i j) :
    CutVertexInterface.CutVertexPartition C :=
  rows.toRepeatedTailExteriorCutRows.toCutVertexPartition

/-- No-cut/minimality rules out any inhabited deleted-tail witness package. -/
theorem false_of_noCutVertex
    (rows :
      S2RepeatedTailExteriorCutWitnessSource (inputs := inputs) O i j) :
    False :=
  inputs.noCutVertex ⟨rows.toCutVertexPartition⟩

end S2RepeatedTailExteriorCutWitnessSource

/-- Claim `S2-dyn-20260520-repeated-tail-witness-source`.

Witness-level no-cut reducer for repeated selected raw tails.  If the selected
raw-orbit geometry/minimality step supplies a concrete cut partition for a
hypothetical repeated tail, the no-cut field makes that branch impossible and
therefore inhabits the deleted-tail witness package by contradiction. -/
def S2_repeatedTailExteriorCutWitnessSource_of_cutPartitions_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (repeated_tail_cutPartitions :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          Nonempty (CutVertexInterface.CutVertexPartition C)) :
    forall {i j : Fin O.period},
      i ≠ j ->
      (O.dart i).tail = (O.dart j).tail ->
        S2RepeatedTailExteriorCutWitnessSource
          (inputs := inputs) O i j := by
  intro i j hij htail
  exact False.elim (inputs.noCutVertex (repeated_tail_cutPartitions hij htail))

/-- Claim `S2-dyn-20260520-repeated-tail-cutpartition-source`.

Concrete cut-partition version of
`S2_repeatedTailExteriorCutWitnessSource_of_cutPartitions_20260520`.

This is the sharp residual Aristotle's repeated-tail lane leaves behind: for
each hypothetical repeated selected raw tail, produce the actual
`CutVertexInterface.CutVertexPartition C`.  The existing no-cut field then
makes the deleted-tail witness package available by contradiction. -/
def S2_repeatedTailExteriorCutWitnessSource_of_concreteCutPartitions_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (repeated_tail_cutPartitions :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          CutVertexInterface.CutVertexPartition C) :
    forall {i j : Fin O.period},
      i ≠ j ->
      (O.dart i).tail = (O.dart j).tail ->
        S2RepeatedTailExteriorCutWitnessSource
          (inputs := inputs) O i j :=
  S2_repeatedTailExteriorCutWitnessSource_of_cutPartitions_20260520
    (inputs := inputs) O
    (fun hij htail => ⟨repeated_tail_cutPartitions hij htail⟩)

/-- Family-shaped selected raw-orbit version of
`S2_repeatedTailExteriorCutWitnessSource_of_cutPartitions_20260520`. -/
def S2_repeatedTailExteriorCutWitnessSource_input_source_of_cutPartitions_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (cut_partition_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              Nonempty (CutVertexInterface.CutVertexPartition C)) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedTailExteriorCutWitnessSource
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    S2_repeatedTailExteriorCutWitnessSource_of_cutPartitions_20260520
      (inputs := inputs) O
      (fun hij' htail' =>
        cut_partition_source edgeRows htail hhead O hij' htail')
      hij hrepeat

/-- Claim `S2-dyn-20260520-repeated-tail-cutpartition-source`.

Input-shaped concrete cut-partition source for Aristotle's repeated-tail lane.
This is a strict reduction of
`S2_repeatedTailExteriorCutWitnessSource_input_source_of_cutPartitions_20260520`:
the callback now returns the concrete `CutVertexInterface.CutVertexPartition C`
for each repeated selected raw-tail pair, and this adapter wraps it for the
already checked no-cut witness reducer. -/
def S2_repeatedTailExteriorCutWitnessSource_input_source_of_concreteCutPartitions_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (cut_partition_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              CutVertexInterface.CutVertexPartition C) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedTailExteriorCutWitnessSource
              (inputs := inputs) O i j :=
  S2_repeatedTailExteriorCutWitnessSource_input_source_of_cutPartitions_20260520
    inputs
    (fun {e} {p} {start} edgeRows htail hhead O {i} {j} hij hrepeat =>
      ⟨cut_partition_source (e := e) (p := p) (start := start)
        edgeRows htail hhead O (i := i) (j := j) hij hrepeat⟩)

/-- Claim `S2-agent-repeated-boundary-arc-separation-source-20260520aa`.

Input-shaped reducer for the finite cyclic arc-separation row for hypothetical
repeated selected raw-orbit tails.  The remaining source obligation is the
explicit `S2RepeatedBoundaryArcSeparationSource`: it supplies one non-cut
witness on each cyclic open arc, non-cut coverage/disjointness for the two
arc images, and anticompleteness across the sides.  The resulting
`RepeatedExteriorBoundaryArcSeparationRows` also carries deleted-tail
nonreachability through its checked reducer. -/
noncomputable def
    S2_agent_repeated_boundary_arc_separation_source_20260520aa
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (arc_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcSeparationSource
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            RepeatedExteriorBoundaryArcSeparationRows C
              (fun k : Fin O.period => (O.dart k).tail) i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    (arc_source edgeRows htail hhead O hij hrepeat).toRepeatedExteriorBoundaryArcSeparationRows

/-- Cut-witness version of
`S2_agent_repeated_boundary_arc_separation_source_20260520aa`.

This is the downstream eraser: the same explicit arc-separation source gives
the minimal repeated-tail witness/nonreachability payload without passing
through actual-boundary rows. -/
noncomputable def
    S2_repeatedTailExteriorCutWitnessSource_of_repeatedBoundaryArcSeparationSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (arc_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcSeparationSource
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedTailExteriorCutWitnessSource
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    S2RepeatedTailExteriorCutWitnessSource.ofRepeatedBoundaryArcSeparationSource
      (inputs := inputs)
      (arc_source edgeRows htail hhead O hij hrepeat)

/-- Claim `S2-agent-repeated-tail-cut-witness-input-source-20260520z`.

Selected raw-orbit witness reducer from the finite cyclic arc-separation input.
This stays upstream of actual-boundary rows: for each hypothetical repeated
raw tail, the only remaining plane-separation content is the finite
`RepeatedExteriorBoundaryArcSeparationRows` package for the two cyclic open
arcs. -/
noncomputable def
    S2_repeatedTailExteriorCutWitnessSource_of_boundaryArcSeparationRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (boundary_arcRows_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              RepeatedExteriorBoundaryArcSeparationRows C
                (fun k : Fin O.period => (O.dart k).tail) i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedTailExteriorCutWitnessSource
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    S2RepeatedTailExteriorCutWitnessSource.ofRepeatedExteriorBoundaryArcSeparationRows
      (inputs := inputs)
      (boundary_arcRows_source edgeRows htail hhead O hij hrepeat)

/-- Claim `S2-dyn-20260520-repeated-tail-two-arc-cutpartition`.

For one hypothetical repeated selected raw-tail pair, the two cyclic open arcs
of the raw orbit after deleting the repeated tail give the concrete
`CutVertexInterface.CutVertexPartition C` as soon as the checked S2 two-arc
separation source is available.  This is a claim-specific adapter only; the
generic cut-interface construction remains the existing helper. -/
noncomputable def S2_repeated_tail_two_arc_cutpartition_20260520
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    {i j : Fin O.period}
    (rows :
      S2RepeatedBoundaryArcSeparationSource (inputs := inputs) O i j) :
    CutVertexInterface.CutVertexPartition C :=
  rows.toCutVertexPartition

/-- Input-shaped version of
`S2_repeated_tail_two_arc_cutpartition_20260520`.

This exposes Mendel's concrete repeated-tail cut-partition callback while
keeping the residual source at the two raw cyclic open arcs, upstream of
boundary-cycle rows, actual-boundary equivalence rows, induced frontier graphs,
arbitrary carrier/cycle choices, synthetic enclosures, and endpoint shortcuts. -/
noncomputable def
    S2_repeatedTail_cutPartition_callback_of_twoArcSeparationSource_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (two_arc_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcSeparationSource
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            CutVertexInterface.CutVertexPartition C := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    S2_repeated_tail_two_arc_cutpartition_20260520
      (inputs := inputs) O
      (two_arc_source edgeRows htail hhead O hij hrepeat)

/-- Claim `S2-agent-repeated-tail-cutpartition-source`.

Selected raw-orbit/frontier-edge source form of the repeated-tail
cut-partition residual.  Once the selected exterior seed edge, its oriented
raw face-successor orbit, and the repeated-tail two-arc separation source are
available, any repeated raw tail produces the `Nonempty CutVertexPartition`
callback expected by `SelectedRawOrbitRepeatedTailCutPartitions` downstream.

This is only a packaging reducer: the geometric separation content remains
the existing `S2RepeatedBoundaryArcSeparationSource` for the two cyclic open
raw-tail arcs. -/
theorem
    S2_agent_repeatedTail_cutPartition_nonempty_source_of_twoArcSeparationSource_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (two_arc_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcSeparationSource
                (inputs := inputs) O i j)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start) :
    forall {i j : Fin O.period},
      i ≠ j ->
      (O.dart i).tail = (O.dart j).tail ->
        Nonempty (CutVertexInterface.CutVertexPartition C) := by
  intro i j hij hrepeat
  exact
    Nonempty.intro
      (S2_repeated_tail_two_arc_cutpartition_20260520
        (inputs := inputs) O
        (two_arc_source edgeRows htail hhead O hij hrepeat))

/-- Repeated-boundary-arc-row version of
`S2_agent_repeatedTail_cutPartition_nonempty_source_of_twoArcSeparationSource_20260520`.

This exposes the residual in the older checked
`RepeatedExteriorBoundaryArcSeparationRows` language and packages it directly
as the cut-partition callback for the selected raw orbit. -/
theorem
    S2_agent_repeatedTail_cutPartition_nonempty_source_of_boundaryArcSeparationRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (boundary_arcRows_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              RepeatedExteriorBoundaryArcSeparationRows C
                (fun k : Fin O.period => (O.dart k).tail) i j)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start) :
    forall {i j : Fin O.period},
      i ≠ j ->
      (O.dart i).tail = (O.dart j).tail ->
        Nonempty (CutVertexInterface.CutVertexPartition C) := by
  intro i j hij hrepeat
  exact
    Nonempty.intro
      ((RepeatedExteriorBoundaryArcSeparationRows.toRepeatedExteriorBoundarySeparationRows
          (boundary_arcRows_source edgeRows htail hhead O hij hrepeat)).toCutVertexPartition)

/-- Primitive two-open-arc version of the repeated-tail cut-partition
callback.

This is the selected raw-orbit no-cut handoff with the residual stated at the
primitive arc-image level: for each hypothetical repeated raw tail, provide
the two open-arc image witnesses, non-cut raw-tail coverage, off-cut
disjointness, and anticompleteness across the two sides. -/
theorem
    S2_agent_repeatedTail_cutPartition_nonempty_source_of_primitiveTwoOpenArcRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (primitive_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessPrimitiveRows
                (inputs := inputs) O i j)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start) :
    forall {i j : Fin O.period},
      i ≠ j ->
      (O.dart i).tail = (O.dart j).tail ->
        Nonempty (CutVertexInterface.CutVertexPartition C) :=
  S2_agent_repeatedTail_cutPartition_nonempty_source_of_twoArcSeparationSource_20260520
    inputs
    (S2_repeatedBoundaryArcSeparationSource_of_primitiveTwoOpenArcRows_20260520
      inputs primitive_source)
    edgeRows htail hhead O

/-- Raw-index primitive source version of the repeated-tail cut-partition
callback.

This is the narrowest checked source reducer in this file: the callback is
reduced to chosen indices on the two cyclic open arcs, non-cut tail coverage,
off-cut image disjointness, and anticompleteness across the two arc images. -/
theorem
    S2_agent_repeatedTail_cutPartition_nonempty_source_of_primitiveSourceRows_20260520
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (primitive_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows
                (inputs := inputs) O i j)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start) :
    forall {i j : Fin O.period},
      i ≠ j ->
      (O.dart i).tail = (O.dart j).tail ->
        Nonempty (CutVertexInterface.CutVertexPartition C) :=
  S2_agent_repeatedTail_cutPartition_nonempty_source_of_primitiveTwoOpenArcRows_20260520
    inputs
    (S2_dyn_20260520_repeated_tail_primitive_source inputs primitive_source)
    edgeRows htail hhead O

/-- Cut-row source obtained from finite cyclic arc-separation rows via the
explicit repeated-tail witness source. -/
noncomputable def
    S2_repeatedTailExteriorCutRows_input_source_of_boundaryArcSeparationRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (boundary_arcRows_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              RepeatedExteriorBoundaryArcSeparationRows C
                (fun k : Fin O.period => (O.dart k).tail) i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            RawFaceSuccOrbitRepeatedTailExteriorCutRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    (S2_repeatedTailExteriorCutWitnessSource_of_boundaryArcSeparationRows
      inputs boundary_arcRows_source edgeRows htail hhead O hij hrepeat).toRepeatedTailExteriorCutRows

/-- The real-witness source also erases to the explicit repeated-tail
cut-witness callback, still upstream of actual-boundary and final S2 rows. -/
noncomputable def
    S2_repeatedTailExteriorCutWitnessSource_of_realWitnessSource_20260520ad
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (real_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            Not (i = j) ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessSourceRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          Not (i = j) ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedTailExteriorCutWitnessSource
              (inputs := inputs) O i j :=
  S2_repeatedTailExteriorCutWitnessSource_of_boundaryArcSeparationRows
    inputs
    (S2_agent_repeated_boundary_arc_real_witness_source_20260520ad
      inputs real_source)

/-- Cut-row callback obtained from the primitive real-witness repeated-arc
source.  This is the no-cut handoff surface used by the selected raw-orbit
route; the only unproved geometric content remains the real-witness row. -/
noncomputable def
    S2_repeatedTailExteriorCutRows_input_source_of_realWitnessSource_20260520ad
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (real_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            Not (i = j) ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessSourceRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          Not (i = j) ->
          (O.dart i).tail = (O.dart j).tail ->
            RawFaceSuccOrbitRepeatedTailExteriorCutRows
              (inputs := inputs) O i j :=
  S2_repeatedTailExteriorCutRows_input_source_of_boundaryArcSeparationRows
    inputs
    (S2_agent_repeated_boundary_arc_real_witness_source_20260520ad
      inputs real_source)

/-- The primitive arc-image real-witness source also erases to the explicit
repeated-tail cut-witness callback. -/
noncomputable def
    S2_repeatedTailExteriorCutWitnessSource_of_realWitnessPrimitiveSource_20260520ae
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (primitive_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            Not (i = j) ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessPrimitiveRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          Not (i = j) ->
          (O.dart i).tail = (O.dart j).tail ->
            S2RepeatedTailExteriorCutWitnessSource
              (inputs := inputs) O i j :=
  S2_repeatedTailExteriorCutWitnessSource_of_realWitnessSource_20260520ad
    inputs
    (S2_agent_repeated_boundary_real_witness_primitive_source_20260520ae
      inputs primitive_source)

/-- Cut-row callback obtained from the primitive arc-image real-witness source. -/
noncomputable def
    S2_repeatedTailExteriorCutRows_input_source_of_realWitnessPrimitiveSource_20260520ae
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (primitive_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            Not (i = j) ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedBoundaryArcRealWitnessPrimitiveRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          Not (i = j) ->
          (O.dart i).tail = (O.dart j).tail ->
            RawFaceSuccOrbitRepeatedTailExteriorCutRows
              (inputs := inputs) O i j :=
  S2_repeatedTailExteriorCutRows_input_source_of_realWitnessSource_20260520ad
    inputs
    (S2_agent_repeated_boundary_real_witness_primitive_source_20260520ae
      inputs primitive_source)

/-- Claim `S2-agent-repeated-tail-cutrows-input-source-20260520y`.

Input-shaped reducer for the remaining repeated-tail cut-row source.  The only
honest geometric/topological work left is the explicit witness source
`S2RepeatedTailExteriorCutWitnessSource`: one index on each cyclic open arc,
both different from the repeated tail, plus nonreachability after deleting
that tail. -/
noncomputable def
    S2_repeatedTailExteriorCutRows_input_source_of_unreachable_after_delete
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (witness_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedTailExteriorCutWitnessSource (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            RawFaceSuccOrbitRepeatedTailExteriorCutRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  let witness := witness_source edgeRows htail hhead O hij hrepeat
  exact
    S2_repeatedTailExteriorCutRows_of_unreachable_after_delete
      (inputs := inputs) O
      witness.left_index witness.left_index_mem witness.left_index_ne_cut
      witness.right_index witness.right_index_mem witness.right_index_ne_cut
      witness.unreachable_after_delete

/-- A deleted-tail witness is enough for the repeated-boundary separation row
needed by raw source rows.

This is the direct handoff from the primitive unreachable-after-delete
payload to the ordinary repeated-tail separation field, without passing
through actual-boundary rows. -/
def S2_repeatedBoundarySeparationRows_of_deletedTailWitness
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    {i j : Fin O.period}
    (hij : i ≠ j)
    (hrepeat : (O.dart i).tail = (O.dart j).tail)
    (witness :
      S2RepeatedTailExteriorCutWitnessSource (inputs := inputs) O i j) :
    RepeatedExteriorBoundarySeparationRows C
      (fun k : Fin O.period => (O.dart k).tail) i j :=
  RawFaceSuccOrbitRepeatedTailExteriorCutRows.toRepeatedExteriorBoundarySeparationRows
    witness.toRepeatedTailExteriorCutRows hij hrepeat

/-- Family/source version of
`S2_repeatedBoundarySeparationRows_of_deletedTailWitness`.

The source obligation is exactly the deleted-tail witness package for each
hypothetical repeated selected raw tail: one non-cut index on each cyclic open
arc and nonreachability after deleting the repeated tail. -/
def S2_repeatedBoundarySeparationRows_source_of_deletedTailWitnesses
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (witness_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              S2RepeatedTailExteriorCutWitnessSource
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            RepeatedExteriorBoundarySeparationRows C
              (fun k : Fin O.period => (O.dart k).tail) i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact
    S2_repeatedBoundarySeparationRows_of_deletedTailWitness
      (inputs := inputs) O hij hrepeat
      (witness_source edgeRows htail hhead O hij hrepeat)

/-- Raw source rows with the repeated-tail field reduced to deleted-tail
unreachable witnesses.

The residual is the primitive cut payload: for every hypothetical repeated
raw tail, choose one non-cut index on each cyclic open arc and prove the two
chosen tails are unreachable in the unit-distance graph after deleting the
repeated tail. -/
noncomputable def
    S2_rawFaceSuccOrbitSourceRows_of_dart_frontier_period_deletedTailWitnesses
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (connectedRows : UnboundedFrontierCarrierCyclicCoverageRows C inputs)
    (period_ge_three : 3 <= O.period)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (deleted_tail_witnesses :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          S2RepeatedTailExteriorCutWitnessSource (inputs := inputs) O i j) :
    RawFaceSuccOrbitSourceRows (inputs := inputs) O :=
  S2_rawFaceSuccOrbitSourceRows_of_dart_frontier_period_cutRows
    (C := C) (inputs := inputs) (R := R) O
    dart_edge_openSegment_frontier connectedRows period_ge_three
    localSectorRows
    (fun hij hrepeat =>
      S2_repeatedBoundarySeparationRows_of_deletedTailWitness
        (inputs := inputs) O hij hrepeat
        (deleted_tail_witnesses hij hrepeat))

/-- No-cut variant of the repeated-tail cut-row source.

If the exterior-face analysis can turn any repeated raw tail into a concrete
cut-vertex partition, then the `FinitePlanarOuterComponentInputs.noCutVertex`
field makes the repeated-tail cut-row callback vacuous. -/
def S2_repeatedTailExteriorCutRows_of_cutPartitions
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (repeated_tail_cutPartitions :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          Nonempty (CutVertexInterface.CutVertexPartition C)) :
    forall {i j : Fin O.period},
      i ≠ j ->
      (O.dart i).tail = (O.dart j).tail ->
        RawFaceSuccOrbitRepeatedTailExteriorCutRows
          (inputs := inputs) O i j := by
  intro i j hij htail
  exact False.elim (inputs.noCutVertex (repeated_tail_cutPartitions hij htail))

/-- Repeated-boundary separation rows are enough to source the minimal
repeated-tail cut callback.

This keeps S2-E on the smaller cut-row surface: a worker may prove the usual
`RepeatedExteriorBoundarySeparationRows` for repeated raw tails, and the
checked no-cut interface then makes the requested
`RawFaceSuccOrbitRepeatedTailExteriorCutRows` callback vacuous. -/
def S2_repeatedTailExteriorCutRows_of_repeatedBoundarySeparationRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (repeated_tail_rows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RepeatedExteriorBoundarySeparationRows C
            (fun k : Fin O.period => (O.dart k).tail) i j) :
    forall {i j : Fin O.period},
      i ≠ j ->
      (O.dart i).tail = (O.dart j).tail ->
        RawFaceSuccOrbitRepeatedTailExteriorCutRows
          (inputs := inputs) O i j :=
  S2_repeatedTailExteriorCutRows_of_cutPartitions
    (inputs := inputs) O
    (fun hij htail => ⟨(repeated_tail_rows hij htail).toCutVertexPartition⟩)

/-- Claim `S2-agent-repeated-boundary-separation-input-source-20260520x`.

Input-level reducer for the repeated-tail no-cut separation callback used by
`repeatedTailActualArcRows_source_of_repeatedBoundarySeparationRows`.

The residual source row is strictly upstream of actual-boundary rows: for a
hypothetical repeated raw tail it asks only for the minimal exterior cut row,
namely one witness on each cyclic open arc and graph nonreachability after
deleting the repeated tail.  That row erases to the Boolean-side repeated
boundary separation package by
`RawFaceSuccOrbitRepeatedTailExteriorCutRows.toRepeatedExteriorBoundarySeparationRows`. -/
noncomputable def
    repeatedBoundarySeparationRows_source_of_repeatedTailExteriorCutRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (repeated_tail_cutRows_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            i ≠ j ->
            (O.dart i).tail = (O.dart j).tail ->
              RawFaceSuccOrbitRepeatedTailExteriorCutRows
                (inputs := inputs) O i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          i ≠ j ->
          (O.dart i).tail = (O.dart j).tail ->
            RepeatedExteriorBoundarySeparationRows C
              (fun k : Fin O.period => (O.dart k).tail) i j :=
  fun {_e} {_p} {_start} edgeRows htail hhead O {_i} {_j} hij hrepeat =>
    RawFaceSuccOrbitRepeatedTailExteriorCutRows.toRepeatedExteriorBoundarySeparationRows
      (repeated_tail_cutRows_source edgeRows htail hhead O hij hrepeat)
      hij hrepeat

/-- Claim `S2-agent-repeated-tail-actual-arc-source-20260520w`.

Callback-shaped reducer for the selected raw-orbit actual exterior-arc source.
If an existing repeated-boundary separation source can produce the no-cut
separation rows for every hypothetical repeated raw tail, then the stronger
actual exterior-arc callback is available vacuously from
`FinitePlanarOuterComponentInputs.noCutVertex`.

This is intentionally a reducer to the existing repeated-boundary source row:
it does not introduce a new package or manufacture the actual finite arc
witness data directly. -/
noncomputable def repeatedTailActualArcRows_source_of_repeatedBoundarySeparationRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (repeated_tail_rows_source :
      forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
          {start : UnitDistanceDart C},
        UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
        start.tail = e.1 ->
        start.head = e.2 ->
        forall O :
          UnitDistanceRotationSystem.RawFaceSuccOrbit
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
            start,
          forall {i j : Fin O.period},
            Not (i = j) ->
            (O.dart i).tail = (O.dart j).tail ->
              RepeatedExteriorBoundarySeparationRows C
                (fun k : Fin O.period => (O.dart k).tail) i j) :
    forall {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
      UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
      start.tail = e.1 ->
      start.head = e.2 ->
      forall O :
        UnitDistanceRotationSystem.RawFaceSuccOrbit
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
          start,
        forall {i j : Fin O.period},
          Not (i = j) ->
          (O.dart i).tail = (O.dart j).tail ->
            RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
              (inputs := inputs) O i j := by
  intro e p start edgeRows htail hhead O i j hij hrepeat
  exact False.elim
    (inputs.noCutVertex
      ⟨(repeated_tail_rows_source edgeRows htail hhead O hij hrepeat).toCutVertexPartition⟩)

/-- Boundary-free local two-germ rows supply the pointwise local-sector family
used by the connected-carrier route. -/
theorem S2_carrier_connected_of_frontier_edge_point_localTwoGermRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  frontier_cover_to_connected_carrier_of_frontier_edge_point_localTwoGermRows
    inputs frontier_preconnected localTwoGermRows

/-- Local-sector rows plus the fixed-side half-ball interior-edge membership
row cover the whole unbounded exterior frontier by actual selected frontier
edges. -/
theorem S2_frontier_edge_cover_of_localSectorRows_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall p : PlanarInterface.Point,
      p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
        Exists fun e : PlanarInterface.Edge n =>
          e ∈ unboundedFrontierEdgeSet C inputs ∧
            p ∈ FinitePlaneDrawing.closedSegment
              ((canonicalGraph C).point e.1)
              ((canonicalGraph C).point e.2) :=
  frontier_edge_cover_of_localSectorRows_and_interior_edge_mem
    inputs localSectorRows
    (interior_frontier_edge_carrier_membership_source_of_fixed_side_halfballs
      (C := C) (inputs := inputs))

/-- The current frontier-preconnectedness source with the interior-edge
membership residual discharged by the fixed-side half-ball row. -/
theorem S2_frontier_preconnected_of_edge_chain_localSectorRows_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    IsPreconnected
      (frontier (unboundedExteriorComponentRows C inputs).exterior) :=
  S2_agent_frontier_preconnected_source_route
    inputs edge_segment_chain
    (S2_frontier_edge_cover_of_localSectorRows_fixedSide
      inputs localSectorRows)

/-- Compact preconnected-source package from edge-chain connectivity and the
fixed-side local-sector frontier cover. -/
def S2_frontierPreconnectedSourceRows_of_edgeChain_localSectorRows_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierPreconnectedSourceRows inputs where
  edge_segment_chain := edge_segment_chain
  frontier_edge_cover :=
    S2_frontier_edge_cover_of_localSectorRows_fixedSide inputs localSectorRows

/-- Frontier-preconnectedness from the actual selected-edge chain and the
boundary-free two-selected-edge/no-third-germ local source.

This is the current non-circular reduction for claim
`S2-agent-frontier-preconnected-from-inputs-20260520u`: the global input is the
actual unbounded frontier edge-carrier chain, while the pointwise input is the
local-sector cover source.  The cover is obtained through the existing
boundary-free local two-germ adapter, not from a completed cycle. -/
theorem S2_frontier_preconnected_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
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
    IsPreconnected
      (frontier (unboundedExteriorComponentRows C inputs).exterior) :=
  S2_frontier_preconnected_of_edge_chain_localSectorRows_fixedSide
    inputs edge_segment_chain
    (localSectorRows_of_localTwoGermRows
      (S2_localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
        (C := C) (inputs := inputs) source))

/-- Compact source-row package for the same non-circular frontier-
preconnectedness route. -/
def S2_frontierPreconnectedSourceRows_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
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
    UnboundedExteriorFrontierPreconnectedSourceRows inputs :=
  S2_frontierPreconnectedSourceRows_of_edgeChain_localSectorRows_fixedSide
    inputs edge_segment_chain
    (localSectorRows_of_localTwoGermRows
      (S2_localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
        (C := C) (inputs := inputs) source))

/-- Family-level frontier-preconnectedness target for claim
`S2-agent-frontier-preconnected-from-inputs-20260520u`.

It reduces the bare-input frontier row to two proof-owning source families:
the selected frontier edge-carrier chain and the boundary-free local-sector
source. -/
theorem S2_agent_frontier_preconnected_from_inputs_20260520u
    (edgeChainRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (sourceRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
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
                    q ∈ frontier
                        (unboundedExteriorComponentRows C inputs).exterior ->
                      (canonicalGraph C).Adj a.1 x ->
                        q ∈ vertexIncidentGermW3 C a.1 x ε ->
                          q ≠ (canonicalGraph C).point a.1 ->
                            x ≠ left ->
                              x ≠ right ->
                                False) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        IsPreconnected
          (frontier (unboundedExteriorComponentRows C inputs).exterior) :=
  fun C inputs =>
    S2_frontier_preconnected_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
      (C := C) (inputs := inputs)
      (edgeChainRows C inputs) (sourceRows C inputs)

/-- Compact preconnected-frontier source rows imply connectedness of the
concrete unbounded-frontier carrier graph.

This is the adjacency-closed topology route: the edge-chain/cover package first
proves preconnectedness of the actual exterior frontier, and the same cover
then supplies the nonempty adjacency-closed carrier rows. -/
theorem S2_carrier_connected_of_frontierPreconnectedSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (rows : UnboundedExteriorFrontierPreconnectedSourceRows inputs) :
    (unboundedFrontierCarrierGraph C inputs).Connected := by
  let frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior) :=
    unboundedExterior_frontier_preconnected_of_sourceRows inputs rows
  let topologyRows :
      UnboundedFrontierCarrierAdjClosedTopologySourceRows inputs :=
    unboundedFrontierCarrierAdjClosedTopologyRows_of_frontier_preconnected_and_frontier_edge_cover
      (C := C) (inputs := inputs)
      frontier_preconnected rows.frontier_edge_cover
  let frontier_vertices_nonempty :
      Nonempty {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    unboundedFrontierCarrier_nonempty_of_frontier_edge_cover
      inputs rows.frontier_edge_cover
  exact
    unboundedFrontierCarrierGraph_connected_of_adjClosed_topologyRows
      inputs frontier_vertices_nonempty topologyRows

/-- Carrier route to the concrete actual-boundary-cycle frontier rows.

This is the non-circular carrier source surfaced by the current S2 workboard:
frontier preconnectedness gives connectedness of the actual carrier, local
sector rows give degree two, and the carrier's own edge definition supplies
the boundary edge-membership row. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_frontierPreconnected_localSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (preconnectedRows : UnboundedExteriorFrontierPreconnectedSourceRows inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs := by
  classical
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  let source :
      ActualBoundaryCycleFrontierEquivalenceRows.BoundaryCycleEdgeMemSource
        C inputs :=
    boundaryCycleEdgeMemSource_of_connected_two_regular_frontier_graph_edge_mem
      (inputs := inputs)
      (F := unboundedFrontierCarrierGraph C inputs)
      (S2_carrier_connected_of_frontierPreconnectedSourceRows
        inputs preconnectedRows)
      (S2_agent_boundary_carrier_degree_two_from_local_sectors
        inputs localSectorRows)
      (unboundedFrontierCarrierGraphHom C inputs)
      (unboundedFrontierCarrierGraphHom_injective C inputs)
      (unboundedFrontierCarrierGraph_vertex_image_iff_frontier C inputs)
      (by
        intro x y hxy
        exact (unboundedFrontierCarrierGraph_adj_iff).1 hxy)
  exact
    ActualBoundaryCycleFrontierEquivalenceRows.ofBoundaryCycleEdgeMemSource
      (C := C) (inputs := inputs) source

/-- Final S2 cycle rows from the same non-circular carrier source. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_frontierPreconnected_localSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (preconnectedRows : UnboundedExteriorFrontierPreconnectedSourceRows inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
    (S2_actualBoundaryCycleFrontierEquivalenceRows_of_frontierPreconnected_localSectorRows
      inputs preconnectedRows localSectorRows)

/-- Carrier route to actual-boundary-cycle rows from the current component
topology primitive.

This is the component-topology sibling of
`S2_actualBoundaryCycleFrontierEquivalenceRows_of_frontierPreconnected_localSectorRows`.
The component source already gives connectedness of the concrete unbounded
frontier carrier; local-sector rows give two-regularity.  The carrier edge
definition supplies the boundary edge-membership row for the resulting cycle. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_componentTopology_localSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (componentTopologyRows :
      UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs := by
  classical
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  let source :
      ActualBoundaryCycleFrontierEquivalenceRows.BoundaryCycleEdgeMemSource
        C inputs :=
    boundaryCycleEdgeMemSource_of_connected_two_regular_frontier_graph_edge_mem
      (inputs := inputs)
      (F := unboundedFrontierCarrierGraph C inputs)
      (unboundedFrontierCarrierGraph_connected_of_componentTopologySourceRows
        inputs componentTopologyRows)
      (S2_agent_boundary_carrier_degree_two_from_local_sectors
        inputs localSectorRows)
      (unboundedFrontierCarrierGraphHom C inputs)
      (unboundedFrontierCarrierGraphHom_injective C inputs)
      (unboundedFrontierCarrierGraph_vertex_image_iff_frontier C inputs)
      (by
        intro x y hxy
        exact (unboundedFrontierCarrierGraph_adj_iff).1 hxy)
  exact
    ActualBoundaryCycleFrontierEquivalenceRows.ofBoundaryCycleEdgeMemSource
      (C := C) (inputs := inputs) source

/-- Final S2 cycle rows from component-topology source rows and local sectors. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_componentTopology_localSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (componentTopologyRows :
      UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
    (S2_actualBoundaryCycleFrontierEquivalenceRows_of_componentTopology_localSectorRows
      inputs componentTopologyRows localSectorRows)

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-actual-boundary-cycle-source`.

Strict actual-boundary-cycle reduction from the standard connected-frontier
topology theorem and pointwise actual-carrier local-sector rows.  The proof
uses the concrete `unboundedFrontierCarrierGraph`: connectedness comes from
the component-topology source, degree two from the local-sector rows, and each
cycle side is an actual selected `unboundedFrontierEdgeSet` edge. -/
noncomputable def
    S2_codex_20260520_actualBoundaryCycleFrontierEquivalenceRows_of_connectedFrontier_localSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_connected :
      PlanarContinuumUnboundedComplementFrontierConnected)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_componentTopology_localSectorRows
    inputs
    (componentTopologySourceRows_of_planarContinuumConnected_localSectorRows
      inputs frontier_connected localSectorRows)
    localSectorRows

set_option linter.style.longLine false in
/-- Claim `S2-codex-20260520-actual-boundary-cycle-source`.

The same actual-boundary-cycle reduction erased to the final
`UnboundedExteriorFrontierCycleRows` row consumed by W32. -/
noncomputable def
    S2_codex_20260520_unboundedExteriorFrontierCycleRows_of_connectedFrontier_localSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_connected :
      PlanarContinuumUnboundedComplementFrontierConnected)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
    (S2_codex_20260520_actualBoundaryCycleFrontierEquivalenceRows_of_connectedFrontier_localSectorRows
      inputs frontier_connected localSectorRows)

/-- Actual-boundary-cycle rows from edge-chain connectivity and local sectors,
with the fixed-side half-ball frontier cover hidden in the source package. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_localSectorRows_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_frontierPreconnected_localSectorRows
    inputs
    (S2_frontierPreconnectedSourceRows_of_edgeChain_localSectorRows_fixedSide
      inputs edge_segment_chain localSectorRows)
    localSectorRows

/-- Final S2 cycle rows from edge-chain connectivity and local sectors. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_edgeChain_localSectorRows_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_of_frontierPreconnected_localSectorRows
    inputs
    (S2_frontierPreconnectedSourceRows_of_edgeChain_localSectorRows_fixedSide
      inputs edge_segment_chain localSectorRows)
    localSectorRows

/-- Actual-boundary-cycle rows from the selected frontier-edge chain and the
pointwise concrete carrier neighbour-pair source.

This is the smallest current carrier route through this owner file: the
edge-chain row proves frontier preconnectedness, while the neighbour-pair row
is erased locally to the two exterior carrier germs at each frontier vertex. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_neighborPairRows_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_localSectorRows_fixedSide
    inputs edge_segment_chain
    (localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
      (C := C) inputs neighborRows)

/-- Final S2 cycle rows from the selected frontier-edge chain and the
pointwise concrete carrier neighbour-pair source. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_edgeChain_neighborPairRows_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_of_edgeChain_localSectorRows_fixedSide
    inputs edge_segment_chain
    (localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
      (C := C) inputs neighborRows)

/-- Family-level finite planar outer-component theorem from the two remaining
concrete-carrier source families: selected edge-chain connectivity and
pointwise neighbour-pair rows. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_neighborPairRows
    (edgeChainRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      S2_unboundedExteriorFrontierCycleRows_of_edgeChain_neighborPairRows_fixedSide
        (C := C) (inputs := inputs)
        (edgeChainRows C inputs) (neighborRows C inputs))

/-- Selected endpoint-chain connectivity plus pointwise cut-partition
neighbour rows fill the current concrete-carrier S2 handoff.

This only composes the two source refinements; the remaining geometric proof is
to produce the endpoint chain and the pointwise cut-partition rows from the
unbounded exterior component. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_selectedEndpointChain_cutPartitionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (edge_endpoint_chain :
      UnboundedFrontierSelectedEdgeEndpointChainConnected inputs)
    (cutRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_of_edgeChain_neighborPairRows_fixedSide
    (C := C) (inputs := inputs)
    (S2_agent_edge_chain_source_20260520ar
      (C := C) (inputs := inputs) edge_endpoint_chain)
    (unboundedFrontierCarrierNeighborPairRows_of_noCutVertex_cutPartitionRows
      (C := C) (inputs := inputs) cutRows)

/-- Family-level finite planar outer-component theorem from the sharpened
selected-edge source split: actual endpoint-chain connectivity of selected
frontier edges and pointwise cut-partition rows for third neighbours. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_selectedEndpointChain_cutPartitionRows
    (edgeEndpointRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierSelectedEdgeEndpointChainConnected inputs)
    (cutRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      S2_unboundedExteriorFrontierCycleRows_of_selectedEndpointChain_cutPartitionRows
        (C := C) (inputs := inputs)
        (edgeEndpointRows C inputs) (cutRows C inputs))

/-- Actual-boundary-cycle rows from the edge-chain connectivity row and the
boundary-free no-third-germ local source.

This packages the current non-circular carrier route with the local-sector
adapter hidden: the only remaining source rows are the actual edge-chain
connectivity of the unbounded frontier carrier and the pointwise two-germ
local geometry at each frontier vertex. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
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
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_localSectorRows_fixedSide
    inputs edge_segment_chain
    (S2_localSectorRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
      (C := C) (inputs := inputs) source)

/-- Final S2 cycle rows from edge-chain connectivity and the boundary-free
no-third-germ local source. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
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
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
    (S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
      inputs edge_segment_chain source)

/-- Local-sector rows plus endpoint-frontier incident-edge closure give the
boundary-free two-selected-edge/no-third-germ source.

The open-segment case is already handled by the definition of the actual
unbounded frontier edge set; the only extra local source row is that a
frontier endpoint adjacent to the carrier vertex is itself connected by a
selected unbounded-frontier edge. -/
theorem
    S2_boundaryFree_twoSelectedEdges_noThirdGerm_source_of_localSector_endpointIncidentRows
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
                          False := by
  intro a
  refine
    ⟨(localSectorRows a).left, (localSectorRows a).right,
      (localSectorRows a).left_edge, (localSectorRows a).right_edge,
      (localSectorRows a).heads_ne, ?_⟩
  intro ε q x _hqball hqfrontier hadj hgerm hqne hx_left hx_right
  rcases hgerm with ⟨_hqball_germ, hqclosed⟩
  rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hqclosed with
    hq_center | hq_endpoint | hq_open
  · exact hqne hq_center
  · have hxfrontier :
        (canonicalGraph C).point x ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior := by
      simpa [hq_endpoint] using hqfrontier
    let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
      ⟨x, mem_unboundedFrontierVertexSet_iff.2 hxfrontier⟩
    have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
      exact (unboundedFrontierCarrierGraph_adj_iff).2
        (endpoint_frontier_edge a x hadj hxfrontier)
    rcases (localSectorRows a).only b hadjCarrier with hx | hx
    · exact hx_left hx
    · exact hx_right hx
  · have hsource :
        InteriorFrontierEdgeCarrierMembershipSource C inputs :=
      interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
    rcases hadj with hadj_uv | hadj_vu
    · have hmem :
          (a.1, x) ∈ unboundedFrontierEdgeSet C inputs :=
        hsource (e := (a.1, x)) (p := q) hadj_uv hq_open hqfrontier
      have hxmem : x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
          hmem).2
      let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
        ⟨x, hxmem⟩
      have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
        exact (unboundedFrontierCarrierGraph_adj_iff).2 (Or.inl hmem)
      rcases (localSectorRows a).only b hadjCarrier with hx | hx
      · exact hx_left hx
      · exact hx_right hx
    · have hmem :
          (x, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
        hsource (e := (x, a.1)) (p := q)
          hadj_vu (inOpenSegment_symm hq_open) hqfrontier
      have hxmem : x ∈ unboundedFrontierVertexSet C inputs :=
        (endpoints_mem_unboundedFrontierVertexSet_of_unboundedFrontierEdgeSet
          unboundedFrontierEdgeSetWholeOpenSegmentFrontier_of_definition
          hmem).1
      let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
        ⟨x, hxmem⟩
      have hadjCarrier : (unboundedFrontierCarrierGraph C inputs).Adj a b := by
        exact (unboundedFrontierCarrierGraph_adj_iff).2 (Or.inr hmem)
      rcases (localSectorRows a).only b hadjCarrier with hx | hx
      · exact hx_left hx
      · exact hx_right hx

/-- Local-sector rows plus the adjacent-endpoint interior-closure source give
the boundary-free two-selected-edge/no-third-germ source.

This removes the explicit endpoint incident-edge field from
`S2_boundaryFree_twoSelectedEdges_noThirdGerm_source_of_localSector_endpointIncidentRows`:
the adjacent endpoint closure point is promoted to an actual selected
`unboundedFrontierEdgeSet` edge by the fixed-side half-ball interior carrier
membership theorem. -/
theorem
    S2_boundaryFree_twoSelectedEdges_noThirdGerm_source_of_localSector_interiorClosure
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (interior_closure :
      AdjacentFrontierEndpointsInteriorClosurePointSource C inputs) :
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
                          False :=
  S2_boundaryFree_twoSelectedEdges_noThirdGerm_source_of_localSector_endpointIncidentRows
    (C := C) (inputs := inputs)
    localSectorRows
    (fun a _x hadj hxfrontier =>
      incidentUnboundedFrontierEdgeSource_of_interiorClosure
        (C := C) (inputs := inputs) interior_closure
        hadj (mem_unboundedFrontierVertexSet_iff.1 a.2) hxfrontier)

/-- Actual-boundary-cycle rows from edge-chain connectivity, local-sector rows,
and endpoint-frontier incident-edge closure. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_localSector_endpointIncidentRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
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
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
    (C := C) (inputs := inputs) edge_segment_chain
    (S2_boundaryFree_twoSelectedEdges_noThirdGerm_source_of_localSector_endpointIncidentRows
      (C := C) (inputs := inputs) localSectorRows endpoint_frontier_edge)

/-- Final S2 cycle rows from edge-chain connectivity, local-sector rows, and
endpoint-frontier incident-edge closure. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_edgeChain_localSector_endpointIncidentRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
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
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
    (S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_localSector_endpointIncidentRows
      (C := C) (inputs := inputs) edge_segment_chain localSectorRows
      endpoint_frontier_edge)

/-- Family-level finite planar straight-line outer-component theorem from the
edge-chain, local-sector, and endpoint-frontier incident-edge source rows. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_localSector_endpointIncidentRows
    (edgeChainRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (localSectorRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (endpointRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
            (x : Fin n),
            (canonicalGraph C).Adj a.1 x ->
              (canonicalGraph C).point x ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (a.1, x) ∈ unboundedFrontierEdgeSet C inputs ∨
                  (x, a.1) ∈ unboundedFrontierEdgeSet C inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      S2_unboundedExteriorFrontierCycleRows_of_edgeChain_localSector_endpointIncidentRows
        (C := C) (inputs := inputs)
        (edgeChainRows C inputs) (localSectorRows C inputs)
        (endpointRows C inputs))

/-- Actual-boundary-cycle rows from a raw orbit that covers all selected
frontier edges, plus the boundary-free no-third-germ local source. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_rawOrbitCoverage_boundaryFree_noThirdGerm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail))
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
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
    (C := C) (inputs := inputs)
    (S2_edgeCarrierSegmentChainConnected_of_rawFaceSuccOrbit_dartFrontier_edgeCoverage
      (C := C) (inputs := inputs) O
      dart_edge_openSegment_frontier edge_coverage)
    source

/-- Final S2 cycle rows from a raw orbit that covers all selected frontier
edges, plus the boundary-free no-third-germ local source. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_rawOrbitCoverage_boundaryFree_noThirdGerm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail))
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
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
    (S2_actualBoundaryCycleFrontierEquivalenceRows_of_rawOrbitCoverage_boundaryFree_noThirdGerm
      (C := C) (inputs := inputs) O
      dart_edge_openSegment_frontier edge_coverage source)

/-- Carrier-connected raw-orbit S2 assembly, with pointwise local-sector rows
obtained from the boundary-free local two-germ source. -/
noncomputable def
    S2_rawOrbitCutRows_of_carrierConnected_localTwoGermRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (localTwoGermRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a)
    (carrier_connected : (unboundedFrontierCarrierGraph C inputs).Connected)
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
          RawFaceSuccOrbitRepeatedTailExteriorCutRows (inputs := inputs) O i j) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_agent_input_s2_assembly_gap_reducer_rawOrbitCutRows_of_carrierConnected
    inputs (localSectorRows_of_localTwoGermRows localTwoGermRows)
    carrier_connected edgeRows htail hhead O dart_edge_openSegment_frontier
    cutRows

/-- Fully local-two-germ version of the current raw-orbit S2 assembly surface.
The remaining rows are exactly the global frontier preconnectedness row, the
selected raw-orbit dart-edge frontier row, and repeated-tail cut rows. -/
noncomputable def
    S2_rawOrbitCutRows_of_frontier_edge_point_localTwoGermRows
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
          RawFaceSuccOrbitRepeatedTailExteriorCutRows (inputs := inputs) O i j) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  rawOrbitCutRows_of_frontierPreconnectedLocalTwoGermRows
    inputs frontier_preconnected localTwoGermRows
    edgeRows htail hhead O dart_edge_openSegment_frontier cutRows

/-- Source-facing assembly from the boundary-free local no-third-germ family
and the selected raw exterior face-orbit rows. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_noThirdGermRawRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (left right :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} -> Fin n)
    (left_edge :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (right_edge :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (heads_ne :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        left a ≠ right a)
    (no_third_germ :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ left a ->
                    x ≠ right a ->
                      False)
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
          RawFaceSuccOrbitRepeatedTailExteriorCutRows (inputs := inputs) O i j) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_rawOrbitCutRows_of_frontier_edge_point_localTwoGermRows
    inputs frontier_preconnected
    (S2_localTwoGermRows_of_noThirdGermFamily
      left right left_edge right_edge heads_ne no_third_germ)
    edgeRows htail hhead O dart_edge_openSegment_frontier cutRows

/-- Source-facing assembly from the boundary-free local no-third-germ family
and the stronger actual-exterior-arc package.

The actual-arc package supplies both selected raw dart frontier rows and the
minimal repeated-tail cut rows. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_noThirdGermActualArcRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
    (left right :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} -> Fin n)
    (left_edge :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (right_edge :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (heads_ne :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        left a ≠ right a)
    (no_third_germ :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ left a ->
                    x ≠ right a ->
                      False)
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
  actualArcRows_of_frontierPreconnectedLocalTwoGermRows
    inputs frontier_preconnected
    (S2_localTwoGermRows_of_noThirdGermFamily
      left right left_edge right_edge heads_ne no_third_germ)
    edgeRows htail hhead O actualArcRows

/-- Source-facing actual-arc S2 assembly using the existential boundary-free
two-selected-edge/no-third-germ source at each unbounded-frontier graph vertex.

The remaining inputs are global: preconnectedness of the actual frontier, the
selected edge/raw-orbit seed, and the actual exterior-arc separation rows for
that orbit. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_boundaryFree_noThirdGermActualArcRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior))
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
                            False)
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
  actualArcRows_of_frontierPreconnectedLocalTwoGermRows
    inputs frontier_preconnected
    (S2_localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
      source)
    edgeRows htail hhead O actualArcRows

/-- Actual-arc S2 assembly with the frontier-preconnectedness row sourced from
an honest selected-edge segment chain and the boundary-free no-third-germ rows.

This leaves the proof-owning global inputs as the actual edge-chain source,
the pointwise two-selected-edge/no-third-germ source, and the selected raw
actual-exterior-arc package. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_edgeChain_boundaryFree_noThirdGermActualArcRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (edge_segment_chain :
      UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
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
                            False)
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
    UnboundedExteriorFrontierCycleRows C inputs := by
  let localTwoGermRows :=
    S2_localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
      (C := C) (inputs := inputs) source
  let localSectorRows :=
    localSectorRows_of_localTwoGermRows localTwoGermRows
  let frontier_preconnected :
      IsPreconnected
        (frontier (unboundedExteriorComponentRows C inputs).exterior) :=
    S2_frontier_preconnected_of_edge_chain_localSectorRows_fixedSide
      inputs edge_segment_chain localSectorRows
  exact
    actualArcRows_of_frontierPreconnectedLocalTwoGermRows
      inputs frontier_preconnected localTwoGermRows
      edgeRows htail hhead O actualArcRows

/-- Actual boundary-cycle rows from the boundary-free local source, raw-tail
coverage, per-dart frontier rows, and the repeated-tail cut source.

This is the shortest raw-orbit-to-actual-boundary handoff in this file: the
local source gives local sectors, raw-tail coverage gives the frontier vertex
equivalence, the dart frontier row gives consecutive boundary edge frontier,
and the cut rows make the raw orbit simple. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_boundaryFree_noThirdGermCutRows_tailCoverage
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
                            False)
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
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
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_agent_actualBoundaryCycleRows_of_rawExteriorFaceWalk_cutRows
    (inputs := inputs) O
    (localSectorRows_of_localTwoGermRows
      (S2_localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
        (C := C) (inputs := inputs) source))
    frontier_vertex_tail_coverage dart_edge_openSegment_frontier cutRows

/-- Actual-boundary-cycle rows from the stronger actual-exterior-arc source.

The actual-arc package supplies both the per-dart open-segment frontier row
and the repeated-tail cut rows, so the remaining raw-orbit inputs are the
boundary-free local source and raw-tail coverage of every unbounded-frontier
vertex. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_boundaryFree_noThirdGermActualArcRows_tailCoverage
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
                            False)
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (actualArcRows :
      RawFaceSuccOrbitActualExteriorArcSeparationRows
        (inputs := inputs) O) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_boundaryFree_noThirdGermCutRows_tailCoverage
    (C := C) (inputs := inputs) source O frontier_vertex_tail_coverage
    (rawFaceSuccOrbit_dart_edge_openSegment_frontier_of_actualExteriorArcSeparationRows
      (inputs := inputs) O actualArcRows)
    (rawFaceSuccOrbitRepeatedTailExteriorCutRows_of_actualExteriorArcSeparationRows
      (inputs := inputs) O actualArcRows)

/-- Final S2 row from the same shortest raw-orbit actual-boundary handoff. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_boundaryFree_noThirdGermCutRows_tailCoverage
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
                            False)
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
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
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
    (S2_actualBoundaryCycleFrontierEquivalenceRows_of_boundaryFree_noThirdGermCutRows_tailCoverage
      (C := C) (inputs := inputs) source O frontier_vertex_tail_coverage
      dart_edge_openSegment_frontier cutRows)

/-- Raw-orbit coverage of all selected frontier edges, together with the
boundary-free two-selected-edge local source, covers every selected frontier
vertex by a raw orbit tail.

This is a finite endpoint bookkeeping lemma: the local source gives a genuine
selected unbounded-frontier edge incident to `a`; raw edge coverage says that
edge is one consecutive raw edge up to orientation, so `a` is either the raw
tail at that index or the raw tail at its cyclic successor. -/
theorem S2_frontier_vertex_tail_coverage_of_edgeCoverage_boundaryFree_source
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail))
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
      Exists fun k : Fin O.period => (O.dart k).tail = a.1 := by
  classical
  intro a
  rcases source a with ⟨left, right, hleft, _hright, _hne, _hthird⟩
  rcases hleft with hleft | hleft
  · let e : {e : PlanarInterface.Edge n //
        e ∈ unboundedFrontierEdgeSet C inputs} := ⟨(a.1, left), hleft⟩
    rcases edge_coverage e with ⟨k, hk⟩
    rcases hk with hk | hk
    · refine ⟨k, ?_⟩
      have hfst :
          e.1.1 = (O.dart k).tail := congrArg Prod.fst hk
      simpa [e] using hfst.symm
    · refine ⟨PlanarInterface.cyclicSucc O.period_pos k, ?_⟩
      have hfst :
          e.1.1 =
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
        congrArg Prod.fst hk
      simpa [e] using hfst.symm
  · let e : {e : PlanarInterface.Edge n //
        e ∈ unboundedFrontierEdgeSet C inputs} := ⟨(left, a.1), hleft⟩
    rcases edge_coverage e with ⟨k, hk⟩
    rcases hk with hk | hk
    · refine ⟨PlanarInterface.cyclicSucc O.period_pos k, ?_⟩
      have hsnd :
          e.1.2 =
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
        congrArg Prod.snd hk
      simpa [e] using hsnd.symm
    · refine ⟨k, ?_⟩
      have hsnd :
          e.1.2 = (O.dart k).tail := congrArg Prod.snd hk
      simpa [e] using hsnd.symm

/-- Actual-boundary-cycle rows from raw-orbit edge coverage, per-dart
frontier rows, the boundary-free local source, and repeated-tail cut rows.

Compared with the tail-coverage handoff, this theorem derives raw-tail
coverage from the selected-edge coverage row and the pointwise local source. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_rawOrbitCoverage_boundaryFree_noThirdGermCutRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
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
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail))
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
                            False)
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_boundaryFree_noThirdGermCutRows_tailCoverage
    (C := C) (inputs := inputs) source O
      (S2_frontier_vertex_tail_coverage_of_edgeCoverage_boundaryFree_source
        (C := C) (inputs := inputs) O edge_coverage source)
    dart_edge_openSegment_frontier cutRows

/-- Actual-boundary-cycle rows from raw-orbit edge coverage plus the stronger
actual-exterior-arc package.

Compared with the cut-row handoff, this consumes one honest orbit-level source
`actualArcRows`: its edge-membership field supplies the per-dart frontier row,
and its repeated-tail arc rows erase to the minimal cut payload.  The separate
`edge_coverage` row remains the non-circular statement that every selected
unbounded-frontier edge is reached by the raw orbit. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_rawOrbitCoverage_boundaryFree_noThirdGermActualArcRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail))
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
                            False)
    (actualArcRows :
      RawFaceSuccOrbitActualExteriorArcSeparationRows
        (inputs := inputs) O) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_rawOrbitCoverage_boundaryFree_noThirdGermCutRows
    (C := C) (inputs := inputs) O
    (rawFaceSuccOrbit_dart_edge_openSegment_frontier_of_actualExteriorArcSeparationRows
      (inputs := inputs) O actualArcRows)
    edge_coverage source
    (rawFaceSuccOrbitRepeatedTailExteriorCutRows_of_actualExteriorArcSeparationRows
      (inputs := inputs) O actualArcRows)

set_option linter.style.longLine false in
/-- Actual-boundary-cycle rows from carrier-connectedness and actual-arc rows.

Compared with the raw-coverage handoff above, this reducer derives the needed
raw-tail coverage from connectedness of the honest frontier carrier and the
local sector rows obtained from the boundary-free no-third-germ source.  The
actual-arc package supplies the dart-edge frontier row and the repeated-tail
cut rows through the existing tail-coverage reducer. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_boundaryFree_noThirdGermActualArcRows_carrierConnected
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
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
                            False)
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (actualArcRows :
      RawFaceSuccOrbitActualExteriorArcSeparationRows
        (inputs := inputs) O) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    S2_localSectorRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
      (C := C) (inputs := inputs) source
  let dart_edge_openSegment_frontier :
      forall k : Fin O.period,
        forall q : PlanarInterface.Point,
          PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point (O.dart k).head) ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
    rawFaceSuccOrbit_dart_edge_openSegment_frontier_of_actualExteriorArcSeparationRows
      (inputs := inputs) O actualArcRows
  let frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1 :=
    (S2_agent_selected_raw_orbit_frontier_and_tail_coverage_source_no_edgeRows
      (C := C) (inputs := inputs) localSectorRows carrier_connected O
      dart_edge_openSegment_frontier).2
  exact
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_boundaryFree_noThirdGermActualArcRows_tailCoverage
      (C := C) (inputs := inputs) source O
      frontier_vertex_tail_coverage actualArcRows

set_option linter.style.longLine false in
/-- Family-selected no-third-germ version of
`S2_actualBoundaryCycleFrontierEquivalenceRows_of_boundaryFree_noThirdGermActualArcRows_carrierConnected`.

This is the same actual-boundary reducer with the pointwise left/right
selection exposed directly, matching the source shape used by the current
input-facing S2 route. -/
noncomputable def
    S2_actualBoundaryCycleFrontierEquivalenceRows_of_noThirdGermActualArcRows_carrierConnected
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    (left right :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} -> Fin n)
    (left_edge :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (right_edge :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (heads_ne :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        left a ≠ right a)
    (no_third_germ :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ left a ->
                    x ≠ right a ->
                      False)
    {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (actualArcRows :
      RawFaceSuccOrbitActualExteriorArcSeparationRows
        (inputs := inputs) O) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
  S2_actualBoundaryCycleFrontierEquivalenceRows_of_boundaryFree_noThirdGermActualArcRows_carrierConnected
    inputs carrier_connected
    (fun a =>
      ⟨left a, right a, left_edge a, right_edge a, heads_ne a,
        no_third_germ a⟩)
    O actualArcRows

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-actual-boundary-rows-source`.

Strict connected-carrier/raw-face-successor reduction of the actual boundary
rows.  The construction starts from `FinitePlanarOuterComponentInputs C`, then
uses the current S2 source residuals: local sectors, connectedness of the
actual unbounded-frontier carrier, a selected geometric raw face-successor
orbit, whole raw-dart frontier propagation, and repeated-tail separation.

It constructs `ActualBoundaryCycleFrontierEquivalenceRows` directly through
`ActualBoundaryCycleFrontierEquivalenceRows.ofRawFaceSuccOrbitBoundaryRows`;
it does not consume `UnboundedExteriorFrontierCycleRows`, cyclic coverage from a
completed boundary, an induced frontier graph, arbitrary cycles, convex hulls,
or identity angular order. -/
noncomputable def S2_dyn_20260520_actual_boundary_rows_source
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    {start : UnitDistanceDart C}
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
    (repeated_tail_rows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RepeatedExteriorBoundarySeparationRows C
            (fun k : Fin O.period => (O.dart k).tail) i j) :
    ActualBoundaryCycleFrontierEquivalenceRows C inputs := by
  classical
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
  let frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1 :=
    (S2_agent_selected_raw_orbit_frontier_and_tail_coverage_source_no_edgeRows
      (C := C) (inputs := inputs) localSectorRows carrier_connected O
      dart_edge_openSegment_frontier).2
  let frontier_iff_tail :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin O.period => (O.dart k).tail = v :=
    rawFaceSuccOrbit_frontier_iff_tail_of_frontier_vertex_tail_coverage
      O edge_openSegment_frontier frontier_vertex_tail_coverage
  let period_ge_three : 3 <= O.period :=
    rawFaceSuccOrbit_period_three_le_of_edge_openSegment_frontier_tail_coverage_localSectorRows
      (inputs := inputs) O edge_openSegment_frontier
      frontier_vertex_tail_coverage localSectorRows
  let hB :=
    exists_unitDistanceCycleBoundary_of_rawFaceSuccOrbit_tail_injective
      O period_ge_three
      (rawFaceSuccOrbit_tail_injective_of_noCutVertex
        (inputs := inputs) O repeated_tail_rows)
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose hB
  let hperiod : B.length = O.period :=
    Classical.choose (Classical.choose_spec hB)
  let tail_eq :
      forall k : Fin B.length,
        (O.dart (Fin.cast hperiod k)).tail = B.vertex k :=
    Classical.choose_spec (Classical.choose_spec hB)
  exact
    ActualBoundaryCycleFrontierEquivalenceRows.ofRawFaceSuccOrbitBoundaryRows
      (inputs := inputs) O B hperiod tail_eq frontier_iff_tail
      edge_openSegment_frontier

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-boundary-sector-input-source`.

Actual boundary-cycle rows plus the existing pointwise local-sector rows
strictly reduce the input-facing boundary-sector source to angular
predecessor/successor rows.  The local-sector rows supply incident frontier
edge completeness for the same concrete boundary cycle; no induced frontier
graph, arbitrary cycle, endpoint-only shortcut, or synthetic enclosure is
introduced. -/
theorem
    S2_agent_20260520_boundarySectorRows_of_actualBoundaryRows_localSectorRows_angular
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k :=
  S2_boundaryVertexExteriorSectorRows_source_of_boundaryCycleIncidentFrontierEdgeCompleteness
    (C := C) (inputs := inputs)
    actualRows.boundary
    actualRows.frontier_iff_cycle_vertex
    actualRows.cycle_edge_openSegment_frontier
    angularRows
    (S2_agent_local_sector_incident_bridge
      (C := C) (inputs := inputs) actualRows localSectorRows)

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-boundary-sector-input-source`.

Face-successor/orientation version of
`S2_agent_20260520_boundarySectorRows_of_actualBoundaryRows_localSectorRows_angular`.
The angular rows are sourced from the genuine geometric rotation system and
the local-sector rows discharge the boundary incident-completeness residual
for the same actual boundary cycle. -/
theorem
    S2_agent_20260520_boundarySectorRows_of_actualBoundaryRows_localSectorRows_faceSuccOrientation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
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
  S2_agent_20260520_boundarySectorRows_of_actualBoundaryRows_localSectorRows_angular
    (C := C) (inputs := inputs) actualRows localSectorRows
    (GeometricRotationSystem.boundaryVertexAngularNoBetweenRows_of_faceSuccRows_pred_arg_lt_succ_arg
      C actualRows.boundary faceSuccRows boundary_orientation)

set_option linter.style.longLine false in
/-- Claim `S2-agent-20260520-boundary-sector-input-source`.

Raw-orbit/local-sector reduction of the input-facing boundary-sector source.
It first builds the actual boundary-cycle frontier-equivalence rows from the
selected geometric raw face-successor orbit and local-sector carrier
connectedness, then derives same-boundary face-successor and angular rows from
the raw orbit tail identification and raw orientation row.  The final sector
rows are obtained through the local-sector incident-completeness bridge. -/
noncomputable def
    S2_agent_20260520_boundarySectorRows_of_rawOrbit_localSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    {start : UnitDistanceDart C}
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
    (repeated_tail_rows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RepeatedExteriorBoundarySeparationRows C
            (fun k : Fin O.period => (O.dart k).tail) i j)
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
  classical
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
  let frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1 :=
    (S2_agent_selected_raw_orbit_frontier_and_tail_coverage_source_no_edgeRows
      (C := C) (inputs := inputs) localSectorRows carrier_connected O
      dart_edge_openSegment_frontier).2
  let frontier_iff_tail :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin O.period => (O.dart k).tail = v :=
    rawFaceSuccOrbit_frontier_iff_tail_of_frontier_vertex_tail_coverage
      O edge_openSegment_frontier frontier_vertex_tail_coverage
  let period_ge_three : 3 <= O.period :=
    rawFaceSuccOrbit_period_three_le_of_edge_openSegment_frontier_tail_coverage_localSectorRows
      (inputs := inputs) O edge_openSegment_frontier
      frontier_vertex_tail_coverage localSectorRows
  let hB :=
    exists_unitDistanceCycleBoundary_of_rawFaceSuccOrbit_tail_injective
      O period_ge_three
      (rawFaceSuccOrbit_tail_injective_of_noCutVertex
        (inputs := inputs) O repeated_tail_rows)
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose hB
  let hperiod : B.length = O.period :=
    Classical.choose (Classical.choose_spec hB)
  let tail_eq :
      forall k : Fin B.length,
        (O.dart (Fin.cast hperiod k)).tail = B.vertex k :=
    Classical.choose_spec (Classical.choose_spec hB)
  let actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
    ActualBoundaryCycleFrontierEquivalenceRows.ofRawFaceSuccOrbitBoundaryRows
      (inputs := inputs) O B hperiod tail_eq frontier_iff_tail
      edge_openSegment_frontier
  let faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary := by
    simpa [actualRows] using
      rawFaceSuccOrbit_unitDistanceCycleFaceSuccRows_of_tail_eq
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
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k)) := by
    simpa [actualRows] using
      ActualBoundaryCycleFrontierEquivalenceRows.boundary_orientation_of_rawFaceSuccOrbitBoundaryRows
        (inputs := inputs) O B hperiod tail_eq frontier_iff_tail
        edge_openSegment_frontier raw_orientation
  exact
    S2_agent_20260520_boundarySectorRows_of_actualBoundaryRows_localSectorRows_faceSuccOrientation
      (C := C) (inputs := inputs) actualRows localSectorRows
      faceSuccRows boundary_orientation

/-- Final S2 row from the same raw-orbit edge-coverage plus cut-row handoff. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_rawOrbitCoverage_boundaryFree_noThirdGermCutRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {start : UnitDistanceDart C}
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
    (edge_coverage :
      forall e :
          {e : PlanarInterface.Edge n //
            e ∈ unboundedFrontierEdgeSet C inputs},
        Exists fun k : Fin O.period =>
          e.1 =
              ((O.dart k).tail,
                (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
            e.1 =
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
                (O.dart k).tail))
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
                            False)
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
    (S2_actualBoundaryCycleFrontierEquivalenceRows_of_rawOrbitCoverage_boundaryFree_noThirdGermCutRows
      (C := C) (inputs := inputs) O dart_edge_openSegment_frontier
      edge_coverage source cutRows)

/-- Actual-arc S2 assembly from the boundary-free local source and selected
raw-tail coverage.

This bypasses a separate frontier-preconnectedness input: raw-tail coverage
and local two-germ rows provide the carrier edge coverage used by the existing
tail-coverage reducer. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_boundaryFree_noThirdGermTailCoverage
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
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
                            False)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
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
    (actualArcRows :
      RawFaceSuccOrbitActualExteriorArcSeparationRows
        (inputs := inputs) O) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_agent_input_s2_assembly_gap_reducer_rawOrbitActualArcRows_of_tailCoverage
    inputs
    (localSectorRows_of_localTwoGermRows
      (S2_localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
        (C := C) (inputs := inputs) source))
    edgeRows htail hhead O frontier_vertex_tail_coverage
    dart_edge_openSegment_frontier actualArcRows

/-- Source-facing actual-arc assembly from the boundary-free no-third-germ
family and direct connectedness of the honest unbounded-frontier carrier.

This is the shorter source surface when connectedness is proved through the
actual carrier instead of first turning it into frontier preconnectedness. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_noThirdGermActualArcRows_carrierConnected
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    (left right :
      {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} -> Fin n)
    (left_edge :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, left a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (left a, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (right_edge :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        (a.1, right a) ∈ unboundedFrontierEdgeSet C inputs ∨
          (right a, a.1) ∈ unboundedFrontierEdgeSet C inputs)
    (heads_ne :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        left a ≠ right a)
    (no_third_germ :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
        (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ left a ->
                    x ≠ right a ->
                      False)
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
  S2_agent_input_s2_assembly_gap_reducer_actualArcRows_of_carrierConnected
    inputs
    (localSectorRows_of_localTwoGermRows
      (S2_localTwoGermRows_of_noThirdGermFamily
        left right left_edge right_edge heads_ne no_third_germ))
    carrier_connected edgeRows htail hhead O actualArcRows

/-- Carrier-connected assembly from the two minimal actual-arc source rows.

This is the eraser form for the raw-orbit actual-arc route: the only
orbit-specific inputs are selected raw edge membership and pairwise
repeated-tail actual exterior arc rows. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_edgeMemRepeatedActualArcRows_carrierConnected
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (edge_mem :
      forall k : Fin O.period,
        ((O.dart k).tail,
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∈
            unboundedFrontierEdgeSet C inputs ∨
          ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
              (O.dart k).tail) ∈
            unboundedFrontierEdgeSet C inputs)
    (repeated_tail_arcRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
            (inputs := inputs) O i j) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_agent_input_s2_assembly_gap_reducer_actualArcRows_of_carrierConnected
    inputs localSectorRows carrier_connected edgeRows htail hhead O
    (S2_agent_actual_arc_rows_source
      (inputs := inputs) O edge_mem repeated_tail_arcRows)

/-- Carrier-connected assembly with the repeated-tail residual stated in the
older finite boundary-arc separation language.

This is the same selected raw-orbit route as
`S2_unboundedExteriorFrontierCycleRows_of_edgeMemRepeatedActualArcRows_carrierConnected`,
but it exposes `RepeatedExteriorBoundaryArcSeparationRows` to the next source
proof instead of requiring the newer actual-arc wrapper. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_edgeMemRepeatedBoundaryArcRows_carrierConnected
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (edge_mem :
      forall k : Fin O.period,
        ((O.dart k).tail,
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∈
            unboundedFrontierEdgeSet C inputs ∨
          ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
              (O.dart k).tail) ∈
            unboundedFrontierEdgeSet C inputs)
    (repeated_tail_arcRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RepeatedExteriorBoundaryArcSeparationRows C
            (fun k : Fin O.period => (O.dart k).tail) i j) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_of_edgeMemRepeatedActualArcRows_carrierConnected
    inputs localSectorRows carrier_connected edgeRows htail hhead O edge_mem
    (fun hij htail_repeat =>
      RawFaceSuccOrbitRepeatedTailActualExteriorArcRows.ofRepeatedExteriorBoundaryArcSeparationRows
        (inputs := inputs) (O := O)
        (repeated_tail_arcRows hij htail_repeat))

/-- Carrier-connected assembly with repeated tails reduced to the no-cut
boundary-separation row.

This row-level variant matches the family-level selected route in
`S2SeededRawOrbitSource`: a repeated selected raw tail would produce a concrete
cut partition, contradicting `inputs.noCutVertex`, so the actual-arc callback
is discharged from `RepeatedExteriorBoundarySeparationRows`. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_edgeMemRepeatedBoundarySeparationRows_carrierConnected
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
    {start : UnitDistanceDart C}
    (edgeRows : UnboundedExteriorFrontierEdgeLocalRows C inputs e p)
    (htail : start.tail = e.1)
    (hhead : start.head = e.2)
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        start)
    (edge_mem :
      forall k : Fin O.period,
        ((O.dart k).tail,
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∈
            unboundedFrontierEdgeSet C inputs ∨
          ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
              (O.dart k).tail) ∈
            unboundedFrontierEdgeSet C inputs)
    (repeated_tail_rows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RepeatedExteriorBoundarySeparationRows C
            (fun k : Fin O.period => (O.dart k).tail) i j) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_of_edgeMemRepeatedActualArcRows_carrierConnected
    inputs localSectorRows carrier_connected edgeRows htail hhead O edge_mem
    (fun hij htail_repeat =>
      False.elim
        (inputs.noCutVertex
          ⟨(repeated_tail_rows hij htail_repeat).toCutVertexPartition⟩))

/-- Cut-row analogue of
`S2_unboundedExteriorFrontierCycleRows_of_noThirdGermActualArcRows_carrierConnected`.

This is the minimal source-facing raw-orbit assembly when the repeated-tail
separation proof is supplied only in the weaker cut-row form; the per-dart
open-segment frontier row is then supplied separately. -/
noncomputable def
    S2_unboundedExteriorFrontierCycleRows_of_boundaryFree_noThirdGermCutRows_carrierConnected
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
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
                            False)
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
          RawFaceSuccOrbitRepeatedTailExteriorCutRows (inputs := inputs) O i j) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  S2_rawOrbitCutRows_of_carrierConnected_localTwoGermRows
    inputs
    (S2_localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
      (C := C) (inputs := inputs) source)
    carrier_connected edgeRows htail hhead O dart_edge_openSegment_frontier
    cutRows

set_option linter.style.longLine false in
/-- Claim `S2-dyn-20260520-faceSucc-orientation-source`.

For an actual exterior boundary cycle, genuine adjacent rows in the sorted
geometric boundary rotation lists strictly supply both remaining orientation
outputs for the boundary-sector route: the concrete geometric `faceSucc`
cycle rows and the ordinary predecessor-before-successor boundary orientation
inequalities. -/
theorem
    S2_dyn_20260520_faceSucc_orientation_source_of_actualBoundary_geometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (geometricOrderRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C actualRows.boundary k) :
    UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary ∧
      (forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicPred actualRows.boundary.length_pos k)) <
        GeometricRotationSystem.graphDartArg
            (GeometricRotationSystem.canonicalGeometricGraph C)
            (actualRows.boundary.vertex k)
            (actualRows.boundary.vertex
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k))) :=
  ⟨GeometricRotationSystem.unitDistanceCycleFaceSuccRows_of_geometric_boundary_list_successors
      C actualRows.boundary
      (GeometricRotationSystem.geometricBoundarySuccessorRows_of_boundaryVertexGeometricRotationOrderRows
        C actualRows.boundary geometricOrderRows),
    fun k =>
      (GeometricRotationSystem.boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRows
        C actualRows.boundary geometricOrderRows k).angle⟩

set_option linter.style.longLine false in
/-- Actual exterior-sector rows on a concrete exterior boundary source the
honest face-dart exterior carrier rows.

The carrier boundary is the same boundary `B`; the consecutive carrier sides
remain actual `unboundedFrontierEdgeSet` edges through the sector rows, and
the face-orbit package keeps the corresponding edge-open-segment frontier
field. -/
noncomputable def
    S2_codex_current_20260520_face_dart_orbit_carrier_source_of_actualExteriorSectorInputSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v)
    (rows : ActualExteriorSectorInputSourceRows inputs B) :
    FaceDartOrbitExteriorCarrierRows C inputs :=
  faceDartOrbitExteriorCarrierRows_of_actualExteriorSectorInputSourceRows
    (C := C) (inputs := inputs) B frontier_iff_cycle_vertex rows

set_option linter.style.longLine false in
/-- Claim `S2-codex-current-20260520-face-dart-orbit-carrier-source`.

Sharp actual-boundary source for the honest face-dart exterior carrier rows.
The face walk is the genuine geometric boundary successor walk on
`actualRows.boundary`, while the carrier edge rows and open-segment-frontier
data are read from `actualRows` and the same-boundary incident-completeness
row.  The remaining source is exactly the sorted geometric boundary-order row
and `BoundaryCycleIncidentFrontierEdgeCompleteness` for this actual boundary. -/
noncomputable def
    S2_codex_current_20260520_face_dart_orbit_carrier_source_of_actualBoundary_geometricOrderRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs)
    (geometricOrderRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C actualRows.boundary k)
    (incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary) :
    FaceDartOrbitExteriorCarrierRows C inputs :=
  let faceRowsAndOrientation :=
    S2_dyn_20260520_faceSucc_orientation_source_of_actualBoundary_geometricOrderRows
      (C := C) (inputs := inputs) actualRows geometricOrderRows
  S2_codex_current_20260520_actual_boundary_cycle_source
    (C := C) (inputs := inputs)
    (R := GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
    actualRows faceRowsAndOrientation.1 incident_complete

set_option linter.style.longLine false in
/-- Raw-orbit/local-sector reduction of the exact source required by
`S2_codex_current_20260520_face_dart_orbit_carrier_source`.

The actual boundary is extracted from the selected geometric raw face-successor
orbit by repeated-tail separation.  The geometric order rows are then obtained
from the genuine raw-orbit face-successor rows together with the ordinary
predecessor-before-successor raw orientation row, and incident completeness is
the existing same-boundary local-sector bridge. -/
noncomputable def
    S2_codex_current_20260520_actualBoundary_geometricOrder_incident_source_of_rawOrbit_localSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    {start : UnitDistanceDart C}
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
    (repeated_tail_rows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RepeatedExteriorBoundarySeparationRows C
            (fun k : Fin O.period => (O.dart k).tail) i j)
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
    Exists fun actualRows :
        ActualBoundaryCycleFrontierEquivalenceRows C inputs =>
      (forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C actualRows.boundary k) ∧
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary := by
  classical
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
  let frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1 :=
    (S2_agent_selected_raw_orbit_frontier_and_tail_coverage_source_no_edgeRows
      (C := C) (inputs := inputs) localSectorRows carrier_connected O
      dart_edge_openSegment_frontier).2
  let frontier_iff_tail :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin O.period => (O.dart k).tail = v :=
    rawFaceSuccOrbit_frontier_iff_tail_of_frontier_vertex_tail_coverage
      O edge_openSegment_frontier frontier_vertex_tail_coverage
  let period_ge_three : 3 <= O.period :=
    rawFaceSuccOrbit_period_three_le_of_edge_openSegment_frontier_tail_coverage_localSectorRows
      (inputs := inputs) O edge_openSegment_frontier
      frontier_vertex_tail_coverage localSectorRows
  let hB :=
    exists_unitDistanceCycleBoundary_of_rawFaceSuccOrbit_tail_injective
      O period_ge_three
      (rawFaceSuccOrbit_tail_injective_of_noCutVertex
        (inputs := inputs) O repeated_tail_rows)
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose hB
  let hperiod : B.length = O.period :=
    Classical.choose (Classical.choose_spec hB)
  let tail_eq :
      forall k : Fin B.length,
        (O.dart (Fin.cast hperiod k)).tail = B.vertex k :=
    Classical.choose_spec (Classical.choose_spec hB)
  let actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
    ActualBoundaryCycleFrontierEquivalenceRows.ofRawFaceSuccOrbitBoundaryRows
      (inputs := inputs) O B hperiod tail_eq frontier_iff_tail
      edge_openSegment_frontier
  let faceSuccRows :
      UnitDistanceCycleFaceSuccRows C
        (GeometricRotationSystem.geometricUnitDistanceRotationSystem C)
        actualRows.boundary := by
    simpa [actualRows] using
      rawFaceSuccOrbit_unitDistanceCycleFaceSuccRows_of_tail_eq
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
              (PlanarInterface.cyclicSucc actualRows.boundary.length_pos k)) := by
    simpa [actualRows] using
      ActualBoundaryCycleFrontierEquivalenceRows.boundary_orientation_of_rawFaceSuccOrbitBoundaryRows
        (inputs := inputs) O B hperiod tail_eq frontier_iff_tail
        edge_openSegment_frontier raw_orientation
  let geometricOrderRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C actualRows.boundary k :=
    GeometricRotationSystem.S2_agent_geometric_boundary_order_source_of_pred_arg_lt_succ_arg
      C actualRows.boundary faceSuccRows boundary_orientation
  let incident_complete :
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary :=
    S2_agent_local_sector_incident_bridge
      (C := C) (inputs := inputs) actualRows localSectorRows
  exact ⟨actualRows, geometricOrderRows, incident_complete⟩

set_option linter.style.longLine false in
/-- Direct raw-orbit/local-sector form of the honest face-dart exterior carrier
source.

This is just the preceding exact source reducer followed by the checked
actual-boundary carrier constructor.  The edge-open-segment frontier data stays
the raw orbit's genuine dart frontier row. -/
noncomputable def
    S2_codex_current_20260520_face_dart_orbit_carrier_source_of_rawOrbit_localSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (carrier_connected :
      (unboundedFrontierCarrierGraph C inputs).Connected)
    {start : UnitDistanceDart C}
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
    (repeated_tail_rows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RepeatedExteriorBoundarySeparationRows C
            (fun k : Fin O.period => (O.dart k).tail) i j)
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
    FaceDartOrbitExteriorCarrierRows C inputs := by
  classical
  let source :=
    S2_codex_current_20260520_actualBoundary_geometricOrder_incident_source_of_rawOrbit_localSectorRows
      (C := C) inputs localSectorRows carrier_connected O
      dart_edge_openSegment_frontier repeated_tail_rows raw_orientation
  let actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
    Classical.choose source
  have hsource :
      (forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C actualRows.boundary k) ∧
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary :=
    Classical.choose_spec source
  exact
    S2_codex_current_20260520_face_dart_orbit_carrier_source_of_actualBoundary_geometricOrderRows
      (C := C) (inputs := inputs) actualRows hsource.1 hsource.2

set_option linter.style.longLine false in
/-- Family form of
`S2_codex_current_20260520_face_dart_orbit_carrier_source_of_actualBoundary_geometricOrderRows`.

This exposes the smallest current source surface for this owned route:
construct the actual exterior boundary/frontier equivalence row, prove genuine
geometric boundary-order rows on that boundary, and prove incident frontier-edge
completeness for the same boundary. -/
noncomputable def
    S2_codex_current_20260520_face_dart_orbit_carrier_source
    (source :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun actualRows :
              ActualBoundaryCycleFrontierEquivalenceRows C inputs =>
            (forall k : Fin actualRows.boundary.length,
              GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
                C actualRows.boundary k) ∧
            BoundaryCycleIncidentFrontierEdgeCompleteness inputs
              actualRows.boundary) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (inputs : FinitePlanarOuterComponentInputs C),
        FaceDartOrbitExteriorCarrierRows C inputs := by
  intro n C inputs
  classical
  let actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
    Classical.choose (source C inputs)
  have hsource :
      (forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C actualRows.boundary k) ∧
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary :=
    Classical.choose_spec (source C inputs)
  exact
    S2_codex_current_20260520_face_dart_orbit_carrier_source_of_actualBoundary_geometricOrderRows
      (C := C) (inputs := inputs) actualRows hsource.1 hsource.2

end ExteriorComponentTopology
end Swanepoel
end ErdosProblems1066
