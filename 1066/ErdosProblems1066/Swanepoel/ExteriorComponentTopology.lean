import ErdosProblems1066.Swanepoel.FinitePlaneDrawing
import ErdosProblems1066.Swanepoel.JordanTopologyExteriorEnclosure
import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false

/-!
# Exterior component topology rows for S2

This file records the next honest S2 reduction after the finite drawing layer:
once an exterior component of the complement of the embedded unit-edge drawing
has a frontier carried by a selected unit-distance cycle, the off-cycle
not-in-exterior row is automatic for all graph vertices.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ExteriorComponentTopology

open JordanTopologyFactsConcrete
open JordanTopologyFactsConcrete.MinimalFailureTopology
open FinitePlaneDrawing
open JordanTopologyExteriorEnclosure

noncomputable section

universe u

variable {n : Nat}

section FiniteTwoRegularGraph

variable {V : Type u} [Fintype V]

theorem isCycles_of_degree_eq_two
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (hdegree_two : forall v : V, F.degree v = 2) :
    F.IsCycles := by
  intro v _hv
  rw [show (F.neighborSet v).ncard = F.degree v by
    rw [Set.ncard_eq_toFinset_card]
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset]]
  exact hdegree_two v

theorem connected_two_regular_spanning_cycle
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (hconn : F.Connected)
    (hdegree_two : forall v : V, F.degree v = 2) :
    Exists fun base : V =>
      Exists fun w : F.Walk base base =>
        And w.IsCycle (forall v : V, Set.Mem w.toSubgraph.verts v) := by
  classical
  have hcycF : F.IsCycles :=
    isCycles_of_degree_eq_two F hdegree_two
  cases hconn.nonempty with
  | intro v0 =>
    have hnv0 : (F.neighborSet v0).Nonempty := by
      have hdeg : F.degree v0 = 2 := hdegree_two v0
      rw [SimpleGraph.degree] at hdeg
      have hcardpos : 0 < (F.neighborFinset v0).card := by omega
      cases Finset.card_pos.mp hcardpos with
      | intro w hw =>
        exact Exists.intro w (by simpa [SimpleGraph.neighborFinset] using hw)
    let c : F.ConnectedComponent := F.connectedComponentMk v0
    have hv0c : Set.Mem c.supp v0 :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c v0).2 rfl
    cases hcycF.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
        (c := c) (v := v0) hv0c hnv0 with
    | intro p hp =>
      cases hp with
      | intro hpcycle hpverts =>
        exact Exists.intro v0 (Exists.intro p (And.intro hpcycle (by
          intro v
          have hvc : Set.Mem c.supp v :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff c v).2
              ((SimpleGraph.ConnectedComponent.eq (G := F)).2
                (hconn.preconnected v v0))
          rw [hpverts]
          exact hvc)))

/-- Map a spanning finite graph cycle injectively into the unit-distance graph
of a `UDConfig`, producing the concrete cycle-boundary object used by the S2
topology rows. -/
theorem exists_unitDistanceCycleBoundary_covering_spanning_cycle_hom
    {C : _root_.UDConfig n}
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (phi : SimpleGraph.Hom F (GraphBridge.unitDistanceSimpleGraph C))
    (hphi : Function.Injective phi)
    (hspan : Exists fun base : V =>
      Exists fun w : F.Walk base base =>
        And w.IsCycle (forall v : V, Set.Mem w.toSubgraph.verts v)) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      And (forall v : V, Exists fun k : Fin B.length => B.vertex k = phi v)
        (forall k : Fin B.length, Exists fun v : V => B.vertex k = phi v) := by
  classical
  cases hspan with
  | intro base hbase =>
    cases hbase with
    | intro w hw =>
      cases hw with
      | intro hwcycle hwspan =>
        let mapped :
            (GraphBridge.unitDistanceSimpleGraph C).Walk (phi base) (phi base) :=
          w.map phi
        have hmapped_cycle : mapped.IsCycle := by
          dsimp [mapped]
          exact hwcycle.map hphi
        let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C := {
          base := phi base
          walk := mapped
          isCycle := hmapped_cycle
        }
        refine Exists.intro B ?_
        constructor
        case left =>
          intro v
          have hvset : Set.Mem w.toSubgraph.verts v := hwspan v
          have hvlist : List.Mem v w.support :=
            (w.mem_verts_toSubgraph).1 hvset
          have hex := (SimpleGraph.Walk.mem_support_iff_exists_getVert).1 hvlist
          cases hex with
          | intro m hmAll =>
            cases hmAll with
            | intro hm hmle =>
              by_cases hmlt : m < w.length
              case pos =>
                let k : Fin B.length := Fin.mk m (by
                  simpa [B, JordanBoundaryConcrete.UnitDistanceCycleBoundary.length,
                    mapped, SimpleGraph.Walk.length_map] using hmlt)
                refine Exists.intro k ?_
                simp [k, B, JordanBoundaryConcrete.UnitDistanceCycleBoundary.vertex,
                  mapped, SimpleGraph.Walk.getVert_map, hm]
              case neg =>
                have hm_eq_len : m = w.length := by omega
                let k : Fin B.length := Fin.mk 0 (by
                  have hpos : 0 < B.length := B.length_pos
                  simpa using hpos)
                refine Exists.intro k ?_
                have hbase : w.getVert m = base := by
                  rw [hm_eq_len, SimpleGraph.Walk.getVert_length]
                have hvbase : v = base := by
                  simpa [hbase] using hm.symm
                simp [k, B, JordanBoundaryConcrete.UnitDistanceCycleBoundary.vertex,
                  mapped, hvbase]
        case right =>
          intro k
          refine Exists.intro (w.getVert k.val) ?_
          simp [B, JordanBoundaryConcrete.UnitDistanceCycleBoundary.vertex,
            mapped, SimpleGraph.Walk.getVert_map]

/-- One-direction projection of
`exists_unitDistanceCycleBoundary_covering_spanning_cycle_hom`. -/
theorem exists_unitDistanceCycleBoundary_of_spanning_cycle_hom
    {C : _root_.UDConfig n}
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (phi : SimpleGraph.Hom F (GraphBridge.unitDistanceSimpleGraph C))
    (hphi : Function.Injective phi)
    (hspan : Exists fun base : V =>
      Exists fun w : F.Walk base base =>
        And w.IsCycle (forall v : V, Set.Mem w.toSubgraph.verts v)) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      forall v : V, Exists fun k : Fin B.length => B.vertex k = phi v := by
  cases exists_unitDistanceCycleBoundary_covering_spanning_cycle_hom
      F phi hphi hspan with
  | intro B hB =>
    exact Exists.intro B hB.left

/-- A connected finite two-regular frontier graph whose vertices inject into
the unit-distance graph yields a concrete unit-distance cycle boundary
covering every frontier vertex. -/
theorem exists_unitDistanceCycleBoundary_of_connected_two_regular_hom
    {C : _root_.UDConfig n}
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (hconn : F.Connected)
    (hdegree_two : forall v : V, F.degree v = 2)
    (phi : SimpleGraph.Hom F (GraphBridge.unitDistanceSimpleGraph C))
    (hphi : Function.Injective phi) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      forall v : V, Exists fun k : Fin B.length => B.vertex k = phi v :=
  exists_unitDistanceCycleBoundary_of_spanning_cycle_hom
    F phi hphi (connected_two_regular_spanning_cycle F hconn hdegree_two)

end FiniteTwoRegularGraph

section ComponentFrontier

variable {α : Type u} [TopologicalSpace α] [LocallyConnectedSpace α]

/-- A point on the frontier of an open-set connected component cannot still
lie in the ambient open set.  Otherwise the ambient component of that point is
an open neighborhood meeting the selected component, hence the same component,
contradicting `IsOpen.inter_frontier_eq`. -/
theorem not_mem_open_of_mem_frontier_connectedComponentIn
    {U : Set α} {x y : α} (hU : IsOpen U)
    (hy : y ∈ frontier (connectedComponentIn U x)) :
    y ∉ U := by
  intro hyU
  let E : Set α := connectedComponentIn U x
  let Ey : Set α := connectedComponentIn U y
  have hEopen : IsOpen E := hU.connectedComponentIn
  have hEyopen : IsOpen Ey := hU.connectedComponentIn
  have hy_closureE : y ∈ closure E := frontier_subset_closure hy
  have hyEy : y ∈ Ey := mem_connectedComponentIn hyU
  have hEy_inter_E : (Ey ∩ E).Nonempty :=
    (mem_closure_iff.mp hy_closureE) Ey hEyopen hyEy
  rcases hEy_inter_E with ⟨z, hzEy, hzE⟩
  have hExz : connectedComponentIn U x = connectedComponentIn U z :=
    connectedComponentIn_eq hzE
  have hEyz : connectedComponentIn U y = connectedComponentIn U z :=
    connectedComponentIn_eq hzEy
  have hEy_eq_E : Ey = E := by
    dsimp [Ey, E]
    exact hEyz.trans hExz.symm
  have hyE : y ∈ E := by
    simpa [hEy_eq_E] using hyEy
  have hmem : y ∈ E ∩ frontier E := ⟨hyE, hy⟩
  have hdisj : E ∩ frontier E = ∅ := hEopen.inter_frontier_eq
  rw [hdisj] at hmem
  exact hmem

/-- The frontier of an open-set connected component lies in the frontier of
the ambient open set. -/
theorem frontier_connectedComponentIn_subset_frontier
    {U : Set α} {x : α} (hU : IsOpen U) :
    frontier (connectedComponentIn U x) ⊆ frontier U := by
  intro y hy
  rw [hU.frontier_eq]
  exact
    ⟨closure_mono (connectedComponentIn_subset U x)
        (frontier_subset_closure hy),
      not_mem_open_of_mem_frontier_connectedComponentIn hU hy⟩

end ComponentFrontier

/-- A candidate exterior set lies in the complement of the embedded drawing. -/
structure ExteriorComponentRows
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) where
  exterior : Set PlanarInterface.Point
  exterior_subset_drawingComplement :
    exterior ⊆ drawingComplement C
  exterior_open : IsOpen exterior

/-- The whole complement of the finite drawing is always an open exterior
candidate.  The remaining S2 theorem must select its unbounded component and
identify the simple unit-distance cycle on that component's frontier. -/
def drawingComplementRows
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    ExteriorComponentRows C inputs where
  exterior := drawingComplement C
  exterior_subset_drawingComplement := fun _ hp => hp
  exterior_open := drawingComplement_open C

/-- A component-level exterior candidate obtained by choosing a base point in
the drawing complement.  The true S2 proof must choose the unbounded such
component and identify its frontier cycle. -/
structure ExteriorConnectedComponentRows
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) where
  base : PlanarInterface.Point
  base_mem_drawingComplement : base ∈ drawingComplement C

namespace ExteriorConnectedComponentRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

/-- The selected connected component of the drawing complement. -/
def exterior (E : ExteriorConnectedComponentRows C inputs) :
    Set PlanarInterface.Point :=
  connectedComponentIn (drawingComplement C) E.base

theorem exterior_subset_drawingComplement
    (E : ExteriorConnectedComponentRows C inputs) :
    E.exterior ⊆ drawingComplement C :=
  connectedComponentIn_subset (drawingComplement C) E.base

theorem exterior_open
    (E : ExteriorConnectedComponentRows C inputs) :
    IsOpen E.exterior :=
  (drawingComplement_open C).connectedComponentIn

theorem base_mem_exterior
    (E : ExteriorConnectedComponentRows C inputs) :
    E.base ∈ E.exterior :=
  mem_connectedComponentIn E.base_mem_drawingComplement

/-- A selected complement component is preconnected by construction. -/
theorem exterior_preconnected
    (E : ExteriorConnectedComponentRows C inputs) :
    IsPreconnected E.exterior :=
  isPreconnected_connectedComponentIn

/-- A selected complement component is connected when its base point lies in
the drawing complement. -/
theorem exterior_connected
    (E : ExteriorConnectedComponentRows C inputs) :
    IsConnected E.exterior :=
  isConnected_connectedComponentIn_iff.mpr E.base_mem_drawingComplement

/-- The frontier of a selected complement component is carried by the embedded
unit-edge drawing.  The remaining S2 theorem must identify which drawing
vertices on this frontier form the outer cycle. -/
theorem frontier_subset_embeddedEdgeSet
    (E : ExteriorConnectedComponentRows C inputs) :
    frontier E.exterior ⊆ embeddedEdgeSet C := by
  intro p hp
  exact
    frontier_drawingComplement_subset_embeddedEdgeSet C
      (frontier_connectedComponentIn_subset_frontier
        (drawingComplement_open C) hp)

theorem frontier_graph_vertex_mem_embeddedEdgeSet
    (E : ExteriorConnectedComponentRows C inputs)
    {v : Fin n}
    (hv : (canonicalGraph C).point v ∈ frontier E.exterior) :
    (canonicalGraph C).point v ∈ embeddedEdgeSet C :=
  E.frontier_subset_embeddedEdgeSet hv

theorem frontier_graph_vertex_incident
    (E : ExteriorConnectedComponentRows C inputs)
    {v : Fin n}
    (hv : (canonicalGraph C).point v ∈ frontier E.exterior) :
    Exists fun w : Fin n => (canonicalGraph C).Adj v w := by
  exact
    graph_vertex_mem_embeddedEdgeSet_iff_exists_adj.1
      (E.frontier_graph_vertex_mem_embeddedEdgeSet hv)

theorem frontier_not_mem_exterior
    (E : ExteriorConnectedComponentRows C inputs)
    {p : PlanarInterface.Point}
    (hp : p ∈ frontier E.exterior) :
    p ∉ E.exterior := by
  have hp_not_complement : p ∉ drawingComplement C :=
    not_mem_open_of_mem_frontier_connectedComponentIn
      (drawingComplement_open C)
      (by simpa [ExteriorConnectedComponentRows.exterior] using hp)
  intro hpE
  exact hp_not_complement (E.exterior_subset_drawingComplement hpE)

theorem graph_vertex_not_mem_exterior
    (E : ExteriorConnectedComponentRows C inputs) :
    forall v : Fin n, (canonicalGraph C).point v ∉ E.exterior := by
  intro v hv
  have hnot :
      (canonicalGraph C).point v ∉ embeddedEdgeSet C := by
    simpa [drawingComplement] using E.exterior_subset_drawingComplement hv
  exact hnot (vertex_mem_embeddedEdgeSet_of_inputs inputs v)

/-- Forget a connected-component exterior candidate to the weaker exterior-row
interface consumed by the current S2 reducer. -/
def toExteriorComponentRows
    (E : ExteriorConnectedComponentRows C inputs) :
    ExteriorComponentRows C inputs where
  exterior := E.exterior
  exterior_subset_drawingComplement := E.exterior_subset_drawingComplement
  exterior_open := E.exterior_open

end ExteriorConnectedComponentRows

/-- A canonical complement-component candidate obtained from an arbitrary point
outside the compact embedded drawing.  The remaining planar theorem must show
which connected component is the unbounded exterior component and identify its
frontier cycle. -/
noncomputable def defaultExteriorConnectedComponentRows
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    ExteriorConnectedComponentRows C inputs where
  base := Classical.choose (drawingComplement_nonempty C)
  base_mem_drawingComplement := Classical.choose_spec (drawingComplement_nonempty C)

noncomputable def defaultExteriorComponentRows
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    ExteriorComponentRows C inputs :=
  (defaultExteriorConnectedComponentRows C inputs).toExteriorComponentRows

/-- A selected connected component of the drawing complement that is certified
to be unbounded.  This is the component-level exterior object needed before
the final plane-graph theorem identifies the boundary cycle on its frontier. -/
structure ExteriorUnboundedComponentRows
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) where
  component : ExteriorConnectedComponentRows C inputs
  exterior_unbounded : ¬ Bornology.IsBounded component.exterior

namespace ExteriorUnboundedComponentRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

def exterior (E : ExteriorUnboundedComponentRows C inputs) :
    Set PlanarInterface.Point :=
  E.component.exterior

theorem exterior_subset_drawingComplement
    (E : ExteriorUnboundedComponentRows C inputs) :
    E.exterior ⊆ drawingComplement C :=
  E.component.exterior_subset_drawingComplement

theorem exterior_open
    (E : ExteriorUnboundedComponentRows C inputs) :
    IsOpen E.exterior :=
  E.component.exterior_open

theorem frontier_subset_embeddedEdgeSet
    (E : ExteriorUnboundedComponentRows C inputs) :
    frontier E.exterior ⊆ embeddedEdgeSet C :=
  E.component.frontier_subset_embeddedEdgeSet

theorem frontier_graph_vertex_mem_embeddedEdgeSet
    (E : ExteriorUnboundedComponentRows C inputs)
    {v : Fin n}
    (hv : (canonicalGraph C).point v ∈ frontier E.exterior) :
    (canonicalGraph C).point v ∈ embeddedEdgeSet C :=
  E.frontier_subset_embeddedEdgeSet hv

theorem frontier_graph_vertex_incident
    (E : ExteriorUnboundedComponentRows C inputs)
    {v : Fin n}
    (hv : (canonicalGraph C).point v ∈ frontier E.exterior) :
    Exists fun w : Fin n => (canonicalGraph C).Adj v w := by
  exact
    graph_vertex_mem_embeddedEdgeSet_iff_exists_adj.1
      (E.frontier_graph_vertex_mem_embeddedEdgeSet hv)

theorem frontier_not_mem_exterior
    (E : ExteriorUnboundedComponentRows C inputs)
    {p : PlanarInterface.Point}
    (hp : p ∈ frontier E.exterior) :
    p ∉ E.exterior :=
  E.component.frontier_not_mem_exterior hp

theorem graph_vertex_not_mem_exterior
    (E : ExteriorUnboundedComponentRows C inputs) :
    forall v : Fin n, (canonicalGraph C).point v ∉ E.exterior :=
  E.component.graph_vertex_not_mem_exterior

def toExteriorComponentRows
    (E : ExteriorUnboundedComponentRows C inputs) :
    ExteriorComponentRows C inputs :=
  E.component.toExteriorComponentRows

end ExteriorUnboundedComponentRows

/-- The finite embedded drawing has a concrete unbounded complement component:
take a rightward x-axis ray outside a compact ball containing the drawing, and
then take the complement component containing that ray. -/
noncomputable def unboundedExteriorComponentRows
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    ExteriorUnboundedComponentRows C inputs := by
  classical
  let R : Real := Classical.choose (exists_xAxisRay_subset_drawingComplement C)
  have hR_spec : 0 <= R /\ xAxisRay R ⊆ drawingComplement C :=
    Classical.choose_spec (exists_xAxisRay_subset_drawingComplement C)
  have hR_subset : xAxisRay R ⊆ drawingComplement C := hR_spec.2
  let base : PlanarInterface.Point := (R + 1, 0)
  have hbase_ray : base ∈ xAxisRay R := by
    exact ⟨R + 1, by linarith, rfl⟩
  have hbase : base ∈ drawingComplement C := hR_subset hbase_ray
  let component : ExteriorConnectedComponentRows C inputs :=
    { base := base
      base_mem_drawingComplement := hbase }
  refine
    { component := component
      exterior_unbounded := ?_ }
  intro hbounded_component
  have hray_subset_component : xAxisRay R ⊆ component.exterior :=
    (xAxisRay_preconnected R).subset_connectedComponentIn hbase_ray hR_subset
  exact xAxisRay_unbounded R (hbounded_component.subset hray_subset_component)

theorem unboundedExteriorComponent_not_isBounded
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    ¬ Bornology.IsBounded (unboundedExteriorComponentRows C inputs).exterior :=
  (unboundedExteriorComponentRows C inputs).exterior_unbounded

theorem unboundedExteriorComponent_frontier_subset_embeddedEdgeSet
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    frontier (unboundedExteriorComponentRows C inputs).exterior ⊆
      embeddedEdgeSet C :=
  (unboundedExteriorComponentRows C inputs).frontier_subset_embeddedEdgeSet

theorem unboundedExterior_frontier_vertex_incident
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C)
    {v : Fin n}
    (hv :
      (canonicalGraph C).point v ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior) :
    Exists fun w : Fin n => (canonicalGraph C).Adj v w := by
  exact
    _root_.ErdosProblems1066.Swanepoel.FinitePlaneDrawing.graph_vertex_mem_embeddedEdgeSet_iff_exists_adj.1
      ((unboundedExteriorComponentRows C inputs).frontier_subset_embeddedEdgeSet hv)

/-- The exterior component of the drawing complement contains no graph vertex. -/
theorem graph_vertex_not_mem_exterior
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (E : ExteriorComponentRows C inputs) :
    forall v : Fin n, (canonicalGraph C).point v ∉ E.exterior := by
  intro v hv
  have hnot :
      (canonicalGraph C).point v ∉ embeddedEdgeSet C := by
    simpa [drawingComplement] using E.exterior_subset_drawingComplement hv
  exact hnot (vertex_mem_embeddedEdgeSet_of_inputs inputs v)

theorem graph_vertex_mem_closure_exterior_compl
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (E : ExteriorComponentRows C inputs) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ closure E.exteriorᶜ := by
  intro v
  exact
    mem_closure_compl_of_not_mem
      (graph_vertex_not_mem_exterior E v)

theorem graph_vertex_not_mem_unboundedExterior
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    forall v : Fin n,
      (canonicalGraph C).point v ∉
        (unboundedExteriorComponentRows C inputs).exterior :=
  (unboundedExteriorComponentRows C inputs).graph_vertex_not_mem_exterior

theorem graph_vertex_mem_closure_unboundedExterior_compl
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈
        closure (unboundedExteriorComponentRows C inputs).exteriorᶜ := by
  intro v
  exact
    mem_closure_compl_of_not_mem
      (graph_vertex_not_mem_unboundedExterior inputs v)

/-- The remaining exterior-cycle source after the drawing-complement row:
choose a unit-distance cycle whose vertices are exactly the graph vertices on
the exterior frontier. -/
structure ExteriorFrontierCycleRows
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C)
    extends ExteriorComponentRows C inputs where
  boundary : JordanBoundaryConcrete.UnitDistanceCycleBoundary C
  frontier_iff_cycle_vertex :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ frontier exterior <->
        Exists fun k : Fin boundary.length => boundary.vertex k = v

/-- The final S2 source shape after the unbounded exterior component is
selected: prove that the graph vertices on that component's frontier are
exactly the vertices of one simple unit-distance cycle. -/
structure UnboundedExteriorFrontierCycleRows
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) where
  unbounded : ExteriorUnboundedComponentRows C inputs
  boundary : JordanBoundaryConcrete.UnitDistanceCycleBoundary C
  frontier_iff_cycle_vertex :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ frontier unbounded.exterior <->
        Exists fun k : Fin boundary.length => boundary.vertex k = v

/-- Constructor form for the canonical unbounded component: after the finite
plane-graph theorem selects a simple unit-distance cycle and identifies the
graph vertices on this component's frontier, the S2 source rows are filled. -/
def unboundedExteriorFrontierCycleRowsOfBoundary
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior <->
          Exists fun k : Fin B.length => B.vertex k = v) :
    UnboundedExteriorFrontierCycleRows C inputs where
  unbounded := unboundedExteriorComponentRows C inputs
  boundary := B
  frontier_iff_cycle_vertex := frontier_iff_cycle_vertex

def unboundedExteriorFrontierCycleRowsOfBoundaryFrontierRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (frontier_vertices_are_cycle_vertices :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ->
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_vertices_frontier :
      forall k : Fin B.length,
        (canonicalGraph C).point (B.vertex k) ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsOfBoundary inputs B
    (frontier_iff_cycle_vertex_of_frontier_vertices_cycle_vertices
      B (unboundedExteriorComponentRows C inputs).exterior
      frontier_vertices_are_cycle_vertices cycle_vertices_frontier)

def unboundedExteriorFrontierCycleRowsOfBoundaryFrontierNotFrontierRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (cycle_vertices_frontier :
      forall k : Fin B.length,
        (canonicalGraph C).point (B.vertex k) ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior)
    (off_cycle_vertices_not_frontier :
      forall v : Fin n,
        (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
          (canonicalGraph C).point v ∉
            frontier (unboundedExteriorComponentRows C inputs).exterior) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsOfBoundary inputs B
    (frontier_iff_cycle_vertex_of_cycle_frontier_off_cycle_not_frontier
      B (unboundedExteriorComponentRows C inputs).exterior
      cycle_vertices_frontier off_cycle_vertices_not_frontier)

section FrontierGraphToRows

variable {V : Type u} [Fintype V]

/-- If the graph vertices on the unbounded exterior frontier are represented by
a finite connected two-regular graph whose edges map to unit-distance edges,
then the current S2 row surface is inhabited.  The remaining geometric work is
to construct this frontier graph and prove these hypotheses from the embedded
drawing. -/
noncomputable def unboundedExteriorFrontierCycleRows_of_connected_two_regular_frontier_graph
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (hconn : F.Connected)
    (hdegree_two : forall v : V, F.degree v = 2)
    (phi : SimpleGraph.Hom F (GraphBridge.unitDistanceSimpleGraph C))
    (hphi : Function.Injective phi)
    (hfrontier :
      forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior <->
          Exists fun x : V => phi x = v) :
    UnboundedExteriorFrontierCycleRows C inputs := by
  classical
  let hcycle :=
    exists_unitDistanceCycleBoundary_covering_spanning_cycle_hom
      F phi hphi
      (connected_two_regular_spanning_cycle F hconn hdegree_two)
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose hcycle
  have hB :
      (forall v : V, Exists fun k : Fin B.length => B.vertex k = phi v) /\
        (forall k : Fin B.length, Exists fun v : V => B.vertex k = phi v) :=
    Classical.choose_spec hcycle
  exact
    unboundedExteriorFrontierCycleRowsOfBoundary inputs B (by
      intro v
      constructor
      · intro hv
        cases (hfrontier v).1 hv with
        | intro x hx =>
          cases hB.left x with
          | intro k hk =>
            exact Exists.intro k (hk.trans hx)
      · intro hv
        cases hv with
        | intro k hk =>
          cases hB.right k with
          | intro x hx =>
            exact (hfrontier v).2
              (Exists.intro x (hx.symm.trans hk)))

end FrontierGraphToRows

namespace UnboundedExteriorFrontierCycleRows

variable {C : _root_.UDConfig n}
variable {inputs : FinitePlanarOuterComponentInputs C}

theorem graph_vertex_not_mem_exterior
    (rows : UnboundedExteriorFrontierCycleRows C inputs) :
    forall v : Fin n, (canonicalGraph C).point v ∉ rows.unbounded.exterior :=
  _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.graph_vertex_not_mem_exterior
    rows.unbounded.toExteriorComponentRows

theorem cycle_vertices_frontier
    (rows : UnboundedExteriorFrontierCycleRows C inputs) :
    forall k : Fin rows.boundary.length,
      (canonicalGraph C).point (rows.boundary.vertex k) ∈
        frontier rows.unbounded.exterior := by
  intro k
  exact (rows.frontier_iff_cycle_vertex (rows.boundary.vertex k)).2 ⟨k, rfl⟩

theorem frontier_vertices_are_cycle_vertices
    (rows : UnboundedExteriorFrontierCycleRows C inputs) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ frontier rows.unbounded.exterior ->
        Exists fun k : Fin rows.boundary.length =>
          rows.boundary.vertex k = v := by
  intro v hv
  exact (rows.frontier_iff_cycle_vertex v).1 hv

theorem off_cycle_vertices_not_frontier
    (rows : UnboundedExteriorFrontierCycleRows C inputs) :
    forall v : Fin n,
      (¬ Exists fun k : Fin rows.boundary.length =>
        rows.boundary.vertex k = v) ->
        (canonicalGraph C).point v ∉ frontier rows.unbounded.exterior := by
  intro v hv hfrontier
  exact hv ((rows.frontier_iff_cycle_vertex v).1 hfrontier)

theorem frontier_graph_vertex_incident
    (rows : UnboundedExteriorFrontierCycleRows C inputs)
    {v : Fin n}
    (hv : (canonicalGraph C).point v ∈ frontier rows.unbounded.exterior) :
    Exists fun w : Fin n => (canonicalGraph C).Adj v w :=
  rows.unbounded.frontier_graph_vertex_incident hv

theorem cycle_frontier_edge_rows
    (rows : UnboundedExteriorFrontierCycleRows C inputs) :
    forall k : Fin rows.boundary.length,
      (canonicalGraph C).Adj (rows.boundary.vertex k)
        (rows.boundary.vertex
          (PlanarInterface.cyclicSucc rows.boundary.length_pos k)) /\
      (canonicalGraph C).point (rows.boundary.vertex k) ∈
        frontier rows.unbounded.exterior /\
      (canonicalGraph C).point
          (rows.boundary.vertex
            (PlanarInterface.cyclicSucc rows.boundary.length_pos k)) ∈
        frontier rows.unbounded.exterior := by
  intro k
  exact
    ⟨rows.boundary.adjacent k,
      rows.cycle_vertices_frontier k,
      rows.cycle_vertices_frontier
        (PlanarInterface.cyclicSucc rows.boundary.length_pos k)⟩

theorem frontier_vertex_incident_cycle_edge
    (rows : UnboundedExteriorFrontierCycleRows C inputs) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ frontier rows.unbounded.exterior ->
        Exists fun k : Fin rows.boundary.length =>
          rows.boundary.vertex k = v /\
          (canonicalGraph C).Adj v
            (rows.boundary.vertex
              (PlanarInterface.cyclicSucc rows.boundary.length_pos k)) := by
  intro v hv
  rcases rows.frontier_vertices_are_cycle_vertices v hv with ⟨k, hk⟩
  refine ⟨k, hk, ?_⟩
  rw [← hk]
  exact rows.boundary.adjacent k

def toExteriorFrontierCycleRows
    (rows : UnboundedExteriorFrontierCycleRows C inputs) :
    ExteriorFrontierCycleRows C inputs where
  exterior := rows.unbounded.exterior
  exterior_subset_drawingComplement :=
    rows.unbounded.toExteriorComponentRows.exterior_subset_drawingComplement
  exterior_open := rows.unbounded.toExteriorComponentRows.exterior_open
  boundary := rows.boundary
  frontier_iff_cycle_vertex := rows.frontier_iff_cycle_vertex

end UnboundedExteriorFrontierCycleRows

/-- Exterior frontier-cycle rows supply the exact cycle/frontier/not-in-exterior
shape consumed by the current S2 reducer. -/
theorem exterior_cycle_frontier_not_mem_rows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs : FinitePlanarOuterComponentInputs C) ->
          ExteriorFrontierCycleRows C inputs) :
    forall {n : Nat} (C : _root_.UDConfig n),
      FinitePlanarOuterComponentInputs C ->
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          Exists fun exterior : Set PlanarInterface.Point =>
            (forall v : Fin n,
              (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
                (canonicalGraph C).point v ∉ exterior) /\
            (forall v : Fin n,
              (canonicalGraph C).point v ∈ frontier exterior <->
                Exists fun k : Fin B.length => B.vertex k = v) := by
  intro n C inputs
  let row := rows C inputs
  refine
    ⟨row.boundary, row.exterior, ?_, row.frontier_iff_cycle_vertex⟩
  intro v _hv
  exact graph_vertex_not_mem_exterior row.toExteriorComponentRows v

/-- The honest S2 theorem is now reduced to producing exterior frontier-cycle
rows for the complement of the embedded drawing. -/
def finitePlanarStraightLineOuterComponentTheorem_of_exteriorFrontierCycleRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs : FinitePlanarOuterComponentInputs C) ->
          ExteriorFrontierCycleRows C inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exterior_cycle_frontier_not_mem
    (exterior_cycle_frontier_not_mem_rows rows)

/-- The S2 theorem follows once the selected unbounded component is shown to
have a simple unit-distance frontier cycle on graph vertices. -/
def finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs : FinitePlanarOuterComponentInputs C) ->
          UnboundedExteriorFrontierCycleRows C inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorFrontierCycleRows
    (fun C inputs =>
      (rows C inputs).toExteriorFrontierCycleRows)

end

end ExteriorComponentTopology
end Swanepoel
end ErdosProblems1066
