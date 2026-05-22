import ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly

set_option autoImplicit false

/-!
# S2 actual carrier cut source

This owner file records the e32 handoff for the sharp carrier
cut-partition source.  The residual is kept in the fieldwise e19 shape:
two actual incident `unboundedFrontierEdgeSet` heads at each actual
unbounded-frontier carrier vertex, plus a concrete cut partition for every
third actual carrier neighbour.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace S2CarrierCutSource

open JordanTopologyFactsConcrete
open JordanTopologyFactsConcrete.MinimalFailureTopology
open ExteriorComponentTopology
open FinitePlaneDrawing
open S2LocalTwoGermAssembly

noncomputable section

variable {n : Nat}

/-- r30 compatibility name for the finite-plane deleted-neighbour local
separation primitive.

The current primitive is exactly nonempty deleted-neighbour local-separation
input rows.  Keeping this name avoids stale route drift without introducing a
new source layer. -/
abbrev S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  Nonempty (UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource C inputs)

/-- Erase the r30 compatibility primitive to the actual deleted-neighbour
local-separation input source. -/
noncomputable def
    S2_r30_deleted_neighbor_local_separation_source_20260521r30_of_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
      C inputs :=
  Classical.choice source

/-- The r30 compatibility primitive is exactly nonempty deleted-neighbour
local-separation input rows. -/
theorem
    S2_r30_deleted_neighbor_local_separation_source_nonempty_iff_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
          C inputs) ↔
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs :=
  Iff.rfl

/-- Package an actual deleted-neighbour local-separation source as the r30
compatibility primitive. -/
theorem
    S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_localPlanarSeparationInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
        C inputs) :
    S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
      (C := C) inputs :=
  ⟨source⟩

set_option linter.style.longLine false in
/-- A concrete cut partition separates vertices on opposite sides after
deleting the cut vertex.

This is the finite graph eraser used by the repeated raw-tail cut route: once
the exterior face-walk argument produces a genuine
`CutVertexInterface.CutVertexPartition` with the two successor tails on
opposite sides, reachability in the graph induced away from the cut vertex is
impossible. -/
theorem cutVertexPartition_not_reachable_after_delete_of_mem_opposite_sides
    {C : _root_.UDConfig n}
    (P : CutVertexInterface.CutVertexPartition C)
    {cut u v : Fin n}
    (hcut : P.cut = cut)
    (hu_cut : u ≠ cut)
    (hv_cut : v ≠ cut)
    (hopposite :
      (u ∈ P.left ∧ v ∈ P.right) ∨
        (u ∈ P.right ∧ v ∈ P.left)) :
    ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
        ({cut}ᶜ : Set (Fin n))).Reachable
        ⟨u, by simpa using hu_cut⟩
        ⟨v, by simpa using hv_cut⟩ := by
  classical
  rcases hopposite with huv | huv
  · let R : BoolSideSeparationRows C :=
      { cut := cut
        side := fun x => decide (x ∈ P.left)
        trueWitness := u
        trueWitness_ne_cut := hu_cut
        trueWitness_side := by
          simp [huv.1]
        falseWitness := v
        falseWitness_ne_cut := hv_cut
        falseWitness_side := by
          have hv_not_left : v ∉ P.left := by
            intro hv_left
            exact (Finset.disjoint_left.mp P.disjoint) hv_left huv.2
          simp [hv_not_left]
        anticomplete := by
          intro a b _ha_cut hb_cut ha_side hb_side
          have ha_left : a ∈ P.left := by
            exact of_decide_eq_true ha_side
          have hb_not_left : b ∉ P.left := by
            exact of_decide_eq_false hb_side
          have hb_right : b ∈ P.right := by
            have hb_P_cut : b ≠ P.cut := by
              intro h
              exact hb_cut (h.trans hcut)
            rcases P.mem_left_or_mem_right_of_ne_cut hb_P_cut with hb_left | hb_right
            · exact False.elim (hb_not_left hb_left)
            · exact hb_right
          exact P.anticomplete a ha_left b hb_right }
    simpa [R] using BoolSideSeparationRows.not_reachable_true_false_after_delete R
  · let R : BoolSideSeparationRows C :=
      { cut := cut
        side := fun x => decide (x ∈ P.right)
        trueWitness := u
        trueWitness_ne_cut := hu_cut
        trueWitness_side := by
          simp [huv.1]
        falseWitness := v
        falseWitness_ne_cut := hv_cut
        falseWitness_side := by
          have hv_not_right : v ∉ P.right := by
            intro hv_right
            exact (Finset.disjoint_left.mp P.disjoint) huv.2 hv_right
          simp [hv_not_right]
        anticomplete := by
          intro a b ha_cut _hb_cut ha_side hb_side
          have ha_right : a ∈ P.right := by
            exact of_decide_eq_true ha_side
          have hb_not_right : b ∉ P.right := by
            exact of_decide_eq_false hb_side
          have hb_left : b ∈ P.left := by
            have hb_P_cut : b ≠ P.cut := by
              intro h
              exact _hb_cut (h.trans hcut)
            rcases P.mem_left_or_mem_right_of_ne_cut hb_P_cut with hb_left | hb_right
            · exact hb_left
            · exact False.elim (hb_not_right hb_right)
          intro hab
          exact P.anticomplete b hb_left a ha_right
            ((GraphBridge.unitDistanceSimpleGraph C).symm hab) }
    simpa [R] using BoolSideSeparationRows.not_reachable_true_false_after_delete R

/-- The exact fieldwise residual for claim
`S2-agent-carrier-cut-source-worker-20260521e32`.

For each actual unbounded-frontier carrier vertex this names two true incident
`unboundedFrontierEdgeSet` heads and asks every third actual carrier neighbour
to produce an honest `CutVertexInterface.CutVertexPartition`. -/
abbrev S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
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
              forall b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
                (unboundedFrontierCarrierGraph C inputs).Adj a b ->
                  b.1 ≠ left ->
                    b.1 ≠ right ->
                      Nonempty (CutVertexInterface.CutVertexPartition C)

/-- e32 is definitionally the e19 exact residual. -/
theorem S2_agent_carrier_cut_source_worker_20260521e32_exact_iff
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) ↔
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  constructor
  · rintro ⟨source⟩
    simpa [S2_agent_carrier_cut_source_worker_20260521e32_fieldwise] using
      source.rows
  · intro source
    exact ⟨{ rows := source }⟩

/-- Package a fieldwise e32 source into the input-shaped cut-partition source
through the checked e19 constructor. -/
noncomputable def
    S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  { rows := source }

set_option linter.style.longLine false in
/-- Claim `S2-agent-carrier-cut-rows-source-20260521k10`.

The pointwise cut-row family is sourced directly from the actual selected
unbounded-frontier edge pairs and third-neighbour cut partitions stored in the
e32 fieldwise source.  This is only the existing sharp input-source package
followed by the existing row unpacker; it does not pass through neighbour-pair
degree, cycle, enclosure, or W-facing rows. -/
noncomputable def
    S2_agent_carrier_cut_rows_source_20260521k10_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a :=
  unboundedFrontierCarrierNeighborPairCutPartitionRows_of_inputSource
    (C := C) (inputs := inputs)
    (S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_carrier_cut_rows_source_20260521k10_of_carrierCutFieldwise`. -/
noncomputable def
    S2_agent_carrier_cut_rows_source_family_20260521k10_of_carrierCutFieldwise
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_rows_source_20260521k10_of_carrierCutFieldwise
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact nonempty form of the k10 row source.

The lower source leaf is precisely the actual selected-edge/third-cut e32
fieldwise package; the reverse direction unpacks it to pointwise cut rows, and
the forward direction repackages those rows fieldwise. -/
theorem
    S2_agent_carrier_cut_rows_source_20260521k10_nonempty_iff_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) ↔
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  constructor
  · rintro ⟨rows⟩
    intro a
    let r := rows a
    exact
      ⟨r.left, r.right, r.left_edge, r.right_edge, r.heads_ne,
        r.third_neighbor_cutPartitions⟩
  · intro source
    exact
      ⟨S2_agent_carrier_cut_rows_source_20260521k10_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source⟩

/-- Read the fieldwise e32 source from already checked pointwise
cut-partition rows, preserving the selected heads and their actual
`unboundedFrontierEdgeSet` incidences. -/
theorem
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise_of_cutPartitionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  intro a
  let r := rows a
  exact
    ⟨r.left, r.right, r.left_edge, r.right_edge, r.heads_ne,
      r.third_neighbor_cutPartitions⟩

/-- The deleted-graph source strictly reduces the fieldwise e32 source.

The selected heads and the two incident `unboundedFrontierEdgeSet` rows are
copied from the deleted-graph source; its third-neighbour nonreachability row
is converted by the existing deleted-graph-to-cut-partition eraser. -/
theorem
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise_of_unreachableAfterDelete
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  have hsource :
      Nonempty
        (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :=
    ⟨S2_agent_cutpartition_source_construction_worker_20260521e4
      (C := C) (inputs := inputs) source⟩
  exact
    (S2_agent_carrier_cut_source_worker_20260521e32_exact_iff
      (C := C) (inputs := inputs)).1 hsource

/-- Input-shaped e32 handoff from the deleted-graph source, via the fieldwise
e19 residual above. -/
noncomputable def
    S2_agent_carrier_cut_source_worker_20260521e32_of_unreachableAfterDelete
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
    (C := C) (inputs := inputs)
    (S2_agent_carrier_cut_source_worker_20260521e32_fieldwise_of_unreachableAfterDelete
      (C := C) (inputs := inputs) source)

/-- Feed the e25 selected-incident-edge reducer directly from the fieldwise
e32 source, keeping the same two actual selected heads. -/
noncomputable def
    S2_agent_carrier_cut_source_worker_20260521e32_selectedIncidentRows_of_fieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_neighborPairRows
    (C := C) inputs
    (fun a =>
      (S2_agent_carrier_cut_rows_source_20260521k10_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source a).toNeighborPairAt)

/-- Deleted-graph source form of the same e25 selected-incident-edge handoff. -/
noncomputable def
    S2_agent_carrier_cut_source_worker_20260521e32_selectedIncidentRows_of_unreachableAfterDelete
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_agent_carrier_cut_source_worker_20260521e32_selectedIncidentRows_of_fieldwise
    (C := C) (inputs := inputs)
    (S2_agent_carrier_cut_source_worker_20260521e32_fieldwise_of_unreachableAfterDelete
      (C := C) (inputs := inputs) source)

/-- Family form of the e32 cut-partition handoff from the deleted-graph
source. -/
noncomputable def
    S2_agent_carrier_cut_source_worker_20260521e32_family_of_unreachableAfterDelete
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_source_worker_20260521e32_of_unreachableAfterDelete
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-carrier-cut-source-direct-20260521e65`.

The input-only cut-partition source is strictly reduced to the actual selected
exterior-carrier incidence package.  The selected heads and their
`unboundedFrontierEdgeSet` incidences are copied directly from
`LocalSelectedIncidentEdgePairSourceRows`; a requested third concrete carrier
neighbour is impossible by `only_selected_incident`, so the cut-partition
branch is discharged without using induced frontier graphs, arbitrary carrier
cycles, all-adjacent endpoint rows, all-outgoing no-between rows, final
boundary-cycle rows, or a W facade. -/
noncomputable def
    S2_agent_carrier_cut_source_direct_20260521e65_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs where
  rows := by
    intro a
    refine
      ⟨source.left a, source.right a,
        source.left_edge a, source.right_edge a, source.heads_ne a, ?_⟩
    intro b hb hb_left hb_right
    have hedge :
        (a.1, b.1) ∈ unboundedFrontierEdgeSet C inputs ∨
          (b.1, a.1) ∈ unboundedFrontierEdgeSet C inputs :=
      (unboundedFrontierCarrierGraph_adj_iff).1 hb
    rcases source.only_selected_incident a b.1 hedge with hb_left' | hb_right'
    · exact False.elim (hb_left hb_left')
    · exact False.elim (hb_right hb_right')

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_carrier_cut_source_direct_20260521e65_of_selectedIncidentEdgePairRows`.

Thus the remaining input-only local source is the family of actual selected
incident exterior-carrier rows: two genuine selected
`unboundedFrontierEdgeSet` heads at each actual carrier vertex, plus
completeness for selected incident carrier edges. -/
noncomputable def
    S2_agent_carrier_cut_source_direct_family_20260521e65_of_selectedIncidentEdgePairRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_source_direct_20260521e65_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact nonempty form of the e65 direct source reduction.

The forward direction only forgets the cut-partition payload to the same
selected incident heads; the reverse direction is the direct e65 constructor
above. -/
theorem
    S2_agent_carrier_cut_source_direct_20260521e65_nonempty_iff_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) ↔
      Nonempty (LocalSelectedIncidentEdgePairSourceRows inputs) := by
  constructor
  · rintro ⟨source⟩
    exact
      ⟨S2_agent_carrier_cut_source_worker_20260521e32_selectedIncidentRows_of_fieldwise
        (C := C) (inputs := inputs) source.rows⟩
  · rintro ⟨source⟩
    exact
      ⟨S2_agent_carrier_cut_source_direct_20260521e65_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- Claim `S2-r22-cutPartitionInputSource`, exact selected-carrier source.

This is the source surface requested for the boundary-free/no-third local
handoff: at each actual unbounded-frontier carrier vertex choose two genuine
incident `unboundedFrontierEdgeSet` heads, and for every third actual carrier
neighbour provide the concrete cut partition.  The no-cut field in
`FinitePlanarOuterComponentInputs` is consumed only by the selected-incident
eraser below. -/
abbrev S2_r22_selectedCarrierNeighborThirdCutPartitionSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs

set_option linter.style.longLine false in
/-- r22 source theorem for the sharp cut-partition input source.

No actual-sector rows, final boundary cycle, W32 route, induced frontier graph,
or all-adjacent endpoint shortcut is used here; the theorem just packages the
selected carrier heads plus third-neighbour cut partitions into the current
input source. -/
noncomputable def
    S2_r22_cutPartitionInputSource_of_selectedCarrierNeighborThirdCutPartitions
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r22_selectedCarrierNeighborThirdCutPartitionSource inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of the r22 selected-carrier/third-cut source theorem. -/
noncomputable def
    S2_r22_cutPartitionInputSource_family_of_selectedCarrierNeighborThirdCutPartitions
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r22_selectedCarrierNeighborThirdCutPartitionSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_r22_cutPartitionInputSource_of_selectedCarrierNeighborThirdCutPartitions
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact nonempty residual for r22.

Thus the live local source is precisely selected carrier neighbours plus
third-neighbour cut partitions; it is not an actual-sector, final-boundary, or
W-facing premise. -/
theorem
    S2_r22_cutPartitionInputSource_nonempty_iff_selectedCarrierNeighborThirdCutPartitions
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs) ↔
      S2_r22_selectedCarrierNeighborThirdCutPartitionSource inputs := by
  simpa [S2_r22_selectedCarrierNeighborThirdCutPartitionSource] using
    (S2_agent_carrier_cut_source_worker_20260521e32_exact_iff
      (C := C) (inputs := inputs))

set_option linter.style.longLine false in
/-- r22 no-cut eraser to the selected-incident carrier source.

The third-neighbour cut partitions contradict `inputs.noCutVertex`, so the two
selected carrier heads classify every actual incident unbounded-frontier edge.
-/
noncomputable def
    S2_r22_selectedIncidentRows_of_selectedCarrierNeighborThirdCutPartitions
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r22_selectedCarrierNeighborThirdCutPartitionSource inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_agent_carrier_cut_source_worker_20260521e32_selectedIncidentRows_of_fieldwise
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- r22 strict lowering to selected incident carrier rows.

This exposes the smaller remaining local leaf after no-cut: prove the two
actual selected `unboundedFrontierEdgeSet` heads and selected-incident
completeness at each unbounded-frontier carrier vertex. -/
theorem
    S2_r22_cutPartitionInputSource_nonempty_iff_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs) ↔
      Nonempty (LocalSelectedIncidentEdgePairSourceRows inputs) :=
  S2_agent_carrier_cut_source_direct_20260521e65_nonempty_iff_selectedIncidentEdgePairRows
    (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-carrier-cut-fieldwise-source-20260521f3`.

The e32 fieldwise cut package is strictly reduced to the pure selected
incident-edge pair source.  The selected heads and their actual
`unboundedFrontierEdgeSet` incidences are copied from the source; the concrete
cut-partition branch is unreachable because `only_selected_incident` says any
actual incident carrier neighbour has one of the selected heads. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_20260521f3_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  exact
    (S2_agent_carrier_cut_source_worker_20260521e32_exact_iff
      (C := C) (inputs := inputs)).1
      ⟨S2_agent_carrier_cut_source_direct_20260521e65_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- Honest face-dart exterior-carrier rows source the e32 fieldwise cut
package.

The selected heads and selected `unboundedFrontierEdgeSet` incidences are read
from `FaceDartOrbitExteriorCarrierRows.toLocalSectorRowsAt`; third-neighbour
requests are discharged by the same actual-carrier `only` row. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_20260521j8_of_faceDartOrbitExteriorCarrierRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : FaceDartOrbitExteriorCarrierRows C inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521f3_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs)
      (S2_agent_selected_incident_edge_source_20260520c_of_localSectorRows
        (C := C) (inputs := inputs) rows.toLocalSectorRowsAt)

set_option linter.style.longLine false in
/-- Family form of the face-dart exterior-carrier source for the e32 fieldwise
cut package. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_family_20260521j8_of_faceDartOrbitExteriorCarrierRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FaceDartOrbitExteriorCarrierRows C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521j8_of_faceDartOrbitExteriorCarrierRows
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Actual exterior-sector input rows source the e32 fieldwise cut package.

This keeps the local residual below the honest exterior face-dart carrier:
the only remaining geometric input is an actual boundary cycle whose vertices
are exactly the unbounded-frontier graph vertices, together with the bundled
actual exterior-sector rows for that same boundary. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_20260521j16_of_actualExteriorSectorInputSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
        (forall v : Fin n,
          (canonicalGraph C).point v ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ↔
            Exists fun k : Fin B.length => B.vertex k = v) ∧
        _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B)) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521j8_of_faceDartOrbitExteriorCarrierRows
      (C := C) (inputs := inputs)
      (S2_agent_cl_face_orbit_carrier_source_20260520cl
        (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of the actual exterior-sector source for the e32 fieldwise cut
package. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_family_20260521j16_of_actualExteriorSectorInputSourceRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin m,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521j16_of_actualExteriorSectorInputSourceRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Primitive boundary-sector rows source the e32 fieldwise cut package.

This is the same-boundary form of the j16 lowering.  The boundary cycle,
exact frontier-vertex equivalence, and primitive
`BoundaryVertexExteriorSectorRowsAt` family are first bundled into
`ActualExteriorSectorInputSourceRows`, then erased through the honest
face-dart carrier. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_20260521j17_of_boundaryVertexExteriorSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
        (forall v : Fin n,
          (canonicalGraph C).point v ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ↔
            Exists fun k : Fin B.length => B.vertex k = v) ∧
        (forall k : Fin B.length,
          BoundaryVertexExteriorSectorRowsAt inputs B k)) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs :=
  S2_agent_carrier_cut_fieldwise_source_20260521j16_of_actualExteriorSectorInputSourceRows
    (C := C) (inputs := inputs)
    (exists_actualExteriorSectorInputSourceRows_with_frontier_of_boundaryVertexExteriorSectorRows_source
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of the primitive boundary-sector source for the e32 fieldwise
cut package. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_family_20260521j17_of_boundaryVertexExteriorSectorRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin m,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            (forall k : Fin B.length,
              BoundaryVertexExteriorSectorRowsAt inputs B k)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521j17_of_boundaryVertexExteriorSectorRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_carrier_cut_fieldwise_source_20260521f3_of_selectedIncidentEdgePairRows`.

Thus the remaining fieldwise e32 source is reduced to selected incident-edge
pair rows on the actual carrier graph, without induced frontier graphs,
all-adjacent endpoint rows, arbitrary cycles, identity angular order,
selected-head all-outgoing no-between rows, or final boundary-cycle rows. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_family_20260521f3_of_selectedIncidentEdgePairRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521f3_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact nonempty form of the f3 strict reduction.

The forward direction forgets the concrete cut-partition payload back to the
same selected incident heads; the reverse direction is the f3 reducer above. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_20260521f3_nonempty_iff_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs <->
      Nonempty (LocalSelectedIncidentEdgePairSourceRows inputs) := by
  constructor
  · intro source
    exact
      ⟨S2_agent_carrier_cut_source_worker_20260521e32_selectedIncidentRows_of_fieldwise
        (C := C) (inputs := inputs) source⟩
  · rintro ⟨source⟩
    exact
      S2_agent_carrier_cut_fieldwise_source_20260521f3_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Claim `S2-k6-selected-incident-edge-pair-from-inputs`.

The input-level selected incident-edge pair source is strictly lowered to the
e32 actual-carrier cut field.  The residual is the concrete carrier data:
for each actual unbounded-frontier vertex, two incident
`unboundedFrontierEdgeSet` heads and a cut-partition payload for every third
actual `unboundedFrontierCarrierGraph` neighbour. -/
noncomputable def
    S2_k6_selected_incident_edge_pair_from_inputs_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_agent_carrier_cut_source_worker_20260521e32_selectedIncidentRows_of_fieldwise
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of `S2_k6_selected_incident_edge_pair_from_inputs_of_carrierCutFieldwise`.

This is the requested input-family lowering: no induced frontier graph,
all-adjacent endpoint closure, arbitrary cycle, convex hull, identity angular
order, or all-outgoing no-between row is introduced. -/
noncomputable def
    S2_k6_selected_incident_edge_pair_from_inputs_family_of_carrierCutFieldwise
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_k6_selected_incident_edge_pair_from_inputs_of_carrierCutFieldwise
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact k6 residual.

The selected incident-edge source is equivalent to the e32 actual-carrier cut
field.  The displayed forward direction is the k6 lowering; the reverse
direction is the existing f3 selected-row-to-cut-field reducer. -/
theorem
    S2_k6_selected_incident_edge_pair_from_inputs_nonempty_iff_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty (LocalSelectedIncidentEdgePairSourceRows inputs) <->
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  simpa using
    (S2_agent_carrier_cut_fieldwise_source_20260521f3_nonempty_iff_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs)).symm

/-- Claim `S2-agent-cutpartition-input-source-prover-20260521e52`.

The sharp cut-partition input source is strictly reduced to the exact
deleted-neighbour local separation fields.  The lower source still names the
two actual incident `unboundedFrontierEdgeSet` heads at every actual carrier
vertex and supplies only the Boolean side-separation row for each third
`unboundedFrontierCarrierGraph` neighbour; the existing checked erasers turn
that local separation into deleted-graph nonreachability and then into the
concrete `CutVertexInterface.CutVertexPartition`. -/
noncomputable def
    S2_agent_cutpartition_input_source_prover_20260521e52_of_deletedNeighborLocalSeparationExactFieldSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
        inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_agent_deleted_neighbor_local_separation_worker_20260521e6_to_e4_cutpartition
    (C := C) (inputs := inputs) source

/-- Family form of the e52 strict reduction.  Thus the remaining input-only
local source is the exact deleted-neighbour local separation theorem, stated on
the actual carrier graph and actual unbounded-frontier edge set. -/
noncomputable def
    S2_agent_cutpartition_input_source_prover_family_20260521e52_of_deletedNeighborLocalSeparationExactFieldSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs := by
  intro m C inputs
  exact
    S2_agent_cutpartition_input_source_prover_20260521e52_of_deletedNeighborLocalSeparationExactFieldSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-r3`, deleted-neighbour exact-field source from ambient
deleted-graph nonreachability.

This is the strict lowering of the exact local Boolean field package: the
remaining source is precisely the existing ambient deleted-graph row saying
that every actual third unbounded-frontier carrier neighbour is unreachable
from the selected left head after deleting the frontier vertex.  The Boolean
side labelling is then the connected component of that left head in the
deleted graph, and the existing cut-partition erasers remain the only
conversion to `CutVertexInterface.CutVertexPartition`. -/
noncomputable def
    S2_r3_deleted_neighbor_local_separation_exact_field_source_of_unreachableAfterDelete
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
      inputs :=
  UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource.ofUnreachableAfterDeleteInputSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of
`S2_r3_deleted_neighbor_local_separation_exact_field_source_of_unreachableAfterDelete`. -/
noncomputable def
    S2_r3_deleted_neighbor_local_separation_exact_field_source_family_of_unreachableAfterDelete
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
          inputs := by
  intro m C inputs
  exact
    S2_r3_deleted_neighbor_local_separation_exact_field_source_of_unreachableAfterDelete
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q6-neighbor-cutpartition-input-source-20260521q2`,
first pointwise cut-row step.

This is the sharp local theorem below the input-only source: once the actual
deleted-neighbour local separation fields are known, the two selected heads are
the real incident `unboundedFrontierEdgeSet` heads from that field source, and
each third concrete carrier neighbour is turned into an honest
`CutVertexInterface.CutVertexPartition` through the checked deleted-graph
unreachability constructor.  This does not add a consumer facade for the full
bare-input theorem. -/
noncomputable def
    S2_q6_neighbor_cutpartition_input_source_20260521q2_cutRows_of_deletedNeighborLocalSeparationExactFieldSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
        inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a := by
  intro a
  exact
    ((source.toRowsAt a).toUnreachableAfterDeleteRowsAt).toCutPartitionRowsAt

set_option linter.style.longLine false in
/-- The `S2-r3` lowering also feeds the checked pointwise cut-row source.

Thus an actual third carrier neighbour with deleted-graph nonreachability is
immediately converted to the existing cut-partition row, with no W-facing
wrapper, induced-frontier shortcut, or endpoint-chord shortcut. -/
noncomputable def
    S2_r3_neighbor_cutRows_of_unreachableAfterDelete
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a :=
  S2_q6_neighbor_cutpartition_input_source_20260521q2_cutRows_of_deletedNeighborLocalSeparationExactFieldSource
    (C := C) (inputs := inputs)
    (S2_r3_deleted_neighbor_local_separation_exact_field_source_of_unreachableAfterDelete
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Claim `S2-r7`, pointwise deleted-neighbour source from the sharp carrier
cut field.

At one actual unbounded-frontier carrier vertex, the e32 cut field already
names two genuine incident `unboundedFrontierEdgeSet` heads and a concrete cut
partition for every requested third actual carrier neighbour.  The existing
checked no-cut/cut-partition eraser makes the deleted-graph reachability
branch contradictory, yielding the ambient unreachable-after-delete row at
that same vertex. -/
noncomputable def
    S2_r7_unreachableAfterDelete_rowsAt_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs)
    (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteRowsAt
      inputs a :=
  unboundedFrontierCarrierNeighborPairUnreachableAfterDeleteRowsAt_of_localSectorRowsAt
    (localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
      (C := C) inputs
      (fun a =>
        (S2_agent_carrier_cut_rows_source_20260521k10_of_carrierCutFieldwise
          (C := C) (inputs := inputs) source a).toNeighborPairAt)
      a)

set_option linter.style.longLine false in
/-- Claim `S2-r7`, input-source deleted-neighbour lowering.

This packages the pointwise r7 row above for every actual carrier vertex.  The
remaining source is exactly the sharp e32 carrier cut field; no final
boundary-sector rows, actual exterior-sector rows, induced frontier graph,
all-adjacent endpoint rows, arbitrary carrier cycle, or unchecked placeholder
is used. -/
noncomputable def
    S2_r7_unreachableAfterDelete_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs where
  rows := fun a =>
    S2_r7_unreachableAfterDelete_rowsAt_of_carrierCutFieldwise
      (C := C) (inputs := inputs) source a

set_option linter.style.longLine false in
/-- Family form of the r7 deleted-neighbour lowering from the sharp carrier
cut field. -/
noncomputable def
    S2_r7_unreachableAfterDelete_family_of_carrierCutFieldwise
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_r7_unreachableAfterDelete_of_carrierCutFieldwise
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact nonempty residual for r7.

The ambient deleted-neighbour source and the e32 fieldwise carrier cut source
are equivalent at this local level: one direction is the existing r3/e32
unpacker, and the other is the pointwise r7 no-cut/cut-partition lowering. -/
theorem S2_r7_unreachableAfterDelete_nonempty_iff_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs) ↔
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs := by
  constructor
  · rintro ⟨source⟩
    exact
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise_of_unreachableAfterDelete
        (C := C) (inputs := inputs) source
  · intro source
    exact
      ⟨S2_r7_unreachableAfterDelete_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- Claim `S2-r24-carrier-cut-input-source-20260521r24`,
deleted-neighbour local-separation source form.

This is the strict source theorem for the current local carrier-cut leaf:
Boolean side-separation rows in the graph with the frontier vertex deleted are
promoted by the checked local-separation eraser to ambient deleted-graph
nonreachability, and then by the checked e4/e19 cut-partition eraser to the
actual `UnboundedFrontierCarrierNeighborPairCutPartitionInputSource`.  The
source stays on actual `unboundedFrontierEdgeSet` heads and actual carrier
neighbours; it does not use exterior-sector rows, final boundary cycles, W32,
induced frontier graphs, or all-adjacent endpoint shortcuts. -/
noncomputable def
    S2_r24_carrier_cut_input_source_of_deletedNeighborLocalSeparationInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
        C inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_agent_cutpartition_source_construction_worker_20260521e4_of_localSeparation
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of the r24 local-separation source theorem. -/
noncomputable def
    S2_r24_carrier_cut_input_source_family_of_deletedNeighborLocalSeparationInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_r24_carrier_cut_input_source_of_deletedNeighborLocalSeparationInputSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact nonempty residual exposed by r24.

The forward direction only reads the deleted-neighbour/local-separation rows
already forced by an existing carrier-cut source, via the r7 deleted-graph
unreachability reducer and the checked component-side construction.  The
reverse direction is the strict r24 source theorem above. -/
theorem
    S2_r24_carrier_cut_input_source_nonempty_iff_deletedNeighborLocalSeparationInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs) ↔
      Nonempty
        (UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
          C inputs) := by
  constructor
  · rintro ⟨source⟩
    let unreachable :
        UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs :=
      S2_r7_unreachableAfterDelete_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source.rows
    let exactField :
        UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
          inputs :=
      S2_r3_deleted_neighbor_local_separation_exact_field_source_of_unreachableAfterDelete
        (C := C) (inputs := inputs) unreachable
    exact ⟨exactField.toInputSource⟩
  · rintro ⟨source⟩
    exact
      ⟨S2_r24_carrier_cut_input_source_of_deletedNeighborLocalSeparationInputSource
        (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- r30 carrier-cut source from the explicit local planar separation package.

This is the main cut-source handoff after the r30 primitive has been exposed:
local Boolean deleted-neighbour separation rows are promoted to the existing
selected carrier cut input source. -/
noncomputable def
    S2_r30_carrier_cut_input_source_of_localPlanarSeparationInputSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
        C inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_r24_carrier_cut_input_source_of_deletedNeighborLocalSeparationInputSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of the r30 carrier-cut source from local planar separation. -/
noncomputable def
    S2_r30_carrier_cut_input_source_family_of_localPlanarSeparationInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs := by
  intro m C inputs
  exact
    S2_r30_carrier_cut_input_source_of_localPlanarSeparationInputSource
      (C := C) inputs (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-r5r-carrier-cut-source-next-leaf-20260521r5r`.

The next deleted-neighbour/local-separation leaf for the carrier cut source is
the finite-plane Boolean side-separation primitive already exposed by r30.  We
first package that primitive as the checked deleted-neighbour local-separation
input source, then reuse the r24 eraser to obtain the actual
`UnboundedFrontierCarrierNeighborPairCutPartitionInputSource`. -/
noncomputable def
    S2_r5r_carrier_cut_source_next_leaf_20260521r5r_of_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_r24_carrier_cut_input_source_of_deletedNeighborLocalSeparationInputSource
    (C := C) (inputs := inputs)
    (S2_r30_deleted_neighbor_local_separation_source_20260521r30_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of the r5r next-leaf reduction. -/
noncomputable def
    S2_r5r_carrier_cut_source_next_leaf_family_20260521r5r_of_finitePlaneLocalSeparationPrimitive
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_r5r_carrier_cut_source_next_leaf_20260521r5r_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact r5r residual.

The current carrier cut input source is equivalent to the earlier r30
finite-plane deleted-neighbour local-separation primitive.  This is only the
composition of the checked r24 local-separation residual and the checked r30
field-level residual. -/
theorem
    S2_r5r_carrier_cut_source_next_leaf_nonempty_iff_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs) ↔
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs :=
  Iff.trans
    (S2_r24_carrier_cut_input_source_nonempty_iff_deletedNeighborLocalSeparationInputSource
      (C := C) (inputs := inputs))
    (S2_r30_deleted_neighbor_local_separation_source_nonempty_iff_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs))

set_option linter.style.longLine false in
/-- Claim `S2-r7f-finite-plane-local-separation-source`.

The sharp finite-plane cut primitive for a third unbounded-frontier carrier
neighbour feeds the current r30 deleted-neighbour Boolean separation source.
The source remains entirely local to the actual `unboundedFrontierCarrierGraph`:
the selected heads are the two real `unboundedFrontierEdgeSet` incidences from
the fieldwise cut source, the third-neighbour branch first becomes deleted
graph nonreachability through the checked no-cut/cut-partition eraser, and the
Boolean side rows are the deleted graph connected-component rows. -/
noncomputable def
    S2_r7f_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
  S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
      (C := C) inputs :=
  S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_localPlanarSeparationInputSource
    (C := C) (inputs := inputs)
    ((UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource.ofUnreachableAfterDeleteInputSource
      (C := C) (inputs := inputs)
      (S2_r7_unreachableAfterDelete_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source)).toInputSource)

set_option linter.style.longLine false in
/-- Family form of the r7f finite-plane local-separation source. -/
noncomputable def
    S2_r7f_deleted_neighbor_finitePlaneLocalSeparationPrimitive_family_of_carrierCutFieldwise
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
          (C := C) inputs := by
  intro m C inputs
  exact
    S2_r7f_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact r7f residual.

At this level, the r30 finite-plane Boolean local-separation primitive is
equivalent to the sharp fieldwise cut source: r30 gives the checked carrier cut
input source by the existing r5r eraser, while the reverse direction is the
r7f cut-to-deleted-component construction above. -/
theorem
    S2_r7f_deleted_neighbor_finitePlaneLocalSeparationPrimitive_iff_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs ↔
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs := by
  constructor
  · intro source
    exact
      (S2_agent_carrier_cut_source_worker_20260521e32_exact_iff
        (C := C) (inputs := inputs)).1
        ⟨S2_r5r_carrier_cut_source_next_leaf_20260521r5r_of_finitePlaneLocalSeparationPrimitive
          (C := C) (inputs := inputs) source⟩
  · intro source
    exact
      S2_r7f_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Claim `S2-q23-deleted-neighbor-source`.

Shortest checked local reducer chain from the r30 deleted-neighbour
finite-plane local-separation primitive to the e32 fieldwise carrier-cut
source.  This is only the existing r7f exact residual, restated in the q23
source direction. -/
theorem
    S2_q23_carrierCutFieldwise_iff_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs <->
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs :=
  (S2_r7f_deleted_neighbor_finitePlaneLocalSeparationPrimitive_iff_carrierCutFieldwise
    (C := C) (inputs := inputs)).symm

set_option linter.style.longLine false in
/-- Direct q23 e32 handoff from the finite-plane deleted-neighbour
local-separation primitive. -/
theorem
    S2_q23_carrierCutFieldwise_of_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
      inputs :=
  (S2_q23_carrierCutFieldwise_iff_finitePlaneLocalSeparationPrimitive
    (C := C) (inputs := inputs)).2 source

set_option linter.style.longLine false in
/-- Family q23 e32 handoff from the finite-plane deleted-neighbour
local-separation primitive. -/
theorem
    S2_q23_carrierCutFieldwise_family_of_finitePlaneLocalSeparationPrimitive
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_q23_carrierCutFieldwise_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family-level q23 residual: producing the r30 deleted-neighbour source for
every finite-plane input is equivalent to producing the e32 fieldwise
carrier-cut source for every finite-plane input. -/
theorem
    S2_q23_finitePlaneLocalSeparationPrimitive_family_iff_carrierCutFieldwise_family :
    (forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
          (C := C) inputs) <->
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) := by
  constructor
  · intro source m C inputs
    exact
      S2_q23_carrierCutFieldwise_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs) (source C inputs)
  · intro source m C inputs
    exact
      (S2_q23_carrierCutFieldwise_iff_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs)).1 (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q25-carrier-cut-source`.

The current e32 carrier-cut residual is exactly the r30 finite-plane
deleted-neighbour local-separation primitive.  This is a q25-facing name for
the checked r7f/q23 equivalence: the forward direction lowers the e32
fieldwise cut rows through no-cut to deleted-neighbour local separation, and
the reverse direction rebuilds the cut-partition input rows from that local
separation source. -/
theorem
    S2_q25_carrier_cut_source_iff_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs <->
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs :=
  S2_q23_carrierCutFieldwise_iff_finitePlaneLocalSeparationPrimitive
    (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- q25 forward lowering from e32 fieldwise carrier-cut rows to r30
deleted-neighbour local separation. -/
theorem
    S2_q25_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
      (C := C) inputs :=
  (S2_q25_carrier_cut_source_iff_finitePlaneLocalSeparationPrimitive
    (C := C) (inputs := inputs)).1 source

set_option linter.style.longLine false in
/-- q25 reverse handoff from r30 deleted-neighbour local separation to the e32
fieldwise carrier-cut source. -/
theorem
    S2_q25_carrierCutFieldwise_of_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
      inputs :=
  (S2_q25_carrier_cut_source_iff_finitePlaneLocalSeparationPrimitive
    (C := C) (inputs := inputs)).2 source

set_option linter.style.longLine false in
/-- q25 input-source form: r30 deleted-neighbour local separation produces the
actual carrier cut-partition input rows. -/
noncomputable def
    S2_q25_cutPartitionInputSource_of_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
    (C := C) (inputs := inputs)
    (S2_q25_carrierCutFieldwise_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- q25 no-cut consequence from the r30 primitive: the cut-partition rows erase
to the selected incident-edge source already used by the carrier local route. -/
noncomputable def
    S2_q25_selectedIncidentRows_of_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
    (C := C) (inputs := inputs)
    (S2_q25_cutPartitionInputSource_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Exact q25 nonempty residual for the input-shaped carrier cut source. -/
theorem
    S2_q25_carrier_cut_source_nonempty_iff_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs) <->
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs :=
  Iff.trans
    (S2_agent_carrier_cut_source_worker_20260521e32_exact_iff
      (C := C) (inputs := inputs))
    (S2_q25_carrier_cut_source_iff_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs))

set_option linter.style.longLine false in
/-- Family form of the q25 carrier-cut source reduction. -/
theorem
    S2_q25_carrierCutFieldwise_family_of_finitePlaneLocalSeparationPrimitive
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_q25_carrierCutFieldwise_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family-level q25 residual: e32 carrier-cut source families are equivalent
to r30 finite-plane local-separation primitive families. -/
theorem
    S2_q25_finitePlaneLocalSeparationPrimitive_family_iff_carrierCutFieldwise_family :
    (forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
          (C := C) inputs) <->
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) := by
  constructor
  · intro source m C inputs
    exact
      S2_q25_carrierCutFieldwise_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs) (source C inputs)
  · intro source m C inputs
    exact
      S2_q25_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
        (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q22-carrier-cut-to-selection-source`, e32 local-separation form.

The e32 fieldwise carrier-cut source is exactly the concrete finite-plane
deleted-neighbour local-separation input source: the selected heads are actual
`unboundedFrontierEdgeSet` incidences, and every third actual carrier neighbour
is separated in the graph with the carrier vertex deleted. -/
theorem
    S2_q22_carrierCutFieldwise_iff_deletedNeighborLocalSeparationInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs <->
      Nonempty
        (UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
          C inputs) := by
  exact
    Iff.trans
      (S2_agent_carrier_cut_source_worker_20260521e32_exact_iff
        (C := C) (inputs := inputs)).symm
      (S2_r24_carrier_cut_input_source_nonempty_iff_deletedNeighborLocalSeparationInputSource
        (C := C) (inputs := inputs))

set_option linter.style.longLine false in
/-- Direct e32 handoff from concrete deleted-neighbour local-separation data. -/
theorem
    S2_q22_carrierCutFieldwise_of_deletedNeighborLocalSeparationInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
        C inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
      inputs :=
  (S2_q22_carrierCutFieldwise_iff_deletedNeighborLocalSeparationInputSource
    (C := C) (inputs := inputs)).2 ⟨source⟩

set_option linter.style.longLine false in
/-- Family form of the q22 e32 handoff from concrete local-separation data. -/
theorem
    S2_q22_carrierCutFieldwise_family_of_deletedNeighborLocalSeparationInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_q22_carrierCutFieldwise_of_deletedNeighborLocalSeparationInputSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Equivalent q22 e32 residual in ambient deleted-graph form. -/
theorem
    S2_q22_carrierCutFieldwise_iff_unreachableAfterDeleteInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs <->
      Nonempty
        (UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs) :=
  (S2_r7_unreachableAfterDelete_nonempty_iff_carrierCutFieldwise
    (C := C) (inputs := inputs)).symm

set_option linter.style.longLine false in
/-- Direct e32 handoff from ambient deleted-neighbour nonreachability data. -/
theorem
    S2_q22_carrierCutFieldwise_of_unreachableAfterDeleteInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
      inputs :=
  (S2_q22_carrierCutFieldwise_iff_unreachableAfterDeleteInputSource
    (C := C) (inputs := inputs)).2 ⟨source⟩

set_option linter.style.longLine false in
/-- Claim `S2-r7i-agent-carrier-cut-source`.

Fieldwise raw-walk cut source below the e32 carrier-cut residual.

For each actual unbounded-frontier carrier vertex this names two actual selected
frontier-edge heads.  For any third concrete carrier neighbour it asks for the
specific lower primitive still missing from the raw exterior face-walk route: a
repeated-tail exterior cut row whose repeated tail is the carrier vertex.  This
does not assume an actual exterior-sector package, a final boundary cycle, a W32
consumer, an induced frontier graph, or an all-adjacent endpoint shortcut. -/
abbrev S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource
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
              forall b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
                (unboundedFrontierCarrierGraph C inputs).Adj a b ->
                  b.1 ≠ left ->
                    b.1 ≠ right ->
                      Exists fun R : UnitDistanceRotationSystem C =>
                        Exists fun start : UnitDistanceDart C =>
                          Exists fun O :
                              UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                            Exists fun i : Fin O.period =>
                              Exists fun j : Fin O.period =>
                                i ≠ j ∧
                                  (O.dart i).tail = (O.dart j).tail ∧
                                    (O.dart i).tail = a.1 ∧
                                      Nonempty
                                        (RawFaceSuccOrbitRepeatedTailExteriorCutRows
                                          (inputs := inputs) O i j)

set_option linter.style.longLine false in
/-- The raw repeated-tail exterior cut source strictly feeds the e32 fieldwise
carrier-cut rows.

The only erasure used here is
`RawFaceSuccOrbitRepeatedTailExteriorCutRows.toCutVertexPartition`; the selected
heads and their actual `unboundedFrontierEdgeSet` incidences are copied from the
raw-walk source.  Thus the remaining honest primitive is exactly the production
of those raw repeated-tail cut rows for each third carrier neighbour. -/
theorem
    S2_r7i_carrierCutFieldwise_of_rawFaceWalkRepeatedTailCutSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  intro a
  rcases source a with
    ⟨left, right, left_edge, right_edge, heads_ne, third_cut_rows⟩
  refine ⟨left, right, left_edge, right_edge, heads_ne, ?_⟩
  intro b hb hb_left hb_right
  rcases third_cut_rows b hb hb_left hb_right with
    ⟨R, start, O, i, j, _hij, _htail, _hcut, hcutRows⟩
  rcases hcutRows with ⟨cutRows⟩
  exact ⟨cutRows.toCutVertexPartition⟩

set_option linter.style.longLine false in
/-- Family form of the r7i raw repeated-tail cut source handoff. -/
theorem
    S2_r7i_carrierCutFieldwise_family_of_rawFaceWalkRepeatedTailCutSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_r7i_carrierCutFieldwise_of_rawFaceWalkRepeatedTailCutSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-r7j-raw-repeated-tail-carrier-cut-primitive`.

Raw-orbit-level residual for the r7i carrier-cut primitive.

For one selected raw exterior face walk, whenever a concrete carrier neighbour
of a raw tail is not the raw predecessor or raw successor at a chosen
occurrence, the source must exhibit a second occurrence of that same raw tail
and the minimal deleted-tail cut row for that repeated pair.

This is the non-circular finite-plane source field below r7i: it mentions the
raw face walk and the actual carrier neighbour, but it does not use W32, a
final boundary cycle, actual-sector rows, an induced frontier graph, an
arbitrary cycle, or all-adjacent endpoint rows. -/
abbrev S2_r7j_rawFaceWalkThirdCarrierNeighborRepeatedTailCutSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start) : Prop :=
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    forall b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (unboundedFrontierCarrierGraph C inputs).Adj a b ->
        forall k : Fin O.period,
          (O.dart k).tail = a.1 ->
            b.1 ≠
                (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ->
              b.1 ≠
                  (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail ->
                Exists fun j : Fin O.period =>
                  k ≠ j ∧
                    (O.dart j).tail = a.1 ∧
                      Nonempty
                        (RawFaceSuccOrbitRepeatedTailExteriorCutRows
                          (inputs := inputs) O k j)

set_option linter.style.longLine false in
/-- Claim `S2-r11-repeated-tail-cut-source`, cut-partition form.

This is the sharper source below the r7j raw repeated-tail carrier branch:
for a third concrete carrier neighbour of a raw-tail occurrence, it asks only
for the concrete cut partition forced by a second occurrence of the same raw
tail.  The exterior repeated-tail row source still implies this source by
`toCutVertexPartition`, but the carrier-cut consumer does not need the
stronger row once the partition is already available. -/
abbrev S2_r11_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start) : Prop :=
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    forall b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (unboundedFrontierCarrierGraph C inputs).Adj a b ->
        forall k : Fin O.period,
          (O.dart k).tail = a.1 ->
            b.1 ≠
                (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ->
              b.1 ≠
                  (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail ->
                Exists fun j : Fin O.period =>
                  k ≠ j ∧
                    (O.dart j).tail = a.1 ∧
                      Nonempty (CutVertexInterface.CutVertexPartition C)

set_option linter.style.longLine false in
/-- Exterior repeated-tail cut rows erase to the r11 cut-partition residual. -/
theorem
    S2_r11_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource_of_repeatedTailCutSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (source :
      S2_r7j_rawFaceWalkThirdCarrierNeighborRepeatedTailCutSource
        (inputs := inputs) O) :
    S2_r11_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource
      (inputs := inputs) O := by
  intro a b hb k hk hb_pred hb_succ
  rcases source a b hb k hk hb_pred hb_succ with
    ⟨j, hkj, hj_tail, hcutRows⟩
  rcases hcutRows with ⟨cutRows⟩
  exact ⟨j, hkj, hj_tail, ⟨cutRows.toCutVertexPartition⟩⟩

set_option linter.style.longLine false in
/-- r11 cut-partition residual directly supplies the e32 carrier-cut field.

The selected heads are still the predecessor and successor tails of the raw
occurrence, with actual `unboundedFrontierEdgeSet` incidence read from the raw
edge-frontier row.  The third-neighbour branch now consumes the concrete cut
partition directly, so this is strictly below the r7j exterior-cut-row source. -/
theorem
    S2_r11_carrierCutFieldwise_of_rawOrbit_thirdNeighborRepeatedTailCutPartitions
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (raw_pred_succ_tail_ne :
      forall k : Fin O.period,
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail)
    (thirdCutPartitions :
      S2_r11_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource
        (inputs := inputs) O) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
      (C := C) inputs := by
  classical
  intro a
  let k : Fin O.period := Classical.choose (frontier_vertex_tail_coverage a)
  have hk : (O.dart k).tail = a.1 :=
    Classical.choose_spec (frontier_vertex_tail_coverage a)
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  let left : Fin n := (O.dart pred).tail
  let right : Fin n := (O.dart succ).tail
  have hsucc_pred : PlanarInterface.cyclicSucc O.period_pos pred = k := by
    simp [pred, PlanarInterface.cyclicSucc_cyclicPred O.period_pos k]
  have left_edge :
      (a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hraw :=
      rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm
        (C := C) (inputs := inputs) O edge_openSegment_frontier pred
    rcases hraw with hforward | hreverse
    · exact Or.inr (by
        simpa [left, pred, hsucc_pred, hk] using hforward)
    · exact Or.inl (by
        simpa [left, pred, hsucc_pred, hk] using hreverse)
  have right_edge :
      (a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hraw :=
      rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm
        (C := C) (inputs := inputs) O edge_openSegment_frontier k
    rcases hraw with hforward | hreverse
    · exact Or.inl (by
        simpa [right, succ, hk] using hforward)
    · exact Or.inr (by
        simpa [right, succ, hk] using hreverse)
  have heads_ne : left ≠ right := by
    intro h
    exact
      raw_pred_succ_tail_ne k
        (by simpa [left, right, pred, succ] using h)
  refine ⟨left, right, left_edge, right_edge, heads_ne, ?_⟩
  intro b hb hb_left hb_right
  rcases
      thirdCutPartitions a b hb k hk
        (by simpa [left, pred] using hb_left)
        (by simpa [right, succ] using hb_right) with
    ⟨_j, _hkj, _hj_tail, hcutPartition⟩
  exact hcutPartition

set_option linter.style.longLine false in
/-- Family form of the r11 cut-partition residual for the carrier-cut field. -/
theorem
    S2_r11_carrierCutFieldwiseFamily_of_rawOrbit_thirdNeighborRepeatedTailCutPartitions
    (rawRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                (forall k : Fin O.period,
                  forall p : PlanarInterface.Point,
                    PlanarInterface.InOpenSegment p
                      ((canonicalGraph C).point (O.dart k).tail)
                      ((canonicalGraph C).point
                        (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
                    p ∈
                      frontier
                        (unboundedExteriorComponentRows C inputs).exterior) ∧
                (forall a : {v : Fin m //
                    v ∈ unboundedFrontierVertexSet C inputs},
                  Exists fun k : Fin O.period => (O.dart k).tail = a.1) ∧
                (forall k : Fin O.period,
                  (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
                    (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∧
                S2_r11_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource
                  (inputs := inputs) O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          (C := C) inputs := by
  intro m C inputs
  rcases rawRows C inputs with
    ⟨R, start, O, edgeRows, tailCoverage, predSuccNe, thirdPartitions⟩
  exact
    S2_r11_carrierCutFieldwise_of_rawOrbit_thirdNeighborRepeatedTailCutPartitions
      (C := C) (inputs := inputs) O edgeRows tailCoverage predSuccNe
      thirdPartitions

set_option linter.style.longLine false in
/-- Claim `S2-r12-repeated-tail-cut-partitions-from-exterior-walk`.

Raw-orbit third-neighbour source with the repeated-tail payload lowered below
`RawFaceSuccOrbitRepeatedTailExteriorCutRows`.

For each third concrete carrier neighbour of a raw-tail occurrence, this asks
only for the finite deleted-tail separation data for a second occurrence of
the same tail: one non-cut index on each cyclic open side and nonreachability
between their tails in the unit-distance graph induced after deleting the
repeated tail. -/
abbrev S2_r12_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start) : Prop :=
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    forall b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (unboundedFrontierCarrierGraph C inputs).Adj a b ->
        forall k : Fin O.period,
          (O.dart k).tail = a.1 ->
            b.1 ≠
                (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ->
              b.1 ≠
                  (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail ->
                Exists fun j : Fin O.period =>
                  k ≠ j ∧
                    (O.dart j).tail = a.1 ∧
                      Exists fun left :
                          {l : Fin O.period //
                            cyclicForwardOpenArc k j l ∧
                              (O.dart l).tail ≠ (O.dart k).tail} =>
                        Exists fun right :
                            {r : Fin O.period //
                              cyclicForwardOpenArc j k r ∧
                                (O.dart r).tail ≠ (O.dart k).tail} =>
                          ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
                              ({(O.dart k).tail}ᶜ : Set (Fin n))).Reachable
                              ⟨(O.dart left.1).tail, by simpa using left.2.2⟩
                              ⟨(O.dart right.1).tail, by simpa using right.2.2⟩

set_option linter.style.longLine false in
/-- q36 index-only third-neighbour repeated-tail source for one raw orbit.

For every actual third carrier neighbour of a raw-tail occurrence, this source
only supplies the second occurrence of that same raw tail.  The deleted-tail
separation payload is deliberately factored out into the minimal repeated-tail
source on the same raw orbit. -/
abbrev S2_q36_rawFaceWalkThirdCarrierNeighborRepeatedTailIndexSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start) : Prop :=
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    forall b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      (unboundedFrontierCarrierGraph C inputs).Adj a b ->
        forall k : Fin O.period,
          (O.dart k).tail = a.1 ->
            b.1 ≠
                (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ->
              b.1 ≠
                  (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail ->
                Exists fun j : Fin O.period =>
                  k ≠ j ∧ (O.dart j).tail = a.1

set_option linter.style.longLine false in
/-- q36 r12 source adapter, minimal deleted-tail form.

The third-neighbour branch contributes only the repeated-tail index; the
finite deleted-tail separation is read from the raw repeated-tail minimal
source for that exact pair.  This proves the r12 source without actual-sector
rows, W32 composers, boundary-sector erasers, arbitrary cycles, induced
frontier graphs, endpoint/all-adjacent shortcuts, or identity angular order. -/
theorem
    S2_q36_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource_of_repeatedTailIndex_minimalDeletedTailSeparation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (thirdRepeatedTail :
      S2_q36_rawFaceWalkThirdCarrierNeighborRepeatedTailIndexSource
        (inputs := inputs) O)
    (minimalSeparation :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          Exists fun left :
              {l : Fin O.period //
                cyclicForwardOpenArc i j l ∧
                  (O.dart l).tail ≠ (O.dart i).tail} =>
            Exists fun right :
                {r : Fin O.period //
                  cyclicForwardOpenArc j i r ∧
                    (O.dart r).tail ≠ (O.dart i).tail} =>
              ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
                  ({(O.dart i).tail}ᶜ : Set (Fin n))).Reachable
                  ⟨(O.dart left.1).tail, by simpa using left.2.2⟩
                  ⟨(O.dart right.1).tail, by simpa using right.2.2⟩) :
    S2_r12_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource
      (inputs := inputs) O := by
  intro a b hb k hk hb_pred hb_succ
  rcases thirdRepeatedTail a b hb k hk hb_pred hb_succ with
    ⟨j, hkj, hj_tail⟩
  have htail : (O.dart k).tail = (O.dart j).tail := hk.trans hj_tail.symm
  rcases minimalSeparation hkj htail with ⟨left, right, hnonreach⟩
  exact ⟨j, hkj, hj_tail, left, right, hnonreach⟩

set_option linter.style.longLine false in
/-- Claim `S2-r13-repeated-tail-minimal-deleted-separation-source`.

The r12 minimal deleted-tail source is vacuous once the actual raw-walk
third-neighbour branch already supplies the r11 cut-partition residual: the
concrete `CutVertexInterface.CutVertexPartition` contradicts
`inputs.noCutVertex`, so no endpoint closed-side shortcut, whole-frontier
split, induced frontier graph, or W32 consumer is introduced. -/
theorem
    S2_r13_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource_of_repeatedTailCutPartitions_noCut
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (thirdCutPartitions :
      S2_r11_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource
        (inputs := inputs) O) :
    S2_r12_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource
      (inputs := inputs) O := by
  intro a b hb k hk hb_pred hb_succ
  rcases thirdCutPartitions a b hb k hk hb_pred hb_succ with
    ⟨_j, _hkj, _hj_tail, hcutPartition⟩
  exact False.elim (inputs.noCutVertex hcutPartition)

set_option linter.style.longLine false in
/-- Claim `S2-r14-repeated-tail-cut-source`, local-sector no-cut form.

The r11 third-neighbour repeated-tail cut-partition source already forces the
actual local-sector rows for the raw exterior walk.  For each actual frontier
carrier vertex, choose the predecessor and successor raw tails as the two
selected heads.  A third actual carrier neighbour would invoke the r11
cut-partition callback, and that concrete cut partition contradicts
`inputs.noCutVertex`.

This is a strict source lowering of the third-neighbour branch: it keeps the
same raw exterior face walk, uses only the actual open-segment frontier row for
the two selected incidences, and introduces no final boundary cycle, W32
composer, arbitrary carrier cycle, or induced frontier graph. -/
noncomputable def
    S2_r14_localSectorRows_of_rawOrbit_thirdNeighborRepeatedTailCutPartitions_noCut
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (raw_pred_succ_tail_ne :
      forall k : Fin O.period,
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail)
    (thirdCutPartitions :
      S2_r11_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource
        (inputs := inputs) O) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  classical
  intro a
  let k : Fin O.period := Classical.choose (frontier_vertex_tail_coverage a)
  have hk : (O.dart k).tail = a.1 :=
    Classical.choose_spec (frontier_vertex_tail_coverage a)
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  let left : Fin n := (O.dart pred).tail
  let right : Fin n := (O.dart succ).tail
  have hsucc_pred : PlanarInterface.cyclicSucc O.period_pos pred = k := by
    simp [pred, PlanarInterface.cyclicSucc_cyclicPred O.period_pos k]
  have left_edge :
      (a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hraw :=
      rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm
        (C := C) (inputs := inputs) O edge_openSegment_frontier pred
    rcases hraw with hforward | hreverse
    · exact Or.inr (by
        simpa [left, pred, hsucc_pred, hk] using hforward)
    · exact Or.inl (by
        simpa [left, pred, hsucc_pred, hk] using hreverse)
  have right_edge :
      (a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hraw :=
      rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm
        (C := C) (inputs := inputs) O edge_openSegment_frontier k
    rcases hraw with hforward | hreverse
    · exact Or.inl (by
        simpa [right, succ, hk] using hforward)
    · exact Or.inr (by
        simpa [right, succ, hk] using hreverse)
  have heads_ne : left ≠ right := by
    intro h
    exact
      raw_pred_succ_tail_ne k
        (by simpa [left, right, pred, succ] using h)
  refine
    { left := left
      right := right
      left_edge := left_edge
      right_edge := right_edge
      heads_ne := heads_ne
      only := ?_ }
  intro b hb
  by_cases hb_left : b.1 = left
  · exact Or.inl hb_left
  by_cases hb_right : b.1 = right
  · exact Or.inr hb_right
  exfalso
  rcases
      thirdCutPartitions a b hb k hk
        (by simpa [left, pred] using hb_left)
        (by simpa [right, succ] using hb_right) with
    ⟨_j, _hkj, _hj_tail, hcutPartition⟩
  exact inputs.noCutVertex hcutPartition

set_option linter.style.longLine false in
/-- Family form of the r14 local-sector no-cut lowering from the r11
third-neighbour repeated-tail cut-partition source. -/
theorem
    S2_r14_localSectorRowsFamily_of_rawOrbit_thirdNeighborRepeatedTailCutPartitions_noCut
    (rawRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                (forall k : Fin O.period,
                  forall p : PlanarInterface.Point,
                    PlanarInterface.InOpenSegment p
                      ((canonicalGraph C).point (O.dart k).tail)
                      ((canonicalGraph C).point
                        (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
                    p ∈
                      frontier
                        (unboundedExteriorComponentRows C inputs).exterior) ∧
                (forall a : {v : Fin m //
                    v ∈ unboundedFrontierVertexSet C inputs},
                  Exists fun k : Fin O.period => (O.dart k).tail = a.1) ∧
                (forall k : Fin O.period,
                  (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
                    (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∧
                S2_r11_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource
                  (inputs := inputs) O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Nonempty
          (forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) := by
  intro m C inputs
  rcases rawRows C inputs with
    ⟨R, start, O, edgeRows, tailCoverage, predSuccNe, thirdPartitions⟩
  exact ⟨
    S2_r14_localSectorRows_of_rawOrbit_thirdNeighborRepeatedTailCutPartitions_noCut
      (C := C) (inputs := inputs) O edgeRows tailCoverage predSuccNe
      thirdPartitions⟩

set_option linter.style.longLine false in
/-- The r12 finite deleted-tail separation source supplies the r11 concrete
cut-partition residual.

This is the checked lowering requested by r12: the only construction step is
the existing minimal repeated-tail cut-row constructor from the two open-arc
witnesses and deleted-tail nonreachability, followed by
`toCutVertexPartition`. -/
theorem
    S2_r12_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource_of_minimalDeletedTailSeparation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (source :
      S2_r12_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource
        (inputs := inputs) O) :
    S2_r11_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource
      (inputs := inputs) O := by
  intro a b hb k hk hb_pred hb_succ
  rcases source a b hb k hk hb_pred hb_succ with
    ⟨j, hkj, hj_tail, hsep⟩
  rcases hsep with ⟨left, right, hunreachable⟩
  let cutRows :
      RawFaceSuccOrbitRepeatedTailExteriorCutRows
        (inputs := inputs) O k j :=
    { left_index := left.1
      left_index_mem := left.2.1
      left_index_ne_cut := left.2.2
      right_index := right.1
      right_index_mem := right.2.1
      right_index_ne_cut := right.2.2
      unreachable_after_delete := hunreachable }
  exact ⟨j, hkj, hj_tail, ⟨cutRows.toCutVertexPartition⟩⟩

set_option linter.style.longLine false in
/-- The same r12 finite-plane source also supplies the stronger r7j cut-row
residual, when a downstream consumer still asks for
`RawFaceSuccOrbitRepeatedTailExteriorCutRows`. -/
theorem
    S2_r12_rawFaceWalkThirdCarrierNeighborRepeatedTailCutRowsSource_of_minimalDeletedTailSeparation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (source :
      S2_r12_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource
        (inputs := inputs) O) :
    S2_r7j_rawFaceWalkThirdCarrierNeighborRepeatedTailCutSource
      (inputs := inputs) O := by
  intro a b hb k hk hb_pred hb_succ
  rcases source a b hb k hk hb_pred hb_succ with
    ⟨j, hkj, hj_tail, hsep⟩
  rcases hsep with ⟨left, right, hunreachable⟩
  refine ⟨j, hkj, hj_tail, ⟨?_⟩⟩
  exact
    { left_index := left.1
      left_index_mem := left.2.1
      left_index_ne_cut := left.2.2
      right_index := right.1
      right_index_mem := right.2.1
      right_index_ne_cut := right.2.2
      unreachable_after_delete := hunreachable }

set_option linter.style.longLine false in
/-- q24 canonical cyclic-successor deleted-tail nonreachability source for one
raw face-successor orbit. -/
abbrev S2_q24_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource
    {C : _root_.UDConfig n}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start) : Prop :=
  forall {i j : Fin O.period}
    (hij : i ≠ j)
    (htail : (O.dart i).tail = (O.dart j).tail),
      ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
          ({(O.dart i).tail}ᶜ : Set (Fin n))).Reachable
          ⟨(O.dart (PlanarInterface.cyclicSucc O.period_pos i)).tail, by
            intro h
            exact
              (rawFaceSuccOrbit_tail_ne_cyclicSucc O i)
                (by simpa using h.symm)⟩
          ⟨(O.dart (PlanarInterface.cyclicSucc O.period_pos j)).tail, by
            intro h
            exact
              (rawFaceSuccOrbit_tail_ne_cyclicSucc O j)
                (htail.symm.trans h.symm)⟩

set_option linter.style.longLine false in
/-- q24 cut-partition source for the canonical cyclic successors of a repeated
tail on the same raw face-successor orbit. -/
abbrev S2_q24_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource
    {C : _root_.UDConfig n}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start) : Prop :=
  forall {i j : Fin O.period}
    (_hij : i ≠ j)
    (_htail : (O.dart i).tail = (O.dart j).tail),
      Nonempty
        (PSigma fun P : CutVertexInterface.CutVertexPartition C =>
          P.cut = (O.dart i).tail ∧
            (((O.dart (PlanarInterface.cyclicSucc O.period_pos i)).tail ∈
                  P.left ∧
                (O.dart (PlanarInterface.cyclicSucc O.period_pos j)).tail ∈
                  P.right) ∨
              ((O.dart (PlanarInterface.cyclicSucc O.period_pos i)).tail ∈
                  P.right ∧
                (O.dart (PlanarInterface.cyclicSucc O.period_pos j)).tail ∈
                  P.left)))

set_option linter.style.longLine false in
/-- Claim `S2-q24-cyclic-cut-source`, deleted-tail nonreachability form.

For the exact raw orbit under discussion, the canonical cyclic-successor
deleted-tail nonreachability primitive constructs the corresponding concrete
cut partition.  This is only the finite deleted-tail graph eraser; it does not
use boundary-cycle, actual-sector, W32, induced-frontier, arbitrary-cycle,
convex-hull, endpoint-all-adjacent, or identity-order data. -/
noncomputable def
    S2_q24_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource_of_deletedTailNonreachability
    {C : _root_.UDConfig n}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (nonreachability :
      S2_q24_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource O) :
    S2_q24_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource O := by
  intro i j hij htail
  let left : Fin n :=
    (O.dart (PlanarInterface.cyclicSucc O.period_pos i)).tail
  let right : Fin n :=
    (O.dart (PlanarInterface.cyclicSucc O.period_pos j)).tail
  let cut : Fin n := (O.dart i).tail
  have hleft_ne_cut : left ≠ cut := by
    intro h
    exact
      (rawFaceSuccOrbit_tail_ne_cyclicSucc O i)
        (by simpa [left, cut] using h.symm)
  have hright_ne_cut : right ≠ cut := by
    intro h
    exact
      (rawFaceSuccOrbit_tail_ne_cyclicSucc O j)
        (by simpa [right, cut] using htail.symm.trans h.symm)
  have hnonreach :
      ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
          ({cut}ᶜ : Set (Fin n))).Reachable
          ⟨left, by simpa [cut] using hleft_ne_cut⟩
          ⟨right, by simpa [cut] using hright_ne_cut⟩ := by
    simpa [left, right, cut] using
      nonreachability (i := i) (j := j) hij htail
  let rows : RepeatedExteriorBoundarySeparationRows C
      (fun k : Fin O.period => (O.dart k).tail) i j :=
    repeatedExteriorBoundarySeparationRows_of_unreachable_after_delete
      (C := C)
      (vertex := fun k : Fin O.period => (O.dart k).tail)
      (i := i) (j := j)
      htail hij left right
      (by simpa [cut] using hleft_ne_cut)
      (by simpa [cut] using hright_ne_cut)
      (by simpa [cut] using hnonreach)
  let P : CutVertexInterface.CutVertexPartition C := rows.toCutVertexPartition
  have hleft_side : rows.side left = true := by
    simpa [rows] using rows.left_witness_side
  have hright_side : rows.side right = false := by
    simpa [rows] using rows.right_witness_side
  refine ⟨⟨P, ?_, ?_⟩⟩
  · simp [P, RepeatedExteriorBoundarySeparationRows.toCutVertexPartition, rows]
  · left
    have hleft_mem :
        left ∈ rows.toCutVertexPartition.left := by
      simp only [RepeatedExteriorBoundarySeparationRows.toCutVertexPartition,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simpa [cut] using hleft_ne_cut, hleft_side⟩
    have hright_mem :
        right ∈ rows.toCutVertexPartition.right := by
      simp only [RepeatedExteriorBoundarySeparationRows.toCutVertexPartition,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simpa [cut] using hright_ne_cut, hright_side⟩
    constructor
    · simpa [P, left] using hleft_mem
    · simpa [P, right] using hright_mem

set_option linter.style.longLine false in
/-- Claim `S2-q41-repeated-tail-cut-worker`, actual exterior-arc form.

Pair-level repeated raw-tail actual exterior arc rows already separate the two
canonical cyclic-successor tails after deleting the repeated tail.  The proof
uses the finite forward-arc side labelling carried by
`RawFaceSuccOrbitRepeatedTailActualExteriorArcRows`; it does not use no-cut
contradiction, actual-sector rows, final boundary-cycle rows, W32 consumers,
induced-frontier shortcuts, arbitrary cycles, or endpoint frontier-component
separation. -/
noncomputable def
    S2_q41_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource_of_repeatedTailActualExteriorArcRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (arcRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
            (inputs := inputs) O i j) :
    S2_q24_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource O := by
  intro i j hij htail
  let pairRows := arcRows (i := i) (j := j) hij htail
  let boundaryRows :
      RepeatedExteriorBoundaryArcSeparationRows C
        (fun k : Fin O.period => (O.dart k).tail) i j :=
    pairRows.toRepeatedExteriorBoundaryArcSeparationRows hij htail
  let vertex : Fin O.period -> Fin n := fun k => (O.dart k).tail
  let cut : Fin n := (O.dart i).tail
  let left : Fin n :=
    (O.dart (PlanarInterface.cyclicSucc O.period_pos i)).tail
  let right : Fin n :=
    (O.dart (PlanarInterface.cyclicSucc O.period_pos j)).tail
  let side : Fin n -> Bool := repeatedBoundaryArcSide vertex i j
  have hleft_succ_ne :
      PlanarInterface.cyclicSucc O.period_pos i ≠ j := by
    intro hsucc
    have htail_succ :
        (O.dart i).tail =
          (O.dart (PlanarInterface.cyclicSucc O.period_pos i)).tail := by
      simpa [hsucc] using htail
    exact (rawFaceSuccOrbit_tail_ne_cyclicSucc O i) htail_succ
  have hleft_arc :
      cyclicForwardOpenArc i j
        (PlanarInterface.cyclicSucc O.period_pos i) :=
    cyclicForwardOpenArc_cyclicSucc_left O.period_pos hleft_succ_ne
  have hleft_side : side left = true := by
    exact
      repeatedBoundaryArcSide_eq_true_iff.2
        ⟨PlanarInterface.cyclicSucc O.period_pos i, hleft_arc, rfl⟩
  have hright_succ_ne :
      PlanarInterface.cyclicSucc O.period_pos j ≠ i := by
    intro hsucc
    have htail_succ :
        (O.dart j).tail =
          (O.dart (PlanarInterface.cyclicSucc O.period_pos j)).tail := by
      simp [hsucc, htail.symm]
    exact (rawFaceSuccOrbit_tail_ne_cyclicSucc O j) htail_succ
  have hright_arc :
      cyclicForwardOpenArc j i
        (PlanarInterface.cyclicSucc O.period_pos j) :=
    cyclicForwardOpenArc_cyclicSucc_left O.period_pos hright_succ_ne
  have hright_image :
      repeatedBoundaryArcImage vertex j i right := by
    exact
      ⟨PlanarInterface.cyclicSucc O.period_pos j, hright_arc, by
        simp [vertex, right]⟩
  have hleft_ne_cut : left ≠ cut := by
    intro h
    exact
      (rawFaceSuccOrbit_tail_ne_cyclicSucc O i)
        (by simpa [left, cut] using h.symm)
  have hright_ne_cut : right ≠ cut := by
    intro h
    exact
      (rawFaceSuccOrbit_tail_ne_cyclicSucc O j)
        (by simpa [right, cut] using htail.symm.trans h.symm)
  have hright_side : side right = false := by
    exact
      repeatedBoundaryArcSide_eq_false_iff.2
        (boundaryRows.reverse_arc_not_forward_off_cut
          (by simpa [vertex, cut] using hright_ne_cut)
          (by simpa [vertex, right] using hright_image))
  let boolRows : BoolSideSeparationRows C :=
    { cut := cut
      side := side
      trueWitness := left
      trueWitness_ne_cut := hleft_ne_cut
      trueWitness_side := hleft_side
      falseWitness := right
      falseWitness_ne_cut := hright_ne_cut
      falseWitness_side := hright_side
      anticomplete := by
        intro a b ha_cut hb_cut ha_side hb_side
        have ha_left :
            repeatedBoundaryArcImage vertex i j a :=
          repeatedBoundaryArcSide_eq_true_iff.1 ha_side
        have hb_not_left :
            ¬ repeatedBoundaryArcImage vertex i j b :=
          repeatedBoundaryArcSide_eq_false_iff.1 hb_side
        have hb_right :
            repeatedBoundaryArcImage vertex j i b := by
          rcases
              boundaryRows.cover_noncut b
                (by simpa [vertex, cut] using hb_cut) with
            hb_left | hb_right
          · exact False.elim (hb_not_left hb_left)
          · exact hb_right
        exact
          boundaryRows.arcs_anticomplete ha_left hb_right
            (by simpa [vertex, cut] using ha_cut)
            (by simpa [vertex, cut] using hb_cut) }
  change
    ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
        ({cut}ᶜ : Set (Fin n))).Reachable
        ⟨left, by simpa [left, cut] using hleft_ne_cut⟩
        ⟨right, by simpa [right, cut] using hright_ne_cut⟩
  simpa [boolRows] using
    BoolSideSeparationRows.not_reachable_true_false_after_delete boolRows

set_option linter.style.longLine false in
/-- q41 cut-partition form from pair-level repeated raw-tail actual exterior
arc rows.

This is the same finite arc-side separation as the q41 nonreachability form,
followed by the q24 deleted-tail nonreachability-to-cut-partition eraser. -/
noncomputable def
    S2_q41_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource_of_repeatedTailActualExteriorArcRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (arcRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
            (inputs := inputs) O i j) :
    S2_q24_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource O :=
  S2_q24_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource_of_deletedTailNonreachability
    (C := C) O
    (S2_q41_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource_of_repeatedTailActualExteriorArcRows
      (C := C) (inputs := inputs) (O := O) arcRows)

set_option linter.style.longLine false in
/-- q38 pairwise minimal deleted-tail separation source for one raw
face-successor orbit.

This names only the finite graph obligation inside
`RawFaceSuccOrbitRepeatedTailExteriorCutRows`: for each repeated raw tail,
choose one non-cut tail on each cyclic open side and prove those two tails are
not reachable after deleting the repeated tail. -/
structure S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
    {C : _root_.UDConfig n}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start) where
  rows :
    forall {i j : Fin O.period},
    i ≠ j ->
    (O.dart i).tail = (O.dart j).tail ->
      PSigma fun left :
          {l : Fin O.period //
            cyclicForwardOpenArc i j l ∧
              (O.dart l).tail ≠ (O.dart i).tail} =>
        PSigma fun right :
            {r : Fin O.period //
              cyclicForwardOpenArc j i r ∧
                (O.dart r).tail ≠ (O.dart i).tail} =>
          ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
              ({(O.dart i).tail}ᶜ : Set (Fin n))).Reachable
              ⟨(O.dart left.1).tail, by simpa using left.2.2⟩
              ⟨(O.dart right.1).tail, by simpa using right.2.2⟩

set_option linter.style.longLine false in
/-- Pairwise exterior cut rows erase to the q38 minimal deleted-tail source by
forgetting the cut-partition wrapper. -/
def
    S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource_of_repeatedTailExteriorCutRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j) :
    S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource O where
  rows := by
    intro i j hij htail
    let rows := cutRows hij htail
    refine
      ⟨⟨rows.left_index, rows.left_index_mem, rows.left_index_ne_cut⟩,
        ⟨⟨rows.right_index, rows.right_index_mem, rows.right_index_ne_cut⟩,
          ?_⟩⟩
    simpa [rows] using rows.unreachable_after_delete

set_option linter.style.longLine false in
/-- The q38 minimal deleted-tail source rebuilds the pointwise exterior cut
rows when a downstream consumer still expects the older row shape. -/
def
    S2_q38_repeatedTailExteriorCutRows_of_pairwiseMinimalDeletedTailSeparationSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (source :
      S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource O) :
    forall {i j : Fin O.period},
      i ≠ j ->
      (O.dart i).tail = (O.dart j).tail ->
        RawFaceSuccOrbitRepeatedTailExteriorCutRows
          (inputs := inputs) O i j := by
  intro i j hij htail
  rcases source.rows hij htail with ⟨left, right, hnonreach⟩
  exact
    { left_index := left.1
      left_index_mem := left.2.1
      left_index_ne_cut := left.2.2
      right_index := right.1
      right_index_mem := right.2.1
      right_index_ne_cut := right.2.2
      unreachable_after_delete := hnonreach }

set_option linter.style.longLine false in
/-- Pairwise repeated-tail exterior cut rows strictly lower to the existing
q24 cyclic-successor deleted-tail nonreachability source.

The proof uses only the direct cut-partition eraser on the supplied cut row and
the `inputs.noCutVertex` field, so it introduces no actual-sector, final
boundary-cycle, W32, induced-frontier, arbitrary-cycle, or endpoint-shortcut
premise. -/
theorem
    S2_q38_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource_of_repeatedTailExteriorCutRows_noCut
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j) :
    S2_q24_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource O := by
  intro i j hij htail
  exact False.elim ((cutRows hij htail).false_of_noCutVertex)

set_option linter.style.longLine false in
/-- q38 minimal deleted-tail separation also lowers to the existing q24
cyclic-successor deleted-tail nonreachability source through the same no-cut
eraser. -/
theorem
    S2_q38_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource_of_pairwiseMinimalDeletedTailSeparation_noCut
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (source :
      S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource O) :
    S2_q24_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource O :=
  S2_q38_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource_of_repeatedTailExteriorCutRows_noCut
    (C := C) (inputs := inputs)
    (S2_q38_repeatedTailExteriorCutRows_of_pairwiseMinimalDeletedTailSeparationSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Pairwise repeated-tail exterior cut rows supply the q24 cyclic-successor
cut-partition source by first erasing to the smaller nonreachability row. -/
noncomputable def
    S2_q38_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource_of_repeatedTailExteriorCutRows_noCut
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (cutRows :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          RawFaceSuccOrbitRepeatedTailExteriorCutRows
            (inputs := inputs) O i j) :
    S2_q24_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource O :=
  S2_q24_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource_of_deletedTailNonreachability
    (C := C) O
    (S2_q38_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource_of_repeatedTailExteriorCutRows_noCut
      (C := C) (inputs := inputs) cutRows)

set_option linter.style.longLine false in
/-- q38 minimal deleted-tail separation supplies the q24 cyclic-successor
cut-partition source through the pointwise cut-row eraser. -/
noncomputable def
    S2_q38_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource_of_pairwiseMinimalDeletedTailSeparation_noCut
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (source :
      S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource O) :
    S2_q24_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource O :=
  S2_q38_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource_of_repeatedTailExteriorCutRows_noCut
    (C := C) (inputs := inputs) O
    (S2_q38_repeatedTailExteriorCutRows_of_pairwiseMinimalDeletedTailSeparationSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- r12 composed with the existing r11 carrier-cut handoff. -/
theorem
    S2_r12_carrierCutFieldwise_of_rawOrbit_thirdNeighborMinimalDeletedTailSeparation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (raw_pred_succ_tail_ne :
      forall k : Fin O.period,
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail)
    (thirdMinimalSeparation :
      S2_r12_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource
        (inputs := inputs) O) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
      (C := C) inputs :=
  S2_r11_carrierCutFieldwise_of_rawOrbit_thirdNeighborRepeatedTailCutPartitions
    (C := C) (inputs := inputs) O
    edge_openSegment_frontier frontier_vertex_tail_coverage raw_pred_succ_tail_ne
    (S2_r12_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource_of_minimalDeletedTailSeparation
      (C := C) (inputs := inputs) thirdMinimalSeparation)

set_option linter.style.longLine false in
/-- Family form of the r12 finite-plane handoff to the carrier-cut field. -/
theorem
    S2_r12_carrierCutFieldwiseFamily_of_rawOrbit_thirdNeighborMinimalDeletedTailSeparation
    (rawRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                (forall k : Fin O.period,
                  forall p : PlanarInterface.Point,
                    PlanarInterface.InOpenSegment p
                      ((canonicalGraph C).point (O.dart k).tail)
                      ((canonicalGraph C).point
                        (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
                    p ∈
                      frontier
                        (unboundedExteriorComponentRows C inputs).exterior) ∧
                (forall a : {v : Fin m //
                    v ∈ unboundedFrontierVertexSet C inputs},
                  Exists fun k : Fin O.period => (O.dart k).tail = a.1) ∧
                (forall k : Fin O.period,
                  (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
                    (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∧
                S2_r12_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource
                  (inputs := inputs) O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          (C := C) inputs := by
  intro m C inputs
  rcases rawRows C inputs with
    ⟨R, start, O, edgeRows, tailCoverage, predSuccNe, thirdSeparation⟩
  exact
    S2_r12_carrierCutFieldwise_of_rawOrbit_thirdNeighborMinimalDeletedTailSeparation
      (C := C) (inputs := inputs) O edgeRows tailCoverage predSuccNe
      thirdSeparation

set_option linter.style.longLine false in
/-- q36 carrier-cut handoff for the selected raw-orbit lane.

This strictly lowers the r12 source by splitting it into an index-only
third-neighbour repeated-tail branch and the minimal deleted-tail separation
source for repeated tails on the same raw orbit. -/
theorem
    S2_q36_carrierCutFieldwise_of_rawOrbit_thirdNeighborRepeatedTailIndex_minimalDeletedTailSeparation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (raw_pred_succ_tail_ne :
      forall k : Fin O.period,
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail)
    (thirdRepeatedTail :
      S2_q36_rawFaceWalkThirdCarrierNeighborRepeatedTailIndexSource
        (inputs := inputs) O)
    (minimalSeparation :
      forall {i j : Fin O.period},
        i ≠ j ->
        (O.dart i).tail = (O.dart j).tail ->
          Exists fun left :
              {l : Fin O.period //
                cyclicForwardOpenArc i j l ∧
                  (O.dart l).tail ≠ (O.dart i).tail} =>
            Exists fun right :
                {r : Fin O.period //
                  cyclicForwardOpenArc j i r ∧
                    (O.dart r).tail ≠ (O.dart i).tail} =>
              ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
                  ({(O.dart i).tail}ᶜ : Set (Fin n))).Reachable
                  ⟨(O.dart left.1).tail, by simpa using left.2.2⟩
                  ⟨(O.dart right.1).tail, by simpa using right.2.2⟩) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
      (C := C) inputs :=
  S2_r12_carrierCutFieldwise_of_rawOrbit_thirdNeighborMinimalDeletedTailSeparation
    (C := C) (inputs := inputs) O
    edge_openSegment_frontier frontier_vertex_tail_coverage raw_pred_succ_tail_ne
    (S2_q36_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource_of_repeatedTailIndex_minimalDeletedTailSeparation
      (C := C) (inputs := inputs) thirdRepeatedTail minimalSeparation)

set_option linter.style.longLine false in
/-- Family form of the q36 raw-orbit carrier-cut handoff. -/
theorem
    S2_q36_carrierCutFieldwiseFamily_of_rawOrbit_thirdNeighborRepeatedTailIndex_minimalDeletedTailSeparation
    (rawRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                (forall k : Fin O.period,
                  forall p : PlanarInterface.Point,
                    PlanarInterface.InOpenSegment p
                      ((canonicalGraph C).point (O.dart k).tail)
                      ((canonicalGraph C).point
                        (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
                    p ∈
                      frontier
                        (unboundedExteriorComponentRows C inputs).exterior) ∧
                (forall a : {v : Fin m //
                    v ∈ unboundedFrontierVertexSet C inputs},
                  Exists fun k : Fin O.period => (O.dart k).tail = a.1) ∧
                (forall k : Fin O.period,
                  (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
                    (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∧
                S2_q36_rawFaceWalkThirdCarrierNeighborRepeatedTailIndexSource
                  (inputs := inputs) O ∧
                (forall {i j : Fin O.period},
                  i ≠ j ->
                  (O.dart i).tail = (O.dart j).tail ->
                    Exists fun left :
                        {l : Fin O.period //
                          cyclicForwardOpenArc i j l ∧
                            (O.dart l).tail ≠ (O.dart i).tail} =>
                      Exists fun right :
                          {r : Fin O.period //
                            cyclicForwardOpenArc j i r ∧
                              (O.dart r).tail ≠ (O.dart i).tail} =>
                        ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
                            ({(O.dart i).tail}ᶜ : Set (Fin m))).Reachable
                            ⟨(O.dart left.1).tail, by simpa using left.2.2⟩
                            ⟨(O.dart right.1).tail, by simpa using right.2.2⟩)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          (C := C) inputs := by
  intro m C inputs
  rcases rawRows C inputs with
    ⟨R, start, O, edgeRows, tailCoverage, predSuccNe,
      thirdRepeatedTail, minimalSeparation⟩
  exact
    S2_q36_carrierCutFieldwise_of_rawOrbit_thirdNeighborRepeatedTailIndex_minimalDeletedTailSeparation
      (C := C) (inputs := inputs) O edgeRows tailCoverage predSuccNe
      thirdRepeatedTail minimalSeparation

set_option linter.style.longLine false in
/-- Raw exterior face-walk data plus the r7j repeated-tail residual supplies
the r7i fieldwise carrier-cut source.

The selected heads at a frontier vertex are the predecessor and successor
tails of a raw occurrence of that vertex.  Consecutive raw edges are converted
to genuine `unboundedFrontierEdgeSet` incidences by the stored open-segment
frontier row; any third carrier neighbour is then handed to the r7j residual,
which returns the repeated-tail cut row consumed by r7i. -/
theorem
    S2_r7j_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource_of_rawOrbit_thirdNeighborRepeatedTailCutSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    (O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start)
    (edge_openSegment_frontier :
      forall k : Fin O.period,
        forall p : PlanarInterface.Point,
          PlanarInterface.InOpenSegment p
            ((canonicalGraph C).point (O.dart k).tail)
            ((canonicalGraph C).point
              (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
          p ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (frontier_vertex_tail_coverage :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin O.period => (O.dart k).tail = a.1)
    (raw_pred_succ_tail_ne :
      forall k : Fin O.period,
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail)
    (thirdCutRows :
      S2_r7j_rawFaceWalkThirdCarrierNeighborRepeatedTailCutSource
        (inputs := inputs) O) :
    S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource
      (C := C) inputs := by
  classical
  intro a
  let k : Fin O.period := Classical.choose (frontier_vertex_tail_coverage a)
  have hk : (O.dart k).tail = a.1 :=
    Classical.choose_spec (frontier_vertex_tail_coverage a)
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  let left : Fin n := (O.dart pred).tail
  let right : Fin n := (O.dart succ).tail
  have hsucc_pred : PlanarInterface.cyclicSucc O.period_pos pred = k := by
    simp [pred, PlanarInterface.cyclicSucc_cyclicPred O.period_pos k]
  have left_edge :
      (a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
        (left, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hraw :=
      rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm
        (C := C) (inputs := inputs) O edge_openSegment_frontier pred
    rcases hraw with hforward | hreverse
    · exact Or.inr (by
        simpa [left, pred, hsucc_pred, hk] using hforward)
    · exact Or.inl (by
        simpa [left, pred, hsucc_pred, hk] using hreverse)
  have right_edge :
      (a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
        (right, a.1) ∈ unboundedFrontierEdgeSet C inputs := by
    have hraw :=
      rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm
        (C := C) (inputs := inputs) O edge_openSegment_frontier k
    rcases hraw with hforward | hreverse
    · exact Or.inl (by
        simpa [right, succ, hk] using hforward)
    · exact Or.inr (by
        simpa [right, succ, hk] using hreverse)
  have heads_ne : left ≠ right := by
    intro h
    exact
      raw_pred_succ_tail_ne k
        (by simpa [left, right, pred, succ] using h)
  refine ⟨left, right, left_edge, right_edge, heads_ne, ?_⟩
  intro b hb hb_left hb_right
  rcases
      thirdCutRows a b hb k hk
        (by simpa [left, pred] using hb_left)
        (by simpa [right, succ] using hb_right) with
    ⟨j, hkj, hj_tail, hcutRows⟩
  refine ⟨R, start, O, k, j, hkj, ?_, hk, hcutRows⟩
  exact hk.trans hj_tail.symm

set_option linter.style.longLine false in
/-- Family form of the r7j raw-orbit repeated-tail handoff. -/
theorem
    S2_r7j_rawFaceWalkRepeatedTailCarrierCutFieldwiseFamily_of_rawOrbit_thirdNeighborRepeatedTailCutSource
    (rawRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O :
                UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                (forall k : Fin O.period,
                  forall p : PlanarInterface.Point,
                    PlanarInterface.InOpenSegment p
                      ((canonicalGraph C).point (O.dart k).tail)
                      ((canonicalGraph C).point
                        (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ->
                    p ∈
                      frontier
                        (unboundedExteriorComponentRows C inputs).exterior) ∧
                (forall a : {v : Fin m //
                    v ∈ unboundedFrontierVertexSet C inputs},
                  Exists fun k : Fin O.period => (O.dart k).tail = a.1) ∧
                (forall k : Fin O.period,
                  (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail ≠
                    (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∧
                S2_r7j_rawFaceWalkThirdCarrierNeighborRepeatedTailCutSource
                  (inputs := inputs) O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource
          (C := C) inputs := by
  intro m C inputs
  rcases rawRows C inputs with
    ⟨R, start, O, edgeRows, tailCoverage, predSuccNe, thirdRows⟩
  exact
    S2_r7j_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource_of_rawOrbit_thirdNeighborRepeatedTailCutSource
      (C := C) (inputs := inputs) O edgeRows tailCoverage predSuccNe
      thirdRows

set_option linter.style.longLine false in
/-- Local-sector rows give a checked, vacuous r7i source.

This is not the preferred primitive proof of a repeated-tail cut; it is a
sanity reducer showing that r7i has the right variance.  If the actual local
sector rows are already known, there is no third carrier neighbour, so the
third-neighbour branch of the r7i source is discharged by contradiction. -/
theorem
    S2_r7j_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource_of_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource
      (C := C) inputs := by
  intro a
  let rows := localSectorRows a
  refine
    ⟨rows.left, rows.right, rows.left_edge, rows.right_edge,
      rows.heads_ne, ?_⟩
  intro b hb hb_left hb_right
  rcases rows.only b hb with hb_left_eq | hb_right_eq
  · exact False.elim (hb_left hb_left_eq)
  · exact False.elim (hb_right hb_right_eq)

set_option linter.style.longLine false in
/-- Exact local-sector residual for the r7i raw repeated-tail source.

The reverse direction is the existing vacuous local-sector constructor.  The
forward direction is the useful local content: any carrier neighbour different
from the two selected heads would trigger a raw repeated-tail cut row, whose
cut-partition eraser contradicts `inputs.noCutVertex`. -/
theorem
    S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource_iff_nonempty_localSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource
        (C := C) inputs ↔
      Nonempty
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a) := by
  constructor
  · intro source
    refine ⟨?_⟩
    intro a
    let left : Fin n := Classical.choose (source a)
    let right : Fin n := Classical.choose (Classical.choose_spec (source a))
    have hspec :
        ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
            (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
          ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
              (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
            left ≠ right ∧
              forall b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
                (unboundedFrontierCarrierGraph C inputs).Adj a b ->
                  b.1 ≠ left ->
                    b.1 ≠ right ->
                      Exists fun R : UnitDistanceRotationSystem C =>
                        Exists fun start : UnitDistanceDart C =>
                          Exists fun O :
                              UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                            Exists fun i : Fin O.period =>
                              Exists fun j : Fin O.period =>
                                i ≠ j ∧
                                  (O.dart i).tail = (O.dart j).tail ∧
                                    (O.dart i).tail = a.1 ∧
                                      Nonempty
                                        (RawFaceSuccOrbitRepeatedTailExteriorCutRows
                                          (inputs := inputs) O i j) := by
      dsimp [left, right]
      exact Classical.choose_spec (Classical.choose_spec (source a))
    refine
      { left := left
        right := right
        left_edge := hspec.1
        right_edge := hspec.2.1
        heads_ne := hspec.2.2.1
        only := ?_ }
    intro b hb
    by_cases hb_left : b.1 = left
    · exact Or.inl hb_left
    by_cases hb_right : b.1 = right
    · exact Or.inr hb_right
    exfalso
    rcases hspec.2.2.2 b hb hb_left hb_right with
      ⟨R, start, O, i, j, _hij, _htail, _hcut, hcutRows⟩
    rcases hcutRows with ⟨cutRows⟩
    exact inputs.noCutVertex ⟨cutRows.toCutVertexPartition⟩
  · rintro ⟨localSectorRows⟩
    exact
      S2_r7j_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource_of_localSectorRows
        (C := C) (inputs := inputs) localSectorRows

set_option linter.style.longLine false in
/-- Claim `S2-subagent-r7i-carrier-cut-source-20260521-current3`.

The r7i raw repeated-tail carrier-cut source is reduced to the actual local
selected-edge/no-third-germ primitive.  The local no-third-germ rows first
erase to pointwise local-sector rows, and the local-sector constructor supplies
the raw repeated-tail source. -/
theorem
    S2_subagent_r7i_carrier_cut_source_20260521_current3_of_localSelectedNoThirdGermSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource
      (C := C) inputs :=
  S2_r7j_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource_of_localSectorRows
    (C := C) (inputs := inputs)
    (unboundedFrontierCarrierLocalSectorRows_of_localSelectedNoThirdGermSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of
`S2_subagent_r7i_carrier_cut_source_20260521_current3_of_localSelectedNoThirdGermSource`.

The first remaining source below r7i is now the pointwise actual local
selected-edge/no-third-germ primitive, not bare
`FinitePlanarOuterComponentInputs`. -/
theorem
    S2_subagent_r7i_carrier_cut_source_20260521_current3
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource
          (C := C) inputs := by
  intro m C inputs
  exact
    S2_subagent_r7i_carrier_cut_source_20260521_current3_of_localSelectedNoThirdGermSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact current3 residual for the r7i carrier-cut leaf.

The forward direction uses the checked raw repeated-tail/no-cut contradiction
to recover pointwise local-sector rows, then erases those rows to the current
actual selected-edge/no-third-germ source.  The reverse direction is the
current3 constructor above. -/
theorem
    S2_subagent_r7i_carrier_cut_source_20260521_current3_nonempty_iff_localSelectedNoThirdGermSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource
        (C := C) inputs ↔
      Nonempty
        (UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) := by
  constructor
  · intro source
    rcases
        (S2_r7i_rawFaceWalkRepeatedTailCarrierCutFieldwiseSource_iff_nonempty_localSectorRows
          (C := C) (inputs := inputs)).1 source with
      ⟨localSectorRows⟩
    exact
      ⟨localSelectedNoThirdGermSource_of_localSectorRows
        (C := C) (inputs := inputs) localSectorRows⟩
  · rintro ⟨source⟩
    exact
      S2_subagent_r7i_carrier_cut_source_20260521_current3_of_localSelectedNoThirdGermSource
        (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Claim `S2-r42-carrier-cut-local-separation-reducer-20260521r42`.

The live selected-neighbour local source is lowered to the already existing
finite-plane deleted-neighbour separation primitive from r30.  This theorem
stays below actual exterior-sector rows, final boundary cycles, and W32:
it only repackages the primitive Boolean side separation as the checked
`UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource`. -/
noncomputable def
    S2_r42_deleted_neighbor_local_separation_input_source_of_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
      C inputs :=
  S2_r30_deleted_neighbor_local_separation_source_20260521r30_of_finitePlaneLocalSeparationPrimitive
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of the r42 local-separation reducer. -/
noncomputable def
    S2_r42_deleted_neighbor_local_separation_input_source_family_of_finitePlaneLocalSeparationPrimitive
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_r42_deleted_neighbor_local_separation_input_source_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact r42 residual for the live local-separation source. -/
theorem
    S2_r42_deleted_neighbor_local_separation_input_source_nonempty_iff_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
          C inputs) ↔
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs :=
  S2_r30_deleted_neighbor_local_separation_source_nonempty_iff_finitePlaneLocalSeparationPrimitive
    (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- r42 handoff from the same primitive all the way to the selected-neighbour
carrier cut input source.

This is the r42 local-separation reducer followed by the checked r24
local-separation-to-cut source eraser; it introduces no final boundary-cycle,
actual-sector, or W32 consumer row. -/
noncomputable def
    S2_r42_carrier_cut_input_source_of_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_r24_carrier_cut_input_source_of_deletedNeighborLocalSeparationInputSource
    (C := C) (inputs := inputs)
    (S2_r42_deleted_neighbor_local_separation_input_source_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of the r42 carrier-cut handoff. -/
noncomputable def
    S2_r42_carrier_cut_input_source_family_of_finitePlaneLocalSeparationPrimitive
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_r42_carrier_cut_input_source_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact r42 residual for the selected-neighbour carrier cut source. -/
theorem
    S2_r42_carrier_cut_input_source_nonempty_iff_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs) ↔
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs :=
  Iff.trans
    (S2_r24_carrier_cut_input_source_nonempty_iff_deletedNeighborLocalSeparationInputSource
      (C := C) (inputs := inputs))
    (S2_r42_deleted_neighbor_local_separation_input_source_nonempty_iff_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs))

set_option linter.style.longLine false in
/-- Claim `S2-agent-carrier-cut-source-direct-20260521e65`.

The sharp cut-partition source is strictly reduced to the actual local
two-germ source.  The selected heads and `unboundedFrontierEdgeSet` incidences
are copied from the local two-germ rows via the checked local-sector eraser;
the third-neighbour cut branch is discharged by the resulting actual carrier
`only` row. -/
noncomputable def
    S2_agent_carrier_cut_source_direct_20260521e65_of_localTwoGermRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  unboundedFrontierCarrierNeighborPairCutPartitionInputSource_of_localTwoGermRows
    (C := C) (inputs := inputs) localRows

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_carrier_cut_source_direct_20260521e65_of_localTwoGermRows`. -/
noncomputable def
    S2_agent_carrier_cut_source_direct_family_20260521e65_of_localTwoGermRows
    (localRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_source_direct_20260521e65_of_localTwoGermRows
      (C := C) (inputs := inputs) (localRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-pool8-neighbor-cut-partition-source`.

The actual carrier neighbour-pair/cut-partition input source is strictly
lowered to the no-cut/two-exterior-germ row at each unbounded-frontier vertex.
The selected heads are the two actual `unboundedFrontierEdgeSet` heads named by
the boundary-free local source; the local two-germ eraser makes every third
actual carrier-neighbour branch contradictory, so no actual-sector rows, final
boundary cycle, W32 target, induced frontier graph, endpoint-closure shortcut,
or arbitrary spanning cycle is introduced. -/
noncomputable def
    S2_agent_pool8_neighbor_cut_partition_source_of_boundaryFreeTwoSelectedEdgesNoThirdExteriorFrontierGermRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      BoundaryFreeTwoSelectedEdgesNoThirdExteriorFrontierGermRows inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_agent_carrier_cut_source_direct_20260521e65_of_localTwoGermRows
    (C := C) (inputs := inputs)
    (localTwoGermRows_of_boundaryFreeTwoSelectedEdgesNoThirdExteriorFrontierGermRows
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of the pool8 no-cut/two-exterior-germ carrier
cut-partition source. -/
noncomputable def
    S2_agent_pool8_neighbor_cut_partition_source_family_of_boundaryFreeTwoSelectedEdgesNoThirdExteriorFrontierGermRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeTwoSelectedEdgesNoThirdExteriorFrontierGermRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs := by
  intro m C inputs
  exact
    S2_agent_pool8_neighbor_cut_partition_source_of_boundaryFreeTwoSelectedEdgesNoThirdExteriorFrontierGermRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Nonempty form of the pool8 no-cut/two-exterior-germ carrier
cut-partition source. -/
theorem
    S2_agent_pool8_neighbor_cut_partition_source_nonempty_of_boundaryFreeTwoSelectedEdgesNoThirdExteriorFrontierGermRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      BoundaryFreeTwoSelectedEdgesNoThirdExteriorFrontierGermRows inputs) :
    Nonempty
      (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :=
  ⟨S2_agent_pool8_neighbor_cut_partition_source_of_boundaryFreeTwoSelectedEdgesNoThirdExteriorFrontierGermRows
    (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- Claim `S2-agent-carrier-neighbor-source-20260521k5`, selected-edge
local-isolation cut source.

The pointwise carrier-neighbour/cut source is lowered to the current local
finite-drawing selected-edge isolation rows.  The two selected heads and their
actual `unboundedFrontierEdgeSet` incidences are the ones stored in
`SelectedUnboundedFrontierEdgeLocalIsolationSourceRows`; the existing
local-two-germ and local-sector erasers preserve those heads and make the
third-neighbour branch impossible. -/
noncomputable def
    S2_agent_carrier_neighbor_source_20260521k5_cutPartitionInputSource_of_selectedEdgeLocalIsolation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_agent_carrier_cut_source_direct_20260521e65_of_localTwoGermRows
    (C := C) (inputs := inputs)
    (localTwoGermRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Pointwise neighbour-row form of
`S2_agent_carrier_neighbor_source_20260521k5_cutPartitionInputSource_of_selectedEdgeLocalIsolation`. -/
noncomputable def
    S2_agent_carrier_neighbor_source_20260521k5_neighborRows_of_selectedEdgeLocalIsolation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a :=
  S2_agent_frontier_neighbor_pair_input_20260520ax_neighborPairRows
    (C := C) (inputs := inputs)
    (S2_agent_carrier_neighbor_source_20260521k5_cutPartitionInputSource_of_selectedEdgeLocalIsolation
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Fieldwise e32 form of the k5 selected-edge local-isolation reduction. -/
theorem
    S2_agent_carrier_neighbor_source_20260521k5_fieldwise_of_selectedEdgeLocalIsolation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  exact
    (S2_agent_carrier_cut_source_worker_20260521e32_exact_iff
      (C := C) (inputs := inputs)).1
      ⟨S2_agent_carrier_neighbor_source_20260521k5_cutPartitionInputSource_of_selectedEdgeLocalIsolation
        (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- Family cut-partition form of the k5 selected-edge local-isolation
reduction. -/
noncomputable def
    S2_agent_carrier_neighbor_source_20260521k5_cutPartitionInputSource_family_of_selectedEdgeLocalIsolation
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_neighbor_source_20260521k5_cutPartitionInputSource_of_selectedEdgeLocalIsolation
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family fieldwise e32 form of the k5 selected-edge local-isolation
reduction. -/
theorem
    S2_agent_carrier_neighbor_source_20260521k5_fieldwise_family_of_selectedEdgeLocalIsolation
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_neighbor_source_20260521k5_fieldwise_of_selectedEdgeLocalIsolation
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q26-carrier-cut-source`, actual unbounded-frontier germ source.

This is the sharp local residual below the r30/e32 carrier-cut surface: at
each actual unbounded-frontier carrier vertex, choose two genuine incident
`unboundedFrontierEdgeSet` heads and a positive local radius on which every
nearby noncenter frontier point in an incident W3 germ is carried by one of
those two heads.  The finite drawing vertex-isolation step is part of this
source shape; no all-adjacent endpoint row, induced frontier graph, arbitrary
cycle, actual-sector row, or W32 consumer is used. -/
abbrev S2_q26_actualUnboundedFrontierGermCarrierCutSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  Nonempty (SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)

set_option linter.style.longLine false in
/-- The e32 fieldwise carrier-cut package gives the q26 local germ source.

The selected heads are first read as actual selected-incident rows from e32;
the local-radius/no-third-germ row is then supplied by the finite vertex-star
isolation eraser for those same selected heads. -/
noncomputable def
    S2_q26_actualUnboundedFrontierGermCarrierCutSource_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
  localRadiusSelectedEdgeSourceRows_of_selectedIncidentEdgePairRows
    (C := C) (inputs := inputs)
    (S2_agent_carrier_cut_source_worker_20260521e32_selectedIncidentRows_of_fieldwise
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- The q26 local germ source supplies the e32 fieldwise carrier-cut package. -/
theorem
    S2_q26_carrierCutFieldwise_of_actualUnboundedFrontierGermCarrierCutSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_q26_actualUnboundedFrontierGermCarrierCutSource
        (C := C) inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  rcases source with ⟨localRows⟩
  exact
    S2_agent_carrier_neighbor_source_20260521k5_fieldwise_of_selectedEdgeLocalIsolation
      (C := C) (inputs := inputs) localRows

set_option linter.style.longLine false in
/-- Exact q26 residual for the e32 carrier-cut field.

Thus e32 is not lower than the actual local selected-germ source: the two
surfaces are equivalent by the checked selected-incident and local-radius
erasers. -/
theorem
    S2_q26_carrierCutFieldwise_iff_actualUnboundedFrontierGermCarrierCutSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs ↔
      S2_q26_actualUnboundedFrontierGermCarrierCutSource
        (C := C) inputs := by
  constructor
  · intro source
    exact
      ⟨S2_q26_actualUnboundedFrontierGermCarrierCutSource_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source⟩
  · intro source
    exact
      S2_q26_carrierCutFieldwise_of_actualUnboundedFrontierGermCarrierCutSource
        (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Exact q26 residual for the r30 finite-plane local-separation primitive. -/
theorem
    S2_q26_finitePlaneLocalSeparationPrimitive_iff_actualUnboundedFrontierGermCarrierCutSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs ↔
      S2_q26_actualUnboundedFrontierGermCarrierCutSource
        (C := C) inputs :=
  Iff.trans
    (S2_q25_carrier_cut_source_iff_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs)).symm
    (S2_q26_carrierCutFieldwise_iff_actualUnboundedFrontierGermCarrierCutSource
      (C := C) (inputs := inputs))

set_option linter.style.longLine false in
/-- q26 r30 handoff from the actual local selected-germ source. -/
theorem
    S2_q26_finitePlaneLocalSeparationPrimitive_of_actualUnboundedFrontierGermCarrierCutSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_q26_actualUnboundedFrontierGermCarrierCutSource
        (C := C) inputs) :
    S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
      (C := C) inputs :=
  (S2_q26_finitePlaneLocalSeparationPrimitive_iff_actualUnboundedFrontierGermCarrierCutSource
    (C := C) (inputs := inputs)).2 source

set_option linter.style.longLine false in
/-- Family q26 e32 handoff from actual local selected-germ sources. -/
theorem
    S2_q26_carrierCutFieldwise_family_of_actualUnboundedFrontierGermCarrierCutSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q26_actualUnboundedFrontierGermCarrierCutSource
            (C := C) inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_q26_carrierCutFieldwise_of_actualUnboundedFrontierGermCarrierCutSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family q26 r30 handoff from actual local selected-germ sources. -/
theorem
    S2_q26_finitePlaneLocalSeparationPrimitive_family_of_actualUnboundedFrontierGermCarrierCutSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q26_actualUnboundedFrontierGermCarrierCutSource
            (C := C) inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
          (C := C) inputs := by
  intro m C inputs
  exact
    S2_q26_finitePlaneLocalSeparationPrimitive_of_actualUnboundedFrontierGermCarrierCutSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-carrier-cutpartition-source-20260521f9`.

Concrete same-boundary exterior-sector source for the sharp carrier
cut-partition family.  It keeps one actual exterior boundary object, the exact
frontier-vertex equivalence for that object, and primitive sector rows whose
selected predecessor/successor heads are actual `unboundedFrontierEdgeSet`
incidences. -/
abbrev
    S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
    (forall v : Fin n,
      (canonicalGraph C).point v ∈
          frontier (unboundedExteriorComponentRows C inputs).exterior ↔
        Exists fun k : Fin B.length => B.vertex k = v) ∧
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k

set_option linter.style.longLine false in
/-- The f9 source row strictly reduces the exact cut-partition input source.

The selected heads are the actual predecessor/successor exterior-sector edges
from `BoundaryVertexExteriorSectorRowsAt`; incident completeness makes the
third-neighbour cut branch impossible, so the existing selected-incident
eraser packages the requested cut-partition source without induced frontier
graphs, arbitrary cycles, identity angular order, all-adjacent endpoint rows,
selected-head all-outgoing no-between rows, or final boundary-cycle rows. -/
noncomputable def
    S2_agent_carrier_cutpartition_source_20260521f9_of_boundarySectorSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9
        inputs) :
    Nonempty
      (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
        C inputs) := by
  classical
  rcases source with ⟨B, hfrontier, hsector⟩
  exact
    ⟨S2_agent_carrier_cut_source_direct_20260521e65_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs)
      (localSelectedIncidentEdgePairSourceRows_of_boundaryVertexExteriorSectorRows
        (C := C) (inputs := inputs) B hfrontier hsector)⟩

set_option linter.style.longLine false in
/-- Fieldwise e32 form of the f9 source reduction. -/
theorem
    S2_agent_carrier_cutpartition_fieldwise_20260521f9_of_boundarySectorSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9
        inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  exact
    (S2_agent_carrier_cut_source_worker_20260521e32_exact_iff
      (C := C) (inputs := inputs)).1
      (S2_agent_carrier_cutpartition_source_20260521f9_of_boundarySectorSource
        (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of the f9 source reduction. -/
noncomputable def
    S2_agent_carrier_cutpartition_source_family_20260521f9_of_boundarySectorSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Nonempty
          (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs) := by
  intro m C inputs
  exact
    S2_agent_carrier_cutpartition_source_20260521f9_of_boundarySectorSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family fieldwise e32 form of the f9 source reduction. -/
theorem
    S2_agent_carrier_cutpartition_fieldwise_family_20260521f9_of_boundarySectorSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cutpartition_fieldwise_20260521f9_of_boundarySectorSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-k6j-carrier-cut-e32-source`.

The exact residual is the existing primitive same-boundary exterior-sector
package `S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9`: one
actual unit-distance boundary cycle, exact unbounded-frontier vertex coverage,
and `BoundaryVertexExteriorSectorRowsAt` for that same boundary.  This pins the
e32 fieldwise source to honest selected exterior-sector data and does not use
induced frontier graphs, arbitrary cycles, all-adjacent endpoint shortcuts,
identity angular order, synthetic enclosures, or global no-between rows. -/
theorem
    S2_k6j_carrier_cut_e32_source_of_boundarySectorSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9
        inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs :=
  S2_agent_carrier_cutpartition_fieldwise_20260521f9_of_boundarySectorSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of `S2_k6j_carrier_cut_e32_source_of_boundarySectorSource`.

This is the current sharp local residual for the e32 fieldwise source: source
the f9 same-boundary exterior-sector package for every finite drawing. -/
theorem
    S2_k6j_carrier_cut_e32_source_family_of_boundarySectorSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_k6j_carrier_cut_e32_source_of_boundarySectorSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-carrier-cut-from-boundary-package-20260521n7`.

The e32 fieldwise carrier-cut source is lowered directly from the same
actual-boundary package used by the k6m boundary route: the concrete
`ActualBoundaryCycleFrontierEquivalenceRows`, pointwise geometric boundary
rotation-order rows, and same-boundary incident frontier-edge completeness.
The proof only turns the geometric order rows into the primitive
same-boundary exterior-sector rows, then reuses the checked j17 carrier-cut
eraser. -/
theorem
    S2_dynamic_carrier_cut_from_boundary_package_20260521n7_of_actualBoundary_geometricOrder_incident
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      Exists fun actualRows :
          ActualBoundaryCycleFrontierEquivalenceRows C inputs =>
        (forall k : Fin actualRows.boundary.length,
          GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
            C actualRows.boundary k) /\
        BoundaryCycleIncidentFrontierEdgeCompleteness inputs
          actualRows.boundary) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  classical
  let actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs :=
    Classical.choose source
  have hsource :
      (forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
          C actualRows.boundary k) /\
      BoundaryCycleIncidentFrontierEdgeCompleteness inputs
        actualRows.boundary :=
    Classical.choose_spec source
  let angularRows :
      forall k : Fin actualRows.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C actualRows.boundary k :=
    GeometricRotationSystem.boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRows
      C actualRows.boundary hsource.1
  let sectorRows :
      forall k : Fin actualRows.boundary.length,
        BoundaryVertexExteriorSectorRowsAt inputs actualRows.boundary k :=
    boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_boundaryCycleIncidentFrontierEdgeCompleteness
      (C := C) (inputs := inputs) (B := actualRows.boundary)
      angularRows actualRows.cycle_edge_openSegment_frontier hsource.2
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521j17_of_boundaryVertexExteriorSectorRows
      (C := C) (inputs := inputs)
      ⟨actualRows.boundary, actualRows.frontier_iff_cycle_vertex, sectorRows⟩

set_option linter.style.longLine false in
/-- Family form of
`S2_dynamic_carrier_cut_from_boundary_package_20260521n7_of_actualBoundary_geometricOrder_incident`. -/
theorem
    S2_dynamic_carrier_cut_from_boundary_package_family_20260521n7_of_actualBoundary_geometricOrder_incident
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun actualRows :
              ActualBoundaryCycleFrontierEquivalenceRows C inputs =>
            (forall k : Fin actualRows.boundary.length,
              GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
                C actualRows.boundary k) /\
            BoundaryCycleIncidentFrontierEdgeCompleteness inputs
              actualRows.boundary) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_dynamic_carrier_cut_from_boundary_package_20260521n7_of_actualBoundary_geometricOrder_incident
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-k6d-cut-partition-input-source`, actual exterior-carrier form.

The W32 local source family is strictly lowered to the already selected
honest exterior carrier/orbit rows.  The selected predecessor/successor heads
and their actual `unboundedFrontierEdgeSet` incidences are read from
`FaceDartOrbitExteriorCarrierRows.toLocalSectorRowsAt`; the third-neighbour
cut branch is discharged by the existing actual-carrier `only` row. -/
noncomputable def
    S2_k6d_cut_partition_input_source_family_of_faceDartOrbitExteriorCarrierRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FaceDartOrbitExteriorCarrierRows C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
      (C := C) (inputs := inputs)
      (S2_agent_carrier_cut_fieldwise_source_20260521j8_of_faceDartOrbitExteriorCarrierRows
        (C := C) (inputs := inputs) (rows C inputs))

set_option linter.style.longLine false in
/-- Same k6d family handoff from the input-facing actual exterior-sector
package.

This is a direct wrapper around the actual carrier/orbit reduction above:
the boundary object and `ActualExteriorSectorInputSourceRows` are first erased
to `FaceDartOrbitExteriorCarrierRows`, then packaged as the exact
`UnboundedFrontierCarrierNeighborPairCutPartitionInputSource` family. -/
noncomputable def
    S2_k6d_cut_partition_input_source_family_of_actualExteriorSectorInputSourceRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin m,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
      (C := C) (inputs := inputs)
      (S2_agent_carrier_cut_fieldwise_source_20260521j16_of_actualExteriorSectorInputSourceRows
        (C := C) (inputs := inputs) (source C inputs))

set_option linter.style.longLine false in
/-- Same k6d family handoff from primitive same-boundary exterior-sector rows.

This exposes the shortest current input-facing local source below W32 without
using all-adjacent endpoint incidence/closure, induced frontier graphs,
arbitrary cycles, global outgoing-list no-between rows, synthetic enclosure
rows, or identity angular order. -/
noncomputable def
    S2_k6d_cut_partition_input_source_family_of_boundaryVertexExteriorSectorRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin m,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            (forall k : Fin B.length,
              BoundaryVertexExteriorSectorRowsAt inputs B k)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
      (C := C) (inputs := inputs)
      (S2_agent_carrier_cut_fieldwise_source_20260521j17_of_boundaryVertexExteriorSectorRows
        (C := C) (inputs := inputs) (source C inputs))

set_option linter.style.longLine false in
/-- Claim `S2-agent-selected-incident-source-20260521k9`, selected-incident
source from actual local topology cut rows.

This is the non-degree route for `LocalSelectedIncidentEdgePairSourceRows`:
the selected heads are actual incident `unboundedFrontierEdgeSet` heads, and
any third carrier neighbour is eliminated only by the supplied concrete cut
partition plus `inputs.noCutVertex`. -/
noncomputable def
    S2_agent_selected_incident_source_20260521k9_of_cutPartitionRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_cutPartitionRows_20260521k9
    (C := C) (inputs := inputs) rows

set_option linter.style.longLine false in
/-- k9 input-source form.  The exact remaining source leaf is the actual local
topology cut-partition source, not actual carrier degree. -/
noncomputable def
    S2_agent_selected_incident_source_20260521k9_of_cutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- k9 same-boundary exterior-sector source for selected incident edges.

The read-only topology row first constructs the actual per-frontier-vertex
cut rows from `BoundaryVertexExteriorSectorRowsAt`; the k9 eraser then obtains
selected incident-edge completeness through the third-neighbour cut
partition/no-cut route. -/
noncomputable def
    S2_agent_selected_incident_source_20260521k9_of_boundaryVertexExteriorSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
        (forall v : Fin n,
          (canonicalGraph C).point v ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ↔
            Exists fun k : Fin B.length => B.vertex k = v) ∧
        (forall k : Fin B.length,
          BoundaryVertexExteriorSectorRowsAt inputs B k)) :
    LocalSelectedIncidentEdgePairSourceRows inputs := by
  classical
  let B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C :=
    Classical.choose source
  have hsource :
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      (forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k) :=
    Classical.choose_spec source
  exact
    S2_agent_selected_incident_source_20260521k9_of_cutPartitionRows
      (C := C) (inputs := inputs)
      (unboundedFrontierCarrierNeighborPairCutPartitionRows_of_boundaryVertexExteriorSectorRows
        (C := C) (inputs := inputs) (B := B) hsource.1 hsource.2)

set_option linter.style.longLine false in
/-- k9 direct e32 handoff from primitive same-boundary exterior-sector rows.

This lowers the e32 fieldwise source to actual local topology rows:
selected incident unbounded-frontier edges at each frontier vertex plus the
third-neighbour cut partition supplied by the topology cut rows. -/
theorem
    S2_agent_carrier_cut_source_worker_20260521k9_fieldwise_of_boundaryVertexExteriorSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
        (forall v : Fin n,
          (canonicalGraph C).point v ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ↔
            Exists fun k : Fin B.length => B.vertex k = v) ∧
        (forall k : Fin B.length,
          BoundaryVertexExteriorSectorRowsAt inputs B k)) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521f3_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs)
      (S2_agent_selected_incident_source_20260521k9_of_boundaryVertexExteriorSectorRows
        (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of the k9 selected-incident source from primitive
same-boundary exterior-sector rows. -/
noncomputable def
    S2_agent_selected_incident_source_family_20260521k9_of_boundaryVertexExteriorSectorRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin m,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            (forall k : Fin B.length,
              BoundaryVertexExteriorSectorRowsAt inputs B k)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_agent_selected_incident_source_20260521k9_of_boundaryVertexExteriorSectorRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of the k9 direct e32 handoff from primitive same-boundary
exterior-sector rows. -/
theorem
    S2_agent_carrier_cut_source_worker_20260521k9_fieldwise_family_of_boundaryVertexExteriorSectorRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin m,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            (forall k : Fin B.length,
              BoundaryVertexExteriorSectorRowsAt inputs B k)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_source_worker_20260521k9_fieldwise_of_boundaryVertexExteriorSectorRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-carrier-cut-fieldwise-source-20260521k13`,
same-boundary primitive sector-row form.

This is the named k13 local leaf closure from one honest exterior boundary,
the exact frontier-vertex equivalence for that boundary, and primitive
`BoundaryVertexExteriorSectorRowsAt` rows on the same boundary.  It factors
through the existing k9 cut-row eraser, so the selected heads and all
third-neighbour cut partitions remain the actual local/topology rows. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_20260521k13_of_boundaryVertexExteriorSectorRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
        (forall v : Fin n,
          (canonicalGraph C).point v ∈
              frontier (unboundedExteriorComponentRows C inputs).exterior ↔
            Exists fun k : Fin B.length => B.vertex k = v) ∧
        (forall k : Fin B.length,
          BoundaryVertexExteriorSectorRowsAt inputs B k)) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs :=
  S2_agent_carrier_cut_source_worker_20260521k9_fieldwise_of_boundaryVertexExteriorSectorRows
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- k13 face-dart carrier form.

An honest `FaceDartOrbitExteriorCarrierRows` package already carries the
selected unbounded-frontier carrier heads and the same actual carrier
incident-only row needed by the fieldwise e32 source. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_20260521k13_of_faceDartOrbitExteriorCarrierRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : FaceDartOrbitExteriorCarrierRows C inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs :=
  S2_agent_carrier_cut_fieldwise_source_20260521j8_of_faceDartOrbitExteriorCarrierRows
    (C := C) (inputs := inputs) rows

set_option linter.style.longLine false in
/-- k13 selected unbounded-frontier edge local-isolation form.

This keeps the residual at the finite-drawing selected-edge isolation rows:
two actual selected `unboundedFrontierEdgeSet` heads at each carrier vertex,
plus the local isolation row used by the existing local-two-germ eraser. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_20260521k13_of_selectedEdgeLocalIsolation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs :=
  S2_agent_carrier_neighbor_source_20260521k5_fieldwise_of_selectedEdgeLocalIsolation
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of the k13 same-boundary primitive sector-row source. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_family_20260521k13_of_boundaryVertexExteriorSectorRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin m,
              (canonicalGraph C).point v ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            (forall k : Fin B.length,
              BoundaryVertexExteriorSectorRowsAt inputs B k)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521k13_of_boundaryVertexExteriorSectorRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of the k13 face-dart carrier source. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_family_20260521k13_of_faceDartOrbitExteriorCarrierRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FaceDartOrbitExteriorCarrierRows C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521k13_of_faceDartOrbitExteriorCarrierRows
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Family form of the k13 selected-edge local-isolation source. -/
theorem
    S2_agent_carrier_cut_fieldwise_source_family_20260521k13_of_selectedEdgeLocalIsolation
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
          inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_cut_fieldwise_source_20260521k13_of_selectedEdgeLocalIsolation
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-selected-neighbor-cutpartition-source-20260521k20`.

The selected-neighbour cut-partition surface is exactly the actual pointwise
carrier cut data: two genuine incident `unboundedFrontierEdgeSet` heads at each
actual frontier carrier vertex, plus a concrete cut partition for every third
actual carrier neighbour.  No induced frontier graph, all-adjacent endpoint
shortcut, boundary cycle, or geometric-order row is introduced here. -/
noncomputable def
    S2_agent_selected_neighbor_cutpartition_source_20260521k20_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  S2_agent_selected_cutpartition_source_of_cutPartitionRows_20260520
    (C := C) (inputs := inputs)
    (S2_agent_carrier_cut_rows_source_20260521k10_of_carrierCutFieldwise
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Input-source form of
`S2_agent_selected_neighbor_cutpartition_source_20260521k20_of_carrierCutFieldwise`.

This is the same strict pointwise lowering, with the actual carrier data read
from the checked cut-partition input source. -/
noncomputable def
    S2_agent_selected_neighbor_cutpartition_source_20260521k20_of_cutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
  S2_agent_selected_neighbor_cutpartition_source_20260521k20_of_carrierCutFieldwise
    (C := C) (inputs := inputs) source.rows

set_option linter.style.longLine false in
/-- The same k20 rows feed the no-cut selected-incident eraser.

Here `inputs.noCutVertex` is consumed by
`localSelectedIncidentEdgePairSourceRows_of_cutPartitionRows_20260521k9`: an
extra actual incident `unboundedFrontierEdgeSet` head is a third concrete
carrier neighbour, so its supplied cut partition contradicts the input no-cut
field. -/
noncomputable def
    S2_agent_selected_neighbor_cutpartition_source_20260521k20_to_selectedIncidentRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_cutPartitionRows_20260521k9
    (C := C) (inputs := inputs) rows.selectedNeighborRows

set_option linter.style.longLine false in
/-- Exact nonempty form of the k20 selected-neighbour cut-partition source.

Thus this selected-neighbour source is neither stronger nor weaker than the
actual e32 fieldwise carrier cut data; the no-cut consequence is available by
the selected-incident eraser above. -/
theorem
    S2_agent_selected_neighbor_cutpartition_source_20260521k20_nonempty_iff_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs) ↔
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs := by
  constructor
  · rintro ⟨rows⟩
    exact
      S2_agent_carrier_cut_source_worker_20260521e32_fieldwise_of_cutPartitionRows
        (C := C) (inputs := inputs) rows.selectedNeighborRows
  · intro source
    exact
      ⟨S2_agent_selected_neighbor_cutpartition_source_20260521k20_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- Family form of the k20 selected-neighbour cut-partition source. -/
noncomputable def
    S2_agent_selected_neighbor_cutpartition_source_family_20260521k20_of_carrierCutFieldwise
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
          inputs := by
  intro m C inputs
  exact
    S2_agent_selected_neighbor_cutpartition_source_20260521k20_of_carrierCutFieldwise
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-q5-cutpartition-source`, local no-third-germ form.

The q5 cut-partition input source is lowered to the current actual local
selected-edge/no-third-germ primitive.  The proof uses the existing r7i
local-sector erasure and then packages the resulting fieldwise carrier-cut
rows; it introduces no actual boundary rows, induced frontier graph,
arbitrary cycle, all-adjacent chord shortcut, or W-facing facade. -/
noncomputable def
    S2_agent_q5_cutpartition_source_of_localSelectedNoThirdGermSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
    (C := C) (inputs := inputs)
    (S2_r7i_carrierCutFieldwise_of_rawFaceWalkRepeatedTailCutSource
      (C := C) (inputs := inputs)
      (S2_subagent_r7i_carrier_cut_source_20260521_current3_of_localSelectedNoThirdGermSource
        (C := C) (inputs := inputs) source))

set_option linter.style.longLine false in
/-- Family form of the q5 local no-third-germ cut-partition source. -/
noncomputable def
    S2_agent_q5_cutpartition_source_family_of_localSelectedNoThirdGermSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_agent_q5_cutpartition_source_of_localSelectedNoThirdGermSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-q5-cutpartition-source`, deleted-neighbour primitive form.

This is the same q5 target from the current r30 deleted-neighbour finite-plane
local-separation primitive, recorded under the q5 claim name. -/
noncomputable def
    S2_agent_q5_cutpartition_source_of_deletedNeighborFinitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
  S2_r5r_carrier_cut_source_next_leaf_20260521r5r_of_finitePlaneLocalSeparationPrimitive
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of the q5 deleted-neighbour primitive cut-partition source. -/
noncomputable def
    S2_agent_q5_cutpartition_source_family_of_deletedNeighborFinitePlaneLocalSeparationPrimitive
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_agent_q5_cutpartition_source_of_deletedNeighborFinitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact q5 residual at the local no-third-germ primitive.

The forward direction erases cut partitions to selected incident-edge rows and
then to local no-third-germ rows; the reverse direction is the q5 constructor
above. -/
theorem
    S2_agent_q5_cutpartition_source_nonempty_iff_localSelectedNoThirdGermSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs) <->
      Nonempty
        (UnboundedFrontierCarrierLocalSelectedNoThirdGermSource
          C inputs) := by
  constructor
  · rintro ⟨source⟩
    exact
      ⟨localSelectedNoThirdGermSource_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs)
        (localSelectedIncidentEdgePairSourceRows_of_cutPartitionInputSource_20260521k9
          (C := C) (inputs := inputs) source)⟩
  · rintro ⟨source⟩
    exact
      ⟨S2_agent_q5_cutpartition_source_of_localSelectedNoThirdGermSource
        (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- Direct nonempty cycle-row handoff for the f9 same-boundary exterior-sector source.

The f9 source already supplies the actual exterior boundary cycle, the exact
frontier-vertex equivalence, and primitive sector rows on that same cycle.
This reducer sends those rows straight to a nonempty
`UnboundedExteriorFrontierCycleRows` package without detouring through the
cut-partition package.  The result is nonempty because the f9 source is a Prop
existential. -/
noncomputable def
    nonempty_unboundedExteriorFrontierCycleRows_of_boundarySectorSource_20260521h7
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9
        inputs) :
    Nonempty (UnboundedExteriorFrontierCycleRows C inputs) := by
  classical
  rcases source with ⟨B, hfrontier, hsector⟩
  exact ⟨
    unboundedExteriorFrontierCycleRows_of_boundaryVertexExteriorSectorRows
      (C := C) (inputs := inputs) B hfrontier hsector⟩

set_option linter.style.longLine false in
/-- Family form of the direct h7 nonempty cycle-row handoff. -/
noncomputable def
    nonempty_unboundedExteriorFrontierCycleRows_family_of_boundarySectorSource_20260521h7
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Nonempty (UnboundedExteriorFrontierCycleRows C inputs) := by
  intro m C inputs
  exact
    nonempty_unboundedExteriorFrontierCycleRows_of_boundarySectorSource_20260521h7
      (C := C) (inputs := inputs) (source C inputs)

end

end S2CarrierCutSource
end Swanepoel
end ErdosProblems1066
