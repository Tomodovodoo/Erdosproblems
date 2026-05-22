import ErdosProblems1066.Swanepoel.S2BoundaryFreeRawSource
import ErdosProblems1066.Swanepoel.S2CarrierCutSource
import ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
import ErdosProblems1066.Swanepoel.S2TopologySource

set_option autoImplicit false

/-!
# S2 carrier local source

This owner file names the sharp local carrier leaf for the deleted-neighbour
source.  The reduction stays on the actual `unboundedFrontierCarrierGraph`:
two-regularity of that graph gives the selected incident frontier edges and
makes every proposed third carrier neighbour contradictory.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace S2CarrierLocalSource

open JordanTopologyFactsConcrete
open JordanTopologyFactsConcrete.MinimalFailureTopology
open ExteriorComponentTopology
open FinitePlaneDrawing
open S2LocalTwoGermAssembly

noncomputable section

variable {n : Nat}

/-- The exact actual-carrier degree-two source for S2.

This is deliberately stated for `unboundedFrontierCarrierGraph C inputs`, not
for an induced auxiliary frontier graph or a boundary cycle. -/
abbrev ActualCarrierDegreeTwoSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card = 2

/-- Actual carrier degree two is exactly enough for the requested pointwise
local-sector family.

This is the local carrier source in the target shape: the two heads are chosen
from the actual `unboundedFrontierCarrierGraph` neighbour finset, and the
selected-edge fields are read through `unboundedFrontierCarrierGraph_adj_iff`. -/
noncomputable def localSectorRows_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    S2_agent_local_sector_source_worker_20260521e14_of_carrier_degree_two
      (C := C) inputs (by simpa [ActualCarrierDegreeTwoSource] using hdegree)

/-- Actual carrier degree two also gives the pointwise concrete neighbour-pair
rows used by the older finite no-closed-separation support route.

This is just an eraser from the same actual carrier graph degree statement; it
does not choose an induced frontier graph or promote all frontier chords. -/
noncomputable def neighborPairRows_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    unboundedFrontierCarrierNeighborPairRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs)
      (by simpa [ActualCarrierDegreeTwoSource] using hdegree)

/-- Family form of `neighborPairRows_of_actualCarrierDegreeTwo`. -/
noncomputable def neighborPairRows_family_of_actualCarrierDegreeTwo
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierNeighborPairAt inputs a := by
  intro m C inputs
  exact neighborPairRows_of_actualCarrierDegreeTwo
    (C := C) inputs (source C inputs)

/-- The pointwise local-sector source is equivalent to actual carrier
degree-two, in the exact neighbour-finset-cardinality form used downstream. -/
theorem nonempty_localSectorRows_iff_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a) ↔
      ActualCarrierDegreeTwoSource inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  constructor
  · rintro ⟨rows⟩
    exact
      (by
        simpa [ActualCarrierDegreeTwoSource] using
          (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_localSectorRows
            (C := C) (inputs := inputs) rows))
  · intro hdegree
    exact ⟨localSectorRows_of_actualCarrierDegreeTwo (C := C) inputs hdegree⟩

/-- The lower boundary-free local no-third-germ source feeds the requested
local-sector family directly.

This is the current shortest lower source below the actual carrier degree
leaf: it names two actual selected carrier edges at each frontier vertex and a
local-radius no-third-germ row, then erases through the checked local two-germ
constructor. -/
noncomputable def localSectorRows_of_boundaryFreeLocalNoThirdGermSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  source.toLocalSectorRows

/-- The same lower source also supplies the actual carrier degree-two leaf
used by `localSectorRows_of_actualCarrierDegreeTwo`. -/
theorem actualCarrierDegreeTwo_of_boundaryFreeLocalNoThirdGermSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    ActualCarrierDegreeTwoSource inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    (by
      simpa [ActualCarrierDegreeTwoSource] using
        (BoundaryFreeLocalNoThirdGermSourceRows.toNeighborFinsetCardTwo
          (C := C) (inputs := inputs) source))

/-- Pointwise actual carrier neighbour-pair rows give the exact degree-two
source used by this file. -/
theorem actualCarrierDegreeTwo_of_neighborPairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    ActualCarrierDegreeTwoSource inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    (by
      simpa [ActualCarrierDegreeTwoSource] using
        (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_neighborPairRows
          (C := C) (inputs := inputs) neighborRows))

set_option linter.style.longLine false in
/-- Honest face-dart exterior-carrier rows source the actual carrier
degree-two leaf directly.

The two neighbours are read from the same selected
`unboundedFrontierEdgeSet` carrier encoded by
`FaceDartOrbitExteriorCarrierRows`; no induced frontier graph, all-adjacent
endpoint row, or outgoing-list no-between premise is introduced. -/
theorem actualCarrierDegreeTwo_of_faceDartOrbitExteriorCarrierRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : FaceDartOrbitExteriorCarrierRows C inputs) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_neighborPairRows
    (C := C) (inputs := inputs) rows.toNeighborPairRows

set_option linter.style.longLine false in
/-- Family form of
`actualCarrierDegreeTwo_of_faceDartOrbitExteriorCarrierRows`. -/
theorem actualCarrierDegreeTwo_family_of_faceDartOrbitExteriorCarrierRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FaceDartOrbitExteriorCarrierRows C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact actualCarrierDegreeTwo_of_faceDartOrbitExteriorCarrierRows
    (C := C) (inputs := inputs) (rows C inputs)

/-- Actual carrier degree two is equivalent to the pointwise concrete
neighbour-pair rows. -/
theorem actualCarrierDegreeTwo_iff_neighborPairRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    ActualCarrierDegreeTwoSource inputs ↔
      Nonempty
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierNeighborPairAt inputs a) := by
  constructor
  · intro hdegree
    exact ⟨neighborPairRows_of_actualCarrierDegreeTwo
      (C := C) inputs hdegree⟩
  · rintro ⟨rows⟩
    exact actualCarrierDegreeTwo_of_neighborPairRows
      (C := C) (inputs := inputs) rows

set_option linter.style.longLine false in
/-- Actual carrier degree two is exactly the corrected boundary-free local
input package.

This equivalence keeps the live local source on the concrete selected
`unboundedFrontierCarrierGraph`: the boundary-free local package erases to
actual carrier-neighbour rows, and those rows are equivalent to cardinality
two of the actual carrier neighbour finset. -/
theorem actualCarrierDegreeTwo_iff_boundaryFreeLocalInputSourceReduction_20260521h5
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    ActualCarrierDegreeTwoSource inputs ↔
      Nonempty (BoundaryFreeLocalInputSourceReduction inputs) := by
  constructor
  · intro hdegree
    exact
      ⟨boundaryFreeLocalInputSourceReduction_of_neighborPairRows_20260521h4
        (C := C) (inputs := inputs)
        (neighborPairRows_of_actualCarrierDegreeTwo
          (C := C) inputs hdegree)⟩
  · intro hsource
    rcases
        (nonempty_boundaryFreeLocalInputSourceReduction_iff_neighborPairRows_20260521h5
          (C := C) (inputs := inputs)).1 hsource with
      ⟨neighborRows⟩
    exact actualCarrierDegreeTwo_of_neighborPairRows
      (C := C) (inputs := inputs) neighborRows

/-- The sharp cut-partition carrier source erases to actual carrier degree two. -/
theorem actualCarrierDegreeTwo_of_cutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_neighborPairRows
    (C := C) (inputs := inputs)
    (S2_agent_carrier_neighborpair_source_worker_20260521e16_of_cutPartitionInputSource
      (C := C) (inputs := inputs) source)

/-- The deleted-neighbour source erases to actual carrier degree two. -/
theorem actualCarrierDegreeTwo_of_unreachableAfterDeleteInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    ActualCarrierDegreeTwoSource inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    unboundedFrontierCarrierGraph_neighborFinset_card_two_of_unreachableAfterDeleteInputSource
      inputs source

/-- Deleted-neighbour local separation erases to actual carrier degree two. -/
theorem actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
        C inputs) :
    ActualCarrierDegreeTwoSource inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    unboundedFrontierCarrierGraph_neighborFinset_card_two_of_deletedNeighborLocalSeparationInputSource
      inputs source

/-- Exact-field deleted-neighbour local separation erases to actual carrier
degree two.

This is a smaller source than the packaged deleted-neighbour input source: it
only names the two actual selected incident frontier heads and the Boolean
side-separation data for every third carrier neighbour. -/
theorem actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationExactFieldSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
        inputs) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationInputSource
    (C := C) (inputs := inputs)
    (S2_agent_deleted_neighbor_local_separation_worker_20260521e6
      (C := C) (inputs := inputs) source)

/-- Actual carrier degree two constructs the exact deleted-neighbour local
separation fields.

The two selected heads are chosen through the concrete local-sector rows for
`unboundedFrontierCarrierGraph C inputs`.  Every third-neighbour Boolean side
separation is then filled by the checked exact-field constructor, where the
third-neighbour branch is contradictory against the actual local `only` row. -/
noncomputable def deletedNeighborLocalSeparationExactFieldSource_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
      inputs :=
  S2_agent_exact_deleted_neighbor_field_source_worker_20260521e9_of_localSectorRows
    (C := C) (inputs := inputs)
    (localSectorRows_of_actualCarrierDegreeTwo
      (C := C) inputs hdegree)

/-- Claim `S2-agent-deleted-neighbor-exact-source-prover-20260521e55`.

The family exact deleted-neighbour local-separation source is strictly reduced
to the concrete actual carrier two-regularity source.  This keeps the selected
heads in `unboundedFrontierEdgeSet C inputs` and produces the Boolean
deleted-neighbour side separation for every third actual carrier neighbour via
the local-sector exact-field constructor; it does not use induced frontier
graphs, arbitrary carrier cycles, all-adjacent endpoint rows, all-outgoing
no-between rows, or final boundary-cycle rows. -/
noncomputable def
    S2_agent_deleted_neighbor_exact_source_prover_20260521e55
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
          inputs := by
  intro m C inputs
  exact
    deletedNeighborLocalSeparationExactFieldSource_of_actualCarrierDegreeTwo
      (C := C) inputs (source C inputs)

/-- Exact deleted-neighbour local separation is equivalent to actual carrier
two-regularity in the current S2 source surface. -/
theorem nonempty_deletedNeighborLocalSeparationExactFieldSource_iff_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
          inputs) ↔
      ActualCarrierDegreeTwoSource inputs := by
  constructor
  · rintro ⟨source⟩
    exact
      actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationExactFieldSource
        (C := C) (inputs := inputs) source
  · intro hdegree
    exact
      ⟨deletedNeighborLocalSeparationExactFieldSource_of_actualCarrierDegreeTwo
        (C := C) inputs hdegree⟩

/-- Local selected-edge/no-third-germ rows erase to actual carrier degree two
through the checked local-sector source. -/
theorem actualCarrierDegreeTwo_of_localSelectedNoThirdGermSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    ActualCarrierDegreeTwoSource inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    (by
      simpa [ActualCarrierDegreeTwoSource] using
        (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_localSectorRows
          (C := C) (inputs := inputs)
          (unboundedFrontierCarrierLocalSectorRows_of_localSelectedNoThirdGermSource
            (C := C) (inputs := inputs) source)))

/-- Actual carrier degree two rules out the singleton graph-frontier carrier.

If the graph-frontier carrier had one vertex, the degree-two row would give a
carrier neighbour of that vertex, but the singleton carrier would force that
neighbour to be the same vertex, contradicting looplessness of the concrete
carrier graph. -/
theorem unboundedFrontierVertexSet_card_ne_one_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    (unboundedFrontierVertexSet C inputs).card ≠ 1 := by
  classical
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  intro hcard
  rcases Finset.card_eq_one.mp hcard with ⟨v, hsingleton⟩
  let a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨v, by simp [hsingleton]⟩
  have hcard_two :
      ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card = 2 := by
    simpa [ActualCarrierDegreeTwoSource] using hdegree a
  have hpos :
      0 < ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card := by
    rw [hcard_two]
    norm_num
  rcases Finset.card_pos.1 hpos with ⟨b, hbmem⟩
  have hb :
      (unboundedFrontierCarrierGraph C inputs).Adj a b := by
    simpa [SimpleGraph.mem_neighborFinset] using hbmem
  have hb_val : b.1 = v := by
    simpa [hsingleton] using b.2
  have hb_eq : a = b := Subtype.ext hb_val.symm
  exact (unboundedFrontierCarrierGraph C inputs).ne_of_adj hb hb_eq

/-- Actual carrier degree two forces the concrete unbounded-frontier carrier to
have at least three graph vertices.

This is a small graph-theoretic consequence of the actual carrier source:
one vertex is impossible by looplessness, and two vertices cannot support
degree two in a loopless simple graph. -/
theorem three_le_unboundedFrontierVertexSet_card_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    3 <= (unboundedFrontierVertexSet C inputs).card := by
  classical
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  have hnonempty : (unboundedFrontierVertexSet C inputs).Nonempty := by
    rcases unboundedFrontierCarrier_nonempty (C := C) inputs with ⟨a⟩
    exact ⟨a.1, a.2⟩
  have hpos : 0 < (unboundedFrontierVertexSet C inputs).card :=
    Finset.card_pos.2 hnonempty
  have hne_one :
      (unboundedFrontierVertexSet C inputs).card ≠ 1 :=
    unboundedFrontierVertexSet_card_ne_one_of_actualCarrierDegreeTwo
      (C := C) (inputs := inputs) hdegree
  have hne_two :
      (unboundedFrontierVertexSet C inputs).card ≠ 2 := by
    intro hcard_two_vertices
    rcases Finset.card_eq_two.mp hcard_two_vertices with ⟨v, w, hvw, hset⟩
    have hv_mem : v ∈ unboundedFrontierVertexSet C inputs := by
      simp [hset]
    have hw_mem : w ∈ unboundedFrontierVertexSet C inputs := by
      simp [hset]
    let a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
      ⟨v, hv_mem⟩
    let b : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
      ⟨w, hw_mem⟩
    have hsubset :
        (unboundedFrontierCarrierGraph C inputs).neighborFinset a ⊆ {b} := by
      intro x hx
      have hx_frontier : x.1 ∈ unboundedFrontierVertexSet C inputs := x.2
      have hx_in_pair : x.1 ∈ ({v, w} : Finset (Fin n)) := by
        simpa [hset] using hx_frontier
      have hxvw : x.1 = v ∨ x.1 = w := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx_in_pair
      rcases hxvw with hxv | hxw
      · have hadj :
            (unboundedFrontierCarrierGraph C inputs).Adj a x := by
          simpa [SimpleGraph.mem_neighborFinset] using hx
        have hx_eq_a : x = a := Subtype.ext hxv
        exact False.elim
          ((unboundedFrontierCarrierGraph C inputs).ne_of_adj hadj hx_eq_a.symm)
      · have hx_eq_b : x = b := Subtype.ext hxw
        simp [hx_eq_b]
    have hcard_neighbor_two :
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card = 2 := by
      simpa [ActualCarrierDegreeTwoSource] using hdegree a
    have hcard_neighbor_le_one :
        ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card <= 1 := by
      exact le_trans (Finset.card_le_card hsubset) (by simp)
    omega
  omega

/-- Subtype-cardinality form of
`three_le_unboundedFrontierVertexSet_card_of_actualCarrierDegreeTwo`. -/
theorem three_le_unboundedFrontierCarrier_fintype_card_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    3 <= Fintype.card {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} := by
  classical
  simpa [Fintype.card_subtype] using
    three_le_unboundedFrontierVertexSet_card_of_actualCarrierDegreeTwo
      (C := C) (inputs := inputs) hdegree

/-- Actual carrier degree two supplies the selected incident-edge source at
every graph vertex on the actual unbounded exterior frontier.

The proof only uses the concrete carrier graph: degree two makes the
neighbour finset nonempty, and carrier adjacency is definitionally an
orientation of an edge in `unboundedFrontierEdgeSet`. -/
theorem frontierVertexIncidentSource_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs := by
  classical
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  intro v hvfrontier
  let a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs} :=
    ⟨v, mem_unboundedFrontierVertexSet_iff.2 hvfrontier⟩
  have hcard_two :
      ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card = 2 := by
    simpa [ActualCarrierDegreeTwoSource] using hdegree a
  have hpos :
      0 < ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card := by
    rw [hcard_two]
    norm_num
  rcases Finset.card_pos.1 hpos with ⟨b, hbmem⟩
  have hb :
      (unboundedFrontierCarrierGraph C inputs).Adj a b := by
    simpa [SimpleGraph.mem_neighborFinset] using hbmem
  exact ⟨b.1, (unboundedFrontierCarrierGraph_adj_iff).1 hb⟩

/-- Actual carrier degree two covers the whole unbounded exterior frontier by
selected `unboundedFrontierEdgeSet` edge segments.

This packages the existing fixed-side edge-cover theorem with the concrete
local-sector rows obtained from actual carrier degree two. -/
theorem selectedFrontierEdgeCover_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    UnboundedExteriorSelectedFrontierEdgeCover C inputs :=
  frontier_edge_cover_of_localSectorRows_fixedSide
    (C := C) inputs
    (localSectorRows_of_actualCarrierDegreeTwo
      (C := C) inputs hdegree)

/-- Family form of
`selectedFrontierEdgeCover_of_actualCarrierDegreeTwo`. -/
theorem selectedFrontierEdgeCover_family_of_actualCarrierDegreeTwo
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorSelectedFrontierEdgeCover C inputs := by
  intro m C inputs
  exact
    selectedFrontierEdgeCover_of_actualCarrierDegreeTwo
      (C := C) (inputs := inputs) (source C inputs)

/-- Finite-drawing no-closed-separation plus actual carrier degree two makes the
concrete unbounded-frontier carrier connected.

The topology input supplies preconnectedness of the actual exterior frontier;
actual degree two supplies the selected frontier-edge cover. -/
theorem unboundedFrontierCarrierGraph_connected_of_finiteDrawingNoClosedSeparation_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    (unboundedFrontierCarrierGraph C inputs).Connected :=
  unboundedFrontierCarrierGraph_connected_of_frontier_preconnected_and_frontier_edge_cover
    (C := C) inputs
    (actualFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      (C := C) inputs frontier_noClosedSeparation)
    (selectedFrontierEdgeCover_of_actualCarrierDegreeTwo
      (C := C) (inputs := inputs) hdegree)

/-- Finite-drawing no-closed-separation plus actual carrier degree two closes
the component-topology rows through the non-singleton carrier branch.

This is only a support reducer: the live local work remains proving the actual
carrier degree-two source from the finite plane drawing inputs. -/
def unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  S2_agent_component_topology_source_worker_20260520r4
    (C := C) inputs frontier_noClosedSeparation
    (selectedFrontierEdgeCover_of_actualCarrierDegreeTwo
      (C := C) (inputs := inputs) hdegree)

/-- Finite-drawing no-closed-separation plus actual carrier degree two produces
the unbounded exterior frontier-cycle rows through the concrete carrier graph.

This is a support route, not a new source: the only inputs are the finite
frontier topology theorem and the actual carrier degree-two source. -/
noncomputable def unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_frontierPreconnected_localSectorRows
    (C := C) inputs
    (actualFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      (C := C) inputs frontier_noClosedSeparation)
    (localSectorRows_of_actualCarrierDegreeTwo
      (C := C) inputs hdegree)

/-- Family source reducer from boundary-free local no-third-germ rows to the
live actual-carrier degree-two leaf. -/
theorem actualCarrierDegreeTwo_family_of_boundaryFreeLocalNoThirdGermSourceRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    actualCarrierDegreeTwo_of_boundaryFreeLocalNoThirdGermSourceRows
      (C := C) (inputs := inputs) (source C inputs)

/-- Family source reducer from the sharp cut-partition input source to the
live actual-carrier degree-two leaf. -/
theorem actualCarrierDegreeTwo_family_of_cutPartitionInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    actualCarrierDegreeTwo_of_cutPartitionInputSource
      (C := C) (inputs := inputs) (source C inputs)

/-- Claim `S2-agent-actual-carrier-degree-source-prover-20260521e53`.

The family actual-carrier degree-two leaf reduces directly to the already
isolated fieldwise cut-partition source.  The source names two actual
`unboundedFrontierEdgeSet` heads at each concrete carrier vertex and asks for a
cut partition for every third neighbour of the actual
`unboundedFrontierCarrierGraph`; no induced frontier graph, arbitrary cycle, or
all-outgoing angular row is introduced. -/
theorem S2_agent_actual_carrier_degree_source_prover_20260521e53
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
                      forall b :
                          {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                        (unboundedFrontierCarrierGraph C inputs).Adj a b ->
                          b.1 ≠ left ->
                            b.1 ≠ right ->
                              Nonempty (CutVertexInterface.CutVertexPartition C)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    actualCarrierDegreeTwo_of_cutPartitionInputSource
      (C := C) (inputs := inputs)
      (S2_agent_cutpartition_input_source_worker_20260521e19
        (C := C) inputs (source C inputs))

/-- Family source reducer from deleted-neighbour local separation rows to the
live actual-carrier degree-two leaf. -/
theorem actualCarrierDegreeTwo_family_of_deletedNeighborLocalSeparationInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationInputSource
      (C := C) (inputs := inputs) (source C inputs)

/-- Family source reducer from exact-field deleted-neighbour local separation
to the live actual-carrier degree-two leaf. -/
theorem
    actualCarrierDegreeTwo_family_of_deletedNeighborLocalSeparationExactFieldSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationExactFieldSource
      (C := C) (inputs := inputs) (source C inputs)

/-- Family source reducer from local selected-edge/no-third-germ rows to the
live actual-carrier degree-two leaf. -/
theorem actualCarrierDegreeTwo_family_of_localSelectedNoThirdGermSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    actualCarrierDegreeTwo_of_localSelectedNoThirdGermSource
      (C := C) (inputs := inputs) (source C inputs)

/-- Raw face-successor source rows already contain the pointwise local-sector
family, so they erase directly to actual carrier degree two.

This is only a source-free projection from the raw-orbit package; it does not
use the final boundary-cycle rows produced downstream from that package. -/
theorem actualCarrierDegreeTwo_of_rawFaceSuccOrbitSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    {R : UnitDistanceRotationSystem C}
    {start : UnitDistanceDart C}
    {O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start}
    (rows : RawFaceSuccOrbitSourceRows (inputs := inputs) O) :
    ActualCarrierDegreeTwoSource inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  simpa [ActualCarrierDegreeTwoSource] using
    (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_localSectorRows
      (C := C) (inputs := inputs) rows.localSectorRows)

set_option linter.style.longLine false in
/-- Seed-visible selected raw orbit rows erase to actual carrier degree two
once repeated-tail cut partitions close the same raw orbit.

This is the h12 local-source handoff from the raw exterior-face lane: the
degree statement is still about the concrete `unboundedFrontierCarrierGraph`,
and the only extra input is the no-cut/repeated-tail cut row for this selected
raw orbit. -/
theorem actualCarrierDegreeTwo_of_selectedSeededRawFaceSuccOrbitSourceRows_cutPartitions
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : SelectedSeededRawFaceSuccOrbitSourceRows inputs)
    (cut_partitions :
      forall {i j : Fin rows.O.period},
        i ≠ j ->
        (rows.O.dart i).tail = (rows.O.dart j).tail ->
          Nonempty (CutVertexInterface.CutVertexPartition C)) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_rawFaceSuccOrbitSourceRows
    (C := C) (inputs := inputs) (O := rows.O)
    (rows.toRawFaceSuccOrbitSourceRows_of_cutPartitions cut_partitions)

set_option linter.style.longLine false in
/-- Primitive deleted-tail witnesses for the selected raw orbit also erase to
actual carrier degree two. -/
theorem actualCarrierDegreeTwo_of_selectedSeededRawFaceSuccOrbitSourceRows_deletedTailWitnesses
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : SelectedSeededRawFaceSuccOrbitSourceRows inputs)
    (deleted_tail_witnesses :
      SelectedSeededRawOrbitRepeatedTailWitnessSource rows) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_rawFaceSuccOrbitSourceRows
    (C := C) (inputs := inputs) (O := rows.O)
    (rows.toRawFaceSuccOrbitSourceRows_of_deletedTailWitnesses
      deleted_tail_witnesses)

set_option linter.style.longLine false in
/-- Family form of the seed-visible raw-orbit handoff with repeated-tail cut
partitions bundled with the selected orbit. -/
theorem actualCarrierDegreeTwo_family_of_selectedSeededRawFaceSuccOrbitSourceRows_cutPartitions
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun rows : SelectedSeededRawFaceSuccOrbitSourceRows inputs =>
            forall {i j : Fin rows.O.period},
              i ≠ j ->
              (rows.O.dart i).tail = (rows.O.dart j).tail ->
                Nonempty (CutVertexInterface.CutVertexPartition C)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases source C inputs with ⟨rows, cut_partitions⟩
  exact
    actualCarrierDegreeTwo_of_selectedSeededRawFaceSuccOrbitSourceRows_cutPartitions
      (C := C) (inputs := inputs) rows cut_partitions

set_option linter.style.longLine false in
/-- Family form of the seed-visible raw-orbit handoff with primitive
deleted-tail witnesses bundled with the selected orbit. -/
theorem actualCarrierDegreeTwo_family_of_selectedSeededRawFaceSuccOrbitSourceRows_deletedTailWitnesses
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun rows : SelectedSeededRawFaceSuccOrbitSourceRows inputs =>
            Nonempty (SelectedSeededRawOrbitRepeatedTailWitnessSource rows)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases source C inputs with ⟨rows, deleted_tail_witnesses⟩
  rcases deleted_tail_witnesses with ⟨witness⟩
  exact
    actualCarrierDegreeTwo_of_selectedSeededRawFaceSuccOrbitSourceRows_deletedTailWitnesses
      (C := C) (inputs := inputs) rows witness

set_option linter.style.longLine false in
/-- Connected raw-orbit rows feed actual carrier degree two through the
seed-visible selected raw orbit, without requiring the raw-orientation package.

The remaining residual is exactly the repeated-tail cut-partition row for the
selected geometric raw orbit produced from the connected carrier source. -/
theorem actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedSeededCutPartitions
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeConnectedRawOrbitSourceRows inputs)
    (cut_partitions :
      let selectedRows :
          SelectedSeededRawFaceSuccOrbitSourceRows inputs :=
        S2_agent_20260520_selectedSeededRawFaceSuccOrbitSourceRows_of_connectedRawOrbitSourceRows
          (C := C) (inputs := inputs) rows
      forall {i j : Fin selectedRows.O.period},
        i ≠ j ->
        (selectedRows.O.dart i).tail = (selectedRows.O.dart j).tail ->
          Nonempty (CutVertexInterface.CutVertexPartition C)) :
    ActualCarrierDegreeTwoSource inputs := by
  let selectedRows :
      SelectedSeededRawFaceSuccOrbitSourceRows inputs :=
    S2_agent_20260520_selectedSeededRawFaceSuccOrbitSourceRows_of_connectedRawOrbitSourceRows
      (C := C) (inputs := inputs) rows
  exact
    actualCarrierDegreeTwo_of_selectedSeededRawFaceSuccOrbitSourceRows_cutPartitions
      (C := C) (inputs := inputs) selectedRows cut_partitions

set_option linter.style.longLine false in
/-- Family form of
`actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedSeededCutPartitions`. -/
theorem actualCarrierDegreeTwo_family_of_connectedRawOrbitSourceRows_selectedSeededCutPartitions
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun rows : BoundaryFreeConnectedRawOrbitSourceRows inputs =>
            let selectedRows :
                SelectedSeededRawFaceSuccOrbitSourceRows inputs :=
              S2_agent_20260520_selectedSeededRawFaceSuccOrbitSourceRows_of_connectedRawOrbitSourceRows
                (C := C) (inputs := inputs) rows
            forall {i j : Fin selectedRows.O.period},
              i ≠ j ->
              (selectedRows.O.dart i).tail = (selectedRows.O.dart j).tail ->
                Nonempty (CutVertexInterface.CutVertexPartition C)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases source C inputs with ⟨rows, cut_partitions⟩
  exact
    actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedSeededCutPartitions
      (C := C) (inputs := inputs) rows cut_partitions

set_option linter.style.longLine false in
/-- Connected raw-orbit rows feed actual carrier degree two through the
seed-visible selected raw orbit, using primitive deleted-tail witnesses instead
of cut-partition rows. -/
theorem actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedSeededDeletedTailWitnesses
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeConnectedRawOrbitSourceRows inputs)
    (deleted_tail_witnesses :
      let selectedRows :
          SelectedSeededRawFaceSuccOrbitSourceRows inputs :=
        S2_agent_20260520_selectedSeededRawFaceSuccOrbitSourceRows_of_connectedRawOrbitSourceRows
          (C := C) (inputs := inputs) rows
      SelectedSeededRawOrbitRepeatedTailWitnessSource selectedRows) :
    ActualCarrierDegreeTwoSource inputs := by
  let selectedRows :
      SelectedSeededRawFaceSuccOrbitSourceRows inputs :=
    S2_agent_20260520_selectedSeededRawFaceSuccOrbitSourceRows_of_connectedRawOrbitSourceRows
      (C := C) (inputs := inputs) rows
  exact
    actualCarrierDegreeTwo_of_selectedSeededRawFaceSuccOrbitSourceRows_deletedTailWitnesses
      (C := C) (inputs := inputs) selectedRows deleted_tail_witnesses

set_option linter.style.longLine false in
/-- Family form of
`actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedSeededDeletedTailWitnesses`. -/
theorem actualCarrierDegreeTwo_family_of_connectedRawOrbitSourceRows_selectedSeededDeletedTailWitnesses
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun rows : BoundaryFreeConnectedRawOrbitSourceRows inputs =>
            Nonempty
              (let selectedRows :
                  SelectedSeededRawFaceSuccOrbitSourceRows inputs :=
                S2_agent_20260520_selectedSeededRawFaceSuccOrbitSourceRows_of_connectedRawOrbitSourceRows
                  (C := C) (inputs := inputs) rows
               SelectedSeededRawOrbitRepeatedTailWitnessSource selectedRows)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases source C inputs with ⟨rows, deleted_tail_witnesses⟩
  rcases deleted_tail_witnesses with ⟨witness⟩
  exact
    actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedSeededDeletedTailWitnesses
      (C := C) (inputs := inputs) rows witness

/-- Boundary-free local two-germ rows erase directly to actual carrier degree
two through the checked local-sector route.

This is a source-facing reducer, not a cycle or induced-graph shortcut: the
input still supplies the two actual selected `unboundedFrontierEdgeSet` germs
at every concrete unbounded-frontier vertex. -/
theorem actualCarrierDegreeTwo_of_localTwoGermRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    ActualCarrierDegreeTwoSource inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  simpa [ActualCarrierDegreeTwoSource] using
    (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_localSectorRows
      (C := C) (inputs := inputs)
      (localSectorRows_of_localTwoGermRows rows))

/-- Family form of `actualCarrierDegreeTwo_of_localTwoGermRows`. -/
theorem actualCarrierDegreeTwo_family_of_localTwoGermRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    actualCarrierDegreeTwo_of_localTwoGermRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Actual carrier degree two supplies the pointwise local two-germ family.

This is the reverse direction to `actualCarrierDegreeTwo_of_localTwoGermRows`.
It factors through the concrete carrier neighbour finset, so the selected heads
are actual `unboundedFrontierEdgeSet` neighbours and the local germ row is
obtained from the checked vertex-star isolation reducer. -/
noncomputable def localTwoGermRows_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    localTwoGermRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs)
      (by simpa [ActualCarrierDegreeTwoSource] using hdegree)

set_option linter.style.longLine false in
/-- Family form of `localTwoGermRows_of_actualCarrierDegreeTwo`. -/
noncomputable def localTwoGermRows_family_of_actualCarrierDegreeTwo
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a := by
  intro m C inputs
  exact localTwoGermRows_of_actualCarrierDegreeTwo
    (C := C) inputs (source C inputs)

set_option linter.style.longLine false in
/-- Pointwise local two-germ rows are equivalent to actual carrier degree two.

This records the live local S2 leaf in the graph-theoretic form used by the
carrier source files: the remaining proof obligation is exactly
two-regularity of the concrete selected unbounded-frontier carrier graph. -/
theorem nonempty_localTwoGermRows_iff_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a) ↔
      ActualCarrierDegreeTwoSource inputs := by
  constructor
  · rintro ⟨rows⟩
    exact actualCarrierDegreeTwo_of_localTwoGermRows
      (C := C) (inputs := inputs) rows
  · intro hdegree
    exact ⟨localTwoGermRows_of_actualCarrierDegreeTwo
      (C := C) inputs hdegree⟩

set_option linter.style.longLine false in
/-- Family-level exact residual for the pointwise local two-germ source. -/
theorem localTwoGermRows_family_iff_actualCarrierDegreeTwo :
    (forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Nonempty
          (forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a)) ↔
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) := by
  constructor
  · intro source m C inputs
    exact (nonempty_localTwoGermRows_iff_actualCarrierDegreeTwo
      (C := C) (inputs := inputs)).1 (source C inputs)
  · intro source m C inputs
    exact (nonempty_localTwoGermRows_iff_actualCarrierDegreeTwo
      (C := C) (inputs := inputs)).2 (source C inputs)

set_option linter.style.longLine false in
/-- Cycle-row handoff from the reduced topology surface and actual
two-regularity of the selected unbounded-frontier carrier graph.

This is the local branch in its sharp graph-theoretic form: the topology
source gives preconnectedness of the actual unbounded exterior frontier, and
the local source is only degree two of the concrete carrier graph whose edges
are selected by `unboundedFrontierEdgeSet`. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_localTwoGermRows_20260521i1
    inputs frontier_preconnected
    (localTwoGermRows_of_actualCarrierDegreeTwo
      (C := C) inputs hdegree)

set_option linter.style.longLine false in
/-- Family form of the preconnected-topology / actual-carrier-degree handoff. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs := by
  intro m C inputs
  exact
    unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
      (C := C) inputs frontier_preconnected (source C inputs)

set_option linter.style.longLine false in
/-- Finite planar outer-component theorem handoff from preconnected topology
and actual selected-carrier degree two. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
      frontier_preconnected source)

set_option linter.style.longLine false in
/-- Cycle-row handoff from the lower closed-split topology source plus actual
degree two of the selected unbounded-frontier carrier graph. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_closedSeparationForcesContinuumSeparation_actualCarrierDegreeTwo_20260521j1
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (closed_split_forces_continuum_split :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
    (C := C) inputs
    (planarContinuumUnboundedComplementFrontierPreconnected_of_closedSeparationForcesContinuumSeparation
      closed_split_forces_continuum_split)
    hdegree

set_option linter.style.longLine false in
/-- Family form of the closed-split topology / actual-carrier-degree handoff. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_closedSeparationForcesContinuumSeparation_actualCarrierDegreeTwo_20260521j1
    (closed_split_forces_continuum_split :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs := by
  intro m C inputs
  exact
    unboundedExteriorFrontierCycleRows_of_closedSeparationForcesContinuumSeparation_actualCarrierDegreeTwo_20260521j1
      (C := C) inputs closed_split_forces_continuum_split (source C inputs)

set_option linter.style.longLine false in
/-- Finite planar outer-component theorem handoff from the lower closed-split
topology source and actual selected-carrier degree two. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_closedSeparationForcesContinuumSeparation_actualCarrierDegreeTwo_20260521j1
    (closed_split_forces_continuum_split :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_closedSeparationForcesContinuumSeparation_actualCarrierDegreeTwo_20260521j1
      closed_split_forces_continuum_split source)

/-- Family form of
`actualCarrierDegreeTwo_of_rawFaceSuccOrbitSourceRows`.

The source may use any concrete rotation system; the only data read by the
adapter is the `localSectorRows` field stored in `RawFaceSuccOrbitSourceRows`. -/
theorem actualCarrierDegreeTwo_family_of_rawFaceSuccOrbitSourceRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun start : UnitDistanceDart C =>
              Exists fun O : UnitDistanceRotationSystem.RawFaceSuccOrbit R start =>
                Nonempty (RawFaceSuccOrbitSourceRows (inputs := inputs) O)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases source C inputs with ⟨R, start, O, hrows⟩
  exact
    actualCarrierDegreeTwo_of_rawFaceSuccOrbitSourceRows
      (C := C) (inputs := inputs) (R := R) (start := start) (O := O)
      (Classical.choice hrows)

set_option linter.style.longLine false in
/-- Connected raw-orbit rows plus repeated-tail cut partitions for the
internally selected raw-tail orbit feed actual carrier degree two without the
older raw-orientation residual.

The proof uses only the raw `faceSucc` source rows produced from that selected
orbit, then erases their local-sector field to the concrete
`unboundedFrontierCarrierGraph` degree statement. -/
theorem actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedCutPartitions
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeConnectedRawOrbitSourceRows inputs)
    (cut_partitions :
      let selectedRows : SelectedRawTailCoverageSourceRows inputs :=
        S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
          (C := C) (inputs := inputs) rows
      SelectedRawOrbitRepeatedTailCutPartitions selectedRows) :
    ActualCarrierDegreeTwoSource inputs := by
  rcases
      exists_rawFaceSuccOrbit_sourceRows_of_connectedRawOrbitSourceRows_selectedCutPartitions_20260520cx
        (C := C) (inputs := inputs) rows cut_partitions with
    ⟨R, start, O, hrows⟩
  exact
    actualCarrierDegreeTwo_of_rawFaceSuccOrbitSourceRows
      (C := C) (inputs := inputs) (R := R) (start := start) (O := O)
      (Classical.choice hrows)

set_option linter.style.longLine false in
/-- Family form of
`actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedCutPartitions`. -/
theorem actualCarrierDegreeTwo_family_of_connectedRawOrbitSourceRows_selectedCutPartitions
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun rows : BoundaryFreeConnectedRawOrbitSourceRows inputs =>
            let selectedRows : SelectedRawTailCoverageSourceRows inputs :=
              S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
                (C := C) (inputs := inputs) rows
            SelectedRawOrbitRepeatedTailCutPartitions selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases source C inputs with ⟨rows, cut_partitions⟩
  exact
    actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedCutPartitions
      (C := C) (inputs := inputs) rows cut_partitions

set_option linter.style.longLine false in
/-- Primitive repeated-tail deleted-witness rows for the internally selected
raw-tail orbit also feed actual carrier degree two, via the checked
cut-partition eraser for that same selected orbit. -/
theorem actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnessSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeConnectedRawOrbitSourceRows inputs)
    (witnessRows :
      let selectedRows : SelectedRawTailCoverageSourceRows inputs :=
        S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
          (C := C) (inputs := inputs) rows
      SelectedRawOrbitRepeatedTailWitnessSource selectedRows) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedCutPartitions
    (C := C) (inputs := inputs) rows
    (selectedRawOrbitRepeatedTailCutPartitions_of_connectedRawOrbitSourceRows_repeatedTailWitnessSource_20260520
      (C := C) (inputs := inputs) rows witnessRows)

set_option linter.style.longLine false in
/-- Family form of
`actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnessSource`. -/
theorem actualCarrierDegreeTwo_family_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnessSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun rows : BoundaryFreeConnectedRawOrbitSourceRows inputs =>
            Nonempty
              (let selectedRows : SelectedRawTailCoverageSourceRows inputs :=
                S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
                  (C := C) (inputs := inputs) rows
               SelectedRawOrbitRepeatedTailWitnessSource selectedRows)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases source C inputs with ⟨rows, witnessRows⟩
  rcases witnessRows with ⟨witness⟩
  exact
    actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnessSource
      (C := C) (inputs := inputs) rows witness

set_option linter.style.longLine false in
/-- Selected raw-tail coverage rows plus repeated-tail cut partitions erase to
actual carrier degree two without any raw-orientation residual.

This is the generic selected-raw-tail version of the h12 local handoff; the
connected-row theorem below is just the internally selected specialization. -/
theorem actualCarrierDegreeTwo_of_selectedRawTailCoverageSourceRows_cutPartitions
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : SelectedRawTailCoverageSourceRows inputs)
    (cut_partitions : SelectedRawOrbitRepeatedTailCutPartitions rows) :
    ActualCarrierDegreeTwoSource inputs := by
  rcases
      exists_rawFaceSuccOrbit_sourceRows_of_selectedRawTailCoverage_cutPartitions_20260520cx
        (C := C) (inputs := inputs) rows cut_partitions with
    ⟨R, start, O, hrows⟩
  exact
    actualCarrierDegreeTwo_of_rawFaceSuccOrbitSourceRows
      (C := C) (inputs := inputs) (R := R) (start := start) (O := O)
      (Classical.choice hrows)

set_option linter.style.longLine false in
/-- Family form of
`actualCarrierDegreeTwo_of_selectedRawTailCoverageSourceRows_cutPartitions`. -/
theorem actualCarrierDegreeTwo_family_of_selectedRawTailCoverageSourceRows_cutPartitions
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun rows : SelectedRawTailCoverageSourceRows inputs =>
            SelectedRawOrbitRepeatedTailCutPartitions rows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases source C inputs with ⟨rows, cut_partitions⟩
  exact
    actualCarrierDegreeTwo_of_selectedRawTailCoverageSourceRows_cutPartitions
      (C := C) (inputs := inputs) rows cut_partitions

set_option linter.style.longLine false in
/-- Primitive repeated-tail deleted witnesses for selected raw-tail coverage
rows also erase to actual carrier degree two. -/
theorem actualCarrierDegreeTwo_of_selectedRawTailCoverageSourceRows_repeatedTailWitnessSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : SelectedRawTailCoverageSourceRows inputs)
    (witnessRows : SelectedRawOrbitRepeatedTailWitnessSource rows) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_selectedRawTailCoverageSourceRows_cutPartitions
    (C := C) (inputs := inputs) rows
    (selectedRawOrbitRepeatedTailCutPartitions_of_deletedTailWitnesses_20260520
      (C := C) (inputs := inputs) rows witnessRows)

set_option linter.style.longLine false in
/-- Family form of
`actualCarrierDegreeTwo_of_selectedRawTailCoverageSourceRows_repeatedTailWitnessSource`. -/
theorem actualCarrierDegreeTwo_family_of_selectedRawTailCoverageSourceRows_repeatedTailWitnessSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun rows : SelectedRawTailCoverageSourceRows inputs =>
            Nonempty (SelectedRawOrbitRepeatedTailWitnessSource rows)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases source C inputs with ⟨rows, witnessRows⟩
  rcases witnessRows with ⟨witness⟩
  exact
    actualCarrierDegreeTwo_of_selectedRawTailCoverageSourceRows_repeatedTailWitnessSource
      (C := C) (inputs := inputs) rows witness

set_option linter.style.longLine false in
/-- Boundary-free no-third-germ rows are the only carrier-degree field used
from the connected raw-orbit package.

The raw orbit, carrier-connectedness, repeated-tail, and orientation fields are
needed for exterior boundary/cycle construction, but not for
`ActualCarrierDegreeTwoSource`: local-sector rows from the boundary-free
no-third-germ source already force degree two in the actual
`unboundedFrontierCarrierGraph`. -/
theorem actualCarrierDegreeTwo_of_boundaryFreeNoThirdGermSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeNoThirdGermSource inputs) :
    ActualCarrierDegreeTwoSource inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  simpa [ActualCarrierDegreeTwoSource] using
    (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_localSectorRows
      (C := C) (inputs := inputs) source.toLocalSectorRows)

set_option linter.style.longLine false in
/-- Claim `S2-agent-carrier-degree-raw-route-20260521k8`.

Shortest non-circular route from the current connected raw-orbit source rows
to `ActualCarrierDegreeTwoSource`: project the stored boundary-free
no-third-germ/local-sector source.  Thus the raw-orbit-specific leaves
`RawOrbitDartEdgeFrontierSource`, repeated-tail cut/witness rows, and selected
raw orientation are redundant for the carrier-degree target. -/
theorem S2_agent_carrier_degree_raw_route_20260521k8_of_connectedRawOrbitSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (rows : BoundaryFreeConnectedRawOrbitSourceRows inputs) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_boundaryFreeNoThirdGermSource
    (C := C) (inputs := inputs) rows.localSource

set_option linter.style.longLine false in
/-- Family form of the k8 connected raw-orbit carrier-degree reducer. -/
theorem
    S2_agent_carrier_degree_raw_route_family_20260521k8_of_connectedRawOrbitSourceRows
    (rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          BoundaryFreeConnectedRawOrbitSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_degree_raw_route_20260521k8_of_connectedRawOrbitSourceRows
      (C := C) (inputs := inputs) (rows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-raw-orbit-to-degree-source-20260521e59`.

The existing selected geometric raw face-successor package is enough to source
`ActualCarrierDegreeTwoSource`: choose the produced raw orbit, read its
`RawFaceSuccOrbitSourceRows.localSectorRows` field, and use the checked
actual-carrier local-sector-to-degree reducer.  No final boundary-cycle
assumption, W facade, induced frontier graph, arbitrary carrier cycle,
all-adjacent endpoint shortcut, or identity angular-order row is used. -/
theorem S2_agent_raw_orbit_to_degree_source_20260521e59
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Exists fun e : PlanarInterface.Edge m =>
            Exists fun p : PlanarInterface.Point =>
              Exists fun start : UnitDistanceDart C =>
                UnboundedExteriorFrontierEdgeLocalRows C inputs e p /\
                  start.tail = e.1 /\
                    start.head = e.2 /\
                      Exists fun O :
                        UnitDistanceRotationSystem.RawFaceSuccOrbit
                          (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.geometricUnitDistanceRotationSystem
                            C)
                          start =>
                        Nonempty (RawFaceSuccOrbitSourceRows (inputs := inputs) O)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases source C inputs with ⟨_e, _p, _start, _edgeRows, _htail, _hhead, O, hrows⟩
  exact
    actualCarrierDegreeTwo_of_rawFaceSuccOrbitSourceRows
      (C := C) (inputs := inputs) (O := O)
      (Classical.choice hrows)

/-- Actual carrier degree two is equivalent to the pure selected incident-edge
pair source.

The selected-edge source is stated on the actual `unboundedFrontierEdgeSet` at
vertices of the actual `unboundedFrontierCarrierGraph`: it chooses two selected
incident heads and proves that every other selected incident carrier edge has
one of those two heads. -/
theorem actualCarrierDegreeTwo_iff_localSelectedIncidentEdgePairSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    ActualCarrierDegreeTwoSource inputs <->
      Nonempty (LocalSelectedIncidentEdgePairSourceRows inputs) := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  simpa [ActualCarrierDegreeTwoSource] using
    (nonempty_localSelectedIncidentEdgePairSourceRows_iff_unboundedFrontierCarrierGraph_neighborFinset_card_two
      (C := C) (inputs := inputs)).symm

/-- Actual carrier degree two constructs the pure selected incident-edge pair
source.

The selected heads are chosen from the neighbour finset of the actual
`unboundedFrontierCarrierGraph C inputs`; their edge witnesses are read through
`unboundedFrontierCarrierGraph_adj_iff`, so the live edge source remains
`unboundedFrontierEdgeSet C inputs`. -/
noncomputable def localSelectedIncidentEdgePairSourceRows_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two
      (C := C) (inputs := inputs)
      (by simpa [ActualCarrierDegreeTwoSource] using hdegree)

/-- Family form of
`localSelectedIncidentEdgePairSourceRows_of_actualCarrierDegreeTwo`. -/
noncomputable def localSelectedIncidentEdgePairSourceRows_family_of_actualCarrierDegreeTwo
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    localSelectedIncidentEdgePairSourceRows_of_actualCarrierDegreeTwo
      (C := C) inputs (source C inputs)

/-- Family form from concrete actual-carrier neighbour-pair rows. -/
noncomputable def localSelectedIncidentEdgePairSourceRows_family_of_neighborPairRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    localSelectedIncidentEdgePairSourceRows_of_neighborPairRows
      (C := C) inputs (source C inputs)

/-- Claim `S2-agent-local-selected-source-from-carrier-degree-20260521e70`.

The family source
`forall C inputs, LocalSelectedIncidentEdgePairSourceRows inputs` is strictly
reduced to actual degree two of the concrete unbounded-frontier carrier graph.
The proof stays on actual selected `unboundedFrontierEdgeSet` incidences and
does not introduce induced frontier graphs, all-adjacent endpoint rows, or
selected-head outgoing-list no-between rows. -/
noncomputable def
    S2_agent_local_selected_source_from_carrier_degree_20260521e70
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_family_of_actualCarrierDegreeTwo
    source

/-- Neighbour-pair variant of
`S2_agent_local_selected_source_from_carrier_degree_20260521e70`.

This keeps the even lower source as pointwise actual-carrier neighbour-pair
rows, whose selected heads already carry genuine `unboundedFrontierEdgeSet`
incidence witnesses. -/
noncomputable def
    S2_agent_local_selected_source_from_neighborPairRows_20260521e70
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_family_of_neighborPairRows
    source

/-- The pure selected incident-edge pair source gives actual carrier degree two. -/
theorem actualCarrierDegreeTwo_of_localSelectedIncidentEdgePairSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    ActualCarrierDegreeTwoSource inputs :=
  (actualCarrierDegreeTwo_iff_localSelectedIncidentEdgePairSourceRows
    (C := C) inputs).2 ⟨source⟩

set_option linter.style.longLine false in
/-- Claim `S2-agent-actual-carrier-degree-two-source-20260521e58`.

The bare family source
`forall C inputs, ActualCarrierDegreeTwoSource inputs` is strictly reduced to
the pure selected incident-edge pair source for the same finite planar input
package.  The residual still talks only about actual selected
`unboundedFrontierEdgeSet` incidences at vertices of the actual
`unboundedFrontierCarrierGraph`; it does not use induced frontier graphs,
arbitrary cycles, all-adjacent endpoint rows, all-outgoing no-between rows, or
final boundary-cycle rows. -/
theorem S2_agent_actual_carrier_degree_two_source_20260521e58
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    actualCarrierDegreeTwo_of_localSelectedIncidentEdgePairSourceRows
      (C := C) (inputs := inputs) (source C inputs)

/-- Family-level exact residual for the actual carrier degree-two source in
the pure selected-incident-edge-pair form. -/
theorem actualCarrierDegreeTwo_family_iff_localSelectedIncidentEdgePairSourceRows :
    (forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs) <->
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Nonempty (LocalSelectedIncidentEdgePairSourceRows inputs)) := by
  constructor
  · intro source m C inputs
    exact ⟨
      localSelectedIncidentEdgePairSourceRows_of_actualCarrierDegreeTwo
        (C := C) inputs (source C inputs)⟩
  · intro source m C inputs
    exact
      actualCarrierDegreeTwo_of_localSelectedIncidentEdgePairSourceRows
        (C := C) (inputs := inputs) (Classical.choice (source C inputs))

/-- Family-level exact residual in the concrete neighbour-pair form. -/
theorem actualCarrierDegreeTwo_family_iff_neighborPairRows :
    (forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs) <->
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Nonempty
            (forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
              UnboundedFrontierCarrierNeighborPairAt inputs a)) := by
  constructor
  · intro source m C inputs
    exact
      (actualCarrierDegreeTwo_iff_neighborPairRows
        (C := C) inputs).1 (source C inputs)
  · intro source m C inputs
    exact
      (actualCarrierDegreeTwo_iff_neighborPairRows
        (C := C) inputs).2 (source C inputs)

/-- Exact residual for the actual carrier degree-two source.

The remaining local source is the sharp cut-partition package: two genuine
incident `unboundedFrontierEdgeSet` heads at each actual unbounded-frontier
carrier vertex, plus a cut-partition contradiction for any third carrier
neighbour. -/
theorem actualCarrierDegreeTwo_iff_cutPartitionInputSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    ActualCarrierDegreeTwoSource inputs <->
      Nonempty
        (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs) := by
  constructor
  · intro hdegree
    exact
      ⟨unboundedFrontierCarrierNeighborPairCutPartitionInputSource_of_localSectorRows
        (C := C) (inputs := inputs)
        (localSectorRows_of_actualCarrierDegreeTwo
          (C := C) inputs hdegree)⟩
  · rintro ⟨source⟩
    exact actualCarrierDegreeTwo_of_cutPartitionInputSource
      (C := C) (inputs := inputs) source

/-- Exact fieldwise residual for the live actual-carrier degree-two source.

This pins the current local leaf to the already named e32 source in
`S2CarrierCutSource`: at each actual carrier vertex it names two genuine
`unboundedFrontierEdgeSet` heads and asks every third actual carrier neighbour
for a concrete cut partition. -/
theorem actualCarrierDegreeTwo_iff_carrierCutFieldwise
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    ActualCarrierDegreeTwoSource inputs <->
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs := by
  constructor
  · intro hdegree
    exact
      (S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_exact_iff
        (C := C) (inputs := inputs)).1
        ((actualCarrierDegreeTwo_iff_cutPartitionInputSource
          (C := C) inputs).1 hdegree)
  · intro source
    exact
      actualCarrierDegreeTwo_of_cutPartitionInputSource
        (C := C) (inputs := inputs)
        (S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
          (C := C) (inputs := inputs) source)

/-- Family reducer from the named e32 fieldwise cut source to the live
actual-carrier degree-two leaf. -/
theorem actualCarrierDegreeTwo_family_of_carrierCutFieldwise
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    (actualCarrierDegreeTwo_iff_carrierCutFieldwise
      (C := C) inputs).2 (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-actual-carrier-degree-20260521k7`.

The bare actual-carrier degree-two leaf is lowered to the e32 fieldwise
carrier-cut source.  This residual stays on the actual
`unboundedFrontierCarrierGraph`: at each actual frontier-carrier vertex it
names two genuine `unboundedFrontierEdgeSet` incident heads and supplies a
cut-partition payload for any third actual carrier neighbour.  It uses no
induced frontier graph, arbitrary cycle, all-adjacent endpoint shortcut, or
all-outgoing no-between row. -/
theorem S2_agent_actual_carrier_degree_20260521k7_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs) :
    ActualCarrierDegreeTwoSource inputs :=
  (actualCarrierDegreeTwo_iff_carrierCutFieldwise
    (C := C) inputs).2 source

set_option linter.style.longLine false in
/-- Exact k7 residual for the actual-carrier degree-two source. -/
theorem S2_agent_actual_carrier_degree_20260521k7_exact_iff_carrierCutFieldwise
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    ActualCarrierDegreeTwoSource inputs <->
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs :=
  actualCarrierDegreeTwo_iff_carrierCutFieldwise
    (C := C) inputs

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_actual_carrier_degree_20260521k7_of_carrierCutFieldwise`. -/
theorem S2_agent_actual_carrier_degree_family_20260521k7_of_carrierCutFieldwise
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_family_of_carrierCutFieldwise source

set_option linter.style.longLine false in
/-- Claim `S2-q54-actual-carrier-degree-worker`.

Source-level handoff from the raw-orbit third-neighbour repeated-tail index
row plus the repeated-tail minimal deleted-tail separation row to the actual
carrier degree-two source.  This only composes the checked q36 carrier-cut
eraser with the existing e32-to-degree-two eraser; it introduces no
actual-sector rows, boundary-cycle rows, W32 rows, induced frontier graph,
arbitrary carrier cycle, or endpoint shortcut. -/
theorem
    S2_q54_actualCarrierDegreeTwoSource_of_rawOrbit_thirdNeighborRepeatedTailIndex_minimalDeletedTailSeparation
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
      S2CarrierCutSource.S2_q36_rawFaceWalkThirdCarrierNeighborRepeatedTailIndexSource
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
    ActualCarrierDegreeTwoSource inputs :=
  S2_agent_actual_carrier_degree_20260521k7_of_carrierCutFieldwise
    (C := C) (inputs := inputs)
    (S2CarrierCutSource.S2_q36_carrierCutFieldwise_of_rawOrbit_thirdNeighborRepeatedTailIndex_minimalDeletedTailSeparation
      (C := C) (inputs := inputs) O
      edge_openSegment_frontier frontier_vertex_tail_coverage
      raw_pred_succ_tail_ne thirdRepeatedTail minimalSeparation)

set_option linter.style.longLine false in
/-- Family form of the q54 raw-orbit-to-actual-carrier-degree handoff. -/
theorem
    S2_q54_actualCarrierDegreeTwoSource_family_of_rawOrbit_thirdNeighborRepeatedTailIndex_minimalDeletedTailSeparation
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
                S2CarrierCutSource.S2_q36_rawFaceWalkThirdCarrierNeighborRepeatedTailIndexSource
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
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  rcases rawRows C inputs with
    ⟨R, start, O, edgeRows, tailCoverage, predSuccNe,
      thirdRepeatedTail, minimalSeparation⟩
  exact
    S2_q54_actualCarrierDegreeTwoSource_of_rawOrbit_thirdNeighborRepeatedTailIndex_minimalDeletedTailSeparation
      (C := C) (inputs := inputs) O edgeRows tailCoverage predSuccNe
      thirdRepeatedTail minimalSeparation

set_option linter.style.longLine false in
/-- q55 source-facing actual-carrier degree-two handoff on the q32 raw orbit.

The q32 raw geometric orbit package already supplies the concrete raw orbit,
edge-frontier honesty, local-sector rows, and raw predecessor/successor
separation.  This theorem exposes only the two remaining finite plane-graph
source leaves on that same orbit: a third-neighbour repeated-tail index row and
the minimal deleted-tail separation row for repeated raw tails.  It does not
use actual-sector rows, final boundary cycles, W32 rows, induced frontier
graphs, arbitrary cycles, endpoint shortcuts, or identity angular order. -/
theorem
    S2_q55_actualCarrierDegreeTwoSource_family_of_componentTopology_geometricSelection_strictSuccessor_thirdRepeatedTail_minimalDeletedTailSeparation
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (strictSuccessorOrder :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (thirdRepeatedTail :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let pkg :=
            S2_q32_rawGeometricOrbitPackage_family_of_componentTopology_geometricSelection_strictSuccessor
              componentTopology geometricSelection strictSuccessorOrder
              C inputs
          S2CarrierCutSource.S2_q36_rawFaceWalkThirdCarrierNeighborRepeatedTailIndexSource
            (inputs := inputs) pkg.2.2.2.1)
    (minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let pkg :=
            S2_q32_rawGeometricOrbitPackage_family_of_componentTopology_geometricSelection_strictSuccessor
              componentTopology geometricSelection strictSuccessorOrder
              C inputs
          forall {i j : Fin pkg.2.2.2.1.period},
            i ≠ j ->
            (pkg.2.2.2.1.dart i).tail = (pkg.2.2.2.1.dart j).tail ->
              Exists fun left :
                  {l : Fin pkg.2.2.2.1.period //
                    cyclicForwardOpenArc i j l ∧
                      (pkg.2.2.2.1.dart l).tail ≠
                        (pkg.2.2.2.1.dart i).tail} =>
                Exists fun right :
                    {r : Fin pkg.2.2.2.1.period //
                      cyclicForwardOpenArc j i r ∧
                        (pkg.2.2.2.1.dart r).tail ≠
                          (pkg.2.2.2.1.dart i).tail} =>
                  ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
                      ({(pkg.2.2.2.1.dart i).tail}ᶜ : Set (Fin m))).Reachable
                      ⟨(pkg.2.2.2.1.dart left.1).tail, by
                        simpa using left.2.2⟩
                      ⟨(pkg.2.2.2.1.dart right.1).tail, by
                        simpa using right.2.2⟩) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  let pkg :=
    S2_q32_rawGeometricOrbitPackage_family_of_componentTopology_geometricSelection_strictSuccessor
      componentTopology geometricSelection strictSuccessorOrder C inputs
  let coverage :
      RawOrbitCoverageSourceRows (inputs := inputs) pkg.2.2.2.1 :=
    pkg.2.2.2.2.2
  have htail :
      forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
        Exists fun k : Fin pkg.2.2.2.1.period =>
          (pkg.2.2.2.1.dart k).tail = a.1 :=
    rawOrbitCoverage_frontierVertexTailCoverageFromLocalSectorRows
      (C := C) (inputs := inputs) coverage pkg.1
  have hpred_succ :
      forall k : Fin pkg.2.2.2.1.period,
        (pkg.2.2.2.1.dart
            (PlanarInterface.cyclicPred pkg.2.2.2.1.period_pos k)).tail ≠
          (pkg.2.2.2.1.dart
            (PlanarInterface.cyclicSucc pkg.2.2.2.1.period_pos k)).tail :=
    coverage.raw_pred_succ_tail_ne pkg.1
  exact
    S2_q54_actualCarrierDegreeTwoSource_of_rawOrbit_thirdNeighborRepeatedTailIndex_minimalDeletedTailSeparation
      (C := C) (inputs := inputs) pkg.2.2.2.1
      coverage.edge_openSegment_frontier htail hpred_succ
      (thirdRepeatedTail C inputs) (minimalSeparation C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-k6i-local-sector-source`, pointwise cut-field form.

The requested pointwise local-sector rows are lowered to the exact e32
fieldwise carrier-cut source.  The reduction first recovers the actual
carrier degree-two row from the selected cut-partition package and then uses
the existing local-sector constructor for actual unbounded-frontier carrier
vertices.  No global outgoing-list no-between row is introduced. -/
noncomputable def S2_k6i_local_sector_rows_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_actualCarrierDegreeTwo
    (C := C) inputs
    ((actualCarrierDegreeTwo_iff_carrierCutFieldwise
      (C := C) inputs).2 source)

set_option linter.style.longLine false in
/-- Family form of the k6i local-sector cut-field lowering. -/
noncomputable def S2_k6i_local_sector_rows_family_of_carrierCutFieldwise
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    S2_k6i_local_sector_rows_of_carrierCutFieldwise
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact residual for the k6i pointwise local-sector source.

The remaining local source is precisely the e32 fieldwise carrier-cut package:
two actual `unboundedFrontierEdgeSet` incident heads at each actual
unbounded-frontier carrier vertex, plus cut partitions for any third carrier
neighbour. -/
theorem S2_k6i_local_sector_rows_nonempty_iff_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a) ↔
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs := by
  constructor
  · intro hlocal
    exact
      (actualCarrierDegreeTwo_iff_carrierCutFieldwise
        (C := C) inputs).1
        ((nonempty_localSectorRows_iff_actualCarrierDegreeTwo
          (C := C) (inputs := inputs)).1 hlocal)
  · intro source
    exact
      (nonempty_localSectorRows_iff_actualCarrierDegreeTwo
        (C := C) (inputs := inputs)).2
        ((actualCarrierDegreeTwo_iff_carrierCutFieldwise
          (C := C) inputs).2 source)

set_option linter.style.longLine false in
/-- Claim `S2-q25-carrier-cut-source`, local source form.

The actual carrier degree-two leaf is equivalent to the concrete r30
deleted-neighbour finite-plane local-separation primitive.  The reverse
direction is the checked deleted-neighbour degree eraser; the forward direction
chooses the actual local-sector rows and packages them as r30 rows. -/
theorem
    S2_q25_actualCarrierDegreeTwo_iff_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    ActualCarrierDegreeTwoSource inputs <->
      Nonempty
        (S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
          (C := C) inputs) := by
  constructor
  · intro hdegree
    exact
      ⟨S2_q18_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_localSectorRows
        (C := C) (inputs := inputs)
        (localSectorRows_of_actualCarrierDegreeTwo
          (C := C) inputs hdegree)⟩
  · rintro ⟨source⟩
    exact
      actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationInputSource
        (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- q25 local-sector rows directly from the r30 deleted-neighbour primitive. -/
noncomputable def
    S2_q25_localSectorRows_of_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_actualCarrierDegreeTwo
    (C := C) inputs
    (actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationInputSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- q25 no-cut selected-incident rows from the r30 deleted-neighbour primitive. -/
noncomputable def
    S2_q25_selectedIncidentRows_of_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_actualCarrierDegreeTwo
    (C := C) inputs
    (actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationInputSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- q25 equivalence between the e32 carrier-cut field and the concrete r30
deleted-neighbour finite-plane local-separation primitive. -/
theorem
    S2_q25_carrierCutFieldwise_iff_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs <->
      Nonempty
        (S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
          (C := C) inputs) :=
  Iff.trans
    (actualCarrierDegreeTwo_iff_carrierCutFieldwise
      (C := C) inputs).symm
    (S2_q25_actualCarrierDegreeTwo_iff_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs))

set_option linter.style.longLine false in
/-- q25 local-sector rows directly from the e32 carrier-cut field, exposed
through the r30 local-separation equivalence. -/
noncomputable def
    S2_q25_localSectorRows_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  S2_k6i_local_sector_rows_of_carrierCutFieldwise
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of the q25 r30-to-local-sector lowering. -/
noncomputable def
    S2_q25_localSectorRows_family_of_finitePlaneLocalSeparationPrimitive
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    S2_q25_localSectorRows_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Selected carrier/geometric-selection source from actual local-sector heads
and same-head r36 geometric rows.

The local-sector rows provide the two actual selected
`unboundedFrontierEdgeSet` heads and the concrete carrier `only` row.  The r36
premise is only the genuine non-wrap geometric consecutive row for those same
heads, so this avoids global outgoing-list no-between sources, endpoint
closure, final actual-sector rows, and raw-orbit declarations. -/
noncomputable def
    S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
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
  S2_codex_20260520_geometric_selection_input_source_of_localSectorRows_geometricOrderRows
    (C := C) (inputs := inputs) localSectorRows geometricRows

set_option linter.style.longLine false in
/-- r30/r36 selected carrier/geometric-selection source.

The r30 deleted-neighbour local-separation primitive is first erased to actual
selected local-sector heads; the r36 rows are then consumed for those exact
heads.  This is a source-facing bridge for the raw-orbit producer's selected
carrier/geometric package, without depending on seeded raw-orbit declarations. -/
noncomputable def
    S2_q15_geometricSelectionInputSource_of_r30_r36_finitePlaneLocalSeparationPrimitive
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs)
    (geometricRows :
      S2_r36_selectedGeometricOrderRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs) source) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs := by
  let cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
    S2_dynamic_selected_carrier_neighbor_cut_source_20260522_of_deletedNeighborLocalSeparation
      (C := C) (inputs := inputs) source
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    S2_r56_localSectorRows_of_cutPartitionInputSource
      (C := C) (inputs := inputs) cutSource
  exact
    S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
      (C := C) (inputs := inputs) localSectorRows
      (by
        simpa [S2_r36_selectedGeometricOrderRows_of_finitePlaneLocalSeparationPrimitive,
          cutSource, localSectorRows] using geometricRows)

set_option linter.style.longLine false in
/-- Claim `S2-q19-local-sector-input-source`, object form.

The r30 deleted-neighbour local-separation primitive already forces the actual
carrier degree-two source.  The selected exterior-sector angular/no-between
rows are kept in the statement to align with the q18 local-sector surface, but
the shortest non-circular composition strictly lowers the degree-two leaf to
r30 alone. -/
theorem
    S2_q19_actualCarrierDegreeTwo_of_r30_selectedAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs)
    (_angularRows :
      S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs) source) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationInputSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- q19 local-sector row wrapper for the same r30/q18 surface. -/
noncomputable def
    S2_q19_localSectorRows_of_r30_selectedAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs)
    (angularRows :
      S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs) source) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_actualCarrierDegreeTwo
    (C := C) inputs
    (S2_q19_actualCarrierDegreeTwo_of_r30_selectedAngularNoBetweenRows
      (C := C) (inputs := inputs) source angularRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_q19_actualCarrierDegreeTwo_of_r30_selectedAngularNoBetweenRows`. -/
theorem
    S2_q19_actualCarrierDegreeTwo_family_of_r30_selectedAngularNoBetweenRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs) (source C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs := by
  intro m C inputs
  exact
    S2_q19_actualCarrierDegreeTwo_of_r30_selectedAngularNoBetweenRows
      (C := C) (inputs := inputs) (source C inputs)
      (angularRows C inputs)

set_option linter.style.longLine false in
/-- Family form of
`S2_q19_localSectorRows_of_r30_selectedAngularNoBetweenRows`. -/
noncomputable def
    S2_q19_localSectorRows_family_of_r30_selectedAngularNoBetweenRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs) (source C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a := by
  intro m C inputs
  exact
    S2_q19_localSectorRows_of_r30_selectedAngularNoBetweenRows
      (C := C) (inputs := inputs) (source C inputs)
      (angularRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q21-r30-neighbor-pair-source`, r30 cut-field form.

The deleted-neighbour finite-plane local-separation primitive is lowered to the
existing e32 fieldwise carrier-cut source: two actual
`unboundedFrontierEdgeSet` heads at each actual carrier vertex, with a concrete
cut partition for every third actual carrier neighbour. -/
noncomputable def
    S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs) :
    S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
      (C := C) inputs :=
  S2_q18_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_localSectorRows
    (C := C) (inputs := inputs)
    (S2_k6i_local_sector_rows_of_carrierCutFieldwise
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of the q21 r30 cut-field lowering. -/
noncomputable def
    S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_family_of_carrierCutFieldwise
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
          (C := C) inputs := by
  intro m C inputs
  exact
    S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Concrete actual carrier neighbour-pair rows from the same q21 cut-field
source. -/
noncomputable def
    S2_q21_neighborPairRows_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a :=
  Classical.choice
    ((actualCarrierDegreeTwo_iff_neighborPairRows
      (C := C) inputs).1
      ((actualCarrierDegreeTwo_iff_carrierCutFieldwise
        (C := C) inputs).2 source))

set_option linter.style.longLine false in
/-- q21 source package for the r30/r36 selected-head pair together with the
actual carrier neighbour-pair rows. -/
abbrev S2_q21_r30_r36_neighborPairSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) : Prop :=
  Exists fun source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs =>
    S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
      (C := C) (inputs := inputs) source ∧
    Nonempty
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a)

set_option linter.style.longLine false in
/-- q21 lowering of the r30/r36/neighbour-pair source package.

The live lower source is the concrete e32 cut-field package.  The r36 angular
row is kept for the exact r30 primitive produced from that package; the
neighbour-pair rows are recovered through the existing no-cut cut-partition
degree-two eraser. -/
theorem
    S2_q21_r30_r36_neighborPairSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs)
    (angularRows :
      S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs)
        (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
          (C := C) (inputs := inputs) source)) :
    S2_q21_r30_r36_neighborPairSource (C := C) inputs := by
  exact
    ⟨S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source,
      angularRows,
      ⟨S2_q21_neighborPairRows_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source⟩⟩

set_option linter.style.longLine false in
/-- Family form of the q21 r30/r36/neighbour-pair cut-field lowering. -/
theorem
    S2_q21_r30_r36_neighborPairSource_family_of_carrierCutFieldwise_selectedAngularNoBetweenRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs)
            (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
              (C := C) (inputs := inputs) (source C inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q21_r30_r36_neighborPairSource (C := C) inputs := by
  intro m C inputs
  exact
    S2_q21_r30_r36_neighborPairSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
      (C := C) (inputs := inputs) (source C inputs)
      (angularRows C inputs)

set_option linter.style.longLine false in
/-- q22 r30/r36/neighbour-pair package from concrete finite-plane
deleted-neighbour local-separation data and the same-head selected angular row.

This removes the e32 carrier-cut field from the q21 package surface: r30 is the
deleted-neighbour local-separation input source itself, and the neighbour-pair
rows are recovered by the checked no-cut/degree-two eraser. -/
theorem
    S2_q22_r30_r36_neighborPairSource_of_finitePlaneLocalSeparationPrimitive_selectedAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs)
    (angularRows :
      S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs) source) :
    S2_q21_r30_r36_neighborPairSource (C := C) inputs := by
  exact
    ⟨source, angularRows,
      ⟨neighborPairRows_of_actualCarrierDegreeTwo
        (C := C) inputs
        (actualCarrierDegreeTwo_of_deletedNeighborLocalSeparationInputSource
          (C := C) (inputs := inputs) source)⟩⟩

set_option linter.style.longLine false in
/-- q22 r30/r36/neighbour-pair package from concrete local separation and
primitive sorted-list index rows for the selected heads. -/
theorem
    S2_q22_r30_r36_neighborPairSource_of_finitePlaneLocalSeparationPrimitive_indexRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs)
    (indexRows :
      S2_q22_selectedGeometricOrderIndexRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs) source) :
    S2_q21_r30_r36_neighborPairSource (C := C) inputs :=
  S2_q22_r30_r36_neighborPairSource_of_finitePlaneLocalSeparationPrimitive_selectedAngularNoBetweenRows
    (C := C) (inputs := inputs) source
    (S2_q22_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive_indexRows
      (C := C) (inputs := inputs) source indexRows)

set_option linter.style.longLine false in
/-- Family form of the q22 r30/r36/neighbour-pair package from concrete local
separation and primitive selected-head index rows. -/
theorem
    S2_q22_r30_r36_neighborPairSource_family_of_finitePlaneLocalSeparationPrimitive_indexRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q22_selectedGeometricOrderIndexRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs) (source C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q21_r30_r36_neighborPairSource (C := C) inputs := by
  intro m C inputs
  exact
    S2_q22_r30_r36_neighborPairSource_of_finitePlaneLocalSeparationPrimitive_indexRows
      (C := C) (inputs := inputs) (source C inputs)
      (indexRows C inputs)

set_option linter.style.longLine false in
/-- q23 selected-neighbour geometric-selection source from concrete r30 local
separation and same-head r36 angular rows. -/
noncomputable def
    S2_q23_geometricSelectionInputSource_of_finitePlaneLocalSeparationPrimitive_selectedAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs)
    (angularRows :
      S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs) source) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_q15_geometricSelectionInputSource_of_r30_r36_finitePlaneLocalSeparationPrimitive
    (C := C) (inputs := inputs) source
    (S2_r36_selectedGeometricOrderRows_of_finitePlaneLocalSeparationPrimitive_angularNoBetweenRows
      (C := C) (inputs := inputs) source angularRows)

set_option linter.style.longLine false in
/-- q23 r30 package from exact deleted-neighbour local-separation fields. -/
noncomputable def
    S2_q23_finitePlaneLocalSeparationPrimitive_of_deletedNeighborExactField
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
        inputs) :
    S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
      (C := C) inputs :=
  S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_localPlanarSeparationInputSource
    (C := C) (inputs := inputs)
    (S2_agent_deleted_neighbor_local_separation_worker_20260521e6
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- q23 selected-neighbour geometric-selection source from exact
deleted-neighbour local-separation fields and same-head r36 angular rows. -/
noncomputable def
    S2_q23_geometricSelectionInputSource_of_deletedNeighborExactField_selectedAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
        inputs)
    (angularRows :
      let r30source :
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs :=
        S2_q23_finitePlaneLocalSeparationPrimitive_of_deletedNeighborExactField
          (C := C) (inputs := inputs) source
      S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs) r30source) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs := by
  let r30source :
      S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
        (C := C) inputs :=
    S2_q23_finitePlaneLocalSeparationPrimitive_of_deletedNeighborExactField
      (C := C) (inputs := inputs) source
  exact
    S2_q23_geometricSelectionInputSource_of_finitePlaneLocalSeparationPrimitive_selectedAngularNoBetweenRows
      (C := C) (inputs := inputs) r30source
      (by
        simpa [r30source] using angularRows)

set_option linter.style.longLine false in
/-- Family form of the q23 exact-field/r36 geometric-selection lowering. -/
noncomputable def
    S2_q23_geometricSelectionInputSource_family_of_deletedNeighborExactField_selectedAngularNoBetweenRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let r30source :
              S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
                (C := C) inputs :=
            S2_q23_finitePlaneLocalSeparationPrimitive_of_deletedNeighborExactField
              (C := C) (inputs := inputs) (source C inputs)
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs) r30source) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_q23_geometricSelectionInputSource_of_deletedNeighborExactField_selectedAngularNoBetweenRows
      (C := C) (inputs := inputs) (source C inputs)
      (angularRows C inputs)

set_option linter.style.longLine false in
/-- q23 selected-neighbour geometric-selection source from the e32 cut field
and same-head r36 angular rows. -/
noncomputable def
    S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs)
    (angularRows :
      S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs)
        (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
          (C := C) (inputs := inputs) source)) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs :=
  S2_q23_geometricSelectionInputSource_of_finitePlaneLocalSeparationPrimitive_selectedAngularNoBetweenRows
    (C := C) (inputs := inputs)
    (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
      (C := C) (inputs := inputs) source)
    angularRows

set_option linter.style.longLine false in
/-- Family form of the q23 e32/r36 geometric-selection lowering. -/
noncomputable def
    S2_q23_geometricSelectionInputSource_family_of_carrierCutFieldwise_selectedAngularNoBetweenRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs)
            (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
              (C := C) (inputs := inputs) (source C inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
      (C := C) (inputs := inputs) (source C inputs)
      (angularRows C inputs)

set_option linter.style.longLine false in
/-- q30 selected actual-carrier `faceSucc` angle rows rebuilt directly from
the e32 carrier-cut fieldwise source, the r36 same-head angular row, selected
orientation, and local strict order.

This names the exact non-endpoint angular source used by the raw exterior
face-orbit route; it does not pass through endpoint-local-radius rows,
actual-sector rows, W32 consumers, induced frontier graphs, arbitrary cycles,
or identity angular order. -/
theorem
    S2_q30_selectedActualCarrierFaceSuccAngleRows_family_of_carrierCutFieldwise_selectedAngular_orientation_localStrictOrder
    (carrierCutFieldwise :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs)
            (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)))
    (orientationRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geomHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geomHere
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
            inputs selectedRows)
    (localStrictOrder :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geomHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geomHere
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let geomHere :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
            (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
            (angularRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geomHere
        RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
          inputs selectedRows := by
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
    S2_q23_geometricSelectionInputSource_family_of_carrierCutFieldwise_selectedAngularNoBetweenRows
      carrierCutFieldwise angularRows
  intro m C inputs
  exact
    S2_selected_faceSucc_angle_source_family_of_geometricSelection_orientationRows_localStrictOrder
      geometricSelection orientationRows localStrictOrder
      (C := C) inputs

set_option linter.style.longLine false in
/-- q27 selected endpoint local-radius source for the current e32/r36 selected
carrier pair.

This intentionally exposes the selected-germ source below the broader
`IncidentGermEndpointLocalRadiusCoversRows` residual: the rows are only for the
two actual selected `unboundedFrontierEdgeSet` heads projected from the current
local selected-incident edge pair. -/
theorem
    S2_q27_selectedEndpointLocalRadiusSourceRows_of_carrierCutFieldwise_selectedAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs)
    (angularRows :
      S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs)
        (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
          (C := C) (inputs := inputs) source)) :
    let geometricSelection :
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs :=
      S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
        (C := C) (inputs := inputs) source angularRows
    let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
      S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    IncidentGermSelectedEndpointLocalRadiusSourceRows
      (C := C) (inputs := inputs) selectedRows := by
  let geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
      (C := C) (inputs := inputs) source angularRows
  let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
    S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) geometricSelection
  exact
    incidentGermSelectedEndpointLocalRadiusSourceRows_of_selectedRows_20260522q13
      (C := C) (inputs := inputs) selectedRows

set_option linter.style.longLine false in
/-- Family form of the q27 e32/r36 selected endpoint local-radius source. -/
theorem
    S2_q27_selectedEndpointLocalRadiusSourceRows_family_of_carrierCutFieldwise_selectedAngularNoBetweenRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs)
            (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
              (C := C) (inputs := inputs) (source C inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
            (C := C) (inputs := inputs) (source C inputs)
            (angularRows C inputs)
        let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
          S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        IncidentGermSelectedEndpointLocalRadiusSourceRows
          (C := C) (inputs := inputs) selectedRows := by
  intro m C inputs
  exact
    S2_q27_selectedEndpointLocalRadiusSourceRows_of_carrierCutFieldwise_selectedAngularNoBetweenRows
      (C := C) (inputs := inputs) (source C inputs)
      (angularRows C inputs)

set_option linter.style.longLine false in
/-- q23 selected incident-germ membership from the e32/r36 geometric source and
the checked endpoint-local radius cover. -/
theorem
    S2_q23_selectedNeighborIncidentGermFrontierEdgeMembershipRows_of_carrierCutFieldwise_selectedAngularNoBetweenRows_endpointLocalRadiusCovers
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs)
    (angularRows :
      S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
        (C := C) (inputs := inputs)
        (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
          (C := C) (inputs := inputs) source))
    (endpointLocalRadiusCovers :
      let geometricSelection :
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
        S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
          (C := C) (inputs := inputs) source angularRows
      let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
        S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      let localEndpointRows :
          IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
        S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedRows
      IncidentGermEndpointLocalRadiusCoversRows
        (C := C) (inputs := inputs) (selectedRows := selectedRows)
        localEndpointRows) :
    SelectedNeighborIncidentGermFrontierEdgeMembershipRows
      (C := C) (inputs := inputs)
      (S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
        (C := C) (inputs := inputs) source angularRows) := by
  let geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
      (C := C) (inputs := inputs) source angularRows
  exact
    selectedNeighborIncidentGermFrontierEdgeMembershipRows_of_endpointLocalRadiusCovers_20260522
      (C := C) (inputs := inputs) geometricSelection
      (by simpa [geometricSelection] using endpointLocalRadiusCovers)

set_option linter.style.longLine false in
/-- Family form of the q23 selected incident-germ lowering. -/
theorem
    S2_q23_selectedNeighborIncidentGermFrontierEdgeMembershipRows_family_of_carrierCutFieldwise_selectedAngularNoBetweenRows_endpointLocalRadiusCovers
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs)
            (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
              (C := C) (inputs := inputs) (source C inputs)))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
            (C := C) (inputs := inputs) (source C inputs)
            (angularRows C inputs)
        let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
          S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        let localEndpointRows :
            IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
          S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) selectedRows
        IncidentGermEndpointLocalRadiusCoversRows
          (C := C) (inputs := inputs) (selectedRows := selectedRows)
          localEndpointRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedNeighborIncidentGermFrontierEdgeMembershipRows
          (C := C) (inputs := inputs)
          (S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
            (C := C) (inputs := inputs) (source C inputs)
            (angularRows C inputs)) := by
  intro m C inputs
  exact
    S2_q23_selectedNeighborIncidentGermFrontierEdgeMembershipRows_of_carrierCutFieldwise_selectedAngularNoBetweenRows_endpointLocalRadiusCovers
      (C := C) (inputs := inputs) (source C inputs)
      (angularRows C inputs) (endpointLocalRadiusCovers C inputs)

set_option linter.style.longLine false in
/-- q24 actual-sector source with the geometric-selection leaf reduced to
e32/r36.

This composes the q23 actual-sector producer with the q23 carrier-local
geometric-selection reducer.  The selected incident-germ row remains explicit
so this theorem stays small and avoids expanding the endpoint-local-radius
branch inside the raw-orbit cyclic-cut type. -/
noncomputable def
    S2_q24_actualExteriorSectorInputSourceRows_family_of_kComponentPointsBetween_vertexIncident_carrierCutFieldwise_selectedAngular_incidentGerm_selectedCarrierRows_cyclicSuccCutPartitions
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (frontier_vertex_incident :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs)
    (carrierCutFieldwise :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs)
            (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)))
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)))
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geomHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geomHere
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (cyclicSuccCutPartitions :
      let localSectorRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRowsFamily_of_geometricSelection_localIncident_20260520
          (fun {_m} C inputs =>
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs))
      let topologyRows :=
        S2_q15_finiteDrawing_noClosed_noOpen_componentTopology_family_of_kComponentPointsBetween_localSectorRows_20260522
          points_between localSectorRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let componentTopology :
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
            S2_r13_component_topology_input_source_of_finiteDrawingNoOpenSeparation_vertexIncident_20260521r13
              (C := C) inputs topologyRows.2.1
              (frontier_vertex_incident C inputs)
          let geomHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geomHere
          let angleRows :
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
                inputs selectedRows :=
            S2_r15_selected_actual_carrier_faceSucc_angle_source_of_selectedCarrierRows
              (C := C) (inputs := inputs) selectedRows
              (selectedCarrierRows C inputs)
          let successorTailRows :
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_agent_raw_successor_tail_source_20260521k14
              (C := C) (inputs := inputs) selectedRows
              (S2_agent_raw_orbit_selectedCarrier_successorTail_source_20260521k15
                (C := C) (inputs := inputs) selectedRows
                (S2_k6k_faceSucc_tail_faceSucc_rows_source_of_selectedActualCarrierFaceSuccAngleRows
                  (C := C) (inputs := inputs) selectedRows angleRows))
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_successorTailRows_20260521r13
              (C := C) (inputs := inputs)
              componentTopology geomHere
              (incidentGermFrontierEdgeRows C inputs)
              (rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_eta
                successorTailRows)
          SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource
            selectedRawRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  exact
    S2_q23_actualExteriorSectorInputSourceRows_family_of_kComponentPointsBetween_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_cyclicSuccCutPartitions
      points_between frontier_vertex_incident
      (fun {m} C inputs =>
        S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
          (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
          (angularRows C inputs))
      incidentGermFrontierEdgeRows selectedCarrierRows cyclicSuccCutPartitions

set_option linter.style.longLine false in
/-- q24 actual-sector source with both the geometric-selection and
incident-germ leaves reduced to e32/r36 plus endpoint-local-radius covers.

This is the small q24-facing wrapper around the checked q23 incident-germ
lowering.  The endpoint premise remains the selected-head local-radius cover
for the actual selected unbounded-frontier germs induced by the rebuilt
geometric selection; it does not introduce an all-adjacent endpoint closure
row. -/
noncomputable def
    S2_q24_actualExteriorSectorInputSourceRows_family_of_kComponentPointsBetween_vertexIncident_carrierCutFieldwise_selectedAngular_endpointLocalRadiusCovers_selectedCarrierRows_cyclicSuccCutPartitions
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (frontier_vertex_incident :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs)
    (carrierCutFieldwise :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs)
            (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
            (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
            (angularRows C inputs)
        let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
          S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        let localEndpointRows :
            IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
          S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) selectedRows
        IncidentGermEndpointLocalRadiusCoversRows
          (C := C) (inputs := inputs) (selectedRows := selectedRows)
          localEndpointRows)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geomHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geomHere
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (cyclicSuccCutPartitions :
      let localSectorRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRowsFamily_of_geometricSelection_localIncident_20260520
          (fun {_m} C inputs =>
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs))
      let topologyRows :=
        S2_q15_finiteDrawing_noClosed_noOpen_componentTopology_family_of_kComponentPointsBetween_localSectorRows_20260522
          points_between localSectorRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let componentTopology :
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
            S2_r13_component_topology_input_source_of_finiteDrawingNoOpenSeparation_vertexIncident_20260521r13
              (C := C) inputs topologyRows.2.1
              (frontier_vertex_incident C inputs)
          let geomHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geomHere
          let angleRows :
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
                inputs selectedRows :=
            S2_r15_selected_actual_carrier_faceSucc_angle_source_of_selectedCarrierRows
              (C := C) (inputs := inputs) selectedRows
              (selectedCarrierRows C inputs)
          let successorTailRows :
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_agent_raw_successor_tail_source_20260521k14
              (C := C) (inputs := inputs) selectedRows
              (S2_agent_raw_orbit_selectedCarrier_successorTail_source_20260521k15
                (C := C) (inputs := inputs) selectedRows
                (S2_k6k_faceSucc_tail_faceSucc_rows_source_of_selectedActualCarrierFaceSuccAngleRows
                  (C := C) (inputs := inputs) selectedRows angleRows))
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_successorTailRows_20260521r13
              (C := C) (inputs := inputs)
              componentTopology geomHere
              (S2_q23_selectedNeighborIncidentGermFrontierEdgeMembershipRows_family_of_carrierCutFieldwise_selectedAngularNoBetweenRows_endpointLocalRadiusCovers
                carrierCutFieldwise angularRows endpointLocalRadiusCovers
                C inputs)
              (rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_eta
                successorTailRows)
          SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource
            selectedRawRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  exact
    S2_q24_actualExteriorSectorInputSourceRows_family_of_kComponentPointsBetween_vertexIncident_carrierCutFieldwise_selectedAngular_incidentGerm_selectedCarrierRows_cyclicSuccCutPartitions
      points_between frontier_vertex_incident carrierCutFieldwise angularRows
      (S2_q23_selectedNeighborIncidentGermFrontierEdgeMembershipRows_family_of_carrierCutFieldwise_selectedAngularNoBetweenRows_endpointLocalRadiusCovers
        carrierCutFieldwise angularRows endpointLocalRadiusCovers)
      selectedCarrierRows cyclicSuccCutPartitions

set_option linter.style.longLine false in
/-- q27 actual-sector source through the q25 face-dart producer.

This removes the selected-carrier successor and incident-germ rows from the
live source surface: the selected carrier is rebuilt from e32/r36, the
selected incident-germ row from endpoint-local-radius covers, and the selected
actual `faceSucc` angle row from orientation plus local strict order.  The
remaining repeated-tail source is the deleted-tail nonreachability row on the
same selected raw orbit. -/
noncomputable def
    S2_q27_actualExteriorSectorInputSourceRows_family_of_componentTopology_carrierCutFieldwise_selectedAngular_endpointLocalRadius_orientation_localStrict_cyclicSuccDeletedTailNonreachability
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (carrierCutFieldwise :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
            (C := C) (inputs := inputs)
            (S2_q21_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive_of_carrierCutFieldwise
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
            (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
            (angularRows C inputs)
        let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
          S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        let localEndpointRows :
            IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
          S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) selectedRows
        IncidentGermEndpointLocalRadiusCoversRows
          (C := C) (inputs := inputs) (selectedRows := selectedRows)
          localEndpointRows)
    (orientationRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geomHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geomHere
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
            inputs selectedRows)
    (localStrictOrder :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geomHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geomHere
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (cyclicSuccDeletedTail :
      let angleRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geomHere :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
                  (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
                  (angularRows C inputs)
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geomHere
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
                inputs selectedRows :=
        fun {m} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C) =>
          (S2_q24_selected_carrier_successor_and_angle_sources_of_geometricSelection_orientationRows_localStrictOrder
            (C := C) (inputs := inputs)
            (S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs))
            (orientationRows C inputs) (localStrictOrder C inputs)).2
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geomHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geomHere
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) geomHere
              (angleRows C inputs)
          let incidentHere :
              SelectedNeighborIncidentGermFrontierEdgeMembershipRows
                (C := C) (inputs := inputs) geomHere :=
            S2_q23_selectedNeighborIncidentGermFrontierEdgeMembershipRows_of_carrierCutFieldwise_selectedAngularNoBetweenRows_endpointLocalRadiusCovers
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs) (endpointLocalRadiusCovers C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) geomHere
              incidentHere
              strictSuccessorOrder
          SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
            selectedRawRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
    S2_q23_geometricSelectionInputSource_family_of_carrierCutFieldwise_selectedAngularNoBetweenRows
      carrierCutFieldwise angularRows
  let incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs)
            (S2_q23_geometricSelectionInputSource_of_carrierCutFieldwise_selectedAngularNoBetweenRows
              (C := C) (inputs := inputs) (carrierCutFieldwise C inputs)
              (angularRows C inputs)) :=
    S2_q23_selectedNeighborIncidentGermFrontierEdgeMembershipRows_family_of_carrierCutFieldwise_selectedAngularNoBetweenRows_endpointLocalRadiusCovers
      carrierCutFieldwise angularRows endpointLocalRadiusCovers
  let angleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection (C := C) inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows :=
    S2_q30_selectedActualCarrierFaceSuccAngleRows_family_of_carrierCutFieldwise_selectedAngular_orientation_localStrictOrder
      carrierCutFieldwise angularRows orientationRows localStrictOrder
  intro m C inputs
  exact
    actualExteriorSectorInputSourceRows_of_faceDartOrbitExteriorCarrierRows
      (C := C) (inputs := inputs)
      (S2_q25_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability
        componentTopology geometricSelection incidentGermFrontierEdgeRows
        angleRows cyclicSuccDeletedTail
        C inputs).1
      (S2_q25_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability
        componentTopology geometricSelection incidentGermFrontierEdgeRows
        angleRows cyclicSuccDeletedTail
        C inputs).2

set_option linter.style.longLine false in
/-- Pointwise cycle-row handoff from the reduced topology surface and the
sharp e32 fieldwise carrier cut source. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_carrierCutFieldwise_20260521i5
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs) :
    UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
    (C := C) inputs frontier_preconnected
    ((actualCarrierDegreeTwo_iff_carrierCutFieldwise
      (C := C) inputs).2 source)

set_option linter.style.longLine false in
/-- Cycle-row handoff from the reduced topology surface and the sharp e32
fieldwise carrier cut source.

This keeps the live local source below actual carrier degree two: the
fieldwise source names two actual selected `unboundedFrontierEdgeSet`
incidences at each carrier vertex and asks a third actual carrier neighbour
for a concrete cut partition. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_carrierCutFieldwise_20260521i5
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
    frontier_preconnected
    (actualCarrierDegreeTwo_family_of_carrierCutFieldwise source)

set_option linter.style.longLine false in
/-- Finite planar outer-component theorem handoff from preconnected topology
and the sharp e32 fieldwise carrier cut source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_planarContinuumPreconnected_carrierCutFieldwise_20260521i5
    (frontier_preconnected :
      PlanarContinuumUnboundedComplementFrontierPreconnected)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_carrierCutFieldwise_20260521i5
      frontier_preconnected source)

set_option linter.style.longLine false in
/-- Cycle-row handoff from the lower closed-split topology source and the
sharp e32 fieldwise carrier cut source. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_closedSeparationForcesContinuumSeparation_carrierCutFieldwise_20260521i5
    (closed_split_forces_continuum_split :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_carrierCutFieldwise_20260521i5
    (planarContinuumUnboundedComplementFrontierPreconnected_of_closedSeparationForcesContinuumSeparation
      closed_split_forces_continuum_split)
    source

set_option linter.style.longLine false in
/-- Finite planar outer-component theorem handoff from the lower closed-split
topology source and the sharp e32 fieldwise carrier cut source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_closedSeparationForcesContinuumSeparation_carrierCutFieldwise_20260521i5
    (closed_split_forces_continuum_split :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_closedSeparationForcesContinuumSeparation_carrierCutFieldwise_20260521i5
      closed_split_forces_continuum_split source)

set_option linter.style.longLine false in
/-- Cycle-row handoff from the current same-`K` Janiszewski topology leaf and
the sharp e32 fieldwise actual-carrier cut source.

This is only a route compression: the topology source remains the same-`K`
boundary-bumping point theorem, and the local source remains the actual
selected-carrier e32 fieldwise cut package. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_janiszewskiKComponentPointsBetween_carrierCutFieldwise_20260521j9
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsFamily_of_closedSeparationForcesContinuumSeparation_carrierCutFieldwise_20260521i5
    (planarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation_of_janiszewskiKComponentPointsBetween
      points_between)
    source

set_option linter.style.longLine false in
/-- Finite planar outer-component handoff from the current same-`K`
Janiszewski topology leaf and the sharp e32 fieldwise actual-carrier cut
source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_janiszewskiKComponentPointsBetween_carrierCutFieldwise_20260521j9
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_janiszewskiKComponentPointsBetween_carrierCutFieldwise_20260521j9
      points_between source)

set_option linter.style.longLine false in
/-- Cycle-row handoff from the continuous-`Bool` side topology source and the
sharp e32 fieldwise actual-carrier cut source.

The continuous-side source is the current topology leaf below the same-`K`
point-between packaging.  The local source remains the actual selected-carrier
e32 fieldwise cut package. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_continuousKSide_carrierCutFieldwise_20260521j10
    (continuous_side :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsFamily_of_janiszewskiKComponentPointsBetween_carrierCutFieldwise_20260521j9
    (planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_frontierComponent
      (planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_continuousKSide
        continuous_side))
    source

set_option linter.style.longLine false in
/-- Finite planar outer-component handoff from the continuous-`Bool` side
topology source and the sharp e32 fieldwise actual-carrier cut source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_continuousKSide_carrierCutFieldwise_20260521j10
    (continuous_side :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_continuousKSide_carrierCutFieldwise_20260521j10
      continuous_side source)

set_option linter.style.longLine false in
/-- Cycle-row handoff from the point-level crossing-subcontinuum topology
source and the sharp e32 fieldwise actual-carrier cut source.

This is the same local source as the j10 route, but with the topology source
lowered through the checked continuous-side constructor. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_crossingSubcontinuumPointsBetween_carrierCutFieldwise_20260521j11
    (points_between :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsFamily_of_continuousKSide_carrierCutFieldwise_20260521j10
    (planarContinuumUnboundedComplementFrontierContinuousKSide_of_pointsBetween_closedSplit
      points_between)
    source

set_option linter.style.longLine false in
/-- Finite planar outer-component handoff from the point-level
crossing-subcontinuum topology source and the sharp e32 fieldwise
actual-carrier cut source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_crossingSubcontinuumPointsBetween_carrierCutFieldwise_20260521j11
    (points_between :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_crossingSubcontinuumPointsBetween_carrierCutFieldwise_20260521j11
      points_between source)

set_option linter.style.longLine false in
/-- Cycle-row handoff from the U-indexed pair frontier-component topology
source and the sharp e32 fieldwise actual-carrier cut source.

This is the same local source as the j11 route, with the topology source
lowered through the checked point-between constructor in `S2TopologySource`. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_uPairFrontierComponent_carrierCutFieldwise_20260521j14
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsFamily_of_crossingSubcontinuumPointsBetween_carrierCutFieldwise_20260521j11
    (S2_agent_topology_points_between_source_20260521f5 pair_component)
    source

set_option linter.style.longLine false in
/-- Finite planar outer-component handoff from the U-indexed pair
frontier-component topology source and the sharp e32 fieldwise actual-carrier
cut source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_uPairFrontierComponent_carrierCutFieldwise_20260521j14
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_uPairFrontierComponent_carrierCutFieldwise_20260521j14
      pair_component source)

set_option linter.style.longLine false in
/-- Cycle-row handoff from the U-indexed Janiszewski subcontinuum boundedness
source and the sharp e32 fieldwise actual-carrier cut source.

This is the j14 route with the topology source lowered through the checked
U-pair frontier-component constructor. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_subcontinuumForcesBounded_carrierCutFieldwise_20260521j15
    (subcontinuum_forces_bounded :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  unboundedExteriorFrontierCycleRowsFamily_of_uPairFrontierComponent_carrierCutFieldwise_20260521j14
    (S2_agent_U_pair_frontier_component_source_20260521f7
      subcontinuum_forces_bounded)
    (fun {m} C inputs => source (m := m) C inputs)

set_option linter.style.longLine false in
/-- Finite planar outer-component handoff from the U-indexed Janiszewski
subcontinuum boundedness source and the sharp e32 fieldwise actual-carrier cut
source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_subcontinuumForcesBounded_carrierCutFieldwise_20260521j15
    (subcontinuum_forces_bounded :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_subcontinuumForcesBounded_carrierCutFieldwise_20260521j15
      subcontinuum_forces_bounded source)

set_option linter.style.longLine false in
/-- Cycle-row handoff from the generic pairwise subcontinuum-between topology
source and the sharp e32 fieldwise actual-carrier cut source.

This keeps the local source on the actual selected carrier graph, but lowers
the topology side below the U-indexed Janiszewski boundedness alias to the
standard compact-connected planar frontier subcontinuum theorem. -/
noncomputable def
    unboundedExteriorFrontierCycleRowsFamily_of_subcontinuumBetween_carrierCutFieldwise_20260521k1
    (subcontinuum_between :
      PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs := by
  intro m C inputs
  exact
    unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_actualCarrierDegreeTwo
      (C := C) inputs
      (finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_frontierPreconnected
        (S2_codex_current_20260520_finite_frontier_preconnected_acyclic_source
          subcontinuum_between))
      ((actualCarrierDegreeTwo_iff_carrierCutFieldwise
        (C := C) inputs).2 (source C inputs))

set_option linter.style.longLine false in
/-- Finite planar outer-component handoff from the generic pairwise
subcontinuum-between topology source and the sharp e32 fieldwise actual-carrier
cut source. -/
noncomputable def
    finitePlanarStraightLineOuterComponentTheorem_of_subcontinuumBetween_carrierCutFieldwise_20260521k1
    (subcontinuum_between :
      PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween)
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRowsFamily_of_subcontinuumBetween_carrierCutFieldwise_20260521k1
      subcontinuum_between source)

/-- Family-level exact residual for the live local source.

The remaining source is precisely the e32 fieldwise cut package already
available in local code; it is stated only on actual
`unboundedFrontierEdgeSet` incidences and actual neighbours of
`unboundedFrontierCarrierGraph`. -/
theorem actualCarrierDegreeTwo_family_iff_carrierCutFieldwise :
    (forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs) <->
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) := by
  constructor
  · intro source m C inputs
    exact
      (actualCarrierDegreeTwo_iff_carrierCutFieldwise
        (C := C) inputs).1 (source C inputs)
  · intro source m C inputs
    exact
      (actualCarrierDegreeTwo_iff_carrierCutFieldwise
        (C := C) inputs).2 (source C inputs)

/-- Claim `S2-codex-local-carrier-source-20260521f1`.

Checked reduction of the input-only actual-carrier degree-two leaf to the
already available e32 fieldwise cut theorem.  This is intentionally just an
adapter: the unresolved mathematical source is the displayed fieldwise cut
package, with two actual selected frontier-edge heads and third-neighbour cut
partitions for the concrete carrier graph. -/
theorem S2_codex_local_carrier_source_20260521f1
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_family_of_carrierCutFieldwise source

/-- Claim `S2-agent-carrier-graph-degree-two-source-20260521f6`.

Checked strict reducer for the exact source requested by the local selected
incident-edge route.  The residual is the sharp cut-partition input: at each
actual unbounded-frontier carrier vertex, choose two genuine incident
`unboundedFrontierEdgeSet` heads and show that any third concrete carrier
neighbour yields a `CutVertexInterface.CutVertexPartition`. -/
theorem S2_agent_carrier_graph_degree_two_source_20260521f6_of_cutPartitionInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Nonempty
            (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
              C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
          unboundedFrontierCarrierGraph_decidableAdj C inputs
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
            2 := by
  intro m C inputs
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    S2_agent_carrier_degree_two_source_worker_20260521d1_neighborFinset_card_two
      (C := C) inputs (Classical.choice (source C inputs))

/-- Family-level exact residual for the f6 carrier graph degree-two source.

This records that the requested neighbour-finset-cardinality family is
equivalent to the existing sharp cut-partition source, with no induced
frontier graph, arbitrary cycle, all-adjacent endpoint row, selected-head
outgoing-list row, or final cycle rows in the reduction. -/
theorem S2_agent_carrier_graph_degree_two_source_20260521f6_family_iff_cutPartitionInputSource :
    (forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
          unboundedFrontierCarrierGraph_decidableAdj C inputs
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
            2) <->
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Nonempty
            (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
              C inputs)) := by
  constructor
  · intro hdegree m C inputs
    letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
      unboundedFrontierCarrierGraph_decidableAdj C inputs
    exact
      (actualCarrierDegreeTwo_iff_cutPartitionInputSource
        (C := C) inputs).1
        (by
          simpa [ActualCarrierDegreeTwoSource] using hdegree C inputs)
  · intro source
    exact
      S2_agent_carrier_graph_degree_two_source_20260521f6_of_cutPartitionInputSource
        source

/-- Claim `S2-agent-actual-carrier-degree-two-worker-20260521e43`.

Named e43 route: the actual-carrier degree-two leaf reduces to the sharp
cut-partition local source, staying on the concrete
`unboundedFrontierCarrierGraph` and actual `unboundedFrontierEdgeSet`
incidences. -/
theorem S2_agent_actual_carrier_degree_two_worker_20260521e43
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
        C inputs) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_cutPartitionInputSource
    (C := C) (inputs := inputs) source

/-- Boundary-free local no-third-germ rows give the deleted-neighbour source
through the exposed local-sector route. -/
noncomputable def
    unreachableAfterDeleteInputSource_of_boundaryFreeLocalNoThirdGermSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : BoundaryFreeLocalNoThirdGermSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  unboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource_of_localSectorRows
    (C := C) (inputs := inputs)
    (localSectorRows_of_boundaryFreeLocalNoThirdGermSourceRows
      (C := C) (inputs := inputs) source)

/-- Actual carrier degree two supplies the deleted-neighbour source.

The route is:
`ActualCarrierDegreeTwoSource` -> local-sector rows for the actual carrier ->
`UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource`.
-/
noncomputable def
    unreachableAfterDeleteInputSource_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    unboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource_of_localSectorRows
      (C := C) (inputs := inputs)
      (S2_agent_local_sector_source_worker_20260521e14_of_carrier_degree_two
        (C := C) inputs (by simpa [ActualCarrierDegreeTwoSource] using hdegree))

/-- Simple-degree form of
`unreachableAfterDeleteInputSource_of_actualCarrierDegreeTwo`. -/
noncomputable def
    unreachableAfterDeleteInputSource_of_actualCarrierSimpleDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (hdegree :
      letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
        unboundedFrontierCarrierGraph_decidableAdj C inputs
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        @SimpleGraph.degree _
          (unboundedFrontierCarrierGraph C inputs) a
          ((unboundedFrontierCarrierGraph C inputs).neighborSetFintype a) =
            2) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs := by
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  exact
    unreachableAfterDeleteInputSource_of_actualCarrierDegreeTwo
      (C := C) inputs
      (by
        intro a
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact hdegree a)

/-- The deleted-neighbour source is exactly reduced to actual carrier
two-regularity.

The forward direction reads the two selected heads from the deleted-neighbour
source and erases it to the checked carrier degree row.  The reverse direction
is the local-sector route above. -/
theorem nonempty_unreachableAfterDeleteInputSource_iff_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs) ↔
      ActualCarrierDegreeTwoSource inputs := by
  constructor
  · rintro ⟨source⟩
    exact
      actualCarrierDegreeTwo_of_unreachableAfterDeleteInputSource
        (C := C) (inputs := inputs) source
  · intro hdegree
    exact
      ⟨unreachableAfterDeleteInputSource_of_actualCarrierDegreeTwo
        (C := C) inputs hdegree⟩

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-no-cut-degree-two-k4`, cut-partition form.

The finite-plane no-cut field in `FinitePlanarOuterComponentInputs` is consumed
by the existing cut-partition eraser: if a third actual carrier neighbour
supplied a concrete `CutVertexInterface.CutVertexPartition`, `inputs.noCutVertex`
rules it out, so the two selected `unboundedFrontierEdgeSet` heads are exactly
the carrier neighbours. -/
theorem S2_dynamic_no_cut_degree_two_k4_of_cutPartitionInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
        C inputs) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_cutPartitionInputSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-no-cut-degree-two-k4`, ambient deleted-graph form.

This is the same no-cut degree-two reduction with the lower
unreachable-after-delete source exposed.  The existing API first converts each
deleted-graph disconnection into the sharp cut-partition contradiction and
then reads the exact two selected carrier neighbours. -/
theorem S2_dynamic_no_cut_degree_two_k4_of_unreachableAfterDeleteInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    ActualCarrierDegreeTwoSource inputs :=
  actualCarrierDegreeTwo_of_unreachableAfterDeleteInputSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- The same k4 reduction in selected-neighbour row form.

After no-cut eliminates third carrier neighbours through the cut/unreachable
API, the two actual selected `unboundedFrontierEdgeSet` incidences can be
exported as `LocalSelectedIncidentEdgePairSourceRows`. -/
noncomputable def
    S2_dynamic_no_cut_selectedIncidentRows_k4_of_unreachableAfterDeleteInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  localSelectedIncidentEdgePairSourceRows_of_actualCarrierDegreeTwo
    (C := C) inputs
    (S2_dynamic_no_cut_degree_two_k4_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Claim `S2-q44-carrier-degree-two-source-worker`, selected incident-edge form.

The local selected incident-edge source is lowered to the same ambient
deleted-neighbour source used for actual carrier degree two.  This exposes the
input-facing local row without introducing an induced frontier graph,
arbitrary carrier cycle, all-adjacent endpoint row, actual-sector premise, or
identity angular-order shortcut. -/
noncomputable def
    S2_q44_localSelectedIncidentEdgePairSourceRows_of_unreachableAfterDeleteInputSource
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    LocalSelectedIncidentEdgePairSourceRows inputs :=
  S2_dynamic_no_cut_selectedIncidentRows_k4_of_unreachableAfterDeleteInputSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Family form of
`S2_q44_localSelectedIncidentEdgePairSourceRows_of_unreachableAfterDeleteInputSource`. -/
noncomputable def
    S2_q44_localSelectedIncidentEdgePairSourceRows_family_of_unreachableAfterDeleteInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        LocalSelectedIncidentEdgePairSourceRows inputs := by
  intro m C inputs
  exact
    S2_q44_localSelectedIncidentEdgePairSourceRows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- q53 direct geometric-selection source from actual carrier degree two.

The degree-two source supplies only the actual selected local-sector heads.
The remaining premise is the same-head geometric row for those chosen heads;
no boundary cycle, actual exterior-sector package, W32 facade, or outgoing-list
shortcut is used. -/
noncomputable def
    S2_q53_geometricSelectionInputSource_of_actualCarrierDegreeTwo_geometricRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (degreeRows : ActualCarrierDegreeTwoSource inputs)
    (geometricRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_actualCarrierDegreeTwo
          (C := C) inputs degreeRows
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right)) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_actualCarrierDegreeTwo
      (C := C) inputs degreeRows
  exact
    S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
      (C := C) (inputs := inputs) localSectorRows
      (by
        simpa [localSectorRows] using geometricRows)

set_option linter.style.longLine false in
/-- Family form of the q53 actual-degree-two geometric-selection lowering. -/
noncomputable def
    S2_q53_geometricSelectionInputSource_family_of_actualCarrierDegreeTwo_geometricRows
    (degreeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_q53_geometricSelectionInputSource_of_actualCarrierDegreeTwo_geometricRows
      (C := C) (inputs := inputs) (degreeRows C inputs)
      (geometricRows C inputs)

set_option linter.style.longLine false in
/-- q53 direct boundary-free local angular source from actual carrier degree
two, same-head geometric rows, and point-third-germ angular containment.

This is the source-level local-angular analogue of
`S2_q53_geometricSelectionInputSource_of_actualCarrierDegreeTwo_geometricRows`:
actual carrier degree two chooses the local heads, while the geometric and
point-third-germ rows remain explicit local premises for exactly those heads. -/
noncomputable def
    S2_q53_boundaryFreeLocalSectorGeometricAngularSource_of_actualCarrierDegreeTwo_geometricRows_pointThirdGerm
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (degreeRows : ActualCarrierDegreeTwoSource inputs)
    (geometricRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_actualCarrierDegreeTwo
          (C := C) inputs degreeRows
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right))
    (pointThirdGermRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_actualCarrierDegreeTwo
          (C := C) inputs degreeRows
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ (localSectorRows a).left ->
                    x ≠ (localSectorRows a).right ->
                      BoundaryFreeGraphVertexPointAngularBetween C a.1
                        (localSectorRows a).left (localSectorRows a).right
                        q) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_actualCarrierDegreeTwo
      (C := C) inputs degreeRows
  exact
    S2_r56_boundaryFreeLocalSectorGeometricAngularSource_of_localSectorRows_geometricRows_pointThirdGerm
      (C := C) (inputs := inputs) localSectorRows
      (by
        simpa [localSectorRows] using geometricRows)
      (by
        simpa [localSectorRows] using pointThirdGermRows)

set_option linter.style.longLine false in
/-- Family form of the q53 actual-degree-two boundary-free local-angular
lowering. -/
noncomputable def
    S2_q53_boundaryFreeLocalSectorGeometricAngularSource_family_of_actualCarrierDegreeTwo_geometricRows_pointThirdGerm
    (degreeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right))
    (pointThirdGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          forall (a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin m),
            q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
              q ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj a.1 x ->
                  q ∈ vertexIncidentGermW3 C a.1 x ε ->
                    q ≠ (canonicalGraph C).point a.1 ->
                      x ≠ (localSectorRows a).left ->
                        x ≠ (localSectorRows a).right ->
                          BoundaryFreeGraphVertexPointAngularBetween C a.1
                            (localSectorRows a).left
                            (localSectorRows a).right q) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro m C inputs
  exact
    S2_q53_boundaryFreeLocalSectorGeometricAngularSource_of_actualCarrierDegreeTwo_geometricRows_pointThirdGerm
      (C := C) (inputs := inputs) (degreeRows C inputs)
      (geometricRows C inputs) (pointThirdGermRows C inputs)

set_option linter.style.longLine false in
/-- q45 head-match row tying the selected heads obtained from
unreachable-after-delete to one actual exterior boundary sector.

The selected heads remain the actual local carrier heads produced from the
ambient deleted-neighbour source; this row only records that, pointwise, they
are the predecessor and successor bounding the same concrete exterior sector. -/
abbrev
    S2_q45_unreachableAfterDeleteSelectedHeadsMatchBoundaryExteriorSector
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C) : Prop :=
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    S2_r56_localSectorRows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) source
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    Exists fun k : Fin B.length =>
      B.vertex k = a.1 ∧
        (localSectorRows a).left =
          B.vertex (PlanarInterface.cyclicPred B.length_pos k) ∧
        (localSectorRows a).right =
          B.vertex (PlanarInterface.cyclicSucc B.length_pos k)

set_option linter.style.longLine false in
/-- q45 selected angular rows from actual exterior-sector orientation.

This lowers the angular/geometric-selection side for the q44 composer to the
unreachable-after-delete carrier heads plus an explicit same-boundary exterior
sector orientation row; no global all-outgoing no-between row is used. -/
theorem
    S2_q45_selectedAngularNoBetweenRows_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k)
    (headRows :
      S2_q45_unreachableAfterDeleteSelectedHeadsMatchBoundaryExteriorSector
        (C := C) (inputs := inputs) source B) :
    S2_q18_selectedExteriorSectorAngularNoBetweenRows
      (C := C) (inputs := inputs)
      (S2_r56_localSectorRows_of_unreachableAfterDeleteInputSource
        (C := C) (inputs := inputs) source) := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    S2_r56_localSectorRows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) source
  change S2_q18_selectedExteriorSectorAngularNoBetweenRows
    (C := C) (inputs := inputs) localSectorRows
  intro a
  rcases headRows a with ⟨k, hcenter, hleft, hright⟩
  let boundaryRows :
      GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows C B k :=
    BoundaryVertexExteriorSectorRowsAt.toBoundaryVertexAngularNoBetweenRows
      (sectorRows k)
  refine
    { angle := by
        simpa [localSectorRows, hcenter, hleft, hright] using
          boundaryRows.angle
      no_between := ?_ }
  intro other hAdj hother_left hother_right hbetween
  have hother_pred :
      other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) := by
    intro hother
    exact hother_left (hother.trans hleft.symm)
  have hother_succ :
      other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) := by
    intro hother
    exact hother_right (hother.trans hright.symm)
  exact
    boundaryRows.no_between other
      (by simpa [hcenter] using hAdj)
      hother_pred
      hother_succ
      (by
        have hleft_between := hbetween.1
        have hright_between := hbetween.2
        rw [hleft] at hleft_between
        rw [hright] at hright_between
        exact
          ⟨by
              simpa [GeometricRotationSystem.BoundaryPredSuccAngularBetween,
                GeometricRotationSystem.GraphVertexAngularBetween,
                hcenter] using hleft_between,
            by
              simpa [GeometricRotationSystem.BoundaryPredSuccAngularBetween,
                GeometricRotationSystem.GraphVertexAngularBetween,
                hcenter] using hright_between⟩)

set_option linter.style.longLine false in
/-- q45 geometric-selection source for the q44 composer from
unreachable-after-delete heads and actual exterior-sector orientation. -/
noncomputable def
    S2_q45_geometricSelectionInputSource_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k)
    (headRows :
      S2_q45_unreachableAfterDeleteSelectedHeadsMatchBoundaryExteriorSector
        (C := C) (inputs := inputs) source B) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    S2_r56_localSectorRows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) source
  exact
    S2_q18_geometricSelectionInputSource_of_localSectorRows_angularNoBetweenRows
      (C := C) (inputs := inputs) localSectorRows
      (by
        simpa [localSectorRows] using
          S2_q45_selectedAngularNoBetweenRows_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
            (C := C) (inputs := inputs) source B sectorRows headRows)

set_option linter.style.longLine false in
/-- Family form of the q45 geometric-selection lowering from
unreachable-after-delete and same-boundary exterior-sector rows. -/
noncomputable def
    S2_q45_geometricSelectionInputSource_family_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs)
    (boundary :
      forall {m : Nat} (C : _root_.UDConfig m)
        (_inputs : FinitePlanarOuterComponentInputs C),
          JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (sectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall k : Fin (boundary C inputs).length,
            BoundaryVertexExteriorSectorRowsAt inputs (boundary C inputs) k)
    (headRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q45_unreachableAfterDeleteSelectedHeadsMatchBoundaryExteriorSector
            (C := C) (inputs := inputs) (source C inputs)
            (boundary C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_q45_geometricSelectionInputSource_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
      (C := C) (inputs := inputs) (source C inputs)
      (boundary C inputs) (sectorRows C inputs) (headRows C inputs)

set_option linter.style.longLine false in
/-- q45 boundary-free local-angular source from the same
unreachable-after-delete carrier heads and actual exterior-sector orientation.

The third-germ angular row is stated on the same concrete boundary sector and
then transported through the selected-head match; the geometric row is read
from the primitive exterior-sector angular order. -/
noncomputable def
    S2_q45_boundaryFreeLocalSectorGeometricAngularSource_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (sectorRows :
      forall k : Fin B.length,
        BoundaryVertexExteriorSectorRowsAt inputs B k)
    (headRows :
      S2_q45_unreachableAfterDeleteSelectedHeadsMatchBoundaryExteriorSector
        (C := C) (inputs := inputs) source B)
    (third_germ_between :
      forall (k : Fin B.length) (ε : Real) (q : PlanarInterface.Point)
          (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point (B.vertex k)) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj (B.vertex k) x ->
              q ∈ vertexIncidentGermW3 C (B.vertex k) x ε ->
                q ≠ (canonicalGraph C).point (B.vertex k) ->
                  x ≠
                      B.vertex
                        (PlanarInterface.cyclicPred B.length_pos k) ->
                    x ≠
                        B.vertex
                          (PlanarInterface.cyclicSucc B.length_pos k) ->
                      GeometricRotationSystem.BoundaryPredSuccAngularBetween
                        C B k x) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    S2_r56_localSectorRows_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) source
  have angularRows :
      S2_q18_selectedExteriorSectorAngularNoBetweenRows
        (C := C) (inputs := inputs) localSectorRows := by
    simpa [localSectorRows] using
      S2_q45_selectedAngularNoBetweenRows_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
        (C := C) (inputs := inputs) source B sectorRows headRows
  have geometricRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right) :=
    S2_q18_selectedExteriorSectorGeometricRows_of_angularNoBetweenRows
      (C := C) (inputs := inputs) localSectorRows angularRows
  have pointThirdGermRows :
      forall (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs})
          (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
        q ∈ Metric.ball ((canonicalGraph C).point a.1) ε ->
          q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
            (canonicalGraph C).Adj a.1 x ->
              q ∈ vertexIncidentGermW3 C a.1 x ε ->
                q ≠ (canonicalGraph C).point a.1 ->
                  x ≠ (localSectorRows a).left ->
                    x ≠ (localSectorRows a).right ->
                      BoundaryFreeGraphVertexPointAngularBetween C a.1
                        (localSectorRows a).left (localSectorRows a).right
                        q := by
    intro a ε q x hqball hqfrontier hadj hgerm hqcenter hx_left hx_right
    rcases headRows a with ⟨k, hcenter, hleft, hright⟩
    have hx_pred :
        x ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) := by
      intro hx
      exact hx_left (hx.trans hleft.symm)
    have hx_succ :
        x ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) := by
      intro hx
      exact hx_right (hx.trans hright.symm)
    have hbetween :
        GeometricRotationSystem.BoundaryPredSuccAngularBetween C B k x :=
      third_germ_between k ε q x
        (by simpa [hcenter] using hqball)
        hqfrontier
        (by simpa [hcenter] using hadj)
        (by simpa [hcenter] using hgerm)
        (by simpa [hcenter] using hqcenter)
        hx_pred
        hx_succ
    have hpoint : BoundaryPredSuccPointAngularBetween C B k q :=
      boundary_frontier_third_germ_point_between_of_graphDart_between
        (C := C) (B := B) (k := k) (eps := ε) (q := q) (other := x)
        hbetween
        (by simpa [hcenter] using hgerm)
        (by simpa [hcenter] using hqcenter)
    have hpoint_left := hpoint.1
    have hpoint_right := hpoint.2
    rw [← hleft] at hpoint_left
    rw [← hright] at hpoint_right
    exact
      ⟨by
          simpa [BoundaryFreeGraphVertexPointAngularBetween,
            BoundaryPredSuccPointAngularBetween, hcenter] using hpoint_left,
        by
          simpa [BoundaryFreeGraphVertexPointAngularBetween,
            BoundaryPredSuccPointAngularBetween, hcenter] using hpoint_right⟩
  exact
    S2_r56_boundaryFreeLocalSectorGeometricAngularSource_of_localSectorRows_geometricRows_pointThirdGerm
      (C := C) (inputs := inputs) localSectorRows geometricRows
      pointThirdGermRows

set_option linter.style.longLine false in
/-- Family form of the q45 boundary-free local-angular lowering from
unreachable-after-delete and same-boundary exterior-sector rows. -/
noncomputable def
    S2_q45_boundaryFreeLocalSectorGeometricAngularSource_family_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs)
    (boundary :
      forall {m : Nat} (C : _root_.UDConfig m)
        (_inputs : FinitePlanarOuterComponentInputs C),
          JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (sectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall k : Fin (boundary C inputs).length,
            BoundaryVertexExteriorSectorRowsAt inputs (boundary C inputs) k)
    (headRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q45_unreachableAfterDeleteSelectedHeadsMatchBoundaryExteriorSector
            (C := C) (inputs := inputs) (source C inputs)
            (boundary C inputs))
    (third_germ_between :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall (k : Fin (boundary C inputs).length) (ε : Real)
            (q : PlanarInterface.Point) (x : Fin m),
            q ∈
                Metric.ball
                  ((canonicalGraph C).point ((boundary C inputs).vertex k))
                  ε ->
              q ∈
                  frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (canonicalGraph C).Adj ((boundary C inputs).vertex k) x ->
                  q ∈
                      vertexIncidentGermW3 C
                        ((boundary C inputs).vertex k) x ε ->
                    q ≠
                        (canonicalGraph C).point
                          ((boundary C inputs).vertex k) ->
                      x ≠
                          (boundary C inputs).vertex
                            (PlanarInterface.cyclicPred
                              (boundary C inputs).length_pos k) ->
                        x ≠
                            (boundary C inputs).vertex
                              (PlanarInterface.cyclicSucc
                                (boundary C inputs).length_pos k) ->
                          GeometricRotationSystem.BoundaryPredSuccAngularBetween
                            C (boundary C inputs) k x) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro m C inputs
  exact
    S2_q45_boundaryFreeLocalSectorGeometricAngularSource_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
      (C := C) (inputs := inputs) (source C inputs)
      (boundary C inputs) (sectorRows C inputs) (headRows C inputs)
      (third_germ_between C inputs)

set_option linter.style.longLine false in
/-- q45 orientation leaf for the q44 composer lowered to the selected-carrier
successor row on the same geometric-selection heads. -/
theorem
    S2_q45_orientationRows_of_geometricSelection_selectedCarrierRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (selectedCarrierRows :
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)) :
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
      inputs selectedRows :=
  S2_agent_q7_selected_actual_carrier_orientation_source_of_geometricSelection_selectedCarrierRows_20260522q7
    (C := C) (inputs := inputs) geometricSelection selectedCarrierRows

set_option linter.style.longLine false in
/-- q45 local strict-turn leaf for the q44 composer lowered to the same
selected-carrier successor row. -/
theorem
    S2_q45_localStrictOrder_of_geometricSelection_selectedCarrierRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (selectedCarrierRows :
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)) :
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
      inputs
      (selectedNeighborGeometricCarrierLeft
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource)
      (selectedNeighborGeometricCarrierRight
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) :=
  S2_agent_q7_localStrictOrder_source_of_geometricSelection_selectedCarrierRows_20260522q7
    (C := C) (inputs := inputs) geometricSelection selectedCarrierRows

set_option linter.style.longLine false in
/-- Family form of the q45 orientation leaf lowering. -/
theorem
    S2_q45_orientationRows_family_of_geometricSelection_selectedCarrierRows
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) (geometricSelection C inputs)
        RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
          inputs selectedRows := by
  intro m C inputs
  exact
    S2_q45_orientationRows_of_geometricSelection_selectedCarrierRows
      (C := C) (inputs := inputs) (geometricSelection C inputs)
      (selectedCarrierRows C inputs)

set_option linter.style.longLine false in
/-- Family form of the q45 local strict-turn leaf lowering. -/
theorem
    S2_q45_localStrictOrder_family_of_geometricSelection_selectedCarrierRows
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) (geometricSelection C inputs)
        RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
          (inputs := inputs)
          (left := selectedNeighborGeometricCarrierLeft
            (C := C) (inputs := inputs)
            selectedRows.toGeometricSelectionInputSource)
          (right := selectedNeighborGeometricCarrierRight
            (C := C) (inputs := inputs)
            selectedRows.toGeometricSelectionInputSource) := by
  intro m C inputs
  exact
    S2_q45_localStrictOrder_of_geometricSelection_selectedCarrierRows
      (C := C) (inputs := inputs) (geometricSelection C inputs)
      (selectedCarrierRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q46-local-geometric-source`.

Honest local geometric source rows for the q44/q45 actual-sector composer.
The selected heads are the actual `unboundedFrontierEdgeSet` heads stored in
the selected-edge local-isolation row.  The remaining non-local adapters are
kept explicit: the raw-orbit selected-carrier successor row and the selected
endpoint row needed to erase into the older all-radius local-angular consumer.
No global all-outgoing no-between source is part of this package. -/
structure S2_q46_localGeometricSourceRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  localIsolation :
    SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs
  geometricRows :
    let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) localIsolation
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (localSectorRows a).left (localSectorRows a).right)
  endpointRows :
    let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) localIsolation
    IncidentGermEndpointSelectedHeadRows
      (localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
        (C := C) (inputs := inputs) localSectorRows)
  selectedCarrierRows :
    let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) localIsolation
    let geometricSelection :
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs :=
      S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
        (C := C) (inputs := inputs) localSectorRows geometricRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
      inputs
      (selectedNeighborGeometricCarrierLeft
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource)
      (selectedNeighborGeometricCarrierRight
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource)

set_option linter.style.longLine false in
/-- q46 local-sector rows projected from the local geometric source. -/
noncomputable def S2_q46_localSectorRows_of_localGeometricSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : S2_q46_localGeometricSourceRows inputs) :
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
  localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
    (C := C) (inputs := inputs) source.localIsolation

set_option linter.style.longLine false in
/-- q46 lowers the q44/q45 geometric-selection premise to selected-edge local
isolation plus same-head geometric rows. -/
noncomputable def
    S2_q46_geometricSelectionInputSource_of_localGeometricSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : S2_q46_localGeometricSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
      C inputs := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    S2_q46_localSectorRows_of_localGeometricSourceRows
      (C := C) (inputs := inputs) source
  exact
    S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
      (C := C) (inputs := inputs) localSectorRows
      (by
        simpa [localSectorRows,
          S2_q46_localSectorRows_of_localGeometricSourceRows] using
          source.geometricRows)

set_option linter.style.longLine false in
/-- q46 lowers the q44/q45 selected actual-carrier orientation premise to the
same selected-carrier successor row carried by the local geometric source. -/
theorem S2_q46_orientationRows_of_localGeometricSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : S2_q46_localGeometricSourceRows inputs) :
    let geometricSelection :
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs :=
      S2_q46_geometricSelectionInputSource_of_localGeometricSourceRows
        (C := C) (inputs := inputs) source
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
      inputs selectedRows := by
  let geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2_q46_geometricSelectionInputSource_of_localGeometricSourceRows
      (C := C) (inputs := inputs) source
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs :=
    selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) geometricSelection
  have carrierRows :
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource) := by
    intro e p start edgeRows htail hhead m current_frontier hsucc_tail
    simpa [selectedRows, geometricSelection,
      S2_q46_geometricSelectionInputSource_of_localGeometricSourceRows,
      S2_q46_localSectorRows_of_localGeometricSourceRows] using
      (S2_q46_localGeometricSourceRows.selectedCarrierRows
        (C := C) (inputs := inputs) source
        (e := e) (p := p) (start := start)
        edgeRows htail hhead m current_frontier hsucc_tail)
  change
    RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
      inputs selectedRows
  intro e p start edgeRows htail hhead m current_frontier hsucc_tail
  rcases carrierRows edgeRows htail hhead m current_frontier hsucc_tail with
    ⟨hleft, hright, _leftRow, _rightRow⟩
  exact ⟨hleft, hright⟩

set_option linter.style.longLine false in
/-- q46 lowers the q44/q45 local strict-order premise to the same
selected-carrier successor row carried by the local geometric source. -/
theorem S2_q46_localStrictOrder_of_localGeometricSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : S2_q46_localGeometricSourceRows inputs) :
    let geometricSelection :
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs :=
      S2_q46_geometricSelectionInputSource_of_localGeometricSourceRows
        (C := C) (inputs := inputs) source
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
      inputs
      (selectedNeighborGeometricCarrierLeft
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource)
      (selectedNeighborGeometricCarrierRight
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource) := by
  let geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2_q46_geometricSelectionInputSource_of_localGeometricSourceRows
      (C := C) (inputs := inputs) source
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs :=
    selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) geometricSelection
  have carrierRows :
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource) := by
    intro e p start edgeRows htail hhead m current_frontier hsucc_tail
    simpa [selectedRows, geometricSelection,
      S2_q46_geometricSelectionInputSource_of_localGeometricSourceRows,
      S2_q46_localSectorRows_of_localGeometricSourceRows] using
      (S2_q46_localGeometricSourceRows.selectedCarrierRows
        (C := C) (inputs := inputs) source
        (e := e) (p := p) (start := start)
        edgeRows htail hhead m current_frontier hsucc_tail)
  change
    RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
      inputs
      (selectedNeighborGeometricCarrierLeft
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource)
      (selectedNeighborGeometricCarrierRight
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource)
  intro e p start edgeRows htail hhead m current_frontier hsucc_tail
  exact
    (rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_successorTailGeometricRows
      (C := C) (inputs := inputs)
      (S2_k6h_successor_tail_source_of_selectedCarrierRows
        (C := C) (inputs := inputs) selectedRows carrierRows))
      edgeRows htail hhead m current_frontier hsucc_tail

set_option linter.style.longLine false in
/-- q46 lowers the q44/q45 boundary-free local-angular premise to selected-edge
local isolation, same-head geometric rows, and selected-head endpoint rows. -/
noncomputable def
    S2_q46_boundaryFreeLocalSectorGeometricAngularSource_of_localGeometricSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : S2_q46_localGeometricSourceRows inputs) :
    BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    S2_q46_localSectorRows_of_localGeometricSourceRows
      (C := C) (inputs := inputs) source
  have geometricRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right) := by
    simpa [localSectorRows,
      S2_q46_localSectorRows_of_localGeometricSourceRows] using
      source.geometricRows
  have endpointRows :
      IncidentGermEndpointSelectedHeadRows
        (localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
          (C := C) (inputs := inputs) localSectorRows) := by
    simpa [localSectorRows,
      S2_q46_localSectorRows_of_localGeometricSourceRows] using
      source.endpointRows
  have pointRows :
      S2R21PointThirdGermGeometricSourceRows
        (C := C) (inputs := inputs) localSectorRows :=
    S2_r21_pointThirdGermGeometricSourceRows_of_localSectorRows_geometricRows_endpointSelectedHeadRows
      (C := C) (inputs := inputs) localSectorRows geometricRows endpointRows
  exact
    S2_r56_boundaryFreeLocalSectorGeometricAngularSource_of_localSectorRows_geometricRows_pointThirdGerm
      (C := C) (inputs := inputs) localSectorRows geometricRows pointRows.2

set_option linter.style.longLine false in
/-- Family form of the q46 geometric-selection lowering. -/
noncomputable def
    S2_q46_geometricSelectionInputSource_family_of_localGeometricSourceRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q46_localGeometricSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_q46_geometricSelectionInputSource_of_localGeometricSourceRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of the q46 orientation lowering. -/
theorem S2_q46_orientationRows_family_of_localGeometricSourceRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q46_localGeometricSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q46_geometricSelectionInputSource_of_localGeometricSourceRows
            (C := C) (inputs := inputs) (source C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
          inputs selectedRows := by
  intro m C inputs
  exact
    S2_q46_orientationRows_of_localGeometricSourceRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of the q46 local strict-order lowering. -/
theorem S2_q46_localStrictOrder_family_of_localGeometricSourceRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q46_localGeometricSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q46_geometricSelectionInputSource_of_localGeometricSourceRows
            (C := C) (inputs := inputs) (source C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
          inputs
          (selectedNeighborGeometricCarrierLeft
            (C := C) (inputs := inputs)
            selectedRows.toGeometricSelectionInputSource)
          (selectedNeighborGeometricCarrierRight
            (C := C) (inputs := inputs)
            selectedRows.toGeometricSelectionInputSource) := by
  intro m C inputs
  exact
    S2_q46_localStrictOrder_of_localGeometricSourceRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Family form of the q46 boundary-free local-angular lowering. -/
noncomputable def
    S2_q46_boundaryFreeLocalSectorGeometricAngularSource_family_of_localGeometricSourceRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q46_localGeometricSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        BoundaryFreeLocalSectorGeometricAngularSource inputs := by
  intro m C inputs
  exact
    S2_q46_boundaryFreeLocalSectorGeometricAngularSource_of_localGeometricSourceRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q47-local-geometric-producer-worker`.

Producer rows strictly below `S2_q46_localGeometricSourceRows`.  The selected
heads still come from the selected unbounded-frontier local-isolation source;
the endpoint branch is only the local-radius cover needed to promote the
checked selected-head local row, and the selected-carrier successor row is
lowered to the genuine selected actual-carrier `faceSucc` angle row. -/
structure S2_q47_localGeometricProducerRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) where
  localIsolation :
    SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs
  geometricRows :
    let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) localIsolation
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (localSectorRows a).left (localSectorRows a).right)
  endpointLocalRadiusCovers :
    let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) localIsolation
    let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
      localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
        (C := C) (inputs := inputs) localSectorRows
    let localEndpointRows :
        IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
      S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedRows
    IncidentGermEndpointLocalRadiusCoversRows
      (C := C) (inputs := inputs) (selectedRows := selectedRows)
      localEndpointRows
  selectedActualCarrierFaceSuccAngleRows :
    let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) localIsolation
    let geometricSelection :
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs :=
      S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
        (C := C) (inputs := inputs) localSectorRows geometricRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
      inputs selectedRows

set_option linter.style.longLine false in
/-- Claim `S2-q48-local-geometric-producer-lowering`.

Strict q48 lowering into the q47 local-geometric producer package.  The
premises are exactly the lower local rows: selected-edge local isolation,
pointwise same-head geometric angular rows, endpoint local-radius cover rows,
and selected actual-carrier `faceSucc` angle rows. -/
noncomputable def
    S2_q48_localGeometricProducerRows_of_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localIsolation :
      SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
        localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
          (C := C) (inputs := inputs) localSectorRows
      let localEndpointRows :
          IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
        S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedRows
      IncidentGermEndpointLocalRadiusCoversRows
        (C := C) (inputs := inputs) (selectedRows := selectedRows)
        localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      let geometricSelection :
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
        S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
          (C := C) (inputs := inputs) localSectorRows geometricRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
        inputs selectedRows) :
    S2_q47_localGeometricProducerRows inputs :=
  { localIsolation := localIsolation
    geometricRows := geometricRows
    endpointLocalRadiusCovers := endpointLocalRadiusCovers
    selectedActualCarrierFaceSuccAngleRows :=
      selectedActualCarrierFaceSuccAngleRows }

set_option linter.style.longLine false in
/-- Family form of the q48 local-geometric producer lowering. -/
noncomputable def
    S2_q48_localGeometricProducerRows_family_of_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q47_localGeometricProducerRows inputs := by
  intro m C inputs
  exact
    S2_q48_localGeometricProducerRows_of_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles
      (C := C) (inputs := inputs)
      (localIsolation C inputs) (geometricRows C inputs)
      (endpointLocalRadiusCovers C inputs)
      (selectedActualCarrierFaceSuccAngleRows C inputs)

set_option linter.style.longLine false in
/-- q48 local-geometric producer with the actual-carrier `faceSucc` angle row
lowered to orientation plus local strict angular order.

This keeps the selected local-isolation, geometric, and endpoint-radius rows
unchanged, but replaces the bundled selected actual-carrier angle row by the
two checked rows consumed by
`S2_selected_faceSucc_angle_source_of_geometricSelection_orientationRows_localStrictOrder`.
-/
noncomputable def
    S2_q48_localGeometricProducerRows_of_selectedLocalIsolation_geometric_endpointLocalRadius_orientation_localStrictOrder
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localIsolation :
      SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
        localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
          (C := C) (inputs := inputs) localSectorRows
      let localEndpointRows :
          IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
        S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedRows
      IncidentGermEndpointLocalRadiusCoversRows
        (C := C) (inputs := inputs) (selectedRows := selectedRows)
        localEndpointRows)
    (orientationRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      let geometricSelection :
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
        S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
          (C := C) (inputs := inputs) localSectorRows geometricRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
        inputs selectedRows)
    (localStrictOrder :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      let geometricSelection :
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
        S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
          (C := C) (inputs := inputs) localSectorRows geometricRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)) :
    S2_q47_localGeometricProducerRows inputs := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      (C := C) (inputs := inputs) localIsolation
  let geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
      (C := C) (inputs := inputs) localSectorRows geometricRows
  let selectedActualCarrierFaceSuccAngleRows :
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
        inputs selectedRows :=
    S2_selected_faceSucc_angle_source_of_geometricSelection_orientationRows_localStrictOrder
      (C := C) (inputs := inputs) geometricSelection
      (by
        change
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection)
        intro e p start edgeRows htail hhead k current_frontier hsucc_tail
        exact
          orientationRows (e := e) (p := p) (start := start)
            edgeRows htail hhead k current_frontier hsucc_tail)
      (by
        change
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              (selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                (C := C) (inputs := inputs) geometricSelection).toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              (selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                (C := C) (inputs := inputs) geometricSelection).toGeometricSelectionInputSource)
        intro e p start edgeRows htail hhead k current_frontier hsucc_tail
        exact
          localStrictOrder (e := e) (p := p) (start := start)
            edgeRows htail hhead k current_frontier hsucc_tail)
  exact
    S2_q48_localGeometricProducerRows_of_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles
      (C := C) (inputs := inputs)
      localIsolation geometricRows endpointLocalRadiusCovers
      (by
        change
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection)
        intro e p start edgeRows htail hhead k current_frontier hsucc_tail
        exact
          selectedActualCarrierFaceSuccAngleRows
            (e := e) (p := p) (start := start)
            edgeRows htail hhead k current_frontier hsucc_tail)

set_option linter.style.longLine false in
/-- Family form of the q48 producer lowering through selected actual-carrier
orientation and local strict-order rows. -/
noncomputable def
    S2_q48_localGeometricProducerRows_family_of_selectedLocalIsolation_geometric_endpointLocalRadius_orientation_localStrictOrder
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (orientationRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
            inputs selectedRows)
    (localStrictOrder :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q47_localGeometricProducerRows inputs := by
  intro m C inputs
  exact
    S2_q48_localGeometricProducerRows_of_selectedLocalIsolation_geometric_endpointLocalRadius_orientation_localStrictOrder
      (C := C) (inputs := inputs) (localIsolation C inputs)
      (geometricRows C inputs) (endpointLocalRadiusCovers C inputs)
      (orientationRows C inputs) (localStrictOrder C inputs)

set_option linter.style.longLine false in
/-- q47 erases the local producer rows to the q46 local-geometric source
package. -/
noncomputable def
    S2_q47_localGeometricSourceRows_of_localGeometricProducerRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : S2_q47_localGeometricProducerRows inputs) :
    S2_q46_localGeometricSourceRows inputs := by
  refine
    { localIsolation := source.localIsolation
      geometricRows := source.geometricRows
      endpointRows := ?_
      selectedCarrierRows := ?_ }
  · let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) source.localIsolation
    let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
      localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
        (C := C) (inputs := inputs) localSectorRows
    let localEndpointRows :
        IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
      S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedRows
    exact
      incidentGermEndpointSelectedHeadRows_of_selectedHeadLocalRows_endpointLocalRadiusCoversRows_20260521r15
        (C := C) (inputs := inputs) selectedRows localEndpointRows
        (by
          simpa [localSectorRows, selectedRows, localEndpointRows] using
            source.endpointLocalRadiusCovers)
  · let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) source.localIsolation
    let geometricSelection :
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs :=
      S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
        (C := C) (inputs := inputs) localSectorRows source.geometricRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    let angleRows :
        RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
          inputs selectedRows := by
      intro e p start edgeRows htail hhead m current_frontier hsucc_tail
      simpa [localSectorRows, geometricSelection, selectedRows] using
        source.selectedActualCarrierFaceSuccAngleRows
          (e := e) (p := p) (start := start)
          edgeRows htail hhead m current_frontier hsucc_tail
    let carrierRows :
        RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
          inputs
          (selectedNeighborGeometricCarrierLeft
            (C := C) (inputs := inputs)
            selectedRows.toGeometricSelectionInputSource)
          (selectedNeighborGeometricCarrierRight
            (C := C) (inputs := inputs)
            selectedRows.toGeometricSelectionInputSource) :=
      rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource_of_selectedActualCarrierFaceSuccAngleRows_20260522q5
        (C := C) (inputs := inputs) selectedRows angleRows
    change
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
    intro e p start edgeRows htail hhead m current_frontier hsucc_tail
    exact carrierRows edgeRows htail hhead m current_frontier hsucc_tail

set_option linter.style.longLine false in
/-- Family form of the q47 local-geometric producer eraser. -/
noncomputable def
    S2_q47_localGeometricSourceRows_family_of_localGeometricProducerRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q47_localGeometricProducerRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q46_localGeometricSourceRows inputs := by
  intro m C inputs
  exact
    S2_q47_localGeometricSourceRows_of_localGeometricProducerRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q47-actual-sector-composer-main`, selected raw-row helper.

This names the exact selected raw orbit produced by the current q47 source
leaves: trace no-closed topology, pointwise outside accumulation, and the q47
local-geometric producer rows.  It is intentionally below the actual-sector
and W32 consumers, so later repeated-tail/cut sources can target this orbit
directly. -/
noncomputable def
    S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs)
    (localProducerRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q47_localGeometricProducerRows inputs)
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    SelectedRawTailCoverageSourceRows inputs := by
  let localGeometricRows :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          S2_q46_localGeometricSourceRows Dinputs :=
    S2_q47_localGeometricSourceRows_family_of_localGeometricProducerRows
      localProducerRows
  let geometricSelection :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            D Dinputs :=
    S2_q46_geometricSelectionInputSource_family_of_localGeometricSourceRows
      localGeometricRows
  let orientationRows :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                Dinputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := D) (inputs := Dinputs) (geometricSelection D Dinputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
            Dinputs selectedRows :=
    S2_q46_orientationRows_family_of_localGeometricSourceRows
      localGeometricRows
  let localStrictOrder :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                Dinputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := D) (inputs := Dinputs) (geometricSelection D Dinputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            Dinputs
            (selectedNeighborGeometricCarrierLeft
              (C := D) (inputs := Dinputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := D) (inputs := Dinputs)
              selectedRows.toGeometricSelectionInputSource) :=
    S2_q46_localStrictOrder_family_of_localGeometricSourceRows
      localGeometricRows
  let localAngular :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          BoundaryFreeLocalSectorGeometricAngularSource Dinputs :=
    S2_q46_boundaryFreeLocalSectorGeometricAngularSource_family_of_localGeometricSourceRows
      localGeometricRows
  let frontier_noOpen :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
    (S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentPointsBetween_20260522
      (S2_q26_kComponentPointsBetween_of_traceNoClosedSeparation_20260522
        trace_noClosed)).1
  let frontier_noClosed :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
    (S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentPointsBetween_20260522
      (S2_q26_kComponentPointsBetween_of_traceNoClosedSeparation_20260522
        trace_noClosed)).2
  let frontier_vertex_incident :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          FrontierVertexIncidentUnboundedFrontierEdgeSource D Dinputs :=
    S2_q37_selected_frontier_incidence_worker_of_finiteDrawingPreconnected_outsideAccumulation_20260522
      (finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
        frontier_noClosed)
      outside_accumulation
  let pair :=
    S2_q31_selectedCarrierRows_and_incidentGermRows_of_geometricSelection_orientation_localStrict_localAngular
      (C := C) (inputs := inputs)
      (geometricSelection C inputs)
      (orientationRows C inputs)
      (localStrictOrder C inputs)
      (localAngular C inputs)
  exact
    S2_r17_selectedRawTailCoverageSourceRows_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows
      (C := C) (inputs := inputs)
      frontier_noOpen (frontier_vertex_incident C inputs)
      (geometricSelection C inputs)
      pair.2 pair.1

set_option linter.style.longLine false in
/-- Claim `S2-q47-face-dart-producer-composition`.

This is the source-facing q47 producer surface: the same q47 rows that feed the
actual-sector composer first produce the face-dart exterior carrier plus
same-boundary angular rows.  The remaining repeated-tail premise is still on
the selected raw orbit built from the input rows; no actual-sector, boundary
cycle, W32 target, or induced frontier graph is assumed. -/
noncomputable def
    S2_q47_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_traceNoClosed_outsideAccumulation_localGeometricProducer_pairwiseMinimalDeletedTailSeparation
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs)
    (localProducerRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q47_localGeometricProducerRows inputs)
    (pairwiseMinimal :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
            (S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
              trace_noClosed outside_accumulation localProducerRows
              (C := C) inputs).O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        PSigma fun rows : FaceDartOrbitExteriorCarrierRows C inputs =>
          forall k : Fin rows.orbit.boundary.length,
            GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
              C rows.orbit.boundary k := by
  let localGeometricRows :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          S2_q46_localGeometricSourceRows Dinputs :=
    S2_q47_localGeometricSourceRows_family_of_localGeometricProducerRows
      localProducerRows
  let geometricSelection :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            D Dinputs :=
    S2_q46_geometricSelectionInputSource_family_of_localGeometricSourceRows
      localGeometricRows
  let orientationRows :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                Dinputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := D) (inputs := Dinputs) (geometricSelection D Dinputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
            Dinputs selectedRows :=
    S2_q46_orientationRows_family_of_localGeometricSourceRows
      localGeometricRows
  let localStrictOrder :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                Dinputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := D) (inputs := Dinputs) (geometricSelection D Dinputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            Dinputs
            (selectedNeighborGeometricCarrierLeft
              (C := D) (inputs := Dinputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := D) (inputs := Dinputs)
              selectedRows.toGeometricSelectionInputSource) :=
    S2_q46_localStrictOrder_family_of_localGeometricSourceRows
      localGeometricRows
  let localAngular :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          BoundaryFreeLocalSectorGeometricAngularSource Dinputs :=
    S2_q46_boundaryFreeLocalSectorGeometricAngularSource_family_of_localGeometricSourceRows
      localGeometricRows
  let frontier_noClosed :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
    (S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentPointsBetween_20260522
      (S2_q26_kComponentPointsBetween_of_traceNoClosedSeparation_20260522
        trace_noClosed)).2
  let frontier_vertex_incident :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          FrontierVertexIncidentUnboundedFrontierEdgeSource D Dinputs :=
    S2_q37_selected_frontier_incidence_worker_of_finiteDrawingPreconnected_outsideAccumulation_20260522
      (finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
        frontier_noClosed)
      outside_accumulation
  intro m C inputs
  exact
    S2_q46_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_traceNoClosed_frontierVertexIncident_geometricSelection_orientation_localStrict_localAngular_cyclicSuccCutPartitions
      trace_noClosed frontier_vertex_incident geometricSelection
      orientationRows localStrictOrder localAngular
      (fun {m'} C' inputs' => by
        let selectedRawRows : SelectedRawTailCoverageSourceRows inputs' :=
          S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
            trace_noClosed outside_accumulation localProducerRows
            (C := C') inputs'
        have hpairwise :
            S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
              selectedRawRows.O := by
          change
            S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
              (S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
                trace_noClosed outside_accumulation localProducerRows
                (C := C') inputs').O
          exact pairwiseMinimal C' inputs'
        have hactual :
            SelectedRawOrbitRepeatedTailActualExteriorArcRows selectedRawRows :=
          selectedRawOrbitRepeatedTailActualExteriorArcRows_of_pairwiseMinimalDeletedTailSeparation_20260522q47
            (C := C') (inputs := inputs') selectedRawRows hpairwise
        change SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource selectedRawRows
        exact
          selectedRawOrbitCyclicSuccDeletedTailCutPartitionSource_of_actualExteriorArcRows_20260522q46
            (C := C') (inputs := inputs') selectedRawRows hactual)
      (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q48-face-dart-producer-assembler`.

This is the current input-facing face-dart/angular producer assembler.  It
replaces the q47 bundled topology and local-producer premises by the q48 lower
source rows: Janiszewski/boundary-bumping topology, selected-edge local
isolation, pointwise geometric rows, endpoint local-radius cover rows, selected
actual-carrier `faceSucc` angle rows, and q38 pairwise repeated-tail
separation for the exact selected raw orbit assembled from those rows. -/
noncomputable def
    S2_q48_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_janiszewskiBoundaryBumping_frontierPreconnected_boundaryBumpingObstruction_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles_pairwiseMinimalDeletedTailSeparation
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs)
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (pairwiseMinimal :
      let topologySources :=
        S2_q48_traceNoClosed_outsideAccumulation_sources_of_janiszewskiBoundaryBumping_boundaryBumpingObstruction_20260522q48
          boundary_bumping no_singleton_bumping
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
            (S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
              topologySources.1 topologySources.2
              (S2_q48_localGeometricProducerRows_family_of_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles
                localIsolation geometricRows endpointLocalRadiusCovers
                selectedActualCarrierFaceSuccAngleRows)
              (C := C) inputs).O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        PSigma fun rows : FaceDartOrbitExteriorCarrierRows C inputs =>
          forall k : Fin rows.orbit.boundary.length,
            GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
              C rows.orbit.boundary k := by
  let topologySources :=
    S2_q48_traceNoClosed_outsideAccumulation_sources_of_janiszewskiBoundaryBumping_boundaryBumpingObstruction_20260522q48
      boundary_bumping no_singleton_bumping
  let localProducerRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q47_localGeometricProducerRows inputs :=
    S2_q48_localGeometricProducerRows_family_of_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles
      localIsolation geometricRows endpointLocalRadiusCovers
      selectedActualCarrierFaceSuccAngleRows
  intro m C inputs
  exact
    S2_q47_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_traceNoClosed_outsideAccumulation_localGeometricProducer_pairwiseMinimalDeletedTailSeparation
      topologySources.1 topologySources.2 localProducerRows
      (by
        intro m C inputs
        simpa [topologySources, localProducerRows] using
          pairwiseMinimal C inputs)
      (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q48-face-dart-producer-assembler`, repeated-tail
cut-partition source form.

This is the same q48 face-dart/angular producer surface as the pairwise
minimal assembler above, but the repeated-tail premise is lowered from
`SelectedRawOrbitRepeatedTailCutPartitions` for the exact selected raw rows
built from the q48 topology and local-geometric producer rows. -/
noncomputable def
    S2_q48_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_janiszewskiBoundaryBumping_frontierPreconnected_boundaryBumpingObstruction_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles_repeatedTailCutPartitions
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs)
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (cutPartitions :
      let topologySources :=
        S2_q48_traceNoClosed_outsideAccumulation_sources_of_janiszewskiBoundaryBumping_boundaryBumpingObstruction_20260522q48
          boundary_bumping no_singleton_bumping
      let localProducerRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              S2_q47_localGeometricProducerRows inputs :=
        S2_q48_localGeometricProducerRows_family_of_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles
          localIsolation geometricRows endpointLocalRadiusCovers
          selectedActualCarrierFaceSuccAngleRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitRepeatedTailCutPartitions
            (S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
              topologySources.1 topologySources.2 localProducerRows
              (C := C) (inputs := inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        PSigma fun rows : FaceDartOrbitExteriorCarrierRows C inputs =>
          forall k : Fin rows.orbit.boundary.length,
            GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
              C rows.orbit.boundary k := by
  let topologySources :=
    S2_q48_traceNoClosed_outsideAccumulation_sources_of_janiszewskiBoundaryBumping_boundaryBumpingObstruction_20260522q48
      boundary_bumping no_singleton_bumping
  let localProducerRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q47_localGeometricProducerRows inputs :=
    S2_q48_localGeometricProducerRows_family_of_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles
      localIsolation geometricRows endpointLocalRadiusCovers
      selectedActualCarrierFaceSuccAngleRows
  intro m C inputs
  exact
    S2_q48_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_janiszewskiBoundaryBumping_frontierPreconnected_boundaryBumpingObstruction_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles_pairwiseMinimalDeletedTailSeparation
      boundary_bumping no_singleton_bumping localIsolation geometricRows
      endpointLocalRadiusCovers selectedActualCarrierFaceSuccAngleRows
      (fun {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C) => by
        let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
          S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
            topologySources.1 topologySources.2 localProducerRows
            (C := C) (inputs := inputs)
        have hcut :
            SelectedRawOrbitRepeatedTailCutPartitions selectedRawRows := by
          intro i j hij htail
          exact
            (cutPartitions (C := C) (inputs := inputs))
              hij
              (by
                simpa [selectedRawRows, topologySources, localProducerRows] using
                  htail)
        change
          S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
            selectedRawRows.O
        exact
          S2_q48_pairwiseMinimalDeletedTailSeparationSource_of_repeatedTailCutPartitions_noCut
            (C := C) (inputs := inputs) selectedRawRows hcut)
      (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q49-main-exterior-face-source`, actual-sector eraser for the q48
producer surface.

This is not a new W32 route.  It records the direct handoff from the q48
face-dart/angular producer surface to the actual exterior-sector source shape
that S2 still has to inhabit from `FinitePlanarOuterComponentInputs C`. -/
noncomputable def
    S2_q49_actualExteriorSectorInputSourceRows_family_of_janiszewskiBoundaryBumping_frontierPreconnected_boundaryBumpingObstruction_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles_pairwiseMinimalDeletedTailSeparation
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs)
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (pairwiseMinimal :
      let topologySources :=
        S2_q48_traceNoClosed_outsideAccumulation_sources_of_janiszewskiBoundaryBumping_boundaryBumpingObstruction_20260522q48
          boundary_bumping no_singleton_bumping
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
            (S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
              topologySources.1 topologySources.2
              (S2_q48_localGeometricProducerRows_family_of_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles
                localIsolation geometricRows endpointLocalRadiusCovers
                selectedActualCarrierFaceSuccAngleRows)
              (C := C) inputs).O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) :=
  actualExteriorSectorInputSourceRows_of_faceDartOrbitExteriorCarrierRows_family
    (S2_q48_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_janiszewskiBoundaryBumping_frontierPreconnected_boundaryBumpingObstruction_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles_pairwiseMinimalDeletedTailSeparation
      boundary_bumping no_singleton_bumping localIsolation geometricRows
      endpointLocalRadiusCovers selectedActualCarrierFaceSuccAngleRows
      pairwiseMinimal)

set_option linter.style.longLine false in
/-- Claim `S2-q47-actual-sector-composer-main`.

The current q47 source-facing composer for the actual exterior-sector package:
topology gives trace no-closed and frontier incidence, q47 local-geometric
producer rows give the selected geometric raw-walk data, and q38 pairwise
minimal deleted-tail separation supplies the repeated-tail actual exterior arc
rows for the exact selected raw orbit. -/
noncomputable def
    S2_q47_actualExteriorSectorInputSourceRows_family_of_traceNoClosed_outsideAccumulation_localGeometricProducer_pairwiseMinimalDeletedTailSeparation
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs)
    (localProducerRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q47_localGeometricProducerRows inputs)
    (pairwiseMinimal :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
            (S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
              trace_noClosed outside_accumulation localProducerRows
              (C := C) inputs).O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let localGeometricRows :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          S2_q46_localGeometricSourceRows Dinputs :=
    S2_q47_localGeometricSourceRows_family_of_localGeometricProducerRows
      localProducerRows
  let geometricSelection :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            D Dinputs :=
    S2_q46_geometricSelectionInputSource_family_of_localGeometricSourceRows
      localGeometricRows
  let orientationRows :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                Dinputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := D) (inputs := Dinputs) (geometricSelection D Dinputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
            Dinputs selectedRows :=
    S2_q46_orientationRows_family_of_localGeometricSourceRows
      localGeometricRows
  let localStrictOrder :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                Dinputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := D) (inputs := Dinputs) (geometricSelection D Dinputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            Dinputs
            (selectedNeighborGeometricCarrierLeft
              (C := D) (inputs := Dinputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := D) (inputs := Dinputs)
              selectedRows.toGeometricSelectionInputSource) :=
    S2_q46_localStrictOrder_family_of_localGeometricSourceRows
      localGeometricRows
  let localAngular :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          BoundaryFreeLocalSectorGeometricAngularSource Dinputs :=
    S2_q46_boundaryFreeLocalSectorGeometricAngularSource_family_of_localGeometricSourceRows
      localGeometricRows
  intro m C inputs
  exact
    S2_q45_actualExteriorSectorInputSourceRows_family_of_traceNoClosed_outsideAccumulation_geometricSelection_orientation_localStrict_localAngular_cyclicSuccCutPartitions
      trace_noClosed outside_accumulation geometricSelection
      orientationRows localStrictOrder localAngular
      (fun {m} C inputs => by
        let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
          S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
            trace_noClosed outside_accumulation localProducerRows
            (C := C) inputs
        have hpairwise :
            S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
              selectedRawRows.O := by
          change
            S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
              (S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
                trace_noClosed outside_accumulation localProducerRows
                (C := C) inputs).O
          exact pairwiseMinimal C inputs
        have hactual :
            SelectedRawOrbitRepeatedTailActualExteriorArcRows selectedRawRows :=
          selectedRawOrbitRepeatedTailActualExteriorArcRows_of_pairwiseMinimalDeletedTailSeparation_20260522q47
            (C := C) (inputs := inputs) selectedRawRows hpairwise
        change SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource selectedRawRows
        exact
          selectedRawOrbitCyclicSuccDeletedTailCutPartitionSource_of_actualExteriorArcRows_20260522q46
            (C := C) (inputs := inputs) selectedRawRows hactual)
      (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- Family-level exact k4 lowering.

Thus the bare family statement "every actual unbounded-frontier carrier vertex
has exactly two selected carrier neighbours" is equivalent to the lower
ambient deleted-graph source family.  The remaining source obligation is to
produce those two selected incident frontier edges and the deleted-graph
unreachability row for any proposed third carrier neighbour. -/
theorem S2_dynamic_no_cut_degree_two_family_k4_iff_unreachableAfterDeleteInputSource :
    (forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        ActualCarrierDegreeTwoSource inputs) <->
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          Nonempty
            (UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
              C inputs)) := by
  constructor
  · intro source m C inputs
    exact
      (nonempty_unreachableAfterDeleteInputSource_iff_actualCarrierDegreeTwo
        (C := C) (inputs := inputs)).2 (source C inputs)
  · intro source m C inputs
    exact
      (nonempty_unreachableAfterDeleteInputSource_iff_actualCarrierDegreeTwo
        (C := C) (inputs := inputs)).1 (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-k5-deleted-neighbor-unreachable`, actual selected-carrier cut
field form.

The finite-plane no-cut field is consumed through the k4 cut-partition
consumer.  The residual source is the actual selected frontier carrier data:
two genuine `unboundedFrontierEdgeSet` heads at each actual carrier vertex and
the concrete cut-partition payload for any third actual carrier neighbour. -/
noncomputable def
    S2_k5_deleted_neighbor_unreachable_of_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source :
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  unreachableAfterDeleteInputSource_of_actualCarrierDegreeTwo
    (C := C) inputs
    (S2_dynamic_no_cut_degree_two_k4_of_cutPartitionInputSource
      (C := C) (inputs := inputs)
      (S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_inputSource_of_fieldwise
        (C := C) (inputs := inputs) source))

set_option linter.style.longLine false in
/-- Family form of
`S2_k5_deleted_neighbor_unreachable_of_carrierCutFieldwise`. -/
noncomputable def
    S2_k5_deleted_neighbor_unreachable_family_of_carrierCutFieldwise
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
            inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_k5_deleted_neighbor_unreachable_of_carrierCutFieldwise
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-k5-deleted-neighbor-unreachable`, pure selected-incident-edge
form.

Pure actual selected frontier-carrier rows first give the e32 cut field, then
the k5 fieldwise reducer uses the k4 no-cut consumer to obtain the ambient
deleted-neighbour unreachable source. -/
noncomputable def
    S2_k5_deleted_neighbor_unreachable_of_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : LocalSelectedIncidentEdgePairSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  S2_k5_deleted_neighbor_unreachable_of_carrierCutFieldwise
    (C := C) (inputs := inputs)
    (S2CarrierCutSource.S2_agent_carrier_cut_fieldwise_source_20260521f3_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of
`S2_k5_deleted_neighbor_unreachable_of_selectedIncidentEdgePairRows`. -/
noncomputable def
    S2_k5_deleted_neighbor_unreachable_family_of_selectedIncidentEdgePairRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          LocalSelectedIncidentEdgePairSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_k5_deleted_neighbor_unreachable_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Exact k5 residual in the actual selected-carrier cut-field form.

Forward direction forgets the deleted-neighbour proof to the same selected
heads and cut rows.  Reverse direction is the k5 no-cut/selected-carrier
reducer above. -/
theorem S2_k5_deleted_neighbor_unreachable_nonempty_iff_carrierCutFieldwise
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs) <->
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
        inputs := by
  constructor
  · rintro ⟨source⟩
    exact
      S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise_of_unreachableAfterDelete
        (C := C) (inputs := inputs) source
  · intro source
    exact
      ⟨S2_k5_deleted_neighbor_unreachable_of_carrierCutFieldwise
        (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- Exact k5 residual in the pure selected-incident-edge form.

The forward direction uses the k4 deleted-neighbour consumer to recover the
selected incident rows; the reverse direction is the selected-row k5 reducer. -/
theorem S2_k5_deleted_neighbor_unreachable_nonempty_iff_selectedIncidentEdgePairRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty
        (UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs) <->
      Nonempty (LocalSelectedIncidentEdgePairSourceRows inputs) := by
  constructor
  · rintro ⟨source⟩
    exact
      ⟨S2_dynamic_no_cut_selectedIncidentRows_k4_of_unreachableAfterDeleteInputSource
        (C := C) (inputs := inputs) source⟩
  · rintro ⟨source⟩
    exact
      ⟨S2_k5_deleted_neighbor_unreachable_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) source⟩

set_option linter.style.longLine false in
/-- Claim `S2-agent-carrier-neighbor-source-20260521k5`,
unreachable-after-delete form.

The ambient deleted-neighbour source is lowered to the selected-edge local
isolation rows.  The selected heads remain the actual
`unboundedFrontierEdgeSet` heads stored in the isolation source; the carrier
cut field is produced by the k5 cut-source reducer, then consumed by the
existing no-cut deleted-neighbour route. -/
noncomputable def
    S2_agent_carrier_neighbor_source_20260521k5_unreachableAfterDelete_of_selectedEdgeLocalIsolation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
      C inputs :=
  unboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource_of_localSectorRows
    (C := C) (inputs := inputs)
    (localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of the k5 selected-edge local-isolation deleted-neighbour
reduction. -/
noncomputable def
    S2_agent_carrier_neighbor_source_20260521k5_unreachableAfterDelete_family_of_selectedEdgeLocalIsolation
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
          C inputs := by
  intro m C inputs
  exact
    S2_agent_carrier_neighbor_source_20260521k5_unreachableAfterDelete_of_selectedEdgeLocalIsolation
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- Selected-edge local finite-drawing isolation gives actual carrier degree two.

The lower row is the selected-edge local finite-drawing isolation package: at
each actual unbounded-frontier carrier vertex it names two genuine
`unboundedFrontierEdgeSet` heads and a local no-third-germ radius. -/
theorem
    actualCarrierDegreeTwo_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    ActualCarrierDegreeTwoSource inputs := by
  let localRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      (C := C) (inputs := inputs) source
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  simpa [ActualCarrierDegreeTwoSource] using
    (unboundedFrontierCarrierGraph_neighborFinset_card_two_of_localSectorRows
      (C := C) (inputs := inputs) localRows)

set_option linter.style.longLine false in
/-- Claim `S2-q42-local-frontier-carrier-worker`, local-isolation consumer.

From the same selected-edge local finite-drawing isolation package, export the
two pointwise carrier row families used downstream: actual neighbour-pair rows
and actual local-sector rows. -/
noncomputable def
    S2_q42_local_frontier_carrier_worker_of_selectedEdgeLocalIsolation
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      UnboundedFrontierCarrierNeighborPairAt inputs a) ×
      (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) := by
  let localRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      (C := C) (inputs := inputs) source
  let neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a :=
    unboundedFrontierCarrierNeighborPairRows_of_localSectorRows
      (C := C) (inputs := inputs) localRows
  exact ⟨neighborRows, localRows⟩

set_option linter.style.longLine false in
/-- Family form of
`S2_q42_local_frontier_carrier_worker_of_selectedEdgeLocalIsolation`. -/
noncomputable def
    S2_q42_local_frontier_carrier_worker_family_of_selectedEdgeLocalIsolation
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        (forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierNeighborPairAt inputs a) ×
          (forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) := by
  intro m C inputs
  exact
    S2_q42_local_frontier_carrier_worker_of_selectedEdgeLocalIsolation
      (C := C) (inputs := inputs) (source C inputs)

set_option linter.style.longLine false in
/-- The selected-edge local finite-drawing isolation package is an exact
residual for actual carrier degree two.

The reverse direction chooses the two actual carrier neighbours and obtains
the local no-third-germ radius from the existing finite graph-vertex isolation
row.  Thus the remaining unproved q42 input-level source can be stated either
as `ActualCarrierDegreeTwoSource inputs` or as nonemptiness of
`SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs`; neither form
uses induced frontier graphs, arbitrary cycles, all-adjacent endpoint rows,
W32, or actual-sector rows. -/
theorem
    nonempty_selectedUnboundedFrontierEdgeLocalIsolationSourceRows_iff_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    Nonempty (SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) ↔
      ActualCarrierDegreeTwoSource inputs := by
  constructor
  · rintro ⟨source⟩
    exact
      actualCarrierDegreeTwo_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) source
  · intro hdegree
    exact
      ⟨localRadiusSelectedEdgeSourceRows_of_neighborPairRows
        (C := C) (inputs := inputs)
        (neighborPairRows_of_actualCarrierDegreeTwo
          (C := C) inputs hdegree)⟩

set_option linter.style.longLine false in
/-- Selected-edge local finite-drawing isolation chosen directly from actual
carrier degree two.

This names the constructive reverse direction of
`nonempty_selectedUnboundedFrontierEdgeLocalIsolationSourceRows_iff_actualCarrierDegreeTwo`:
the two selected heads are the actual carrier neighbours, and the local
finite-drawing isolation radius is supplied by the existing neighbour-pair
local-radius constructor. -/
noncomputable def
    selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (hdegree : ActualCarrierDegreeTwoSource inputs) :
    SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
  localRadiusSelectedEdgeSourceRows_of_neighborPairRows
    (C := C) (inputs := inputs)
    (neighborPairRows_of_actualCarrierDegreeTwo
      (C := C) inputs hdegree)

set_option linter.style.longLine false in
/-- Family form of
`selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo`. -/
noncomputable def
    selectedUnboundedFrontierEdgeLocalIsolationSourceRows_family_of_actualCarrierDegreeTwo
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs := by
  intro m C inputs
  exact
    selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
      (C := C) inputs (source C inputs)

set_option linter.style.longLine false in
/-- Selected-edge local finite-drawing isolation chosen from the
deleted-neighbour unreachable source.

The deleted-neighbour row is used only through its already checked erasure to
actual carrier degree two; no actual-sector, boundary-cycle, W32, induced
frontier graph, all-adjacent endpoint, or global no-between row is introduced. -/
noncomputable def
    selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_unreachableAfterDeleteInputSource
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (source :
      UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
        C inputs) :
    SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
  selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
    (C := C) inputs
    (actualCarrierDegreeTwo_of_unreachableAfterDeleteInputSource
      (C := C) (inputs := inputs) source)

set_option linter.style.longLine false in
/-- Family form of
`selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_unreachableAfterDeleteInputSource`. -/
noncomputable def
    selectedUnboundedFrontierEdgeLocalIsolationSourceRows_family_of_unreachableAfterDeleteInputSource
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs := by
  intro m C inputs
  exact
    selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_unreachableAfterDeleteInputSource
      (C := C) inputs (source C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q48-local-geometric-producer-source-worker`, pointwise packager.

This is the exact q48 local source surface: selected finite-drawing local
isolation supplies the actual two-germ carrier heads, the geometric rows are
genuine `GraphVertexGeometricAngularNeighborSelectionRow`s for those same
heads, and the remaining endpoint/face-successor rows stay on the selected
actual carrier. -/
noncomputable def
    S2_q48_localGeometricProducerRows_of_localIsolation_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localIsolation :
      SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
        localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
          (C := C) (inputs := inputs) localSectorRows
      let localEndpointRows :
          IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
        S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
          (C := C) (inputs := inputs) selectedRows
      IncidentGermEndpointLocalRadiusCoversRows
        (C := C) (inputs := inputs) (selectedRows := selectedRows)
        localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      let geometricSelection :
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
        S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
          (C := C) (inputs := inputs) localSectorRows geometricRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
        inputs selectedRows) :
    S2_q47_localGeometricProducerRows inputs := by
  refine
    { localIsolation := localIsolation
      geometricRows := ?_
      endpointLocalRadiusCovers := ?_
      selectedActualCarrierFaceSuccAngleRows := ?_ }
  · simpa using geometricRows
  · simpa using endpointLocalRadiusCovers
  · let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) localIsolation
    let geometricSelection :
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs :=
      S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
        (C := C) (inputs := inputs) localSectorRows geometricRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    change
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
        inputs selectedRows
    intro e p start edgeRows htail hhead m current_frontier hsucc_tail
    exact
      selectedActualCarrierFaceSuccAngleRows
        (e := e) (p := p) (start := start)
        edgeRows htail hhead m current_frontier hsucc_tail

set_option linter.style.longLine false in
/-- Family form of the q48 pointwise local-geometric producer packager. -/
noncomputable def
    S2_q48_localGeometricProducerRows_family_of_localIsolation_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q47_localGeometricProducerRows inputs := by
  intro m C inputs
  exact
    S2_q48_localGeometricProducerRows_of_localIsolation_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
      (C := C) (inputs := inputs) (localIsolation C inputs)
      (geometricRows C inputs)
      (endpointLocalRadiusCovers C inputs)
      (selectedActualCarrierFaceSuccAngleRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q79-selected-local-angular-source`, pointwise face-successor
rotation rows.

For the heads selected by the local-isolation source, this is the honest local
rotation evidence closest to q18: an actual geometric `faceSucc` step and the
strict selected exterior-sector turn for exactly those two heads. -/
abbrev S2_q79_selectedLocalFaceSuccRotationRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localIsolation :
      SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs) : Prop :=
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      (C := C) (inputs := inputs) localIsolation
  forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    Exists fun d : UnitDistanceDart C =>
      Exists fun e : UnitDistanceDart C =>
          d.head = a.1 ∧
          d.reverse.head = (localSectorRows a).left ∧
          e.head = (localSectorRows a).right ∧
          (GeometricRotationSystem.geometricUnitDistanceRotationSystem C).faceSucc
              d = e ∧
          GeometricRotationSystem.graphDartArg
              (GeometricRotationSystem.canonicalGeometricGraph C) a.1
              (localSectorRows a).left <
            GeometricRotationSystem.graphDartArg
              (GeometricRotationSystem.canonicalGeometricGraph C) a.1
              (localSectorRows a).right

set_option linter.style.longLine false in
/-- q79 lowers the selected local q18 angular/no-between source to actual
selected exterior-sector `faceSucc` rotation rows.

The no-between payload is obtained through the geometric rotation system for
the one selected sector at each local-isolation carrier.  No global
all-outgoing no-between row, actual-sector package, W32 row, boundary cycle,
induced frontier graph, arbitrary cycle, or all-adjacent endpoint row is used. -/
theorem
    S2_q79_selectedExteriorSectorAngularNoBetweenRows_of_selectedLocalIsolation_faceSuccRotationRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localIsolation :
      SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (rotationRows :
      S2_q79_selectedLocalFaceSuccRotationRows
        (C := C) (inputs := inputs) localIsolation) :
    let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) localIsolation
    S2_q18_selectedExteriorSectorAngularNoBetweenRows
      (C := C) (inputs := inputs) localSectorRows := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      (C := C) (inputs := inputs) localIsolation
  change S2_q18_selectedExteriorSectorAngularNoBetweenRows
    (C := C) (inputs := inputs) localSectorRows
  intro a
  rcases rotationRows a with
    ⟨d, e, hcenter, hleft, hright, hface, hturn⟩
  exact
    GeometricRotationSystem.graphVertexAngularNoBetweenRows_of_faceSucc_eq_selected_strictTurn
      C a.1 (localSectorRows a).left (localSectorRows a).right
      d e hcenter hleft hright hface hturn

set_option linter.style.longLine false in
/-- Family form of
`S2_q79_selectedExteriorSectorAngularNoBetweenRows_of_selectedLocalIsolation_faceSuccRotationRows`. -/
theorem
    S2_q79_selectedExteriorSectorAngularNoBetweenRows_family_of_selectedLocalIsolation_faceSuccRotationRows
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (rotationRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q79_selectedLocalFaceSuccRotationRows
            (C := C) (inputs := inputs) (localIsolation C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let localSectorRows :
            forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
              UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
          localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
            (C := C) (inputs := inputs) (localIsolation C inputs)
        S2_q18_selectedExteriorSectorAngularNoBetweenRows
          (C := C) (inputs := inputs) localSectorRows := by
  intro m C inputs
  exact
    S2_q79_selectedExteriorSectorAngularNoBetweenRows_of_selectedLocalIsolation_faceSuccRotationRows
      (C := C) (inputs := inputs) (localIsolation C inputs)
      (rotationRows C inputs)

set_option linter.style.longLine false in
/-- q79 selected-sector rotation row form.

If the selected local-isolation heads already come with genuine geometric
neighbour-selection rows, the q18 angular/no-between source is obtained
pointwise from those selected rows. -/
theorem
    S2_q79_selectedExteriorSectorAngularNoBetweenRows_of_selectedLocalIsolation_geometricRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localIsolation :
      SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (localSectorRows a).left (localSectorRows a).right)) :
    let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) localIsolation
    S2_q18_selectedExteriorSectorAngularNoBetweenRows
      (C := C) (inputs := inputs) localSectorRows := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      (C := C) (inputs := inputs) localIsolation
  change S2_q18_selectedExteriorSectorAngularNoBetweenRows
    (C := C) (inputs := inputs) localSectorRows
  intro a
  rcases geometricRows a with ⟨row⟩
  exact
    GeometricRotationSystem.graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      row

set_option linter.style.longLine false in
/-- Family form of the q79 selected-sector geometric-row source. -/
theorem
    S2_q79_selectedExteriorSectorAngularNoBetweenRows_family_of_selectedLocalIsolation_geometricRows
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let localSectorRows :
            forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
              UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
          localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
            (C := C) (inputs := inputs) (localIsolation C inputs)
        S2_q18_selectedExteriorSectorAngularNoBetweenRows
          (C := C) (inputs := inputs) localSectorRows := by
  intro m C inputs
  exact
    S2_q79_selectedExteriorSectorAngularNoBetweenRows_of_selectedLocalIsolation_geometricRows
      (C := C) (inputs := inputs) (localIsolation C inputs)
      (geometricRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q49-local-geometric-premise-source`, pointwise geometric row.

Selected local-isolation heads plus same-head angular/no-between rows supply
the q48 pointwise `GraphVertexGeometricAngularNeighborSelectionRow` premise.
This is a local source-row lowering: the only geometry input is the selected
exterior-sector angular/no-between row for the heads already chosen by the
selected local-isolation source. -/
theorem
    S2_q49_geometricRows_of_selectedLocalIsolation_angularNoBetweenRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localIsolation :
      SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (angularRows :
      let localSectorRows :
          forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          (C := C) (inputs := inputs) localIsolation
      S2_q18_selectedExteriorSectorAngularNoBetweenRows
        (C := C) (inputs := inputs) localSectorRows) :
    let localSectorRows :
        forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
          UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
      localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
        (C := C) (inputs := inputs) localIsolation
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (localSectorRows a).left (localSectorRows a).right) := by
  let localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      (C := C) (inputs := inputs) localIsolation
  exact
    S2_q18_selectedExteriorSectorGeometricRows_of_angularNoBetweenRows
      (C := C) (inputs := inputs) localSectorRows
      (by simpa [localSectorRows] using angularRows)

set_option linter.style.longLine false in
/-- Family form of the q49 pointwise geometric-row lowering. -/
theorem
    S2_q49_geometricRows_family_of_selectedLocalIsolation_angularNoBetweenRows
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          S2_q18_selectedExteriorSectorAngularNoBetweenRows
            (C := C) (inputs := inputs) localSectorRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let localSectorRows :
            forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
              UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
          localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
            (C := C) (inputs := inputs) (localIsolation C inputs)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          Nonempty
            (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
              C a.1 (localSectorRows a).left (localSectorRows a).right) := by
  intro m C inputs
  exact
    S2_q49_geometricRows_of_selectedLocalIsolation_angularNoBetweenRows
      (C := C) (inputs := inputs) (localIsolation C inputs)
      (angularRows C inputs)

set_option linter.style.longLine false in
/-- q49 local-producer family with the q48 pointwise geometric premise lowered
to selected same-head angular/no-between rows. -/
noncomputable def
    S2_q49_localGeometricProducerRows_family_of_selectedLocalIsolation_angularNoBetween_endpointRadius_selectedActualCarrierFaceSuccAngles
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          S2_q18_selectedExteriorSectorAngularNoBetweenRows
            (C := C) (inputs := inputs) localSectorRows)
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let geometricRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                Nonempty
                  (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                    C a.1 (localSectorRows a).left (localSectorRows a).right) :=
            S2_q49_geometricRows_of_selectedLocalIsolation_angularNoBetweenRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
              (angularRows C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q47_localGeometricProducerRows inputs := by
  let geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right) :=
    S2_q49_geometricRows_family_of_selectedLocalIsolation_angularNoBetweenRows
      localIsolation angularRows
  exact
    fun {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C) =>
      S2_q48_localGeometricProducerRows_family_of_localIsolation_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
      localIsolation geometricRows endpointLocalRadiusCovers
      selectedActualCarrierFaceSuccAngleRows
        (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- q49 actual-carrier-degree-two producer family with the q48 geometric-row
premise lowered to honest selected angular/no-between rows.

Actual carrier degree two is used only to choose the selected local-isolation
rows.  The geometry premise is the same-head angular/no-between source for
those selected carrier heads; q49 then reifies the corresponding genuine
geometric rotation row before feeding the q48 producer. -/
noncomputable def
    S2_q49_localGeometricProducerRows_family_of_actualCarrierDegreeTwo_angularNoBetween_endpointRadius_selectedActualCarrierFaceSuccAngles
    (degreeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          S2_q18_selectedExteriorSectorAngularNoBetweenRows
            (C := C) (inputs := inputs) localSectorRows)
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          let geometricRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                Nonempty
                  (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                    C a.1 (localSectorRows a).left (localSectorRows a).right) :=
            S2_q49_geometricRows_of_selectedLocalIsolation_angularNoBetweenRows
              (C := C) (inputs := inputs) localIsolation
              (angularRows C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q47_localGeometricProducerRows inputs := by
  let localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
    selectedUnboundedFrontierEdgeLocalIsolationSourceRows_family_of_actualCarrierDegreeTwo
      degreeRows
  exact
    fun {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C) =>
      S2_q49_localGeometricProducerRows_family_of_selectedLocalIsolation_angularNoBetween_endpointRadius_selectedActualCarrierFaceSuccAngles
      localIsolation angularRows endpointLocalRadiusCovers
      selectedActualCarrierFaceSuccAngleRows
        (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q56-carrier-degree-integration-worker`.

Integrates the checked q55 actual-carrier degree-two source into the shortest
current actual-sector producer: q55 supplies degree two, q49 turns degree two
plus the remaining local geometric leaves into q47 local-geometric producer
rows, and q47 produces the actual exterior-sector source from the exact
selected raw orbit and its pairwise minimal deleted-tail separation row.

The exposed carrier-degree leaves are exactly the q55 third-neighbour
repeated-tail index row and minimal deleted-tail separation row on the q32 raw
geometric orbit; this theorem does not assume actual-sector rows, final
boundary cycles, W32 rows, induced frontier graphs, arbitrary cycles, endpoint
shortcuts, or identity angular order. -/
noncomputable def
    S2_q56_actualExteriorSectorInputSourceRows_family_of_traceNoClosed_outsideAccumulation_componentTopology_geometricSelection_strictSuccessor_thirdRepeatedTail_minimalDeletedTailSeparation_angularNoBetween_endpointRadius_selectedActualCarrierFaceSuccAngles_pairwiseMinimalDeletedTailSeparation
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs)
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (strictSuccessorOrder :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (thirdRepeatedTail :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let pkg :=
            S2_q32_rawGeometricOrbitPackage_family_of_componentTopology_geometricSelection_strictSuccessor
              componentTopology geometricSelection strictSuccessorOrder
              C inputs
          S2CarrierCutSource.S2_q36_rawFaceWalkThirdCarrierNeighborRepeatedTailIndexSource
            (inputs := inputs) pkg.2.2.2.1)
    (minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let pkg :=
            S2_q32_rawGeometricOrbitPackage_family_of_componentTopology_geometricSelection_strictSuccessor
              componentTopology geometricSelection strictSuccessorOrder
              C inputs
          forall {i j : Fin pkg.2.2.2.1.period},
            i ≠ j ->
            (pkg.2.2.2.1.dart i).tail = (pkg.2.2.2.1.dart j).tail ->
              Exists fun left :
                  {l : Fin pkg.2.2.2.1.period //
                    cyclicForwardOpenArc i j l ∧
                      (pkg.2.2.2.1.dart l).tail ≠
                        (pkg.2.2.2.1.dart i).tail} =>
                Exists fun right :
                    {r : Fin pkg.2.2.2.1.period //
                      cyclicForwardOpenArc j i r ∧
                        (pkg.2.2.2.1.dart r).tail ≠
                          (pkg.2.2.2.1.dart i).tail} =>
                  ¬ ((GraphBridge.unitDistanceSimpleGraph C).induce
                      ({(pkg.2.2.2.1.dart i).tail}ᶜ : Set (Fin m))).Reachable
                      ⟨(pkg.2.2.2.1.dart left.1).tail, by
                        simpa using left.2.2⟩
                      ⟨(pkg.2.2.2.1.dart right.1).tail, by
                        simpa using right.2.2⟩)
    (angularRows :
      let degreeRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              ActualCarrierDegreeTwoSource inputs :=
        S2_q55_actualCarrierDegreeTwoSource_family_of_componentTopology_geometricSelection_strictSuccessor_thirdRepeatedTail_minimalDeletedTailSeparation
          componentTopology geometricSelection strictSuccessorOrder
          thirdRepeatedTail minimalSeparation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          S2_q18_selectedExteriorSectorAngularNoBetweenRows
            (C := C) (inputs := inputs) localSectorRows)
    (endpointLocalRadiusCovers :
      let degreeRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              ActualCarrierDegreeTwoSource inputs :=
        S2_q55_actualCarrierDegreeTwoSource_family_of_componentTopology_geometricSelection_strictSuccessor_thirdRepeatedTail_minimalDeletedTailSeparation
          componentTopology geometricSelection strictSuccessorOrder
          thirdRepeatedTail minimalSeparation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      let degreeRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              ActualCarrierDegreeTwoSource inputs :=
        S2_q55_actualCarrierDegreeTwoSource_family_of_componentTopology_geometricSelection_strictSuccessor_thirdRepeatedTail_minimalDeletedTailSeparation
          componentTopology geometricSelection strictSuccessorOrder
          thirdRepeatedTail minimalSeparation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          let geometricRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                Nonempty
                  (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                    C a.1 (localSectorRows a).left (localSectorRows a).right) :=
            S2_q49_geometricRows_of_selectedLocalIsolation_angularNoBetweenRows
              (C := C) (inputs := inputs) localIsolation
              (angularRows C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (pairwiseMinimal :
      let degreeRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              ActualCarrierDegreeTwoSource inputs :=
        S2_q55_actualCarrierDegreeTwoSource_family_of_componentTopology_geometricSelection_strictSuccessor_thirdRepeatedTail_minimalDeletedTailSeparation
          componentTopology geometricSelection strictSuccessorOrder
          thirdRepeatedTail minimalSeparation
      let localProducerRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              S2_q47_localGeometricProducerRows inputs :=
        S2_q49_localGeometricProducerRows_family_of_actualCarrierDegreeTwo_angularNoBetween_endpointRadius_selectedActualCarrierFaceSuccAngles
          degreeRows angularRows endpointLocalRadiusCovers
          selectedActualCarrierFaceSuccAngleRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
            (S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
              trace_noClosed outside_accumulation localProducerRows
              (C := C) inputs).O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let degreeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs :=
    S2_q55_actualCarrierDegreeTwoSource_family_of_componentTopology_geometricSelection_strictSuccessor_thirdRepeatedTail_minimalDeletedTailSeparation
      componentTopology geometricSelection strictSuccessorOrder
      thirdRepeatedTail minimalSeparation
  let localProducerRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q47_localGeometricProducerRows inputs :=
    S2_q49_localGeometricProducerRows_family_of_actualCarrierDegreeTwo_angularNoBetween_endpointRadius_selectedActualCarrierFaceSuccAngles
      degreeRows angularRows endpointLocalRadiusCovers
      selectedActualCarrierFaceSuccAngleRows
  intro m C inputs
  exact
    S2_q47_actualExteriorSectorInputSourceRows_family_of_traceNoClosed_outsideAccumulation_localGeometricProducer_pairwiseMinimalDeletedTailSeparation
      trace_noClosed outside_accumulation localProducerRows
      (by
        intro m C inputs
        simpa [degreeRows, localProducerRows] using
          pairwiseMinimal (C := C) (inputs := inputs))
      (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- q48 family reducer from actual carrier degree two plus the remaining
explicit local geometric rows.

Actual carrier degree two supplies only the selected local-isolation premise.
The geometric angular rows, endpoint local-radius covers, and selected
actual-carrier `faceSucc` angle rows remain explicit premises for the chosen
local-isolation rows. -/
noncomputable def
    S2_q48_localGeometricProducerRows_family_of_actualCarrierDegreeTwo_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
    (degreeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          ActualCarrierDegreeTwoSource inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
              (C := C) inputs (degreeRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q47_localGeometricProducerRows inputs := by
  intro m C inputs
  let localIsolation : SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
    selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
      (C := C) inputs (degreeRows C inputs)
  exact
    S2_q48_localGeometricProducerRows_of_localIsolation_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
      (C := C) (inputs := inputs) localIsolation
      (by simpa [localIsolation] using geometricRows C inputs)
      (by simpa [localIsolation] using endpointLocalRadiusCovers C inputs)
      (by
        let localSectorRows :
            forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
              UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
          localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
            (C := C) (inputs := inputs) localIsolation
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
            (C := C) (inputs := inputs) localSectorRows
            (by simpa [localIsolation, localSectorRows] using
              geometricRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        change
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows
        intro e p start edgeRows htail hhead k current_frontier hsucc_tail
        simpa [localSectorRows, geometricSelection, selectedRows, localIsolation] using
          (selectedActualCarrierFaceSuccAngleRows C inputs)
            edgeRows htail hhead k current_frontier hsucc_tail)

set_option linter.style.longLine false in
/-- q48 family reducer from deleted-neighbour unreachable rows plus the
remaining explicit local geometric rows.

The deleted-neighbour source is consumed only to obtain actual carrier degree
two, and hence selected local-isolation rows; all geometric, endpoint, and
selected actual-carrier `faceSucc` rows remain explicit. -/
noncomputable def
    S2_q48_localGeometricProducerRows_family_of_unreachableAfterDelete_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
    (unreachableRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_unreachableAfterDeleteInputSource
              (C := C) inputs (unreachableRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_unreachableAfterDeleteInputSource
              (C := C) inputs (unreachableRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_unreachableAfterDeleteInputSource
              (C := C) inputs (unreachableRows C inputs)
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q47_localGeometricProducerRows inputs := by
  intro m C inputs
  let localIsolation : SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
    selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_unreachableAfterDeleteInputSource
      (C := C) inputs (unreachableRows C inputs)
  exact
    S2_q48_localGeometricProducerRows_of_localIsolation_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
      (C := C) (inputs := inputs) localIsolation
      (by simpa [localIsolation] using geometricRows C inputs)
      (by
        simpa [localIsolation] using
          endpointLocalRadiusCovers C inputs)
      (by
        let localSectorRows :
            forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
              UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
          localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
            (C := C) (inputs := inputs) localIsolation
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
            (C := C) (inputs := inputs) localSectorRows
            (by simpa [localIsolation, localSectorRows] using
              geometricRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        change
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows
        intro e p start edgeRows htail hhead k current_frontier hsucc_tail
        simpa [localSectorRows, geometricSelection, selectedRows, localIsolation] using
          (selectedActualCarrierFaceSuccAngleRows C inputs)
            edgeRows htail hhead k current_frontier hsucc_tail)

set_option linter.style.longLine false in
/-- q48 family reducer from actual carrier local two-germ rows.

The existing equivalence between actual carrier degree two and selected
finite-drawing local isolation chooses the local-isolation rows; the remaining
premises are exactly the genuine geometric rotation rows and selected
actual-carrier face-successor angle rows for that chosen local source. -/
noncomputable def
    S2_q48_localGeometricProducerRows_family_of_localTwoGermRows_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
    (localTwoGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            Classical.choice
              ((nonempty_selectedUnboundedFrontierEdgeLocalIsolationSourceRows_iff_actualCarrierDegreeTwo
                (C := C) (inputs := inputs)).2
                (actualCarrierDegreeTwo_of_localTwoGermRows
                  (C := C) (inputs := inputs) (localTwoGermRows C inputs)))
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (localSectorRows a).left (localSectorRows a).right))
    (endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            Classical.choice
              ((nonempty_selectedUnboundedFrontierEdgeLocalIsolationSourceRows_iff_actualCarrierDegreeTwo
                (C := C) (inputs := inputs)).2
                (actualCarrierDegreeTwo_of_localTwoGermRows
                  (C := C) (inputs := inputs) (localTwoGermRows C inputs)))
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localIsolation :
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
            Classical.choice
              ((nonempty_selectedUnboundedFrontierEdgeLocalIsolationSourceRows_iff_actualCarrierDegreeTwo
                (C := C) (inputs := inputs)).2
                (actualCarrierDegreeTwo_of_localTwoGermRows
                  (C := C) (inputs := inputs) (localTwoGermRows C inputs)))
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) localIsolation
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q47_localGeometricProducerRows inputs := by
  let localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs := by
    intro m C inputs
    exact
      Classical.choice
        ((nonempty_selectedUnboundedFrontierEdgeLocalIsolationSourceRows_iff_actualCarrierDegreeTwo
          (C := C) (inputs := inputs)).2
          (actualCarrierDegreeTwo_of_localTwoGermRows
            (C := C) (inputs := inputs) (localTwoGermRows C inputs)))
  intro m C inputs
  exact
    S2_q48_localGeometricProducerRows_family_of_localIsolation_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
      localIsolation geometricRows endpointLocalRadiusCovers
      selectedActualCarrierFaceSuccAngleRows
      (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q51-route-compression-worker`.

Compose the checked q50 endpoint-radius reducer from `S2LocalTwoGermAssembly`
with the q49 selected local-geometric producer route.  The endpoint-radius
premise is lowered to same-selected-head endpoint rows plus selected-endpoint
radius containment; the remaining leaves stay on the selected local-isolation
heads, selected angular/no-between rows, and selected actual-carrier
`faceSucc` angle rows. -/
noncomputable def
    S2_q51_localGeometricProducerRows_family_of_selectedLocalIsolation_angularNoBetween_endpointSelectedHead_endpointRadiusContains_selectedActualCarrierFaceSuccAngles
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          S2_q18_selectedExteriorSectorAngularNoBetweenRows
            (C := C) (inputs := inputs) localSectorRows)
    (endpointSelectedHeadRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (endpointRadiusContains :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermSelectedEndpointLocalRadiusContainsAt localEndpointRows a)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let geometricRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                Nonempty
                  (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                    C a.1 (localSectorRows a).left (localSectorRows a).right) :=
            S2_q49_geometricRows_of_selectedLocalIsolation_angularNoBetweenRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
              (angularRows C inputs)
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) localSectorRows geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q47_localGeometricProducerRows inputs := by
  let endpointLocalRadiusCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localEndpointRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_r38_incidentGerm_endpoint_selectedHeadLocalRows_of_selectedIncidentEdgePairRows
              (C := C) (inputs := inputs) selectedRows
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localEndpointRows := by
    intro m C inputs
    exact
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_q50_endpointLocalRadiusCoversRows_family_of_selectedLocalIsolation_endpointSelectedHeadRows_endpointRadiusContains
        localIsolation endpointSelectedHeadRows endpointRadiusContains
        (C := C) (inputs := inputs)
  intro m C inputs
  exact
    S2_q49_localGeometricProducerRows_family_of_selectedLocalIsolation_angularNoBetween_endpointRadius_selectedActualCarrierFaceSuccAngles
      localIsolation angularRows endpointLocalRadiusCovers
      selectedActualCarrierFaceSuccAngleRows
      (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q52-local-angular-bypass-worker`, selected row pair.

If the selected incident-germ membership row is supplied directly, the q31
handoff does not need to manufacture it through a boundary-free local-angular
source.  The selected carrier successor row is projected from the actual
selected-carrier `faceSucc` angle rows, and the incident-germ row is carried
unchanged. -/
theorem
    S2_q52_selectedCarrierRows_and_incidentGermRows_of_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs)
    (incidentGermFrontierEdgeRows :
      SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs) geometricSelection)
    (selectedActualCarrierFaceSuccAngleRows :
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
        inputs selectedRows) :
    (let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
      inputs
      (selectedNeighborGeometricCarrierLeft
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource)
      (selectedNeighborGeometricCarrierRight
        (C := C) (inputs := inputs)
        selectedRows.toGeometricSelectionInputSource)) ∧
    SelectedNeighborIncidentGermFrontierEdgeMembershipRows
      (C := C) (inputs := inputs) geometricSelection := by
  constructor
  · let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    change
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
    exact
      rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource_of_selectedActualCarrierFaceSuccAngleRows_20260522q5
        (C := C) (inputs := inputs) selectedRows
        (by
          change
            RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
              inputs selectedRows at selectedActualCarrierFaceSuccAngleRows
          exact selectedActualCarrierFaceSuccAngleRows)
  · exact incidentGermFrontierEdgeRows

set_option linter.style.longLine false in
/-- Family form of the q52 selected carrier/incident-germ bypass pair. -/
theorem
    S2_q52_selectedCarrierRows_and_incidentGermRows_family_of_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs))
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        (let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) (geometricSelection C inputs)
        RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
          inputs
          (selectedNeighborGeometricCarrierLeft
            (C := C) (inputs := inputs)
            selectedRows.toGeometricSelectionInputSource)
          (selectedNeighborGeometricCarrierRight
            (C := C) (inputs := inputs)
            selectedRows.toGeometricSelectionInputSource)) ∧
        SelectedNeighborIncidentGermFrontierEdgeMembershipRows
          (C := C) (inputs := inputs) (geometricSelection C inputs) := by
  intro m C inputs
  exact
    S2_q52_selectedCarrierRows_and_incidentGermRows_of_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles
      (C := C) (inputs := inputs)
      (geometricSelection C inputs)
      (incidentGermFrontierEdgeRows C inputs)
      (selectedActualCarrierFaceSuccAngleRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q52-local-angular-bypass-worker`, selected raw rows.

This is the q47 selected-raw handoff with the local-angular/q46 endpoint
promotion removed.  The inputs are the same topology rows plus a direct
selected incident-germ membership source and selected actual-carrier
`faceSucc` angle rows. -/
noncomputable def
    S2_q52_selectedRawRows_of_traceNoClosed_outsideAccumulation_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs))
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    SelectedRawTailCoverageSourceRows inputs := by
  let frontier_noOpen :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
    (S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentPointsBetween_20260522
      (S2_q26_kComponentPointsBetween_of_traceNoClosedSeparation_20260522
        trace_noClosed)).1
  let frontier_noClosed :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
    (S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentPointsBetween_20260522
      (S2_q26_kComponentPointsBetween_of_traceNoClosedSeparation_20260522
        trace_noClosed)).2
  let frontier_vertex_incident :
      forall {m : Nat} (D : _root_.UDConfig m)
        (Dinputs : FinitePlanarOuterComponentInputs D),
          FrontierVertexIncidentUnboundedFrontierEdgeSource D Dinputs :=
    S2_q37_selected_frontier_incidence_worker_of_finiteDrawingPreconnected_outsideAccumulation_20260522
      (finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
        frontier_noClosed)
      outside_accumulation
  let pair :=
    S2_q52_selectedCarrierRows_and_incidentGermRows_of_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles
      (C := C) (inputs := inputs)
      (geometricSelection C inputs)
      (incidentGermFrontierEdgeRows C inputs)
      (selectedActualCarrierFaceSuccAngleRows C inputs)
  exact
    S2_r17_selectedRawTailCoverageSourceRows_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows
      (C := C) (inputs := inputs)
      frontier_noOpen (frontier_vertex_incident C inputs)
      (geometricSelection C inputs)
      pair.2 pair.1

set_option linter.style.longLine false in
/-- Claim `S2-q57-local-geometric-source-worker`.

Source-facing q57 worker below the direct actual-sector composer.  The
selected geometric carrier source is built from actual unbounded-frontier
local-sector rows and pointwise geometric carrier rows; the strict-successor
and raw `faceSucc` turn leaves are built from the selected actual-carrier
`faceSucc` angle rows plus the packaged start-edge local row for the exposed
q32 raw orbit. -/
noncomputable def
    S2_q57_local_geometric_source_worker
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
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
                  ((localSectorRows C inputs) a).right))
    (selectedActualCarrierFaceSuccAngleRows :
      let geometricSelection :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs := fun C inputs =>
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) (localSectorRows C inputs)
              (geometricRows C inputs)
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (startEdgeRows :
      let geometricSelection :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs := fun C inputs =>
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) (localSectorRows C inputs)
              (geometricRows C inputs)
      let strictSuccessorOrder :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) (geometricSelection C inputs)
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
        fun C inputs =>
          S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
            (C := C) (inputs := inputs) (geometricSelection C inputs)
            (selectedActualCarrierFaceSuccAngleRows C inputs)
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let pkg :=
            S2_q32_rawGeometricOrbitPackage_family_of_componentTopology_geometricSelection_strictSuccessor
              componentTopology geometricSelection strictSuccessorOrder C inputs
          PSigma fun p : PlanarInterface.Point =>
            UnboundedExteriorFrontierEdgeLocalRows C inputs
              ((pkg.2.2.1.tail, pkg.2.2.1.head) : PlanarInterface.Edge m) p)
    (arcRows :
      let geometricSelection :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs := fun C inputs =>
            S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
              (C := C) (inputs := inputs) (localSectorRows C inputs)
              (geometricRows C inputs)
      let strictSuccessorOrder :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) (geometricSelection C inputs)
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
        fun C inputs =>
          S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
            (C := C) (inputs := inputs) (geometricSelection C inputs)
            (selectedActualCarrierFaceSuccAngleRows C inputs)
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let pkg :=
            S2_q32_rawGeometricOrbitPackage_family_of_componentTopology_geometricSelection_strictSuccessor
              componentTopology geometricSelection strictSuccessorOrder C inputs
          forall {i j : Fin pkg.2.2.2.1.period},
            i ≠ j ->
            (pkg.2.2.2.1.dart i).tail =
              (pkg.2.2.2.1.dart j).tail ->
              RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
                (inputs := inputs) pkg.2.2.2.1 i j) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs := fun C inputs =>
        S2_q15_geometricSelectionInputSource_of_localSectorRows_r36
          (C := C) (inputs := inputs) (localSectorRows C inputs)
          (geometricRows C inputs)
  let strictSuccessorOrder :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource) :=
    fun C inputs =>
      S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
        (C := C) (inputs := inputs) (geometricSelection C inputs)
        (selectedActualCarrierFaceSuccAngleRows C inputs)
  let faceSuccTurnRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let pkg :=
            S2_q32_rawGeometricOrbitPackage_family_of_componentTopology_geometricSelection_strictSuccessor
              componentTopology geometricSelection strictSuccessorOrder C inputs
          S2_q32RawGeometricOrbitPackageFaceSuccTurnRows
            (inputs := inputs) pkg.2.2.2.1 :=
    S2_q36_q32RawGeometricOrbitPackageFaceSuccTurnRows_family_of_componentTopology_geometricSelection_strictSuccessor_selectedActualCarrierFaceSuccAngles_startEdgeLocalRows
      componentTopology geometricSelection strictSuccessorOrder
      selectedActualCarrierFaceSuccAngleRows startEdgeRows
  intro m C inputs
  exact
    S2_q33_actualExteriorSectorInputSourceRows_family_of_componentTopology_geometricSelection_strictSuccessor_minimalSeparation_faceSuccTurn
      componentTopology geometricSelection strictSuccessorOrder
      (fun {m} C inputs =>
        let pkg :=
          S2_q32_rawGeometricOrbitPackage_family_of_componentTopology_geometricSelection_strictSuccessor
            componentTopology geometricSelection strictSuccessorOrder C inputs
        (S2CarrierCutSource.S2_q49_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource_of_repeatedTailActualExteriorArcRows
          (C := C) (inputs := inputs) (O := pkg.2.2.2.1)
          (arcRows C inputs)).rows)
      faceSuccTurnRows
      (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- q61 carrier-facing selected geometric source family.

This is the r14 selected-geometric premise lowered to actual carrier
neighbour-pair/cut rows plus genuine geometric rows at the selected heads. -/
noncomputable def
    S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs :=
  S2_q60_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
    cutRows geometricRows

set_option linter.style.longLine false in
/-- q61 carrier-facing incident-germ source family.

This is the r14 incident-germ premise lowered to the same actual carrier
neighbour-pair/cut rows and selected-head geometric rows as the q61 geometric
source.  The only remaining endpoint source is the pointwise selected-head row
for those selected heads; no actual-sector, W32, or completed boundary-cycle
premise is introduced here. -/
theorem
    S2_q61_r14_incidentGermFrontierEdgeMembershipRows_family_of_cutPartitionInputSource_geometricRows_selectedHeadAt
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
            (C := C) (inputs := inputs) (cutRows C inputs)
            (geometricRows C inputs)
        SelectedNeighborIncidentGermFrontierEdgeMembershipRows
          (C := C) (inputs := inputs) geometricSelection :=
  S2_q61_incidentGermFrontierEdgeMembershipRows_family_of_cutPartitionInputSource_geometricRows_selectedHeadAt
    cutRows geometricRows selectedHeadAt

set_option linter.style.longLine false in
/-- q62 selected-head endpoint source lowering.

The q61/q62 selected-head leaf is only a selected-carrier rephrasing of the
selection-free endpoint frontier-edge membership row for the same q60
geometric selection.  This keeps the endpoint statement tied to actual
selected incident germs, not to all adjacent frontier endpoints. -/
theorem
    S2_q62_selectedHeadAt_family_of_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembershipRows
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          IncidentGermEndpointFrontierEdgeMembershipRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
            (C := C) (inputs := inputs) (cutRows C inputs)
            (geometricRows C inputs)
        let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
          S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          IncidentGermEndpointSelectedHeadAt
            (C := C) (inputs := inputs) selectedRows a := by
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
    S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
      cutRows geometricRows
  intro m C inputs
  exact
    incidentGermEndpointSelectedHeadAt_family_of_geometricSelection_endpointFrontierEdgeMembershipRows_20260522q15
      geometricSelection endpointRows (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- q62 carrier-facing selected actual-carrier `faceSucc` angle source.

This is the q7 selected-carrier angle reducer tied to the q61/q60 carrier
cut-partition geometric selection.  The remaining source leaf is the selected
carrier successor row on those q60-selected heads; no actual-sector, W32, or
completed boundary-cycle row is used. -/
theorem
    S2_q62_r14_selectedActualCarrierFaceSuccAngleRows_of_cutPartitionInputSource_geometricRows_selectedCarrierRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (cutRows :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs :=
        S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
          (C := C) (inputs := inputs) cutRows
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        Nonempty
          (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right))
    (selectedCarrierRows :
      let geometricSelection :
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
        S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
          (C := C) (inputs := inputs) cutRows geometricRows
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)) :
    let geometricSelection :
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs :=
      S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
        (C := C) (inputs := inputs) cutRows geometricRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
      inputs selectedRows := by
  let geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
      (C := C) (inputs := inputs) cutRows geometricRows
  change
    RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
      inputs
      (selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection)
  exact
    S2_agent_q7_selected_actual_carrier_faceSucc_angle_source_of_geometricSelection_selectedCarrierRows_20260522q7
      (C := C) (inputs := inputs) geometricSelection
      (by
        refine fun {e} {p} {start} edgeRows htail hhead m current_frontier hsucc_tail => ?_
        simpa [geometricSelection] using
          selectedCarrierRows edgeRows htail hhead m current_frontier
            hsucc_tail)

set_option linter.style.longLine false in
/-- Family form of the q62 q61-route selected actual-carrier `faceSucc`
angle lowering. -/
theorem
    S2_q62_r14_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_geometricRows_selectedCarrierRows
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
            (C := C) (inputs := inputs) (cutRows C inputs)
            (geometricRows C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
          inputs selectedRows := by
  intro m C inputs
  exact
    S2_q62_r14_selectedActualCarrierFaceSuccAngleRows_of_cutPartitionInputSource_geometricRows_selectedCarrierRows
      (C := C) (inputs := inputs) (cutRows C inputs)
      (geometricRows C inputs) (selectedCarrierRows C inputs)

set_option linter.style.longLine false in
/-- q62 selected raw orbit rows for the q61 seed-visible route.

This is the shared selected raw orbit used by the q62 source-facing
compression. It is built from the same component topology, q60/q61 geometric
selection, q61 incident-germ rows, and q62 selected-carrier angle rows, so the
remaining minimal-deleted-tail source can be stated against this concrete
orbit instead of restating the long `let` tower at every use. -/
noncomputable def
    S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    SelectedRawTailCoverageSourceRows inputs := by
  let geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
      cutRows geometricRows C inputs
  let incidentGermFrontierEdgeRows :
      SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs) geometricSelection :=
    S2_q61_r14_incidentGermFrontierEdgeMembershipRows_family_of_cutPartitionInputSource_geometricRows_selectedHeadAt
      cutRows geometricRows selectedHeadAt C inputs
  let angleRows :
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) geometricSelection
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
        inputs selectedRows :=
    S2_q62_r14_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_geometricRows_selectedCarrierRows
      cutRows geometricRows selectedCarrierRows C inputs
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs :=
    selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) geometricSelection
  let successorTailRows :
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource) :=
    S2_agent_raw_successor_tail_source_20260521k14
      (C := C) (inputs := inputs) selectedRows
      (S2_agent_raw_orbit_selectedCarrier_successorTail_source_20260521k15
        (C := C) (inputs := inputs) selectedRows
        (S2_k6k_faceSucc_tail_faceSucc_rows_source_of_selectedActualCarrierFaceSuccAngleRows
          (C := C) (inputs := inputs) selectedRows angleRows))
  exact
    selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_successorTailRows_20260521r13
      (C := C) (inputs := inputs)
      (componentTopology C inputs) geometricSelection
      incidentGermFrontierEdgeRows
      (rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_eta
        successorTailRows)

set_option linter.style.longLine false in
/-- q62 source-facing actual-sector compression.

This composes the q61 seed-visible actual-sector route with the q60/q61
carrier-geometric and q62 selected-carrier angle lowerings. The exposed source
leaves are now component topology, actual carrier cut rows, geometric
selected-head rows, selected-head endpoint rows, selected carrier successor
rows, and minimal deleted-tail separation for the concrete q62 raw orbit. -/
noncomputable def
    S2_q62_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_minimalDeletedTailSeparation
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
              componentTopology cutRows geometricRows selectedHeadAt
              selectedCarrierRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
    S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
      cutRows geometricRows
  let incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs) :=
    S2_q61_r14_incidentGermFrontierEdgeMembershipRows_family_of_cutPartitionInputSource_geometricRows_selectedHeadAt
      cutRows geometricRows selectedHeadAt
  let angleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows :=
    S2_q62_r14_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_geometricRows_selectedCarrierRows
      cutRows geometricRows selectedCarrierRows
  let minimalSeparation' :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let successorTailRows :
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_agent_raw_successor_tail_source_20260521k14
              (C := C) (inputs := inputs) selectedRows
              (S2_agent_raw_orbit_selectedCarrier_successorTail_source_20260521k15
                (C := C) (inputs := inputs) selectedRows
                (S2_k6k_faceSucc_tail_faceSucc_rows_source_of_selectedActualCarrierFaceSuccAngleRows
                  (C := C) (inputs := inputs) selectedRows
                  (angleRows C inputs)))
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_successorTailRows_20260521r13
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              (rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_eta
                successorTailRows);
          SelectedRawOrbitMinimalDeletedTailSeparation selectedRawRows := by
    intro m C inputs
    change
      SelectedRawOrbitMinimalDeletedTailSeparation
        (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
          componentTopology cutRows geometricRows selectedHeadAt
          selectedCarrierRows (C := C) inputs)
    exact minimalSeparation C inputs
  intro m C inputs
  exact
    ExteriorComponentTopology.S2_q61_actualExteriorSectorInputSourceRows_family_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_minimalDeletedTailSeparation
      componentTopology geometricSelection incidentGermFrontierEdgeRows
      angleRows minimalSeparation' (m := m) C inputs

set_option linter.style.longLine false in
/-- q62 source-facing actual-sector compression, cyclic-successor
nonreachability form.

This is the same q62 selected raw orbit as
`S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows`,
with the repeated-tail leaf lowered from minimal deleted-tail separation to
canonical cyclic-successor deleted-tail nonreachability. -/
noncomputable def
    S2_q62_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_cyclicSuccDeletedTailNonreachability
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (cyclicSuccNonreachability :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
            (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
              componentTopology cutRows geometricRows selectedHeadAt
              selectedCarrierRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) :=
  S2_q62_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_minimalDeletedTailSeparation
    componentTopology cutRows geometricRows selectedHeadAt selectedCarrierRows
    (fun {m} C inputs =>
      selectedRawOrbitMinimalDeletedTailSeparation_of_cyclicSuccDeletedTailNonreachability_20260521r8c
        (C := C) (inputs := inputs)
        (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
          componentTopology cutRows geometricRows selectedHeadAt
          selectedCarrierRows (C := C) inputs)
        (cyclicSuccNonreachability (m := m) C inputs))

set_option linter.style.longLine false in
/-- q62 selected raw orbit cyclic-successor nonreachability, finite
no-closed plus endpoint-closed form.

This lowers the remaining q62 deleted-tail source for the concrete selected
raw orbit, rather than wrapping the final actual-sector target. Endpoint-side
closed separation is first erased to the frontier-closed source, and finite
no-closed-separation rules out the reachable deleted-tail path. -/
noncomputable def
    S2_q62_cyclicSuccDeletedTailNonreachability_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_finiteNoClosed_endpointClosedSeparation
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (endpointClosedSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitCyclicSuccDeletedTailReachableEndpointClosedSeparationSource
            (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
              componentTopology cutRows geometricRows selectedHeadAt
              selectedCarrierRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
          (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
            componentTopology cutRows geometricRows selectedHeadAt
            selectedCarrierRows (C := C) inputs) := by
  intro m C inputs
  let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
    S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
      componentTopology cutRows geometricRows selectedHeadAt
      selectedCarrierRows (C := C) inputs
  change SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource selectedRawRows
  exact
    selectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource_of_reachableFrontierClosedSeparation_finiteDrawingNoClosedSeparation_20260521r8c
      (C := C) (inputs := inputs) selectedRawRows frontier_noClosedSeparation
      (S2_q39_selectedRawOrbitReachableFrontierClosedSeparationSource_of_endpointClosedSeparation
        (C := C) (inputs := inputs) selectedRawRows
        (endpointClosedSeparation (m := m) C inputs))

set_option linter.style.longLine false in
/-- q63 selected raw orbit with the q62 selected-carrier successor leaf
lowered to selected actual-carrier `faceSucc` angle rows.

This keeps the carrier cut rows, selected-head geometric rows, and
selected-head endpoint rows on the same q60/q61 selected heads, but it no
longer asks for
`RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource`.
The selected raw orbit is the same q61/r13 construction, sourced from the
already projected selected actual-carrier `faceSucc` angle rows. -/
noncomputable abbrev
    S2_q63_selectedRawTailCoverageSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        SelectedRawTailCoverageSourceRows inputs := by
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
    S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
      cutRows geometricRows
  let incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs) :=
    S2_q61_r14_incidentGermFrontierEdgeMembershipRows_family_of_cutPartitionInputSource_geometricRows_selectedHeadAt
      cutRows geometricRows selectedHeadAt
  intro m C inputs
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs :=
    selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) (geometricSelection C inputs)
  let successorTailRows :
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource) :=
    S2_agent_raw_successor_tail_source_20260521k14
      (C := C) (inputs := inputs) selectedRows
      (S2_agent_raw_orbit_selectedCarrier_successorTail_source_20260521k15
        (C := C) (inputs := inputs) selectedRows
        (S2_k6k_faceSucc_tail_faceSucc_rows_source_of_selectedActualCarrierFaceSuccAngleRows
          (C := C) (inputs := inputs) selectedRows
          (selectedActualCarrierFaceSuccAngleRows C inputs)))
  exact
    selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_successorTailRows_20260521r13
      (C := C) (inputs := inputs)
      (componentTopology C inputs) (geometricSelection C inputs)
      (incidentGermFrontierEdgeRows C inputs)
      (rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_eta
        successorTailRows)

set_option linter.style.longLine false in
/-- Claim `S2-q63-carrier-cut-geometric-source-worker`.

This lowers the q62 selected-carrier successor source leaf to the selected
actual-carrier `faceSucc` angle source already consumed by the q61
actual-sector producer.  The q60 carrier cut/geometric selection and q61
selected-head endpoint adapters are reused unchanged, and the repeated-tail
minimal-separation leaf is stated against the concrete q63 selected raw orbit
above. -/
noncomputable def
    S2_q63_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_minimalDeletedTailSeparation
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q63_selectedRawTailCoverageSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles
              componentTopology cutRows geometricRows selectedHeadAt
              selectedActualCarrierFaceSuccAngleRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
    S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
      cutRows geometricRows
  let incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs) :=
    S2_q61_r14_incidentGermFrontierEdgeMembershipRows_family_of_cutPartitionInputSource_geometricRows_selectedHeadAt
      cutRows geometricRows selectedHeadAt
  let minimalSeparation' :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let successorTailRows :
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_agent_raw_successor_tail_source_20260521k14
              (C := C) (inputs := inputs) selectedRows
              (S2_agent_raw_orbit_selectedCarrier_successorTail_source_20260521k15
                (C := C) (inputs := inputs) selectedRows
                (S2_k6k_faceSucc_tail_faceSucc_rows_source_of_selectedActualCarrierFaceSuccAngleRows
                  (C := C) (inputs := inputs) selectedRows
                  (selectedActualCarrierFaceSuccAngleRows C inputs)))
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_successorTailRows_20260521r13
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              (rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_eta
                successorTailRows);
          SelectedRawOrbitMinimalDeletedTailSeparation selectedRawRows := by
    intro m C inputs
    change
      SelectedRawOrbitMinimalDeletedTailSeparation
        (S2_q63_selectedRawTailCoverageSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles
          componentTopology cutRows geometricRows selectedHeadAt
          selectedActualCarrierFaceSuccAngleRows (C := C) inputs)
    exact minimalSeparation (m := m) C inputs
  exact
    fun {m} C inputs =>
    S2_q61_actualExteriorSectorInputSourceRows_family_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_minimalDeletedTailSeparation
      componentTopology geometricSelection incidentGermFrontierEdgeRows
      selectedActualCarrierFaceSuccAngleRows minimalSeparation' (m := m) C inputs


set_option linter.style.longLine false in
/-- q65 source-facing actual-sector route with topology and repeated-tail
leaves lowered one step.

The finite topology rows come from the same nontrivial relative-clopen `K`-side
plus punctured-accumulation package.  The deleted-tail row is sourced from
primitive repeated-tail rows on the exact q63 selected raw orbit via the
selected endpoint-closed adapter and finite no-closed contradiction. -/
noncomputable def
    S2_q65_actualExteriorSectorInputSourceRows_family_of_nontrivialRelativeClopen_puncturedAccumulation_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_primitiveSourceRows
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (punctured :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (primitiveSourceRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitRepeatedTailPrimitiveSourceRows
            (S2_q63_selectedRawTailCoverageSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles
              (S2_q62_traceNoClosed_componentTopologyInputSourceRows_family_of_nontrivialRelativeClopen_puncturedAccumulation_20260522q62
                nontrivial_side punctured).2
              cutRows geometricRows selectedHeadAt
              selectedActualCarrierFaceSuccAngleRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
    (S2_q62_traceNoClosed_componentTopologyInputSourceRows_family_of_nontrivialRelativeClopen_puncturedAccumulation_20260522q62
      nontrivial_side punctured).2
  let frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
    S2_q65_finiteDrawing_noClosedSeparation_source_of_nontrivialRelativeClopen_puncturedAccumulation_20260522q65
      nontrivial_side punctured
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
    S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
      cutRows geometricRows
  let incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs) :=
    S2_q61_r14_incidentGermFrontierEdgeMembershipRows_family_of_cutPartitionInputSource_geometricRows_selectedHeadAt
      cutRows geometricRows selectedHeadAt
  let minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q63_selectedRawTailCoverageSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles
              componentTopology cutRows geometricRows selectedHeadAt
              selectedActualCarrierFaceSuccAngleRows (C := C) inputs) := by
    intro m C inputs
    exact
      selectedRawOrbitMinimalDeletedTailSeparation_of_primitiveSourceRows_20260521r7g
        (C := C) (inputs := inputs)
        (S2_q63_selectedRawTailCoverageSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles
          componentTopology cutRows geometricRows selectedHeadAt
          selectedActualCarrierFaceSuccAngleRows (C := C) inputs)
        (primitiveSourceRows (m := m) C inputs)
  intro m C inputs
  exact
    S2_q63_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_minimalDeletedTailSeparation
      componentTopology cutRows geometricRows selectedHeadAt
      selectedActualCarrierFaceSuccAngleRows minimalSeparation (m := m) C inputs

/-
Stale q72 source-integrator attempt from a closed worker.
The existing checked q72 composer above is the live route; this blocked variant
is intentionally disabled rather than used as a source claim.

set_option linter.style.longLine false in
/-- Claim `S2-q66-selected-head-geometric-source-worker`, geometric leaf.

For the q65/q60 selected carrier heads, honest same-head angular no-between
rows are enough to rebuild the requested
`GraphVertexGeometricAngularNeighborSelectionRow`s.  The selected heads still
come from the actual carrier cut rows; no global outgoing-list no-between row,
identity angular order, W32 row, or completed boundary cycle is introduced. -/
theorem
    S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
            (C := C) (inputs := inputs) (cutRows C inputs)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          Nonempty
            (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right) := by
  intro m C inputs
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
        inputs :=
    S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
      (C := C) (inputs := inputs) (cutRows C inputs)
  change forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
      Nonempty
        (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
          C a.1 (selectedRows.selectedNeighborRows a).left
            (selectedRows.selectedNeighborRows a).right)
  exact
    (S2_q35_selectedNeighborGeometricOrderRows_of_selectedCutPartition_angularNoBetweenRows
      (C := C) (inputs := inputs) (selectedRows := selectedRows)
      (by
        intro a
        simpa [selectedRows] using angularRows C inputs a)).geometricOrderRows

set_option linter.style.longLine false in
/-- Claim `S2-q66-selected-head-geometric-source-worker`, endpoint leaf.

The q65 pointwise endpoint-selected-head premise is just the pointwise form of
the selected-head endpoint rows for the same q60 selected carrier heads. -/
theorem
    S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let geometricRows :=
          S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
            cutRows angularRows (C := C) inputs
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
            (C := C) (inputs := inputs) (cutRows C inputs)
            geometricRows
        let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
          S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          IncidentGermEndpointSelectedHeadAt
            (C := C) (inputs := inputs) selectedRows a := by
  intro m C inputs
  let geometricRows :=
    S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
      cutRows angularRows (C := C) inputs
  let geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
      (C := C) (inputs := inputs) (cutRows C inputs)
      geometricRows
  let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
    S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) geometricSelection
  have endpointRowsHere :
      IncidentGermEndpointSelectedHeadRows selectedRows := by
    simpa [geometricRows, geometricSelection, selectedRows] using
      endpointRows C inputs
  change
    forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
      IncidentGermEndpointSelectedHeadAt
        (C := C) (inputs := inputs) selectedRows a
  intro a eps x hxball hxfrontier hadj hxgerm hxne
  exact endpointRowsHere a eps x hxball hxfrontier hadj hxgerm hxne

set_option linter.style.longLine false in
/-- Claim `S2-q66-selected-head-geometric-source-worker`, selected
actual-carrier `faceSucc` angle leaf.

The q65 selected actual-carrier angle rows are rebuilt from the selected
carrier successor rows on the same q60 selected heads, after the geometric
leaf has been lowered to same-head angular no-between rows. -/
theorem
    S2_q66_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_selectedCarrierRows
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let geometricRows :=
          S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
            cutRows angularRows (C := C) inputs
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
            (C := C) (inputs := inputs) (cutRows C inputs)
            geometricRows
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
          inputs selectedRows :=
  S2_q62_r14_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_geometricRows_selectedCarrierRows
    cutRows
    (S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
      cutRows angularRows)
    selectedCarrierRows

set_option linter.style.longLine false in
/-- Claim `S2-q69-q64-source-bundle-compression-worker`, direct primitive
bundle form.

The q64 actual exterior-walk primitive bundle is just the shared q62 source
surface packaged before any actual-sector eraser is used.  The minimal
deleted-tail separation row is stated on the selected raw orbit assembled from
these same component, cut, geometric, endpoint, and selected-carrier rows. -/
noncomputable def
    S2_q69_actualExteriorWalkPrimitiveSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_minimalSeparation
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology := componentTopology (m := m) C inputs)
              (cutRows := cutRows (m := m) C inputs)
              (geometricRows := geometricRows (C := C) (inputs := inputs))
              (selectedHeadAt := selectedHeadAt (C := C) (inputs := inputs))
              (selectedCarrierRows := selectedCarrierRows (m := m) C inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q64ActualExteriorWalkPrimitiveSourceRows inputs := by
  intro m C inputs
  refine
    { componentTopology := componentTopology C inputs
      cutRows := cutRows C inputs
      geometricRows := geometricRows C inputs
      selectedHeadAt := selectedHeadAt C inputs
      selectedCarrierRows := selectedCarrierRows C inputs
      minimalSeparation := ?_ }
  exact minimalSeparation (m := m) C inputs

set_option linter.style.longLine false in
/-- Claim `S2-q69-q64-source-bundle-compression-worker`, selected-angular
form.

This is the q66-lowered q64 bundle surface: selected same-head angular
no-between rows produce the selected-head geometric rows, endpoint-selected
head rows produce `selectedHeadAt`, and selected-carrier successor rows are
kept as the q64 carrier field. -/
noncomputable def
    S2_q69_actualExteriorWalkPrimitiveSourceRows_family_of_componentTopology_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedCarrierRows_minimalSeparation
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
              componentTopology cutRows
              (S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
                cutRows angularRows)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows)
              selectedCarrierRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q64ActualExteriorWalkPrimitiveSourceRows inputs := by
  intro m C inputs
  let geometricRows :=
    S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
      cutRows angularRows (C := C) inputs
  let selectedHeadAt :=
    S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
      cutRows angularRows endpointRows (C := C) inputs
  let geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
      (C := C) (inputs := inputs) (cutRows C inputs) geometricRows
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs :=
    selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) geometricSelection
  let selectedCarrierRowsHere :
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs)
          selectedRows.toGeometricSelectionInputSource) := by
    refine fun {e} {p} {start} edgeRows htail hhead step current_frontier hsucc_tail => ?_
    simpa [geometricSelection, selectedRows] using
      selectedCarrierRows (m := m) (C := C) inputs edgeRows htail hhead step
        current_frontier hsucc_tail
  refine
    { componentTopology := componentTopology C inputs
      cutRows := cutRows C inputs
      geometricRows := geometricRows
      selectedHeadAt := selectedHeadAt
      selectedCarrierRows := selectedCarrierRowsHere
      minimalSeparation := ?_ }
  change
    SelectedRawOrbitMinimalDeletedTailSeparation
      (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
        componentTopology cutRows
        (S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
          cutRows angularRows)
        (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
          cutRows angularRows endpointRows)
        selectedCarrierRows (C := C) inputs)
  exact minimalSeparation (m := m) (C := C) (inputs := inputs)

/- The selected-angular q64/q70 wrappers below still need a dependent-`let`
normalization pass for the selected-carrier row.  Keep the checked direct q64
packer above live; do not expose these experimental wrappers as active
declarations until that coercion is settled. -/
/-

/- The q69 q67-bundle compression attempt below used a binder variant of the
selected actual-carrier angle row that is not definitionally the q67 bundle
field.  The checked q68 q64-to-q67 compression lives in
`S2SeededRawOrbitSource`; this owner file keeps only the q69 actual-sector
eraser below. -/
/-
set_option linter.style.longLine false in
/-- Claim `S2-q69-q67-bundle-source-compression-worker`, primitive
repeated-tail form.

The current q66 leaves already assemble the q67 actual face-walk source bundle:
component topology, actual carrier cut rows, selected-head geometric rows,
selected-head endpoint rows, selected actual-carrier `faceSucc` angle rows, and
primitive repeated-tail rows on that same selected raw orbit. -/
noncomputable def
    S2_q69_q67ActualFaceWalkSourceBundleRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_primitiveSourceRows
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (primitiveSourceRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitRepeatedTailPrimitiveSourceRows
            (S2_q67_actualFaceWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (cutRows C inputs)
              (geometricRows C inputs)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows (m := m) (C := C) inputs)
              (selectedActualCarrierFaceSuccAngleRows (m := m) (C := C) inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q67ActualFaceWalkSourceBundleRows inputs := by
  intro m C inputs
  let geometricSelection :
      UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs :=
    S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
      (C := C) (inputs := inputs) (cutRows C inputs) (geometricRows C inputs)
  let selectedRows :
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
        inputs :=
    selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
      (C := C) (inputs := inputs) geometricSelection
  have angleRowsHere :
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
        inputs selectedRows := by
    change
      RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
        inputs selectedRows
    exact selectedActualCarrierFaceSuccAngleRows (m := m) (C := C) (inputs := inputs)
  refine
    { componentTopology := componentTopology C inputs
      cutRows := cutRows C inputs
      geometricRows := geometricRows C inputs
      selectedHeadAt := selectedHeadAt C inputs
      angleRows := by
        change
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows
        exact angleRowsHere
      primitiveRepeatedTailRows := ?_ }
  exact primitiveSourceRows (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q69-q67-bundle-source-compression-worker`, pairwise-minimal
repeated-tail form.

The repeated-tail leaf may also be supplied as the q38 pairwise minimal
deleted-tail separation source for the selected q67 raw face walk; the existing
finite-graph eraser lowers it to primitive repeated-tail rows before the bundle
is assembled. -/
noncomputable def
    S2_q69_q67ActualFaceWalkSourceBundleRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_pairwiseMinimalDeletedTailSeparation
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (pairwiseMinimal :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
            (S2_q67_actualFaceWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (cutRows C inputs)
              (geometricRows C inputs)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows (m := m) (C := C) inputs)
              (selectedActualCarrierFaceSuccAngleRows (m := m) (C := C) inputs)).O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q67ActualFaceWalkSourceBundleRows inputs := by
  refine
    S2_q69_q67ActualFaceWalkSourceBundleRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_primitiveSourceRows
      componentTopology cutRows geometricRows selectedHeadAt
      selectedActualCarrierFaceSuccAngleRows ?_
  intro m C inputs
  let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
    S2_q67_actualFaceWalkSelectedRawTailCoverageSourceRows
      (C := C) (inputs := inputs)
      (componentTopology C inputs) (cutRows C inputs)
      (geometricRows C inputs) (selectedHeadAt C inputs)
      (selectedActualCarrierFaceSuccAngleRows (m := m) C inputs)
  change SelectedRawOrbitRepeatedTailPrimitiveSourceRows selectedRawRows
  exact
    selectedRawOrbitRepeatedTailPrimitiveSourceRows_of_repeatedTailExteriorCutRows_20260521r55
      (C := C) (inputs := inputs) selectedRawRows
      (S2CarrierCutSource.S2_q38_repeatedTailExteriorCutRows_of_pairwiseMinimalDeletedTailSeparationSource
        (C := C) (inputs := inputs) (pairwiseMinimal (C := C) (inputs := inputs)))

/-!
Selected-angular q69 wrappers are intentionally not exposed here: the checked
q66 erasers below already lower selected-angular rows to `geometricRows`,
`selectedHeadAt`, and selected actual-carrier angle rows.  The q69 source
composer is kept at that stricter post-erasure surface.
-/
/-
set_option linter.style.longLine false in
/-- Claim `S2-q69-q67-bundle-source-compression-worker`, selected-angular
primitive form.

This is the q66 source-leaf surface: selected same-head angular no-between rows
produce the geometric rows, endpoint rows produce `selectedHeadAt`, selected
carrier successor rows produce selected actual-carrier `faceSucc` angle rows,
and primitive repeated-tail rows fill the q67 bundle. -/
noncomputable def
    S2_q69_q67ActualFaceWalkSourceBundleRows_family_of_componentTopology_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedCarrierRows_primitiveSourceRows
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (primitiveSourceRows :
      let geometricRows :=
        S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
          cutRows angularRows
      let selectedHeadAt :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricRowsHere :=
                S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
                  cutRows angularRows (C := C) inputs
              let geometricSelection :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  geometricRowsHere
              let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
                S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelection
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                IncidentGermEndpointSelectedHeadAt
                  (C := C) (inputs := inputs) selectedRows a :=
        S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
          cutRows angularRows endpointRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitRepeatedTailPrimitiveSourceRows
            (S2_q67_actualFaceWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (cutRows C inputs)
              (geometricRows C inputs)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows (m := m) (C := C) inputs)
              (S2_q66_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_selectedCarrierRows
                cutRows angularRows selectedCarrierRows (m := m) (C := C)
                inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q67ActualFaceWalkSourceBundleRows inputs := by
  let geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right) :=
    S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
      cutRows angularRows
  let selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a :=
    S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
      cutRows angularRows endpointRows
  let selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows := by
    intro m C inputs
    simpa [geometricRows] using
      S2_q66_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_selectedCarrierRows
        cutRows angularRows selectedCarrierRows (m := m) C inputs
  exact
    S2_q69_q67ActualFaceWalkSourceBundleRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_primitiveSourceRows
      componentTopology cutRows geometricRows selectedHeadAt
      selectedActualCarrierFaceSuccAngleRows
      (by
        intro m C inputs
        simpa [geometricRows, selectedHeadAt, selectedActualCarrierFaceSuccAngleRows] using
          primitiveSourceRows (m := m) C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q69-q67-bundle-source-compression-worker`, selected-angular
pairwise-minimal form.

This is the pairwise-minimal version of the q66 source-leaf composer. -/
noncomputable def
    S2_q69_q67ActualFaceWalkSourceBundleRows_family_of_componentTopology_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedCarrierRows_pairwiseMinimalDeletedTailSeparation
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (pairwiseMinimal :
      let geometricRows :=
        S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
          cutRows angularRows
      let selectedHeadAt :=
        fun {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C) =>
            S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
              cutRows angularRows endpointRows (m := m) (C := C) inputs
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
            (S2_q67_actualFaceWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (cutRows C inputs)
              (geometricRows C inputs)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows (m := m) (C := C) inputs)
              (S2_q66_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_selectedCarrierRows
                cutRows angularRows selectedCarrierRows (m := m) (C := C)
                inputs)).O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q67ActualFaceWalkSourceBundleRows inputs := by
  let geometricRows :=
    S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
      cutRows angularRows
  let selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRowsHere :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRowsHere
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a :=
    S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
      cutRows angularRows endpointRows
  let selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows := by
    intro m C inputs
    simpa [geometricRows] using
      S2_q66_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_selectedCarrierRows
        cutRows angularRows selectedCarrierRows (m := m) C inputs
  exact
    S2_q69_q67ActualFaceWalkSourceBundleRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_pairwiseMinimalDeletedTailSeparation
      componentTopology cutRows geometricRows selectedHeadAt
      selectedActualCarrierFaceSuccAngleRows
      (by
        intro m C inputs
        simpa [geometricRows, selectedHeadAt, selectedActualCarrierFaceSuccAngleRows] using
          pairwiseMinimal (m := m) C inputs)

-/
set_option linter.style.longLine false in
/-- Claim `S2-q66-selected-head-geometric-source-worker`.

q65 with the selected-head geometric and endpoint leaves lowered to
source-level selected-carrier/local geometry primitives: selected same-head
angular no-between rows, selected-head endpoint rows, and selected carrier
successor rows.  The repeated-tail primitive row is still stated on the exact
q63 selected raw orbit assembled from these lowered leaves. -/
noncomputable def
    S2_q66_actualExteriorSectorInputSourceRows_family_of_nontrivialRelativeClopen_puncturedAccumulation_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedCarrierRows_primitiveSourceRows
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (punctured :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (primitiveSourceRows :
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        (S2_q62_traceNoClosed_componentTopologyInputSourceRows_family_of_nontrivialRelativeClopen_puncturedAccumulation_20260522q62
          nontrivial_side punctured).2
      let geometricRows :=
        S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
          cutRows angularRows
      let selectedHeadAt :=
        fun {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C) =>
            S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
              cutRows angularRows endpointRows (m := m) (C := C) inputs
      let selectedActualCarrierFaceSuccAngleRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricSelection :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  (geometricRows C inputs)
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelection
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
                inputs selectedRows := by
        intro m C inputs
        simpa [geometricRows] using
          S2_q66_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_selectedCarrierRows
            cutRows angularRows selectedCarrierRows (m := m) C inputs
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitRepeatedTailPrimitiveSourceRows
            (S2_q63_selectedRawTailCoverageSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles
              componentTopology cutRows geometricRows selectedHeadAt
              selectedActualCarrierFaceSuccAngleRows (m := m) (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
    (S2_q62_traceNoClosed_componentTopologyInputSourceRows_family_of_nontrivialRelativeClopen_puncturedAccumulation_20260522q62
      nontrivial_side punctured).2
  let geometricRows :=
    S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
      cutRows angularRows
  let selectedHeadAt :=
    fun {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C) =>
        S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
          cutRows angularRows endpointRows (m := m) (C := C) inputs
  let selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows := by
    intro m C inputs
    simpa [geometricRows] using
      S2_q66_selectedActualCarrierFaceSuccAngleRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_selectedCarrierRows
        cutRows angularRows selectedCarrierRows (m := m) C inputs
  exact
    S2_q65_actualExteriorSectorInputSourceRows_family_of_nontrivialRelativeClopen_puncturedAccumulation_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_primitiveSourceRows
      nontrivial_side punctured cutRows geometricRows selectedHeadAt
      (by
        intro m C inputs
        simpa [geometricRows, selectedActualCarrierFaceSuccAngleRows] using
          selectedActualCarrierFaceSuccAngleRows (m := m) (C := C) (inputs := inputs))
      (by
        intro m C inputs
        simpa [componentTopology, geometricRows, selectedHeadAt,
          selectedActualCarrierFaceSuccAngleRows] using
          primitiveSourceRows (m := m) C inputs)

-/
set_option linter.style.longLine false in
/-- Claim `S2-q69-q67-bundle-source-compression-worker`, q64 primitive form.

The q66 source leaves rebuild the q64 actual exterior-walk primitive bundle:
selected angular no-between rows lower to selected-head geometric rows,
endpoint rows lower to selected-head endpoint rows, and the selected-carrier
successor rows are kept on the same q64 selected raw orbit. -/
noncomputable def
    S2_q69_q64ActualExteriorWalkPrimitiveSourceRows_family_of_componentTopology_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedCarrierRows_minimalDeletedTailSeparation
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
              componentTopology cutRows
              (S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
                cutRows angularRows)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows)
              selectedCarrierRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        S2_q64ActualExteriorWalkPrimitiveSourceRows inputs :=
  S2_q69_actualExteriorWalkPrimitiveSourceRows_family_of_componentTopology_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedCarrierRows_minimalSeparation
    componentTopology cutRows angularRows endpointRows selectedCarrierRows
    minimalSeparation

set_option linter.style.longLine false in
/-- q69 family handoff from the selected-angular q64 primitive bridge to the
checked q68 face-dart/angular producer. -/
noncomputable def
    S2_q69_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_componentTopology_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedCarrierRows_minimalDeletedTailSeparation
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
              componentTopology cutRows
              (S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
                cutRows angularRows)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows)
              selectedCarrierRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        PSigma fun faceRows : FaceDartOrbitExteriorCarrierRows C inputs =>
          forall k : Fin faceRows.orbit.boundary.length,
            GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
              C faceRows.orbit.boundary k :=
  _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q68_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_q64ActualExteriorWalkPrimitiveSourceRows
    (S2_q69_q64ActualExteriorWalkPrimitiveSourceRows_family_of_componentTopology_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedCarrierRows_minimalDeletedTailSeparation
      componentTopology cutRows angularRows endpointRows selectedCarrierRows
      minimalSeparation)

/- The q70 pairwise repeated-tail face-dart route below uses a binder variant
of the selected actual-carrier angle rows that is not definitionally the q64
selected raw orbit surface after the q70 selected-carrier projection.  Keep the
checked q64/q69 erasers active and let q71 compose through the minimal
deleted-tail surface instead. -/
set_option linter.style.longLine false in
/-- Claim `S2-q70-route-integrator-main`, pairwise repeated-tail form.

This is the current q70 actual exterior face-orbit source surface.  The
selected-carrier successor rows are rebuilt from the selected actual-carrier
`faceSucc` angle rows, and the q38 pairwise repeated-tail cut source is erased
to the minimal deleted-tail separation row on that exact q64 selected raw
orbit. -/
noncomputable def
    S2_q70_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_componentTopology_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedActualCarrierFaceSuccAngles_pairwiseMinimalDeletedTailSeparation
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right)
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (pairwiseMinimal :
      let selectedCarrierRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricRows :=
                S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
                  cutRows angularRows (C := C) inputs
              let geometricSelection :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  geometricRows
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelection
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
        (fun {m} C inputs =>
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          have angleRowsHere :
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
                inputs selectedRows := by
            change
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
                inputs selectedRows
            exact
              selectedActualCarrierFaceSuccAngleRows
                (m := m) (C := C) (inputs := inputs)
          S2_q70_selectedCarrierRows_of_cutPartitionInputSource_geometricRows_selectedActualCarrierFaceSuccAngles
            (C := C) (inputs := inputs) (cutRows C inputs)
            geometricRows angleRowsHere
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2CarrierCutSource.S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
            (S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology := componentTopology (m := m) C inputs)
              (cutRows := cutRows (m := m) C inputs)
              (geometricRows :=
                S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
                  cutRows angularRows (m := m) (C := C) inputs)
              (selectedHeadAt :=
                S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                  cutRows angularRows endpointRows (m := m) (C := C) inputs)
              (selectedCarrierRows := selectedCarrierRows (m := m) (C := C) inputs)).O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        PSigma fun faceRows : FaceDartOrbitExteriorCarrierRows C inputs =>
          forall k : Fin faceRows.orbit.boundary.length,
            GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
              C faceRows.orbit.boundary k := by
  let selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource) := by
    intro m C inputs
    let geometricRows :=
      S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
        cutRows angularRows (C := C) inputs
    let geometricSelection :
        UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
          C inputs :=
      S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
        (C := C) (inputs := inputs) (cutRows C inputs)
        geometricRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
          inputs :=
      selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
        (C := C) (inputs := inputs) geometricSelection
    have angleRowsHere :
        RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
          inputs selectedRows := by
      change
        RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
          inputs selectedRows
      exact
        selectedActualCarrierFaceSuccAngleRows
          (m := m) (C := C) (inputs := inputs)
    exact
      S2_q70_selectedCarrierRows_of_cutPartitionInputSource_geometricRows_selectedActualCarrierFaceSuccAngles
        (C := C) (inputs := inputs) (cutRows C inputs) geometricRows
        angleRowsHere
  let minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology := componentTopology (m := m) C inputs)
              (cutRows := cutRows (m := m) C inputs)
              (geometricRows :=
                S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
                  cutRows angularRows (m := m) (C := C) inputs)
              (selectedHeadAt :=
                S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                  cutRows angularRows endpointRows (m := m) (C := C) inputs)
              (selectedCarrierRows := selectedCarrierRows (m := m) (C := C) inputs)) := by
    intro m C inputs
    let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
      S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
        (C := C) (inputs := inputs)
        (componentTopology := componentTopology (m := m) C inputs)
        (cutRows := cutRows (m := m) C inputs)
        (geometricRows :=
          S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
            cutRows angularRows (m := m) (C := C) inputs)
        (selectedHeadAt :=
          S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
            cutRows angularRows endpointRows (m := m) (C := C) inputs)
        (selectedCarrierRows := selectedCarrierRows (m := m) (C := C) inputs)
    change SelectedRawOrbitMinimalDeletedTailSeparation selectedRawRows
    exact
      selectedRawOrbitMinimalDeletedTailSeparation_of_repeatedTailExteriorCutRows_20260521k6
        (C := C) (inputs := inputs) selectedRawRows
        (S2CarrierCutSource.S2_q38_repeatedTailExteriorCutRows_of_pairwiseMinimalDeletedTailSeparationSource
          (C := C) (inputs := inputs)
          (pairwiseMinimal (m := m) (C := C) (inputs := inputs)))
  exact
    S2_q69_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_componentTopology_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedCarrierRows_minimalDeletedTailSeparation
      componentTopology cutRows angularRows endpointRows selectedCarrierRows
      minimalSeparation

-/

set_option linter.style.longLine false in
/-- Claim `S2-q64-actual-exterior-walk-primitive-worker`, q62 eraser.

The q64 primitive bundle jointly supplies every q62 residual for the same
selected raw orbit.  This theorem only projects those fields into the checked
q62 actual-sector route; it introduces no W32 row, completed boundary cycle,
induced frontier graph, arbitrary cycle, convex-hull order, global outgoing
no-between row, or all-adjacent endpoint shortcut. -/
noncomputable def
    S2_q64_actualExteriorSectorInputSourceRows_family_of_actualExteriorWalkPrimitiveSourceRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q64ActualExteriorWalkPrimitiveSourceRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  refine
    S2_q62_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_minimalDeletedTailSeparation
      (fun C inputs => (source C inputs).componentTopology)
      (fun C inputs => (source C inputs).cutRows)
      (fun C inputs => (source C inputs).geometricRows)
      (fun C inputs => (source C inputs).selectedHeadAt)
      (fun C inputs => (source C inputs).selectedCarrierRows)
      ?_
  intro m C inputs
  let rows : _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q64ActualExteriorWalkPrimitiveSourceRows inputs :=
    source C inputs
  change
    SelectedRawOrbitMinimalDeletedTailSeparation
      (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
        (C := C) (inputs := inputs)
        rows.componentTopology rows.cutRows rows.geometricRows
        rows.selectedHeadAt rows.selectedCarrierRows)
  exact rows.minimalSeparation

set_option linter.style.longLine false in
/-- Claim `S2-q69-actual-face-walk-bundle-eraser-worker`.

The q67 actual face-walk bundle is the current sharp local producer surface:
it owns the selected raw exterior walk, the actual carrier cut/geometric rows,
and primitive repeated-tail data on the same walk.  This eraser sends that
bundle through the checked face-dart exterior carrier producer and then through
the existing actual-sector eraser; it introduces no W32 row, facade, synthetic
enclosure, induced frontier graph, arbitrary cycle, or boundary-cycle premise. -/
noncomputable def
    S2_q69_actualExteriorSectorInputSourceRows_family_of_actualFaceWalkSourceBundleRows
    (source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q67ActualFaceWalkSourceBundleRows inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  intro m C inputs
  let producer :=
    S2_q67_actual_face_walk_source_bundle_worker
      (C := C) (inputs := inputs) (source C inputs)
  exact
    actualExteriorSectorInputSourceRows_of_faceDartOrbitExteriorCarrierRows
      (C := C) (inputs := inputs) producer.1 producer.2

set_option linter.style.longLine false in
/-- Claim `S2-q71-route-integrator-main`.

The q63 actual-sector source route with the component-topology leaf discharged
by the checked q70 finite-topology reducer.  The remaining visible leaves are
the genuine topology singleton obstruction, actual carrier cut rows,
selected-head geometric/endpoint rows, selected actual-carrier faceSucc angle
rows, and minimal deleted-tail separation on the same q63 selected raw orbit.
No W32 target, completed boundary cycle, synthetic enclosure, induced frontier
graph, arbitrary cycle, convex-hull shortcut, or all-adjacent endpoint premise
is used. -/
noncomputable def
    S2_q71_actualExteriorSectorInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_minimalDeletedTailSeparation
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (minimalSeparation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q63_selectedRawTailCoverageSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q70_componentTopologyInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_20260522q70
                no_crossing no_singleton_bumping)
              cutRows geometricRows selectedHeadAt
              selectedActualCarrierFaceSuccAngleRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) :=
  S2_q63_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_minimalDeletedTailSeparation
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q70_componentTopologyInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_20260522q70
      no_crossing no_singleton_bumping)
    cutRows geometricRows selectedHeadAt
    selectedActualCarrierFaceSuccAngleRows minimalSeparation

set_option linter.style.longLine false in
/-- Claim `S2-q72-route-integrator-main`.

The q70/q64 route with both the component-topology leaf and the
minimal-deleted-tail leaf discharged by their checked q70 reducers.  The
remaining local leaves are actual carrier cut rows, selected-head
geometric/endpoint rows, selected-carrier successor rows, and the
exterior-frontier arc separation rows for the same q64 selected raw orbit. -/
noncomputable def
    S2_q72_actualExteriorSectorInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_exteriorFrontierArcRows
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a)
    (selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (arcRows :
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q70_componentTopologyInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_20260522q70
          no_crossing no_singleton_bumping
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology (m := m) C inputs) (cutRows (m := m) C inputs)
              (geometricRows (m := m) C inputs)
              (selectedHeadAt C inputs)
              (selectedCarrierRows (m := m) C inputs)
          RawFaceSuccOrbitExteriorFrontierArcSeparationSourceRows
            (inputs := inputs) selectedRawRows.O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q70_componentTopologyInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_20260522q70
      no_crossing no_singleton_bumping
  let source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q64ActualExteriorWalkPrimitiveSourceRows inputs := by
    intro m C inputs
    let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
      S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
        (C := C) (inputs := inputs)
        (componentTopology C inputs) (cutRows C inputs)
        (geometricRows C inputs) (selectedHeadAt C inputs)
        (selectedCarrierRows C inputs)
    refine
      { componentTopology := componentTopology C inputs
        cutRows := cutRows C inputs
        geometricRows := geometricRows C inputs
        selectedHeadAt := selectedHeadAt C inputs
        selectedCarrierRows := selectedCarrierRows C inputs
        minimalSeparation := ?_ }
    change SelectedRawOrbitMinimalDeletedTailSeparation selectedRawRows
    exact
      selectedRawOrbitMinimalDeletedTailSeparation_of_repeatedTailSeparationRows_20260521k6f
        (C := C) (inputs := inputs) selectedRawRows
        (S2_agent_no_cut_repeated_tail_source_from_actualExteriorArcSeparation
          (C := C) (inputs := inputs) selectedRawRows.O
          (arcRows (m := m) (C := C) (inputs := inputs)))
  intro m C inputs
  exact
    S2_q64_actualExteriorSectorInputSourceRows_family_of_actualExteriorWalkPrimitiveSourceRows
      (fun {m} C inputs => source (m := m) C inputs)
      (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q72-selected-head-geometric-worker`, q71 form.

The q71 composer with the selected-head leaves lowered through the checked q66
erasers.  The selected heads are still exactly the heads chosen by the actual
carrier cut source: selected angular no-between rows produce the geometric
rows, and endpoint-selected-head rows produce `selectedHeadAt`. -/
noncomputable def
    S2_q72_q71_actualExteriorSectorInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedActualCarrierFaceSuccAngles_minimalDeletedTailSeparation
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q68_selectedAngularNoBetweenRows_of_cutPartitionInputSource
            (C := C) (inputs := inputs) (cutRows C inputs))
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (minimalSeparation :
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q70_componentTopologyInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_20260522q70
          no_crossing no_singleton_bumping
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q63_selectedRawTailCoverageSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles
              componentTopology cutRows
              (S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
                cutRows angularRows)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows)
              selectedActualCarrierFaceSuccAngleRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  exact
    S2_q71_actualExteriorSectorInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedActualCarrierFaceSuccAngles_minimalDeletedTailSeparation
      no_crossing no_singleton_bumping cutRows
      (S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
        cutRows angularRows)
      (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
        cutRows angularRows endpointRows)
      selectedActualCarrierFaceSuccAngleRows minimalSeparation

set_option linter.style.longLine false in
/-- Claim `S2-q72-selected-head-geometric-worker`.

The q72 exterior-arc composer with the q71/q72 selected-head geometric and
endpoint leaves lowered to selected angular no-between rows plus
endpoint-selected-head rows for the exact heads chosen by the actual carrier
cut source.  This is only a selected-head eraser/composer; it does not use a
global all-outgoing no-between row, W32, an actual-sector premise, or a
completed boundary cycle. -/
noncomputable def
    S2_q72_actualExteriorSectorInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_cutPartitionInputSource_selectedAngularNoBetween_endpointSelectedHeadRows_selectedActualCarrierFaceSuccAngles_exteriorFrontierArcRows
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q68_selectedAngularNoBetweenRows_of_cutPartitionInputSource
            (C := C) (inputs := inputs) (cutRows C inputs))
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (selectedActualCarrierFaceSuccAngleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (arcRows :
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q70_componentTopologyInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_20260522q70
          no_crossing no_singleton_bumping
      let selectedCarrierRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricRowsHere :=
                S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
                  cutRows angularRows (C := C) inputs
              let geometricSelection :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  geometricRowsHere
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelection
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
        fun {m} C inputs =>
          let geometricRowsHere :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          S2_q70_selectedCarrierRows_of_cutPartitionInputSource_geometricRows_selectedActualCarrierFaceSuccAngles
            (C := C) (inputs := inputs) (cutRows C inputs)
            geometricRowsHere
            (by
              exact selectedActualCarrierFaceSuccAngleRows
                (C := C) (inputs := inputs));
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (cutRows C inputs)
              (S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
                cutRows angularRows (C := C) inputs)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows (C := C) inputs)
              (selectedCarrierRows C inputs)
          RawFaceSuccOrbitExteriorFrontierArcSeparationSourceRows
            (inputs := inputs) selectedRawRows.O) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  exact
    S2_q72_actualExteriorSectorInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_exteriorFrontierArcRows
      no_crossing no_singleton_bumping cutRows
      (S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
        cutRows angularRows)
      (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
        cutRows angularRows endpointRows)
      (fun {m} C inputs =>
        let geometricRowsHere :=
          S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
            cutRows angularRows (C := C) inputs
        let geometricSelection :
            UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
              C inputs :=
          S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
            (C := C) (inputs := inputs) (cutRows C inputs)
            geometricRowsHere
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
            (C := C) (inputs := inputs) geometricSelection
        S2_q70_selectedCarrierRows_of_cutPartitionInputSource_geometricRows_selectedActualCarrierFaceSuccAngles
          (C := C) (inputs := inputs) (cutRows C inputs)
          geometricRowsHere
          (by
            change
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
                inputs selectedRows
            exact selectedActualCarrierFaceSuccAngleRows
              (C := C) (inputs := inputs)))
      arcRows

set_option linter.style.longLine false in
/-- Claim `S2-active-q72-source-integrator`.

Source-facing q72 integrator.  The actual carrier cut rows are lowered from
the concrete actual-carrier two-neighbour row, selected-head geometric rows
from selected angular no-between rows, selected-head endpoint rows from the
selected endpoint source, selected `faceSucc` angle rows from the q72
orientation/local-strict face-turn worker, and the q72 exterior-frontier arc
source from repeated-tail cut partitions on the same q64 selected raw orbit.
The topology leaf is the Janiszewski boundary-bumping source plus the selected
frontier-incident singleton obstruction source. -/
noncomputable def
    S2_active_q72_actualExteriorSectorInputSourceRows_family_of_janiszewskiBoundaryBumping_frontierVertexIncident_actualCarrierCard_selectedAngular_endpointHeads_orientation_localStrict_repeatedTailCutPartitions
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (frontier_vertex_incident :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs)
    (hcard :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
            unboundedFrontierCarrierGraph_decidableAdj C inputs
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card =
              2)
    (angularRows :
      let cutRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
                C inputs :=
        S2CarrierCutSource.S2_q72_cutrows_from_card_worker_family_of_frontierCarrierGraph_neighborFinset_card_two
          hcard
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q68_selectedAngularNoBetweenRows_of_cutPartitionInputSource
            (C := C) (inputs := inputs) (cutRows C inputs))
    (endpointRows :
      let cutRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
                C inputs :=
        S2CarrierCutSource.S2_q72_cutrows_from_card_worker_family_of_frontierCarrierGraph_neighborFinset_card_two
          hcard
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricRows :=
            S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
              cutRows angularRows (C := C) inputs
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              geometricRows
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (orientationRows :
      let cutRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
                C inputs :=
        S2CarrierCutSource.S2_q72_cutrows_from_card_worker_family_of_frontierCarrierGraph_neighborFinset_card_two
          hcard
      let geometricRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                    inputs :=
                S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
                  (C := C) (inputs := inputs) (cutRows C inputs)
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                Nonempty
                  (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                    C a.1 (selectedRows.selectedNeighborRows a).left
                      (selectedRows.selectedNeighborRows a).right) :=
        S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
          cutRows angularRows
      let geometricSelection :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
        S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
          cutRows geometricRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource
            inputs selectedRows)
    (localStrictOrder :
      let cutRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
                C inputs :=
        S2CarrierCutSource.S2_q72_cutrows_from_card_worker_family_of_frontierCarrierGraph_neighborFinset_card_two
          hcard
      let geometricRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                    inputs :=
                S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
                  (C := C) (inputs := inputs) (cutRows C inputs)
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                Nonempty
                  (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                    C a.1 (selectedRows.selectedNeighborRows a).left
                      (selectedRows.selectedNeighborRows a).right) :=
        S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
          cutRows angularRows
      let geometricSelection :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
        S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
          cutRows geometricRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (cutPartitions :
      let no_crossing :
          PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
        S2_q72_noCompactConnectedKCrossing_of_janiszewskiBoundaryBumping_20260522q72
          boundary_bumping
      let no_singleton_bumping :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
                C inputs :=
        S2_q72_singletonBoundaryBumpingObstruction_family_of_frontierVertexIncident_20260522q72
          frontier_vertex_incident
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        S2_q70_componentTopologyInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_20260522q70
          no_crossing no_singleton_bumping
      let cutRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
                C inputs :=
        S2CarrierCutSource.S2_q72_cutrows_from_card_worker_family_of_frontierCarrierGraph_neighborFinset_card_two
          hcard
      let geometricRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                    inputs :=
                S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
                  (C := C) (inputs := inputs) (cutRows C inputs)
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                Nonempty
                  (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                    C a.1 (selectedRows.selectedNeighborRows a).left
                      (selectedRows.selectedNeighborRows a).right) :=
        S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
          cutRows angularRows
      let selectedHeadAt :=
        S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
          cutRows angularRows endpointRows
      let geometricSelection :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
        fun {m} C inputs =>
          S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
            (C := C) (inputs := inputs) (cutRows (m := m) C inputs)
            (geometricRows (m := m) C inputs)
      let angleRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) (geometricSelection C inputs)
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
                inputs selectedRows :=
        S2_q72_selected_face_turn_angle_worker_family_of_geometricSelection_orientation_localStrict
          geometricSelection orientationRows localStrictOrder
      let selectedCarrierRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricSelectionHere :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  (geometricRows C inputs)
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelectionHere
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
        fun {m} C inputs =>
          S2_q70_selectedCarrierRows_of_cutPartitionInputSource_geometricRows_selectedActualCarrierFaceSuccAngles
            (C := C) (inputs := inputs) (cutRows C inputs)
            (geometricRows C inputs)
            (by
              let geometricSelectionHere :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  (geometricRows C inputs)
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelectionHere
              change
                RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
                  inputs selectedRows
              change
                RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
                  inputs selectedRows
              exact angleRows (m := m) (C := C) (inputs := inputs))
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology (m := m) C inputs) (cutRows (m := m) C inputs)
              (geometricRows (m := m) C inputs)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows (C := C) inputs)
              (selectedCarrierRows (m := m) C inputs)
          SelectedRawOrbitRepeatedTailCutPartitions selectedRawRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
    S2_q72_noCompactConnectedKCrossing_of_janiszewskiBoundaryBumping_20260522q72
      boundary_bumping
  let no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs :=
    S2_q72_singletonBoundaryBumpingObstruction_family_of_frontierVertexIncident_20260522q72
      frontier_vertex_incident
  let cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs :=
    S2CarrierCutSource.S2_q72_cutrows_from_card_worker_family_of_frontierCarrierGraph_neighborFinset_card_two
      hcard
  let geometricRows :=
    S2_q66_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
      cutRows angularRows
  let selectedHeadAt :=
    S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
      cutRows angularRows endpointRows
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
    S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
      cutRows geometricRows
  let angleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows :=
    S2_q72_selected_face_turn_angle_worker_family_of_geometricSelection_orientation_localStrict
      geometricSelection orientationRows localStrictOrder
  let selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelectionHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelectionHere
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource) :=
    fun {m} C inputs =>
      S2_q70_selectedCarrierRows_of_cutPartitionInputSource_geometricRows_selectedActualCarrierFaceSuccAngles
        (C := C) (inputs := inputs) (cutRows C inputs)
        (geometricRows C inputs)
        (by
          let geometricSelectionHere :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelectionHere
          change
            RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
              inputs selectedRows
          change
            RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
              inputs selectedRows
          exact angleRows (m := m) (C := C) (inputs := inputs))
  let arcRows :
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        S2_q70_componentTopologyInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_20260522q70
          no_crossing no_singleton_bumping
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (cutRows C inputs)
              (geometricRows C inputs)
              (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
                cutRows angularRows endpointRows (C := C) inputs)
              (selectedCarrierRows C inputs)
          RawFaceSuccOrbitExteriorFrontierArcSeparationSourceRows
            (inputs := inputs) selectedRawRows.O := by
    intro m C inputs
    let componentTopology :
        forall {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C),
            UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
      S2_q70_componentTopologyInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_20260522q70
        no_crossing no_singleton_bumping
    let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
      S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
        (C := C) (inputs := inputs)
        (componentTopology (m := m) C inputs) (cutRows (m := m) C inputs)
        (geometricRows (m := m) C inputs)
        (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
          cutRows angularRows endpointRows (C := C) inputs)
        (selectedCarrierRows (m := m) C inputs)
    change RawFaceSuccOrbitExteriorFrontierArcSeparationSourceRows
      (inputs := inputs) selectedRawRows.O
    exact
      S2_q72_exteriorFrontierArcSeparationSourceRows_of_selectedRawOrbit_repeatedTailCutPartitions
        (C := C) (inputs := inputs) selectedRawRows
        (by
          change SelectedRawOrbitRepeatedTailCutPartitions selectedRawRows
          exact cutPartitions (C := C) (inputs := inputs))
  exact
    S2_q72_actualExteriorSectorInputSourceRows_family_of_noCompactConnectedKCrossing_boundaryBumping_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_exteriorFrontierArcRows
      no_crossing no_singleton_bumping cutRows geometricRows
      (S2_q66_selectedHeadAt_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows_endpointSelectedHeadRows
        cutRows angularRows endpointRows)
      selectedCarrierRows arcRows
-/

set_option linter.style.longLine false in
/-- Claim `S2-q75-actual-exterior-sector-integrator`.

The q75 source-facing actual-sector route with the component topology leaf
lowered to finite no-closed separation plus singleton boundary-bumping, the
selected-head endpoint leaf lowered to selection-free endpoint frontier-edge
membership, and the selected carrier successor leaf lowered to the concrete
selected `faceSucc` rows.  The only remaining repeated-tail input is the
minimal deleted-tail separation row on the exact q62 selected raw orbit built
inside this theorem. -/
noncomputable def
    S2_q75_actualExteriorSectorInputSourceRows_family_of_finiteNoClosed_singletonBumping_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembership_faceSuccRows_minimalDeletedTailSeparation
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          IncidentGermEndpointFrontierEdgeMembershipRows inputs)
    (faceSuccRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailFaceSuccRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (minimalSeparation :
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        S2_q75_componentTopologyInputSourceRows_family_of_finiteDrawingNoClosedSeparation_singletonBoundaryBumping_20260522q75
          frontier_noClosedSeparation no_singleton_bumping
      let selectedHeadAt :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricSelection :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  (geometricRows C inputs)
              let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
                S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelection
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                IncidentGermEndpointSelectedHeadAt
                  (C := C) (inputs := inputs) selectedRows a :=
        S2_q62_selectedHeadAt_family_of_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembershipRows
          cutRows geometricRows endpointRows
      let geometricSelection :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
        S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
          cutRows geometricRows
      let selectedCarrierRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) (geometricSelection C inputs)
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
        S2_q75_selected_successor_tail_source_family_of_geometricSelection_faceSuccRows
          geometricSelection faceSuccRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
              componentTopology cutRows geometricRows selectedHeadAt
              selectedCarrierRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
    S2_q75_componentTopologyInputSourceRows_family_of_finiteDrawingNoClosedSeparation_singletonBoundaryBumping_20260522q75
      frontier_noClosedSeparation no_singleton_bumping
  let selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a :=
    S2_q62_selectedHeadAt_family_of_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembershipRows
      cutRows geometricRows endpointRows
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
    S2_q61_r14_geometricSelectionInputSource_family_of_cutPartitionInputSource_geometricRows
      cutRows geometricRows
  let selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource) :=
    S2_q75_selected_successor_tail_source_family_of_geometricSelection_faceSuccRows
      geometricSelection faceSuccRows
  intro m C inputs
  exact
    S2_q62_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_minimalDeletedTailSeparation
      componentTopology cutRows geometricRows selectedHeadAt selectedCarrierRows
      minimalSeparation
      C inputs

set_option linter.style.longLine false in
/-- Claim `S2-q77-route-integrator-main`.

The q75 actual-sector route with the singleton boundary-bumping branch lowered
to selected frontier-vertex incidence.  This keeps the route source-facing:
frontier incidence is still a genuine producer obligation below the exterior
walk, and the theorem does not introduce a W-facing facade or any completed
boundary-cycle premise. -/
noncomputable def
    S2_q77_actualExteriorSectorInputSourceRows_family_of_finiteNoClosed_frontierVertexIncident_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembership_faceSuccRows_minimalDeletedTailSeparation
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (frontier_vertex_incident :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          IncidentGermEndpointFrontierEdgeMembershipRows inputs)
    (faceSuccRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailFaceSuccRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (minimalSeparation :
      let no_singleton_bumping :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
                C inputs :=
        S2_q76_singletonBoundaryBumpingObstruction_family_of_frontierVertexIncident_20260522q76
          frontier_vertex_incident
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        S2_q75_componentTopologyInputSourceRows_family_of_finiteDrawingNoClosedSeparation_singletonBoundaryBumping_20260522q75
          frontier_noClosedSeparation no_singleton_bumping
      let selectedHeadAt :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricSelection :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  (geometricRows C inputs)
              let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
                S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelection
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                IncidentGermEndpointSelectedHeadAt
                  (C := C) (inputs := inputs) selectedRows a :=
        S2_q62_selectedHeadAt_family_of_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembershipRows
          cutRows geometricRows endpointRows
      let geometricSelection :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
        fun {m} C inputs =>
          S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
            (C := C) (inputs := inputs) (cutRows (m := m) C inputs)
            (geometricRows (m := m) C inputs)
      let selectedCarrierRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) (geometricSelection C inputs)
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
        S2_q75_selected_successor_tail_source_family_of_geometricSelection_faceSuccRows
          geometricSelection faceSuccRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitMinimalDeletedTailSeparation
            (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
              componentTopology cutRows geometricRows selectedHeadAt
              selectedCarrierRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs :=
    S2_q76_singletonBoundaryBumpingObstruction_family_of_frontierVertexIncident_20260522q76
      frontier_vertex_incident
  intro m C inputs
  exact
    S2_q75_actualExteriorSectorInputSourceRows_family_of_finiteNoClosed_singletonBumping_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembership_faceSuccRows_minimalDeletedTailSeparation
      frontier_noClosedSeparation no_singleton_bumping cutRows geometricRows
      endpointRows faceSuccRows minimalSeparation
      C inputs

set_option linter.style.longLine false in
/-- Claim `S2-q80-q60-geometric-head-alignment-source`, exact q60-head form.

The q78 geometric-row leaf is lowered to selected angular/no-between rows
for the exact heads selected by
`S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource`.  This
does not identify those heads with any other local source by definitional
equality; the angular premise is already stated on the q60 cut-selected
heads. -/
theorem
    S2_q80_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q68_selectedAngularNoBetweenRows_of_cutPartitionInputSource
            (C := C) (inputs := inputs) (cutRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
            (C := C) (inputs := inputs) (cutRows C inputs)
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          Nonempty
            (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right) := by
  intro m C inputs
  exact
    S2_q60_geometricRows_of_cutPartitionInputSource_angularNoBetweenRows
      (C := C) (inputs := inputs) (cutRows C inputs)
      (angularRows C inputs)

set_option linter.style.longLine false in
/-- q80 local-isolation carrier-cut specialization.

Selected local-isolation rows supply the carrier-cut input through the checked
q78 lowering; the remaining angular/no-between source is still required on
the exact q60 cut-selected heads produced from that lowered cut source.  This
records the head-aligned route without assuming a same-head bridge from the
local-isolation sector heads. -/
theorem
    S2_q80_geometricRows_family_of_selectedLocalIsolation_selectedAngularNoBetweenRows
    (localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs)
    (angularRows :
      let cutRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
                C inputs :=
        S2CarrierCutSource.S2_q78_carrier_cut_source_lowering_family_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          localIsolation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_q68_selectedAngularNoBetweenRows_of_cutPartitionInputSource
            (C := C) (inputs := inputs) (cutRows C inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        let cutRows :
            UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
              C inputs :=
          S2CarrierCutSource.S2_q78_carrier_cut_source_lowering_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
            (C := C) (inputs := inputs) (localIsolation C inputs)
        let selectedRows :
            UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
            (C := C) (inputs := inputs) cutRows
        forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
          Nonempty
            (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right) := by
  let cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs :=
    S2CarrierCutSource.S2_q78_carrier_cut_source_lowering_family_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      localIsolation
  intro m C inputs
  exact
    S2_q80_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
      cutRows
      (by
        intro m C inputs
        simpa [cutRows] using angularRows (m := m) C inputs)
      (C := C) (inputs := inputs)

set_option linter.style.longLine false in
/-- q81 source-facing actual exterior-sector route.

This composes the q80/q79 lowerings into the checked face-dart route while
keeping the remaining obligations source-level: finite component rows, angular
rows on the exact q60 cut-selected heads, endpoint local-radius containment
for the finite local-isolation heads, selected actual-carrier face-successor
angles, and minimal deleted-tail separation on the exact q64 raw orbit. -/
noncomputable def
    S2_q81_actualExteriorSectorInputSourceRows_family_of_finiteRows_q60Angular_endpointRadius_faceSuccAngles_minimalDeletedTailSeparation
    (finiteRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyFiniteDrawingSourceRows
            inputs)
    (angularRows :
      let localIsolation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows
                inputs :=
        S2_q79_selectedLocalIsolationSource_family_of_localSectorRows
          (fun C inputs => (finiteRows C inputs).localSectorRows)
      let cutRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
                C inputs :=
        S2CarrierCutSource.S2_q78_carrier_cut_source_lowering_family_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          localIsolation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            GeometricRotationSystem.GraphVertexAngularNoBetweenRows
              C a.1 (selectedRows.selectedNeighborRows a).left
                (selectedRows.selectedNeighborRows a).right)
    (endpointSelectedHeadRows :
      let localIsolation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows
                inputs :=
        S2_q79_selectedLocalIsolationSource_family_of_localSectorRows
          (fun C inputs => (finiteRows C inputs).localSectorRows)
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          IncidentGermEndpointSelectedHeadRows selectedRows)
    (endpointRadiusContains :
      let localIsolation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows
                inputs :=
        S2_q79_selectedLocalIsolationSource_family_of_localSectorRows
          (fun C inputs => (finiteRows C inputs).localSectorRows)
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_q51_endpointSelectedHeadLocalRows_of_selectedLocalIsolation
              (C := C) (inputs := inputs) (localIsolation C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermSelectedEndpointLocalRadiusContainsAt localRows a)
    (selectedActualCarrierFaceSuccAngles :
      let localIsolation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows
                inputs :=
        S2_q79_selectedLocalIsolationSource_family_of_localSectorRows
          (fun C inputs => (finiteRows C inputs).localSectorRows)
      let cutRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
                C inputs :=
        S2CarrierCutSource.S2_q78_carrier_cut_source_lowering_family_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          localIsolation
      let geometricRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                    inputs :=
                S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
                  (C := C) (inputs := inputs) (cutRows C inputs)
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                Nonempty
                  (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                    C a.1 (selectedRows.selectedNeighborRows a).left
                      (selectedRows.selectedNeighborRows a).right) :=
        S2_q80_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
          cutRows angularRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (minimalSeparation :
      let localIsolation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              SelectedUnboundedFrontierEdgeLocalIsolationSourceRows
                inputs :=
        S2_q79_selectedLocalIsolationSource_family_of_localSectorRows
          (fun C inputs => (finiteRows C inputs).localSectorRows)
      let cutRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
                C inputs :=
        S2CarrierCutSource.S2_q78_carrier_cut_source_lowering_family_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
          localIsolation
      let geometricRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                    inputs :=
                S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
                  (C := C) (inputs := inputs) (cutRows C inputs)
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                Nonempty
                  (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                    C a.1 (selectedRows.selectedNeighborRows a).left
                      (selectedRows.selectedNeighborRows a).right) :=
        S2_q80_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
          cutRows angularRows
      let endpointCovers :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let localSectorRows :
                  forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                    UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
                localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
                  (C := C) (inputs := inputs) (localIsolation C inputs)
              let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
                localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
                  (C := C) (inputs := inputs) localSectorRows
              let localRows :
                  IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
                S2_q51_endpointSelectedHeadLocalRows_of_selectedLocalIsolation
                  (C := C) (inputs := inputs) (localIsolation C inputs)
              IncidentGermEndpointLocalRadiusCoversRows
                (C := C) (inputs := inputs) (selectedRows := selectedRows)
                localRows :=
        S2_q80_endpointLocalRadiusCoversRows_family_of_selectedLocalIsolation
          localIsolation endpointSelectedHeadRows endpointRadiusContains
      let endpointRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              IncidentGermEndpointFrontierEdgeMembershipRows inputs :=
        S2_q77_incidentGermEndpointFrontierEdgeMembershipRows_family_of_selectedLocalIsolation_endpointLocalRadiusCovers
          localIsolation endpointCovers
      let selectedHeadAt :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricSelection :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  (geometricRows C inputs)
              let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
                S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelection
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                IncidentGermEndpointSelectedHeadAt
                  (C := C) (inputs := inputs) selectedRows a :=
        S2_q62_selectedHeadAt_family_of_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembershipRows
          cutRows geometricRows endpointRows
      let faceSuccRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricSelection :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  (geometricRows C inputs)
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelection
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailFaceSuccRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
        S2_q79_q60_selected_faceSucc_source_family_of_cutPartitionInputSource_geometricRows_selectedActualCarrierFaceSuccAngles
          cutRows geometricRows selectedActualCarrierFaceSuccAngles
      let selectedCarrierRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricSelection :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  (geometricRows C inputs)
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelection
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
        S2_q77_q64SelectedCarrierRows_family_of_cutPartitionInputSource_geometricRows_faceSuccRows
          cutRows geometricRows faceSuccRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_q64_actualExteriorWalkSelectedRawTailCoverageSourceRows
              (C := C) (inputs := inputs)
              ((finiteRows C inputs).toInputSourceRows) (cutRows C inputs)
              (geometricRows C inputs) (selectedHeadAt C inputs)
              (selectedCarrierRows C inputs)
          SelectedRawOrbitMinimalDeletedTailSeparation selectedRawRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let localIsolation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedUnboundedFrontierEdgeLocalIsolationSourceRows inputs :=
    S2_q79_selectedLocalIsolationSource_family_of_localSectorRows
      (fun C inputs => (finiteRows C inputs).localSectorRows)
  let cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs :=
    S2CarrierCutSource.S2_q78_carrier_cut_source_lowering_family_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
      localIsolation
  let geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right) :=
    S2_q80_geometricRows_family_of_cutPartitionInputSource_selectedAngularNoBetweenRows
      cutRows angularRows
  let endpointCovers :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let localSectorRows :
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
            localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
              (C := C) (inputs := inputs) (localIsolation C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
              (C := C) (inputs := inputs) localSectorRows
          let localRows :
              IncidentGermEndpointSelectedHeadLocalRows selectedRows :=
            S2_q51_endpointSelectedHeadLocalRows_of_selectedLocalIsolation
              (C := C) (inputs := inputs) (localIsolation C inputs)
          IncidentGermEndpointLocalRadiusCoversRows
            (C := C) (inputs := inputs) (selectedRows := selectedRows)
            localRows :=
    S2_q80_endpointLocalRadiusCoversRows_family_of_selectedLocalIsolation
      localIsolation endpointSelectedHeadRows endpointRadiusContains
  let endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          IncidentGermEndpointFrontierEdgeMembershipRows inputs :=
    S2_q77_incidentGermEndpointFrontierEdgeMembershipRows_family_of_selectedLocalIsolation_endpointLocalRadiusCovers
      localIsolation endpointCovers
  let selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a :=
    S2_q62_selectedHeadAt_family_of_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembershipRows
      cutRows geometricRows endpointRows
  let faceSuccRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailFaceSuccRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource) :=
    S2_q79_q60_selected_faceSucc_source_family_of_cutPartitionInputSource_geometricRows_selectedActualCarrierFaceSuccAngles
      cutRows geometricRows selectedActualCarrierFaceSuccAngles
  intro m C inputs
  exact
    S2_q80_actualExteriorSectorInputSourceRows_family_of_faceSuccRows_minimalDeletedTailSeparation
      (fun {m} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C) =>
        (finiteRows C inputs).toInputSourceRows)
      (fun {m} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C) =>
        cutRows C inputs)
      (fun {m} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C) =>
        geometricRows C inputs)
      (fun {m} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C) =>
        selectedHeadAt C inputs)
      (fun {m} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C) =>
        faceSuccRows C inputs)
      (fun {m} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C) =>
        minimalSeparation C inputs)
      C inputs

set_option linter.style.longLine false in
/-- Claim `S2-q78-actual-sector-cyclicSucc-integrator`.

The q77 actual-sector source route with the repeated-tail leaf lowered from
minimal deleted-tail separation to cyclic-successor deleted-tail
nonreachability on the same q62 selected raw orbit.  The exposed leaves are
exactly the q77 lower source leaves, with the repeated-tail source sharpened
to the existing q77 cyclic-successor nonreachability row. -/
noncomputable def
    S2_q78_actualExteriorSectorInputSourceRows_family_of_finiteNoClosed_frontierVertexIncident_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembership_faceSuccRows_cyclicSuccDeletedTailNonreachability
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (frontier_vertex_incident :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs)
    (cutRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
                inputs :=
            S2_q60_selectedCutPartitionSourceRows_of_cutPartitionInputSource
              (C := C) (inputs := inputs) (cutRows C inputs)
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 (selectedRows.selectedNeighborRows a).left
                  (selectedRows.selectedNeighborRows a).right))
    (endpointRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          IncidentGermEndpointFrontierEdgeMembershipRows inputs)
    (faceSuccRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailFaceSuccRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource))
    (cyclicSuccNonreachability :
      let no_singleton_bumping :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
                C inputs :=
        S2_q76_singletonBoundaryBumpingObstruction_family_of_frontierVertexIncident_20260522q76
          frontier_vertex_incident
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        S2_q75_componentTopologyInputSourceRows_family_of_finiteDrawingNoClosedSeparation_singletonBoundaryBumping_20260522q75
          frontier_noClosedSeparation no_singleton_bumping
      let selectedHeadAt :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let geometricSelection :
                  UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                    C inputs :=
                S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
                  (C := C) (inputs := inputs) (cutRows C inputs)
                  (geometricRows C inputs)
              let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
                S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) geometricSelection
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                IncidentGermEndpointSelectedHeadAt
                  (C := C) (inputs := inputs) selectedRows a :=
        S2_q62_selectedHeadAt_family_of_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembershipRows
          cutRows geometricRows endpointRows
      let geometricSelection :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
        fun {m} C inputs =>
          S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
            (C := C) (inputs := inputs) (cutRows (m := m) C inputs)
            (geometricRows (m := m) C inputs)
      let selectedCarrierRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              let selectedRows :
                  UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                    inputs :=
                selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
                  (C := C) (inputs := inputs) (geometricSelection C inputs)
              RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
        S2_q75_selected_successor_tail_source_family_of_geometricSelection_faceSuccRows
          geometricSelection faceSuccRows
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
            (S2_q62_selectedRawTailCoverageSourceRows_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows
              componentTopology cutRows geometricRows selectedHeadAt
              selectedCarrierRows (C := C) inputs)) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs :=
    S2_q76_singletonBoundaryBumpingObstruction_family_of_frontierVertexIncident_20260522q76
      frontier_vertex_incident
  let componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
    S2_q75_componentTopologyInputSourceRows_family_of_finiteDrawingNoClosedSeparation_singletonBoundaryBumping_20260522q75
      frontier_noClosedSeparation no_singleton_bumping
  let selectedHeadAt :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let geometricSelection :
              UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
                C inputs :=
            S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
              (C := C) (inputs := inputs) (cutRows C inputs)
              (geometricRows C inputs)
          let selectedRows : LocalSelectedIncidentEdgePairSourceRows inputs :=
            S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) geometricSelection
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            IncidentGermEndpointSelectedHeadAt
              (C := C) (inputs := inputs) selectedRows a :=
    S2_q62_selectedHeadAt_family_of_cutPartitionInputSource_geometricRows_endpointFrontierEdgeMembershipRows
      cutRows geometricRows endpointRows
  let geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs :=
    fun {m} C inputs =>
      S2_q60_geometricSelectionInputSource_of_cutPartitionInputSource_geometricRows
        (C := C) (inputs := inputs) (cutRows (m := m) C inputs)
        (geometricRows (m := m) C inputs)
  let selectedCarrierRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs)
              selectedRows.toGeometricSelectionInputSource) :=
    S2_q75_selected_successor_tail_source_family_of_geometricSelection_faceSuccRows
      geometricSelection faceSuccRows
  intro m C inputs
  exact
    S2_q62_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_cyclicSuccDeletedTailNonreachability
      componentTopology cutRows geometricRows selectedHeadAt selectedCarrierRows
      cyclicSuccNonreachability
      C inputs

end

end S2CarrierLocalSource
end Swanepoel
end ErdosProblems1066
