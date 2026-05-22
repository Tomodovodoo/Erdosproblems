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

end

end S2CarrierLocalSource
end Swanepoel
end ErdosProblems1066
