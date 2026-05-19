import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete

set_option autoImplicit false

/-!
# Finite plane drawing rows for S2

This file starts the honest S2 outer-component theorem at the drawing level.
It defines the subset of the plane occupied by canonical unit-distance edges
and proves the endpoint membership facts needed before an exterior component
can be selected.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FinitePlaneDrawing

open JordanTopologyFactsConcrete
open JordanTopologyFactsConcrete.MinimalFailureTopology

noncomputable section

variable {n : Nat}

/-- The closed affine segment from `a` to `b`, expressed using the project-local
straight-line parametrization. -/
def closedSegment (a b : PlanarInterface.Point) : Set PlanarInterface.Point :=
  {p | Exists fun t : Real =>
    0 <= t /\ t <= 1 /\ p = PlanarInterface.segmentPoint a b t}

/-- The project-local closed segment is the image of the compact interval
`[0, 1]` under the affine segment parametrization. -/
theorem closedSegment_eq_image_Icc (a b : PlanarInterface.Point) :
    closedSegment a b =
      (fun t : Real => PlanarInterface.segmentPoint a b t) ''
        Set.Icc (0 : Real) 1 := by
  ext p
  constructor
  · rintro ⟨t, ht0, ht1, hpt⟩
    exact ⟨t, ⟨ht0, ht1⟩, hpt.symm⟩
  · rintro ⟨t, ht, hpt⟩
    exact ⟨t, ht.1, ht.2, hpt.symm⟩

/-- The affine segment parametrization is continuous. -/
theorem continuous_segmentPoint (a b : PlanarInterface.Point) :
    Continuous fun t : Real => PlanarInterface.segmentPoint a b t := by
  unfold PlanarInterface.segmentPoint
  continuity

/-- Closed straight segments are compact. -/
theorem isCompact_closedSegment (a b : PlanarInterface.Point) :
    IsCompact (closedSegment a b) := by
  rw [closedSegment_eq_image_Icc]
  exact isCompact_Icc.image (continuous_segmentPoint a b)

/-- Closed straight segments are topologically closed in the plane. -/
theorem isClosed_closedSegment (a b : PlanarInterface.Point) :
    IsClosed (closedSegment a b) :=
  (isCompact_closedSegment a b).isClosed

/-- The left endpoint lies on its closed segment. -/
theorem left_mem_closedSegment (a b : PlanarInterface.Point) :
    a ∈ closedSegment a b := by
  refine ⟨0, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · ext <;> norm_num [PlanarInterface.segmentPoint]

/-- The right endpoint lies on its closed segment. -/
theorem right_mem_closedSegment (a b : PlanarInterface.Point) :
    b ∈ closedSegment a b := by
  refine ⟨1, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · ext <;> norm_num [PlanarInterface.segmentPoint]

theorem segmentPoint_mem_closedSegment
    (a b : PlanarInterface.Point) {t : Real}
    (ht0 : 0 <= t) (ht1 : t <= 1) :
    PlanarInterface.segmentPoint a b t ∈ closedSegment a b :=
  ⟨t, ht0, ht1, rfl⟩

theorem inOpenSegment_mem_closedSegment
    {x a b : PlanarInterface.Point}
    (hx : PlanarInterface.InOpenSegment x a b) :
    x ∈ closedSegment a b := by
  rcases hx with ⟨t, ht0, ht1, hxt⟩
  exact ⟨t, le_of_lt ht0, le_of_lt ht1, hxt⟩

theorem mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment
    {x a b : PlanarInterface.Point}
    (hx : x ∈ closedSegment a b) :
    x = a ∨ x = b ∨ PlanarInterface.InOpenSegment x a b := by
  rcases hx with ⟨t, ht0, ht1, hxt⟩
  rcases lt_trichotomy t 0 with htneg | rfl | htpos
  · exact False.elim ((not_lt_of_ge ht0) htneg)
  · left
    simpa [PlanarInterface.segmentPoint] using hxt
  · rcases lt_trichotomy t 1 with htlt | htEq | htgt
    · exact Or.inr (Or.inr ⟨t, htpos, htlt, hxt⟩)
    · subst t
      right
      left
      simpa [PlanarInterface.segmentPoint] using hxt
    · exact False.elim ((not_lt_of_ge ht1) htgt)

theorem closedSegment_symm
    (a b : PlanarInterface.Point) :
    closedSegment a b = closedSegment b a := by
  ext x
  constructor
  · rintro ⟨t, ht0, ht1, hxt⟩
    refine ⟨1 - t, sub_nonneg.mpr ht1, by linarith, ?_⟩
    rw [hxt]
    ext <;> simp [PlanarInterface.segmentPoint] <;> ring
  · rintro ⟨t, ht0, ht1, hxt⟩
    refine ⟨1 - t, sub_nonneg.mpr ht1, by linarith, ?_⟩
    rw [hxt]
    ext <;> simp [PlanarInterface.segmentPoint] <;> ring

theorem eucDist_left_segmentPoint
    (a b : PlanarInterface.Point) (t : Real) (ht : 0 <= t) :
    _root_.eucDist a (PlanarInterface.segmentPoint a b t) =
      t * _root_.eucDist a b := by
  unfold _root_.eucDist PlanarInterface.segmentPoint
  have hs :
      (a.1 - ((1 - t) * a.1 + t * b.1)) ^ 2 +
        (a.2 - ((1 - t) * a.2 + t * b.2)) ^ 2 =
      t ^ 2 * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
    ring
  rw [hs]
  rw [Real.sqrt_mul (sq_nonneg t)]
  rw [Real.sqrt_sq ht]

theorem eucDist_segmentPoint_right
    (a b : PlanarInterface.Point) (t : Real) (ht : t <= 1) :
    _root_.eucDist (PlanarInterface.segmentPoint a b t) b =
      (1 - t) * _root_.eucDist a b := by
  unfold _root_.eucDist PlanarInterface.segmentPoint
  have hs :
      (((1 - t) * a.1 + t * b.1) - b.1) ^ 2 +
        (((1 - t) * a.2 + t * b.2) - b.2) ^ 2 =
      (1 - t) ^ 2 * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
    ring
  rw [hs]
  rw [Real.sqrt_mul (sq_nonneg (1 - t))]
  rw [Real.sqrt_sq (sub_nonneg.mpr ht)]

/-- The geometric drawing of the canonical unit-distance graph, as the union of
all closed straight segments carried by graph adjacencies. -/
def embeddedEdgeSet (C : _root_.UDConfig n) : Set PlanarInterface.Point :=
  {p | Exists fun i : Fin n =>
    Exists fun j : Fin n =>
      (canonicalGraph C).Adj i j /\
        p ∈ closedSegment
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j)}

/-- The finite set of ordered canonical graph edges used to present the
embedded drawing as a finite union of closed segments. -/
def embeddedEdgePairs (C : _root_.UDConfig n) :
    Finset (Prod (Fin n) (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).product
      (Finset.univ : Finset (Fin n))).filter
    (fun e : Prod (Fin n) (Fin n) => (canonicalGraph C).Adj e.1 e.2)

theorem mem_embeddedEdgePairs_iff
    {C : _root_.UDConfig n} {e : Prod (Fin n) (Fin n)} :
    e ∈ embeddedEdgePairs C <-> (canonicalGraph C).Adj e.1 e.2 := by
  classical
  simp [embeddedEdgePairs]

/-- The existential drawing definition is equivalent to the finite ordered-edge
presentation. -/
theorem mem_embeddedEdgeSet_iff_exists_embeddedEdgePairs
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} :
    p ∈ embeddedEdgeSet C <->
      Exists fun e : Prod (Fin n) (Fin n) =>
        e ∈ embeddedEdgePairs C /\
          p ∈ closedSegment
            ((canonicalGraph C).point e.1)
            ((canonicalGraph C).point e.2) := by
  classical
  constructor
  · intro hp
    rcases hp with ⟨i, j, hAdj, hpseg⟩
    refine ⟨(i, j), ?_, hpseg⟩
    exact mem_embeddedEdgePairs_iff.2 hAdj
  · intro hp
    rcases hp with ⟨e, he, hpseg⟩
    refine ⟨e.1, e.2, ?_, hpseg⟩
    exact mem_embeddedEdgePairs_iff.1 he

/-- The embedded drawing as a finite double union over all ordered vertex
pairs, retaining only adjacent pairs. -/
theorem embeddedEdgeSet_eq_iUnion_edges
    (C : _root_.UDConfig n) :
    embeddedEdgeSet C =
      ⋃ i : Fin n, ⋃ j : Fin n,
        {p | (canonicalGraph C).Adj i j /\
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} := by
  ext p
  simp [embeddedEdgeSet]

/-- The embedded drawing is closed: it is a finite union of compact straight
segments. -/
theorem embeddedEdgeSet_closed
    (C : _root_.UDConfig n) :
    IsClosed (embeddedEdgeSet C) := by
  rw [embeddedEdgeSet_eq_iUnion_edges]
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_iUnion_of_finite
  intro j
  by_cases hAdj : (canonicalGraph C).Adj i j
  · rw [show {p | (canonicalGraph C).Adj i j /\
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} =
          closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) by
        ext p
        simp [hAdj]]
    exact isClosed_closedSegment _ _
  · rw [show {p | (canonicalGraph C).Adj i j /\
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} =
          (∅ : Set PlanarInterface.Point) by
        ext p
        simp [hAdj]]
    exact isClosed_empty

/-- The embedded drawing is compact: it is a finite union of compact straight
segments. -/
theorem embeddedEdgeSet_compact
    (C : _root_.UDConfig n) :
    IsCompact (embeddedEdgeSet C) := by
  rw [embeddedEdgeSet_eq_iUnion_edges]
  simpa only [Set.mem_univ, Set.iUnion_true] using
    (Set.finite_univ.isCompact_biUnion (s := (Set.univ : Set (Fin n)))
      (f := fun i : Fin n =>
        ⋃ j : Fin n,
          {p | (canonicalGraph C).Adj i j /\
            p ∈ closedSegment
              ((canonicalGraph C).point i)
              ((canonicalGraph C).point j)})
      (by
        intro i _hi
        simpa only [Set.mem_univ, Set.iUnion_true] using
          (Set.finite_univ.isCompact_biUnion (s := (Set.univ : Set (Fin n)))
            (f := fun j : Fin n =>
              {p | (canonicalGraph C).Adj i j /\
                p ∈ closedSegment
                  ((canonicalGraph C).point i)
                  ((canonicalGraph C).point j)})
            (by
              intro j _hj
              by_cases hAdj : (canonicalGraph C).Adj i j
              · simpa [hAdj] using
                  isCompact_closedSegment
                    ((canonicalGraph C).point i)
                    ((canonicalGraph C).point j)
              · simp [hAdj]))))

/-- The tail endpoint of any canonical graph edge lies in the embedded drawing. -/
theorem left_vertex_mem_embeddedEdgeSet_of_adj
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    (canonicalGraph C).point i ∈ embeddedEdgeSet C := by
  exact
    ⟨i, j, hAdj,
      left_mem_closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)⟩

/-- The head endpoint of any canonical graph edge lies in the embedded drawing. -/
theorem right_vertex_mem_embeddedEdgeSet_of_adj
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    (canonicalGraph C).point j ∈ embeddedEdgeSet C := by
  exact
    ⟨i, j, hAdj,
      right_mem_closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)⟩

/-- A canonical graph edge contributes its whole closed segment to the embedded
drawing. -/
theorem closedSegment_subset_embeddedEdgeSet_of_adj
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) ⊆
      embeddedEdgeSet C := by
  intro p hp
  exact ⟨i, j, hAdj, hp⟩

theorem mem_embeddedEdgeSet_of_mem_embeddedEdgePairs
    {C : _root_.UDConfig n} {e : Prod (Fin n) (Fin n)}
    (he : e ∈ embeddedEdgePairs C) :
    closedSegment
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2) ⊆
      embeddedEdgeSet C :=
  closedSegment_subset_embeddedEdgeSet_of_adj
    (mem_embeddedEdgePairs_iff.1 he)

theorem left_vertex_mem_embeddedEdgeSet_of_mem_embeddedEdgePairs
    {C : _root_.UDConfig n} {e : Prod (Fin n) (Fin n)}
    (he : e ∈ embeddedEdgePairs C) :
    (canonicalGraph C).point e.1 ∈ embeddedEdgeSet C :=
  mem_embeddedEdgeSet_of_mem_embeddedEdgePairs he
    (left_mem_closedSegment _ _)

theorem right_vertex_mem_embeddedEdgeSet_of_mem_embeddedEdgePairs
    {C : _root_.UDConfig n} {e : Prod (Fin n) (Fin n)}
    (he : e ∈ embeddedEdgePairs C) :
    (canonicalGraph C).point e.2 ∈ embeddedEdgeSet C :=
  mem_embeddedEdgeSet_of_mem_embeddedEdgePairs he
    (right_mem_closedSegment _ _)

theorem inOpenSegment_subset_embeddedEdgeSet_of_adj
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    {p | PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)} ⊆
      embeddedEdgeSet C := by
  intro p hp
  exact closedSegment_subset_embeddedEdgeSet_of_adj hAdj
    (inOpenSegment_mem_closedSegment hp)

theorem graph_vertex_on_unit_edge_segment_is_endpoint
    {C : _root_.UDConfig n} {v i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j)
    (hmem :
      (canonicalGraph C).point v ∈
        closedSegment
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j)) :
    v = i ∨ v = j := by
  by_cases hvi : v = i
  · exact Or.inl hvi
  by_cases hvj : v = j
  · exact Or.inr hvj
  exfalso
  rcases hmem with ⟨t, ht0, ht1, hpoint⟩
  have hij :
      _root_.eucDist ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) = 1 := by
    simpa [PlanarInterface.geometry_eucDist_eq_root] using
      ((canonicalGraph C).adj_geometry_dist_eq_one hAdj)
  have hleft :
      _root_.eucDist ((canonicalGraph C).point i)
        ((canonicalGraph C).point v) = t := by
    rw [hpoint]
    rw [eucDist_left_segmentPoint _ _ t ht0]
    rw [hij]
    ring
  have hright :
      _root_.eucDist ((canonicalGraph C).point v)
        ((canonicalGraph C).point j) = 1 - t := by
    rw [hpoint]
    rw [eucDist_segmentPoint_right _ _ t ht1]
    rw [hij]
    ring
  have hsep_left :
      1 <= _root_.eucDist ((canonicalGraph C).point i)
        ((canonicalGraph C).point v) := by
    simpa [_root_.eucDist_comm] using C.sep v i hvi
  have ht_ge_one : 1 <= t := by
    simpa [hleft] using hsep_left
  have ht_eq_one : t = 1 := le_antisymm ht1 ht_ge_one
  have hsep_right :
      1 <= _root_.eucDist ((canonicalGraph C).point v)
        ((canonicalGraph C).point j) := by
    simpa using C.sep v j hvj
  have hzero : _root_.eucDist ((canonicalGraph C).point v)
        ((canonicalGraph C).point j) = 0 := by
    rw [hright, ht_eq_one]
    ring
  linarith

theorem graph_vertex_not_inOpenSegment_of_adj
    {C : _root_.UDConfig n} {v i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    ¬ PlanarInterface.InOpenSegment
        ((canonicalGraph C).point v)
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) := by
  intro hmem
  rcases hmem with ⟨t, ht0, ht1, hpoint⟩
  have hclosed :
      (canonicalGraph C).point v ∈
        closedSegment
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) :=
    ⟨t, le_of_lt ht0, le_of_lt ht1, hpoint⟩
  rcases graph_vertex_on_unit_edge_segment_is_endpoint hAdj hclosed with hvi | hvj
  · subst v
    have hij :
        _root_.eucDist ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) = 1 := by
      simpa [PlanarInterface.geometry_eucDist_eq_root] using
        ((canonicalGraph C).adj_geometry_dist_eq_one hAdj)
    have hdist :
        _root_.eucDist ((canonicalGraph C).point i)
          (PlanarInterface.segmentPoint
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) t) = t := by
      rw [eucDist_left_segmentPoint _ _ t (le_of_lt ht0), hij]
      ring
    have hzero :
        _root_.eucDist ((canonicalGraph C).point i)
          (PlanarInterface.segmentPoint
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) t) = 0 := by
      rw [← hpoint]
      exact _root_.eucDist_self _
    linarith
  · subst v
    have hij :
        _root_.eucDist ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) = 1 := by
      simpa [PlanarInterface.geometry_eucDist_eq_root] using
        ((canonicalGraph C).adj_geometry_dist_eq_one hAdj)
    have hdist :
        _root_.eucDist
          (PlanarInterface.segmentPoint
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) t)
          ((canonicalGraph C).point j) = 1 - t := by
      rw [eucDist_segmentPoint_right _ _ t (le_of_lt ht1), hij]
      ring
    have hzero :
        _root_.eucDist
          (PlanarInterface.segmentPoint
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) t)
          ((canonicalGraph C).point j) = 0 := by
      rw [← hpoint]
      exact _root_.eucDist_self _
    linarith

theorem graph_vertex_inOpenSegment_false_of_adj
    {C : _root_.UDConfig n} {v i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j)
    (hmem :
      PlanarInterface.InOpenSegment
        ((canonicalGraph C).point v)
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    False :=
  (graph_vertex_not_inOpenSegment_of_adj hAdj) hmem

/-- Any vertex with an incident canonical edge lies in the embedded drawing. -/
theorem vertex_mem_embeddedEdgeSet_of_incident
    {C : _root_.UDConfig n} {v w : Fin n}
    (hAdj : (canonicalGraph C).Adj v w) :
    (canonicalGraph C).point v ∈ embeddedEdgeSet C :=
  left_vertex_mem_embeddedEdgeSet_of_adj hAdj

theorem graph_vertex_mem_embeddedEdgeSet_iff_exists_adj
    {C : _root_.UDConfig n} {v : Fin n} :
    (canonicalGraph C).point v ∈ embeddedEdgeSet C <->
      Exists fun w : Fin n => (canonicalGraph C).Adj v w := by
  constructor
  · intro hv
    rcases hv with ⟨i, j, hAdj, hseg⟩
    rcases graph_vertex_on_unit_edge_segment_is_endpoint hAdj hseg with hvi | hvj
    · subst i
      exact ⟨j, hAdj⟩
    · subst j
      exact
        ⟨i,
          ((canonicalGraph C).adj_iff_unitDistanceAdj v i).2
            (GraphBridge.unitDistanceAdj_symm C
              (((canonicalGraph C).adj_iff_unitDistanceAdj i v).1 hAdj))⟩
  · rintro ⟨w, hAdj⟩
    exact vertex_mem_embeddedEdgeSet_of_incident hAdj

theorem graph_vertex_on_two_unit_edge_segments_share_endpoint
    {C : _root_.UDConfig n} {v i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hmemij :
      (canonicalGraph C).point v ∈
        closedSegment
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j))
    (hmemkl :
      (canonicalGraph C).point v ∈
        closedSegment
          ((canonicalGraph C).point k)
          ((canonicalGraph C).point l)) :
    (v = i ∨ v = j) /\ (v = k ∨ v = l) :=
  ⟨graph_vertex_on_unit_edge_segment_is_endpoint hij hmemij,
    graph_vertex_on_unit_edge_segment_is_endpoint hkl hmemkl⟩

/-- The graph-side S2 inputs imply every graph vertex lies on the embedded
unit-edge drawing.  Connectedness rules out isolated vertices because the
supplied unit-distance cycle provides a vertex in the nontrivial component. -/
theorem vertex_mem_embeddedEdgeSet_of_inputs
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    forall v : Fin n, (canonicalGraph C).point v ∈ embeddedEdgeSet C := by
  classical
  rcases inputs.hasUnitDistanceCycle with ⟨B⟩
  let k : Fin B.length := ⟨0, B.length_pos⟩
  let u : Fin n := B.vertex k
  intro v
  by_cases hvu : v = u
  · subst v
    exact left_vertex_mem_embeddedEdgeSet_of_adj (B.adjacent k)
  · have hreach :
        (GraphBridge.unitDistanceSimpleGraph C).Reachable v u :=
      inputs.connected v u
    have hv_support :
        v ∈ (GraphBridge.unitDistanceSimpleGraph C).support :=
      SimpleGraph.mem_support_of_reachable hvu hreach
    rcases
      (SimpleGraph.mem_support
        (G := GraphBridge.unitDistanceSimpleGraph C)).1 hv_support with
      ⟨w, hw⟩
    exact
      vertex_mem_embeddedEdgeSet_of_incident
        (((canonicalGraph C).adj_iff_unitDistanceAdj v w).2
          ((GraphBridge.unitDistanceSimpleGraph_adj C v w).1 hw))

/-- The embedded drawing is nonempty whenever the S2 graph-side inputs hold. -/
theorem embeddedEdgeSet_nonempty_of_inputs
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    (embeddedEdgeSet C).Nonempty := by
  classical
  obtain ⟨v⟩ := inputs.vertex_nonempty
  exact ⟨(canonicalGraph C).point v, vertex_mem_embeddedEdgeSet_of_inputs inputs v⟩

theorem adjacent_segments_not_cross_of_edgeVertexDisjoint
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l)) :
    ¬ PlanarInterface.SegmentsCrossInterior
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l) := by
  have hij_dist :
      Geometry.Distance.eucDist (C.pts i) (C.pts j) = 1 := by
    simpa using ((canonicalGraph C).adj_geometry_dist_eq_one hij)
  have hkl_dist :
      Geometry.Distance.eucDist (C.pts k) (C.pts l) = 1 := by
    simpa using ((canonicalGraph C).adj_geometry_dist_eq_one hkl)
  simpa [PlanarInterface.EdgeSegmentsCross,
    PlanarInterface.StraightLineUnitDistanceGraph.point] using
    (NoncrossingUnitEdges.separated_unit_edges_not_cross
      C (e := (i, j)) (f := (k, l)) hdisj hij_dist hkl_dist)

theorem not_exists_common_inOpenSegment_of_adj_edgeVertexDisjoint
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l)) :
    ¬ Exists fun p : PlanarInterface.Point =>
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) /\
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l) := by
  intro h
  exact
    adjacent_segments_not_cross_of_edgeVertexDisjoint hij hkl hdisj
      h

theorem inOpenSegment_inter_inOpenSegment_eq_empty_of_adj_edgeVertexDisjoint
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l)) :
    ({p | PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)} ∩
      {p | PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l)} :
        Set PlanarInterface.Point) = ∅ := by
  ext p
  constructor
  · intro hp
    exact False.elim
      (not_exists_common_inOpenSegment_of_adj_edgeVertexDisjoint
        hij hkl hdisj ⟨p, hp.1, hp.2⟩)
  · intro hp
    exact False.elim hp

theorem closedSegment_inter_closedSegment_eq_empty_of_adj_edgeVertexDisjoint
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l)) :
    (closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) ∩
      closedSegment
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l) :
        Set PlanarInterface.Point) = ∅ := by
  rcases hdisj with ⟨hik, hil, hjk, hjl⟩
  ext p
  constructor
  · intro hp
    rcases
        mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hp.1 with
      hpi | hpj | hpij
    · have hendpoint :
          i = k ∨ i = l := by
        rcases
          graph_vertex_on_unit_edge_segment_is_endpoint
            (C := C) (v := i) hkl (hpi ▸ hp.2) with hik' | hil'
        · exact Or.inl hik'
        · exact Or.inr hil'
      exact False.elim (hendpoint.elim hik hil)
    · have hendpoint :
          j = k ∨ j = l := by
        rcases
          graph_vertex_on_unit_edge_segment_is_endpoint
            (C := C) (v := j) hkl (hpj ▸ hp.2) with hjk' | hjl'
        · exact Or.inl hjk'
        · exact Or.inr hjl'
      exact False.elim (hendpoint.elim hjk hjl)
    · rcases
          mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hp.2 with
        hpk | hpl | hpkl
      · exact False.elim
          (graph_vertex_not_inOpenSegment_of_adj
            (C := C) (v := k) hij (hpk ▸ hpij))
      · exact False.elim
          (graph_vertex_not_inOpenSegment_of_adj
            (C := C) (v := l) hij (hpl ▸ hpij))
      · exact False.elim
          (adjacent_segments_not_cross_of_edgeVertexDisjoint
            hij hkl ⟨hik, hil, hjk, hjl⟩ ⟨p, hpij, hpkl⟩)
  · intro hp
    exact False.elim hp

theorem disjoint_closedSegment_of_adj_edgeVertexDisjoint
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l)) :
    Disjoint
      (closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j))
      (closedSegment
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l)) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  exact closedSegment_inter_closedSegment_eq_empty_of_adj_edgeVertexDisjoint
    hij hkl hdisj

theorem not_edgeVertexDisjoint_of_adj_closedSegment_inter
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hinter :
      (closedSegment
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) ∩
        closedSegment
          ((canonicalGraph C).point k)
          ((canonicalGraph C).point l) :
          Set PlanarInterface.Point).Nonempty) :
    ¬ PlanarInterface.EdgeVertexDisjoint (i, j) (k, l) := by
  intro hdisj
  rw [closedSegment_inter_closedSegment_eq_empty_of_adj_edgeVertexDisjoint
    hij hkl hdisj] at hinter
  exact Set.not_nonempty_empty hinter

/-- The embedded drawing is the set whose complement will be used for the
exterior-component proof. -/
def drawingComplement (C : _root_.UDConfig n) : Set PlanarInterface.Point :=
  (embeddedEdgeSet C)ᶜ

/-- The complement of the embedded drawing is open. -/
theorem drawingComplement_open
    (C : _root_.UDConfig n) :
    IsOpen (drawingComplement C) := by
  simpa [drawingComplement] using (embeddedEdgeSet_closed C).isOpen_compl

/-- The drawing complement is nonempty.  A finite union of compact edge
segments cannot cover the whole Euclidean plane. -/
theorem drawingComplement_nonempty
    (C : _root_.UDConfig n) :
    (drawingComplement C).Nonempty := by
  by_contra h
  have hsubset : (Set.univ : Set PlanarInterface.Point) ⊆ embeddedEdgeSet C := by
    intro p _hp
    by_contra hp
    exact h ⟨p, hp⟩
  have hb_univ : Bornology.IsBounded (Set.univ : Set PlanarInterface.Point) :=
    (embeddedEdgeSet_compact C).isBounded.subset hsubset
  exact NormedSpace.unbounded_univ ℝ PlanarInterface.Point hb_univ

/-- The open x-axis ray to the right of `R`, used to select a concrete
unbounded component of the drawing complement after a compactness bound is
chosen. -/
def xAxisRay (R : Real) : Set PlanarInterface.Point :=
  {p | Exists fun t : Real => R < t /\ p = (t, 0)}

theorem xAxisRay_eq_image_Ioi (R : Real) :
    xAxisRay R =
      (fun t : Real => ((t, 0) : PlanarInterface.Point)) '' Set.Ioi R := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · intro hp
    rcases hp with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

/-- The chosen x-axis ray is preconnected. -/
theorem xAxisRay_preconnected (R : Real) :
    IsPreconnected (xAxisRay R) := by
  rw [xAxisRay_eq_image_Ioi]
  exact isPreconnected_Ioi.image _ (by fun_prop)

theorem fst_image_xAxisRay (R : Real) :
    Prod.fst '' xAxisRay R = Set.Ioi R := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨p, hp, rfl⟩
    rcases hp with ⟨u, hu, rfl⟩
    exact hu
  · intro ht
    exact ⟨(t, 0), ⟨t, ht, rfl⟩, rfl⟩

/-- The chosen x-axis ray is unbounded. -/
theorem xAxisRay_unbounded (R : Real) :
    ¬ Bornology.IsBounded (xAxisRay R) := by
  intro hbounded
  have hfst : Bornology.IsBounded (Prod.fst '' xAxisRay R) :=
    Bornology.IsBounded.image_fst hbounded
  have hIoi : Bornology.IsBounded (Set.Ioi R) := by
    simpa [fst_image_xAxisRay R] using hfst
  exact
    (not_bddAbove_Ioi (a := R))
      (isBounded_iff_bddBelow_bddAbove.mp hIoi).2

theorem xAxisRay_subset_closedBall_compl
    (R : Real) (hR : 0 <= R) :
    xAxisRay R ⊆ (Metric.closedBall (0 : PlanarInterface.Point) R)ᶜ := by
  intro p hp hpball
  rcases hp with ⟨t, ht, rfl⟩
  have ht_nonneg : 0 <= t := le_trans hR ht.le
  have hdist : dist (0 : PlanarInterface.Point) (t, 0) <= R := by
    simpa [Metric.mem_closedBall] using hpball
  have hdist_eq : dist (0 : PlanarInterface.Point) (t, 0) = |t| := by
    rw [dist_eq_norm]
    simp
  have ht_abs : R < |t| := by
    simpa [abs_of_nonneg ht_nonneg] using ht
  exact not_le_of_gt ht_abs (hdist_eq ▸ hdist)

/-- Some rightward x-axis ray lies entirely in the drawing complement. -/
theorem exists_xAxisRay_subset_drawingComplement
    (C : _root_.UDConfig n) :
    Exists fun R : Real => 0 <= R /\ xAxisRay R ⊆ drawingComplement C := by
  rcases
      (Metric.isBounded_iff_subset_closedBall
        (0 : PlanarInterface.Point)).mp
        (embeddedEdgeSet_compact C).isBounded with
    ⟨A, hA⟩
  refine ⟨max A 0, le_max_right A 0, ?_⟩
  intro p hp
  rw [drawingComplement]
  intro hpdraw
  have hpballA : p ∈ Metric.closedBall (0 : PlanarInterface.Point) A :=
    hA hpdraw
  have hpballR : p ∈ Metric.closedBall (0 : PlanarInterface.Point) (max A 0) :=
    Metric.closedBall_subset_closedBall (le_max_left A 0) hpballA
  exact
    xAxisRay_subset_closedBall_compl
      (max A 0) (le_max_right A 0) hp hpballR

/-- The frontier of the whole drawing complement is carried by the embedded
unit-edge drawing.  Selecting the exterior component and proving which of
these drawing points lie on its frontier remains the S2 topology theorem. -/
theorem frontier_drawingComplement_subset_embeddedEdgeSet
    (C : _root_.UDConfig n) :
    frontier (drawingComplement C) ⊆ embeddedEdgeSet C := by
  intro p hp
  have hp' : p ∈ frontier (embeddedEdgeSet C) := by
    simpa [drawingComplement, frontier_compl] using hp
  simpa [(embeddedEdgeSet_closed C).closure_eq] using
    (frontier_subset_closure (s := embeddedEdgeSet C) hp')

end

end FinitePlaneDrawing
end Swanepoel
end ErdosProblems1066
