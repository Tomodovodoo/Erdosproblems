import ErdosProblems1066.Swanepoel.BoundaryWalkClassificationConcrete

/-!
# Finite partitions for concrete boundary-walk classifications

This module adds finset-level partition lemmas for the concrete boundary walk
classes.  The representatives are the boundary indices already used by
`BoundaryWalkClassificationConcrete`; the lemmas here only prove disjointness,
coverage, and cardinal projections for those finite index classes.
-/

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryWalkClassificationConcrete
namespace OuterBoundaryClassificationInputs

open BoundaryClassification
open BoundaryCounting
open BoundaryWalkConstruction
open FaceReduction
open PlanarInterface

noncomputable section

variable {n : Nat}
variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}

/-! ## Edge-class partitions -/

/-- Boundary indices whose concrete edge is triangular, as a finset. -/
def triangleEdgeIndexFinset
    (_D : OuterBoundaryClassificationInputs P) :
    Finset (Fin P.outerCycle.length) := by
  classical
  exact Finset.univ.filter fun k =>
    IsTriangleEdge G (P.outerCycle.edge k)

/-- Boundary indices whose concrete edge is nontriangular, as a finset. -/
def nontriangleEdgeIndexFinset
    (_D : OuterBoundaryClassificationInputs P) :
    Finset (Fin P.outerCycle.length) := by
  classical
  exact Finset.univ.filter fun k =>
    IsNontriangleEdge G (P.outerCycle.edge k)

@[simp]
theorem mem_triangleEdgeIndexFinset
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    k ∈ D.triangleEdgeIndexFinset <->
      IsTriangleEdge G (P.outerCycle.edge k) := by
  classical
  simp [triangleEdgeIndexFinset]

@[simp]
theorem mem_nontriangleEdgeIndexFinset
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    k ∈ D.nontriangleEdgeIndexFinset <->
      IsNontriangleEdge G (P.outerCycle.edge k) := by
  classical
  simp [nontriangleEdgeIndexFinset]

@[simp]
theorem card_triangleEdgeIndexFinset
    (D : OuterBoundaryClassificationInputs P) :
    D.triangleEdgeIndexFinset.card = Fintype.card D.triangleEdgeIndices := by
  classical
  unfold triangleEdgeIndexFinset triangleEdgeIndices
  rw [Fintype.card_subtype]

@[simp]
theorem card_nontriangleEdgeIndexFinset
    (D : OuterBoundaryClassificationInputs P) :
    D.nontriangleEdgeIndexFinset.card =
      Fintype.card D.nontriangleEdgeIndices := by
  classical
  unfold nontriangleEdgeIndexFinset nontriangleEdgeIndices
  rw [Fintype.card_subtype]

/-- Triangle and nontriangle boundary-edge index finsets are disjoint. -/
theorem edgeIndexFinsets_disjoint
    (D : OuterBoundaryClassificationInputs P) :
    Disjoint D.triangleEdgeIndexFinset D.nontriangleEdgeIndexFinset := by
  classical
  rw [Finset.disjoint_left]
  intro k htri hnon
  exact
    ((isNontriangleEdge_iff_not_isTriangleEdge P k).1
      ((mem_nontriangleEdgeIndexFinset D k).1 hnon))
      ((mem_triangleEdgeIndexFinset D k).1 htri)

/-- Triangle and nontriangle boundary-edge index finsets cover all boundary
edge indices. -/
theorem edgeIndexFinsets_cover
    (D : OuterBoundaryClassificationInputs P) :
    D.triangleEdgeIndexFinset ∪ D.nontriangleEdgeIndexFinset =
      Finset.univ := by
  classical
  ext k
  by_cases htri : IsTriangleEdge G (P.outerCycle.edge k)
  · simp [htri]
  · have hnon : IsNontriangleEdge G (P.outerCycle.edge k) :=
      isNontriangleEdge_of_not_isTriangleEdge P k htri
    simp [htri, hnon]

/-- Finset cardinal form of the triangle/nontriangle boundary-edge partition. -/
theorem edgeIndexFinsets_card_add
    (D : OuterBoundaryClassificationInputs P) :
    D.triangleEdgeIndexFinset.card + D.nontriangleEdgeIndexFinset.card =
      P.outerCycle.length := by
  classical
  have hcard := Finset.card_union_of_disjoint (edgeIndexFinsets_disjoint D)
  rw [edgeIndexFinsets_cover D] at hcard
  simpa using hcard.symm

/-- Subtype cardinal form of the triangle/nontriangle boundary-edge
partition. -/
theorem edgeIndices_card_add
    (D : OuterBoundaryClassificationInputs P) :
    Fintype.card D.triangleEdgeIndices +
        Fintype.card D.nontriangleEdgeIndices =
      P.outerCycle.length := by
  simpa using (edgeIndexFinsets_card_add D)

@[simp]
theorem boundaryBookkeeping_triangleEdgeCount
    (D : OuterBoundaryClassificationInputs P) :
    D.boundaryBookkeeping.triangleEdgeCount =
      Fintype.card D.triangleEdgeIndices := by
  change
    Fintype.card
        D.toOuterBoundaryWalkBookkeeping.data.triangleEdgeIndices =
      Fintype.card D.triangleEdgeIndices
  exact Fintype.card_congr D.walkTriangleEdgeIndicesEquiv

@[simp]
theorem boundaryBookkeeping_triangleEdgeCount_eq_triangleEdgeIndexFinset_card
    (D : OuterBoundaryClassificationInputs P) :
    D.boundaryBookkeeping.triangleEdgeCount =
      D.triangleEdgeIndexFinset.card := by
  simp

@[simp]
theorem counts_b_eq_nontriangleEdgeIndexFinset_card
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.b = D.nontriangleEdgeIndexFinset.card := by
  simp

/-- The projected triangle-edge count plus the `b` count is the boundary
length. -/
theorem boundaryBookkeeping_triangleEdgeCount_add_counts_b
    (D : OuterBoundaryClassificationInputs P) :
    D.boundaryBookkeeping.triangleEdgeCount + D.counts.b =
      P.outerCycle.length := by
  simpa using (edgeIndices_card_add D)

/-! ## Degree-class partitions -/

/-- Boundary indices whose concrete vertex has ambient degree `d`, as a
finset. -/
def degreeIndexFinset
    (_D : OuterBoundaryClassificationInputs P) (d : Nat) :
    Finset (Fin P.outerCycle.length) := by
  classical
  exact Finset.univ.filter fun k =>
    IsDegree G d (P.outerCycle.vertex k)

/-- Boundary indices whose vertex has ambient degree three, as a finset. -/
def degree3IndexFinset
    (D : OuterBoundaryClassificationInputs P) :
    Finset (Fin P.outerCycle.length) :=
  D.degreeIndexFinset 3

/-- Boundary indices whose vertex has ambient degree four, as a finset. -/
def degree4IndexFinset
    (D : OuterBoundaryClassificationInputs P) :
    Finset (Fin P.outerCycle.length) :=
  D.degreeIndexFinset 4

/-- Boundary indices whose vertex has ambient degree five, as a finset. -/
def degree5IndexFinset
    (D : OuterBoundaryClassificationInputs P) :
    Finset (Fin P.outerCycle.length) :=
  D.degreeIndexFinset 5

/-- Boundary indices whose vertex has ambient degree six, as a finset. -/
def degree6IndexFinset
    (D : OuterBoundaryClassificationInputs P) :
    Finset (Fin P.outerCycle.length) :=
  D.degreeIndexFinset 6

@[simp]
theorem mem_degreeIndexFinset
    (D : OuterBoundaryClassificationInputs P) (d : Nat)
    (k : Fin P.outerCycle.length) :
    k ∈ D.degreeIndexFinset d <->
      IsDegree G d (P.outerCycle.vertex k) := by
  classical
  simp [degreeIndexFinset]

@[simp]
theorem mem_degree3IndexFinset
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    k ∈ D.degree3IndexFinset <->
      IsDegree3 G (P.outerCycle.vertex k) := by
  simp [degree3IndexFinset, IsDegree3]

@[simp]
theorem mem_degree4IndexFinset
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    k ∈ D.degree4IndexFinset <->
      IsDegree4 G (P.outerCycle.vertex k) := by
  simp [degree4IndexFinset, IsDegree4]

@[simp]
theorem mem_degree5IndexFinset
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    k ∈ D.degree5IndexFinset <->
      IsDegree5 G (P.outerCycle.vertex k) := by
  simp [degree5IndexFinset, IsDegree5]

@[simp]
theorem mem_degree6IndexFinset
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    k ∈ D.degree6IndexFinset <->
      IsDegree6 G (P.outerCycle.vertex k) := by
  simp [degree6IndexFinset, IsDegree6]

@[simp]
theorem card_degree3IndexFinset
    (D : OuterBoundaryClassificationInputs P) :
    D.degree3IndexFinset.card = Fintype.card D.degree3Indices := by
  classical
  unfold degree3IndexFinset degreeIndexFinset degree3Indices IsDegree3
  rw [Fintype.card_subtype]

@[simp]
theorem card_degree4IndexFinset
    (D : OuterBoundaryClassificationInputs P) :
    D.degree4IndexFinset.card = Fintype.card D.degree4Indices := by
  classical
  unfold degree4IndexFinset degreeIndexFinset degree4Indices IsDegree4
  rw [Fintype.card_subtype]

@[simp]
theorem card_degree5IndexFinset
    (D : OuterBoundaryClassificationInputs P) :
    D.degree5IndexFinset.card = Fintype.card D.degree5Indices := by
  classical
  unfold degree5IndexFinset degreeIndexFinset degree5Indices IsDegree5
  rw [Fintype.card_subtype]

@[simp]
theorem card_degree6IndexFinset
    (D : OuterBoundaryClassificationInputs P) :
    D.degree6IndexFinset.card = Fintype.card D.degree6Indices := by
  classical
  unfold degree6IndexFinset degreeIndexFinset degree6Indices IsDegree6
  rw [Fintype.card_subtype]

/-- Generic disjointness for two distinct ambient-degree index finsets. -/
theorem degreeIndexFinsets_disjoint
    (D : OuterBoundaryClassificationInputs P) {d e : Nat}
    (hne : d ≠ e) :
    Disjoint (D.degreeIndexFinset d) (D.degreeIndexFinset e) := by
  classical
  rw [Finset.disjoint_left]
  intro k hd he
  have hkd :
      ambientDegree G (P.outerCycle.vertex k) = d := by
    exact ((mem_degreeIndexFinset D d k).1 hd)
  have hke :
      ambientDegree G (P.outerCycle.vertex k) = e := by
    exact ((mem_degreeIndexFinset D e k).1 he)
  exact hne (hkd.symm.trans hke)

theorem degree3_degree4_disjoint
    (D : OuterBoundaryClassificationInputs P) :
    Disjoint D.degree3IndexFinset D.degree4IndexFinset := by
  simpa [degree3IndexFinset, degree4IndexFinset] using
    degreeIndexFinsets_disjoint (D := D) (d := 3) (e := 4)
      (by norm_num)

theorem degree3_degree5_disjoint
    (D : OuterBoundaryClassificationInputs P) :
    Disjoint D.degree3IndexFinset D.degree5IndexFinset := by
  simpa [degree3IndexFinset, degree5IndexFinset] using
    degreeIndexFinsets_disjoint (D := D) (d := 3) (e := 5)
      (by norm_num)

theorem degree3_degree6_disjoint
    (D : OuterBoundaryClassificationInputs P) :
    Disjoint D.degree3IndexFinset D.degree6IndexFinset := by
  simpa [degree3IndexFinset, degree6IndexFinset] using
    degreeIndexFinsets_disjoint (D := D) (d := 3) (e := 6)
      (by norm_num)

theorem degree4_degree5_disjoint
    (D : OuterBoundaryClassificationInputs P) :
    Disjoint D.degree4IndexFinset D.degree5IndexFinset := by
  simpa [degree4IndexFinset, degree5IndexFinset] using
    degreeIndexFinsets_disjoint (D := D) (d := 4) (e := 5)
      (by norm_num)

theorem degree4_degree6_disjoint
    (D : OuterBoundaryClassificationInputs P) :
    Disjoint D.degree4IndexFinset D.degree6IndexFinset := by
  simpa [degree4IndexFinset, degree6IndexFinset] using
    degreeIndexFinsets_disjoint (D := D) (d := 4) (e := 6)
      (by norm_num)

theorem degree5_degree6_disjoint
    (D : OuterBoundaryClassificationInputs P) :
    Disjoint D.degree5IndexFinset D.degree6IndexFinset := by
  simpa [degree5IndexFinset, degree6IndexFinset] using
    degreeIndexFinsets_disjoint (D := D) (d := 5) (e := 6)
      (by norm_num)

/-- Every concrete boundary vertex index belongs to one of the four degree
classes. -/
theorem degree_eq_three_or_four_or_five_or_six
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    IsDegree3 G (P.outerCycle.vertex k) \/
      IsDegree4 G (P.outerCycle.vertex k) \/
      IsDegree5 G (P.outerCycle.vertex k) \/
      IsDegree6 G (P.outerCycle.vertex k) := by
  unfold IsDegree3 IsDegree4 IsDegree5 IsDegree6 IsDegree
  have hlo : 3 <= ambientDegree G (P.outerCycle.vertex k) :=
    D.degree_ge_three k
  have hhi : ambientDegree G (P.outerCycle.vertex k) <= 6 :=
    ambientDegree_le_six G (P.outerCycle.vertex k)
  omega

/-- The four concrete degree-class finsets cover all boundary vertex indices. -/
theorem degreeIndexFinsets_cover
    (D : OuterBoundaryClassificationInputs P) :
    ((D.degree3IndexFinset ∪ D.degree4IndexFinset) ∪
        D.degree5IndexFinset) ∪ D.degree6IndexFinset =
      Finset.univ := by
  classical
  ext k
  constructor
  · intro _h
    simp
  · intro _h
    rcases degree_eq_three_or_four_or_five_or_six D k with
      h3 | h4 | h5 | h6
    · exact
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_union.mpr <| Or.inl <|
              (mem_degree3IndexFinset D k).2 h3
    · exact
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_union.mpr <| Or.inr <|
              (mem_degree4IndexFinset D k).2 h4
    · exact
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr <|
            (mem_degree5IndexFinset D k).2 h5
    · exact
        Finset.mem_union.mpr <| Or.inr <|
          (mem_degree6IndexFinset D k).2 h6

theorem degree34IndexFinset_disjoint_degree5
    (D : OuterBoundaryClassificationInputs P) :
    Disjoint (D.degree3IndexFinset ∪ D.degree4IndexFinset)
      D.degree5IndexFinset := by
  classical
  rw [Finset.disjoint_left]
  intro k h34 h5
  rcases Finset.mem_union.mp h34 with h3 | h4
  · exact (Finset.disjoint_left.mp (degree3_degree5_disjoint D)) h3 h5
  · exact (Finset.disjoint_left.mp (degree4_degree5_disjoint D)) h4 h5

theorem degree345IndexFinset_disjoint_degree6
    (D : OuterBoundaryClassificationInputs P) :
    Disjoint
      ((D.degree3IndexFinset ∪ D.degree4IndexFinset) ∪
        D.degree5IndexFinset)
      D.degree6IndexFinset := by
  classical
  rw [Finset.disjoint_left]
  intro k h345 h6
  rcases Finset.mem_union.mp h345 with h34 | h5
  · rcases Finset.mem_union.mp h34 with h3 | h4
    · exact (Finset.disjoint_left.mp (degree3_degree6_disjoint D)) h3 h6
    · exact (Finset.disjoint_left.mp (degree4_degree6_disjoint D)) h4 h6
  · exact (Finset.disjoint_left.mp (degree5_degree6_disjoint D)) h5 h6

/-- Finset cardinal form of the degree-class boundary-vertex partition. -/
theorem degreeIndexFinsets_card_add
    (D : OuterBoundaryClassificationInputs P) :
    D.degree3IndexFinset.card + D.degree4IndexFinset.card +
        D.degree5IndexFinset.card + D.degree6IndexFinset.card =
      P.outerCycle.length := by
  classical
  have h34 :=
    Finset.card_union_of_disjoint (degree3_degree4_disjoint D)
  have h345 :=
    Finset.card_union_of_disjoint (degree34IndexFinset_disjoint_degree5 D)
  have h3456 :=
    Finset.card_union_of_disjoint (degree345IndexFinset_disjoint_degree6 D)
  rw [degreeIndexFinsets_cover D] at h3456
  have hfin :
      (Finset.univ : Finset (Fin P.outerCycle.length)).card =
        P.outerCycle.length := by
    simp
  omega

/-- Subtype cardinal form of the degree-class boundary-vertex partition. -/
theorem degreeIndices_card_add
    (D : OuterBoundaryClassificationInputs P) :
    Fintype.card D.degree3Indices + Fintype.card D.degree4Indices +
        Fintype.card D.degree5Indices + Fintype.card D.degree6Indices =
      P.outerCycle.length := by
  simpa using (degreeIndexFinsets_card_add D)

@[simp]
theorem counts_d3_eq_degree3IndexFinset_card
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.d3 = D.degree3IndexFinset.card := by
  simp

@[simp]
theorem counts_d4_eq_degree4IndexFinset_card
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.d4 = D.degree4IndexFinset.card := by
  simp

@[simp]
theorem counts_d5_eq_degree5IndexFinset_card
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.d5 = D.degree5IndexFinset.card := by
  simp

@[simp]
theorem counts_d6_eq_degree6IndexFinset_card
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.d6 = D.degree6IndexFinset.card := by
  simp

/-- The four projected degree counts add up to the boundary length. -/
theorem counts_degree_sum_eq_length
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.d3 + D.counts.d4 + D.counts.d5 + D.counts.d6 =
      P.outerCycle.length := by
  simpa using (degreeIndices_card_add D)

end

end OuterBoundaryClassificationInputs
end BoundaryWalkClassificationConcrete
end Swanepoel
end ErdosProblems1066
