import ErdosProblems1066.Swanepoel.DegreeBound
import ErdosProblems1066.Swanepoel.GraphBridge

set_option linter.unusedDecidableInType false

/-!
# Swanepoel local exclusion lemmas

This module records small kernel-checked local facts used by the
common-neighbor and `K_{2,3}` route.  The geometric statements here are only
bridges to already-proved facts, or are explicitly graph-theoretic routing
lemmas; no global Swanepoel bound is asserted.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LocalExclusions

universe u

namespace LocalGraph

noncomputable section

variable {V : Type u}
variable (G : _root_.ErdosProblems1066.Swanepoel.LocalConfigurations.LocalGraph V)
variable {a b x y z w : V}

/-! ## Common-neighbor bookkeeping -/

lemma commonNeighbor_swap (h : G.CommonNeighbor a b x) :
    G.CommonNeighbor b a x :=
  ⟨h.2, h.1⟩

lemma commonNeighbor_left_ne (h : G.CommonNeighbor a b x) :
    x ≠ a := by
  intro hxa
  exact G.loopless a (by simpa [hxa] using h.1)

lemma commonNeighbor_right_ne (h : G.CommonNeighbor a b x) :
    x ≠ b := by
  intro hxb
  exact G.loopless b (by simpa [hxb] using h.2)

lemma isTriangleEdge_of_adj_commonNeighbor
    (hab : G.Adj a b) (hx : G.CommonNeighbor a b x) :
    G.IsTriangleEdge a b :=
  ⟨hab, ⟨x, hx⟩⟩

lemma not_commonNeighbor_of_isNontriangleEdge
    (h : G.IsNontriangleEdge a b) (x : V) :
    ¬ G.CommonNeighbor a b x :=
  h.2 x

lemma not_isTriangleEdge_of_isNontriangleEdge
    (h : G.IsNontriangleEdge a b) :
    ¬ G.IsTriangleEdge a b := by
  intro htri
  rcases htri.2 with ⟨x, hx⟩
  exact h.2 x hx

lemma not_isNontriangleEdge_of_isTriangleEdge
    (h : G.IsTriangleEdge a b) :
    ¬ G.IsNontriangleEdge a b := by
  intro hn
  rcases h.2 with ⟨x, hx⟩
  exact hn.2 x hx

/-! ## Finite neighbor and degree language -/

section Finite

variable [Fintype V] [DecidableEq V]

/-- The finite neighbor set of a vertex in a local graph. -/
def neighborFinset (v : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun u => G.Adj v u

/-- The finite common-neighbor set of two vertices. -/
def commonNeighborFinset (a b : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun u => G.CommonNeighbor a b u

/-- The local degree induced by `neighborFinset`. -/
def degree (v : V) : Nat :=
  (neighborFinset G v).card

omit [DecidableEq V] in
@[simp]
lemma mem_neighborFinset (v u : V) :
    u ∈ neighborFinset G v ↔ G.Adj v u := by
  simp [neighborFinset]

omit [DecidableEq V] in
@[simp]
lemma mem_commonNeighborFinset (a b u : V) :
    u ∈ commonNeighborFinset G a b ↔ G.CommonNeighbor a b u := by
  simp [commonNeighborFinset]

lemma degree_ge_two_of_two_neighbors
    (hy : G.Adj x y) (hz : G.Adj x z) (hyz : y ≠ z) :
    2 ≤ degree G x := by
  have hsubset : ({y, z} : Finset V) ⊆ neighborFinset G x := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · simpa [neighborFinset] using hy
    · simpa [neighborFinset] using hz
  have hcard : ({y, z} : Finset V).card = 2 := by
    simp [hyz]
  have := Finset.card_le_card hsubset
  simpa [degree, hcard] using this

lemma degree_ge_three_of_three_neighbors
    (hy : G.Adj x y) (hz : G.Adj x z) (hw : G.Adj x w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    3 ≤ degree G x := by
  have hsubset : ({y, z, w} : Finset V) ⊆ neighborFinset G x := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · simpa [neighborFinset] using hy
    · simpa [neighborFinset] using hz
    · simpa [neighborFinset] using hw
  have hcard : ({y, z, w} : Finset V).card = 3 := by
    simp [hyz, hyw, hzw]
  have := Finset.card_le_card hsubset
  simpa [degree, hcard] using this

lemma degree_ge_two_of_commonNeighbor
    (hab : a ≠ b) (hx : G.CommonNeighbor a b x) :
    2 ≤ degree G x :=
  degree_ge_two_of_two_neighbors G hx.1 hx.2 hab

lemma not_commonNeighbor_of_degree_le_one
    (hdeg : degree G x ≤ 1) (hab : a ≠ b) :
    ¬ G.CommonNeighbor a b x := by
  intro hx
  have htwo : 2 ≤ degree G x :=
    degree_ge_two_of_commonNeighbor G hab hx
  omega

lemma degree_ge_two_of_isTriangleEdge_left
    (h : G.IsTriangleEdge a b) :
    2 ≤ degree G a := by
  rcases h.2 with ⟨x, hx⟩
  exact degree_ge_two_of_two_neighbors G h.1 (G.symm hx.1)
    (by
      intro hbx
      exact commonNeighbor_right_ne G hx hbx.symm)

lemma degree_ge_two_of_isTriangleEdge_right
    (h : G.IsTriangleEdge a b) :
    2 ≤ degree G b := by
  rcases h.2 with ⟨x, hx⟩
  exact degree_ge_two_of_two_neighbors G (G.symm h.1) (G.symm hx.2)
    (by
      intro hax
      exact commonNeighbor_left_ne G hx hax.symm)

lemma not_isTriangleEdge_left_of_degree_le_one
    (hdeg : degree G a ≤ 1) :
    ¬ G.IsTriangleEdge a b := by
  intro htri
  have htwo := degree_ge_two_of_isTriangleEdge_left G htri
  omega

lemma not_isTriangleEdge_right_of_degree_le_one
    (hdeg : degree G b ≤ 1) :
    ¬ G.IsTriangleEdge a b := by
  intro htri
  have htwo := degree_ge_two_of_isTriangleEdge_right G htri
  omega

end Finite

/-! ## `K_{2,3}` routing -/

lemma hasK23_of_three_commonNeighbors
    (hab : a ≠ b)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : G.CommonNeighbor a b x)
    (hy : G.CommonNeighbor a b y)
    (hz : G.CommonNeighbor a b z) :
    _root_.ErdosProblems1066.Swanepoel.LocalConfigurations.HasK23 G := by
  exact ⟨{
    left0 := a
    left1 := b
    right0 := x
    right1 := y
    right2 := z
    left_ne := hab
    right01_ne := hxy
    right02_ne := hxz
    right12_ne := hyz
    right0_common := hx
    right1_common := hy
    right2_common := hz
  }⟩

lemma no_three_commonNeighbors_of_not_hasK23
    (hno : ¬ _root_.ErdosProblems1066.Swanepoel.LocalConfigurations.HasK23 G) (hab : a ≠ b) :
    ¬ (∃ x y z : V,
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        G.CommonNeighbor a b x ∧
        G.CommonNeighbor a b y ∧
        G.CommonNeighbor a b z) := by
  rintro ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩
  exact hno (hasK23_of_three_commonNeighbors G hab hxy hxz hyz hx hy hz)

section Finite

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma commonNeighborFinset_card_le_two_of_not_hasK23
    (hno : ¬ _root_.ErdosProblems1066.Swanepoel.LocalConfigurations.HasK23 G) (hab : a ≠ b) :
    (commonNeighborFinset G a b).card ≤ 2 := by
  by_contra hle
  have hlt : 2 < (commonNeighborFinset G a b).card :=
    Nat.lt_of_not_ge hle
  rcases (Finset.two_lt_card.mp hlt) with
    ⟨x, hxmem, y, hymem, z, hzmem, hxy, hxz, hyz⟩
  have hx : G.CommonNeighbor a b x := by
    simpa using (mem_commonNeighborFinset G a b x).1 hxmem
  have hy : G.CommonNeighbor a b y := by
    simpa using (mem_commonNeighborFinset G a b y).1 hymem
  have hz : G.CommonNeighbor a b z := by
    simpa using (mem_commonNeighborFinset G a b z).1 hzmem
  exact hno (hasK23_of_three_commonNeighbors G hab hxy hxz hyz hx hy hz)

omit [DecidableEq V] in
lemma exists_hasK23_of_commonNeighborFinset_card_ge_three
    (hab : a ≠ b) (hcard : 3 ≤ (commonNeighborFinset G a b).card) :
    _root_.ErdosProblems1066.Swanepoel.LocalConfigurations.HasK23 G := by
  have hlt : 2 < (commonNeighborFinset G a b).card := by omega
  rcases (Finset.two_lt_card.mp hlt) with
    ⟨x, hxmem, y, hymem, z, hzmem, hxy, hxz, hyz⟩
  exact hasK23_of_three_commonNeighbors G hab hxy hxz hyz
    ((mem_commonNeighborFinset G a b x).1 hxmem)
    ((mem_commonNeighborFinset G a b y).1 hymem)
    ((mem_commonNeighborFinset G a b z).1 hzmem)

lemma degree_ge_three_left0_of_K23Pattern
    (P : _root_.ErdosProblems1066.Swanepoel.LocalConfigurations.K23Pattern G) :
    3 ≤ degree G P.left0 :=
  degree_ge_three_of_three_neighbors G
    (G.symm P.right0_common.1)
    (G.symm P.right1_common.1)
    (G.symm P.right2_common.1)
    P.right01_ne P.right02_ne P.right12_ne

lemma degree_ge_three_left1_of_K23Pattern
    (P : _root_.ErdosProblems1066.Swanepoel.LocalConfigurations.K23Pattern G) :
    3 ≤ degree G P.left1 :=
  degree_ge_three_of_three_neighbors G
    (G.symm P.right0_common.2)
    (G.symm P.right1_common.2)
    (G.symm P.right2_common.2)
    P.right01_ne P.right02_ne P.right12_ne

end Finite

end

end LocalGraph

/-! ## Unit-distance graph wrappers -/

namespace UnitDistance

open GraphBridge

noncomputable section

variable {n : Nat} (C : _root_.UDConfig n)

lemma unitDistance_commonNeighbor_iff (a b x : Fin n) :
    (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor a b x <->
      eucDist (C.pts x) (C.pts a) = 1 /\
        eucDist (C.pts x) (C.pts b) = 1 :=
  Iff.rfl

lemma unitDistance_neighborFinset_eq (center : Fin n) :
    LocalGraph.neighborFinset (GraphBridge.unitDistanceLocalGraph C) center =
      (Finset.univ : Finset (Fin n)).filter
        (fun j => j ≠ center /\ eucDist (C.pts j) (C.pts center) = 1) := by
  classical
  ext j
  constructor
  · intro hj
    have hdist_center_j : eucDist (C.pts center) (C.pts j) = 1 := by
      simpa [LocalGraph.neighborFinset, GraphBridge.unitDistanceLocalGraph_adj] using hj
    have hne : j ≠ center := by
      intro h
      exact GraphBridge.unitDistanceAdj_loopless C center
        (by
          subst h
          exact hdist_center_j)
    have hdist_j_center : eucDist (C.pts j) (C.pts center) = 1 := by
      simpa [eucDist_comm] using hdist_center_j
    simp [hne, hdist_j_center]
  · intro hj
    rcases (Finset.mem_filter.mp hj).2 with ⟨_hne, hdist_j_center⟩
    have hdist_center_j : eucDist (C.pts center) (C.pts j) = 1 := by
      simpa [eucDist_comm] using hdist_j_center
    simpa [LocalGraph.neighborFinset, GraphBridge.unitDistanceLocalGraph_adj] using
      hdist_center_j

theorem unitDistanceLocalGraph_degree_le_six (center : Fin n) :
    LocalGraph.degree (GraphBridge.unitDistanceLocalGraph C) center ≤ 6 := by
  classical
  rw [LocalGraph.degree, unitDistance_neighborFinset_eq C center]
  exact DegreeBound.UDConfig.unitDistanceNeighborSet_card_le_six C center

theorem unitDistance_commonNeighborFinset_card_le_two_of_not_hasK23
    (hno : ¬ _root_.ErdosProblems1066.Swanepoel.LocalConfigurations.HasK23
      (GraphBridge.unitDistanceLocalGraph C)) {a b : Fin n}
    (hab : a ≠ b) :
    (LocalGraph.commonNeighborFinset (GraphBridge.unitDistanceLocalGraph C) a b).card ≤ 2 := by
  classical
  exact LocalGraph.commonNeighborFinset_card_le_two_of_not_hasK23
    (GraphBridge.unitDistanceLocalGraph C)
    hno hab

end

end UnitDistance

end LocalExclusions
end Swanepoel
end ErdosProblems1066
