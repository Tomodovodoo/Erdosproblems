import Mathlib.Combinatorics.SimpleGraph.Clique
import ErdosProblems1066.Combinatorics.Independence
import ErdosProblems1066.Swanepoel.LocalConfigurations

/-!
# Swanepoel unit-distance graph bridge

This module gives the Swanepoel development a small, checked bridge from
`UDConfig` to the local graph and finite adjacency languages.  It deliberately
does not state any global Swanepoel lower bound.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace GraphBridge

open Combinatorics
open LocalConfigurations

noncomputable section

/-! ## Unit-distance adjacency as a local graph -/

/-- The unit-distance adjacency relation of a `UDConfig`, exposed under the
Swanepoel namespace. -/
def UnitDistanceAdj {n : Nat} (C : _root_.UDConfig n) (i j : Fin n) : Prop :=
  Combinatorics.UDConfig.UnitAdj C i j

lemma unitDistanceAdj_iff {n : Nat} (C : _root_.UDConfig n) (i j : Fin n) :
    UnitDistanceAdj C i j <-> eucDist (C.pts i) (C.pts j) = 1 :=
  Iff.rfl

lemma unitDistanceAdj_symm {n : Nat} (C : _root_.UDConfig n) {i j : Fin n}
    (h : UnitDistanceAdj C i j) :
    UnitDistanceAdj C j i := by
  simpa [UnitDistanceAdj, Combinatorics.UDConfig.UnitAdj, eucDist_comm] using h

lemma unitDistanceAdj_loopless {n : Nat} (C : _root_.UDConfig n) (i : Fin n) :
    Not (UnitDistanceAdj C i i) := by
  intro h
  simp [UnitDistanceAdj, Combinatorics.UDConfig.UnitAdj] at h

/-- The unit-distance graph of a `UDConfig`, as a Swanepoel `LocalGraph`. -/
def unitDistanceLocalGraph {n : Nat} (C : _root_.UDConfig n) :
    LocalGraph (Fin n) where
  Adj := UnitDistanceAdj C
  symm := unitDistanceAdj_symm C
  loopless := unitDistanceAdj_loopless C

@[simp]
lemma unitDistanceLocalGraph_adj {n : Nat} (C : _root_.UDConfig n) (i j : Fin n) :
    (unitDistanceLocalGraph C).Adj i j <-> eucDist (C.pts i) (C.pts j) = 1 :=
  Iff.rfl

/-- `UDConfig.IsIndep` is exactly independence in the associated local graph. -/
lemma isIndep_iff_localGraph_independent {n : Nat} (C : _root_.UDConfig n)
    {s : Finset (Fin n)} :
    C.IsIndep s <->
      Combinatorics.IsIndependentOn (unitDistanceLocalGraph C).Adj s := by
  exact Combinatorics.UDConfig.isIndep_iff_isIndependentOn_unitAdj C

/-! ## Mathlib `SimpleGraph` representation -/

/-- The unit-distance graph of a `UDConfig`, as a Mathlib `SimpleGraph`. -/
def unitDistanceSimpleGraph {n : Nat} (C : _root_.UDConfig n) :
    SimpleGraph (Fin n) where
  Adj i j := eucDist (C.pts i) (C.pts j) = 1
  symm := by
    intro i j h
    simpa [eucDist_comm] using h
  loopless := by
    refine ⟨fun i h => ?_⟩
    simp at h

@[simp]
lemma unitDistanceSimpleGraph_adj {n : Nat} (C : _root_.UDConfig n) (i j : Fin n) :
    (unitDistanceSimpleGraph C).Adj i j <-> eucDist (C.pts i) (C.pts j) = 1 :=
  Iff.rfl

lemma unitDistanceSimpleGraph_adj_iff_ne_and_dist {n : Nat}
    (C : _root_.UDConfig n) (i j : Fin n) :
    (unitDistanceSimpleGraph C).Adj i j <->
      i ≠ j /\ eucDist (C.pts i) (C.pts j) = 1 := by
  constructor
  · intro h
    exact ⟨(unitDistanceSimpleGraph C).ne_of_adj h, h⟩
  · intro h
    exact h.2

/-- `UDConfig.IsIndep` is exactly Mathlib `SimpleGraph` independence for the
associated unit-distance graph. -/
lemma isIndep_iff_simpleGraph_isIndepSet {n : Nat} (C : _root_.UDConfig n)
    {s : Finset (Fin n)} :
    C.IsIndep s <-> (unitDistanceSimpleGraph C).IsIndepSet (s : Set (Fin n)) := by
  constructor
  · intro h
    rw [SimpleGraph.isIndepSet_iff]
    intro i hi j hj hij hadj
    exact h i hi j hj hij hadj
  · intro h i hi j hj hij hadj
    rw [SimpleGraph.isIndepSet_iff] at h
    exact h hi hj hij hadj

/-- The local graph and Mathlib `SimpleGraph` views have the same adjacency. -/
lemma unitDistanceSimpleGraph_adj_iff_localGraph_adj {n : Nat}
    (C : _root_.UDConfig n) (i j : Fin n) :
    (unitDistanceSimpleGraph C).Adj i j <->
      (unitDistanceLocalGraph C).Adj i j :=
  Iff.rfl

/-! ## Finite adjacency representation -/

/-- The finite edge set of the unit-distance graph, stored once per unordered
edge by orienting each edge from the smaller index to the larger index. -/
noncomputable def unitDistanceEdges {n : Nat} (C : _root_.UDConfig n) :
    Finset (Fin n × Fin n) :=
  by
    classical
    exact (Finset.univ : Finset (Fin n × Fin n)).filter
      fun e => e.1 < e.2 /\ UnitDistanceAdj C e.1 e.2

/-- Adjacency induced by an oriented finite edge set of unordered edges. -/
def AdjFromEdges {n : Nat} (edges : Finset (Fin n × Fin n)) (i j : Fin n) : Prop :=
  (i, j) ∈ edges \/ (j, i) ∈ edges

lemma adjFromEdges_symm {n : Nat} (edges : Finset (Fin n × Fin n)) {i j : Fin n}
    (h : AdjFromEdges edges i j) :
    AdjFromEdges edges j i := by
  exact h.symm

lemma adjFromEdges_loopless_of_ordered {n : Nat} {edges : Finset (Fin n × Fin n)}
    (hordered : forall e : Fin n × Fin n, e ∈ edges -> e.1 < e.2) (i : Fin n) :
    Not (AdjFromEdges edges i i) := by
  intro h
  rcases h with h | h
  · exact (lt_irrefl i) (hordered (i, i) h)
  · exact (lt_irrefl i) (hordered (i, i) h)

/-- A finite edge set packaged as a Swanepoel `LocalGraph`. -/
def localGraphFromOrderedEdges {n : Nat} (edges : Finset (Fin n × Fin n))
    (hordered : forall e : Fin n × Fin n, e ∈ edges -> e.1 < e.2) :
    LocalGraph (Fin n) where
  Adj := AdjFromEdges edges
  symm := adjFromEdges_symm edges
  loopless := adjFromEdges_loopless_of_ordered hordered

lemma unitDistanceEdges_ordered {n : Nat} (C : _root_.UDConfig n)
    {e : Fin n × Fin n} (he : e ∈ unitDistanceEdges C) :
    e.1 < e.2 := by
  classical
  have h : e.1 < e.2 /\ UnitDistanceAdj C e.1 e.2 := by
    simpa only [unitDistanceEdges, Finset.mem_filter, Finset.mem_univ, true_and] using he
  exact h.1

lemma mem_unitDistanceEdges_iff {n : Nat} (C : _root_.UDConfig n) (i j : Fin n) :
    (i, j) ∈ unitDistanceEdges C <-> i < j /\ UnitDistanceAdj C i j := by
  classical
  simp [unitDistanceEdges]

/-- The finite edge-set adjacency recovers exactly the unit-distance adjacency. -/
lemma adjFrom_unitDistanceEdges_iff {n : Nat} (C : _root_.UDConfig n) (i j : Fin n) :
    AdjFromEdges (unitDistanceEdges C) i j <-> UnitDistanceAdj C i j := by
  constructor
  · intro h
    rcases h with h | h
    · exact (mem_unitDistanceEdges_iff C i j).1 h |>.2
    · exact unitDistanceAdj_symm C ((mem_unitDistanceEdges_iff C j i).1 h |>.2)
  · intro h
    rcases lt_trichotomy i j with hij | hij | hij
    · exact Or.inl ((mem_unitDistanceEdges_iff C i j).2 ⟨hij, h⟩)
    · exact False.elim ((unitDistanceAdj_loopless C i) (by simpa [hij] using h))
    · exact Or.inr ((mem_unitDistanceEdges_iff C j i).2
        ⟨hij, unitDistanceAdj_symm C h⟩)

/-- `UDConfig.IsIndep` can also be read from the finite unit-distance edge set. -/
lemma isIndep_iff_edges_independent {n : Nat} (C : _root_.UDConfig n)
    {s : Finset (Fin n)} :
    C.IsIndep s <->
      Combinatorics.IsIndependentOn (AdjFromEdges (unitDistanceEdges C)) s := by
  rw [isIndep_iff_localGraph_independent]
  constructor
  · intro h i hi j hj hij hadj
    exact h hi hj hij ((adjFrom_unitDistanceEdges_iff C i j).1 hadj)
  · intro h i hi j hj hij hadj
    exact h hi hj hij ((adjFrom_unitDistanceEdges_iff C i j).2 hadj)

/-- The graph built from the finite unit-distance edge set has the same
adjacency as the direct unit-distance local graph. -/
lemma localGraphFrom_unitDistanceEdges_adj_iff {n : Nat} (C : _root_.UDConfig n)
    (i j : Fin n) :
    (localGraphFromOrderedEdges (unitDistanceEdges C)
        (fun _ he => unitDistanceEdges_ordered C he)).Adj i j <->
      (unitDistanceLocalGraph C).Adj i j :=
  adjFrom_unitDistanceEdges_iff C i j

end

end GraphBridge
end Swanepoel
end ErdosProblems1066
