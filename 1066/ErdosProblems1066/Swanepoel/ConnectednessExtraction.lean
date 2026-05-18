import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import ErdosProblems1066.Swanepoel.ConnectednessSeparator

/-!
# Extracting anticomplete partitions from disconnected unit-distance graphs

This module connects Mathlib's `SimpleGraph` connected-component API to the
finite anticomplete partition structure used by `ConnectednessSeparator`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ConnectednessExtraction

open GraphBridge
open ConnectednessSeparator

noncomputable section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace ConnectedComponent

variable [Fintype V] [DecidableEq V] (c : G.ConnectedComponent)

/-- The finite vertex set of a connected component. -/
noncomputable def suppFinset : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∈ c.supp

/-- The finite complement of a connected component. -/
noncomputable def complSuppFinset : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∉ c.supp

@[simp]
lemma mem_suppFinset {v : V} :
    v ∈ suppFinset c ↔ v ∈ c.supp := by
  classical
  simp [suppFinset]

@[simp]
lemma mem_complSuppFinset {v : V} :
    v ∈ complSuppFinset c ↔ v ∉ c.supp := by
  classical
  simp [complSuppFinset]

lemma suppFinset_nonempty :
    (suppFinset c).Nonempty := by
  obtain ⟨v, hv⟩ := _root_.SimpleGraph.ConnectedComponent.nonempty_supp c
  exact ⟨v, by simpa using hv⟩

lemma complSuppFinset_nonempty
    (hcompl : (c.suppᶜ : Set V).Nonempty) :
    (complSuppFinset c).Nonempty := by
  obtain ⟨v, hv⟩ := hcompl
  exact ⟨v, by simpa using hv⟩

lemma disjoint_suppFinset_complSuppFinset :
    Disjoint (suppFinset c) (complSuppFinset c) := by
  rw [Finset.disjoint_left]
  intro v hvLeft hvRight
  exact (mem_complSuppFinset c).1 hvRight ((mem_suppFinset c).1 hvLeft)

lemma suppFinset_union_complSuppFinset :
    suppFinset c ∪ complSuppFinset c = Finset.univ := by
  ext v
  by_cases hv : v ∈ c.supp <;> simp [hv]

lemma not_adj_supp_compl {i j : V}
    (hi : i ∈ suppFinset c) (hj : j ∈ complSuppFinset c) :
    ¬ G.Adj i j := by
  intro hij
  exact ((mem_complSuppFinset c).1 hj)
    (_root_.SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp c
      ((mem_suppFinset c).1 hi) hij)

end ConnectedComponent

variable (G : SimpleGraph V)

lemma not_preconnected_iff_exists_unreachable :
    ¬ G.Preconnected ↔ ∃ u v : V, ¬ G.Reachable u v := by
  constructor
  · contrapose!
    intro h u v
    exact h u v
  · rintro ⟨u, v, huv⟩ hconn
    exact huv (hconn u v)

end SimpleGraph

open SimpleGraph

variable {n : Nat} (C : _root_.UDConfig n)

/-- If the unit-distance graph is not preconnected, one connected component and
its complement form a finite anticomplete partition of `Fin n`. -/
theorem finAnticompletePartition_of_not_preconnected
    (hdisc : ¬ (unitDistanceSimpleGraph C).Preconnected) :
    Nonempty (FinAnticompletePartition C) := by
  classical
  let G := unitDistanceSimpleGraph C
  obtain ⟨u, v, huv⟩ :=
    (SimpleGraph.not_preconnected_iff_exists_unreachable G).1 hdisc
  let c : G.ConnectedComponent := G.connectedComponentMk u
  have hvNotMem : v ∉ c.supp := by
    intro hv
    exact huv (c.reachable_of_mem_supp
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem) hv)
  have hcompl : (c.suppᶜ : Set (Fin n)).Nonempty := ⟨v, hvNotMem⟩
  refine ⟨{
    left := SimpleGraph.ConnectedComponent.suppFinset c
    right := SimpleGraph.ConnectedComponent.complSuppFinset c
    left_nonempty := SimpleGraph.ConnectedComponent.suppFinset_nonempty c
    right_nonempty := SimpleGraph.ConnectedComponent.complSuppFinset_nonempty c hcompl
    disjoint := SimpleGraph.ConnectedComponent.disjoint_suppFinset_complSuppFinset c
    cover := SimpleGraph.ConnectedComponent.suppFinset_union_complSuppFinset c
    anticomplete := ?_
  }⟩
  intro i hi j hj
  exact SimpleGraph.ConnectedComponent.not_adj_supp_compl c hi hj

/-- Non-connectedness gives an anticomplete partition for nonempty finite
unit-distance graphs.  The hypothesis `0 < n` excludes the empty graph, where
`¬ Connected` is true but no nonempty two-block partition can exist. -/
theorem finAnticompletePartition_of_not_connected
    (hn : 0 < n)
    (hdisc : ¬ (unitDistanceSimpleGraph C).Connected) :
    Nonempty (FinAnticompletePartition C) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine finAnticompletePartition_of_not_preconnected C ?_
  intro hpre
  exact hdisc ⟨hpre⟩

end

end ConnectednessExtraction
end Swanepoel
end ErdosProblems1066
