import ErdosProblems1066.PachToth.Chain

/-!
# Pach--Toth Block Partition Accounting

This module contains only finite indexing bookkeeping.  It gives a canonical
noncomputable bijection between vertices indexed by `Fin (16 * k)` and pairs
`(block, local vertex)`, then proves that the induced local block selections
have cardinalities summing to the original selected set.
-/

namespace ErdosProblems1066
namespace PachToth
namespace BlockPartition

open Chain
open FiniteGraph

noncomputable section

/-- A finite equivalence between the transcribed local vertex type and
`Fin 16`, using the checked cardinality of the local graph. -/
def localVertexEquivFin16 : Equiv LocalVertex (Fin 16) :=
  Fintype.equivFinOfCardEq localVertex_card

/-- Pair a cyclic block index with a local vertex, then encode it as a global
`Fin (16 * k)` vertex index. -/
def blockLocalEquiv (k : Nat) :
    Equiv (Prod (Fin k) LocalVertex) (Fin (16 * k)) :=
  ((Equiv.prodCongr (Equiv.refl (Fin k)) localVertexEquivFin16).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm k 16))))

/-- Decode a global vertex index into its block and local vertex. -/
def vertexBlockLocal (k : Nat) (v : Fin (16 * k)) :
    Prod (Fin k) LocalVertex :=
  (blockLocalEquiv k).symm v

/-- Reindex a global selected set by block and local vertex. -/
def indexedSelection (k : Nat) (s : Finset (Fin (16 * k))) :
    Finset (Prod (Fin k) LocalVertex) :=
  s.image (vertexBlockLocal k)

/-- The local vertices selected in a fixed block. -/
def blockSelection (k : Nat) (s : Finset (Fin (16 * k))) :
    BlockSelection k :=
  fun i : Fin k =>
    ((indexedSelection k s).filter fun p : Prod (Fin k) LocalVertex => p.1 = i).image
      Prod.snd

theorem indexedSelection_card (k : Nat) (s : Finset (Fin (16 * k))) :
    (indexedSelection k s).card = s.card := by
  unfold indexedSelection vertexBlockLocal
  rw [Finset.card_image_of_injective]
  exact (blockLocalEquiv k).symm.injective

theorem filter_snd_injective {k : Nat}
    (S : Finset (Prod (Fin k) LocalVertex)) (i : Fin k) :
    Set.InjOn Prod.snd
      (((S.filter fun p : Prod (Fin k) LocalVertex => p.1 = i) :
        Finset (Prod (Fin k) LocalVertex)) : Set (Prod (Fin k) LocalVertex)) := by
  intro p hp q hq hsnd
  exact Prod.ext
    ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) hsnd

theorem blockSelection_card (k : Nat) (s : Finset (Fin (16 * k))) (i : Fin k) :
    ((blockSelection k s) i).card =
      ((indexedSelection k s).filter fun p : Prod (Fin k) LocalVertex => p.1 = i).card := by
  unfold blockSelection
  rw [Finset.card_image_of_injOn]
  exact filter_snd_injective (indexedSelection k s) i

theorem sum_block_fibers_card {k : Nat}
    (S : Finset (Prod (Fin k) LocalVertex)) :
    (Finset.univ.sum fun i : Fin k =>
      (S.filter fun p : Prod (Fin k) LocalVertex => p.1 = i).card) = S.card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_fiberwise]

/-- The canonical block selections account for exactly all selected global
vertices. -/
theorem card_eq_sum_blockSelection (k : Nat) (s : Finset (Fin (16 * k))) :
    s.card = Finset.univ.sum fun i : Fin k => ((blockSelection k s) i).card := by
  calc
    s.card = (indexedSelection k s).card := (indexedSelection_card k s).symm
    _ = Finset.univ.sum fun i : Fin k =>
        ((indexedSelection k s).filter fun p : Prod (Fin k) LocalVertex => p.1 = i).card :=
          (sum_block_fibers_card (indexedSelection k s)).symm
    _ = Finset.univ.sum fun i : Fin k => ((blockSelection k s) i).card := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (blockSelection_card k s i).symm

end

end BlockPartition
end PachToth
end ErdosProblems1066
