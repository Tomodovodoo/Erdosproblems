import ErdosProblems1066.PachToth.Arithmetic
import ErdosProblems1066.PachToth.FiniteGraph

/-!
# Pach--Toth Chain Combinatorics

This module proves the checked combinatorial chain step used by the
Pach--Toth `5 / 16` upper-bound construction.

It is conditional on the geometric realization layer: the hypotheses say that
each block intersection is independent for the certified finite block graph,
and that the geometric connector edges between consecutive blocks enforce the
four forbidden vertices in the next block.
-/

namespace ErdosProblems1066
namespace PachToth
namespace Chain

open FiniteGraph
open FiniteGraph.LocalVertex
open Arithmetic

/-- A selected subset in each block of a cyclic chain. -/
abbrev BlockSelection (k : Nat) : Type :=
  Fin k -> Finset LocalVertex

/-- Each block selection is independent in the certified first-block graph. -/
def BlocksIndependent {k : Nat} (blocks : BlockSelection k) : Prop :=
  forall i : Fin k, IsIndependent (blocks i)

/-- If a block contains both connector vertices, the next block cannot contain
the four vertices hit by the connector edges. -/
def ConnectorRule {k : Nat} (hk : 0 < k) (blocks : BlockSelection k) : Prop :=
  forall i : Fin k,
    T2_2 ∈ blocks i ->
    T4_0 ∈ blocks i ->
    forall v : LocalVertex,
      v ∈ blocks (cyclicSucc hk i) -> v ∉ nextForbidden

/-- A full block forces the following block to have at most four selected
vertices, provided the connector rule is available. -/
theorem full_block_forces_next_small {k : Nat} (hk : 0 < k)
    (blocks : BlockSelection k)
    (hindep : BlocksIndependent blocks)
    (hconnect : ConnectorRule hk blocks)
    (i : Fin k)
    (hfull : (blocks i).card = 6) :
    (blocks (cyclicSucc hk i)).card <= 4 := by
  have hfull_set :
      blocks i = extractedSixSet :=
    unique_size_six_independent (blocks i) (hindep i) hfull
  have hpq : T2_2 ∈ blocks i /\ T4_0 ∈ blocks i := by
    rw [hfull_set]
    exact extractedSixSet_contains_connectors
  exact next_block_after_forbidden_le_four
    (blocks (cyclicSucc hk i))
    (hindep (cyclicSucc hk i))
    (hconnect i hpq.1 hpq.2)

/-- The selected vertices across a closed chain of `k` certified blocks are at
most `5 * k`, assuming the connector rule between consecutive blocks. -/
theorem selected_card_le_five_mul {k : Nat} (hk : 0 < k)
    (blocks : BlockSelection k)
    (hindep : BlocksIndependent blocks)
    (hconnect : ConnectorRule hk blocks) :
    (Finset.univ.sum fun i : Fin k => (blocks i).card) <= 5 * k := by
  apply CyclicAverageSixFour hk (fun i : Fin k => (blocks i).card)
  · intro i
    exact alpha_le_six (blocks i) (hindep i)
  · intro i hfull
    exact full_block_forces_next_small hk blocks hindep hconnect i hfull

end Chain
end PachToth
end ErdosProblems1066
