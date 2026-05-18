import ErdosProblems1066.PachToth.Chain

/-!
# Pach--Toth Cross-Block Connectors

This module isolates the finite directed connector relation between one
Pach--Toth block and the next block.  It is disjoint from the geometric
realization layer: selecting vertices in two consecutive local blocks is
cross-independent when it contains no edge of this finite relation.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlock

open FiniteGraph
open FiniteGraph.LocalVertex
open Arithmetic
open Chain

/-- The directed connector edges from one block to the next block. -/
def nextConnectorEdges : Finset (LocalVertex × LocalVertex) :=
  {(T2_2, T1_1), (T2_2, T1_2), (T4_0, T0_0), (T4_0, T0_2)}

/-- The finite next-block connector relation. -/
def NextConnector (u v : LocalVertex) : Prop :=
  (u, v) ∈ nextConnectorEdges

instance instDecidableNextConnector (u v : LocalVertex) :
    Decidable (NextConnector u v) := by
  unfold NextConnector
  infer_instance

/-- The connector relation has exactly the two stated targets from `T2_2`
and the two stated targets from `T4_0`. -/
theorem nextForbidden_connector_source :
    forall v : LocalVertex,
      v ∈ nextForbidden -> NextConnector T2_2 v \/ NextConnector T4_0 v := by
  decide

/-- Two local selections in consecutive blocks are cross-independent when no
selected vertex in the first block is joined by a directed connector edge to a
selected vertex in the next block. -/
def CrossIndependent (left right : Finset LocalVertex) : Prop :=
  forall u : LocalVertex,
    u ∈ left ->
    forall v : LocalVertex,
      v ∈ right -> Not (NextConnector u v)

/-- Cross-independence around the cyclic block chain. -/
def CyclicCrossIndependent {k : Nat} (hk : 0 < k)
    (blocks : BlockSelection k) : Prop :=
  forall i : Fin k, CrossIndependent (blocks i) (blocks (cyclicSucc hk i))

/-- If a block selects both connector sources, cross-independence forbids every
vertex in `nextForbidden` from the following block. -/
theorem crossIndependent_forbids_nextForbidden
    {left right : Finset LocalVertex}
    (hcross : CrossIndependent left right)
    (hT2 : T2_2 ∈ left)
    (hT4 : T4_0 ∈ left)
    {v : LocalVertex}
    (hv : v ∈ right) :
    v ∉ nextForbidden := by
  intro hv_forbidden
  rcases nextForbidden_connector_source v hv_forbidden with hconn | hconn
  · exact hcross T2_2 hT2 v hv hconn
  · exact hcross T4_0 hT4 v hv hconn

/-- Cyclic cross-independence implies the connector rule used by the existing
chain theorem. -/
theorem connectorRule_of_cyclicCrossIndependent {k : Nat} (hk : 0 < k)
    {blocks : BlockSelection k}
    (hcross : CyclicCrossIndependent hk blocks) :
    ConnectorRule hk blocks := by
  intro i hT2 hT4 v hv
  exact crossIndependent_forbids_nextForbidden
    (hcross i) hT2 hT4 hv

/-- The selected vertices across a closed chain of `k` certified blocks are at
most `5 * k`, assuming block independence and the finite cross-block connector
relation between consecutive blocks. -/
theorem selected_card_le_five_mul {k : Nat} (hk : 0 < k)
    (blocks : BlockSelection k)
    (hindep : BlocksIndependent blocks)
    (hcross : CyclicCrossIndependent hk blocks) :
    (Finset.univ.sum fun i : Fin k => (blocks i).card) <= 5 * k := by
  exact Chain.selected_card_le_five_mul hk blocks hindep
    (connectorRule_of_cyclicCrossIndependent hk hcross)

end CrossBlock
end PachToth
end ErdosProblems1066
