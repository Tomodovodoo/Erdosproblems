import ErdosProblems1066.PachToth.CrossBlock

/-!
# Pach--Toth Figure 2 edge-role table

This file records a proof-used finite subset of the Figure 2 edge roles as
plain combinatorial data.  The lemmas below only connect the named roles to the
already checked Boolean graph `FiniteGraph.adj` and directed successor relation
`CrossBlock.NextConnector`; no geometric realization claim is made here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace Figure2EdgeTable

open FiniteGraph
open FiniteGraph.LocalVertex

/-- Local first-block edge roles used by the finite independence proof. -/
inductive LocalEdgeRole where
  | rootBlocksNonFarthest
  | oneTwoBridge
  | forceT2Connector
  | forceT3Farthest
  | forceT4Connector
  deriving DecidableEq, Repr, Fintype

/-- The oriented representatives of the local proof-used edges.  They are
representatives only: `FiniteGraph.adj_symm` supplies the reverse direction. -/
def localEdgeRole : LocalVertex -> LocalVertex -> Option LocalEdgeRole
  | .r, .tri 0 1 => some .rootBlocksNonFarthest
  | .r, .tri 0 2 => some .rootBlocksNonFarthest
  | .r, .tri 1 0 => some .rootBlocksNonFarthest
  | .r, .tri 1 2 => some .rootBlocksNonFarthest
  | .tri 0 1, .tri 1 0 => some .oneTwoBridge
  | .tri 0 0, .tri 2 0 => some .forceT2Connector
  | .tri 0 0, .tri 2 1 => some .forceT2Connector
  | .tri 1 1, .tri 3 1 => some .forceT3Farthest
  | .tri 1 1, .tri 3 2 => some .forceT3Farthest
  | .tri 3 0, .tri 4 1 => some .forceT4Connector
  | .tri 3 0, .tri 4 2 => some .forceT4Connector
  | _, _ => none

/-- Every local role-table entry is an existing edge of the checked finite
graph. -/
theorem localEdgeRole_adj :
    forall u v role,
      localEdgeRole u v = some role -> adj u v = true := by
  decide

/-- The reverse of every local role-table entry is also adjacent in the checked
finite graph. -/
theorem localEdgeRole_adj_symm :
    forall u v role,
      localEdgeRole u v = some role -> adj v u = true := by
  decide

/-- Figure 2 farthest representatives used by the current six-set proof. -/
def farthest : Fin 5 -> LocalVertex
  | 0 => T0_0
  | 1 => T1_1
  | 2 => T2_2
  | 3 => T3_0
  | 4 => T4_0

/-- The proof-used farthest representatives are exactly the five non-root
vertices in the extracted independent six-set. -/
theorem farthest_mem_extractedSixSet :
    forall t : Fin 5, farthest t ∈ extractedSixSet := by
  decide

/-- The source-side connector names corresponding to the paper labels used by
the current finite proof layer. -/
inductive ConnectorSourceName where
  | p
  | q
  deriving DecidableEq, Repr, Fintype

/-- The two connector-source vertices selected in the unique six-set. -/
def connectorSource : ConnectorSourceName -> LocalVertex
  | .p => T2_2
  | .q => T4_0

/-- The connector sources are among the proof-used farthest representatives. -/
theorem connectorSource_mem_extractedSixSet :
    forall c : ConnectorSourceName, connectorSource c ∈ extractedSixSet := by
  decide

/-- Directed next-block connector roles used by the chain proof. -/
inductive NextConnectorRole where
  | pToUpper
  | pToLower
  | qToUpper
  | qToLower
  deriving DecidableEq, Repr, Fintype

/-- The complete proof-used directed successor-connector table. -/
def nextConnectorRole : LocalVertex -> LocalVertex -> Option NextConnectorRole
  | .tri 2 2, .tri 1 1 => some .pToUpper
  | .tri 2 2, .tri 1 2 => some .pToLower
  | .tri 4 0, .tri 0 0 => some .qToUpper
  | .tri 4 0, .tri 0 2 => some .qToLower
  | _, _ => none

/-- Every named successor-connector role is present in
`CrossBlock.NextConnector`. -/
theorem nextConnectorRole_nextConnector :
    forall u v role,
      nextConnectorRole u v = some role -> CrossBlock.NextConnector u v := by
  decide

/-- Conversely, every currently checked successor connector has a named role in
this finite table. -/
theorem nextConnector_has_role :
    forall u v,
      CrossBlock.NextConnector u v ->
        exists role, nextConnectorRole u v = some role := by
  decide

/-- The target vertices of the named successor connectors are exactly the
vertices forbidden in the next block after both connector sources are chosen. -/
theorem nextConnectorRole_target_mem_nextForbidden :
    forall u v role,
      nextConnectorRole u v = some role -> v ∈ nextForbidden := by
  decide

/-- The source vertices of the named successor connectors are exactly the two
connector-source vertices from the extracted six-set. -/
theorem nextConnectorRole_source_is_connectorSource :
    forall u v role,
      nextConnectorRole u v = some role ->
        u = connectorSource .p \/ u = connectorSource .q := by
  decide

end Figure2EdgeTable
end PachToth
end ErdosProblems1066
