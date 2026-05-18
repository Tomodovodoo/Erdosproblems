import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import ErdosProblems1066.Swanepoel.ConnectednessSeparator

/-!
# Connectedness of minimal cleared failures

This file is the final routing layer for connectedness.  It deliberately does
not prove a no-cut-vertex theorem and does not manufacture a separator: an
honest extraction of an anticomplete two-block partition from disconnectedness
is kept as an explicit hypothesis.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalConnectedness

open ConnectednessSeparator
open GraphBridge

noncomputable section

/-- An honest separator extraction for the unit-distance graph of `C`.

The hypothesis says that if the unit-distance graph is not preconnected, then
one can exhibit a nonempty finite anticomplete two-block partition of its
vertices. -/
def HonestAnticompleteSeparatorExtraction {n : Nat}
    (C : _root_.UDConfig n) : Prop :=
  Not (unitDistanceSimpleGraph C).Preconnected ->
    Nonempty (ConnectednessSeparator.FinAnticompletePartition C)

/-- Minimal cleared failures have no finite anticomplete two-block partition. -/
theorem no_anticomplete_partition_of_minimalClearedFailure {n : Nat}
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Not (Nonempty (ConnectednessSeparator.FinAnticompletePartition C)) := by
  intro hP
  cases hP with
  | intro P =>
  exact P.contradiction_of_minimalClearedFailure hmin

/-- Conditional connectedness core: if disconnectedness honestly extracts an
anticomplete partition, then a minimal cleared failure is preconnected. -/
theorem preconnected_of_minimalClearedFailure_of_separatorExtraction {n : Nat}
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hextract : HonestAnticompleteSeparatorExtraction C) :
    (unitDistanceSimpleGraph C).Preconnected := by
  by_contra hnot
  exact no_anticomplete_partition_of_minimalClearedFailure hmin (hextract hnot)

/-- Connectedness form of
`preconnected_of_minimalClearedFailure_of_separatorExtraction`.  The explicit
`Nonempty (Fin n)` assumption is exactly the extra data in Mathlib's
`SimpleGraph.Connected` predicate beyond preconnectedness. -/
theorem connected_of_minimalClearedFailure_of_separatorExtraction {n : Nat}
    {C : _root_.UDConfig n} [Nonempty (Fin n)]
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hextract : HonestAnticompleteSeparatorExtraction C) :
    (unitDistanceSimpleGraph C).Connected where
  preconnected :=
    preconnected_of_minimalClearedFailure_of_separatorExtraction hmin hextract
  nonempty := inferInstance

/-- A reusable form independent of minimality: absence of anticomplete
partitions plus an honest extraction already gives preconnectedness. -/
theorem preconnected_of_no_anticomplete_partition {n : Nat}
    {C : _root_.UDConfig n}
    (hno : Not (Nonempty (ConnectednessSeparator.FinAnticompletePartition C)))
    (hextract : HonestAnticompleteSeparatorExtraction C) :
    (unitDistanceSimpleGraph C).Preconnected := by
  by_contra hnot
  exact hno (hextract hnot)

/-- Connected version of `preconnected_of_no_anticomplete_partition`. -/
theorem connected_of_no_anticomplete_partition {n : Nat}
    {C : _root_.UDConfig n} [Nonempty (Fin n)]
    (hno : Not (Nonempty (ConnectednessSeparator.FinAnticompletePartition C)))
    (hextract : HonestAnticompleteSeparatorExtraction C) :
    (unitDistanceSimpleGraph C).Connected where
  preconnected := preconnected_of_no_anticomplete_partition hno hextract
  nonempty := inferInstance

end

end MinimalConnectedness
end Swanepoel
end ErdosProblems1066
