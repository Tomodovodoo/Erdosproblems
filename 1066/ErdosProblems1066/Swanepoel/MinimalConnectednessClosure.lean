import ErdosProblems1066.Swanepoel.ConnectednessExtraction
import ErdosProblems1066.Swanepoel.MinimalConnectedness

/-!
# Connectedness closure for minimal cleared failures

This module closes the first connectedness layer for minimal cleared failures.
The separator witness is the concrete one extracted in `ConnectednessExtraction`;
minimality rules it out through `ConnectednessSeparator`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalConnectednessClosure

open GraphBridge

noncomputable section

/-- The concrete disconnectedness-to-separator extraction for unit-distance
graphs, packaged in the form expected by `MinimalConnectedness`. -/
theorem honestAnticompleteSeparatorExtraction_of_connectednessExtraction
    {n : Nat} (C : _root_.UDConfig n) :
    MinimalConnectedness.HonestAnticompleteSeparatorExtraction C :=
  ConnectednessExtraction.finAnticompletePartition_of_not_preconnected C

/-- If no finite anticomplete two-block partition exists, the unit-distance
graph is preconnected. -/
theorem unitDistanceSimpleGraph_preconnected_of_no_anticomplete_partition
    {n : Nat} {C : _root_.UDConfig n}
    (hno :
      Not (Nonempty (ConnectednessSeparator.FinAnticompletePartition C))) :
    (unitDistanceSimpleGraph C).Preconnected :=
  MinimalConnectedness.preconnected_of_no_anticomplete_partition hno
    (honestAnticompleteSeparatorExtraction_of_connectednessExtraction C)

/-- Connected form of
`unitDistanceSimpleGraph_preconnected_of_no_anticomplete_partition`. -/
theorem unitDistanceSimpleGraph_connected_of_no_anticomplete_partition
    {n : Nat} {C : _root_.UDConfig n} [Nonempty (Fin n)]
    (hno :
      Not (Nonempty (ConnectednessSeparator.FinAnticompletePartition C))) :
    (unitDistanceSimpleGraph C).Connected :=
  MinimalConnectedness.connected_of_no_anticomplete_partition hno
    (honestAnticompleteSeparatorExtraction_of_connectednessExtraction C)

/-- A minimal cleared failure has at least one vertex. -/
theorem fin_nonempty_of_minimalClearedFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (Fin n) := by
  cases n with
  | zero =>
      exfalso
      exact (MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin) (by
        refine ⟨∅, ?_, ?_⟩
        · intro i hi j _hj _hij _hunit
          simp at hi
        · norm_num [MinimalCounterexample.ClearedEightThirtyOneBound])
  | succ n =>
      exact ⟨⟨0, Nat.succ_pos n⟩⟩

/-- Minimal cleared failures have preconnected unit-distance graphs. -/
theorem unitDistanceSimpleGraph_preconnected_of_minimalClearedFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (unitDistanceSimpleGraph C).Preconnected :=
  MinimalConnectedness.preconnected_of_minimalClearedFailure_of_separatorExtraction
    hmin
    (honestAnticompleteSeparatorExtraction_of_connectednessExtraction C)

/-- Minimal cleared failures have connected unit-distance graphs. -/
theorem unitDistanceSimpleGraph_connected_of_minimalClearedFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (unitDistanceSimpleGraph C).Connected where
  preconnected :=
    unitDistanceSimpleGraph_preconnected_of_minimalClearedFailure hmin
  nonempty := fin_nonempty_of_minimalClearedFailure hmin

end

end MinimalConnectednessClosure
end Swanepoel
end ErdosProblems1066
