import ErdosProblems1066.Swanepoel.ConnectednessExtraction
import ErdosProblems1066.Swanepoel.MinimalConnectedness

/-!
# Closing the connectedness extraction route

This module supplies the concrete extraction hypothesis used by
`MinimalConnectedness`, then packages the resulting connectedness theorems for
minimal cleared failures.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ConnectednessExtractionClosure

open ConnectednessExtraction
open GraphBridge

/-- The concrete honest separator extraction obtained from reachability. -/
theorem honestAnticompleteSeparatorExtraction {n : Nat}
    (C : _root_.UDConfig n) :
    MinimalConnectedness.HonestAnticompleteSeparatorExtraction C := by
  intro hnot
  exact finAnticompletePartition_of_not_preconnected C hnot

/-- A minimal cleared failure has preconnected unit-distance graph. -/
theorem preconnected_of_minimalClearedFailure {n : Nat}
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (unitDistanceSimpleGraph C).Preconnected :=
  MinimalConnectedness.preconnected_of_minimalClearedFailure_of_separatorExtraction
    hmin (honestAnticompleteSeparatorExtraction C)

/-- A nonempty minimal cleared failure has connected unit-distance graph. -/
theorem connected_of_minimalClearedFailure {n : Nat}
    {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (unitDistanceSimpleGraph C).Connected := by
  haveI : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hn)
  exact
    MinimalConnectedness.connected_of_minimalClearedFailure_of_separatorExtraction
      hmin (honestAnticompleteSeparatorExtraction C)

/-- Absence of an anticomplete partition implies preconnectedness, using the
concrete extraction theorem. -/
theorem preconnected_of_no_anticomplete_partition {n : Nat}
    {C : _root_.UDConfig n}
    (hno :
      Not (Nonempty
        (ConnectednessSeparator.FinAnticompletePartition C))) :
    (unitDistanceSimpleGraph C).Preconnected :=
  MinimalConnectedness.preconnected_of_no_anticomplete_partition
    hno (honestAnticompleteSeparatorExtraction C)

/-- Connected version of `preconnected_of_no_anticomplete_partition`. -/
theorem connected_of_no_anticomplete_partition {n : Nat}
    {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hno :
      Not (Nonempty
        (ConnectednessSeparator.FinAnticompletePartition C))) :
    (unitDistanceSimpleGraph C).Connected := by
  haveI : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hn)
  exact
    MinimalConnectedness.connected_of_no_anticomplete_partition
      hno (honestAnticompleteSeparatorExtraction C)

end ConnectednessExtractionClosure
end Swanepoel
end ErdosProblems1066
