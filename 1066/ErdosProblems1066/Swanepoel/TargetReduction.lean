import ErdosProblems1066.Swanepoel.Bridge
import ErdosProblems1066.Swanepoel.CounterexamplePipeline
import ErdosProblems1066.Swanepoel.MinimalCounterexample

/-!
# Swanepoel Target Reduction

This file keeps the public `8 / 31` target honest: it proves only that the
proposition-valued target follows from a per-configuration cleared bound.
The geometric and minimal-counterexample machinery needed to prove that
per-configuration bound remains explicit elsewhere.
-/

namespace ErdosProblems1066
namespace Swanepoel

open MinimalCounterexample

/-- The in-progress Swanepoel target follows from a cleared `8 / 31` independent
set in every unit-distance configuration. -/
theorem targetLowerBoundEightThirtyOne_of_clearedBound
    (H :
      forall (n : Nat) (C : _root_.UDConfig n),
        Exists fun s : Finset (Fin n) =>
          C.IsIndep s /\ ClearedEightThirtyOneBound n s.card) :
    targetLowerBoundEightThirtyOne := by
  intro n C
  obtain ⟨s, hs, hbound⟩ := H n C
  exact ⟨s, hs, hbound⟩

/-- The in-progress Swanepoel target follows from the cleared-bound predicate
used by the counterexample pipeline. -/
theorem targetLowerBoundEightThirtyOne_of_pipelineCleared
    (H :
      forall (n : Nat) (C : _root_.UDConfig n),
        CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet C) :
    targetLowerBoundEightThirtyOne := by
  apply targetLowerBoundEightThirtyOne_of_clearedBound
  intro n C
  exact H n C

end Swanepoel
end ErdosProblems1066
