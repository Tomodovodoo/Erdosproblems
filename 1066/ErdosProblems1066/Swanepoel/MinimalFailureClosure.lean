import ErdosProblems1066.Swanepoel.MinimalGraphFacts
import ErdosProblems1066.Swanepoel.TargetReduction

/-!
# Closure from minimal cleared failures

This file proves only the well-founded closure step: an actual failure yields a
minimal actual failure, so any honest eliminator for minimal cleared failures
implies the per-configuration cleared `8 / 31` bound and hence the public
Swanepoel target.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureClosure

open CounterexamplePipeline
open MinimalGraphFacts

noncomputable section

/-- Any counterexample to the cleared pipeline predicate has a minimal
counterexample at some cardinality. -/
theorem exists_minimalClearedFailure_of_not_hasCleared {n : Nat}
    {C : _root_.UDConfig n}
    (hC : ¬ HasClearedEightThirtyOneIndependentSet C) :
    Exists fun m : Nat =>
      Exists fun Cmin : _root_.UDConfig m =>
        IsMinimalClearedFailure Cmin := by
  classical
  let Bad : Nat -> Prop := fun m =>
    Exists fun Cbad : _root_.UDConfig m =>
      ¬ HasClearedEightThirtyOneIndependentSet Cbad
  have hBad : Exists Bad := ⟨n, C, hC⟩
  let m := Nat.find hBad
  rcases Nat.find_spec hBad with ⟨Cmin, hCmin⟩
  refine ⟨m, Cmin, ?_⟩
  constructor
  · exact hCmin
  · intro k Csmall hk
    by_contra hSmall
    have hkBad : Bad k := ⟨Csmall, hSmall⟩
    exact (Nat.find_min hBad hk) hkBad

/-- Eliminating every minimal cleared failure gives the cleared pipeline
predicate for every unit-distance configuration. -/
theorem hasCleared_of_minimalClearedFailure_eliminator
    (hElim :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C -> False) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C := by
  intro n C
  by_contra hC
  rcases exists_minimalClearedFailure_of_not_hasCleared (C := C) hC with
    ⟨m, Cmin, hmin⟩
  exact hElim Cmin hmin

/-- A negated minimal-failure theorem is enough to get the cleared pipeline
predicate for every unit-distance configuration. -/
theorem hasCleared_of_no_minimalClearedFailure
    (hNoMin :
      forall {n : Nat} (C : _root_.UDConfig n),
        ¬ IsMinimalClearedFailure C) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C :=
  hasCleared_of_minimalClearedFailure_eliminator
    (fun C hmin => hNoMin C hmin)

/-- Eliminating every minimal cleared failure proves the public Swanepoel
`8 / 31` lower-bound target. -/
theorem targetLowerBoundEightThirtyOne_of_minimalClearedFailure_eliminator
    (hElim :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C -> False) :
    targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_pipelineCleared
    (hasCleared_of_minimalClearedFailure_eliminator hElim)

/-- A negated minimal-failure theorem proves the public Swanepoel `8 / 31`
lower-bound target. -/
theorem targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (hNoMin :
      forall {n : Nat} (C : _root_.UDConfig n),
        ¬ IsMinimalClearedFailure C) :
    targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_minimalClearedFailure_eliminator
    (fun C hmin => hNoMin C hmin)

end

end MinimalFailureClosure
end Swanepoel
end ErdosProblems1066
