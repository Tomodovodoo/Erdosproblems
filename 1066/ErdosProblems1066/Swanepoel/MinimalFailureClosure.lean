import ErdosProblems1066.Swanepoel.MinimalGraphFacts
import ErdosProblems1066.Swanepoel.M8PipelineClosure
import ErdosProblems1066.Swanepoel.TargetReduction

set_option autoImplicit false

/-!
# Closure from minimal cleared failures

This file proves only the well-founded closure step: an actual failure yields a
minimal actual failure, so any honest eliminator for minimal cleared failures
implies the per-configuration cleared `8 / 31` bound and hence the public
Swanepoel target.

The final sections expose conditional surfaces for downstream paper-fact
matrices.  They keep the remaining assumptions explicit: either supply the
existing M8 pipeline eliminator, or supply a pointwise fact family together
with the checked consumer that makes each minimal failure contradictory.  No
unconditional lower-bound theorem is introduced here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureClosure

open CounterexamplePipeline
open MinimalGraphFacts

universe u

noncomputable section

/-- Any counterexample to the cleared pipeline predicate has a minimal
counterexample at some cardinality. -/
theorem exists_minimalClearedFailure_of_not_hasCleared {n : Nat}
    {C : _root_.UDConfig n}
    (hC : Not (HasClearedEightThirtyOneIndependentSet C)) :
    Exists fun m : Nat =>
      Exists fun Cmin : _root_.UDConfig m =>
        IsMinimalClearedFailure Cmin := by
  classical
  let Bad : Nat -> Prop := fun m =>
    Exists fun Cbad : _root_.UDConfig m =>
      Not (HasClearedEightThirtyOneIndependentSet Cbad)
  have hBad : Exists Bad := Exists.intro n (Exists.intro C hC)
  let m := Nat.find hBad
  cases Nat.find_spec hBad with
  | intro Cmin hCmin =>
      refine Exists.intro m (Exists.intro Cmin ?_)
      constructor
      case left =>
        exact hCmin
      case right =>
        intro k Csmall hk
        by_contra hSmall
        have hkBad : Bad k := Exists.intro Csmall hSmall
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
  cases exists_minimalClearedFailure_of_not_hasCleared (C := C) hC with
  | intro m hm =>
      cases hm with
      | intro Cmin hmin =>
          exact hElim Cmin hmin

/-- A negated minimal-failure theorem is enough to get the cleared pipeline
predicate for every unit-distance configuration. -/
theorem hasCleared_of_no_minimalClearedFailure
    (hNoMin :
      forall {n : Nat} (C : _root_.UDConfig n),
        Not (IsMinimalClearedFailure C)) :
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
        Not (IsMinimalClearedFailure C)) :
    targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_minimalClearedFailure_eliminator
    (fun C hmin => hNoMin C hmin)

/-! ## Existing M8 pipeline closure -/

/-- The existing M8 separated-construction eliminator is the pipeline-level
assumption currently sufficient to close every minimal cleared failure. -/
abbrev MinimalFailureM8SeparatedConstructionEliminator : Prop :=
  M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator

/-- The separated-construction pipeline eliminator rules out every minimal
cleared failure. -/
theorem no_minimalClearedFailure_of_m8SeparatedConstructionEliminator
    (hbuild : MinimalFailureM8SeparatedConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_separatedConstructionEliminator
    hbuild

/-- The separated-construction pipeline eliminator supplies the cleared
pipeline predicate for every unit-distance configuration. -/
theorem hasCleared_of_m8SeparatedConstructionEliminator
    (hbuild : MinimalFailureM8SeparatedConstructionEliminator) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C :=
  hasCleared_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8SeparatedConstructionEliminator hbuild)

/-- Conditional target wrapper from the existing M8 separated-construction
pipeline eliminator. -/
theorem targetLowerBoundEightThirtyOne_of_m8SeparatedConstructionEliminator
    (hbuild : MinimalFailureM8SeparatedConstructionEliminator) :
    targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_pipelineCleared
    (hasCleared_of_m8SeparatedConstructionEliminator hbuild)

/-! ## Generic pointwise paper-fact closure -/

/-- A minimal and dependency-light interface for downstream paper-fact
matrices: for each indexed minimal failure, provide the remaining facts and a
checked consumer showing those facts are contradictory. -/
theorem no_minimalClearedFailure_of_pointwiseFacts
    (Facts :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C -> Type u)
    (hfacts :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Facts C hmin)
    (hconsume :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Facts C hmin -> False) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  intro n C hmin
  exact hconsume C hmin (hfacts C hmin)

/-- A pointwise remaining-facts family and its checked consumer supply the
cleared pipeline predicate. -/
theorem hasCleared_of_pointwiseFacts
    (Facts :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C -> Type u)
    (hfacts :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Facts C hmin)
    (hconsume :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Facts C hmin -> False) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C :=
  hasCleared_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_pointwiseFacts Facts hfacts hconsume)

/-- Conditional target wrapper for any downstream refined paper-fact matrix.

The remaining assumptions are exactly the pointwise fact supplier and the
checked consumer for those facts.  Downstream matrix files can instantiate
`Facts` with their refined row type without making this base closure import
the matrix.
-/
theorem targetLowerBoundEightThirtyOne_of_pointwiseFacts
    (Facts :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C -> Type u)
    (hfacts :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Facts C hmin)
    (hconsume :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Facts C hmin -> False) :
    targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_pipelineCleared
    (hasCleared_of_pointwiseFacts Facts hfacts hconsume)

end

end MinimalFailureClosure
end Swanepoel
end ErdosProblems1066
