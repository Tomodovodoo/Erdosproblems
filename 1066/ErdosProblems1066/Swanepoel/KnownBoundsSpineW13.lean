import ErdosProblems1066.KnownBounds
import ErdosProblems1066.Swanepoel.M8MinimalFailureEliminatorInterface
import ErdosProblems1066.Swanepoel.MinimalFailurePaperFactMatrix

set_option autoImplicit false

/-!
# W13 Swanepoel known-bounds spine

This standalone module connects the currently checked Swanepoel closure
surfaces to the target proposition and to the same per-configuration lower-bound
shape used by `KnownBounds`.

The wrappers below are intentionally conditional.  They do not add a public
unconditional `8 / 31` theorem to `KnownBounds`; each theorem explicitly carries
the remaining closure input it consumes.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace KnownBoundsSpineW13

universe u v

noncomputable section

/-- The W13-facing row-family condition supplied by the current M8 interface. -/
abbrev PipelineRefinedFactMatrixRowFamily :=
  M8MinimalFailureEliminatorInterface.M8PipelineRefinedFactMatrixRowFamily

/-- The current turn/window/no-early eliminator condition. -/
abbrev TurnWindowNoEarlyEliminator : Prop :=
  M8MinimalFailureEliminatorInterface.MinimalFailureM8TurnWindowNoEarlyEliminator

/-- The refined remaining paper-facts family condition. -/
abbrev RefinedPaperFactsFamily :=
  M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFactsFamily.{u, v}

/-- The exact target-input family recorded by the paper-fact matrix. -/
abbrev ExactTargetInputs :=
  MinimalFailurePaperFactMatrix.TargetLowerBoundEightThirtyOneInputs.{u, v}

/-! ## Target-proposition wrappers -/

/-- The pipeline-facing refined row family proves the Swanepoel target. -/
theorem targetLowerBoundEightThirtyOne_of_pipelineRefinedFactMatrixRowFamily
    (H : PipelineRefinedFactMatrixRowFamily) :
    targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

/-- The turn/window/no-early eliminator proves the Swanepoel target. -/
theorem targetLowerBoundEightThirtyOne_of_turnWindowNoEarlyEliminator
    (H : TurnWindowNoEarlyEliminator) :
    targetLowerBoundEightThirtyOne :=
  M8MinimalFailureEliminatorInterface.targetLowerBoundEightThirtyOne_of_turnWindowNoEarlyEliminator
    H

/-- The refined paper-facts family proves the Swanepoel target. -/
theorem targetLowerBoundEightThirtyOne_of_refinedPaperFactsFamily
    (H : RefinedPaperFactsFamily) :
    targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

/-- The exact target-input family proves the Swanepoel target. -/
theorem targetLowerBoundEightThirtyOne_of_exactTargetInputs
    (H : ExactTargetInputs) :
    targetLowerBoundEightThirtyOne :=
  MinimalFailurePaperFactMatrix.targetLowerBoundEightThirtyOne_consumes_exact_inputs
    H

/-! ## KnownBounds-shaped lower-bound wrappers -/

/-- Per-configuration `8 / 31` lower-bound statement from the pipeline-facing
refined row family. -/
theorem lower_bound_eight_thirty_one_of_pipelineRefinedFactMatrixRowFamily
    (H : PipelineRefinedFactMatrixRowFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_pipelineRefinedFactMatrixRowFamily H n C

/-- Per-configuration `8 / 31` lower-bound statement from the
turn/window/no-early eliminator. -/
theorem lower_bound_eight_thirty_one_of_turnWindowNoEarlyEliminator
    (H : TurnWindowNoEarlyEliminator)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_turnWindowNoEarlyEliminator H n C

/-- Per-configuration `8 / 31` lower-bound statement from the refined
paper-facts family. -/
theorem lower_bound_eight_thirty_one_of_refinedPaperFactsFamily
    (H : RefinedPaperFactsFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_refinedPaperFactsFamily H n C

/-- Per-configuration `8 / 31` lower-bound statement from the exact target
input family. -/
theorem lower_bound_eight_thirty_one_of_exactTargetInputs
    (H : ExactTargetInputs)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_exactTargetInputs H n C

end

end KnownBoundsSpineW13

/-! ## Source-specific public-style aliases -/

/-- Source-specific conditional alias for the W13 pipeline-facing refined row
family route. -/
theorem lower_bound_eight_thirty_one_of_w13_pipelineRefinedFactMatrixRowFamily
    (H : KnownBoundsSpineW13.PipelineRefinedFactMatrixRowFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  KnownBoundsSpineW13.lower_bound_eight_thirty_one_of_pipelineRefinedFactMatrixRowFamily
    H n C

/-- Source-specific conditional alias for the W13 exact target-input route. -/
theorem lower_bound_eight_thirty_one_of_w13_exactTargetInputs
    (H : KnownBoundsSpineW13.ExactTargetInputs)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  KnownBoundsSpineW13.lower_bound_eight_thirty_one_of_exactTargetInputs H n C

end Swanepoel

namespace Verified

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound from the
W13 pipeline-facing refined row family route. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w13_pipelineRefinedFactMatrixRowFamily
    (H : Swanepoel.KnownBoundsSpineW13.PipelineRefinedFactMatrixRowFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.lower_bound_eight_thirty_one_of_w13_pipelineRefinedFactMatrixRowFamily
    H n C

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound from the
W13 exact target-input route. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w13_exactTargetInputs
    (H : Swanepoel.KnownBoundsSpineW13.ExactTargetInputs)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.lower_bound_eight_thirty_one_of_w13_exactTargetInputs H n C

end Verified
end ErdosProblems1066
