import ErdosProblems1066.KnownBounds
import ErdosProblems1066.Swanepoel.SwanepoelRemainingObligationsW9
import ErdosProblems1066.Swanepoel.SwanepoelW8ClosureMatrix
import ErdosProblems1066.Swanepoel.TargetReduction

set_option autoImplicit false

/-!
# Swanepoel W10 target facade

This module is a small conditional facade from the checked W8/W9 Swanepoel
matrices to the public Swanepoel target proposition.  It deliberately does not
add any `KnownBounds` theorem: the imported public facade remains reserved for
unconditional bounds whose proof terms are fully closed.

The W10-facing `Matrix` below is target-level data only: a proof that all
minimal cleared failures are eliminated.  W8/W9 matrix adapters populate that
field from the existing checked conditional matrices, and the target projection
then goes through `MinimalGraphFacts` and `TargetReduction`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelTargetFacadeW10

open MinimalGraphFacts

universe u

noncomputable section

/-- Local name for the Swanepoel `8 / 31` target proposition. -/
abbrev Target : Prop :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

/-- Target-level exclusion of all minimal cleared failures. -/
abbrev MinimalFailureExclusion : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    Not (IsMinimalClearedFailure C)

/-- Pipeline-cleared form consumed by `TargetReduction`. -/
abbrev PipelineCleared : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet C

/-! ## Generic W10 facade matrix -/

/-- W10 target-facade matrix.

This is intentionally just the minimal-failure exclusion needed by the target
reduction.  It is not a hidden assertion that the geometric W8/W9 obligations
are inhabited.
-/
structure Matrix where
  excludesMinimalFailures : MinimalFailureExclusion

namespace Matrix

/-- The W10 facade matrix rules out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : Matrix) :
    MinimalFailureExclusion :=
  M.excludesMinimalFailures

/-- The W10 facade matrix supplies the cleared pipeline predicate. -/
theorem pipelineCleared
    (M : Matrix) :
    PipelineCleared :=
  MinimalGraphFacts.hasCleared_of_no_minimalClearedFailure
    M.excludesMinimalFailures

/-- The W10 facade matrix reaches the Swanepoel target through the checked
minimal-failure and target-reduction wrappers. -/
theorem targetLowerBoundEightThirtyOne
    (M : Matrix) :
    Target :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne_of_pipelineCleared
    M.pipelineCleared

/-! ## Adapters from existing checked matrices -/

/-- View a W8 closure matrix as W10 target-facade data. -/
def ofW8Matrix
    (M : SwanepoelW8ClosureMatrix.Matrix.{u}) :
    Matrix where
  excludesMinimalFailures :=
    SwanepoelW8ClosureMatrix.no_minimalClearedFailure_of_matrix M

/-- View a direct W9 remaining-obligation matrix as W10 target-facade data. -/
def ofW9DirectMatrix
    (M : SwanepoelRemainingObligationsW9.DirectMatrix.{u}) :
    Matrix where
  excludesMinimalFailures :=
    SwanepoelRemainingObligationsW9.DirectMatrix.no_minimalClearedFailure M

/-- View a K23-derived W9 remaining-obligation matrix as W10 target-facade
data. -/
def ofW9K23Matrix
    (M : SwanepoelRemainingObligationsW9.K23Matrix.{u}) :
    Matrix where
  excludesMinimalFailures :=
    SwanepoelRemainingObligationsW9.K23Matrix.no_minimalClearedFailure M

end Matrix

/-! ## Generic theorem forms -/

/-- Minimal-failure exclusion supplies the cleared pipeline predicate. -/
theorem pipelineCleared_of_no_minimalClearedFailure
    (hNoMin : MinimalFailureExclusion) :
    PipelineCleared :=
  MinimalGraphFacts.hasCleared_of_no_minimalClearedFailure hNoMin

/-- Minimal-failure exclusion reaches the Swanepoel target. -/
theorem targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (hNoMin : MinimalFailureExclusion) :
    Target :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne_of_pipelineCleared
    (pipelineCleared_of_no_minimalClearedFailure hNoMin)

/-- Top-level target projection from a W10 facade matrix. -/
theorem targetLowerBoundEightThirtyOne_of_matrix
    (M : Matrix) :
    Target :=
  M.targetLowerBoundEightThirtyOne

/-! ## W8 matrix facades -/

/-- A W8 closure matrix rules out all minimal cleared failures. -/
theorem no_minimalClearedFailure_of_w8Matrix
    (M : SwanepoelW8ClosureMatrix.Matrix.{u}) :
    MinimalFailureExclusion :=
  (Matrix.ofW8Matrix M).no_minimalClearedFailure

/-- A W8 closure matrix supplies the cleared pipeline predicate. -/
theorem pipelineCleared_of_w8Matrix
    (M : SwanepoelW8ClosureMatrix.Matrix.{u}) :
    PipelineCleared :=
  (Matrix.ofW8Matrix M).pipelineCleared

/-- Conditional Swanepoel target from a W8 closure matrix. -/
theorem targetLowerBoundEightThirtyOne_of_w8Matrix
    (M : SwanepoelW8ClosureMatrix.Matrix.{u}) :
    Target :=
  (Matrix.ofW8Matrix M).targetLowerBoundEightThirtyOne

/-! ## W9 direct matrix facades -/

/-- A direct W9 remaining-obligation matrix rules out all minimal cleared
failures. -/
theorem no_minimalClearedFailure_of_w9DirectMatrix
    (M : SwanepoelRemainingObligationsW9.DirectMatrix.{u}) :
    MinimalFailureExclusion :=
  (Matrix.ofW9DirectMatrix M).no_minimalClearedFailure

/-- A direct W9 remaining-obligation matrix supplies the cleared pipeline
predicate. -/
theorem pipelineCleared_of_w9DirectMatrix
    (M : SwanepoelRemainingObligationsW9.DirectMatrix.{u}) :
    PipelineCleared :=
  (Matrix.ofW9DirectMatrix M).pipelineCleared

/-- Conditional Swanepoel target from a direct W9 remaining-obligation matrix.
-/
theorem targetLowerBoundEightThirtyOne_of_w9DirectMatrix
    (M : SwanepoelRemainingObligationsW9.DirectMatrix.{u}) :
    Target :=
  (Matrix.ofW9DirectMatrix M).targetLowerBoundEightThirtyOne

/-! ## W9 K23-derived matrix facades -/

/-- A K23-derived W9 remaining-obligation matrix rules out all minimal cleared
failures. -/
theorem no_minimalClearedFailure_of_w9K23Matrix
    (M : SwanepoelRemainingObligationsW9.K23Matrix.{u}) :
    MinimalFailureExclusion :=
  (Matrix.ofW9K23Matrix M).no_minimalClearedFailure

/-- A K23-derived W9 remaining-obligation matrix supplies the cleared pipeline
predicate. -/
theorem pipelineCleared_of_w9K23Matrix
    (M : SwanepoelRemainingObligationsW9.K23Matrix.{u}) :
    PipelineCleared :=
  (Matrix.ofW9K23Matrix M).pipelineCleared

/-- Conditional Swanepoel target from a K23-derived W9 remaining-obligation
matrix. -/
theorem targetLowerBoundEightThirtyOne_of_w9K23Matrix
    (M : SwanepoelRemainingObligationsW9.K23Matrix.{u}) :
    Target :=
  (Matrix.ofW9K23Matrix M).targetLowerBoundEightThirtyOne

end

end SwanepoelTargetFacadeW10
end Swanepoel
end ErdosProblems1066
