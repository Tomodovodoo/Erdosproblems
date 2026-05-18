import ErdosProblems1066.Swanepoel.MinimalFailureClosureW13
import ErdosProblems1066.Swanepoel.KnownBoundsSpineW13
import ErdosProblems1066.Swanepoel.BrokenLatticeEliminatorW13

set_option autoImplicit false

/-!
# W14 Swanepoel endpoint attempt

This file keeps the W14 endpoint conditional.  The strongest endpoint-shaped
route available here is the W13 exact target-input family, exposed below as a
small named record and then projected to the target proposition and to the
KnownBounds-shaped per-configuration statement.
-/

namespace ErdosProblems1066
namespace Swanepoel
universe u v

namespace SwanepoelEndpointAttemptW14

open MinimalGraphFacts

noncomputable section

/-- The exact remaining W14 endpoint assumption.

The single field is the current shortest checked source-facing family:
`MinimalFailurePaperFactMatrix.TargetLowerBoundEightThirtyOneInputs`, also
named by `KnownBoundsSpineW13.ExactTargetInputs`.
-/
structure EndpointAssumptions : Type (max (u + 1) (v + 1)) where
  exactTargetInputs : KnownBoundsSpineW13.ExactTargetInputs.{u, v}

namespace EndpointAssumptions

/-- The remaining assumption as the refined paper-facts family. -/
def refinedPaperFactsFamily
    (H : EndpointAssumptions.{u, v}) :
    KnownBoundsSpineW13.RefinedPaperFactsFamily.{u, v} :=
  H.exactTargetInputs

/-- The remaining assumption rules out minimal cleared failures through the
checked refined-family route. -/
theorem no_minimalClearedFailure
    (H : EndpointAssumptions.{u, v}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalFailurePaperFactMatrix.refined_family_noMinimalClearedFailure_consumes_eliminator
    H.exactTargetInputs

/-- Conditional W14 endpoint: the exact remaining input family proves the
Swanepoel `8 / 31` target. -/
theorem targetLowerBoundEightThirtyOne
    (H : EndpointAssumptions.{u, v}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  KnownBoundsSpineW13.targetLowerBoundEightThirtyOne_of_exactTargetInputs
    H.exactTargetInputs

/-- Conditional KnownBounds-shaped endpoint from the exact W14 assumptions. -/
theorem lower_bound_eight_thirty_one
    (H : EndpointAssumptions.{u, v})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  KnownBoundsSpineW13.lower_bound_eight_thirty_one_of_exactTargetInputs
    H.exactTargetInputs n C

end EndpointAssumptions

/-- Top-level theorem form of the W14 conditional target endpoint. -/
theorem targetLowerBoundEightThirtyOne_of_endpointAssumptions
    (H : EndpointAssumptions.{u, v}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

/-- Top-level theorem form of the W14 conditional KnownBounds-shaped endpoint.
-/
theorem lower_bound_eight_thirty_one_of_endpointAssumptions
    (H : EndpointAssumptions.{u, v})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  H.lower_bound_eight_thirty_one n C

/-- Direct endpoint wrapper from the W13 minimal-failure closure input family.
-/
theorem targetLowerBoundEightThirtyOne_of_remainingInputFamily
    (H : MinimalFailureClosureW13.RemainingInputFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosureW13.targetLowerBoundEightThirtyOne_of_remainingInputFamily
    H

/-- KnownBounds-shaped wrapper from the W13 minimal-failure closure input
family. -/
theorem lower_bound_eight_thirty_one_of_remainingInputFamily
    (H : MinimalFailureClosureW13.RemainingInputFamily.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_remainingInputFamily H n C

/-- Direct endpoint wrapper from the W13 broken-lattice explicit-record
builder. -/
theorem targetLowerBoundEightThirtyOne_of_explicitBrokenLatticeRecordBuilder
    (build :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BrokenLatticeAssemblyW13.ExplicitBrokenLatticeM8LocalWindowRecords
            C hmin) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  BrokenLatticeEliminatorW13.targetLowerBoundEightThirtyOne_of_explicitRecordBuilder
    build

/-- KnownBounds-shaped wrapper from the W13 broken-lattice explicit-record
builder. -/
theorem lower_bound_eight_thirty_one_of_explicitBrokenLatticeRecordBuilder
    (build :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          BrokenLatticeAssemblyW13.ExplicitBrokenLatticeM8LocalWindowRecords
            C hmin)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_explicitBrokenLatticeRecordBuilder
    build n C

end

end SwanepoelEndpointAttemptW14

/-- Source-specific conditional alias for the W14 endpoint attempt. -/
theorem lower_bound_eight_thirty_one_of_w14_endpointAssumptions
    (H : SwanepoelEndpointAttemptW14.EndpointAssumptions.{u, v})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  SwanepoelEndpointAttemptW14.lower_bound_eight_thirty_one_of_endpointAssumptions
    H n C

end Swanepoel

namespace Verified
universe u v

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound from the
W14 exact endpoint assumptions. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w14_endpointAssumptions
    (H : Swanepoel.SwanepoelEndpointAttemptW14.EndpointAssumptions.{u, v})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.lower_bound_eight_thirty_one_of_w14_endpointAssumptions
    H n C

end Verified
end ErdosProblems1066
