import ErdosProblems1066.Swanepoel.SwanepoelEndpointAttemptW14
import ErdosProblems1066.Swanepoel.RemainingInputFamilyBuilderW14
import ErdosProblems1066.Swanepoel.FaceReductionEndpointW14
import ErdosProblems1066.Swanepoel.KnownBoundsSpineW13

set_option autoImplicit false

/-!
# W15 Swanepoel final gate

The smallest current endpoint-facing gate is the uniform exclusion of minimal
cleared failures.  From that single field, the W14 builder can synthesize the
older `RemainingInputFamily` shape by ex falso, and all Swanepoel endpoint
wrappers below remain conditional on an explicit `FinalGate`.

This file deliberately does not add an unconditional `8 / 31` theorem.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FinalSwanepoelGateW15

open MinimalGraphFacts

universe u

noncomputable section

abbrev Target : Prop :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  Exists fun s : Finset (Fin n) =>
    C.IsIndep s /\ 31 * s.card >= 8 * n

abbrev MinimalFailureExclusion : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    Not (IsMinimalClearedFailure C)

abbrev RemainingInputFamily :=
  MinimalFailureClosureW13.RemainingInputFamily

/-- The current smallest final gate: every minimal cleared failure is excluded. -/
structure FinalGate where
  minimalFailureExclusion : MinimalFailureExclusion

namespace FinalGate

/-- The gate field in the common W11/W14 minimal-failure spelling. -/
theorem no_minimalClearedFailure (G : FinalGate) :
    MinimalFailureExclusion :=
  G.minimalFailureExclusion

/-- Repackage the minimal-failure exclusion as the older W13 remaining-input
family shape. -/
def remainingInputFamily (G : FinalGate) :
    RemainingInputFamily.{u} :=
  RemainingInputFamilyBuilderW14.remainingInputFamily_of_no_minimalClearedFailure
    G.no_minimalClearedFailure

/-- Nonempty form of the older W13 remaining-input family. -/
theorem nonempty_remainingInputFamily (G : FinalGate) :
    Nonempty RemainingInputFamily.{u} :=
  Nonempty.intro (G.remainingInputFamily)

/-- Target endpoint through the direct minimal-failure-exclusion wrapper. -/
theorem targetLowerBoundEightThirtyOne (G : FinalGate) :
    Target :=
  FaceReductionEndpointW14.targetLowerBoundEightThirtyOne_of_minimalFailureExclusion
    G.no_minimalClearedFailure

/-- KnownBounds-shaped endpoint through the direct minimal-failure-exclusion
wrapper. -/
theorem lower_bound_eight_thirty_one
    (G : FinalGate) (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  FaceReductionEndpointW14.lower_bound_eight_thirty_one_of_minimalFailureExclusion
    G.no_minimalClearedFailure n C

/-- Target endpoint through the W14 remaining-input-family wrapper. -/
theorem targetLowerBoundEightThirtyOne_via_remainingInputFamily
    (G : FinalGate) :
    Target :=
  SwanepoelEndpointAttemptW14.targetLowerBoundEightThirtyOne_of_remainingInputFamily.{0}
    (FinalGate.remainingInputFamily.{0} G)

/-- KnownBounds-shaped endpoint through the W14 remaining-input-family wrapper. -/
theorem lower_bound_eight_thirty_one_via_remainingInputFamily
    (G : FinalGate) (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  SwanepoelEndpointAttemptW14.lower_bound_eight_thirty_one_of_remainingInputFamily.{0}
    (FinalGate.remainingInputFamily.{0} G) n C

/-- Target endpoint through the W14 face-reduction endpoint facade. -/
theorem targetLowerBoundEightThirtyOne_via_faceReductionEndpoint
    (G : FinalGate) :
    Target :=
  FaceReductionEndpointW14.targetLowerBoundEightThirtyOne_of_minimalFailureExclusion
    G.no_minimalClearedFailure

/-- KnownBounds-shaped endpoint through the W14 face-reduction endpoint facade. -/
theorem lower_bound_eight_thirty_one_via_faceReductionEndpoint
    (G : FinalGate) (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  FaceReductionEndpointW14.lower_bound_eight_thirty_one_of_minimalFailureExclusion
    G.no_minimalClearedFailure n C

end FinalGate

/-- Top-level target wrapper from the W15 final gate. -/
theorem targetLowerBoundEightThirtyOne_of_finalGate
    (G : FinalGate) :
    Target :=
  G.targetLowerBoundEightThirtyOne

/-- Top-level KnownBounds-shaped wrapper from the W15 final gate. -/
theorem lower_bound_eight_thirty_one_of_finalGate
    (G : FinalGate) (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  G.lower_bound_eight_thirty_one n C

end

end FinalSwanepoelGateW15

/-! ## Source-specific public-style aliases -/

/-- Source-specific conditional target alias for the W15 final gate. -/
theorem targetLowerBoundEightThirtyOne_of_w15_finalGate
    (G : FinalSwanepoelGateW15.FinalGate) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  FinalSwanepoelGateW15.targetLowerBoundEightThirtyOne_of_finalGate G

/-- Source-specific conditional alias for the W15 final gate. -/
theorem lower_bound_eight_thirty_one_of_w15_finalGate
    (G : FinalSwanepoelGateW15.FinalGate)
    (n : Nat) (C : _root_.UDConfig n) :
    FinalSwanepoelGateW15.LowerBoundAt n C :=
  FinalSwanepoelGateW15.lower_bound_eight_thirty_one_of_finalGate
    G n C

end Swanepoel

namespace Verified

abbrev SwanepoelW15FinalGate :=
  Swanepoel.FinalSwanepoelGateW15.FinalGate

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound from the
W15 final gate. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w15_finalGate
    (G : SwanepoelW15FinalGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Swanepoel.FinalSwanepoelGateW15.LowerBoundAt n C :=
  Swanepoel.lower_bound_eight_thirty_one_of_w15_finalGate
    G n C

end Verified
end ErdosProblems1066
