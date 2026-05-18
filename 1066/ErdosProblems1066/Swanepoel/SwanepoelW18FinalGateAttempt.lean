import ErdosProblems1066.Swanepoel.SwanepoelConcreteBlockerLedgerW17

set_option autoImplicit false

/-!
# W18 Swanepoel final gate attempt

This file is endpoint plumbing only.  It packages the concrete W17 blocker
family as the W18 input family, sends that family to the W15 `FinalGate`, and
then exposes the checked target and lower-bound wrappers.

It deliberately remains conditional on an explicit concrete blocker family.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW18FinalGateAttempt

universe u

noncomputable section

abbrev Target : Prop :=
  FinalSwanepoelGateW15.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  FinalSwanepoelGateW15.LowerBoundAt n C

abbrev MinimalFailureExclusion : Prop :=
  FinalSwanepoelGateW15.MinimalFailureExclusion

abbrev W15FinalGate :=
  FinalSwanepoelGateW15.FinalGate

abbrev ConcreteW18InputFamily :=
  SwanepoelConcreteBlockerLedgerW17.ConcreteBlockerInputFamily

abbrev ConcreteBlockerInputFamily :=
  ConcreteW18InputFamily

abbrev W15BoundaryArcLocalWindowInputFamily :=
  SwanepoelConcreteBlockerLedgerW17.W15InputFamily

abbrev W15RemainingInputFamily :=
  FinalSwanepoelGateW15.RemainingInputFamily

namespace ConcreteW18InputFamily

def toW15BoundaryArcLocalWindowInputFamily
    (H : ConcreteW18InputFamily.{u}) :
    W15BoundaryArcLocalWindowInputFamily.{u} :=
  H.toW15InputFamily

def toW15RemainingInputFamily
    (H : ConcreteW18InputFamily.{u}) :
    W15RemainingInputFamily.{u} :=
  H.toRemainingInputFamily

theorem minimalFailureExclusion
    (H : ConcreteW18InputFamily.{u}) :
    MinimalFailureExclusion :=
  H.no_minimalClearedFailure

theorem no_minimalClearedFailure
    (H : ConcreteW18InputFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (MinimalGraphFacts.IsMinimalClearedFailure C) :=
  H.minimalFailureExclusion

def finalGate
    (H : ConcreteW18InputFamily.{u}) :
    W15FinalGate where
  minimalFailureExclusion := H.minimalFailureExclusion

theorem targetLowerBoundEightThirtyOne
    (H : ConcreteW18InputFamily.{u}) :
    Target :=
  H.finalGate.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one
    (H : ConcreteW18InputFamily.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  H.finalGate.lower_bound_eight_thirty_one n C

end ConcreteW18InputFamily

def finalGate_of_concreteW18InputFamily
    (H : ConcreteW18InputFamily.{u}) :
    W15FinalGate :=
  H.finalGate

def finalGate_of_concreteBlockerInputFamily
    (H : ConcreteBlockerInputFamily.{u}) :
    W15FinalGate :=
  finalGate_of_concreteW18InputFamily H

theorem targetLowerBoundEightThirtyOne_of_concreteW18InputFamily
    (H : ConcreteW18InputFamily.{u}) :
    Target :=
  H.targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_concreteBlockerInputFamily
    (H : ConcreteBlockerInputFamily.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_concreteW18InputFamily H

theorem lower_bound_eight_thirty_one_of_concreteW18InputFamily
    (H : ConcreteW18InputFamily.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  H.lower_bound_eight_thirty_one n C

theorem lower_bound_eight_thirty_one_of_concreteBlockerInputFamily
    (H : ConcreteBlockerInputFamily.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one_of_concreteW18InputFamily H n C

end

end SwanepoelW18FinalGateAttempt

theorem targetLowerBoundEightThirtyOne_of_w18_concreteBlockerInputFamily
    (H : SwanepoelW18FinalGateAttempt.ConcreteBlockerInputFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  SwanepoelW18FinalGateAttempt.targetLowerBoundEightThirtyOne_of_concreteBlockerInputFamily
    H

theorem lower_bound_eight_thirty_one_of_w18_concreteBlockerInputFamily
    (H : SwanepoelW18FinalGateAttempt.ConcreteBlockerInputFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelW18FinalGateAttempt.LowerBoundAt n C :=
  SwanepoelW18FinalGateAttempt.lower_bound_eight_thirty_one_of_concreteBlockerInputFamily
    H n C

end Swanepoel

namespace Verified

abbrev SwanepoelW18ConcreteBlockerInputFamily :=
  Swanepoel.SwanepoelW18FinalGateAttempt.ConcreteW18InputFamily

abbrev SwanepoelW18FinalGate :=
  Swanepoel.FinalSwanepoelGateW15.FinalGate

def swanepoelW18FinalGate_of_concreteBlockerInputFamily
    (H : SwanepoelW18ConcreteBlockerInputFamily) :
    SwanepoelW18FinalGate :=
  Swanepoel.SwanepoelW18FinalGateAttempt.finalGate_of_concreteW18InputFamily
    H

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound from the
W18 concrete blocker input family. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w18_concreteBlockerInputFamily
    (H : SwanepoelW18ConcreteBlockerInputFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    Swanepoel.SwanepoelW18FinalGateAttempt.LowerBoundAt n C :=
  Swanepoel.lower_bound_eight_thirty_one_of_w18_concreteBlockerInputFamily
    H n C

end Verified
end ErdosProblems1066
