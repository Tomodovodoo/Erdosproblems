import ErdosProblems1066.Swanepoel.NoCutFromMinimalityW16

set_option autoImplicit false

/-!
# W17 Swanepoel uniform family gate

This file exposes the current endpoint-facing Swanepoel source family.  It is
uniform over minimal cleared failures and repackages only data already used by
the W16 no-cut-from-minimality route.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelUniformFamilyGateW17

open MinimalGraphFacts

universe u

noncomputable section

abbrev Target : Prop :=
  FinalSwanepoelGateW15.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  FinalSwanepoelGateW15.LowerBoundAt n C

abbrev MinimalFailureExclusion : Prop :=
  FinalSwanepoelGateW15.MinimalFailureExclusion

abbrev RemainingInputFamily :=
  MinimalFailureClosureW13.RemainingInputFamily

abbrev PointwiseUniformInputs {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  NoCutFromMinimalityW16.PointwiseNoCutMinimalityInputs.{u} C hmin

/-- Uniform pointwise source family currently sufficient for the W15 gate. -/
structure UniformFamily : Type (u + 1) where
  inputs :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseUniformInputs.{u} C hmin

namespace UniformFamily

def toNoCutMinimalityRemainingInputFamily
    (H : UniformFamily.{u}) :
    NoCutFromMinimalityW16.NoCutMinimalityRemainingInputFamily.{u} where
  inputs := H.inputs

def ofNoCutMinimalityRemainingInputFamily
    (H : NoCutFromMinimalityW16.NoCutMinimalityRemainingInputFamily.{u}) :
    UniformFamily.{u} where
  inputs := H.inputs

theorem minimalitySelectedPayForCutFamily
    (H : UniformFamily.{u}) :
    NoCutFromMinimalityW16.MinimalitySelectedPayForCutFamily :=
  H.toNoCutMinimalityRemainingInputFamily.minimalitySelectedPayForCutFamily

def toRemainingInputFamily
    (H : UniformFamily.{u}) :
    RemainingInputFamily.{u} :=
  H.toNoCutMinimalityRemainingInputFamily.toRemainingInputFamily

theorem nonempty_remainingInputFamily
    (H : UniformFamily.{u}) :
    Nonempty RemainingInputFamily.{u} :=
  Nonempty.intro H.toRemainingInputFamily

theorem minimalFailureExclusion
    (H : UniformFamily.{u}) :
    MinimalFailureExclusion :=
  H.toNoCutMinimalityRemainingInputFamily.minimalFailureExclusion

theorem no_minimalClearedFailure
    (H : UniformFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.minimalFailureExclusion

def finalGate
    (H : UniformFamily.{u}) :
    FinalSwanepoelGateW15.FinalGate :=
  H.toNoCutMinimalityRemainingInputFamily.finalGate

theorem targetLowerBoundEightThirtyOne
    (H : UniformFamily.{u}) :
    Target :=
  H.finalGate.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one
    (H : UniformFamily.{u}) (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  H.finalGate.lower_bound_eight_thirty_one n C

end UniformFamily

def toNoCutMinimalityRemainingInputFamily
    (H : UniformFamily.{u}) :
    NoCutFromMinimalityW16.NoCutMinimalityRemainingInputFamily.{u} :=
  H.toNoCutMinimalityRemainingInputFamily

def ofNoCutMinimalityRemainingInputFamily
    (H : NoCutFromMinimalityW16.NoCutMinimalityRemainingInputFamily.{u}) :
    UniformFamily.{u} :=
  UniformFamily.ofNoCutMinimalityRemainingInputFamily H

def remainingInputFamily_of_uniformFamily
    (H : UniformFamily.{u}) :
    RemainingInputFamily.{u} :=
  H.toRemainingInputFamily

theorem nonempty_remainingInputFamily_of_uniformFamily
    (H : UniformFamily.{u}) :
    Nonempty RemainingInputFamily.{u} :=
  H.nonempty_remainingInputFamily

theorem minimalitySelectedPayForCutFamily_of_uniformFamily
    (H : UniformFamily.{u}) :
    NoCutFromMinimalityW16.MinimalitySelectedPayForCutFamily :=
  H.minimalitySelectedPayForCutFamily

theorem minimalFailureExclusion_of_uniformFamily
    (H : UniformFamily.{u}) :
    MinimalFailureExclusion :=
  H.minimalFailureExclusion

theorem no_minimalClearedFailure_of_uniformFamily
    (H : UniformFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.no_minimalClearedFailure

def finalGate_of_uniformFamily
    (H : UniformFamily.{u}) :
    FinalSwanepoelGateW15.FinalGate :=
  H.finalGate

theorem targetLowerBoundEightThirtyOne_of_uniformFamily
    (H : UniformFamily.{u}) :
    Target :=
  H.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_uniformFamily
    (H : UniformFamily.{u}) (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  H.lower_bound_eight_thirty_one n C

end

end SwanepoelUniformFamilyGateW17

/-- Source-specific conditional target alias for the W17 uniform family gate. -/
theorem targetLowerBoundEightThirtyOne_of_w17_uniformFamily
    (H : SwanepoelUniformFamilyGateW17.UniformFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  SwanepoelUniformFamilyGateW17.targetLowerBoundEightThirtyOne_of_uniformFamily
    H

/-- Source-specific conditional alias for the W17 uniform family gate. -/
theorem lower_bound_eight_thirty_one_of_w17_uniformFamily
    (H : SwanepoelUniformFamilyGateW17.UniformFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelUniformFamilyGateW17.LowerBoundAt n C :=
  SwanepoelUniformFamilyGateW17.lower_bound_eight_thirty_one_of_uniformFamily
    H n C

end Swanepoel

namespace Verified

abbrev SwanepoelW17UniformFamily :=
  Swanepoel.SwanepoelUniformFamilyGateW17.UniformFamily

abbrev SwanepoelW17FinalGate :=
  Swanepoel.FinalSwanepoelGateW15.FinalGate

def swanepoelW17FinalGate_of_uniformFamily
    (H : SwanepoelW17UniformFamily) :
    SwanepoelW17FinalGate :=
  Swanepoel.SwanepoelUniformFamilyGateW17.finalGate_of_uniformFamily H

/-- Public-facade-shaped conditional Swanepoel lower bound from the W17
uniform family gate. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w17_uniformFamily
    (H : SwanepoelW17UniformFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    Swanepoel.SwanepoelUniformFamilyGateW17.LowerBoundAt n C :=
  Swanepoel.lower_bound_eight_thirty_one_of_w17_uniformFamily
    H n C

end Verified
end ErdosProblems1066
