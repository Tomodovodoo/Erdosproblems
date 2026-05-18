import ErdosProblems1066.W18IntegrationLedger
import ErdosProblems1066.Swanepoel.SwanepoelW18FinalGateAttempt

set_option autoImplicit false

/-!
# W19 Swanepoel final conditional closure

This file is a final facade over the W18 Swanepoel ledgers.  It keeps the
Swanepoel `8 / 31` endpoint conditional on an explicit W16 pointwise assembly
family or an explicit concrete blocker input family.

No unconditional public `KnownBounds` wrapper is introduced here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelFinalClosureW19

open MinimalGraphFacts

noncomputable section

abbrev PointwiseW16AssemblyFamily : Type 1 :=
  W18IntegrationLedger.PointwiseAssemblyFamily

abbrev ConcreteBlockerInputFamily : Type 1 :=
  W18IntegrationLedger.ConcreteBlockerInputFamily

abbrev W18InputPackage : Type 1 :=
  W18IntegrationLedger.InputPackage

abbrev UniformFamily : Type 1 :=
  W18IntegrationLedger.UniformFamily

abbrev Target : Prop :=
  W18IntegrationLedger.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  W18IntegrationLedger.LowerBoundAt n C

abbrev FinalGate : Prop :=
  FinalSwanepoelGateW15.FinalGate

/-! ## Pointwise W16 assembly family route -/

def inputPackageOfPointwiseW16AssemblyFamily
    (F : PointwiseW16AssemblyFamily) :
    W18InputPackage where
  pointwise := F

def concreteBlockerInputFamilyOfPointwiseW16AssemblyFamily
    (F : PointwiseW16AssemblyFamily) :
    ConcreteBlockerInputFamily :=
  W18IntegrationLedger.concreteBlockerInputFamilyOfPointwiseAssemblyFamily F

def uniformFamilyOfPointwiseW16AssemblyFamily
    (F : PointwiseW16AssemblyFamily) :
    UniformFamily :=
  W18IntegrationLedger.uniformFamilyOfPointwiseAssemblyFamily F

def finalGateOfPointwiseW16AssemblyFamily
    (F : PointwiseW16AssemblyFamily) :
    FinalGate :=
  (uniformFamilyOfPointwiseW16AssemblyFamily F).finalGate

theorem no_minimalClearedFailure_of_pointwiseW16AssemblyFamily
    (F : PointwiseW16AssemblyFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  (inputPackageOfPointwiseW16AssemblyFamily F).no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne_of_pointwiseW16AssemblyFamily
    (F : PointwiseW16AssemblyFamily) :
    Target :=
  W18IntegrationLedger.targetLowerBoundEightThirtyOne_of_w18InputPackage
    (inputPackageOfPointwiseW16AssemblyFamily F)

theorem targetLowerBoundEightThirtyOne_of_pointwiseW16AssemblyFamily_via_concrete
    (F : PointwiseW16AssemblyFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  (concreteBlockerInputFamilyOfPointwiseW16AssemblyFamily F).targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_pointwiseW16AssemblyFamily
    (F : PointwiseW16AssemblyFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  W18IntegrationLedger.lower_bound_eight_thirty_one_of_w18InputPackage
    (inputPackageOfPointwiseW16AssemblyFamily F) n C

/-! ## Concrete blocker input family route -/

def finalGateOfConcreteBlockerInputFamily
    (F : ConcreteBlockerInputFamily) :
    FinalGate :=
  SwanepoelW18FinalGateAttempt.finalGate_of_concreteBlockerInputFamily F

theorem no_minimalClearedFailure_of_concreteBlockerInputFamily
    (F : ConcreteBlockerInputFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  F.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne_of_concreteBlockerInputFamily
    (F : ConcreteBlockerInputFamily) :
    Target :=
  SwanepoelW18FinalGateAttempt.targetLowerBoundEightThirtyOne_of_concreteBlockerInputFamily
    F

theorem lower_bound_eight_thirty_one_of_concreteBlockerInputFamily
    (F : ConcreteBlockerInputFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  SwanepoelW18FinalGateAttempt.lower_bound_eight_thirty_one_of_concreteBlockerInputFamily
    F n C

/-! ## Short endpoint aliases -/

theorem targetLowerBoundEightThirtyOne
    (F : PointwiseW16AssemblyFamily) :
    Target :=
  targetLowerBoundEightThirtyOne_of_pointwiseW16AssemblyFamily F

theorem lower_bound_eight_thirty_one
    (F : PointwiseW16AssemblyFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one_of_pointwiseW16AssemblyFamily F n C

end

end SwanepoelFinalClosureW19

theorem targetLowerBoundEightThirtyOne_of_w19_pointwiseW16AssemblyFamily
    (F : SwanepoelFinalClosureW19.PointwiseW16AssemblyFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  SwanepoelFinalClosureW19.targetLowerBoundEightThirtyOne_of_pointwiseW16AssemblyFamily
    F

theorem targetLowerBoundEightThirtyOne_of_w19_concreteBlockerInputFamily
    (F : SwanepoelFinalClosureW19.ConcreteBlockerInputFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  SwanepoelFinalClosureW19.targetLowerBoundEightThirtyOne_of_concreteBlockerInputFamily
    F

theorem lower_bound_eight_thirty_one_of_w19_pointwiseW16AssemblyFamily
    (F : SwanepoelFinalClosureW19.PointwiseW16AssemblyFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelFinalClosureW19.LowerBoundAt n C :=
  SwanepoelFinalClosureW19.lower_bound_eight_thirty_one_of_pointwiseW16AssemblyFamily
    F n C

theorem lower_bound_eight_thirty_one_of_w19_concreteBlockerInputFamily
    (F : SwanepoelFinalClosureW19.ConcreteBlockerInputFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelFinalClosureW19.LowerBoundAt n C :=
  SwanepoelFinalClosureW19.lower_bound_eight_thirty_one_of_concreteBlockerInputFamily
    F n C

end Swanepoel

namespace Verified

abbrev SwanepoelW19PointwiseW16AssemblyFamily :=
  Swanepoel.SwanepoelFinalClosureW19.PointwiseW16AssemblyFamily

abbrev SwanepoelW19ConcreteBlockerInputFamily :=
  Swanepoel.SwanepoelFinalClosureW19.ConcreteBlockerInputFamily

abbrev SwanepoelW19FinalGate :=
  Swanepoel.SwanepoelFinalClosureW19.FinalGate

def swanepoelW19FinalGate_of_pointwiseW16AssemblyFamily
    (F : SwanepoelW19PointwiseW16AssemblyFamily) :
    SwanepoelW19FinalGate :=
  Swanepoel.SwanepoelFinalClosureW19.finalGateOfPointwiseW16AssemblyFamily F

def swanepoelW19FinalGate_of_concreteBlockerInputFamily
    (F : SwanepoelW19ConcreteBlockerInputFamily) :
    SwanepoelW19FinalGate :=
  Swanepoel.SwanepoelFinalClosureW19.finalGateOfConcreteBlockerInputFamily F

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound from a
W19 pointwise W16 assembly family. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w19_pointwiseW16AssemblyFamily
    (F : SwanepoelW19PointwiseW16AssemblyFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    Swanepoel.SwanepoelFinalClosureW19.LowerBoundAt n C :=
  Swanepoel.lower_bound_eight_thirty_one_of_w19_pointwiseW16AssemblyFamily
    F n C

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound from a
W19 concrete blocker input family. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w19_concreteBlockerInputFamily
    (F : SwanepoelW19ConcreteBlockerInputFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    Swanepoel.SwanepoelFinalClosureW19.LowerBoundAt n C :=
  Swanepoel.lower_bound_eight_thirty_one_of_w19_concreteBlockerInputFamily
    F n C

end Verified
end ErdosProblems1066
