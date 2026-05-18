import ErdosProblems1066.Swanepoel.PointwiseRemainingRowAssemblyW17
import ErdosProblems1066.Swanepoel.SwanepoelConcreteBlockerLedgerW17
import ErdosProblems1066.Swanepoel.SwanepoelUniformFamilyGateW17
import ErdosProblems1066.PachToth.AllPositiveFinalCertificateW17
import ErdosProblems1066.PachToth.PachTothEventualFinalGateW17

set_option autoImplicit false

/-!
# W18 integration ledger

This file is an adapter ledger only.  It states the W18 input packages that
worker files are meant to inhabit and routes those packages to the stable W17
gates.  No theorem below removes the displayed input package.
-/

namespace ErdosProblems1066

noncomputable section

universe u

namespace Swanepoel
namespace W18IntegrationLedger

open MinimalGraphFacts

abbrev PointwiseAssemblyFamily : Type 1 :=
  PointwiseRemainingRowAssemblyW17.PointwiseW16AssemblyFamily.{0}

abbrev ConcreteBlockerInputFamily : Type 1 :=
  SwanepoelConcreteBlockerLedgerW17.ConcreteBlockerInputFamily.{0}

abbrev UniformFamily : Type 1 :=
  SwanepoelUniformFamilyGateW17.UniformFamily.{0}

abbrev Target : Prop :=
  SwanepoelUniformFamilyGateW17.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelUniformFamilyGateW17.LowerBoundAt n C

/-- Exact Swanepoel W18 input: a uniform pointwise W16 assembly family. -/
structure InputPackage : Type 1 where
  pointwise : PointwiseAssemblyFamily

def concreteBlockerFieldsOfPointwiseAssembly
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (P :
      PointwiseRemainingRowAssemblyW17.PointwiseW16AssemblyInputs.{u}
        C hmin) :
    SwanepoelConcreteBlockerLedgerW17.PointwiseConcreteBlockerFields.{u, 0}
      C hmin where
  minimalitySelectedPayForCut := P.base.minimalitySelectedPayForCut
  planarBoundary := P.base.planarBoundary
  boundaryArcInstantiation := P.boundaryArcInstantiation
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  localWindowContainment := P.localWindowContainment

def noCutMinimalityInputsOfPointwiseAssembly
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (P :
      PointwiseRemainingRowAssemblyW17.PointwiseW16AssemblyInputs.{u}
        C hmin) :
    NoCutFromMinimalityW16.PointwiseNoCutMinimalityInputs.{u, 0}
      C hmin where
  minimalitySelectedPayForCut := P.base.minimalitySelectedPayForCut
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  windowContainment := P.localWindowContainment.toM8WindowContainment

def concreteBlockerInputFamilyOfPointwiseAssemblyFamily
    (F : PointwiseAssemblyFamily) :
    ConcreteBlockerInputFamily where
  row := fun C hmin =>
    concreteBlockerFieldsOfPointwiseAssembly (F.row C hmin)

def uniformFamilyOfPointwiseAssemblyFamily
    (F : PointwiseAssemblyFamily) :
    UniformFamily where
  inputs := fun C hmin =>
    noCutMinimalityInputsOfPointwiseAssembly (F.row C hmin)

namespace InputPackage

def toConcreteBlockerInputFamily
    (P : InputPackage) :
    ConcreteBlockerInputFamily :=
  concreteBlockerInputFamilyOfPointwiseAssemblyFamily P.pointwise

def toUniformFamily
    (P : InputPackage) :
    UniformFamily :=
  uniformFamilyOfPointwiseAssemblyFamily P.pointwise

theorem no_minimalClearedFailure
    (P : InputPackage) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  P.toUniformFamily.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (P : InputPackage) :
    Target :=
  P.toUniformFamily.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one
    (P : InputPackage) (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.toUniformFamily.lower_bound_eight_thirty_one n C

theorem targetLowerBoundEightThirtyOne_concrete
    (P : InputPackage) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  P.toConcreteBlockerInputFamily.targetLowerBoundEightThirtyOne

end InputPackage

theorem targetLowerBoundEightThirtyOne_of_w18InputPackage
    (P : InputPackage) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_w18InputPackage
    (P : InputPackage) (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.lower_bound_eight_thirty_one n C

end W18IntegrationLedger
end Swanepoel

namespace PachToth
namespace W18IntegrationLedger

abbrev AllPositiveInputs :=
  AllPositiveFinalCertificateW17.AllPositiveFinalCertificateInputs

abbrev AllPositiveValueInputs :=
  AllPositiveFinalCertificateW17.AllPositiveFinalCertificateValueInputs

abbrev EventualObligations (K0 : Nat) :=
  PachTothEventualFinalGateW17.EventualFiniteCertificateObligations K0

abbrev EventualFinalGatePackage (K0 : Nat) :=
  PachTothEventualFinalGateW17.EventualFinalGatePackage K0

abbrev ExactTarget : Prop :=
  PachTothEventualFinalGateW17.ExactTarget

abbrev EventualTarget : Prop :=
  PachTothEventualFinalGateW17.EventualTarget

abbrev ArbitraryTarget : Prop :=
  PachTothEventualFinalGateW17.ArbitraryTarget

abbrev FixedTarget (n : Nat) : Prop :=
  PachTothEventualFinalGateW17.FixedTarget n

/-- Exact Pach-Toth W18 input: eventual large-k obligations plus the
all-positive finite certificate package. -/
structure InputPackage (K0 : Nat) where
  obligations : EventualObligations K0
  allPositive : AllPositiveInputs

/-- Value-row variant of the exact Pach-Toth W18 input package. -/
structure ValueInputPackage (K0 : Nat) where
  obligations : EventualObligations K0
  allPositive : AllPositiveValueInputs

namespace InputPackage

def toW17EventualFinalGatePackage
    {K0 : Nat} (P : InputPackage K0) :
    EventualFinalGatePackage K0 :=
  PachTothEventualFinalGateW17.of_eventualFiniteCertificateObligations_allPositiveFields
    K0 P.obligations P.allPositive.fields

@[simp]
theorem toW17EventualFinalGatePackage_obligations
    {K0 : Nat} (P : InputPackage K0) :
    P.toW17EventualFinalGatePackage.obligations = P.obligations :=
  rfl

theorem exact_eventual_arbitrary
    {K0 : Nat} (P : InputPackage K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  P.toW17EventualFinalGatePackage.exact_eventual_arbitrary

theorem targetUpperConstructionFiveSixteen
    {K0 : Nat} (P : InputPackage K0) :
    ExactTarget :=
  P.toW17EventualFinalGatePackage.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : InputPackage K0) :
    EventualTarget :=
  P.toW17EventualFinalGatePackage.targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : InputPackage K0) :
    ArbitraryTarget :=
  P.toW17EventualFinalGatePackage.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt
    {K0 : Nat} (P : InputPackage K0) (n : Nat) :
    FixedTarget n :=
  P.toW17EventualFinalGatePackage.targetUpperConstructionFiveSixteenAt n

theorem upper_bound_five_sixteen_exact
    {K0 : Nat} (P : InputPackage K0) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  P.toW17EventualFinalGatePackage.upper_bound_five_sixteen_exact k hk

theorem upper_bound_five_sixteen_arbitrary
    {K0 : Nat} (P : InputPackage K0) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  P.toW17EventualFinalGatePackage.upper_bound_five_sixteen_arbitrary n

end InputPackage

namespace ValueInputPackage

def toInputPackage
    {K0 : Nat} (P : ValueInputPackage K0) :
    InputPackage K0 where
  obligations := P.obligations
  allPositive := P.allPositive.toInputs

def toW17EventualFinalGatePackage
    {K0 : Nat} (P : ValueInputPackage K0) :
    EventualFinalGatePackage K0 :=
  P.toInputPackage.toW17EventualFinalGatePackage

theorem exact_eventual_arbitrary
    {K0 : Nat} (P : ValueInputPackage K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  P.toInputPackage.exact_eventual_arbitrary

theorem targetUpperConstructionFiveSixteen
    {K0 : Nat} (P : ValueInputPackage K0) :
    ExactTarget :=
  P.toInputPackage.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : ValueInputPackage K0) :
    EventualTarget :=
  P.toInputPackage.targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : ValueInputPackage K0) :
    ArbitraryTarget :=
  P.toInputPackage.targetUpperConstructionFiveSixteenArbitrary

theorem upper_bound_five_sixteen_exact
    {K0 : Nat} (P : ValueInputPackage K0) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  P.toInputPackage.upper_bound_five_sixteen_exact k hk

theorem upper_bound_five_sixteen_arbitrary
    {K0 : Nat} (P : ValueInputPackage K0) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  P.toInputPackage.upper_bound_five_sixteen_arbitrary n

end ValueInputPackage

theorem exact_eventual_arbitrary_of_w18InputPackage
    {K0 : Nat} (P : InputPackage K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  P.exact_eventual_arbitrary

theorem upper_bound_five_sixteen_arbitrary_of_w18InputPackage
    {K0 : Nat} (P : InputPackage K0) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  P.upper_bound_five_sixteen_arbitrary n

theorem exact_eventual_arbitrary_of_w18ValueInputPackage
    {K0 : Nat} (P : ValueInputPackage K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  P.exact_eventual_arbitrary

theorem upper_bound_five_sixteen_arbitrary_of_w18ValueInputPackage
    {K0 : Nat} (P : ValueInputPackage K0) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  P.upper_bound_five_sixteen_arbitrary n

end W18IntegrationLedger
end PachToth

end

end ErdosProblems1066
