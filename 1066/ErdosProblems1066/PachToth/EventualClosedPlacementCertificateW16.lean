import ErdosProblems1066.PachToth.EventualRoleHingeClosure
import ErdosProblems1066.PachToth.LargeClosedPlacementW12
import ErdosProblems1066.PachToth.LargeSmallCaseClosureW14
import ErdosProblems1066.PachToth.AllPositiveCertificateAssemblyW15
import ErdosProblems1066.PachToth.LargeThresholdSmallCasesW15
import ErdosProblems1066.PachToth.FinalPachTothGateW15

set_option autoImplicit false

/-!
# W16 eventual closed-placement certificate facade

This module records the certificate-level handoff from eventual finite
role-hinge obligations to the large closed-placement fields used by the W14
and W15 gates.  It is only a facade: every endpoint still receives explicit
certificate or small-complement input.
-/

namespace ErdosProblems1066
namespace PachToth
namespace EventualClosedPlacementCertificateW16

noncomputable section

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactBlockTarget (k : Nat) : Prop :=
  LargeThresholdSmallCasesW15.ExactBlockTarget k

abbrev EventualFiniteCertificateObligations (K0 : Nat) :=
  EventualRoleHingeClosure.EventualFiniteCertificateObligations K0

abbrev LargeExplicitClosedPlacementCertificates (K0 : Nat) :=
  LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates K0

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeThresholdSmallCasesW15.LargeClosedPlacementFields K0

abbrev SmallComplement (K0 : Nat) :=
  LargeThresholdSmallCasesW15.SmallComplement K0

abbrev LargeWithThresholdSmallCases (K0 : Nat) :=
  LargeThresholdSmallCasesW15.LargeWithThresholdSmallCases K0

abbrev FinalGate :=
  FinalPachTothGateW15.FinalGate

abbrev AllPositiveCertificateRows :=
  AllPositiveCertificateAssemblyW15.AllPositiveCertificateRows

abbrev AllPositiveFiniteFields :=
  LargeSmallCaseClosureW14.AllPositiveFiniteFields

/-! ## Eventual finite obligations to large closed-placement fields -/

def largeExplicitClosedPlacementCertificatesOfEventualFiniteCertificateObligations
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0) :
    LargeExplicitClosedPlacementCertificates K0 :=
  LargeClosedPlacementW12.largeExplicitClosedPlacementCertificatesOfFiniteObligations
    O

def largeClosedPlacementFieldsOfEventualFiniteCertificateObligations
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0) :
    LargeClosedPlacementFields K0 :=
  largeExplicitClosedPlacementCertificatesOfEventualFiniteCertificateObligations
    O

theorem targetUpperConstructionFiveSixteenEventually_of_eventualFiniteCertificateObligations
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0) :
    EventualTarget :=
  (largeExplicitClosedPlacementCertificatesOfEventualFiniteCertificateObligations
    O).targetUpperConstructionFiveSixteenEventually

structure EventualClosedPlacementCertificate (K0 : Nat) where
  obligations : EventualFiniteCertificateObligations K0

namespace EventualClosedPlacementCertificate

def largeExplicitClosedPlacementCertificates
    {K0 : Nat} (C : EventualClosedPlacementCertificate K0) :
    LargeExplicitClosedPlacementCertificates K0 :=
  largeExplicitClosedPlacementCertificatesOfEventualFiniteCertificateObligations
    C.obligations

def largeClosedPlacementFields
    {K0 : Nat} (C : EventualClosedPlacementCertificate K0) :
    LargeClosedPlacementFields K0 :=
  largeClosedPlacementFieldsOfEventualFiniteCertificateObligations
    C.obligations

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (C : EventualClosedPlacementCertificate K0) :
    EventualTarget :=
  targetUpperConstructionFiveSixteenEventually_of_eventualFiniteCertificateObligations
    C.obligations

def finalGate_atMostOne
    {K0 : Nat} (C : EventualClosedPlacementCertificate K0) (hK0 : K0 <= 1) :
    FinalGate :=
  FinalPachTothGateW15.of_largeClosedPlacementFields_atMostOne
    C.largeClosedPlacementFields hK0

theorem exact_eventual_arbitrary_atMostOne
    {K0 : Nat} (C : EventualClosedPlacementCertificate K0) (hK0 : K0 <= 1) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  LargeThresholdSmallCasesW15.exact_eventual_arbitrary_atMostOne
    C.largeClosedPlacementFields hK0

end EventualClosedPlacementCertificate

/-! ## Adding the W15 finite complement -/

def largeWithThresholdSmallCasesOfEventualFiniteCertificateObligations
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (small : SmallComplement K0) :
    LargeWithThresholdSmallCases K0 where
  large := largeClosedPlacementFieldsOfEventualFiniteCertificateObligations O
  small := small

def finalGateOfEventualFiniteCertificateObligations
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (small : SmallComplement K0) :
    FinalGate :=
  FinalPachTothGateW15.of_largeWithThresholdSmallCases
    (largeWithThresholdSmallCasesOfEventualFiniteCertificateObligations
      O small)

theorem exactBlockTarget_of_eventualFiniteCertificateObligations_smallComplement
    {K0 k : Nat} (O : EventualFiniteCertificateObligations K0)
    (small : SmallComplement K0) (hk : 0 < k) :
    ExactBlockTarget k :=
  (largeWithThresholdSmallCasesOfEventualFiniteCertificateObligations
    O small).exactBlockTarget hk

theorem targetUpperConstructionFiveSixteen_of_eventualFiniteCertificateObligations_smallComplement
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (small : SmallComplement K0) :
    ExactTarget :=
  (largeWithThresholdSmallCasesOfEventualFiniteCertificateObligations
    O small).targetUpperConstructionFiveSixteen

theorem targetEventually_of_eventualFiniteCertificateObligations_smallComplement
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (small : SmallComplement K0) :
    EventualTarget :=
  (largeWithThresholdSmallCasesOfEventualFiniteCertificateObligations
    O small).targetUpperConstructionFiveSixteenEventually

theorem targetArbitrary_of_eventualFiniteCertificateObligations_smallComplement
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (small : SmallComplement K0) :
    ArbitraryTarget :=
  (largeWithThresholdSmallCasesOfEventualFiniteCertificateObligations
    O small).targetUpperConstructionFiveSixteenArbitrary

theorem exact_eventual_arbitrary_of_eventualFiniteCertificateObligations_smallComplement
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (small : SmallComplement K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (largeWithThresholdSmallCasesOfEventualFiniteCertificateObligations
    O small).exact_eventual_arbitrary

def finalGateOfEventualFiniteCertificateObligations_atMostOne
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (hK0 : K0 <= 1) :
    FinalGate :=
  FinalPachTothGateW15.of_largeClosedPlacementFields_atMostOne
    (largeClosedPlacementFieldsOfEventualFiniteCertificateObligations O)
    hK0

theorem exact_eventual_arbitrary_of_eventualFiniteCertificateObligations_atMostOne
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (hK0 : K0 <= 1) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  LargeThresholdSmallCasesW15.exact_eventual_arbitrary_atMostOne
    (largeClosedPlacementFieldsOfEventualFiniteCertificateObligations O)
    hK0

structure EventualClosedPlacementWithSmallComplement (K0 : Nat) where
  certificate : EventualClosedPlacementCertificate K0
  small : SmallComplement K0

namespace EventualClosedPlacementWithSmallComplement

def toLargeWithThresholdSmallCases
    {K0 : Nat} (C : EventualClosedPlacementWithSmallComplement K0) :
    LargeWithThresholdSmallCases K0 where
  large := C.certificate.largeClosedPlacementFields
  small := C.small

def finalGate
    {K0 : Nat} (C : EventualClosedPlacementWithSmallComplement K0) :
    FinalGate :=
  FinalPachTothGateW15.of_largeWithThresholdSmallCases
    C.toLargeWithThresholdSmallCases

theorem exactBlockTarget
    {K0 k : Nat} (C : EventualClosedPlacementWithSmallComplement K0)
    (hk : 0 < k) :
    ExactBlockTarget k :=
  C.toLargeWithThresholdSmallCases.exactBlockTarget hk

theorem targetUpperConstructionFiveSixteen
    {K0 : Nat} (C : EventualClosedPlacementWithSmallComplement K0) :
    ExactTarget :=
  C.toLargeWithThresholdSmallCases.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (C : EventualClosedPlacementWithSmallComplement K0) :
    EventualTarget :=
  C.toLargeWithThresholdSmallCases.targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (C : EventualClosedPlacementWithSmallComplement K0) :
    ArbitraryTarget :=
  C.toLargeWithThresholdSmallCases.targetUpperConstructionFiveSixteenArbitrary

theorem exact_eventual_arbitrary
    {K0 : Nat} (C : EventualClosedPlacementWithSmallComplement K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  C.toLargeWithThresholdSmallCases.exact_eventual_arbitrary

end EventualClosedPlacementWithSmallComplement

/-! ## W15 all-positive rows to large fields -/

def allPositiveFiniteFieldsOfRows
    (R : AllPositiveCertificateRows) :
    AllPositiveFiniteFields :=
  R.fields

def largeClosedPlacementFieldsOfAllPositiveFiniteFields
    (K0 : Nat) (F : AllPositiveFiniteFields) :
    LargeClosedPlacementFields K0 :=
  LargeClosedPlacementInstantiationW13.largeClosedPlacementFieldsOfAllPositiveFiniteFields
    K0 F

def largeClosedPlacementFieldsOfAllPositiveCertificateRows
    (K0 : Nat) (R : AllPositiveCertificateRows) :
    LargeClosedPlacementFields K0 :=
  largeClosedPlacementFieldsOfAllPositiveFiniteFields K0
    (allPositiveFiniteFieldsOfRows R)

def largeWithAllPositiveFiniteFieldsOfRows
    (K0 : Nat) (R : AllPositiveCertificateRows) :
    LargeSmallCaseClosureW14.LargeWithAllPositiveFiniteFields K0 where
  large := largeClosedPlacementFieldsOfAllPositiveCertificateRows K0 R
  finite := allPositiveFiniteFieldsOfRows R

theorem exact_eventual_arbitrary_of_allPositiveCertificateRows
    (K0 : Nat) (R : AllPositiveCertificateRows) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (largeWithAllPositiveFiniteFieldsOfRows K0 R).exact_eventual_arbitrary

def finalGateOfAllPositiveCertificateRows
    (R : AllPositiveCertificateRows) :
    FinalGate :=
  FinalPachTothGateW15.of_exact_arbitrary
    R.targetUpperConstructionFiveSixteen
    R.targetUpperConstructionFiveSixteenArbitrary

end

end EventualClosedPlacementCertificateW16
end PachToth
end ErdosProblems1066
