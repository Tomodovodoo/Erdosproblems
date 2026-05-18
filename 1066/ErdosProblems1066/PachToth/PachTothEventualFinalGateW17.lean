import ErdosProblems1066.PachToth.LargeKGlobalSeparationW16
import ErdosProblems1066.PachToth.SmallComplementExactBlocksW16
import ErdosProblems1066.PachToth.EventualClosedPlacementCertificateW16
import ErdosProblems1066.PachToth.FinalPachTothGateW15

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace PachTothEventualFinalGateW17

noncomputable section

open EventualClosedPlacementCertificateW16

abbrev ExactTarget : Prop :=
  EventualClosedPlacementCertificateW16.ExactTarget

abbrev EventualTarget : Prop :=
  EventualClosedPlacementCertificateW16.EventualTarget

abbrev ArbitraryTarget : Prop :=
  EventualClosedPlacementCertificateW16.ArbitraryTarget

abbrev FixedTarget (n : Nat) : Prop :=
  FinalPachTothGateW15.FixedTarget n

abbrev FinalGate :=
  FinalPachTothGateW15.FinalGate

abbrev EventualFiniteCertificateObligations (K0 : Nat) :=
  EventualClosedPlacementCertificateW16.EventualFiniteCertificateObligations K0

abbrev EventualClosedPlacementCertificate (K0 : Nat) :=
  EventualClosedPlacementCertificateW16.EventualClosedPlacementCertificate K0

abbrev EventualClosedPlacementWithSmallComplement (K0 : Nat) :=
  EventualClosedPlacementCertificateW16.EventualClosedPlacementWithSmallComplement K0

abbrev LargeWithThresholdSmallCases (K0 : Nat) :=
  EventualClosedPlacementCertificateW16.LargeWithThresholdSmallCases K0

abbrev SmallComplement (K0 : Nat) :=
  EventualClosedPlacementCertificateW16.SmallComplement K0

abbrev AllPositiveFields :=
  SmallComplementExactBlocksW16.AllPositiveFields

abbrev ConcreteValueMatrixFamily :=
  SmallComplementExactBlocksW16.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  SmallComplementExactBlocksW16.CandidateValueMatrixFamily

abbrev LargeKCrossBlockDistanceFields (K0 : Nat) :=
  LargeKGlobalSeparationW16.LargeKCrossBlockDistanceFields K0

abbrev LargeKNonConnectorSqDistanceFields (K0 : Nat) :=
  LargeKGlobalSeparationW16.LargeKNonConnectorSqDistanceFields K0

structure EventualFinalGatePackage (K0 : Nat) where
  obligations : EventualFiniteCertificateObligations K0
  small : SmallComplement K0

namespace EventualFinalGatePackage

def certificate
    {K0 : Nat} (P : EventualFinalGatePackage K0) :
    EventualClosedPlacementCertificate K0 where
  obligations := P.obligations

def withSmallComplement
    {K0 : Nat} (P : EventualFinalGatePackage K0) :
    EventualClosedPlacementWithSmallComplement K0 where
  certificate := P.certificate
  small := P.small

def toLargeWithThresholdSmallCases
    {K0 : Nat} (P : EventualFinalGatePackage K0) :
    LargeWithThresholdSmallCases K0 :=
  largeWithThresholdSmallCasesOfEventualFiniteCertificateObligations
    P.obligations P.small

def finalGate
    {K0 : Nat} (P : EventualFinalGatePackage K0) :
    FinalGate :=
  EventualClosedPlacementCertificateW16.finalGateOfEventualFiniteCertificateObligations
    P.obligations P.small

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : EventualFinalGatePackage K0) :
    EventualTarget :=
  targetEventually_of_eventualFiniteCertificateObligations_smallComplement
    P.obligations P.small

theorem targetUpperConstructionFiveSixteen
    {K0 : Nat} (P : EventualFinalGatePackage K0) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_eventualFiniteCertificateObligations_smallComplement
    P.obligations P.small

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : EventualFinalGatePackage K0) :
    ArbitraryTarget :=
  targetArbitrary_of_eventualFiniteCertificateObligations_smallComplement
    P.obligations P.small

theorem exact_eventual_arbitrary
    {K0 : Nat} (P : EventualFinalGatePackage K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  exact_eventual_arbitrary_of_eventualFiniteCertificateObligations_smallComplement
    P.obligations P.small

theorem targetUpperConstructionFiveSixteenAt
    {K0 : Nat} (P : EventualFinalGatePackage K0) (n : Nat) :
    FixedTarget n :=
  P.targetUpperConstructionFiveSixteenArbitrary n

theorem upper_bound_five_sixteen_exact
    {K0 : Nat} (P : EventualFinalGatePackage K0)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  P.finalGate.upper_bound_five_sixteen_exact k hk

theorem upper_bound_five_sixteen_arbitrary
    {K0 : Nat} (P : EventualFinalGatePackage K0) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  P.finalGate.upper_bound_five_sixteen_arbitrary n

end EventualFinalGatePackage

def of_eventualFiniteCertificateObligations_smallComplement
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (small : SmallComplement K0) :
    EventualFinalGatePackage K0 where
  obligations := O
  small := small

def of_eventualFiniteCertificateObligations_allPositiveFields
    (K0 : Nat) (O : EventualFiniteCertificateObligations K0)
    (F : AllPositiveFields) :
    EventualFinalGatePackage K0 :=
  of_eventualFiniteCertificateObligations_smallComplement
    O
    (SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields K0 F)

def of_eventualFiniteCertificateObligations_concreteValueMatrixFamily
    (K0 : Nat) (O : EventualFiniteCertificateObligations K0)
    (C : ConcreteValueMatrixFamily) :
    EventualFinalGatePackage K0 :=
  of_eventualFiniteCertificateObligations_smallComplement
    O
    (SmallComplementExactBlocksW16.smallComplement_of_concreteValueMatrixFamily
      K0 C)

def of_eventualFiniteCertificateObligations_candidateValueMatrixFamily
    (K0 : Nat) (O : EventualFiniteCertificateObligations K0)
    (C : CandidateValueMatrixFamily) :
    EventualFinalGatePackage K0 :=
  of_eventualFiniteCertificateObligations_smallComplement
    O
    (SmallComplementExactBlocksW16.smallComplement_of_candidateValueMatrixFamily
      K0 C)

def of_crossBlockDistanceFields_smallComplement
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (small : SmallComplement K0) :
    EventualFinalGatePackage K0 :=
  of_eventualFiniteCertificateObligations_smallComplement
    F.toEventualFiniteCertificateObligations small

def of_nonConnectorSqDistanceFields_smallComplement
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (small : SmallComplement K0) :
    EventualFinalGatePackage K0 :=
  of_eventualFiniteCertificateObligations_smallComplement
    F.toEventualFiniteCertificateObligations small

def of_crossBlockDistanceFields_allPositiveFields
    (K0 : Nat) (F : LargeKCrossBlockDistanceFields K0)
    (finite : AllPositiveFields) :
    EventualFinalGatePackage K0 :=
  of_crossBlockDistanceFields_smallComplement
    F
    (SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
      K0 finite)

def of_nonConnectorSqDistanceFields_allPositiveFields
    (K0 : Nat) (F : LargeKNonConnectorSqDistanceFields K0)
    (finite : AllPositiveFields) :
    EventualFinalGatePackage K0 :=
  of_nonConnectorSqDistanceFields_smallComplement
    F
    (SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
      K0 finite)

def of_crossBlockDistanceFields_concreteValueMatrixFamily
    (K0 : Nat) (F : LargeKCrossBlockDistanceFields K0)
    (finite : ConcreteValueMatrixFamily) :
    EventualFinalGatePackage K0 :=
  of_crossBlockDistanceFields_smallComplement
    F
    (SmallComplementExactBlocksW16.smallComplement_of_concreteValueMatrixFamily
      K0 finite)

def of_nonConnectorSqDistanceFields_concreteValueMatrixFamily
    (K0 : Nat) (F : LargeKNonConnectorSqDistanceFields K0)
    (finite : ConcreteValueMatrixFamily) :
    EventualFinalGatePackage K0 :=
  of_nonConnectorSqDistanceFields_smallComplement
    F
    (SmallComplementExactBlocksW16.smallComplement_of_concreteValueMatrixFamily
      K0 finite)

def of_crossBlockDistanceFields_candidateValueMatrixFamily
    (K0 : Nat) (F : LargeKCrossBlockDistanceFields K0)
    (finite : CandidateValueMatrixFamily) :
    EventualFinalGatePackage K0 :=
  of_crossBlockDistanceFields_smallComplement
    F
    (SmallComplementExactBlocksW16.smallComplement_of_candidateValueMatrixFamily
      K0 finite)

def of_nonConnectorSqDistanceFields_candidateValueMatrixFamily
    (K0 : Nat) (F : LargeKNonConnectorSqDistanceFields K0)
    (finite : CandidateValueMatrixFamily) :
    EventualFinalGatePackage K0 :=
  of_nonConnectorSqDistanceFields_smallComplement
    F
    (SmallComplementExactBlocksW16.smallComplement_of_candidateValueMatrixFamily
      K0 finite)

theorem exact_eventual_arbitrary_of_eventualFinalGatePackage
    {K0 : Nat} (P : EventualFinalGatePackage K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  P.exact_eventual_arbitrary

theorem upper_bound_five_sixteen_exact_of_eventualFinalGatePackage
    {K0 : Nat} (P : EventualFinalGatePackage K0)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  P.upper_bound_five_sixteen_exact k hk

theorem upper_bound_five_sixteen_arbitrary_of_eventualFinalGatePackage
    {K0 : Nat} (P : EventualFinalGatePackage K0) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  P.upper_bound_five_sixteen_arbitrary n

end

end PachTothEventualFinalGateW17

theorem upper_bound_five_sixteen_exact_of_w17_eventualFinalGatePackage
    {K0 : Nat}
    (P : PachTothEventualFinalGateW17.EventualFinalGatePackage K0)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachTothEventualFinalGateW17.upper_bound_five_sixteen_exact_of_eventualFinalGatePackage
    P k hk

theorem upper_bound_five_sixteen_arbitrary_of_w17_eventualFinalGatePackage
    {K0 : Nat}
    (P : PachTothEventualFinalGateW17.EventualFinalGatePackage K0)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  PachTothEventualFinalGateW17.upper_bound_five_sixteen_arbitrary_of_eventualFinalGatePackage
    P n

end PachToth

namespace Verified

abbrev PachTothW17EventualFinalGatePackage (K0 : Nat) :=
  PachToth.PachTothEventualFinalGateW17.EventualFinalGatePackage K0

theorem upper_bound_five_sixteen_exact_of_pachtoth_w17_eventualFinalGatePackage
    {K0 : Nat} (P : PachTothW17EventualFinalGatePackage K0)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w17_eventualFinalGatePackage
    P k hk

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w17_eventualFinalGatePackage
    {K0 : Nat} (P : PachTothW17EventualFinalGatePackage K0)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w17_eventualFinalGatePackage
    P n

end Verified
end ErdosProblems1066
