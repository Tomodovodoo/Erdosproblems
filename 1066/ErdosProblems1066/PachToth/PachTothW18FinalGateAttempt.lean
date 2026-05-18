import ErdosProblems1066.PachToth.AllPositiveFinalCertificateW17
import ErdosProblems1066.PachToth.LargeK0ExplicitSeparationDataW17
import ErdosProblems1066.PachToth.SmallComplementConcreteBlocksW17
import ErdosProblems1066.PachToth.PachTothEventualFinalGateW17

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW18FinalGateAttempt

noncomputable section

abbrev AllPositiveFinalCertificateInputs :=
  AllPositiveFinalCertificateW17.AllPositiveFinalCertificateInputs

abbrev AllPositiveFinalCertificateValueInputs :=
  AllPositiveFinalCertificateW17.AllPositiveFinalCertificateValueInputs

abbrev AllPositiveCertificateRows :=
  AllPositiveFinalCertificateW17.AllPositiveCertificateRows

abbrev AllPositiveNonConnectorFields :=
  AllPositiveFinalCertificateW17.AllPositiveNonConnectorFields

abbrev EventualFinalGatePackage (K0 : Nat) :=
  PachTothEventualFinalGateW17.EventualFinalGatePackage K0

abbrev LargeKCrossBlockDistanceFields (K0 : Nat) :=
  PachTothEventualFinalGateW17.LargeKCrossBlockDistanceFields K0

abbrev SmallComplement (K0 : Nat) :=
  PachTothEventualFinalGateW17.SmallComplement K0

abbrev ExactTarget : Prop :=
  PachTothEventualFinalGateW17.ExactTarget

abbrev EventualTarget : Prop :=
  PachTothEventualFinalGateW17.EventualTarget

abbrev ArbitraryTarget : Prop :=
  PachTothEventualFinalGateW17.ArbitraryTarget

abbrev FixedTarget (n : Nat) : Prop :=
  PachTothEventualFinalGateW17.FixedTarget n

abbrev FinalGate :=
  PachTothEventualFinalGateW17.FinalGate

def explicitK0 : Nat :=
  LargeK0ExplicitSeparationDataW17.explicitK0

theorem explicitK0_eq_one : explicitK0 = 1 := by
  simp [explicitK0, LargeK0ExplicitSeparationDataW17.explicitK0]

def largeKCrossBlockDistanceFieldsOfAllPositiveFields
    (F : AllPositiveNonConnectorFields) :
    LargeKCrossBlockDistanceFields explicitK0 :=
  LargeK0ExplicitSeparationDataW17.largeKCrossBlockDistanceFieldsOfAllPositive
    F

def largeKCrossBlockDistanceFieldsOfAllPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) :
    LargeKCrossBlockDistanceFields explicitK0 :=
  largeKCrossBlockDistanceFieldsOfAllPositiveFields I.fields

def largeKCrossBlockDistanceFieldsOfAllPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs) :
    LargeKCrossBlockDistanceFields explicitK0 :=
  largeKCrossBlockDistanceFieldsOfAllPositiveFinalCertificateInputs I.toInputs

theorem smallComplement_explicitK0_of_allPositiveFields
    (F : AllPositiveNonConnectorFields) :
    SmallComplement explicitK0 :=
  SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
    explicitK0 F

theorem smallComplement_explicitK0_of_allPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) :
    SmallComplement explicitK0 :=
  smallComplement_explicitK0_of_allPositiveFields I.fields

theorem smallComplement_explicitK0_of_allPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs) :
    SmallComplement explicitK0 :=
  smallComplement_explicitK0_of_allPositiveFinalCertificateInputs I.toInputs

theorem smallComplement_blockThresholdSix_of_allPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) :
    SmallComplement SmallComplementConcreteBlocksW17.blockThresholdSix :=
  SmallComplementConcreteBlocksW17.smallComplement_six_of_allPositiveCertificateRows
    I.rows

theorem smallComplement_blockThresholdSeven_of_allPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) :
    SmallComplement SmallComplementConcreteBlocksW17.blockThresholdSeven :=
  SmallComplementConcreteBlocksW17.smallComplement_seven_of_allPositiveCertificateRows
    I.rows

def eventualFinalGatePackageOfLargeKCrossBlockDistanceFieldsSmallComplement
    {K0 : Nat} (large : LargeKCrossBlockDistanceFields K0)
    (small : SmallComplement K0) :
    EventualFinalGatePackage K0 :=
  PachTothEventualFinalGateW17.of_crossBlockDistanceFields_smallComplement
    large small

def eventualFinalGatePackageOfAllPositiveFields
    (F : AllPositiveNonConnectorFields) :
    EventualFinalGatePackage explicitK0 :=
  eventualFinalGatePackageOfLargeKCrossBlockDistanceFieldsSmallComplement
    (largeKCrossBlockDistanceFieldsOfAllPositiveFields F)
    (smallComplement_explicitK0_of_allPositiveFields F)

def eventualFinalGatePackageOfAllPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) :
    EventualFinalGatePackage explicitK0 :=
  eventualFinalGatePackageOfAllPositiveFields I.fields

def eventualFinalGatePackageOfAllPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs) :
    EventualFinalGatePackage explicitK0 :=
  eventualFinalGatePackageOfAllPositiveFinalCertificateInputs I.toInputs

def finalGateOfAllPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) :
    FinalGate :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateInputs I).finalGate

def finalGateOfAllPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs) :
    FinalGate :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateValueInputs I).finalGate

theorem exact_eventual_arbitrary_of_allPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateInputs I).exact_eventual_arbitrary

theorem exact_eventual_arbitrary_of_allPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateValueInputs I).exact_eventual_arbitrary

theorem targetUpperConstructionFiveSixteen_of_allPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) :
    ExactTarget :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateInputs I).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteen_of_allPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs) :
    ExactTarget :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateValueInputs I)
    |>.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenEventually_of_allPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) :
    EventualTarget :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateInputs I)
    |>.targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteenEventually_of_allPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs) :
    EventualTarget :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateValueInputs I)
    |>.targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteenArbitrary_of_allPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) :
    ArbitraryTarget :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateInputs I)
    |>.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenArbitrary_of_allPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs) :
    ArbitraryTarget :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateValueInputs I)
    |>.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt_of_allPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) (n : Nat) :
    FixedTarget n :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateInputs I)
    |>.targetUpperConstructionFiveSixteenAt n

theorem targetUpperConstructionFiveSixteenAt_of_allPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs) (n : Nat) :
    FixedTarget n :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateValueInputs I)
    |>.targetUpperConstructionFiveSixteenAt n

theorem upper_bound_five_sixteen_exact_of_allPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateInputs I).upper_bound_five_sixteen_exact
    k hk

theorem upper_bound_five_sixteen_exact_of_allPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateValueInputs I)
    |>.upper_bound_five_sixteen_exact k hk

theorem upper_bound_five_sixteen_arbitrary_of_allPositiveFinalCertificateInputs
    (I : AllPositiveFinalCertificateInputs) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateInputs I).upper_bound_five_sixteen_arbitrary
    n

theorem upper_bound_five_sixteen_arbitrary_of_allPositiveFinalCertificateValueInputs
    (I : AllPositiveFinalCertificateValueInputs) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  (eventualFinalGatePackageOfAllPositiveFinalCertificateValueInputs I)
    |>.upper_bound_five_sixteen_arbitrary n

end

end PachTothW18FinalGateAttempt

open PachTothW18FinalGateAttempt

theorem upper_bound_five_sixteen_exact_of_w18_allPositiveFinalCertificateInputs
    (I : PachTothW18FinalGateAttempt.AllPositiveFinalCertificateInputs)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachTothW18FinalGateAttempt.upper_bound_five_sixteen_exact_of_allPositiveFinalCertificateInputs
    I k hk

theorem upper_bound_five_sixteen_arbitrary_of_w18_allPositiveFinalCertificateInputs
    (I : PachTothW18FinalGateAttempt.AllPositiveFinalCertificateInputs)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  upper_bound_five_sixteen_arbitrary_of_allPositiveFinalCertificateInputs I n

theorem upper_bound_five_sixteen_exact_of_w18_allPositiveFinalCertificateValueInputs
    (I : PachTothW18FinalGateAttempt.AllPositiveFinalCertificateValueInputs)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  upper_bound_five_sixteen_exact_of_allPositiveFinalCertificateValueInputs
    I k hk

theorem upper_bound_five_sixteen_arbitrary_of_w18_allPositiveFinalCertificateValueInputs
    (I : PachTothW18FinalGateAttempt.AllPositiveFinalCertificateValueInputs)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  upper_bound_five_sixteen_arbitrary_of_allPositiveFinalCertificateValueInputs
    I n

end PachToth

namespace Verified

abbrev PachTothW18AllPositiveFinalCertificateInputs :=
  PachToth.PachTothW18FinalGateAttempt.AllPositiveFinalCertificateInputs

abbrev PachTothW18AllPositiveFinalCertificateValueInputs :=
  PachToth.PachTothW18FinalGateAttempt.AllPositiveFinalCertificateValueInputs

theorem upper_bound_five_sixteen_exact_of_pachtoth_w18_allPositiveFinalCertificateInputs
    (I : PachTothW18AllPositiveFinalCertificateInputs)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w18_allPositiveFinalCertificateInputs
    I k hk

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w18_allPositiveFinalCertificateInputs
    (I : PachTothW18AllPositiveFinalCertificateInputs)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w18_allPositiveFinalCertificateInputs
    I n

theorem upper_bound_five_sixteen_exact_of_pachtoth_w18_allPositiveFinalCertificateValueInputs
    (I : PachTothW18AllPositiveFinalCertificateValueInputs)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w18_allPositiveFinalCertificateValueInputs
    I k hk

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w18_allPositiveFinalCertificateValueInputs
    (I : PachTothW18AllPositiveFinalCertificateValueInputs)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w18_allPositiveFinalCertificateValueInputs
    I n

end Verified
end ErdosProblems1066
