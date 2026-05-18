import ErdosProblems1066.PachToth.AllPositiveInputsProducerW18
import ErdosProblems1066.PachToth.PeriodBaseFixingProducerW18
import ErdosProblems1066.PachToth.FinalPachTothGateW15

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementObstructionBypassW19

noncomputable section

abbrev BaseFixingCertificate :=
  PeriodBaseFixingProducerW18.Certificate

abbrev ViableConnectorTransitionPackage :=
  PeriodBaseFixingProducerW18.ViableConnectorTransitionPackage

abbrev StrongConnectorLift :=
  PeriodBaseFixingProducerW18.StrongConnectorLift

abbrev AllPositiveFinalCertificateInputs :=
  AllPositiveInputsProducerW18.AllPositiveFinalCertificateInputs

abbrev AllPositiveFinalCertificateValueInputs :=
  AllPositiveInputsProducerW18.AllPositiveFinalCertificateValueInputs

abbrev ExplicitClosedPlacementRemainingGate (K0 : Nat) :=
  LargeThresholdSmallCasesW15.LargeWithThresholdSmallCases K0

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeThresholdSmallCasesW15.LargeClosedPlacementFields K0

abbrev SmallComplement (K0 : Nat) :=
  LargeThresholdSmallCasesW15.SmallComplement K0

abbrev FinalGate :=
  FinalPachTothGateW15.FinalGate

abbrev ExactTarget : Prop :=
  LargeThresholdSmallCasesW15.ExactTarget

abbrev EventualTarget : Prop :=
  LargeThresholdSmallCasesW15.EventualTarget

abbrev ArbitraryTarget : Prop :=
  LargeThresholdSmallCasesW15.ArbitraryTarget

theorem not_nonempty_baseFixingCertificate :
    Not (Nonempty BaseFixingCertificate) :=
  PeriodBaseFixingProducerW18.not_nonempty_certificate

theorem not_nonempty_allPositiveFinalCertificateInputs :
    Not (Nonempty AllPositiveFinalCertificateInputs) := by
  intro h
  cases h with
  | intro I =>
      exact not_nonempty_baseFixingCertificate (Nonempty.intro I.base)

theorem not_nonempty_allPositiveFinalCertificateValueInputs :
    Not (Nonempty AllPositiveFinalCertificateValueInputs) := by
  intro h
  cases h with
  | intro I =>
      exact not_nonempty_baseFixingCertificate (Nonempty.intro I.base)

theorem not_strongConnectorLift
    (P : ViableConnectorTransitionPackage) :
    Not (StrongConnectorLift P) :=
  PeriodBaseFixingProducerW18.not_strongConnectorLift P

theorem not_exists_baseFixingCertificate_projecting
    (P : ViableConnectorTransitionPackage) :
    Not
      (exists C : BaseFixingCertificate,
        PeriodBaseFixingProducerW18.connectorFactsOfRoleHingeTransitions
          C.transitions = P.transitions) :=
  PeriodBaseFixingProducerW18.not_exists_certificate_projecting P

def explicitClosedPlacementRemainingGate
    {K0 : Nat} (large : LargeClosedPlacementFields K0)
    (small : SmallComplement K0) :
    ExplicitClosedPlacementRemainingGate K0 where
  large := large
  small := small

def finalGateOfExplicitClosedPlacementRemainingGate
    {K0 : Nat} (G : ExplicitClosedPlacementRemainingGate K0) :
    FinalGate :=
  FinalPachTothGateW15.of_largeWithThresholdSmallCases G

theorem explicitClosedPlacementRemainingGate_exact_eventual_arbitrary
    {K0 : Nat} (G : ExplicitClosedPlacementRemainingGate K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  G.exact_eventual_arbitrary

theorem explicitClosedPlacementRemainingGate_exact
    {K0 : Nat} (G : ExplicitClosedPlacementRemainingGate K0) :
    ExactTarget :=
  (explicitClosedPlacementRemainingGate_exact_eventual_arbitrary G).1

theorem explicitClosedPlacementRemainingGate_eventual
    {K0 : Nat} (G : ExplicitClosedPlacementRemainingGate K0) :
    EventualTarget :=
  (explicitClosedPlacementRemainingGate_exact_eventual_arbitrary G).2.1

theorem explicitClosedPlacementRemainingGate_arbitrary
    {K0 : Nat} (G : ExplicitClosedPlacementRemainingGate K0) :
    ArbitraryTarget :=
  (explicitClosedPlacementRemainingGate_exact_eventual_arbitrary G).2.2

theorem w18_allPositive_baseFixing_blocked_explicitClosedPlacement_gate
    {K0 : Nat} :
    Not (Nonempty BaseFixingCertificate) /\
      Not (Nonempty AllPositiveFinalCertificateInputs) /\
        Not (Nonempty AllPositiveFinalCertificateValueInputs) /\
          (ExplicitClosedPlacementRemainingGate K0 ->
            ExactTarget /\ EventualTarget /\ ArbitraryTarget) := by
  exact
    And.intro
      not_nonempty_baseFixingCertificate
      (And.intro
        not_nonempty_allPositiveFinalCertificateInputs
        (And.intro
          not_nonempty_allPositiveFinalCertificateValueInputs
          explicitClosedPlacementRemainingGate_exact_eventual_arbitrary))

end

end ClosedPlacementObstructionBypassW19
end PachToth
end ErdosProblems1066
