import ErdosProblems1066.PachToth.AllPositiveFinalCertificateW17
import ErdosProblems1066.PachToth.SmallRowValueCertificatesW17
import ErdosProblems1066.PachToth.TailValueCertificateConcreteW17

set_option autoImplicit false

/-!
# W18 all-positive input producer

This file is an ownership-local adapter: it does not assert any missing
search result.  It assembles the PT1-PT6-style concrete input families into
the final W17 all-positive certificate input bundles.
-/

namespace ErdosProblems1066
namespace PachToth
namespace AllPositiveInputsProducerW18

noncomputable section

abbrev PeriodBaseFixingCertificate :=
  AllPositiveFinalCertificateW17.PeriodBaseFixingCertificate

abbrev PeriodCandidateFamily :=
  AllPositiveFinalCertificateW17.PeriodCandidateFamily

abbrev PeriodRows :=
  AllPositiveFinalCertificateW17.PeriodRows

abbrev PeriodCompatibility :=
  AllPositiveFinalCertificateW17.PeriodCompatibility

abbrev CandidateLengthTwoThreeRows :=
  AllPositiveFinalCertificateW17.CandidateLengthTwoThreeRows

abbrev CandidateLengthFourFiveRows :=
  AllPositiveFinalCertificateW17.CandidateLengthFourFiveRows

abbrev CandidateTailRows :=
  AllPositiveFinalCertificateW17.CandidateTailRows

abbrev TailValueRows :=
  AllPositiveFinalCertificateW17.TailValueRows

abbrev CandidateLengthTwoThreeValueRows
    (F : PeriodCandidateFamily) :=
  SmallRowValueCertificatesW17.CandidateLengthTwoThreeValueRows F

abbrev CandidateLengthFourFiveValueRows
    (F : PeriodCandidateFamily) :=
  SmallRowValueCertificatesW17.CandidateLengthFourFiveValueRows F

abbrev TailPolynomialCertificateFamily
    (F : PeriodCandidateFamily) :=
  TailValueCertificateConcreteW17.TailPolynomialCertificateFamily
    F.toRoleHingedPeriodSearchFamily

abbrev TailValueFunctionCertificateFamily
    (F : PeriodCandidateFamily) :=
  TailValueCertificateConcreteW17.TailValueFunctionCertificateFamily
    F.toRoleHingedPeriodSearchFamily

abbrev TailValueListCertificateFamily
    (F : PeriodCandidateFamily) :=
  TailValueCertificateConcreteW17.TailValueListCertificateFamily
    F.toRoleHingedPeriodSearchFamily

abbrev AllPositiveFinalCertificateInputs :=
  AllPositiveFinalCertificateW17.AllPositiveFinalCertificateInputs

abbrev AllPositiveFinalCertificateValueInputs :=
  AllPositiveFinalCertificateW17.AllPositiveFinalCertificateValueInputs

abbrev AllPositiveCertificateRows :=
  AllPositiveFinalCertificateW17.AllPositiveCertificateRows

abbrev AllPositiveNonConnectorFields :=
  AllPositiveFinalCertificateW17.AllPositiveNonConnectorFields

abbrev ExplicitAllPositiveCertificate :=
  AllPositiveFinalCertificateW17.ExplicitAllPositiveCertificate

abbrev ExactBlockTarget :=
  AllPositiveFinalCertificateW17.ExactBlockTarget

abbrev ExactTarget :=
  AllPositiveFinalCertificateW17.ExactTarget

abbrev ArbitraryTarget :=
  AllPositiveFinalCertificateW17.ArbitraryTarget

def periodRowsOfBaseFixingCertificate
    (base : PeriodBaseFixingCertificate) :
    PeriodRows :=
  AllPositiveFinalCertificateW17.periodRowsOfBaseFixingCertificate base

def rowInputsOfFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveRows periodCandidate)
    (tail : CandidateTailRows periodCandidate) :
    AllPositiveFinalCertificateInputs where
  base := base
  periodCandidate := periodCandidate
  compatibility := compatibility
  smallTwoThree := smallTwoThree
  smallFourFive := smallFourFive
  tail := tail

def valueInputsOfRowsAndTailValues
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveRows periodCandidate)
    (tail : TailValueRows periodCandidate) :
    AllPositiveFinalCertificateValueInputs where
  base := base
  periodCandidate := periodCandidate
  compatibility := compatibility
  smallTwoThree := smallTwoThree
  smallFourFive := smallFourFive
  tail := tail

def valueInputsOfFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeValueRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveValueRows periodCandidate)
    (tail : TailValueRows periodCandidate) :
    AllPositiveFinalCertificateValueInputs :=
  valueInputsOfRowsAndTailValues base periodCandidate compatibility
    smallTwoThree.toBlockPairGeneratedPointInequalities
    smallFourFive.toBlockPairGeneratedPointInequalities
    tail

def valueInputsOfTailPolynomialCertificates
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeValueRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveValueRows periodCandidate)
    (tail : TailPolynomialCertificateFamily periodCandidate) :
    AllPositiveFinalCertificateValueInputs :=
  valueInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive
    (TailValueCertificateConcreteW17.TailPolynomialCertificateFamily.toTailValueRows
      tail)

def valueInputsOfTailFunctionCertificates
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeValueRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveValueRows periodCandidate)
    (tail : TailValueFunctionCertificateFamily periodCandidate) :
    AllPositiveFinalCertificateValueInputs :=
  valueInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive
    (TailValueCertificateConcreteW17.TailValueFunctionCertificateFamily.toTailValueRows
      tail)

def valueInputsOfTailListCertificates
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeValueRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveValueRows periodCandidate)
    (tail : TailValueListCertificateFamily periodCandidate) :
    AllPositiveFinalCertificateValueInputs :=
  valueInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive
    (TailValueCertificateConcreteW17.TailValueListCertificateFamily.toTailValueRows
      tail)

def rowsOfFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveRows periodCandidate)
    (tail : CandidateTailRows periodCandidate) :
    AllPositiveCertificateRows :=
  (rowInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive tail).rows

def fieldsOfFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveRows periodCandidate)
    (tail : CandidateTailRows periodCandidate) :
    AllPositiveNonConnectorFields :=
  (rowInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive tail).fields

def explicitCertificateOfFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveRows periodCandidate)
    (tail : CandidateTailRows periodCandidate) :
    ExplicitAllPositiveCertificate :=
  (rowInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive tail).explicitCertificate

theorem exactBlockTarget_ofFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveRows periodCandidate)
    (tail : CandidateTailRows periodCandidate)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  (rowInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive tail).targetUpperConstructionFiveSixteenAt
      k hk

theorem exactTarget_ofFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveRows periodCandidate)
    (tail : CandidateTailRows periodCandidate) :
    ExactTarget :=
  (rowInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive tail).targetUpperConstructionFiveSixteen

theorem arbitraryTarget_ofFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveRows periodCandidate)
    (tail : CandidateTailRows periodCandidate) :
    ArbitraryTarget :=
  (rowInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive tail).targetUpperConstructionFiveSixteenArbitrary

theorem exactBlockTarget_ofValueFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeValueRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveValueRows periodCandidate)
    (tail : TailValueRows periodCandidate)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  (valueInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive tail).targetUpperConstructionFiveSixteenAt
      k hk

theorem exactTarget_ofValueFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeValueRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveValueRows periodCandidate)
    (tail : TailValueRows periodCandidate) :
    ExactTarget :=
  (valueInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive tail).targetUpperConstructionFiveSixteen

theorem arbitraryTarget_ofValueFamilies
    (base : PeriodBaseFixingCertificate)
    (periodCandidate : PeriodCandidateFamily)
    (compatibility :
      PeriodCompatibility
        (periodRowsOfBaseFixingCertificate base)
        periodCandidate)
    (smallTwoThree : CandidateLengthTwoThreeValueRows periodCandidate)
    (smallFourFive : CandidateLengthFourFiveValueRows periodCandidate)
    (tail : TailValueRows periodCandidate) :
    ArbitraryTarget :=
  (valueInputsOfFamilies base periodCandidate compatibility
    smallTwoThree smallFourFive tail).targetUpperConstructionFiveSixteenArbitrary

end

end AllPositiveInputsProducerW18
end PachToth
end ErdosProblems1066
