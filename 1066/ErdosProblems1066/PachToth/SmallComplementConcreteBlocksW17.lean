import ErdosProblems1066.PachToth.SmallComplementExactBlocksW16
import ErdosProblems1066.PachToth.AllPositiveCertificateAssemblyW15
import ErdosProblems1066.PachToth.SmallLengthClosureW11

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace SmallComplementConcreteBlocksW17

noncomputable section

abbrev SmallComplement (K0 : Nat) : Prop :=
  SmallComplementExactBlocksW16.SmallComplement K0

abbrev AllPositiveCertificateRows :=
  AllPositiveCertificateAssemblyW15.AllPositiveCertificateRows

abbrev ExactMissingConcreteRowFamily :=
  AllPositiveCertificateAssemblyW15.ExactMissingConcreteRowFamily

abbrev SmallLengthRowsWithTail :=
  AllPositiveCertificateAssemblyW15.SmallLengthRowsWithTail

abbrev CandidatePolynomialCertificateFamily :=
  AllPositiveCertificateAssemblyW15.CandidatePolynomialCertificateFamily

abbrev PeriodRows :=
  AllPositiveCertificateAssemblyW15.PeriodRows

abbrev RemainingRowFamily :=
  AllPositiveCertificateAssemblyW15.RemainingRowFamily

abbrev SmallLengthExactBlockTargets :=
  SmallLengthClosureW11.SmallLengthExactBlockTargets

abbrev LengthFourFiveExactBlockTargets :=
  LengthFourFiveCaseW11.LengthFourFiveExactBlockTargets

def blockThresholdSix : Nat := 6

def blockThresholdSeven : Nat :=
  SmallComplementExactBlocksW16.pt7K0

theorem targetUpperConstructionFiveSixteenSmallUpTo_six_of_allPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * blockThresholdSix) :=
  SmallComplementExactBlocksW16.targetUpperConstructionFiveSixteenSmallUpTo_of_allPositiveFields
    blockThresholdSix C.fields

theorem smallComplement_six_of_allPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    SmallComplement blockThresholdSix :=
  SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
    blockThresholdSix C.fields

theorem smallComplement_seven_of_allPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    SmallComplement blockThresholdSeven :=
  SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
    blockThresholdSeven C.fields

theorem smallComplement_six_of_periodRowsAndNonConnectorRows
    (periodRows : PeriodRows)
    (polynomialRows :
      RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    SmallComplement blockThresholdSix :=
  smallComplement_six_of_allPositiveCertificateRows
    (AllPositiveCertificateAssemblyW15.rowsOfPeriodRowsAndNonConnectorRows
      periodRows polynomialRows)

theorem smallComplement_seven_of_periodRowsAndNonConnectorRows
    (periodRows : PeriodRows)
    (polynomialRows :
      RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    SmallComplement blockThresholdSeven :=
  smallComplement_seven_of_allPositiveCertificateRows
    (AllPositiveCertificateAssemblyW15.rowsOfPeriodRowsAndNonConnectorRows
      periodRows polynomialRows)

theorem targetUpperConstructionFiveSixteenSmallUpTo_six_of_rowFamily
    {F : AllPositiveCertificateAssemblyW15.PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * blockThresholdSix) :=
  SmallComplementExactBlocksW16.targetUpperConstructionFiveSixteenSmallUpTo_of_allPositiveFields
    blockThresholdSix
    (AllPositiveCertificateAssemblyW15.fieldsOfRowFamily R)

theorem smallComplement_six_of_rowFamily
    {F : AllPositiveCertificateAssemblyW15.PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    SmallComplement blockThresholdSix :=
  SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
    blockThresholdSix
    (AllPositiveCertificateAssemblyW15.fieldsOfRowFamily R)

theorem smallComplement_seven_of_rowFamily
    {F : AllPositiveCertificateAssemblyW15.PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    SmallComplement blockThresholdSeven :=
  SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
    blockThresholdSeven
    (AllPositiveCertificateAssemblyW15.fieldsOfRowFamily R)

theorem smallComplement_six_of_smallLengthRowsWithTail
    {F : AllPositiveCertificateAssemblyW15.PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F) :
    SmallComplement blockThresholdSix :=
  SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
    blockThresholdSix
    (AllPositiveCertificateAssemblyW15.fieldsOfSmallLengthRowsWithTail H)

theorem smallComplement_seven_of_smallLengthRowsWithTail
    {F : AllPositiveCertificateAssemblyW15.PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F) :
    SmallComplement blockThresholdSeven :=
  SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
    blockThresholdSeven
    (AllPositiveCertificateAssemblyW15.fieldsOfSmallLengthRowsWithTail H)

theorem smallComplement_six_of_candidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    SmallComplement blockThresholdSix :=
  SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
    blockThresholdSix
    (AllPositiveCertificateAssemblyW15.fieldsOfCandidatePolynomialCertificateFamily C)

theorem smallComplement_seven_of_candidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    SmallComplement blockThresholdSeven :=
  SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields
    blockThresholdSeven
    (AllPositiveCertificateAssemblyW15.fieldsOfCandidatePolynomialCertificateFamily C)

structure ExactBlocksTwoThroughFive where
  lengthTwo : targetUpperConstructionFiveSixteenAt (16 * 2)
  lengthThree : targetUpperConstructionFiveSixteenAt (16 * 3)
  lengthFourFive : LengthFourFiveExactBlockTargets

namespace ExactBlocksTwoThroughFive

def toSmallLengthExactBlockTargets
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ExactBlocksTwoThroughFive)
    (oneBlock :
      ExactBlockCertificateW13.ConcreteOneBlockCertificate orientation) :
    SmallLengthExactBlockTargets where
  lengthOne := by
    simpa using
      ExactBlockCertificateW13.targetUpperConstructionFiveSixteenAt_of_concreteOneBlockCertificate
        oneBlock
  lengthTwo := C.lengthTwo
  lengthThree := C.lengthThree
  lengthFour := C.lengthFourFive.lengthFour
  lengthFive := C.lengthFourFive.lengthFive

theorem targetUpperConstructionFiveSixteenSmallUpTo_six
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ExactBlocksTwoThroughFive)
    (oneBlock :
      ExactBlockCertificateW13.ConcreteOneBlockCertificate orientation) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * blockThresholdSix) := by
  simpa [blockThresholdSix] using
    (C.toSmallLengthExactBlockTargets oneBlock).smallUpToSix

theorem smallComplement_six
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ExactBlocksTwoThroughFive)
    (oneBlock :
      ExactBlockCertificateW13.ConcreteOneBlockCertificate orientation) :
    SmallComplement blockThresholdSix := by
  simpa [SmallComplement, blockThresholdSix,
    SmallComplementExactBlocksW16.SmallComplement] using
    C.targetUpperConstructionFiveSixteenSmallUpTo_six oneBlock

end ExactBlocksTwoThroughFive

theorem smallComplement_six_of_smallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    SmallComplement blockThresholdSix := by
  simpa [SmallComplement, blockThresholdSix,
    SmallComplementExactBlocksW16.SmallComplement] using C.smallUpToSix

end

end SmallComplementConcreteBlocksW17
end PachToth
end ErdosProblems1066
