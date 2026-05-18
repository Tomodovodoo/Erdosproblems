import ErdosProblems1066.PachToth.SmallComplementConcreteBlocksW17
import ErdosProblems1066.PachToth.SmallRowValueCertificatesW17

set_option autoImplicit false

/-!
# W18 exact block producer for k = 2,3,4,5

This file owns only the adapter from the W17 small-row value certificates to
`SmallComplementConcreteBlocksW17.ExactBlocksTwoThroughFive`.

The k=2 and k=3 rows are routed through the same generic fixed-candidate lower
table used by the k=4 and k=5 exact-block route.  No new numerical certificates
are asserted here: the finite small-row lower bounds remain explicit inputs.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactBlocksTwoThroughFiveProducerW18

noncomputable section

abbrev PeriodCandidateFamily :=
  SmallRowValueCertificatesW17.PeriodCandidateFamily

abbrev CandidateLengthTwoThreeValueRows :=
  SmallRowValueCertificatesW17.CandidateLengthTwoThreeValueRows

abbrev CandidateLengthFourFiveValueRows :=
  SmallRowValueCertificatesW17.CandidateLengthFourFiveValueRows

abbrev CandidateSmallRowValueRows :=
  SmallRowValueCertificatesW17.CandidateSmallRowValueRows

abbrev CandidateLengthTwoThreeRows :=
  SmallRowsTwoThreeW16.CandidateLengthTwoThreeBlockPairGeneratedPointInequalities

abbrev CandidateLengthFourFiveRows :=
  SmallRowsFourFiveW16.CandidateLengthFourFiveBlockPairInequalities

abbrev ExactBlocksTwoThroughFive :=
  SmallComplementConcreteBlocksW17.ExactBlocksTwoThroughFive

abbrev LengthFourFiveExactBlockTargets :=
  LengthFourFiveCaseW11.LengthFourFiveExactBlockTargets

abbrev LengthTwoCandidateNonConnectorLowerTable
    (period : PeriodCandidateFamily) :=
  LengthFourFiveCaseW11.FixedCandidateNonConnectorLowerTable
    period 2 ConcreteValueCertificateExamples.twoPositive

abbrev LengthThreeCandidateNonConnectorLowerTable
    (period : PeriodCandidateFamily) :=
  LengthFourFiveCaseW11.FixedCandidateNonConnectorLowerTable
    period 3 LengthTwoThreeCaseW10.threePositive

def lengthTwoCandidateLowerTableOfMissingInequalities
    (period : PeriodCandidateFamily)
    (H :
      LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities
        period.toRoleHingedPeriodSearchFamily) :
    LengthTwoCandidateNonConnectorLowerTable period where
  table :=
    (LengthTwoThreeCaseW10.lengthTwoMatrixOfMissingInequalities
      period.toRoleHingedPeriodSearchFamily H).toNonConnectorLowerTable

def lengthThreeCandidateLowerTableOfMissingInequalities
    (period : PeriodCandidateFamily)
    (H :
      LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities
        period.toRoleHingedPeriodSearchFamily) :
    LengthThreeCandidateNonConnectorLowerTable period where
  table :=
    (LengthTwoThreeCaseW10.lengthThreeMatrixOfMissingInequalities
      period.toRoleHingedPeriodSearchFamily H).toNonConnectorLowerTable

theorem targetUpperConstructionFiveSixteenAt_lengthTwo_of_missingInequalities
    (period : PeriodCandidateFamily)
    (H :
      LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities
        period.toRoleHingedPeriodSearchFamily) :
    targetUpperConstructionFiveSixteenAt (16 * 2) :=
  (lengthTwoCandidateLowerTableOfMissingInequalities period H)
    |>.targetUpperConstructionFiveSixteenAt_exactBlock

theorem targetUpperConstructionFiveSixteenAt_lengthThree_of_missingInequalities
    (period : PeriodCandidateFamily)
    (H :
      LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities
        period.toRoleHingedPeriodSearchFamily) :
    targetUpperConstructionFiveSixteenAt (16 * 3) :=
  (lengthThreeCandidateLowerTableOfMissingInequalities period H)
    |>.targetUpperConstructionFiveSixteenAt_exactBlock

def lengthFourFiveExactBlockTargetsOfCandidateRows
    {period : PeriodCandidateFamily}
    (smallFourFive : CandidateLengthFourFiveRows period) :
    LengthFourFiveExactBlockTargets :=
  (LengthFourFiveCaseW11.lengthFourFiveCandidateLowerTablesOfMissingInequalities
    period
    (SmallRowsFourFiveW16.candidateLengthFourFiveMissing smallFourFive))
      |>.toExactBlockTargets

def exactBlocksOfCandidateRows
    {period : PeriodCandidateFamily}
    (smallTwoThree : CandidateLengthTwoThreeRows period)
    (smallFourFive : CandidateLengthFourFiveRows period) :
    ExactBlocksTwoThroughFive where
  lengthTwo :=
    targetUpperConstructionFiveSixteenAt_lengthTwo_of_missingInequalities
      period
      (SmallRowsTwoThreeW16.candidateLengthTwoMissingOfBlockPairGeneratedPointInequalities
          smallTwoThree.lengthTwo)
  lengthThree :=
    targetUpperConstructionFiveSixteenAt_lengthThree_of_missingInequalities
      period
      (SmallRowsTwoThreeW16.candidateLengthThreeMissingOfBlockPairGeneratedPointInequalities
          smallTwoThree.lengthThree)
  lengthFourFive :=
    lengthFourFiveExactBlockTargetsOfCandidateRows smallFourFive

def exactBlocksOfCandidateLengthValueRows
    {period : PeriodCandidateFamily}
    (smallTwoThree : CandidateLengthTwoThreeValueRows period)
    (smallFourFive : CandidateLengthFourFiveValueRows period) :
    ExactBlocksTwoThroughFive :=
  exactBlocksOfCandidateRows
    smallTwoThree.toBlockPairGeneratedPointInequalities
    smallFourFive.toBlockPairGeneratedPointInequalities

def exactBlocksOfCandidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    (smallRows : CandidateSmallRowValueRows period) :
    ExactBlocksTwoThroughFive :=
  exactBlocksOfCandidateLengthValueRows
    smallRows.lengthTwoThree smallRows.lengthFourFive

theorem smallComplement_six_of_candidateRows
    {period : PeriodCandidateFamily}
    (smallTwoThree : CandidateLengthTwoThreeRows period)
    (smallFourFive : CandidateLengthFourFiveRows period)
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (oneBlock :
      ExactBlockCertificateW13.ConcreteOneBlockCertificate orientation) :
    SmallComplementConcreteBlocksW17.SmallComplement
      SmallComplementConcreteBlocksW17.blockThresholdSix :=
  (exactBlocksOfCandidateRows smallTwoThree smallFourFive)
    |>.smallComplement_six oneBlock

theorem smallComplement_six_of_candidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    (smallRows : CandidateSmallRowValueRows period)
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (oneBlock :
      ExactBlockCertificateW13.ConcreteOneBlockCertificate orientation) :
    SmallComplementConcreteBlocksW17.SmallComplement
      SmallComplementConcreteBlocksW17.blockThresholdSix :=
  (exactBlocksOfCandidateSmallRowValueRows smallRows)
    |>.smallComplement_six oneBlock

end

end ExactBlocksTwoThroughFiveProducerW18
end PachToth
end ErdosProblems1066
