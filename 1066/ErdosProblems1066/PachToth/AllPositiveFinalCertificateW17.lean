import ErdosProblems1066.PachToth.PeriodBaseFixingCertificateW16
import ErdosProblems1066.PachToth.SmallRowsTwoThreeW16
import ErdosProblems1066.PachToth.SmallRowsFourFiveW16
import ErdosProblems1066.PachToth.TailPolynomialRowsW16
import ErdosProblems1066.PachToth.AllPositiveCertificateAssemblyW15

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace AllPositiveFinalCertificateW17

noncomputable section

abbrev AllPositiveCertificateRows :=
  AllPositiveCertificateAssemblyW15.AllPositiveCertificateRows

abbrev ExplicitAllPositiveCertificate :=
  AllPositiveCertificateAssemblyW15.ExplicitAllPositiveCertificate

abbrev AllPositiveNonConnectorFields :=
  AllPositiveCertificateAssemblyW15.W12.AllPositiveNonConnectorFields

abbrev ExactTarget : Prop :=
  AllPositiveCertificateAssemblyW15.W12.ExactTarget

abbrev ArbitraryTarget : Prop :=
  AllPositiveCertificateAssemblyW15.W12.ArbitraryTarget

abbrev ExactBlockTarget (k : Nat) : Prop :=
  AllPositiveCertificateAssemblyW15.W12.ExactBlockTarget k

abbrev PeriodBaseFixingCertificate :=
  PeriodBaseFixingCertificateW16.PeriodBaseFixingCertificate

abbrev PeriodRows :=
  AllPositiveCertificateAssemblyW15.PeriodRows

abbrev PeriodCandidateFamily :=
  AllPositiveCertificateAssemblyW15.PeriodCandidateFamily

abbrev RemainingRowFamily :=
  AllPositiveCertificateAssemblyW15.RemainingRowFamily

abbrev SmallLengthRowsWithTail :=
  AllPositiveCertificateAssemblyW15.SmallLengthRowsWithTail

abbrev ExactMissingConcreteTableFields :=
  AllPositiveCertificateAssemblyW15.ExactMissingConcreteTableFields

abbrev CandidateLengthTwoThreeRows :=
  SmallRowsTwoThreeW16.CandidateLengthTwoThreeBlockPairGeneratedPointInequalities

abbrev CandidateLengthFourFiveRows :=
  SmallRowsFourFiveW16.CandidateLengthFourFiveBlockPairInequalities

abbrev CandidateTailRows :=
  TailPolynomialRowsW16.CandidateTailBlockPairInequalities

abbrev TailValueRows (F : PeriodCandidateFamily) :=
  TailPolynomialRowsW16.TailValueRows F.toRoleHingedPeriodSearchFamily

def periodRowsOfBaseFixingCertificate
    (C : PeriodBaseFixingCertificate) :
    PeriodRows :=
  C.toConcretePeriodEquationFields

abbrev PeriodCompatibility (P : PeriodRows) (F : PeriodCandidateFamily) :
    Prop :=
  AllPositiveFiniteFieldsW14.periodFieldsOfCandidateFamily F =
    P.toW12PeriodEquationFields

def lengthTwoRowsOfW16SmallRows
    {F : PeriodCandidateFamily}
    (smallTwoThree : CandidateLengthTwoThreeRows F) :
    LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  SmallRowsTwoThreeW16.candidateLengthTwoMissingOfBlockPairGeneratedPointInequalities
    smallTwoThree.lengthTwo

def lengthThreeRowsOfW16SmallRows
    {F : PeriodCandidateFamily}
    (smallTwoThree : CandidateLengthTwoThreeRows F) :
    LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  SmallRowsTwoThreeW16.candidateLengthThreeMissingOfBlockPairGeneratedPointInequalities
    smallTwoThree.lengthThree

def lengthFourRowsOfW16SmallRows
    {F : PeriodCandidateFamily}
    (smallFourFive : CandidateLengthFourFiveRows F) :
    LengthFourFiveCaseW11.LengthFourMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  SmallRowsFourFiveW16.candidateLengthFourMissing smallFourFive.lengthFour

def lengthFiveRowsOfW16SmallRows
    {F : PeriodCandidateFamily}
    (smallFourFive : CandidateLengthFourFiveRows F) :
    LengthFourFiveCaseW11.LengthFiveMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  SmallRowsFourFiveW16.candidateLengthFiveMissing smallFourFive.lengthFive

def tailRowsOfTailValueRows
    {F : PeriodCandidateFamily}
    (tail : TailValueRows F) :
    CandidateTailRows F :=
  tail.toBlockPairInequalities

def smallLengthRowsWithTailOfW16Rows
    {F : PeriodCandidateFamily}
    (smallTwoThree : CandidateLengthTwoThreeRows F)
    (smallFourFive : CandidateLengthFourFiveRows F)
    (tail : CandidateTailRows F) :
    SmallLengthRowsWithTail F :=
  TailPolynomialLowerProofW15.smallLengthRowsWithTailOfBlockPairInequalities
    (lengthTwoRowsOfW16SmallRows smallTwoThree)
    (lengthThreeRowsOfW16SmallRows smallTwoThree)
    (lengthFourRowsOfW16SmallRows smallFourFive)
    (lengthFiveRowsOfW16SmallRows smallFourFive)
    tail

def exactMissingFieldsOfW16Rows
    {F : PeriodCandidateFamily}
    (smallTwoThree : CandidateLengthTwoThreeRows F)
    (smallFourFive : CandidateLengthFourFiveRows F)
    (tail : CandidateTailRows F) :
    ExactMissingConcreteTableFields F :=
  SmallRowsFourFiveW16.exactMissingFieldsOfSmallRowsFourFiveAndTail
    (lengthTwoRowsOfW16SmallRows smallTwoThree)
    (lengthThreeRowsOfW16SmallRows smallTwoThree)
    smallFourFive tail

def exactMissingFieldsOfW16RowsAndTailValues
    {F : PeriodCandidateFamily}
    (smallTwoThree : CandidateLengthTwoThreeRows F)
    (smallFourFive : CandidateLengthFourFiveRows F)
    (tail : TailValueRows F) :
    ExactMissingConcreteTableFields F :=
  exactMissingFieldsOfW16Rows
    smallTwoThree smallFourFive (tailRowsOfTailValueRows tail)

def remainingRowFamilyOfExactMissingFields
    {P : PeriodRows} {F : PeriodCandidateFamily}
    (hcompat : PeriodCompatibility P F)
    (D : ExactMissingConcreteTableFields F) :
    RemainingRowFamily P.toW12PeriodEquationFields := by
  rw [Eq.symm hcompat]
  exact (AllPositivePolynomialLowerTableW14.rowFamilyOfFields D).rows

def rowsOfBaseFixingAndExactMissingFields
    (base : PeriodBaseFixingCertificate)
    (F : PeriodCandidateFamily)
    (hcompat : PeriodCompatibility (periodRowsOfBaseFixingCertificate base) F)
    (fields : ExactMissingConcreteTableFields F) :
    AllPositiveCertificateRows where
  periodRows := periodRowsOfBaseFixingCertificate base
  polynomialRows := remainingRowFamilyOfExactMissingFields hcompat fields

def rowsOfBaseFixingAndW16Rows
    (base : PeriodBaseFixingCertificate)
    (F : PeriodCandidateFamily)
    (hcompat : PeriodCompatibility (periodRowsOfBaseFixingCertificate base) F)
    (smallTwoThree : CandidateLengthTwoThreeRows F)
    (smallFourFive : CandidateLengthFourFiveRows F)
    (tail : CandidateTailRows F) :
    AllPositiveCertificateRows :=
  rowsOfBaseFixingAndExactMissingFields base F hcompat
    (exactMissingFieldsOfW16Rows smallTwoThree smallFourFive tail)

def rowsOfBaseFixingAndW16RowsAndTailValues
    (base : PeriodBaseFixingCertificate)
    (F : PeriodCandidateFamily)
    (hcompat : PeriodCompatibility (periodRowsOfBaseFixingCertificate base) F)
    (smallTwoThree : CandidateLengthTwoThreeRows F)
    (smallFourFive : CandidateLengthFourFiveRows F)
    (tail : TailValueRows F) :
    AllPositiveCertificateRows :=
  rowsOfBaseFixingAndW16Rows base F hcompat
    smallTwoThree smallFourFive (tailRowsOfTailValueRows tail)

def fieldsOfBaseFixingAndW16Rows
    (base : PeriodBaseFixingCertificate)
    (F : PeriodCandidateFamily)
    (hcompat : PeriodCompatibility (periodRowsOfBaseFixingCertificate base) F)
    (smallTwoThree : CandidateLengthTwoThreeRows F)
    (smallFourFive : CandidateLengthFourFiveRows F)
    (tail : CandidateTailRows F) :
    AllPositiveNonConnectorFields :=
  (rowsOfBaseFixingAndW16Rows base F hcompat
    smallTwoThree smallFourFive tail).fields

def explicitCertificateOfBaseFixingAndW16Rows
    (base : PeriodBaseFixingCertificate)
    (F : PeriodCandidateFamily)
    (hcompat : PeriodCompatibility (periodRowsOfBaseFixingCertificate base) F)
    (smallTwoThree : CandidateLengthTwoThreeRows F)
    (smallFourFive : CandidateLengthFourFiveRows F)
    (tail : CandidateTailRows F) :
    ExplicitAllPositiveCertificate :=
  (rowsOfBaseFixingAndW16Rows base F hcompat
    smallTwoThree smallFourFive tail).explicitCertificate

structure AllPositiveFinalCertificateInputs where
  base : PeriodBaseFixingCertificate
  periodCandidate : PeriodCandidateFamily
  compatibility :
    PeriodCompatibility
      (periodRowsOfBaseFixingCertificate base)
      periodCandidate
  smallTwoThree : CandidateLengthTwoThreeRows periodCandidate
  smallFourFive : CandidateLengthFourFiveRows periodCandidate
  tail : CandidateTailRows periodCandidate

namespace AllPositiveFinalCertificateInputs

def smallLengthRowsWithTail
    (I : AllPositiveFinalCertificateInputs) :
    SmallLengthRowsWithTail I.periodCandidate :=
  smallLengthRowsWithTailOfW16Rows I.smallTwoThree I.smallFourFive I.tail

def exactMissingFields
    (I : AllPositiveFinalCertificateInputs) :
    ExactMissingConcreteTableFields I.periodCandidate :=
  exactMissingFieldsOfW16Rows I.smallTwoThree I.smallFourFive I.tail

def rows
    (I : AllPositiveFinalCertificateInputs) :
    AllPositiveCertificateRows :=
  rowsOfBaseFixingAndExactMissingFields
    I.base I.periodCandidate I.compatibility I.exactMissingFields

def fields
    (I : AllPositiveFinalCertificateInputs) :
    AllPositiveNonConnectorFields :=
  I.rows.fields

def explicitCertificate
    (I : AllPositiveFinalCertificateInputs) :
    ExplicitAllPositiveCertificate :=
  I.rows.explicitCertificate

theorem targetUpperConstructionFiveSixteenAt
    (I : AllPositiveFinalCertificateInputs)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  I.rows.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem targetUpperConstructionFiveSixteen
    (I : AllPositiveFinalCertificateInputs) :
    ExactTarget :=
  I.rows.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (I : AllPositiveFinalCertificateInputs) :
    ArbitraryTarget :=
  I.rows.targetUpperConstructionFiveSixteenArbitrary

end AllPositiveFinalCertificateInputs

structure AllPositiveFinalCertificateValueInputs where
  base : PeriodBaseFixingCertificate
  periodCandidate : PeriodCandidateFamily
  compatibility :
    PeriodCompatibility
      (periodRowsOfBaseFixingCertificate base)
      periodCandidate
  smallTwoThree : CandidateLengthTwoThreeRows periodCandidate
  smallFourFive : CandidateLengthFourFiveRows periodCandidate
  tail : TailValueRows periodCandidate

namespace AllPositiveFinalCertificateValueInputs

def toInputs
    (I : AllPositiveFinalCertificateValueInputs) :
    AllPositiveFinalCertificateInputs where
  base := I.base
  periodCandidate := I.periodCandidate
  compatibility := I.compatibility
  smallTwoThree := I.smallTwoThree
  smallFourFive := I.smallFourFive
  tail := tailRowsOfTailValueRows I.tail

def rows
    (I : AllPositiveFinalCertificateValueInputs) :
    AllPositiveCertificateRows :=
  I.toInputs.rows

def fields
    (I : AllPositiveFinalCertificateValueInputs) :
    AllPositiveNonConnectorFields :=
  I.toInputs.fields

def explicitCertificate
    (I : AllPositiveFinalCertificateValueInputs) :
    ExplicitAllPositiveCertificate :=
  I.toInputs.explicitCertificate

theorem targetUpperConstructionFiveSixteenAt
    (I : AllPositiveFinalCertificateValueInputs)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  I.toInputs.targetUpperConstructionFiveSixteenAt k hk

theorem targetUpperConstructionFiveSixteen
    (I : AllPositiveFinalCertificateValueInputs) :
    ExactTarget :=
  I.toInputs.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (I : AllPositiveFinalCertificateValueInputs) :
    ArbitraryTarget :=
  I.toInputs.targetUpperConstructionFiveSixteenArbitrary

end AllPositiveFinalCertificateValueInputs

end

end AllPositiveFinalCertificateW17
end PachToth
end ErdosProblems1066
