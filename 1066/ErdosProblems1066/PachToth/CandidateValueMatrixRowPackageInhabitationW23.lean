import ErdosProblems1066.PachToth.ConcreteValueMatrixFamilyInhabitationW22
import ErdosProblems1066.PachToth.PeriodBaseFixingProducerW18
import ErdosProblems1066.PachToth.PeriodCandidateCompatibilityW18

set_option autoImplicit false

/-!
# W23 candidate value-matrix row-package inhabitation

This file isolates the exact candidate-row data behind
`ConcreteValueMatrixFamilyInhabitationW22.CandidateValueMatrixRowPackage` and
records its W18 all-positive value-input bridge.  The row package is equivalent
to choosing one period candidate and the W18/W17/W16 value rows over it; the
present strong role-hinge period-candidate interface is empty, so this route is
blocked before any finite value rows can be consumed.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CandidateValueMatrixRowPackageInhabitationW23

noncomputable section

abbrev PeriodCandidateFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.PeriodCandidateFamily

abbrev CandidateValueMatrixFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.CandidateValueMatrixFamily

abbrev CandidateValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.CandidateValueMatrixRowPackage

abbrev CandidateLengthTwoThreeValueRows
    (F : PeriodCandidateFamily) : Type :=
  SmallRowsTwoThreeValueProducerW18.CandidateLengthTwoThreeValueRows F

abbrev CandidateLengthFourFiveValueRows
    (F : PeriodCandidateFamily) : Type :=
  SmallRowsFourFiveValueProducerW18.CandidateLengthFourFiveValueRows F

abbrev CandidateTailValueRows
    (F : PeriodCandidateFamily) : Type :=
  TailValueRowsProducerW18.CandidateTailValueRows F

abbrev CandidateLengthTwoThreeBlockRows
    (F : PeriodCandidateFamily) : Prop :=
  SmallRowsTwoThreeW16.CandidateLengthTwoThreeBlockPairGeneratedPointInequalities
    F

abbrev CandidateLengthFourFiveBlockRows
    (F : PeriodCandidateFamily) : Prop :=
  SmallRowsFourFiveW16.CandidateLengthFourFiveBlockPairInequalities F

abbrev CandidateTailBlockRows
    (F : PeriodCandidateFamily) : Prop :=
  TailPolynomialRowsW16.CandidateTailBlockPairInequalities F

abbrev PeriodBaseFixingCertificate : Type :=
  AllPositiveInputsProducerW18.PeriodBaseFixingCertificate

abbrev AllPositiveValueInputs : Type :=
  AllPositiveInputsProducerW18.AllPositiveFinalCertificateValueInputs

/-- The exact W18/W17/W16 value-row family needed over one period candidate. -/
structure CandidateValueRowsFor (period : PeriodCandidateFamily) where
  smallTwoThree : CandidateLengthTwoThreeValueRows period
  smallFourFive : CandidateLengthFourFiveValueRows period
  tail : CandidateTailValueRows period

namespace CandidateValueRowsFor

def toRowPackage
    {period : PeriodCandidateFamily}
    (R : CandidateValueRowsFor period) :
    CandidateValueMatrixRowPackage where
  period := period
  smallTwoThree := R.smallTwoThree
  smallFourFive := R.smallFourFive
  tail := R.tail

@[simp]
theorem toRowPackage_period
    {period : PeriodCandidateFamily}
    (R : CandidateValueRowsFor period) :
    R.toRowPackage.period = period :=
  rfl

def toAllPositiveValueInputs
    {period : PeriodCandidateFamily}
    (R : CandidateValueRowsFor period)
    (base : PeriodBaseFixingCertificate)
    (compatibility :
      AllPositiveInputsProducerW18.PeriodCompatibility
        (AllPositiveInputsProducerW18.periodRowsOfBaseFixingCertificate base)
        period) :
    AllPositiveValueInputs :=
  R.toRowPackage.toAllPositiveValueInputs base compatibility

@[simp]
theorem toAllPositiveValueInputs_eq_w18
    {period : PeriodCandidateFamily}
    (R : CandidateValueRowsFor period)
    (base : PeriodBaseFixingCertificate)
    (compatibility :
      AllPositiveInputsProducerW18.PeriodCompatibility
        (AllPositiveInputsProducerW18.periodRowsOfBaseFixingCertificate base)
        period) :
    R.toAllPositiveValueInputs base compatibility =
      AllPositiveInputsProducerW18.valueInputsOfFamilies
        base period compatibility R.smallTwoThree R.smallFourFive R.tail :=
  rfl

def smallTwoThreeBlockRows
    {period : PeriodCandidateFamily}
    (R : CandidateValueRowsFor period) :
    CandidateLengthTwoThreeBlockRows period :=
  R.smallTwoThree.toBlockPairGeneratedPointInequalities

def smallFourFiveBlockRows
    {period : PeriodCandidateFamily}
    (R : CandidateValueRowsFor period) :
    CandidateLengthFourFiveBlockRows period :=
  R.smallFourFive.toBlockPairGeneratedPointInequalities

def tailBlockRows
    {period : PeriodCandidateFamily}
    (R : CandidateValueRowsFor period) :
    CandidateTailBlockRows period :=
  R.tail.toBlockPairInequalities

end CandidateValueRowsFor

def candidateValueRowsForOfRowPackage
    (P : CandidateValueMatrixRowPackage) :
    CandidateValueRowsFor P.period where
  smallTwoThree := P.smallTwoThree
  smallFourFive := P.smallFourFive
  tail := P.tail

@[simp]
theorem candidateValueRowsForOf_toRowPackage
    {period : PeriodCandidateFamily}
    (R : CandidateValueRowsFor period) :
    candidateValueRowsForOfRowPackage R.toRowPackage = R := by
  cases R
  rfl

@[simp]
theorem toRowPackage_candidateValueRowsForOf
    (P : CandidateValueMatrixRowPackage) :
    (candidateValueRowsForOfRowPackage P).toRowPackage = P := by
  cases P
  rfl

theorem nonempty_rowPackage_iff_exists_candidateValueRowsFor :
    Nonempty CandidateValueMatrixRowPackage <->
      Exists fun period : PeriodCandidateFamily =>
        Nonempty (CandidateValueRowsFor period) := by
  constructor
  · intro h
    cases h with
    | intro P =>
        exact
          Exists.intro P.period
            (Nonempty.intro (candidateValueRowsForOfRowPackage P))
  · intro h
    cases h with
    | intro period hrows =>
        cases hrows with
        | intro rows =>
            exact Nonempty.intro rows.toRowPackage

theorem nonempty_candidateValueMatrixFamily_iff_exists_candidateValueRowsFor :
    Nonempty CandidateValueMatrixFamily <->
      Exists fun period : PeriodCandidateFamily =>
        Nonempty (CandidateValueRowsFor period) :=
  Iff.trans
    ConcreteValueMatrixFamilyInhabitationW22.nonempty_candidateValueMatrixFamily_iff_rowPackage
    nonempty_rowPackage_iff_exists_candidateValueRowsFor

/-- A row package plus the W18 base-fixing/compatibility fields needed to
produce all-positive value inputs. -/
structure CandidateValueInputsBridge where
  rows : CandidateValueMatrixRowPackage
  base : PeriodBaseFixingCertificate
  compatibility :
    AllPositiveInputsProducerW18.PeriodCompatibility
      (AllPositiveInputsProducerW18.periodRowsOfBaseFixingCertificate base)
      rows.period

namespace CandidateValueInputsBridge

def toAllPositiveValueInputs
    (B : CandidateValueInputsBridge) :
    AllPositiveValueInputs :=
  B.rows.toAllPositiveValueInputs B.base B.compatibility

@[simp]
theorem toAllPositiveValueInputs_eq_w18
    (B : CandidateValueInputsBridge) :
    B.toAllPositiveValueInputs =
      AllPositiveInputsProducerW18.valueInputsOfFamilies
        B.base B.rows.period B.compatibility
        B.rows.smallTwoThree B.rows.smallFourFive B.rows.tail :=
  rfl

end CandidateValueInputsBridge

def bridgeOfRows
    (P : CandidateValueMatrixRowPackage)
    (base : PeriodBaseFixingCertificate)
    (compatibility :
      AllPositiveInputsProducerW18.PeriodCompatibility
        (AllPositiveInputsProducerW18.periodRowsOfBaseFixingCertificate base)
        P.period) :
    CandidateValueInputsBridge where
  rows := P
  base := base
  compatibility := compatibility

theorem nonempty_bridge_iff_exists_rowPackage_base_compatibility :
    Nonempty CandidateValueInputsBridge <->
      Exists fun P : CandidateValueMatrixRowPackage =>
        Exists fun base : PeriodBaseFixingCertificate =>
          AllPositiveInputsProducerW18.PeriodCompatibility
            (AllPositiveInputsProducerW18.periodRowsOfBaseFixingCertificate
              base)
            P.period := by
  constructor
  · intro h
    cases h with
    | intro B =>
        exact Exists.intro B.rows (Exists.intro B.base B.compatibility)
  · intro h
    cases h with
    | intro P hP =>
        cases hP with
        | intro base compatibility =>
            exact Nonempty.intro (bridgeOfRows P base compatibility)

theorem nonempty_bridge_iff_exists_rowsFor_base_compatibility :
    Nonempty CandidateValueInputsBridge <->
      Exists fun period : PeriodCandidateFamily =>
        Exists fun _rows : CandidateValueRowsFor period =>
          Exists fun base : PeriodBaseFixingCertificate =>
            AllPositiveInputsProducerW18.PeriodCompatibility
              (AllPositiveInputsProducerW18.periodRowsOfBaseFixingCertificate
                base)
              period := by
  constructor
  · intro h
    cases h with
    | intro B =>
        exact
          Exists.intro B.rows.period
            (Exists.intro (candidateValueRowsForOfRowPackage B.rows)
              (Exists.intro B.base B.compatibility))
  · intro h
    cases h with
    | intro period hperiod =>
        cases hperiod with
        | intro rows hrows =>
            cases hrows with
            | intro base compatibility =>
                exact
                  Nonempty.intro
                    (bridgeOfRows rows.toRowPackage base compatibility)

theorem nonempty_allPositiveValueInputs_of_bridge
    (h : Nonempty CandidateValueInputsBridge) :
    Nonempty AllPositiveValueInputs := by
  cases h with
  | intro B =>
      exact Nonempty.intro B.toAllPositiveValueInputs

theorem false_of_periodCandidateFamily
    (period : PeriodCandidateFamily) :
    False :=
  RoleHingeTransitionSearch.false_of_roleHingeTransitionFacts
    period.transitions.same

theorem not_nonempty_periodCandidateFamily :
    Not (Nonempty PeriodCandidateFamily) := by
  intro h
  cases h with
  | intro period =>
      exact false_of_periodCandidateFamily period

theorem not_exists_candidateValueRowsFor :
    Not
      (Exists fun period : PeriodCandidateFamily =>
        Nonempty (CandidateValueRowsFor period)) := by
  intro h
  cases h with
  | intro period _hrows =>
      exact false_of_periodCandidateFamily period

theorem not_nonempty_candidateValueMatrixRowPackage :
    Not (Nonempty CandidateValueMatrixRowPackage) := by
  intro h
  exact
    not_exists_candidateValueRowsFor
      (nonempty_rowPackage_iff_exists_candidateValueRowsFor.1 h)

theorem not_nonempty_candidateValueMatrixFamily :
    Not (Nonempty CandidateValueMatrixFamily) := by
  intro h
  exact
    not_nonempty_candidateValueMatrixRowPackage
      (ConcreteValueMatrixFamilyInhabitationW22.nonempty_candidateValueMatrixFamily_iff_rowPackage.1
        h)

theorem not_nonempty_bridge :
    Not (Nonempty CandidateValueInputsBridge) := by
  intro h
  cases h with
  | intro B =>
      exact false_of_periodCandidateFamily B.rows.period

theorem false_of_allPositiveValueInputs
    (I : AllPositiveValueInputs) :
    False :=
  false_of_periodCandidateFamily I.periodCandidate

theorem not_nonempty_allPositiveValueInputs :
    Not (Nonempty AllPositiveValueInputs) := by
  intro h
  cases h with
  | intro I =>
      exact false_of_allPositiveValueInputs I

theorem not_nonempty_bridge_of_baseFixing_no_go :
    Not (Nonempty CandidateValueInputsBridge) := by
  intro h
  cases h with
  | intro B =>
      exact
        PeriodBaseFixingProducerW18.not_nonempty_certificate
          (Nonempty.intro B.base)

end

end CandidateValueMatrixRowPackageInhabitationW23
end PachToth
end ErdosProblems1066
