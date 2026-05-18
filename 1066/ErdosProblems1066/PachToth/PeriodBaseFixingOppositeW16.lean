import ErdosProblems1066.PachToth.PeriodRowsAllPositiveProofW15
import ErdosProblems1066.PachToth.PeriodEquationConcreteW14
import ErdosProblems1066.PachToth.PeriodCertificateExamples
import ErdosProblems1066.PachToth.PeriodWordCertificates
import ErdosProblems1066.PachToth.BaseTransitionRealization

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace PeriodBaseFixingOppositeW16

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev RoleHingeTransitions :=
  PeriodRowsAllPositiveProofW15.RoleHingeTransitions

abbrev OppositeFixesExactBase (T : RoleHingeTransitions) : Prop :=
  PeriodRowsAllPositiveProofW15.OppositeFixesExactBase T

abbrev OppositeOneWord : OrientationWord.Word 1 :=
  PeriodCertificateExamples.allPositiveOppositeWord
    1 PeriodCertificateExamples.onePositiveLength

abbrev OppositeOneFiniteWord :
    PeriodSearchInterface.FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord
    PeriodCertificateExamples.onePositiveLength OppositeOneWord

abbrev OppositeOneRow (T : RoleHingeTransitions) (i : Fin 16) : Prop :=
  PeriodSearchInterface.AlgebraicVertexPeriodEquation
    T.toFigure2TransitionObligations
    BaseTransitionRealization.exactBase
    OppositeOneFiniteWord
    (BlockPartition.localVertexEquivFin16.symm i)

abbrev OppositeOneRows (T : RoleHingeTransitions) : Prop :=
  forall i : Fin 16, OppositeOneRow T i

theorem oppositeOneFiniteWord_eq_examples :
    OppositeOneFiniteWord =
      PeriodCertificateExamples.finiteOrientationWordOfWord
        PeriodCertificateExamples.onePositiveLength OppositeOneWord := by
  rfl

theorem oppositeFixesExactBase_iff_placeNext
    (T : RoleHingeTransitions) :
    OppositeFixesExactBase T <->
      T.opposite.placeNext BaseTransitionRealization.exactBase =
        BaseTransitionRealization.exactBase := by
  rfl

theorem oppositeOneRows_of_oppositeFixesExactBase
    {T : RoleHingeTransitions}
    (hfix : OppositeFixesExactBase T) :
    OppositeOneRows T := by
  intro i
  simpa [OppositeOneRow, OppositeOneFiniteWord, OppositeOneWord,
    PeriodWordCertificates.finiteOrientationWordOfWord,
    PeriodCertificateExamples.finiteOrientationWordOfWord] using
      PeriodCertificateExamples.allPositiveOppositeEquations
        T.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        hfix 1 PeriodCertificateExamples.onePositiveLength i

theorem oppositeFixesExactBase_of_oppositeOneRows
    {T : RoleHingeTransitions}
    (hrows : OppositeOneRows T) :
    OppositeFixesExactBase T := by
  have hfix :=
    PeriodCertificateExamples.oneLetterEquations_force_transitionFixesBase
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      OppositeOneWord
      (by
        intro i
        simpa [OppositeOneRow, OppositeOneFiniteWord, OppositeOneWord,
          PeriodWordCertificates.finiteOrientationWordOfWord,
          PeriodCertificateExamples.finiteOrientationWordOfWord] using
            hrows i)
  simpa [OppositeOneWord] using hfix

theorem oppositeFixesExactBase_iff_oppositeOneRows
    (T : RoleHingeTransitions) :
    OppositeFixesExactBase T <-> OppositeOneRows T := by
  constructor
  · exact oppositeOneRows_of_oppositeFixesExactBase
  · exact oppositeFixesExactBase_of_oppositeOneRows

theorem no_oppositeFixesExactBase_of_missing_oppositeOneRow
    {T : RoleHingeTransitions}
    (hmiss : exists i : Fin 16, Not (OppositeOneRow T i)) :
    Not (OppositeFixesExactBase T) := by
  intro hfix
  cases hmiss with
  | intro i hi =>
      exact hi (oppositeOneRows_of_oppositeFixesExactBase hfix i)

theorem missing_oppositeOneRow_of_no_oppositeFixesExactBase
    {T : RoleHingeTransitions}
    (hno : Not (OppositeFixesExactBase T)) :
    exists i : Fin 16, Not (OppositeOneRow T i) := by
  classical
  by_contra hnone
  apply hno
  apply oppositeFixesExactBase_of_oppositeOneRows
  intro i
  by_contra hi
  exact hnone (Exists.intro i hi)

theorem no_oppositeFixesExactBase_iff_missing_oppositeOneRow
    (T : RoleHingeTransitions) :
    Not (OppositeFixesExactBase T) <->
      exists i : Fin 16, Not (OppositeOneRow T i) := by
  constructor
  · exact missing_oppositeOneRow_of_no_oppositeFixesExactBase
  · exact no_oppositeFixesExactBase_of_missing_oppositeOneRow

theorem oppositeRows_exist_iff_oppositeFixesExactBase
    (T : RoleHingeTransitions) :
    (exists P : PeriodRowsAllPositiveProofW15.PeriodRows,
        P.transitions = T /\
          P.word 1 PeriodCertificateExamples.onePositiveLength =
            PeriodCertificateExamples.allPositiveOppositeWord
              1 PeriodCertificateExamples.onePositiveLength) <->
      OppositeFixesExactBase T := by
  constructor
  · intro h
    cases h with
    | intro P hP =>
        cases hP with
        | intro hT hword =>
            subst T
            apply oppositeFixesExactBase_of_oppositeOneRows
            intro i
            have hrow :=
              P.equation 1 PeriodCertificateExamples.onePositiveLength i
            simpa [OppositeOneRow, OppositeOneFiniteWord, OppositeOneWord,
              PeriodEquationConcreteW14.AlgebraicEquationRow, hword,
              PeriodWordCertificates.finiteOrientationWordOfWord,
              PeriodCertificateExamples.finiteOrientationWordOfWord] using hrow
  · intro hfix
    exact
      Exists.intro (PeriodRowsAllPositiveProofW15.oppositeRows T hfix)
        (And.intro rfl rfl)

end

end PeriodBaseFixingOppositeW16
end PachToth
end ErdosProblems1066
