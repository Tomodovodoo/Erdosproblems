import ErdosProblems1066.PachToth.PeriodBaseFixingSameW16
import ErdosProblems1066.PachToth.PeriodBaseFixingOppositeW16

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace BaseFixingRowsViableW17

noncomputable section

abbrev RoleHingeTransitions :=
  PeriodBaseFixingSameW16.RoleHingeTransitions

abbrev PeriodRows :=
  PeriodBaseFixingSameW16.PeriodRows

abbrev SameFixesExactBase (T : RoleHingeTransitions) : Prop :=
  PeriodBaseFixingSameW16.SameFixesExactBase T

abbrev OppositeFixesExactBase (T : RoleHingeTransitions) : Prop :=
  PeriodBaseFixingOppositeW16.OppositeFixesExactBase T

abbrev BaseFixingAlternative (T : RoleHingeTransitions) : Prop :=
  PeriodRowsAllPositiveProofW15.BaseFixingAlternative T

structure ViableTransitionFields where
  transitions : RoleHingeTransitions

namespace ViableTransitionFields

abbrev baseFixingAlternative (V : ViableTransitionFields) : Prop :=
  BaseFixingAlternative V.transitions

end ViableTransitionFields

structure SameBaseFixingRows (V : ViableTransitionFields) where
  fixesExactBase : SameFixesExactBase V.transitions
  rows : PeriodRows
  rows_transitions : rows.transitions = V.transitions
  rows_word :
    forall (k : Nat) (hk : 0 < k),
      rows.word k hk = PeriodCertificateExamples.allPositiveSameWord k hk

namespace SameBaseFixingRows

def ofFix
    (V : ViableTransitionFields)
    (hfix : SameFixesExactBase V.transitions) :
    SameBaseFixingRows V where
  fixesExactBase := hfix
  rows := PeriodBaseFixingSameW16.sameRows V.transitions hfix
  rows_transitions :=
    PeriodBaseFixingSameW16.sameRows_transitions V.transitions hfix
  rows_word :=
    PeriodBaseFixingSameW16.sameRows_word V.transitions hfix

@[simp]
theorem ofFix_rows
    (V : ViableTransitionFields)
    (hfix : SameFixesExactBase V.transitions) :
    (ofFix V hfix).rows =
      PeriodBaseFixingSameW16.sameRows V.transitions hfix :=
  rfl

@[simp]
theorem ofFix_fixesExactBase
    (V : ViableTransitionFields)
    (hfix : SameFixesExactBase V.transitions) :
    (ofFix V hfix).fixesExactBase = hfix :=
  rfl

theorem exists_periodRows
    {V : ViableTransitionFields}
    (S : SameBaseFixingRows V) :
    exists P : PeriodRows, P.transitions = V.transitions :=
  Exists.intro S.rows S.rows_transitions

theorem baseFixingAlternative
    {V : ViableTransitionFields}
    (S : SameBaseFixingRows V) :
    BaseFixingAlternative V.transitions :=
  Or.inl S.fixesExactBase

end SameBaseFixingRows

def sameBaseFixingRows
    (V : ViableTransitionFields)
    (hfix : SameFixesExactBase V.transitions) :
    SameBaseFixingRows V :=
  SameBaseFixingRows.ofFix V hfix

@[simp]
theorem sameBaseFixingRows_rows
    (V : ViableTransitionFields)
    (hfix : SameFixesExactBase V.transitions) :
    (sameBaseFixingRows V hfix).rows =
      PeriodBaseFixingSameW16.sameRows V.transitions hfix :=
  rfl

structure OppositeBaseFixingRows (V : ViableTransitionFields) where
  fixesExactBase : OppositeFixesExactBase V.transitions
  rows : PeriodRows
  rows_transitions : rows.transitions = V.transitions
  one_word :
    rows.word 1 PeriodCertificateExamples.onePositiveLength =
      PeriodCertificateExamples.allPositiveOppositeWord
        1 PeriodCertificateExamples.onePositiveLength

namespace OppositeBaseFixingRows

def rowsOfFix
    (V : ViableTransitionFields)
    (hfix : OppositeFixesExactBase V.transitions) :
    PeriodRows :=
  Classical.choose
    ((PeriodBaseFixingOppositeW16.oppositeRows_exist_iff_oppositeFixesExactBase
      V.transitions).2 hfix)

theorem rowsOfFix_spec
    (V : ViableTransitionFields)
    (hfix : OppositeFixesExactBase V.transitions) :
    (rowsOfFix V hfix).transitions = V.transitions /\
      (rowsOfFix V hfix).word 1
          PeriodCertificateExamples.onePositiveLength =
        PeriodCertificateExamples.allPositiveOppositeWord
          1 PeriodCertificateExamples.onePositiveLength :=
  Classical.choose_spec
    ((PeriodBaseFixingOppositeW16.oppositeRows_exist_iff_oppositeFixesExactBase
      V.transitions).2 hfix)

def ofFix
    (V : ViableTransitionFields)
    (hfix : OppositeFixesExactBase V.transitions) :
    OppositeBaseFixingRows V where
  fixesExactBase := hfix
  rows := rowsOfFix V hfix
  rows_transitions := (rowsOfFix_spec V hfix).1
  one_word := (rowsOfFix_spec V hfix).2

@[simp]
theorem ofFix_rows
    (V : ViableTransitionFields)
    (hfix : OppositeFixesExactBase V.transitions) :
    (ofFix V hfix).rows = rowsOfFix V hfix :=
  rfl

@[simp]
theorem ofFix_fixesExactBase
    (V : ViableTransitionFields)
    (hfix : OppositeFixesExactBase V.transitions) :
    (ofFix V hfix).fixesExactBase = hfix :=
  rfl

theorem exists_periodRows
    {V : ViableTransitionFields}
    (O : OppositeBaseFixingRows V) :
    exists P : PeriodRows, P.transitions = V.transitions :=
  Exists.intro O.rows O.rows_transitions

theorem baseFixingAlternative
    {V : ViableTransitionFields}
    (O : OppositeBaseFixingRows V) :
    BaseFixingAlternative V.transitions :=
  Or.inr O.fixesExactBase

end OppositeBaseFixingRows

def oppositeBaseFixingRows
    (V : ViableTransitionFields)
    (hfix : OppositeFixesExactBase V.transitions) :
    OppositeBaseFixingRows V :=
  OppositeBaseFixingRows.ofFix V hfix

@[simp]
theorem oppositeBaseFixingRows_rows
    (V : ViableTransitionFields)
    (hfix : OppositeFixesExactBase V.transitions) :
    (oppositeBaseFixingRows V hfix).rows =
      OppositeBaseFixingRows.rowsOfFix V hfix :=
  rfl

structure BaseFixingRows (V : ViableTransitionFields) where
  rows : PeriodRows
  rows_transitions : rows.transitions = V.transitions
  baseFixing : BaseFixingAlternative V.transitions

namespace BaseFixingRows

def ofSame
    {V : ViableTransitionFields}
    (S : SameBaseFixingRows V) :
    BaseFixingRows V where
  rows := S.rows
  rows_transitions := S.rows_transitions
  baseFixing := S.baseFixingAlternative

def ofOpposite
    {V : ViableTransitionFields}
    (O : OppositeBaseFixingRows V) :
    BaseFixingRows V where
  rows := O.rows
  rows_transitions := O.rows_transitions
  baseFixing := O.baseFixingAlternative

theorem exists_periodRows
    {V : ViableTransitionFields}
    (B : BaseFixingRows V) :
    exists P : PeriodRows, P.transitions = V.transitions :=
  Exists.intro B.rows B.rows_transitions

end BaseFixingRows

def baseFixingRowsOfSame
    (V : ViableTransitionFields)
    (hfix : SameFixesExactBase V.transitions) :
    BaseFixingRows V :=
  BaseFixingRows.ofSame (sameBaseFixingRows V hfix)

def baseFixingRowsOfOpposite
    (V : ViableTransitionFields)
    (hfix : OppositeFixesExactBase V.transitions) :
    BaseFixingRows V :=
  BaseFixingRows.ofOpposite (oppositeBaseFixingRows V hfix)

theorem exists_periodRows_of_sameFixesExactBase
    (V : ViableTransitionFields)
    (hfix : SameFixesExactBase V.transitions) :
    exists P : PeriodRows, P.transitions = V.transitions :=
  (sameBaseFixingRows V hfix).exists_periodRows

theorem exists_periodRows_of_oppositeFixesExactBase
    (V : ViableTransitionFields)
    (hfix : OppositeFixesExactBase V.transitions) :
    exists P : PeriodRows, P.transitions = V.transitions :=
  (oppositeBaseFixingRows V hfix).exists_periodRows

theorem exists_periodRows_iff_baseFixingAlternative
    (V : ViableTransitionFields) :
    (exists P : PeriodRows, P.transitions = V.transitions) <->
      V.baseFixingAlternative :=
  PeriodRowsAllPositiveProofW15.rows_exist_iff_baseFixingAlternative
    V.transitions

end

end BaseFixingRowsViableW17
end PachToth
end ErdosProblems1066
