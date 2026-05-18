import ErdosProblems1066.PachToth.PeriodEquationSourceFieldsW22
import ErdosProblems1066.PachToth.PeriodBaseFixingCertificateW16
import ErdosProblems1066.PachToth.PeriodBaseFixingSameW16

set_option autoImplicit false

/-!
# W23 period base-fixing source inhabitation

This file sharpens the W22 period-equation source-field gate by routing the
inhabited direction through the W16 base-fixing certificate assembly.  It also
records the exact negated form: missing source fields are precisely missing
same/opposite exact-base fixing rows.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodBaseFixingSourceInhabitationW23

open FiniteGraph

noncomputable section

abbrev RoleHingeTransitions :=
  PeriodEquationSourceFieldsW22.RoleHingeTransitions

abbrev RoleHingeSourceFields :=
  PeriodEquationSourceFieldsW22.RoleHingeSourceFields

abbrev BaseFixingAlternative :=
  PeriodEquationSourceFieldsW22.BaseFixingAlternative

abbrev MissingBaseFixingRows :=
  PeriodEquationSourceFieldsW22.MissingBaseFixingRows

def sourceFieldsOfBaseFixingAlternative
    (T : RoleHingeTransitions)
    (H : BaseFixingAlternative T) :
    RoleHingeSourceFields T := by
  let P :=
    PeriodBaseFixingCertificateW16.concretePeriodEquationFieldsOfBaseFixingAlternative
      T H
  have hP : P.transitions = T :=
    PeriodBaseFixingCertificateW16.concretePeriodEquationFieldsOfBaseFixingAlternative_transitions
      T H
  exact hP ▸ PeriodEquationSourceFieldsW22.sourceFieldsOfPeriodRows P

theorem sourceFields_of_baseFixingAlternative_via_certificate
    (T : RoleHingeTransitions)
    (H : BaseFixingAlternative T) :
    Nonempty (RoleHingeSourceFields T) :=
  Nonempty.intro (sourceFieldsOfBaseFixingAlternative T H)

theorem baseFixingAlternative_of_sourceFields_via_rows
    (T : RoleHingeTransitions)
    (S : RoleHingeSourceFields T) :
    BaseFixingAlternative T := by
  simpa using
    PeriodBaseFixingCertificateW16.baseFixingAlternative_of_concretePeriodEquationFields
      (PeriodEquationSourceFieldsW22.periodRowsOfSourceFields T S)

theorem sourceFields_iff_baseFixingAlternative_via_certificate
    (T : RoleHingeTransitions) :
    Nonempty (RoleHingeSourceFields T) <-> BaseFixingAlternative T := by
  constructor
  · intro hS
    cases hS with
    | intro S =>
        exact baseFixingAlternative_of_sourceFields_via_rows T S
  · intro H
    exact sourceFields_of_baseFixingAlternative_via_certificate T H

theorem not_sourceFields_iff_not_baseFixingAlternative
    (T : RoleHingeTransitions) :
    (RoleHingeSourceFields T -> False) <->
      Not (BaseFixingAlternative T) := by
  constructor
  · intro hS H
    exact hS (sourceFieldsOfBaseFixingAlternative T H)
  · intro hno S
    exact hno (baseFixingAlternative_of_sourceFields_via_rows T S)

theorem missingBaseFixingRows_iff_not_baseFixingAlternative
    (T : RoleHingeTransitions) :
    MissingBaseFixingRows T <-> Not (BaseFixingAlternative T) := by
  constructor
  · intro M
    exact M.no_baseFixingAlternative
  · intro hno
    constructor
    · intro hsame
      exact hno (Or.inl hsame)
    · intro hopposite
      exact hno (Or.inr hopposite)

theorem not_sourceFields_iff_missingBaseFixingRows_sharp
    (T : RoleHingeTransitions) :
    (RoleHingeSourceFields T -> False) <-> MissingBaseFixingRows T :=
  (not_sourceFields_iff_not_baseFixingAlternative T).trans
    (missingBaseFixingRows_iff_not_baseFixingAlternative T).symm

theorem not_nonempty_sourceFields_iff_missingBaseFixingRows_sharp
    (T : RoleHingeTransitions) :
    Not (Nonempty (RoleHingeSourceFields T)) <->
      MissingBaseFixingRows T := by
  constructor
  · intro hS
    exact (not_sourceFields_iff_missingBaseFixingRows_sharp T).1
      (fun S => hS (Nonempty.intro S))
  · intro M hS
    cases hS with
    | intro S =>
        exact
          (not_sourceFields_iff_missingBaseFixingRows_sharp T).2 M S

theorem missingBaseFixingRows_of_roleHingeTransitions
    (T : RoleHingeTransitions) :
    MissingBaseFixingRows T := by
  constructor
  · intro _hsame
    exact PeriodBaseFixingSameW16.false_of_roleHingeTransitions_same T
  · intro _hopposite
    exact PeriodBaseFixingSameW16.false_of_roleHingeTransitions_same T

theorem not_baseFixingAlternative_of_roleHingeTransitions
    (T : RoleHingeTransitions) :
    Not (BaseFixingAlternative T) :=
  (missingBaseFixingRows_iff_not_baseFixingAlternative T).1
    (missingBaseFixingRows_of_roleHingeTransitions T)

theorem not_sourceFields_of_roleHingeTransitions
    (T : RoleHingeTransitions) :
    RoleHingeSourceFields T -> False :=
  (not_sourceFields_iff_missingBaseFixingRows_sharp T).2
    (missingBaseFixingRows_of_roleHingeTransitions T)

end

end PeriodBaseFixingSourceInhabitationW23
end PachToth
end ErdosProblems1066
