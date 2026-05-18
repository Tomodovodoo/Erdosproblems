import ErdosProblems1066.PachToth.PeriodRowsAllPositiveProofW15
import ErdosProblems1066.PachToth.TransitionAlternativeW13

set_option autoImplicit false

/-!
# W16 period base-fixing certificate assembly

This file is the adapter from the W15 checked base-fixing alternative to the
W14 concrete all-positive period-equation row fields.  The concrete
connector-only transition obligations are kept separate: W13 proves that they
do not supply the one-step exact-base fixing input required by this route.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodBaseFixingCertificateW16

open FiniteGraph

noncomputable section

abbrev RoleHingeTransitions :=
  PeriodRowsAllPositiveProofW15.RoleHingeTransitions

abbrev PeriodRows :=
  PeriodEquationConcreteW14.ConcretePeriodEquationFields

abbrev BaseFixingAlternative :=
  PeriodRowsAllPositiveProofW15.BaseFixingAlternative

abbrev SameFixesExactBase :=
  PeriodRowsAllPositiveProofW15.SameFixesExactBase

abbrev OppositeFixesExactBase :=
  PeriodRowsAllPositiveProofW15.OppositeFixesExactBase

/-- A transition package together with the precise W15 base-fixing input. -/
structure PeriodBaseFixingCertificate where
  transitions : RoleHingeTransitions
  baseFixing : BaseFixingAlternative transitions

namespace PeriodBaseFixingCertificate

/-- Assemble the supplied base-fixing alternative into W14 concrete rows. -/
def toConcretePeriodEquationFields
    (C : PeriodBaseFixingCertificate) :
    PeriodRows :=
  Classical.choose
    (PeriodRowsAllPositiveProofW15.exists_rows_of_baseFixingAlternative
      C.transitions C.baseFixing)

@[simp]
theorem toConcretePeriodEquationFields_transitions
    (C : PeriodBaseFixingCertificate) :
    C.toConcretePeriodEquationFields.transitions = C.transitions :=
  Classical.choose_spec
    (PeriodRowsAllPositiveProofW15.exists_rows_of_baseFixingAlternative
      C.transitions C.baseFixing)

/-- Existential spelling of the assembled W14 row package. -/
theorem exists_concretePeriodEquationFields
    (C : PeriodBaseFixingCertificate) :
    exists P : PeriodRows, P.transitions = C.transitions :=
  ⟨C.toConcretePeriodEquationFields,
    C.toConcretePeriodEquationFields_transitions⟩

end PeriodBaseFixingCertificate

/-- Build a certificate from the same-orientation base-fixing row. -/
def sameCertificate
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T) :
    PeriodBaseFixingCertificate where
  transitions := T
  baseFixing := Or.inl hfix

/-- Build a certificate from the opposite-orientation base-fixing row. -/
def oppositeCertificate
    (T : RoleHingeTransitions)
    (hfix : OppositeFixesExactBase T) :
    PeriodBaseFixingCertificate where
  transitions := T
  baseFixing := Or.inr hfix

/-- Direct adapter from the W15 alternative to the W14 concrete row fields. -/
def concretePeriodEquationFieldsOfBaseFixingAlternative
    (T : RoleHingeTransitions)
    (H : BaseFixingAlternative T) :
    PeriodRows :=
  (PeriodBaseFixingCertificate.mk T H).toConcretePeriodEquationFields

@[simp]
theorem concretePeriodEquationFieldsOfBaseFixingAlternative_transitions
    (T : RoleHingeTransitions)
    (H : BaseFixingAlternative T) :
    (concretePeriodEquationFieldsOfBaseFixingAlternative T H).transitions =
      T :=
  PeriodBaseFixingCertificate.toConcretePeriodEquationFields_transitions
    (PeriodBaseFixingCertificate.mk T H)

/-- Existential adapter matching the W14 field shape exactly. -/
theorem exists_concretePeriodEquationFields_of_baseFixingAlternative
    (T : RoleHingeTransitions)
    (H : BaseFixingAlternative T) :
    exists P : PeriodRows, P.transitions = T :=
  (PeriodBaseFixingCertificate.mk T H).exists_concretePeriodEquationFields

/-- Any assembled W14 row package carries the W15 base-fixing alternative. -/
theorem baseFixingAlternative_of_concretePeriodEquationFields
    (P : PeriodRows) :
    BaseFixingAlternative P.transitions :=
  PeriodRowsAllPositiveProofW15.baseFixingAlternative_of_rows P

/-- The W16 assembly route is exactly the W15 checked alternative. -/
theorem concretePeriodEquationFields_iff_baseFixingAlternative
    (T : RoleHingeTransitions) :
    (exists P : PeriodRows, P.transitions = T) <->
      BaseFixingAlternative T :=
  PeriodRowsAllPositiveProofW15.rows_exist_iff_baseFixingAlternative T

/-- The current connector-only concrete obligations do not provide the
one-step base-fixing input for the all-positive W14 row route. -/
theorem concreteConnectorOnly_baseFixingAlternative_absent :
    Not
      (PeriodCertificateExamples.TransitionFixesBase
          TransitionAlternativeW13.ConcreteTransitionObligations
          BaseTransitionRealization.exactBase
          OrientationData.BlockOrientation.same \/
        PeriodCertificateExamples.TransitionFixesBase
          TransitionAlternativeW13.ConcreteTransitionObligations
          BaseTransitionRealization.exactBase
          OrientationData.BlockOrientation.opposite) := by
  intro H
  rcases H with hsame | hopposite
  · exact
      TransitionAlternativeW13.concreteTransitionObligations_transitionFixesExactBase_blocked
        OrientationData.BlockOrientation.same hsame
  · exact
      TransitionAlternativeW13.concreteTransitionObligations_transitionFixesExactBase_blocked
        OrientationData.BlockOrientation.opposite hopposite

end

end PeriodBaseFixingCertificateW16
end PachToth
end ErdosProblems1066
