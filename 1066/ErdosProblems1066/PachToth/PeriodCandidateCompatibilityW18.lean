import ErdosProblems1066.PachToth.AllPositiveFinalCertificateW17
import ErdosProblems1066.PachToth.BaseFixingRowsViableW17
import ErdosProblems1066.PachToth.ViableTransitionPackageW17

set_option autoImplicit false

/-!
# W18 period-candidate compatibility

This file supplies the adapter for the compatibility equation required by
`AllPositiveFinalCertificateW17.PeriodCompatibility`.  The equation is a W12
period-field equality; since the row proofs live in propositions, it reduces
to agreement of the transition package and the finite word family.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodCandidateCompatibilityW18

noncomputable section

abbrev W12PeriodEquationFields :=
  FiniteCertificateObligationsW12.PeriodEquationFields

abbrev PeriodRows :=
  AllPositiveFinalCertificateW17.PeriodRows

abbrev PeriodCandidateFamily :=
  AllPositiveFinalCertificateW17.PeriodCandidateFamily

abbrev PeriodCompatibility :=
  AllPositiveFinalCertificateW17.PeriodCompatibility

abbrev PeriodBaseFixingCertificate :=
  AllPositiveFinalCertificateW17.PeriodBaseFixingCertificate

abbrev ViableTransitionFields :=
  BaseFixingRowsViableW17.ViableTransitionFields

abbrev BaseFixingRows :=
  BaseFixingRowsViableW17.BaseFixingRows

abbrev SameBaseFixingRows :=
  BaseFixingRowsViableW17.SameBaseFixingRows

abbrev W16ReadyRoleHingeTransitionPackage :=
  ViableTransitionPackageW17.W16ReadyRoleHingeTransitionPackage

def periodRowsOfCandidateFamily
    (F : PeriodCandidateFamily) :
    PeriodRows :=
  PeriodEquationConcreteW14.ofPeriodCandidateFamily F

@[simp]
theorem periodRowsOfCandidateFamily_toW12
    (F : PeriodCandidateFamily) :
    (periodRowsOfCandidateFamily F).toW12PeriodEquationFields =
      AllPositiveFiniteFieldsW14.periodFieldsOfCandidateFamily F := by
  rfl

theorem candidateFamily_periodCompatibility
    (F : PeriodCandidateFamily) :
    PeriodCompatibility (periodRowsOfCandidateFamily F) F := by
  rfl

theorem w12PeriodEquationFields_ext
    (A B : W12PeriodEquationFields)
    (htransitions : A.transitions = B.transitions)
    (hword :
      forall (k : Nat) (hk : 0 < k),
        A.word k hk = B.word k hk) :
    A = B := by
  cases A with
  | mk Atransitions Aword Aequation =>
      cases B with
      | mk Btransitions Bword Bequation =>
          dsimp at htransitions hword
          subst Btransitions
          have hword_fun : Aword = Bword := by
            funext k hk
            exact hword k hk
          subst Bword
          congr

theorem periodCompatibility_of_transitions_word
    (P : PeriodRows) (F : PeriodCandidateFamily)
    (htransitions : P.transitions = F.transitions.toRoleHingeTransitions)
    (hword :
      forall (k : Nat) (hk : 0 < k),
        P.word k hk = F.word k hk) :
    PeriodCompatibility P F :=
  w12PeriodEquationFields_ext
    (AllPositiveFiniteFieldsW14.periodFieldsOfCandidateFamily F)
    P.toW12PeriodEquationFields
    htransitions.symm
    (fun k hk => (hword k hk).symm)

@[simp]
theorem ofW12_toW12PeriodEquationFields
    (P : PeriodRows) :
    PeriodEquationConcreteW14.ofW12PeriodEquationFields
      P.toW12PeriodEquationFields = P := by
  cases P
  rfl

@[simp]
theorem ofW12_periodFieldsOfCandidateFamily
    (F : PeriodCandidateFamily) :
    PeriodEquationConcreteW14.ofW12PeriodEquationFields
      (AllPositiveFiniteFieldsW14.periodFieldsOfCandidateFamily F) =
      periodRowsOfCandidateFamily F := by
  rfl

theorem periodCompatibility_iff_rows_eq_candidate
    (P : PeriodRows) (F : PeriodCandidateFamily) :
    PeriodCompatibility P F <->
      P = periodRowsOfCandidateFamily F := by
  constructor
  case mp =>
    intro hcompat
    have hrows :
        PeriodEquationConcreteW14.ofW12PeriodEquationFields
          (AllPositiveFiniteFieldsW14.periodFieldsOfCandidateFamily F) =
        PeriodEquationConcreteW14.ofW12PeriodEquationFields
          P.toW12PeriodEquationFields := by
      rw [hcompat]
    simpa [periodRowsOfCandidateFamily] using hrows.symm
  case mpr =>
    intro hrows
    subst P
    exact candidateFamily_periodCompatibility F

theorem periodCompatibility_of_rows_eq_candidate
    (P : PeriodRows) (F : PeriodCandidateFamily)
    (hrows : P = periodRowsOfCandidateFamily F) :
    PeriodCompatibility P F :=
  (periodCompatibility_iff_rows_eq_candidate P F).2 hrows

theorem periodCompatibility_of_baseFixingRows
    {V : ViableTransitionFields} (B : BaseFixingRows V)
    (F : PeriodCandidateFamily)
    (htransitions : V.transitions = F.transitions.toRoleHingeTransitions)
    (hword :
      forall (k : Nat) (hk : 0 < k),
        B.rows.word k hk = F.word k hk) :
    PeriodCompatibility B.rows F :=
  periodCompatibility_of_transitions_word B.rows F
    (by rw [B.rows_transitions, htransitions])
    hword

theorem baseFixingRows_periodCompatibility_iff_rows_eq_candidate
    {V : ViableTransitionFields} (B : BaseFixingRows V)
    (F : PeriodCandidateFamily) :
    PeriodCompatibility B.rows F <->
      B.rows = periodRowsOfCandidateFamily F :=
  periodCompatibility_iff_rows_eq_candidate B.rows F

theorem periodCompatibility_of_baseFixingRows_eq_candidate
    {V : ViableTransitionFields} (B : BaseFixingRows V)
    (F : PeriodCandidateFamily)
    (hrows : B.rows = periodRowsOfCandidateFamily F) :
    PeriodCompatibility B.rows F :=
  periodCompatibility_of_rows_eq_candidate B.rows F hrows

theorem periodCompatibility_of_sameBaseFixingRows
    {V : ViableTransitionFields} (S : SameBaseFixingRows V)
    (F : PeriodCandidateFamily)
    (htransitions : V.transitions = F.transitions.toRoleHingeTransitions)
    (hword :
      forall (k : Nat) (hk : 0 < k),
        F.word k hk =
          PeriodCertificateExamples.allPositiveSameWord k hk) :
    PeriodCompatibility S.rows F :=
  periodCompatibility_of_transitions_word S.rows F
    (by rw [S.rows_transitions, htransitions])
    (fun k hk => (S.rows_word k hk).trans (hword k hk).symm)

theorem periodCompatibility_of_w15_sameRows
    (T : PeriodRowsAllPositiveProofW15.RoleHingeTransitions)
    (hfix : PeriodRowsAllPositiveProofW15.SameFixesExactBase T)
    (F : PeriodCandidateFamily)
    (htransitions : T = F.transitions.toRoleHingeTransitions)
    (hword :
      forall (k : Nat) (hk : 0 < k),
        F.word k hk =
          PeriodCertificateExamples.allPositiveSameWord k hk) :
    PeriodCompatibility (PeriodRowsAllPositiveProofW15.sameRows T hfix) F :=
  periodCompatibility_of_transitions_word
    (PeriodRowsAllPositiveProofW15.sameRows T hfix) F
    (by rw [PeriodRowsAllPositiveProofW15.sameRows_transitions,
      htransitions])
    (fun k hk =>
      (PeriodRowsAllPositiveProofW15.sameRows_word T hfix k hk).trans
        (hword k hk).symm)

theorem periodCompatibility_of_w15_oppositeRows
    (T : PeriodRowsAllPositiveProofW15.RoleHingeTransitions)
    (hfix : PeriodRowsAllPositiveProofW15.OppositeFixesExactBase T)
    (F : PeriodCandidateFamily)
    (htransitions : T = F.transitions.toRoleHingeTransitions)
    (hword :
      forall (k : Nat) (hk : 0 < k),
        F.word k hk =
          PeriodCertificateExamples.allPositiveOppositeWord k hk) :
    PeriodCompatibility (PeriodRowsAllPositiveProofW15.oppositeRows T hfix) F :=
  periodCompatibility_of_transitions_word
    (PeriodRowsAllPositiveProofW15.oppositeRows T hfix) F
    (by rw [PeriodRowsAllPositiveProofW15.oppositeRows_transitions,
      htransitions])
    (fun k hk =>
      (PeriodRowsAllPositiveProofW15.oppositeRows_word T hfix k hk).trans
        (hword k hk).symm)

theorem periodCompatibility_of_w16_sameRows
    (T : PeriodBaseFixingSameW16.RoleHingeTransitions)
    (hfix : PeriodBaseFixingSameW16.SameFixesExactBase T)
    (F : PeriodCandidateFamily)
    (htransitions : T = F.transitions.toRoleHingeTransitions)
    (hword :
      forall (k : Nat) (hk : 0 < k),
        F.word k hk =
          PeriodCertificateExamples.allPositiveSameWord k hk) :
    PeriodCompatibility (PeriodBaseFixingSameW16.sameRows T hfix) F :=
  periodCompatibility_of_transitions_word
    (PeriodBaseFixingSameW16.sameRows T hfix) F
    (by rw [PeriodBaseFixingSameW16.sameRows_transitions, htransitions])
    (fun k hk =>
      (PeriodBaseFixingSameW16.sameRows_word T hfix k hk).trans
        (hword k hk).symm)

theorem periodCompatibility_of_baseFixingCertificate_rows_eq_candidate
    (C : PeriodBaseFixingCertificate)
    (F : PeriodCandidateFamily)
    (hrows :
      AllPositiveFinalCertificateW17.periodRowsOfBaseFixingCertificate C =
        periodRowsOfCandidateFamily F) :
    PeriodCompatibility
      (AllPositiveFinalCertificateW17.periodRowsOfBaseFixingCertificate C) F :=
  periodCompatibility_of_rows_eq_candidate
    (AllPositiveFinalCertificateW17.periodRowsOfBaseFixingCertificate C)
    F hrows

theorem baseFixingCertificate_periodCompatibility_iff_rows_eq_candidate
    (C : PeriodBaseFixingCertificate)
    (F : PeriodCandidateFamily) :
    PeriodCompatibility
        (AllPositiveFinalCertificateW17.periodRowsOfBaseFixingCertificate C) F <->
      AllPositiveFinalCertificateW17.periodRowsOfBaseFixingCertificate C =
        periodRowsOfCandidateFamily F :=
  periodCompatibility_iff_rows_eq_candidate
    (AllPositiveFinalCertificateW17.periodRowsOfBaseFixingCertificate C) F

theorem periodCompatibility_of_w16Ready_transitions_word
    (P : W16ReadyRoleHingeTransitionPackage)
    (F : PeriodCandidateFamily)
    (htransitions : P.transitions = F.transitions.toRoleHingeTransitions)
    (hword :
      forall (k : Nat) (hk : 0 < k),
        P.toConcretePeriodEquationFields.word k hk = F.word k hk) :
    PeriodCompatibility P.toConcretePeriodEquationFields F :=
  periodCompatibility_of_transitions_word P.toConcretePeriodEquationFields F
    (by rw [P.toConcretePeriodEquationFields_transitions, htransitions])
    hword

theorem w16Ready_periodCompatibility_iff_rows_eq_candidate
    (P : W16ReadyRoleHingeTransitionPackage)
    (F : PeriodCandidateFamily) :
    PeriodCompatibility P.toConcretePeriodEquationFields F <->
      P.toConcretePeriodEquationFields = periodRowsOfCandidateFamily F :=
  periodCompatibility_iff_rows_eq_candidate P.toConcretePeriodEquationFields F

end

end PeriodCandidateCompatibilityW18
end PachToth
end ErdosProblems1066
