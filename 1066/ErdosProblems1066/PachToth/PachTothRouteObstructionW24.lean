import ErdosProblems1066.PachToth.PachTothW23RouteAudit
import ErdosProblems1066.PachToth.PachTothKnownBoundsFromConcreteRowsW23
import ErdosProblems1066.PachToth.ConcreteValueMatrixRowPackageInhabitationW23
import ErdosProblems1066.PachToth.CandidateValueMatrixRowPackageInhabitationW23
import ErdosProblems1066.PachToth.PeriodBaseFixingSourceInhabitationW23

set_option autoImplicit false

/-!
# W24 Pach-Toth route obstruction consolidation

This audit layer records the current bad route precisely: the W23 concrete and
candidate row-gated endpoint packages are not independent route successes.
Each one already contains period-equation source fields for a strong
role-hinge transition package, while the same transition package has the
existing W23 missing-base-fixing obstruction.

No global `5/16` endpoint is asserted here.  All endpoint mentions below stay
inside `Nonempty` row-gated packages or implications out of such packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothRouteObstructionW24

noncomputable section

abbrev KnownBoundsGate : Prop :=
  PachTothW23RouteAudit.KnownBoundsGate

abbrev ConcreteValueMatrixRowPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.ConcreteValueMatrixRowPackage

abbrev CandidateValueMatrixRowPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.CandidateValueMatrixRowPackage

abbrev ConcreteRowsEndpointPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.ConcreteRowsEndpointPackage

abbrev CandidateRowsEndpointPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.CandidateRowsEndpointPackage

abbrev ConcretePeriodSearchData : Type :=
  ConcreteValueMatrixRowPackageInhabitationW23.PeriodSearchData

abbrev ConcreteW18RowFamilies
    (periodSearch : ConcretePeriodSearchData) : Type :=
  ConcreteValueMatrixRowPackageInhabitationW23.W18RowFamilies periodSearch

abbrev CandidatePeriodFamily : Type :=
  CandidateValueMatrixRowPackageInhabitationW23.PeriodCandidateFamily

abbrev CandidateValueRowsFor
    (period : CandidatePeriodFamily) : Type :=
  CandidateValueMatrixRowPackageInhabitationW23.CandidateValueRowsFor period

abbrev CandidateValueInputsBridge : Type :=
  CandidateValueMatrixRowPackageInhabitationW23.CandidateValueInputsBridge

abbrev PeriodBaseFixingCertificate : Type :=
  CandidateValueMatrixRowPackageInhabitationW23.PeriodBaseFixingCertificate

abbrev RoleHingeTransitions : Type :=
  PeriodBaseFixingSourceInhabitationW23.RoleHingeTransitions

abbrev RoleHingeSourceFields (T : RoleHingeTransitions) : Type :=
  PeriodBaseFixingSourceInhabitationW23.RoleHingeSourceFields T

abbrev BaseFixingAlternative (T : RoleHingeTransitions) : Prop :=
  PeriodBaseFixingSourceInhabitationW23.BaseFixingAlternative T

abbrev MissingBaseFixingRows (T : RoleHingeTransitions) : Prop :=
  PeriodBaseFixingSourceInhabitationW23.MissingBaseFixingRows T

/-! ## Shared role-hinge/base-fixing obstruction -/

def sourceFieldsOfConcretePeriodSearchData
    (periodSearch : ConcretePeriodSearchData) :
    RoleHingeSourceFields periodSearch.transitions where
  word := periodSearch.word
  equations := periodSearch.exactPeriodEquations

def sourceFieldsOfCandidatePeriodFamily
    (period : CandidatePeriodFamily) :
    RoleHingeSourceFields period.transitions.toRoleHingeTransitions where
  word := period.word
  equations := by
    intro k hk
    exact period.equations k hk

theorem roleHingeSourceFields_iff_baseFixingAlternative
    (T : RoleHingeTransitions) :
    Nonempty (RoleHingeSourceFields T) <-> BaseFixingAlternative T :=
  PeriodBaseFixingSourceInhabitationW23.sourceFields_iff_baseFixingAlternative_via_certificate
    T

theorem not_nonempty_roleHingeSourceFields_iff_missingBaseFixingRows
    (T : RoleHingeTransitions) :
    Not (Nonempty (RoleHingeSourceFields T)) <->
      MissingBaseFixingRows T :=
  PeriodBaseFixingSourceInhabitationW23.not_nonempty_sourceFields_iff_missingBaseFixingRows_sharp
    T

theorem missingBaseFixingRows_of_roleHingeTransitions
    (T : RoleHingeTransitions) :
    MissingBaseFixingRows T :=
  PeriodBaseFixingSourceInhabitationW23.missingBaseFixingRows_of_roleHingeTransitions
    T

theorem not_baseFixingAlternative_of_roleHingeTransitions
    (T : RoleHingeTransitions) :
    Not (BaseFixingAlternative T) :=
  PeriodBaseFixingSourceInhabitationW23.not_baseFixingAlternative_of_roleHingeTransitions
    T

theorem no_sourceFields_and_missingBaseFixingRows
    (T : RoleHingeTransitions) :
    Not (Nonempty (RoleHingeSourceFields T) /\
      MissingBaseFixingRows T) := by
  intro h
  exact
    ((not_nonempty_roleHingeSourceFields_iff_missingBaseFixingRows T).2
      h.2) h.1

theorem no_roleHingePeriodEquationRows :
    Not (Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T)) :=
  PachTothW23RouteAudit.no_roleHingePeriodEquationRows

/-! ## Concrete W23 row-gated endpoint route -/

theorem nonempty_concreteRowsEndpointPackage_iff_rowPackage :
    Nonempty ConcreteRowsEndpointPackage <->
      Nonempty ConcreteValueMatrixRowPackage :=
  PachTothKnownBoundsFromConcreteRowsW23.nonempty_concreteRowsEndpointPackage_iff_rowPackage

theorem nonempty_concreteRowPackage_iff_w18RowFamilies :
    Nonempty ConcreteValueMatrixRowPackage <->
      Exists fun periodSearch : ConcretePeriodSearchData =>
        Nonempty (ConcreteW18RowFamilies periodSearch) :=
  ConcreteValueMatrixRowPackageInhabitationW23.nonempty_rowPackage_iff_exists_w18RowFamilies

theorem nonempty_concreteRowsEndpointPackage_iff_w18RowFamilies :
    Nonempty ConcreteRowsEndpointPackage <->
      Exists fun periodSearch : ConcretePeriodSearchData =>
        Nonempty (ConcreteW18RowFamilies periodSearch) :=
  nonempty_concreteRowsEndpointPackage_iff_rowPackage.trans
    nonempty_concreteRowPackage_iff_w18RowFamilies

theorem concreteRowPackage_implies_roleHingeSourceFields
    (H : Nonempty ConcreteValueMatrixRowPackage) :
    Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T) := by
  cases H with
  | intro rows =>
      exact
        Exists.intro rows.periodSearch.transitions
          (Nonempty.intro
            (sourceFieldsOfConcretePeriodSearchData rows.periodSearch))

theorem concreteRowsEndpointPackage_implies_roleHingeSourceFields
    (H : Nonempty ConcreteRowsEndpointPackage) :
    Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T) :=
  concreteRowPackage_implies_roleHingeSourceFields
    (nonempty_concreteRowsEndpointPackage_iff_rowPackage.1 H)

theorem concreteRowPackage_implies_sourceFields_and_missingBaseFixingRows
    (H : Nonempty ConcreteValueMatrixRowPackage) :
    Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T) /\
        MissingBaseFixingRows T := by
  cases H with
  | intro rows =>
      exact
        Exists.intro rows.periodSearch.transitions
          (And.intro
            (Nonempty.intro
              (sourceFieldsOfConcretePeriodSearchData rows.periodSearch))
            (missingBaseFixingRows_of_roleHingeTransitions
              rows.periodSearch.transitions))

theorem concreteRowsEndpointPackage_implies_sourceFields_and_missingBaseFixingRows
    (H : Nonempty ConcreteRowsEndpointPackage) :
    Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T) /\
        MissingBaseFixingRows T :=
  concreteRowPackage_implies_sourceFields_and_missingBaseFixingRows
    (nonempty_concreteRowsEndpointPackage_iff_rowPackage.1 H)

theorem not_nonempty_concreteValueMatrixRowPackage :
    Not (Nonempty ConcreteValueMatrixRowPackage) := by
  intro H
  exact no_roleHingePeriodEquationRows
    (concreteRowPackage_implies_roleHingeSourceFields H)

theorem not_nonempty_concreteRowsEndpointPackage :
    Not (Nonempty ConcreteRowsEndpointPackage) := by
  intro H
  exact no_roleHingePeriodEquationRows
    (concreteRowsEndpointPackage_implies_roleHingeSourceFields H)

theorem nonempty_concreteValueMatrixRowPackage_iff_false :
    Nonempty ConcreteValueMatrixRowPackage <-> False := by
  constructor
  case mp =>
    exact not_nonempty_concreteValueMatrixRowPackage
  case mpr =>
    intro h
    cases h

theorem nonempty_concreteRowsEndpointPackage_iff_false :
    Nonempty ConcreteRowsEndpointPackage <-> False := by
  constructor
  case mp =>
    exact not_nonempty_concreteRowsEndpointPackage
  case mpr =>
    intro h
    cases h

theorem no_concreteRowsEndpointPackage
    (E : ConcreteRowsEndpointPackage) :
    False :=
  not_nonempty_concreteRowsEndpointPackage (Nonempty.intro E)

/-! ## Candidate W23 row-gated endpoint route -/

theorem nonempty_candidateRowsEndpointPackage_iff_rowPackage :
    Nonempty CandidateRowsEndpointPackage <->
      Nonempty CandidateValueMatrixRowPackage :=
  PachTothKnownBoundsFromConcreteRowsW23.nonempty_candidateRowsEndpointPackage_iff_rowPackage

theorem nonempty_candidateRowPackage_iff_candidateValueRowsFor :
    Nonempty CandidateValueMatrixRowPackage <->
      Exists fun period : CandidatePeriodFamily =>
        Nonempty (CandidateValueRowsFor period) :=
  CandidateValueMatrixRowPackageInhabitationW23.nonempty_rowPackage_iff_exists_candidateValueRowsFor

theorem nonempty_candidateRowsEndpointPackage_iff_candidateValueRowsFor :
    Nonempty CandidateRowsEndpointPackage <->
      Exists fun period : CandidatePeriodFamily =>
        Nonempty (CandidateValueRowsFor period) :=
  nonempty_candidateRowsEndpointPackage_iff_rowPackage.trans
    nonempty_candidateRowPackage_iff_candidateValueRowsFor

theorem candidateRowPackage_implies_periodFamily
    (H : Nonempty CandidateValueMatrixRowPackage) :
    Nonempty CandidatePeriodFamily := by
  cases H with
  | intro rows =>
      exact Nonempty.intro rows.period

theorem candidateRowsEndpointPackage_implies_periodFamily
    (H : Nonempty CandidateRowsEndpointPackage) :
    Nonempty CandidatePeriodFamily :=
  candidateRowPackage_implies_periodFamily
    (nonempty_candidateRowsEndpointPackage_iff_rowPackage.1 H)

theorem candidateRowPackage_implies_roleHingeSourceFields
    (H : Nonempty CandidateValueMatrixRowPackage) :
    Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T) := by
  cases H with
  | intro rows =>
      exact
        Exists.intro rows.period.transitions.toRoleHingeTransitions
          (Nonempty.intro
            (sourceFieldsOfCandidatePeriodFamily rows.period))

theorem candidateRowsEndpointPackage_implies_roleHingeSourceFields
    (H : Nonempty CandidateRowsEndpointPackage) :
    Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T) :=
  candidateRowPackage_implies_roleHingeSourceFields
    (nonempty_candidateRowsEndpointPackage_iff_rowPackage.1 H)

theorem candidateRowPackage_implies_sourceFields_and_missingBaseFixingRows
    (H : Nonempty CandidateValueMatrixRowPackage) :
    Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T) /\
        MissingBaseFixingRows T := by
  cases H with
  | intro rows =>
      exact
        Exists.intro rows.period.transitions.toRoleHingeTransitions
          (And.intro
            (Nonempty.intro
              (sourceFieldsOfCandidatePeriodFamily rows.period))
            (missingBaseFixingRows_of_roleHingeTransitions
              rows.period.transitions.toRoleHingeTransitions))

theorem candidateRowsEndpointPackage_implies_sourceFields_and_missingBaseFixingRows
    (H : Nonempty CandidateRowsEndpointPackage) :
    Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T) /\
        MissingBaseFixingRows T :=
  candidateRowPackage_implies_sourceFields_and_missingBaseFixingRows
    (nonempty_candidateRowsEndpointPackage_iff_rowPackage.1 H)

theorem not_nonempty_candidatePeriodFamily :
    Not (Nonempty CandidatePeriodFamily) :=
  CandidateValueMatrixRowPackageInhabitationW23.not_nonempty_periodCandidateFamily

theorem not_nonempty_candidateValueMatrixRowPackage :
    Not (Nonempty CandidateValueMatrixRowPackage) := by
  intro H
  exact no_roleHingePeriodEquationRows
    (candidateRowPackage_implies_roleHingeSourceFields H)

theorem not_nonempty_candidateRowsEndpointPackage :
    Not (Nonempty CandidateRowsEndpointPackage) := by
  intro H
  exact no_roleHingePeriodEquationRows
    (candidateRowsEndpointPackage_implies_roleHingeSourceFields H)

theorem nonempty_candidatePeriodFamily_iff_false :
    Nonempty CandidatePeriodFamily <-> False := by
  constructor
  case mp =>
    exact not_nonempty_candidatePeriodFamily
  case mpr =>
    intro h
    cases h

theorem nonempty_candidateValueMatrixRowPackage_iff_false :
    Nonempty CandidateValueMatrixRowPackage <-> False := by
  constructor
  case mp =>
    exact not_nonempty_candidateValueMatrixRowPackage
  case mpr =>
    intro h
    cases h

theorem nonempty_candidateRowsEndpointPackage_iff_false :
    Nonempty CandidateRowsEndpointPackage <-> False := by
  constructor
  case mp =>
    exact not_nonempty_candidateRowsEndpointPackage
  case mpr =>
    intro h
    cases h

theorem no_candidateRowsEndpointPackage
    (E : CandidateRowsEndpointPackage) :
    False :=
  not_nonempty_candidateRowsEndpointPackage (Nonempty.intro E)

/-! ## Candidate bridge with base-fixing compatibility -/

theorem nonempty_candidateBridge_iff_exists_rowPackage_base_compatibility :
    Nonempty CandidateValueInputsBridge <->
      Exists fun P : CandidateValueMatrixRowPackage =>
        Exists fun base : PeriodBaseFixingCertificate =>
          AllPositiveInputsProducerW18.PeriodCompatibility
            (AllPositiveInputsProducerW18.periodRowsOfBaseFixingCertificate
              base)
            P.period :=
  CandidateValueMatrixRowPackageInhabitationW23.nonempty_bridge_iff_exists_rowPackage_base_compatibility

theorem candidateBridge_implies_rowPackage
    (H : Nonempty CandidateValueInputsBridge) :
    Nonempty CandidateValueMatrixRowPackage := by
  cases H with
  | intro bridge =>
      exact Nonempty.intro bridge.rows

theorem candidateBridge_implies_baseFixingCertificate
    (H : Nonempty CandidateValueInputsBridge) :
    Nonempty PeriodBaseFixingCertificate := by
  cases H with
  | intro bridge =>
      exact Nonempty.intro bridge.base

theorem candidateBridge_implies_sourceFields_and_missingBaseFixingRows
    (H : Nonempty CandidateValueInputsBridge) :
    Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T) /\
        MissingBaseFixingRows T :=
  candidateRowPackage_implies_sourceFields_and_missingBaseFixingRows
    (candidateBridge_implies_rowPackage H)

theorem not_nonempty_candidateBridge_via_roleHinge :
    Not (Nonempty CandidateValueInputsBridge) := by
  intro H
  exact not_nonempty_candidateValueMatrixRowPackage
    (candidateBridge_implies_rowPackage H)

theorem not_nonempty_candidateBridge_via_baseFixing :
    Not (Nonempty CandidateValueInputsBridge) :=
  CandidateValueMatrixRowPackageInhabitationW23.not_nonempty_bridge_of_baseFixing_no_go

theorem nonempty_candidateBridge_iff_false :
    Nonempty CandidateValueInputsBridge <-> False := by
  constructor
  case mp =>
    exact not_nonempty_candidateBridge_via_roleHinge
  case mpr =>
    intro h
    cases h

end

end PachTothRouteObstructionW24
end PachToth

namespace Verified

abbrev PachTothW24ConcreteRowsEndpointPackage : Type :=
  PachToth.PachTothRouteObstructionW24.ConcreteRowsEndpointPackage

abbrev PachTothW24CandidateRowsEndpointPackage : Type :=
  PachToth.PachTothRouteObstructionW24.CandidateRowsEndpointPackage

theorem pachtoth_w24_no_concreteRowsEndpointPackage :
    Not (Nonempty PachTothW24ConcreteRowsEndpointPackage) :=
  PachToth.PachTothRouteObstructionW24.not_nonempty_concreteRowsEndpointPackage

theorem pachtoth_w24_no_candidateRowsEndpointPackage :
    Not (Nonempty PachTothW24CandidateRowsEndpointPackage) :=
  PachToth.PachTothRouteObstructionW24.not_nonempty_candidateRowsEndpointPackage

end Verified
end ErdosProblems1066
