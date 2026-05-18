import ErdosProblems1066.PachToth.GeneratedChainSourceFieldsConcreteClosureW23
import ErdosProblems1066.PachToth.ConcreteValueMatrixRowPackageInhabitationW23
import ErdosProblems1066.PachToth.CandidateValueMatrixRowPackageInhabitationW23
import ErdosProblems1066.PachToth.ExactBaseFullMetricConcreteW23

set_option autoImplicit false

/-!
# W24 non-role-hinge period source boundary

This module records the precise boundary found in the W20--W23 Pach--Toth
source-field routes.

The raw W20 reduced source-field interface is generic, but the concrete
period/value-matrix routes currently available in W22/W23 all pass through
`ConcretePeriodSearchFamily.PeriodSearchData`, hence through the strong
`RoleHingeTransitions` package already proved empty.  The viable exact-base
replacement is the full-metric source interface from W21/W22; the current
role-hinged handoff into that replacement still factors through a
role-hinged period-search family.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonRoleHingePeriodSourceW24

noncomputable section

abbrev W20SourceFields : Type :=
  GeneratedChainFamilyProducerW20.SourceFields

abbrev PeriodSearchData : Type :=
  ConcreteValueMatrixRowPackageInhabitationW23.PeriodSearchData

abbrev RoleHingeTransitions : Type :=
  ConcreteValueMatrixRowPackageInhabitationW23.RoleHingeTransitions

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteValueMatrixRowPackageInhabitationW23.RowPackage

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteValueMatrixRowPackageInhabitationW23.ConcreteValueMatrixFamily

abbrev W18RowFamilies (periodSearch : PeriodSearchData) : Type :=
  ConcreteValueMatrixRowPackageInhabitationW23.W18RowFamilies periodSearch

abbrev CandidatePeriodFamily : Type :=
  CandidateValueMatrixRowPackageInhabitationW23.PeriodCandidateFamily

abbrev CandidateValueMatrixRowPackage : Type :=
  CandidateValueMatrixRowPackageInhabitationW23.CandidateValueMatrixRowPackage

abbrev CandidateValueMatrixFamily : Type :=
  CandidateValueMatrixRowPackageInhabitationW23.CandidateValueMatrixFamily

abbrev CandidateValueRowsFor (period : CandidatePeriodFamily) : Type :=
  CandidateValueMatrixRowPackageInhabitationW23.CandidateValueRowsFor period

/-! ## Concrete W22/W23 value-matrix route -/

/-- The exact W23 handoff from a concrete value-matrix row package to the raw
W20 source-field interface.  The extra equality keeps this route pinned to the
named W23 constructor, instead of being an arbitrary inhabitant of the generic
W20 source-field type. -/
structure ConcreteValueMatrixW20SourceRoute where
  rows : ConcreteValueMatrixRowPackage
  source : W20SourceFields
  source_eq :
    source =
      GeneratedChainSourceFieldsConcreteClosureW23.sourceFieldsOfConcreteValueMatrixRowPackage
        rows

def concreteValueMatrixW20SourceRouteOfRows
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteValueMatrixW20SourceRoute where
  rows := P
  source :=
    GeneratedChainSourceFieldsConcreteClosureW23.sourceFieldsOfConcreteValueMatrixRowPackage
      P
  source_eq := rfl

theorem nonempty_concreteValueMatrixW20SourceRoute_iff_rowPackage :
    Nonempty ConcreteValueMatrixW20SourceRoute <->
      Nonempty ConcreteValueMatrixRowPackage := by
  constructor
  case mp =>
    intro h
    exact h.elim (fun R => Nonempty.intro R.rows)
  case mpr =>
    intro h
    exact h.elim
      (fun P => Nonempty.intro (concreteValueMatrixW20SourceRouteOfRows P))

theorem nonempty_concreteValueMatrixW20SourceRoute_iff_concreteValueMatrixFamily :
    Nonempty ConcreteValueMatrixW20SourceRoute <->
      Nonempty ConcreteValueMatrixFamily :=
  Iff.trans
    nonempty_concreteValueMatrixW20SourceRoute_iff_rowPackage
    ConcreteValueMatrixFamilyInhabitationW22.nonempty_concreteValueMatrixFamily_iff_rowPackage.symm

theorem nonempty_concreteValueMatrixRowPackage_iff_exists_periodSearch_w18Rows :
    Nonempty ConcreteValueMatrixRowPackage <->
      Exists fun periodSearch : PeriodSearchData =>
        Nonempty (W18RowFamilies periodSearch) :=
  ConcreteValueMatrixRowPackageInhabitationW23.nonempty_rowPackage_iff_exists_w18RowFamilies

theorem concreteValueMatrixW20SourceRoute_requires_periodSearchData :
    Nonempty ConcreteValueMatrixW20SourceRoute ->
      Nonempty PeriodSearchData := by
  intro h
  exact
    ConcreteValueMatrixRowPackageInhabitationW23.rowPackage_requires_periodSearchData
      ((nonempty_concreteValueMatrixW20SourceRoute_iff_rowPackage).1 h)

theorem periodSearchData_requires_roleHingeTransitions :
    Nonempty PeriodSearchData -> Nonempty RoleHingeTransitions :=
  ConcreteValueMatrixRowPackageInhabitationW23.periodSearchData_requires_roleHingeTransitions

theorem concreteValueMatrixW20SourceRoute_requires_roleHingeTransitions :
    Nonempty ConcreteValueMatrixW20SourceRoute ->
      Nonempty RoleHingeTransitions := by
  intro h
  exact
    periodSearchData_requires_roleHingeTransitions
      (concreteValueMatrixW20SourceRoute_requires_periodSearchData h)

theorem not_nonempty_roleHingeTransitions :
    Not (Nonempty RoleHingeTransitions) :=
  ConcreteValueMatrixRowPackageInhabitationW23.not_nonempty_roleHingeTransitions

theorem not_nonempty_periodSearchData :
    Not (Nonempty PeriodSearchData) :=
  ConcreteValueMatrixRowPackageInhabitationW23.not_nonempty_periodSearchData

theorem not_nonempty_concreteValueMatrixW20SourceRoute :
    Not (Nonempty ConcreteValueMatrixW20SourceRoute) := by
  intro h
  exact
    not_nonempty_roleHingeTransitions
      (concreteValueMatrixW20SourceRoute_requires_roleHingeTransitions h)

theorem not_nonempty_concreteValueMatrixRowPackage :
    Not (Nonempty ConcreteValueMatrixRowPackage) :=
  ConcreteValueMatrixRowPackageInhabitationW23.not_nonempty_rowPackage

theorem not_nonempty_concreteValueMatrixFamily :
    Not (Nonempty ConcreteValueMatrixFamily) :=
  ConcreteValueMatrixRowPackageInhabitationW23.no_concreteValueMatrixFamily_from_w18RowFamilies

theorem no_concreteValueMatrixW20SourceRoute_without_roleHingeTransitions
    (hno : Not (Nonempty RoleHingeTransitions)) :
    Not (Nonempty ConcreteValueMatrixW20SourceRoute) := by
  intro h
  exact hno (concreteValueMatrixW20SourceRoute_requires_roleHingeTransitions h)

/-! ## Candidate value-row route -/

theorem nonempty_candidateValueMatrixRowPackage_iff_exists_rowsFor :
    Nonempty CandidateValueMatrixRowPackage <->
      Exists fun period : CandidatePeriodFamily =>
        Nonempty (CandidateValueRowsFor period) :=
  CandidateValueMatrixRowPackageInhabitationW23.nonempty_rowPackage_iff_exists_candidateValueRowsFor

theorem nonempty_candidateValueMatrixFamily_iff_exists_rowsFor :
    Nonempty CandidateValueMatrixFamily <->
      Exists fun period : CandidatePeriodFamily =>
        Nonempty (CandidateValueRowsFor period) :=
  CandidateValueMatrixRowPackageInhabitationW23.nonempty_candidateValueMatrixFamily_iff_exists_candidateValueRowsFor

theorem not_nonempty_candidatePeriodFamily :
    Not (Nonempty CandidatePeriodFamily) :=
  CandidateValueMatrixRowPackageInhabitationW23.not_nonempty_periodCandidateFamily

theorem not_exists_candidateValueRowsFor :
    Not
      (Exists fun period : CandidatePeriodFamily =>
        Nonempty (CandidateValueRowsFor period)) :=
  CandidateValueMatrixRowPackageInhabitationW23.not_exists_candidateValueRowsFor

theorem not_nonempty_candidateValueMatrixRowPackage :
    Not (Nonempty CandidateValueMatrixRowPackage) :=
  CandidateValueMatrixRowPackageInhabitationW23.not_nonempty_candidateValueMatrixRowPackage

theorem not_nonempty_candidateValueMatrixFamily :
    Not (Nonempty CandidateValueMatrixFamily) :=
  CandidateValueMatrixRowPackageInhabitationW23.not_nonempty_candidateValueMatrixFamily

/-! ## Full-metric exact-base boundary -/

abbrev ExactBaseFullMetricSourceFields : Type :=
  ExactBaseFullMetricSourceInhabitationW22.ExactBaseFullMetricSourceFields

abbrev ExactBaseFullMetricCoreFields : Type :=
  ExactBaseFullMetricSourceInhabitationW22.ExactBaseFullMetricCoreFields

abbrev RemainingFullMetricField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  ExactBaseFullMetricSourceInhabitationW22.RemainingFullMetricField C

abbrev RemainingSeparationField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  ExactBaseFullMetricSourceInhabitationW22.RemainingSeparationField C

abbrev RemainingSameBlockField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  ExactBaseFullMetricSourceInhabitationW22.RemainingSameBlockField C

/-- This is the current non-role-hinge escape target: exact-base closure plus
full generated metric data.  It deliberately has no role-hinge transition
field. -/
theorem nonempty_exactBaseFullMetricSourceFields_iff_remainingFullMetric :
    Nonempty ExactBaseFullMetricSourceFields <->
      Exists fun C : ExactBaseFullMetricCoreFields =>
        RemainingFullMetricField C :=
  ExactBaseFullMetricSourceInhabitationW22.nonempty_exactBaseFullMetricSourceFields_iff_remainingFullMetric

theorem nonempty_exactBaseFullMetricSourceFields_iff_parts :
    Nonempty ExactBaseFullMetricSourceFields <->
      Exists fun C : ExactBaseFullMetricCoreFields =>
        RemainingSeparationField C /\ RemainingSameBlockField C :=
  ExactBaseFullMetricSourceInhabitationW22.nonempty_exactBaseFullMetricSourceFields_iff_parts

/-! ## Current role-hinged handoff into the full-metric target -/

abbrev RoleHingedPeriodSearchFamily : Type :=
  ExactBaseFullMetricConcreteW23.RoleHingedPeriodSearchFamily

abbrev RoleHingedRemainingSeparationField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ExactBaseFullMetricConcreteW23.RoleHingedRemainingSeparationField F

/-- The available W23 handoff into the full-metric exact-base source, pinned
to its role-hinged period-search input. -/
structure RoleHingedFullMetricSourceRoute where
  family : RoleHingedPeriodSearchFamily
  separated : RoleHingedRemainingSeparationField family
  source : ExactBaseFullMetricSourceFields
  source_eq :
    source =
      ExactBaseFullMetricConcreteW23.exactBaseFullMetricSourceFieldsOfRoleHingedSeparation
        family separated

def roleHingedFullMetricSourceRouteOfSeparation
    (F : RoleHingedPeriodSearchFamily)
    (separated : RoleHingedRemainingSeparationField F) :
    RoleHingedFullMetricSourceRoute where
  family := F
  separated := separated
  source :=
    ExactBaseFullMetricConcreteW23.exactBaseFullMetricSourceFieldsOfRoleHingedSeparation
      F separated
  source_eq := rfl

theorem nonempty_roleHingedFullMetricSourceRoute_iff_exists_separation :
    Nonempty RoleHingedFullMetricSourceRoute <->
      Exists fun F : RoleHingedPeriodSearchFamily =>
        RoleHingedRemainingSeparationField F := by
  constructor
  case mp =>
    intro h
    exact h.elim (fun R => Exists.intro R.family R.separated)
  case mpr =>
    intro h
    exact
      Exists.elim h
        (fun F separated =>
          Nonempty.intro
            (roleHingedFullMetricSourceRouteOfSeparation F separated))

theorem roleHingedFullMetricSourceRoute_requires_roleHingedPeriodSearchFamily :
    Nonempty RoleHingedFullMetricSourceRoute ->
      Nonempty RoleHingedPeriodSearchFamily := by
  intro h
  exact h.elim (fun R => Nonempty.intro R.family)

theorem not_nonempty_roleHingedPeriodSearchFamily :
    Not (Nonempty RoleHingedPeriodSearchFamily) :=
  RemainingSeparationInhabitationW22.not_nonempty_roleHingedPeriodSearchFamily

theorem not_nonempty_roleHingedFullMetricSourceRoute :
    Not (Nonempty RoleHingedFullMetricSourceRoute) := by
  intro h
  exact
    not_nonempty_roleHingedPeriodSearchFamily
      (roleHingedFullMetricSourceRoute_requires_roleHingedPeriodSearchFamily h)

theorem not_exists_roleHingedSeparation :
    Not
      (Exists fun F : RoleHingedPeriodSearchFamily =>
        RoleHingedRemainingSeparationField F) := by
  intro h
  exact
    not_nonempty_roleHingedFullMetricSourceRoute
      ((nonempty_roleHingedFullMetricSourceRoute_iff_exists_separation).2 h)

/-! ## Reduced connector route remains blocked -/

abbrev ConnectorReducedExactBaseSourceFields : Type :=
  GeneratedChainFamilyProducerW20.ConnectorExactBaseSourceFields

theorem not_nonempty_connectorReducedExactBaseSourceFields :
    Not (Nonempty ConnectorReducedExactBaseSourceFields) :=
  GeneratedChainFamilyProducerW20.not_nonempty_connectorExactBaseSourceFields

end

end NonRoleHingePeriodSourceW24
end PachToth
end ErdosProblems1066
