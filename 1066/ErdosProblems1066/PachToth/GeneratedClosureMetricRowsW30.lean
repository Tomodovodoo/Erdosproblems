import ErdosProblems1066.PachToth.AlternativeNonRoleSourceW28
import ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25
import ErdosProblems1066.PachToth.CompletionRowsSourceW29
import ErdosProblems1066.PachToth.FiniteRowsNoGoAuditW28
import ErdosProblems1066.PachToth.PachTothW24RouteAudit
import ErdosProblems1066.PachToth.PositiveChainComponentsSourceW29
import ErdosProblems1066.PachToth.SquaredOrbitClosureCompletionRowsW29

set_option autoImplicit false

/-!
# W30 generated-closure metric rows

This file keeps the W29 completion-row source package honest.  The actual
source data for `CompletionRowsSourceW29.GeneratedClosureMetricRowPackage` is
not an endpoint theorem and not a closed-orbit target.  It is exactly one
generated-chain family with same-family closure rows and reduced metric rows.

The role-free alternative value-matrix surface and the W24 non-role direct
source package are equivalent spellings of that data.  The positive/non-role
exact-chain sources remain useful for the exact and arbitrary endpoints, but
by themselves they do not provide the generated closure/reduced metric fields
needed by W29 completion rows.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedClosureMetricRowsW30

noncomputable section

abbrev GeneratedChainFamily : Type :=
  GeneratedClosureMetricPackageInhabitationW25.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  GeneratedClosureMetricPackageInhabitationW25.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedClosureMetricPackageInhabitationW25.ReducedMetricHypotheses F

abbrev ClosureSource
    (F : GeneratedChainFamily) :=
  GeneratedClosureMetricPackageInhabitationW25.ClosureSource F

abbrev ReducedMetricFields
    (F : GeneratedChainFamily) :=
  GeneratedClosureMetricPackageInhabitationW25.ReducedMetricFields F

abbrev W20SourceFields : Type :=
  GeneratedChainSourceFieldsInhabitationW22.SourceFields

abbrev W20ClosureReducedMetricSourceFields : Type :=
  AlternativeValueMatrixInhabitationW25.W20ClosureReducedMetricSourceFields

abbrev AlternativeValueMatrixFamily : Type :=
  AlternativeValueMatrixInhabitationW25.AlternativeValueMatrixFamily

abbrev NonRoleDirectSourceMissingPackage : Type :=
  PachTothW24RouteAudit.NonRoleDirectSourceMissingPackage

abbrev AlternativeNonRoleSourcePackage : Type :=
  AlternativeNonRoleSourceW28.AlternativeNonRoleSourcePackage

abbrev PositiveChainComponentSource : Type :=
  PositiveChainComponentsSourceW29.PositiveChainComponentSource

abbrev GeneratedClosureMetricRowPackage : Type :=
  CompletionRowsSourceW29.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  Nonempty GeneratedClosureMetricRowPackage

abbrev GeneratedOrbitSkeleton : Type :=
  CompletionRowsSourceW29.GeneratedOrbitSkeleton

abbrev CompletionRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.CompletionRows G

abbrev SquaredOrbitClosureSourceRows : Type :=
  CompletionRowsSourceW29.SquaredOrbitClosureSourceRows

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  Nonempty SquaredOrbitClosureSourceRows

abbrev ConcreteValueMatrixRowGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteValueMatrixRowGate

abbrev ConcreteLowerTableGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteLowerTableGate

abbrev ConcreteReducedMetricCertificateGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteReducedMetricCertificateGate

abbrev DirectFullMetricSourcePackageGate : Prop :=
  FiniteRowsNoGoAuditW28.DirectFullMetricSourcePackageGate

abbrev RoleHingedPeriodSearchGate : Prop :=
  FiniteRowsNoGoAuditW28.RoleHingedPeriodSearchGate

abbrev MinimalGeneratedClosureMetricSourceFields : Prop :=
  Exists fun F : GeneratedChainFamily =>
    GeneratedChainFamilyClosures F /\ ReducedMetricHypotheses F

/-! ## Constructors into the W29 completion-row source -/

def generatedClosureMetricRowPackageOfClosureReducedMetric
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (metric : ReducedMetricHypotheses F) :
    GeneratedClosureMetricRowPackage :=
  GeneratedClosureMetricPackageInhabitationW25.generatedClosureMetricRowPackageOfClosuresAndReducedMetricHypotheses
      F closure metric

def generatedClosureMetricRowPackageOfW20SourceFields
    (S : W20SourceFields) :
    GeneratedClosureMetricRowPackage :=
  GeneratedClosureMetricPackageInhabitationW25.generatedClosureMetricRowPackageOfRawSourceFields
    S

def generatedClosureMetricRowPackageOfAlternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    GeneratedClosureMetricRowPackage :=
  GeneratedClosureMetricPackageInhabitationW25.generatedClosureMetricRowPackageOfAlternativeValueMatrixFamily
    A

def generatedClosureMetricRowPackageOfNonRoleDirectSourceMissingPackage
    (P : NonRoleDirectSourceMissingPackage) :
    GeneratedClosureMetricRowPackage :=
  P.toGeneratedClosureMetricRowPackage

def completionRowsOfClosureReducedMetric
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (metric : ReducedMetricHypotheses F) :
    CompletionRows
      (CompletionRowsSourceW29.skeletonOfGeneratedClosureMetricRowPackage
        (generatedClosureMetricRowPackageOfClosureReducedMetric
          F closure metric)) :=
  CompletionRowsSourceW29.completionRowsOfGeneratedClosureMetricRowPackage
    (generatedClosureMetricRowPackageOfClosureReducedMetric F closure metric)

def sourceRowsOfClosureReducedMetric
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (metric : ReducedMetricHypotheses F) :
    SquaredOrbitClosureSourceRows :=
  CompletionRowsSourceW29.squaredOrbitClosureSourceRowsOfGeneratedClosureMetricRowPackage
      (generatedClosureMetricRowPackageOfClosureReducedMetric F closure metric)

def sourceRowsOfW20SourceFields
    (S : W20SourceFields) :
    SquaredOrbitClosureSourceRows :=
  CompletionRowsSourceW29.squaredOrbitClosureSourceRowsOfGeneratedClosureMetricRowPackage
      (generatedClosureMetricRowPackageOfW20SourceFields S)

def sourceRowsOfAlternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    SquaredOrbitClosureSourceRows :=
  CompletionRowsSourceW29.squaredOrbitClosureSourceRowsOfGeneratedClosureMetricRowPackage
      (generatedClosureMetricRowPackageOfAlternativeValueMatrixFamily A)

def sourceRowsOfNonRoleDirectSourceMissingPackage
    (P : NonRoleDirectSourceMissingPackage) :
    SquaredOrbitClosureSourceRows :=
  CompletionRowsSourceW29.squaredOrbitClosureSourceRowsOfGeneratedClosureMetricRowPackage
      (generatedClosureMetricRowPackageOfNonRoleDirectSourceMissingPackage P)

/-! ## Exact source-field equivalences -/

theorem generatedClosureMetricGate_iff_w20SourceFields :
    GeneratedClosureMetricGate <-> Nonempty W20SourceFields :=
  PachTothW23RouteAudit.rawSourceFields_iff_generatedClosureMetricRowPackage.symm

theorem generatedClosureMetricGate_iff_closureSource_and_reducedMetricFields :
    GeneratedClosureMetricGate <->
      Exists fun F : GeneratedChainFamily =>
        Nonempty (ClosureSource F) /\ Nonempty (ReducedMetricFields F) :=
  PachTothW23RouteAudit.nonempty_generatedClosureMetricRowPackage_iff_exists

theorem generatedClosureMetricGate_iff_minimalSourceFields :
    GeneratedClosureMetricGate <->
      MinimalGeneratedClosureMetricSourceFields :=
  GeneratedClosureMetricPackageInhabitationW25.nonempty_generatedClosureMetricRowPackage_iff_exists_closures_and_reducedMetricHypotheses

theorem generatedClosureMetricGate_iff_alternativeValueMatrixFamily :
    GeneratedClosureMetricGate <-> Nonempty AlternativeValueMatrixFamily :=
  GeneratedClosureMetricPackageInhabitationW25.nonempty_alternativeValueMatrixFamily_iff_generatedClosureMetricRowPackage
    |>.symm

theorem generatedClosureMetricGate_iff_w20ClosureReducedMetricSourceFields :
    GeneratedClosureMetricGate <->
      Nonempty W20ClosureReducedMetricSourceFields := by
  exact
    Iff.trans generatedClosureMetricGate_iff_alternativeValueMatrixFamily
      AlternativeValueMatrixInhabitationW25.nonempty_alternativeValueMatrixFamily_iff_w20ClosureReducedMetricSourceFields

theorem generatedClosureMetricGate_iff_nonRoleDirectSourceMissingPackage :
    GeneratedClosureMetricGate <->
      Nonempty NonRoleDirectSourceMissingPackage :=
  PachTothW24RouteAudit.nonempty_nonRoleDirectSourceMissingPackage_iff_generatedClosureMetricRowPackage
    |>.symm

theorem squaredOrbitClosureSourceRowsGate_of_generatedClosureMetricGate :
    GeneratedClosureMetricGate -> SquaredOrbitClosureSourceRowsGate :=
  CompletionRowsSourceW29.nonempty_squaredOrbitClosureSourceRows_of_generatedClosureMetricRowPackage

theorem squaredOrbitClosureSourceRowsGate_of_w20SourceFields :
    Nonempty W20SourceFields -> SquaredOrbitClosureSourceRowsGate := by
  intro h
  exact
    squaredOrbitClosureSourceRowsGate_of_generatedClosureMetricGate
      (generatedClosureMetricGate_iff_w20SourceFields.mpr h)

theorem squaredOrbitClosureSourceRowsGate_of_alternativeValueMatrixFamily :
    Nonempty AlternativeValueMatrixFamily ->
      SquaredOrbitClosureSourceRowsGate := by
  intro h
  exact
    squaredOrbitClosureSourceRowsGate_of_generatedClosureMetricGate
      (generatedClosureMetricGate_iff_alternativeValueMatrixFamily.mpr h)

theorem squaredOrbitClosureSourceRowsGate_of_nonRoleDirectSourceMissingPackage :
    Nonempty NonRoleDirectSourceMissingPackage ->
      SquaredOrbitClosureSourceRowsGate := by
  intro h
  exact
    squaredOrbitClosureSourceRowsGate_of_generatedClosureMetricGate
      (generatedClosureMetricGate_iff_nonRoleDirectSourceMissingPackage.mpr h)

/-! ## Exact-chain/non-role sources still need the generated metric fields -/

structure NonRoleSourceWithGeneratedClosureMetricRows where
  nonRole : AlternativeNonRoleSourcePackage
  rows : GeneratedClosureMetricRowPackage

structure PositiveChainSourceWithGeneratedClosureMetricRows where
  positive : PositiveChainComponentSource
  rows : GeneratedClosureMetricRowPackage

def nonRoleSourceWithGeneratedClosureMetricRows
    (S : AlternativeNonRoleSourcePackage)
    (P : GeneratedClosureMetricRowPackage) :
    NonRoleSourceWithGeneratedClosureMetricRows where
  nonRole := S
  rows := P

def positiveChainSourceWithGeneratedClosureMetricRows
    (S : PositiveChainComponentSource)
    (P : GeneratedClosureMetricRowPackage) :
    PositiveChainSourceWithGeneratedClosureMetricRows where
  positive := S
  rows := P

theorem nonempty_nonRoleSourceWithGeneratedClosureMetricRows_iff :
    Nonempty NonRoleSourceWithGeneratedClosureMetricRows <->
      Nonempty AlternativeNonRoleSourcePackage /\
        MinimalGeneratedClosureMetricSourceFields := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          And.intro
            (Nonempty.intro P.nonRole)
            (generatedClosureMetricGate_iff_minimalSourceFields.mp
              (Nonempty.intro P.rows))
  case mpr =>
    intro h
    cases h.1 with
    | intro S =>
        exact
          (generatedClosureMetricGate_iff_minimalSourceFields.mpr h.2).elim
            (fun P =>
              Nonempty.intro
                (nonRoleSourceWithGeneratedClosureMetricRows S P))

theorem nonempty_positiveChainSourceWithGeneratedClosureMetricRows_iff :
    Nonempty PositiveChainSourceWithGeneratedClosureMetricRows <->
      Nonempty PositiveChainComponentSource /\
        MinimalGeneratedClosureMetricSourceFields := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          And.intro
            (Nonempty.intro P.positive)
            (generatedClosureMetricGate_iff_minimalSourceFields.mp
              (Nonempty.intro P.rows))
  case mpr =>
    intro h
    cases h.1 with
    | intro S =>
        exact
          (generatedClosureMetricGate_iff_minimalSourceFields.mpr h.2).elim
            (fun P =>
              Nonempty.intro
                (positiveChainSourceWithGeneratedClosureMetricRows S P))

/-! ## Blocked finite-row/generated-closure wrappers -/

theorem not_roleHingedPeriodSearchGate :
    Not RoleHingedPeriodSearchGate :=
  FiniteRowsNoGoAuditW28.not_roleHingedPeriodSearchGate

theorem not_concreteValueMatrixRowGate :
    Not ConcreteValueMatrixRowGate :=
  FiniteRowsNoGoAuditW28.not_concreteValueMatrixRowGate

theorem not_concreteLowerTableGate :
    Not ConcreteLowerTableGate :=
  FiniteRowsNoGoAuditW28.not_concreteLowerTableGate

theorem not_concreteReducedMetricCertificateGate :
    Not ConcreteReducedMetricCertificateGate :=
  FiniteRowsNoGoAuditW28.not_concreteReducedMetricCertificateGate

theorem not_directFullMetricSourcePackageGate :
    Not DirectFullMetricSourcePackageGate :=
  FiniteRowsNoGoAuditW28.not_directFullMetricSourcePackageGate

theorem finiteRows_generatedClosureMetric_blocker :
    Not RoleHingedPeriodSearchGate /\
      Not ConcreteValueMatrixRowGate /\
        Not ConcreteLowerTableGate /\
          Not ConcreteReducedMetricCertificateGate /\
            Not DirectFullMetricSourcePackageGate /\
              (GeneratedClosureMetricGate <->
                MinimalGeneratedClosureMetricSourceFields) := by
  exact
    And.intro not_roleHingedPeriodSearchGate
      (And.intro not_concreteValueMatrixRowGate
        (And.intro not_concreteLowerTableGate
          (And.intro not_concreteReducedMetricCertificateGate
            (And.intro not_directFullMetricSourcePackageGate
              generatedClosureMetricGate_iff_minimalSourceFields))))

end

end GeneratedClosureMetricRowsW30
end PachToth

namespace Verified

abbrev PachTothW30GeneratedClosureMetricRowPackage : Type :=
  PachToth.GeneratedClosureMetricRowsW30.GeneratedClosureMetricRowPackage

abbrev PachTothW30SquaredOrbitClosureSourceRows : Type :=
  PachToth.GeneratedClosureMetricRowsW30.SquaredOrbitClosureSourceRows

abbrev PachTothW30MinimalGeneratedClosureMetricSourceFields : Prop :=
  PachToth.GeneratedClosureMetricRowsW30.MinimalGeneratedClosureMetricSourceFields

theorem pachtoth_w30_generatedClosureMetricGate_iff_minimalSourceFields :
    Nonempty PachTothW30GeneratedClosureMetricRowPackage <->
      PachTothW30MinimalGeneratedClosureMetricSourceFields :=
  PachToth.GeneratedClosureMetricRowsW30.generatedClosureMetricGate_iff_minimalSourceFields

theorem pachtoth_w30_sourceRows_of_generatedClosureMetricGate :
    Nonempty PachTothW30GeneratedClosureMetricRowPackage ->
      Nonempty PachTothW30SquaredOrbitClosureSourceRows :=
  PachToth.GeneratedClosureMetricRowsW30.squaredOrbitClosureSourceRowsGate_of_generatedClosureMetricGate

theorem pachtoth_w30_finiteRows_generatedClosureMetric_blocker :
    Not PachToth.GeneratedClosureMetricRowsW30.RoleHingedPeriodSearchGate /\
      Not PachToth.GeneratedClosureMetricRowsW30.ConcreteValueMatrixRowGate /\
        Not PachToth.GeneratedClosureMetricRowsW30.ConcreteLowerTableGate /\
          Not
            PachToth.GeneratedClosureMetricRowsW30.ConcreteReducedMetricCertificateGate /\
            Not
              PachToth.GeneratedClosureMetricRowsW30.DirectFullMetricSourcePackageGate /\
              (Nonempty PachTothW30GeneratedClosureMetricRowPackage <->
                PachTothW30MinimalGeneratedClosureMetricSourceFields) :=
  PachToth.GeneratedClosureMetricRowsW30.finiteRows_generatedClosureMetric_blocker

end Verified
end ErdosProblems1066
