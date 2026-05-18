import ErdosProblems1066.PachToth.PachTothW22DependencyAudit
import ErdosProblems1066.PachToth.GeneratedChainSourceFieldsInhabitationW22
import ErdosProblems1066.PachToth.GeneratedChainClosureInhabitationW22
import ErdosProblems1066.PachToth.ConcreteValueMatrixFamilyInhabitationW22
import ErdosProblems1066.PachToth.ConcreteCrossBlockInputPackageW22
import ErdosProblems1066.PachToth.SmallComplementClosureW22
import ErdosProblems1066.PachToth.PeriodEquationSourceFieldsW22
import ErdosProblems1066.PachToth.RemainingSeparationInhabitationW22
import ErdosProblems1066.PachToth.ExactBaseFullMetricSourceInhabitationW22

set_option autoImplicit false

/-!
# W23 Pach-Toth route audit

This module is an audit layer only.  It consolidates the W22 Pach-Toth route
into the smallest checked source-package statements currently available.

The main W24-facing conclusion is that the KnownBounds-shaped final gate is
equivalent to an inhabited generated-chain row package: one generated family,
a closure source for that same family, and reduced metric fields for that same
family.  Concrete value-matrix row packages and small-complement rows are then
recorded as exact row-level route gates or conditional sufficient routes.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW23RouteAudit

noncomputable section

/-! ## W22 final gates and source surfaces -/

abbrev KnownBoundsGate : Prop :=
  PachTothW22DependencyAudit.KnownBoundsGate

abbrev KnownBoundsStatements : Prop :=
  PachTothW22DependencyAudit.KnownBoundsStatements

abbrev FinalConditionalGate : Prop :=
  PachTothW22DependencyAudit.FinalConditionalGate

abbrev W19InputPackage : Type :=
  PachTothW22DependencyAudit.W19InputPackage

abbrev RawSourceFields : Type :=
  PachTothW22DependencyAudit.RawSourceFields

abbrev SourceBundle : Type :=
  PachTothW22DependencyAudit.SourceBundle

abbrev GeneratedChainData : Type :=
  PachTothW22DependencyAudit.GeneratedChainData

abbrev ExactBlockBound (k : Nat) : Prop :=
  PachTothW22DependencyAudit.ExactBlockBound k

abbrev ArbitraryBound (n : Nat) : Prop :=
  PachTothW22DependencyAudit.ArbitraryBound n

theorem knownBoundsGate_iff_inputPackage :
    KnownBoundsGate <-> Nonempty W19InputPackage :=
  PachTothW22DependencyAudit.knownBoundsGate_iff_inputPackage

theorem knownBoundsGate_iff_rawSourceFields :
    KnownBoundsGate <-> Nonempty RawSourceFields :=
  PachTothW22DependencyAudit.knownBoundsGate_iff_rawSourceFields

theorem knownBoundsGate_iff_sourceBundle :
    KnownBoundsGate <-> Nonempty SourceBundle :=
  PachTothW22DependencyAudit.knownBoundsGate_iff_sourceBundle

theorem knownBoundsGate_iff_generatedChainData :
    KnownBoundsGate <-> Nonempty GeneratedChainData :=
  PachTothW22DependencyAudit.knownBoundsGate_iff_generatedChainData

theorem finalConditionalGate_iff_knownBoundsGate :
    FinalConditionalGate <-> KnownBoundsGate :=
  PachTothW22DependencyAudit.finalConditionalGate_iff_knownBoundsGate

/-! ## Minimal generated-chain row package -/

abbrev GeneratedChainFamily : Type :=
  GeneratedChainSourceFieldsInhabitationW22.GeneratedChainFamily

abbrev ClosureSource (F : GeneratedChainFamily) :=
  GeneratedChainSourceFieldsInhabitationW22.ClosureSource F

abbrev ReducedMetricFields (F : GeneratedChainFamily) :=
  GeneratedChainSourceFieldsInhabitationW22.ReducedMetricFields F

/-- The W23 minimal live package: same-family closure source plus reduced
metric fields for one generated-chain family. -/
structure GeneratedClosureMetricRowPackage where
  family : GeneratedChainFamily
  closureSource : ClosureSource family
  reducedMetric : ReducedMetricFields family

namespace GeneratedClosureMetricRowPackage

def toRawSourceFields
    (P : GeneratedClosureMetricRowPackage) :
    RawSourceFields :=
  GeneratedChainSourceFieldsInhabitationW22.sourceFieldsOfClosureSourceAndReducedMetricFields
    P.closureSource P.reducedMetric

def toInputPackage
    (P : GeneratedClosureMetricRowPackage) :
    W19InputPackage :=
  P.toRawSourceFields.toInputPackage

theorem knownBoundsGate
    (P : GeneratedClosureMetricRowPackage) :
    KnownBoundsGate :=
  knownBoundsGate_iff_inputPackage.2 (Nonempty.intro P.toInputPackage)

theorem knownBoundsStatements
    (P : GeneratedClosureMetricRowPackage) :
    KnownBoundsStatements :=
  ClosedPlacementKnownBoundsGateW21.knownBoundsStatements_of_knownBoundsGate
    P.knownBoundsGate

theorem exactBound
    (P : GeneratedClosureMetricRowPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  P.knownBoundsStatements.exact k hk

theorem arbitraryBound
    (P : GeneratedClosureMetricRowPackage) (n : Nat) :
    ArbitraryBound n :=
  P.knownBoundsStatements.arbitrary n

end GeneratedClosureMetricRowPackage

def generatedClosureMetricRowPackageOfRawSourceFields
    (S : RawSourceFields) :
    GeneratedClosureMetricRowPackage where
  family := S.family
  closureSource :=
    GeneratedChainSourceFieldsInhabitationW22.closureSourceOfSourceFields S
  reducedMetric :=
    GeneratedChainSourceFieldsInhabitationW22.reducedMetricFieldsOfSourceFields
      S

def generatedClosureMetricRowPackageOfInputPackage
    (P : W19InputPackage) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfRawSourceFields
    (GeneratedChainSourceFieldsInhabitationW22.sourceFieldsOfInputPackage P)

theorem nonempty_generatedClosureMetricRowPackage_iff_exists :
    Nonempty GeneratedClosureMetricRowPackage <->
      Exists fun F : GeneratedChainFamily =>
        Nonempty (ClosureSource F) /\ Nonempty (ReducedMetricFields F) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro P.family
            (And.intro
              (Nonempty.intro P.closureSource)
              (Nonempty.intro P.reducedMetric))
  case mpr =>
    intro h
    cases h with
    | intro F hF =>
        cases hF.1 with
        | intro closure =>
            cases hF.2 with
            | intro metric =>
                exact
                  Nonempty.intro
                    { family := F
                      closureSource := closure
                      reducedMetric := metric }

theorem rawSourceFields_iff_generatedClosureMetricRowPackage :
    Nonempty RawSourceFields <-> Nonempty GeneratedClosureMetricRowPackage :=
  Iff.trans
    GeneratedChainSourceFieldsInhabitationW22.nonempty_sourceFields_iff_closureSource_and_reducedMetricFields
    nonempty_generatedClosureMetricRowPackage_iff_exists.symm

theorem knownBoundsGate_iff_generatedClosureMetricRowPackage :
    KnownBoundsGate <-> Nonempty GeneratedClosureMetricRowPackage :=
  Iff.trans knownBoundsGate_iff_rawSourceFields
    rawSourceFields_iff_generatedClosureMetricRowPackage

/-! ## Same package in closure-source plus reduced-hypothesis spelling -/

abbrev ClosureReducedMetricHypotheses (F : GeneratedChainFamily) :=
  GeneratedChainClosureInhabitationW22.ReducedMetricHypotheses F

abbrev ClosureReducedMetricSource (F : GeneratedChainFamily) :=
  GeneratedChainClosureInhabitationW22.ClosureSource F

/-- Equivalent W22 spelling of the same live package, after the reduced metric
fields have already been assembled into reduced metric hypotheses. -/
structure ClosureReducedMetricRowPackage where
  family : GeneratedChainFamily
  closureSource : ClosureReducedMetricSource family
  reducedMetric : ClosureReducedMetricHypotheses family

namespace ClosureReducedMetricRowPackage

def toInputPackage
    (P : ClosureReducedMetricRowPackage) :
    W19InputPackage :=
  GeneratedChainClosureInhabitationW22.inputPackageOfClosureSourceReducedMetric
    P.closureSource P.reducedMetric

theorem knownBoundsGate
    (P : ClosureReducedMetricRowPackage) :
    KnownBoundsGate :=
  knownBoundsGate_iff_inputPackage.2 (Nonempty.intro P.toInputPackage)

end ClosureReducedMetricRowPackage

theorem nonempty_closureReducedMetricRowPackage_iff_exists :
    Nonempty ClosureReducedMetricRowPackage <->
      Exists fun F : GeneratedChainFamily =>
        ClosureReducedMetricSource F /\
          ClosureReducedMetricHypotheses F := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Exists.intro P.family
          (And.intro P.closureSource P.reducedMetric)
  case mpr =>
    intro h
    cases h with
    | intro F hF =>
        exact
          Nonempty.intro
            { family := F
              closureSource := hF.1
              reducedMetric := hF.2 }

theorem knownBoundsGate_iff_closureReducedMetricRowPackage :
    KnownBoundsGate <-> Nonempty ClosureReducedMetricRowPackage :=
  Iff.trans knownBoundsGate_iff_inputPackage
    (Iff.trans
      GeneratedChainClosureInhabitationW22.nonempty_inputPackage_iff_exists_closureSource_reducedMetric
      nonempty_closureReducedMetricRowPackage_iff_exists.symm)

/-! ## Concrete value-matrix row packages -/

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixFamily

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage

abbrev CandidateValueMatrixFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.CandidateValueMatrixFamily

abbrev CandidateValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.CandidateValueMatrixRowPackage

abbrev ConcreteValueMatrixRouteGate : Prop :=
  Nonempty ConcreteValueMatrixFamily

abbrev CandidateValueMatrixRouteGate : Prop :=
  Nonempty CandidateValueMatrixFamily

theorem concreteValueMatrixRouteGate_iff_rowPackage :
    ConcreteValueMatrixRouteGate <-> Nonempty ConcreteValueMatrixRowPackage :=
  ConcreteValueMatrixFamilyInhabitationW22.nonempty_concreteValueMatrixFamily_iff_rowPackage

theorem candidateValueMatrixRouteGate_iff_rowPackage :
    CandidateValueMatrixRouteGate <-> Nonempty CandidateValueMatrixRowPackage :=
  ConcreteValueMatrixFamilyInhabitationW22.nonempty_candidateValueMatrixFamily_iff_rowPackage

theorem knownBoundsGate_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    KnownBoundsGate :=
  knownBoundsGate_iff_inputPackage.2
    (Nonempty.intro
      (ConcreteValueMatrixToInputPackageW21.inputPackageOfConcreteValueMatrixFamily
        C))

theorem knownBoundsGate_of_concreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    KnownBoundsGate :=
  knownBoundsGate_of_concreteValueMatrixFamily P.toConcreteValueMatrixFamily

theorem knownBoundsGate_of_concreteValueMatrixRouteGate
    (G : ConcreteValueMatrixRouteGate) :
    KnownBoundsGate := by
  cases G with
  | intro C =>
      exact knownBoundsGate_of_concreteValueMatrixFamily C

/-! ## Small-complement row packages for the thresholded route -/

abbrev ExactTarget : Prop :=
  SmallComplementClosureW22.ExactTarget

abbrev EventualTarget : Prop :=
  SmallComplementClosureW22.EventualTarget

abbrev ArbitraryTarget : Prop :=
  SmallComplementClosureW22.ArbitraryTarget

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  SmallComplementClosureW22.LargeClosedPlacementFields K0

abbrev SmallLengthExactBlockTargets : Prop :=
  SmallComplementClosureW22.SmallLengthExactBlockTargets

abbrev blockThresholdSix : Nat :=
  SmallComplementClosureW22.blockThresholdSix

abbrev ExactBlockTargetsBelowThreshold (K0 : Nat) : Prop :=
  SmallComplementClosureW22.ExactBlockTargetsBelowThreshold K0

abbrev ExactChainTargetsBelowThreshold (K0 : Nat) : Type :=
  SmallComplementClosureW22.ExactChainTargetsBelowThreshold K0

theorem arbitraryTarget_iff_exactBlockTargetsBelowThreshold
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    ArbitraryTarget <-> ExactBlockTargetsBelowThreshold K0 :=
  SmallComplementClosureW22.arbitraryTarget_iff_exactBlockTargetsBelowThreshold_of_largeClosedPlacementFields
    L

theorem exact_eventual_arbitrary_iff_exactBlockTargetsBelowThreshold
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    (ExactTarget /\ EventualTarget /\ ArbitraryTarget) <->
      ExactBlockTargetsBelowThreshold K0 :=
  SmallComplementClosureW22.exact_eventual_arbitrary_iff_exactBlockTargetsBelowThreshold_of_largeClosedPlacementFields
    L

theorem arbitraryTarget_iff_smallLengthExactBlockTargets_six
    (L : LargeClosedPlacementFields blockThresholdSix) :
    ArbitraryTarget <-> Nonempty SmallLengthExactBlockTargets :=
  SmallComplementClosureW22.arbitraryTarget_iff_nonempty_smallLengthExactBlockTargets_of_largeClosedPlacementFields_six
    L

theorem exact_eventual_arbitrary_iff_smallLengthExactBlockTargets_six
    (L : LargeClosedPlacementFields blockThresholdSix) :
    (ExactTarget /\ EventualTarget /\ ArbitraryTarget) <->
      Nonempty SmallLengthExactBlockTargets :=
  SmallComplementClosureW22.exact_eventual_arbitrary_iff_nonempty_smallLengthExactBlockTargets_of_largeClosedPlacementFields_six
    L

/-! ## Reduced non-connector separation rows -/

abbrev RoleHingedPeriodSearchFamily : Type :=
  RemainingSeparationInhabitationW22.RoleHingedPeriodSearchFamily

abbrev RemainingSeparationField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  RemainingSeparationInhabitationW22.RemainingSeparationField F

abbrev RemainingReducedMetricFields
    (F : RoleHingedPeriodSearchFamily) :=
  RemainingSeparationInhabitationW22.ReducedMetricFields F

abbrev CrossBlockLowerBounds
    (F : RoleHingedPeriodSearchFamily) :=
  RemainingSeparationInhabitationW22.CrossBlockLowerBounds F

abbrev IndexedCrossBlockLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  RemainingSeparationInhabitationW22.IndexedCrossBlockLowerTableFamily F

abbrev W19GeneratedSeparationRows
    (F : RoleHingedPeriodSearchFamily) :=
  RemainingSeparationInhabitationW22.W19GeneratedSeparationRows F

theorem remainingSeparation_iff_reducedMetricFields
    (F : RoleHingedPeriodSearchFamily) :
    RemainingSeparationField F <->
      Nonempty (RemainingReducedMetricFields F) :=
  RemainingSeparationInhabitationW22.remainingSeparation_iff_nonempty_reducedMetricFields
    F

theorem remainingSeparation_iff_w19Rows
    (F : RoleHingedPeriodSearchFamily) :
    RemainingSeparationField F <->
      Nonempty (W19GeneratedSeparationRows F) :=
  (RemainingSeparationInhabitationW22.nonempty_w19Rows_iff_remainingSeparation
    F).symm

theorem remainingSeparation_iff_crossBlockLowerBounds
    (F : RoleHingedPeriodSearchFamily) :
    RemainingSeparationField F <->
      Nonempty (CrossBlockLowerBounds F) :=
  (RemainingSeparationInhabitationW22.nonempty_crossBlockLowerBounds_iff_remainingSeparation
    F).symm

theorem remainingSeparation_iff_indexedCrossBlockLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) :
    RemainingSeparationField F <->
      Nonempty (IndexedCrossBlockLowerTableFamily F) :=
  (RemainingSeparationInhabitationW22.nonempty_indexedCrossBlockLowerTableFamily_iff_remainingSeparation
    F).symm

/-! ## W22-blocked role-hinge/base-fixing surfaces -/

abbrev RoleHingeTransitions : Type :=
  PeriodEquationSourceFieldsW22.RoleHingeTransitions

abbrev RoleHingeSourceFields (T : RoleHingeTransitions) :=
  PeriodEquationSourceFieldsW22.RoleHingeSourceFields T

abbrev BaseFixingAlternative (T : RoleHingeTransitions) : Prop :=
  PeriodEquationSourceFieldsW22.BaseFixingAlternative T

theorem roleHingeSourceFields_iff_baseFixingAlternative
    (T : RoleHingeTransitions) :
    Nonempty (RoleHingeSourceFields T) <-> BaseFixingAlternative T :=
  PeriodEquationSourceFieldsW22.sourceFields_iff_baseFixingAlternative T

theorem no_roleHingePeriodEquationRows :
    Not (Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T)) :=
  PeriodEquationSourceFieldsW22.not_exists_roleHingeSourceFields

theorem no_roleHingedPeriodSearchFamily :
    Not (Nonempty RoleHingedPeriodSearchFamily) :=
  RemainingSeparationInhabitationW22.not_nonempty_roleHingedPeriodSearchFamily

/-! ## Exact-base full-metric source spelling -/

abbrev ExactBaseFullMetricSourceFields : Type :=
  ExactBaseFullMetricSourceInhabitationW22.ExactBaseFullMetricSourceFields

abbrev ExactBaseFullMetricCoreFields : Type :=
  ExactBaseFullMetricSourceInhabitationW22.ExactBaseFullMetricCoreFields

abbrev ExactBaseRemainingSeparationField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  ExactBaseFullMetricSourceInhabitationW22.RemainingSeparationField C

abbrev ExactBaseRemainingSameBlockField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  ExactBaseFullMetricSourceInhabitationW22.RemainingSameBlockField C

abbrev ConnectorExactBaseFullMetricSourceFields : Type :=
  ExactBaseFullMetricSourceInhabitationW22.ConnectorExactBaseFullMetricSourceFields

abbrev ConnectorExactBaseFullMetricCoreFields : Type :=
  ExactBaseFullMetricSourceInhabitationW22.ConnectorExactBaseFullMetricCoreFields

abbrev ConnectorRemainingSeparationField
    (C : ConnectorExactBaseFullMetricCoreFields) : Prop :=
  ExactBaseFullMetricSourceInhabitationW22.ConnectorRemainingSeparationField C

abbrev ConnectorRemainingSameBlockField
    (C : ConnectorExactBaseFullMetricCoreFields) : Prop :=
  ExactBaseFullMetricSourceInhabitationW22.ConnectorRemainingSameBlockField C

theorem exactBaseFullMetricSourceFields_iff_metricParts :
    Nonempty ExactBaseFullMetricSourceFields <->
      Exists fun C : ExactBaseFullMetricCoreFields =>
        ExactBaseRemainingSeparationField C /\
          ExactBaseRemainingSameBlockField C :=
  ExactBaseFullMetricSourceInhabitationW22.nonempty_exactBaseFullMetricSourceFields_iff_parts

theorem connectorExactBaseFullMetricSourceFields_iff_metricParts :
    Nonempty ConnectorExactBaseFullMetricSourceFields <->
      Exists fun C : ConnectorExactBaseFullMetricCoreFields =>
        ConnectorRemainingSeparationField C /\
          ConnectorRemainingSameBlockField C :=
  ExactBaseFullMetricSourceInhabitationW22.nonempty_connectorExactBaseFullMetricSourceFields_iff_parts

end

end PachTothW23RouteAudit
end PachToth

namespace Verified

abbrev PachTothW23KnownBoundsGate : Prop :=
  PachToth.PachTothW23RouteAudit.KnownBoundsGate

abbrev PachTothW23GeneratedClosureMetricRowPackage : Type :=
  PachToth.PachTothW23RouteAudit.GeneratedClosureMetricRowPackage

abbrev PachTothW23RouteConcreteValueMatrixRowPackage : Type :=
  PachToth.PachTothW23RouteAudit.ConcreteValueMatrixRowPackage

theorem pachtoth_w23_knownBoundsGate_iff_generatedClosureMetricRowPackage :
    PachTothW23KnownBoundsGate <->
      Nonempty PachTothW23GeneratedClosureMetricRowPackage :=
  PachToth.PachTothW23RouteAudit.knownBoundsGate_iff_generatedClosureMetricRowPackage

theorem pachtoth_w23_knownBoundsGate_of_generatedClosureMetricRowPackage
    (P : PachTothW23GeneratedClosureMetricRowPackage) :
    PachTothW23KnownBoundsGate :=
  P.knownBoundsGate

theorem pachtoth_w23_knownBoundsGate_of_concreteValueMatrixRowPackage
    (P : PachTothW23RouteConcreteValueMatrixRowPackage) :
    PachTothW23KnownBoundsGate :=
  PachToth.PachTothW23RouteAudit.knownBoundsGate_of_concreteValueMatrixRowPackage
    P

end Verified
end ErdosProblems1066
