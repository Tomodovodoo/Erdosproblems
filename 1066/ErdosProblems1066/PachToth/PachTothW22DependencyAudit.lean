import ErdosProblems1066.PachToth.ArbitraryNInputPackageRouteW21
import ErdosProblems1066.PachToth.ClosedPlacementKnownBoundsGateW21
import ErdosProblems1066.PachToth.ConcreteValueMatrixToInputPackageW21
import ErdosProblems1066.PachToth.NonConnectorTableInputPackageW21
import ErdosProblems1066.PachToth.ReducedMetricSourceFieldsW21
import ErdosProblems1066.PachToth.SourceFieldsAssemblyW21

set_option autoImplicit false

/-!
# W22 Pach-Toth dependency audit

This module is an audit layer only.  It does not construct an unconditional
Pach-Toth endpoint.  Instead it records the Lean-level equivalences between
the remaining W21/W22 source surfaces:

* the W19 explicit closed-placement input package,
* the raw W20 source-field package,
* the generated-family plus closure plus metric package,
* the reduced role-hinged metric remainder,
* and the final KnownBounds-shaped conditional gate.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW22DependencyAudit

noncomputable section

abbrev W19InputPackage : Type :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev RawSourceFields : Type :=
  GeneratedChainFamilyProducerW20.SourceFields

abbrev SourceBundle : Type :=
  ExplicitClosedPlacementInputPackageW20.GeneratedFamilyClosureReducedMetricSourceFields

abbrev GeneratedChainData : Type :=
  ClosedPlacementUnconditionalAttemptW20.GeneratedChainData

abbrev W20AvailableRouteData : Prop :=
  ClosedPlacementUnconditionalAttemptW20.W20AvailableRouteData

abbrev KnownBoundsGate : Prop :=
  ClosedPlacementKnownBoundsGateW21.KnownBoundsGate

abbrev KnownBoundsStatements : Prop :=
  ClosedPlacementKnownBoundsGateW21.KnownBoundsStatements

abbrev FinalConditionalGate : Prop :=
  Nonempty W19InputPackage

abbrev ExactBlockBound (k : Nat) : Prop :=
  ClosedPlacementKnownBoundsGateW21.ExactBlockBound k

abbrev ArbitraryBound (n : Nat) : Prop :=
  ClosedPlacementKnownBoundsGateW21.ArbitraryBound n

abbrev GeneratedChainFamily : Type :=
  ExplicitClosedPlacementInputPackageW20.GeneratedChainFamily

abbrev ClosureField (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementInputPackageW20.GeneratedChainFamilyClosures F

abbrev MetricField (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementInputPackageW20.ReducedMetricHypotheses F

abbrev ReducedMetricFields (F : GeneratedChainFamily) : Prop :=
  ReducedMetricHypothesesProducerW20.ReducedMetricFields F

abbrev ClosureSource (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.ClosureSource F

abbrev GeneratedPeriods (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.GeneratedChainFamilyPeriods F

abbrev PeriodEquations (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.FamilyPeriodEquations F

abbrev RoleHingedPeriodSearchFamily : Type :=
  ReducedMetricSourceFieldsW21.RoleHingedPeriodSearchFamily

abbrev RoleHingedGeneratedChainFamily
    (F : RoleHingedPeriodSearchFamily) : GeneratedChainFamily :=
  ReducedMetricSourceFieldsW21.roleHingedGeneratedChainFamily F

abbrev RemainingSeparationField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ReducedMetricSourceFieldsW21.RemainingSeparationField F

abbrev ProducedReducedMetricPackage : Type :=
  ReducedMetricHypothesesProducerW20.ProducedReducedMetricPackage

abbrev InputPackageOver
    (F : GeneratedChainFamily) (metric : MetricField F) : Prop :=
  ConcreteValueMatrixToInputPackageW21.InputPackageOver F metric

/-! ## Input package and source-field equivalences -/

def sourceBundleOfInputPackage
    (P : W19InputPackage) :
    SourceBundle where
  family := P.family
  closure := P.closure
  reducedMetric := P.metric

@[simp]
theorem sourceBundleOfInputPackage_toInputPackage
    (P : W19InputPackage) :
    (sourceBundleOfInputPackage P).toInputPackage = P := by
  cases P
  rfl

theorem nonempty_sourceBundle_iff_inputPackage :
    Nonempty SourceBundle <-> Nonempty W19InputPackage := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro S =>
            exact Nonempty.intro S.toInputPackage)
      (fun h => by
        cases h with
        | intro P =>
            exact Nonempty.intro (sourceBundleOfInputPackage P))

theorem nonempty_rawSourceFields_iff_inputPackage :
    Nonempty RawSourceFields <-> Nonempty W19InputPackage :=
  SourceFieldsAssemblyW21.nonempty_sourceFields_iff_inputPackage

theorem nonempty_inputPackage_iff_rawSourceFields :
    Nonempty W19InputPackage <-> Nonempty RawSourceFields :=
  nonempty_rawSourceFields_iff_inputPackage.symm

theorem nonempty_rawSourceFields_iff_generatedChainData :
    Nonempty RawSourceFields <-> Nonempty GeneratedChainData :=
  SourceFieldsAssemblyW21.nonempty_sourceFields_iff_generatedChainData

theorem nonempty_inputPackage_iff_generatedChainData :
    Nonempty W19InputPackage <-> Nonempty GeneratedChainData :=
  ClosedPlacementUnconditionalAttemptW20.nonempty_generatedChainData_iff_w19InputPackage.symm

theorem nonempty_sourceBundle_iff_rawSourceFields :
    Nonempty SourceBundle <-> Nonempty RawSourceFields :=
  Iff.trans nonempty_sourceBundle_iff_inputPackage
    nonempty_inputPackage_iff_rawSourceFields

theorem nonempty_sourceBundle_iff_generatedChainData :
    Nonempty SourceBundle <-> Nonempty GeneratedChainData :=
  Iff.trans nonempty_sourceBundle_iff_inputPackage
    nonempty_inputPackage_iff_generatedChainData

/-! ## Closure and metric remainders -/

structure SourceBundleOverFamily (F : GeneratedChainFamily) where
  closure : ClosureField F
  metric : MetricField F

namespace SourceBundleOverFamily

def toSourceBundle
    {F : GeneratedChainFamily}
    (S : SourceBundleOverFamily F) :
    SourceBundle where
  family := F
  closure := S.closure
  reducedMetric := S.metric

end SourceBundleOverFamily

def sourceBundleOverFamilyOfSourceBundle
    (S : SourceBundle) :
    SourceBundleOverFamily S.family where
  closure := S.closure
  metric := S.reducedMetric

theorem nonempty_sourceBundleOverFamily_iff_closure_metric
    (F : GeneratedChainFamily) :
    Nonempty (SourceBundleOverFamily F) <->
      ClosureField F /\ MetricField F := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro S =>
            exact And.intro S.closure S.metric)
      (fun h =>
        Nonempty.intro
          { closure := h.1
            metric := h.2 })

theorem nonempty_sourceBundle_iff_exists_family_closure_metric :
    Nonempty SourceBundle <->
      Exists fun F : GeneratedChainFamily =>
        ClosureField F /\ MetricField F := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro S =>
            exact
              Exists.intro S.family
                (And.intro S.closure S.reducedMetric))
      (fun h => by
        cases h with
        | intro F hfields =>
            exact
              Nonempty.intro
                { family := F
                  closure := hfields.1
                  reducedMetric := hfields.2 })

theorem closureField_iff_nonempty_closureSource
    (F : GeneratedChainFamily) :
    ClosureField F <-> Nonempty (ClosureSource F) := by
  exact
    Iff.intro
      (fun closure =>
        Nonempty.intro
          (GeneratedChainClosureProducerW20.ClosureSource.ofClosures
            closure))
      (fun h => by
        cases h with
        | intro source =>
            exact source.closure)

theorem closureField_of_generatedPeriods
    {F : GeneratedChainFamily}
    (periods : GeneratedPeriods F) :
    ClosureField F :=
  GeneratedChainClosureProducerW20.closuresOfGeneratedPeriods F periods

theorem closureField_of_periodEquations
    {F : GeneratedChainFamily}
    (periods : PeriodEquations F) :
    ClosureField F :=
  GeneratedChainClosureProducerW20.closuresOfPeriodEquations F periods

theorem metricField_iff_nonempty_reducedMetricFields
    (F : GeneratedChainFamily) :
    MetricField F <-> Nonempty (ReducedMetricFields F) := by
  exact
    Iff.intro
      (fun metric =>
        Nonempty.intro
          { separated := fun k hk => (metric.metric k hk).separated
            base_same_block_isometry := fun k hk =>
              (metric.metric k hk).base_same_block_isometry
            transition_preserves_same_block_distances := fun k hk =>
              (metric.metric k hk).transition_preserves_same_block_distances })
      (fun h => by
        cases h with
        | intro fields =>
            exact fields.toReducedMetricHypotheses)

theorem nonempty_sourceBundleOverFamily_iff_closure_reducedMetricFields
    (F : GeneratedChainFamily) :
    Nonempty (SourceBundleOverFamily F) <->
      ClosureField F /\ Nonempty (ReducedMetricFields F) := by
  exact
    Iff.intro
      (fun h => by
        have hfields :=
          (nonempty_sourceBundleOverFamily_iff_closure_metric F).1 h
        exact
          And.intro hfields.1
            ((metricField_iff_nonempty_reducedMetricFields F).1
              hfields.2))
      (fun h => by
        exact
          (nonempty_sourceBundleOverFamily_iff_closure_metric F).2
            (And.intro h.1
              ((metricField_iff_nonempty_reducedMetricFields F).2
                h.2)))

theorem roleHinged_metricField_iff_remainingSeparation
    (F : RoleHingedPeriodSearchFamily) :
    MetricField (RoleHingedGeneratedChainFamily F) <->
      RemainingSeparationField F := by
  exact
    Iff.intro
      (fun metric k hk =>
        (metric.metric k hk).separated)
      (fun separated =>
        (ReducedMetricSourceFieldsW21.fieldsOfSeparation F separated)
          |>.toReducedMetricHypotheses)

theorem roleHinged_sourceBundleOverFamily_iff_closure_remainingSeparation
    (F : RoleHingedPeriodSearchFamily) :
    Nonempty (SourceBundleOverFamily (RoleHingedGeneratedChainFamily F)) <->
      ClosureField (RoleHingedGeneratedChainFamily F) /\
        RemainingSeparationField F := by
  exact
    Iff.intro
      (fun h => by
        have hfields :=
          (nonempty_sourceBundleOverFamily_iff_closure_metric
            (RoleHingedGeneratedChainFamily F)).1 h
        exact
          And.intro hfields.1
            ((roleHinged_metricField_iff_remainingSeparation F).1
              hfields.2))
      (fun h => by
        exact
          (nonempty_sourceBundleOverFamily_iff_closure_metric
            (RoleHingedGeneratedChainFamily F)).2
            (And.intro h.1
              ((roleHinged_metricField_iff_remainingSeparation F).2
                h.2)))

theorem nonempty_inputPackageOver_iff_closure
    (F : GeneratedChainFamily) (metric : MetricField F) :
    Nonempty (InputPackageOver F metric) <-> ClosureField F :=
  ConcreteValueMatrixToInputPackageW21.nonempty_inputPackageOver_iff_closure
    F metric

theorem producedReducedMetricPackage_inputPackageOver_iff_closure
    (P : ProducedReducedMetricPackage) :
    Nonempty (InputPackageOver P.family P.metric) <-> ClosureField P.family :=
  ConcreteValueMatrixToInputPackageW21.producedReducedMetricPackage_nonempty_inputPackageOver_iff_closure
    P

/-! ## Final conditional gates -/

theorem knownBoundsGate_iff_sourceBundle :
    KnownBoundsGate <-> Nonempty SourceBundle :=
  Iff.rfl

theorem knownBoundsGate_iff_inputPackage :
    KnownBoundsGate <-> Nonempty W19InputPackage :=
  Iff.trans knownBoundsGate_iff_sourceBundle
    nonempty_sourceBundle_iff_inputPackage

theorem knownBoundsGate_iff_rawSourceFields :
    KnownBoundsGate <-> Nonempty RawSourceFields :=
  Iff.trans knownBoundsGate_iff_inputPackage
    nonempty_inputPackage_iff_rawSourceFields

theorem knownBoundsGate_iff_generatedChainData :
    KnownBoundsGate <-> Nonempty GeneratedChainData :=
  Iff.trans knownBoundsGate_iff_sourceBundle
    nonempty_sourceBundle_iff_generatedChainData

theorem finalConditionalGate_iff_knownBoundsGate :
    FinalConditionalGate <-> KnownBoundsGate :=
  knownBoundsGate_iff_inputPackage.symm

theorem w20AvailableRouteData_iff_knownBoundsGate :
    W20AvailableRouteData <-> KnownBoundsGate :=
  Iff.trans
    ClosedPlacementUnconditionalAttemptW20.w20AvailableRouteData_iff_generatedChainData
    knownBoundsGate_iff_generatedChainData.symm

theorem knownBoundsStatements_of_finalConditionalGate
    (G : FinalConditionalGate) :
    KnownBoundsStatements :=
  ClosedPlacementKnownBoundsGateW21.knownBoundsStatements_of_knownBoundsGate
    (finalConditionalGate_iff_knownBoundsGate.1 G)

theorem exactBound_of_finalConditionalGate
    (G : FinalConditionalGate) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  (knownBoundsStatements_of_finalConditionalGate G).exact k hk

theorem arbitraryBound_of_finalConditionalGate
    (G : FinalConditionalGate) (n : Nat) :
    ArbitraryBound n :=
  (knownBoundsStatements_of_finalConditionalGate G).arbitrary n

end

end PachTothW22DependencyAudit
end PachToth

namespace Verified

abbrev PachTothW22RemainingInputPackage : Type :=
  PachToth.PachTothW22DependencyAudit.W19InputPackage

abbrev PachTothW22RawSourceFields : Type :=
  PachToth.PachTothW22DependencyAudit.RawSourceFields

abbrev PachTothW22SourceBundle : Type :=
  PachToth.PachTothW22DependencyAudit.SourceBundle

abbrev PachTothW22KnownBoundsGate : Prop :=
  PachToth.PachTothW22DependencyAudit.KnownBoundsGate

theorem pachtoth_w22_knownBoundsGate_iff_remainingInputPackage :
    PachTothW22KnownBoundsGate <->
      Nonempty PachTothW22RemainingInputPackage :=
  PachToth.PachTothW22DependencyAudit.knownBoundsGate_iff_inputPackage

theorem pachtoth_w22_knownBoundsGate_iff_rawSourceFields :
    PachTothW22KnownBoundsGate <->
      Nonempty PachTothW22RawSourceFields :=
  PachToth.PachTothW22DependencyAudit.knownBoundsGate_iff_rawSourceFields

theorem pachtoth_w22_knownBoundsGate_iff_sourceBundle :
    PachTothW22KnownBoundsGate <->
      Nonempty PachTothW22SourceBundle :=
  PachToth.PachTothW22DependencyAudit.knownBoundsGate_iff_sourceBundle

end Verified
end ErdosProblems1066
