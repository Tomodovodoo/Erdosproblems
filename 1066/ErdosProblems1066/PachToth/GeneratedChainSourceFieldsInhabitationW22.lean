import ErdosProblems1066.PachToth.PeriodClosureSourceW21
import ErdosProblems1066.PachToth.ReducedMetricSourceFieldsW21
import ErdosProblems1066.PachToth.ConcreteValueMatrixToInputPackageW21
import ErdosProblems1066.PachToth.NonConnectorTableInputPackageW21
import ErdosProblems1066.PachToth.SourceFieldsAssemblyW21

set_option autoImplicit false

/-!
# W22 generated-chain source-field inhabitation

This file gives the direct constructor into
`GeneratedChainFamilyProducerW20.SourceFields`.  The exact remaining
same-family data is a closure source and reduced-metric source; concrete
value-matrix packages already provide both.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedChainSourceFieldsInhabitationW22

open FiniteGraph

noncomputable section

abbrev SourceFields : Type :=
  GeneratedChainFamilyProducerW20.SourceFields

abbrev InputPackage : Type :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev GeneratedChainFamily : Type :=
  GeneratedChainFamilyProducerW20.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainFamilyProducerW20.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainFamilyProducerW20.ReducedMetricHypotheses F

abbrev ClosureSource
    (F : GeneratedChainFamily) :=
  GeneratedChainClosureProducerW20.ClosureSource F

abbrev ReducedMetricFields
    (F : GeneratedChainFamily) :=
  ReducedMetricHypothesesProducerW20.ReducedMetricFields F

abbrev RoleHingedPeriodSearchFamily : Type :=
  NonConnectorTableInputPackageW21.RoleHingedPeriodSearchFamily

abbrev GeneratedNonConnectorSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  NonConnectorTableInputPackageW21.GeneratedNonConnectorSqDistanceTableFamily F

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  NonConnectorTableInputPackageW21.IndexedNonConnectorCrossBlockSqDistanceTableFamily F

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev NonConnectorValueMatrixFamily
    (F : RoleHingedPeriodSearchFamily) : Type :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily F

/-- Flatten a W19 input package to the raw W20 generated-chain source fields. -/
def sourceFieldsOfInputPackage
    (P : InputPackage) :
    SourceFields where
  O := P.family.O
  base := P.family.base
  orientation := P.family.orientation
  closure := P.closure
  separated := fun k hk => (P.metric.metric k hk).separated
  base_same_block_isometry := fun k hk =>
    (P.metric.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances := fun k hk =>
    (P.metric.metric k hk).transition_preserves_same_block_distances

/-- Direct constructor from the exact same-family closure and metric targets. -/
def sourceFieldsOfClosuresAndReducedMetric
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (metric : ReducedMetricHypotheses F) :
    SourceFields where
  O := F.O
  base := F.base
  orientation := F.orientation
  closure := closure
  separated := fun k hk => (metric.metric k hk).separated
  base_same_block_isometry := fun k hk =>
    (metric.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances := fun k hk =>
    (metric.metric k hk).transition_preserves_same_block_distances

@[simp]
theorem sourceFieldsOfClosuresAndReducedMetric_family
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (metric : ReducedMetricHypotheses F) :
    (sourceFieldsOfClosuresAndReducedMetric F closure metric).family = F := by
  cases F
  rfl

/-- Direct constructor from the W20/W21 closure-source wrapper plus metrics. -/
def sourceFieldsOfClosureSourceAndReducedMetric
    {F : GeneratedChainFamily}
    (closure : ClosureSource F)
    (metric : ReducedMetricHypotheses F) :
    SourceFields :=
  sourceFieldsOfClosuresAndReducedMetric F
    closure.toGeneratedChainFamilyClosures metric

/-- Direct constructor from W21 closure-source and reduced-metric fields. -/
def sourceFieldsOfClosureSourceAndReducedMetricFields
    {F : GeneratedChainFamily}
    (closure : ClosureSource F)
    (metric : ReducedMetricFields F) :
    SourceFields :=
  sourceFieldsOfClosureSourceAndReducedMetric closure
    metric.toReducedMetricHypotheses

@[simp]
theorem sourceFieldsOfClosureSourceAndReducedMetricFields_family
    {F : GeneratedChainFamily}
    (closure : ClosureSource F)
    (metric : ReducedMetricFields F) :
    (sourceFieldsOfClosureSourceAndReducedMetricFields closure metric).family =
      F := by
  simp [sourceFieldsOfClosureSourceAndReducedMetricFields,
    sourceFieldsOfClosureSourceAndReducedMetric]

/-- Source fields determine their own closure source. -/
def closureSourceOfSourceFields
    (S : SourceFields) :
    ClosureSource S.family :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures S.closures

/-- Source fields determine their own reduced-metric source fields. -/
def reducedMetricFieldsOfSourceFields
    (S : SourceFields) :
    ReducedMetricFields S.family where
  separated := S.separated
  base_same_block_isometry := S.base_same_block_isometry
  transition_preserves_same_block_distances :=
    S.transition_preserves_same_block_distances

/-- Exact fixed-family criterion: a source-field row with family `F` is
equivalent to a closure source and reduced-metric fields for that same `F`. -/
theorem exists_sourceFields_with_family_iff_closureSource_and_reducedMetricFields
    (F : GeneratedChainFamily) :
    (Exists fun S : SourceFields => S.family = F) <->
      Nonempty (ClosureSource F) /\ Nonempty (ReducedMetricFields F) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S hfamily =>
        cases hfamily
        exact
          And.intro
            (Nonempty.intro (closureSourceOfSourceFields S))
            (Nonempty.intro (reducedMetricFieldsOfSourceFields S))
  case mpr =>
    intro h
    cases h.1 with
    | intro closure =>
        cases h.2 with
        | intro metric =>
            exact
              Exists.intro
                (sourceFieldsOfClosureSourceAndReducedMetricFields
                  closure metric)
                (sourceFieldsOfClosureSourceAndReducedMetricFields_family
                  closure metric)

/-- Unindexed inhabitation form of the same exact conjunction. -/
theorem nonempty_sourceFields_iff_closureSource_and_reducedMetricFields :
    Nonempty SourceFields <->
      Exists fun F : GeneratedChainFamily =>
        Nonempty (ClosureSource F) /\ Nonempty (ReducedMetricFields F) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.family
            (And.intro
              (Nonempty.intro (closureSourceOfSourceFields S))
              (Nonempty.intro (reducedMetricFieldsOfSourceFields S)))
  case mpr =>
    intro h
    cases h with
    | intro F hF =>
        exact
          Nonempty.intro
            ((exists_sourceFields_with_family_iff_closureSource_and_reducedMetricFields
                F).2 hF).choose

/-- The equivalent target-level conjunction, without the source wrappers. -/
theorem nonempty_sourceFields_iff_closures_and_reducedMetricHypotheses :
    Nonempty SourceFields <->
      Exists fun F : GeneratedChainFamily =>
        GeneratedChainFamilyClosures F /\ ReducedMetricHypotheses F := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Exists.intro S.family (And.intro S.closures S.reducedMetric)
  case mpr =>
    intro h
    cases h with
    | intro F hF =>
        exact
          Nonempty.intro
            (sourceFieldsOfClosuresAndReducedMetric F hF.1 hF.2)

/-- W21 input-package equivalence, now with the actual constructor named. -/
theorem nonempty_sourceFields_iff_inputPackage :
    Nonempty SourceFields <-> Nonempty InputPackage := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro S =>
            exact Nonempty.intro S.toInputPackage)
      (fun h => by
        cases h with
        | intro P =>
            exact Nonempty.intro (sourceFieldsOfInputPackage P))

/-- Generated non-connector tables plus a same-family closure source construct
the raw W20 source fields. -/
def sourceFieldsOfGeneratedTableFamilyAndClosureSource
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F)
    (closure :
      ClosureSource (NonConnectorTableInputPackageW21.generatedChainFamily F)) :
    SourceFields :=
  sourceFieldsOfClosureSourceAndReducedMetric closure
    (NonConnectorTableInputPackageW21.reducedMetricOfGeneratedTableFamily T)

/-- Same generated-table constructor, spelled through the W21 period-closure
and reduced-metric source modules. -/
def sourceFieldsOfGeneratedTableFamilyAndPeriodClosureSource
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F)
    (closure :
      PeriodClosureSourceW21.ClosureSource
        (ReducedMetricSourceFieldsW21.roleHingedGeneratedChainFamily F)) :
    SourceFields :=
  sourceFieldsOfClosureSourceAndReducedMetricFields closure
    (ReducedMetricSourceFieldsW21.fieldsOfGeneratedNonConnectorSqDistanceTableFamily
      T)

/-- Indexed non-connector tables use the same closure-source requirement. -/
def sourceFieldsOfIndexedTableFamilyAndClosureSource
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (closure :
      ClosureSource (NonConnectorTableInputPackageW21.generatedChainFamily F)) :
    SourceFields :=
  sourceFieldsOfClosureSourceAndReducedMetric closure
    (NonConnectorTableInputPackageW21.reducedMetricOfIndexedTableFamily T)

/-- Indexed-table constructor through the W21 period-closure and
reduced-metric source modules. -/
def sourceFieldsOfIndexedTableFamilyAndPeriodClosureSource
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (closure :
      PeriodClosureSourceW21.ClosureSource
        (ReducedMetricSourceFieldsW21.roleHingedGeneratedChainFamily F)) :
    SourceFields :=
  sourceFieldsOfClosureSourceAndReducedMetricFields closure
    (ReducedMetricSourceFieldsW21.fieldsOfIndexedNonConnectorCrossBlockSqDistanceTableFamily
      T)

/-- Value-matrix families without their concrete period-search package still
need exactly the same-family closure source. -/
def sourceFieldsOfValueMatrixFamilyAndClosureSource
    {F : RoleHingedPeriodSearchFamily}
    (M : NonConnectorValueMatrixFamily F)
    (closure :
      ClosureSource (NonConnectorTableInputPackageW21.generatedChainFamily F)) :
    SourceFields :=
  sourceFieldsOfClosureSourceAndReducedMetric closure
    (ReducedMetricHypothesesProducerW20.ofGeneratedNonConnectorSqDistanceTableFamily
      (NonConnectorInstantiationW13.generatedTableFamilyOfValueMatrixFamily M))

/-- Concrete value-matrix packages already carry the period-search closure
source and table reduced metrics, so they construct raw W20 source fields. -/
def sourceFieldsOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    SourceFields :=
  sourceFieldsOfClosuresAndReducedMetric
    (ConcreteValueMatrixToInputPackageW21.generatedChainFamilyOfConcreteValueMatrixFamily
      C)
    (ConcreteValueMatrixToInputPackageW21.generatedChainFamilyClosuresOfConcreteValueMatrixFamily
      C)
    (ConcreteValueMatrixToInputPackageW21.reducedMetricHypothesesOfConcreteValueMatrixFamily
      C)

/-- Concrete value matrices through the strongest W21 ingredients: period
closure from the carried period-search package and reduced metric from the
generated non-connector value tables. -/
def sourceFieldsOfConcreteValueMatrixFamilyViaW21Sources
    (C : ConcreteValueMatrixFamily) :
    SourceFields :=
  sourceFieldsOfClosureSourceAndReducedMetricFields
    (PeriodClosureSourceW21.sourceOfConcretePeriodSearchData C.periodSearch)
    (ReducedMetricSourceFieldsW21.fieldsOfConcreteValueMatrixFamily C)

/-- The table-route spelling of the concrete value-matrix constructor. -/
def sourceFieldsOfConcreteValueMatrixFamilyViaTableRoute
    (C : ConcreteValueMatrixFamily) :
    SourceFields :=
  sourceFieldsOfInputPackage
    (NonConnectorTableInputPackageW21.inputPackageOfConcreteValueMatrixFamily
      C)

/-- The input-package route gives the same concrete value-matrix inhabitant
shape in the raw W20 source-field type. -/
def sourceFieldsOfConcreteValueMatrixFamilyViaInputPackage
    (C : ConcreteValueMatrixFamily) :
    SourceFields :=
  sourceFieldsOfInputPackage
    (ConcreteValueMatrixToInputPackageW21.inputPackageOfConcreteValueMatrixFamily
      C)

theorem nonempty_sourceFields_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    Nonempty SourceFields :=
  Nonempty.intro (sourceFieldsOfConcreteValueMatrixFamily C)

end

end GeneratedChainSourceFieldsInhabitationW22
end PachToth
end ErdosProblems1066
