import ErdosProblems1066.PachToth.GeneratedClosureMetricRowsW30
import ErdosProblems1066.PachToth.CompletionRowsClosureW30
import ErdosProblems1066.PachToth.GeneratedClosureSourceSameFamilyW25
import ErdosProblems1066.PachToth.ReducedMetricFieldsSameFamilyW25

set_option autoImplicit false

/-!
# W31 generated metric source fields

This file sharpens the W30 generated-closure blocker.  The remaining source
surface is not just an abstract reduced metric hypothesis: it is exactly one
generated family with closure rows and the three same-family reduced metric
rows: global separation, exact base same-block isometry, and transition
same-block distance preservation.

The period-equation rows are recorded as a sufficient closure source through
the checked W20/W25 constructors.  No target statement is used to manufacture
source data.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedMetricSourceFieldsW31

noncomputable section

/-! ## W30 source vocabulary -/

abbrev GeneratedChainFamily : Type :=
  GeneratedClosureMetricRowsW30.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  GeneratedClosureMetricRowsW30.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedClosureMetricRowsW30.ReducedMetricHypotheses F

abbrev GeneratedClosureMetricRowPackage : Type :=
  GeneratedClosureMetricRowsW30.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  GeneratedClosureMetricRowsW30.GeneratedClosureMetricGate

abbrev MinimalGeneratedClosureMetricSourceFields : Prop :=
  GeneratedClosureMetricRowsW30.MinimalGeneratedClosureMetricSourceFields

abbrev SquaredOrbitClosureSourceRows : Type :=
  GeneratedClosureMetricRowsW30.SquaredOrbitClosureSourceRows

abbrev GeneratedClosureCompletionRowsSource : Type :=
  CompletionRowsClosureW30.GeneratedClosureCompletionRowsSource

/-! ## Sharper same-family closure and metric rows -/

abbrev FamilyPeriodEquations
    (F : GeneratedChainFamily) : Prop :=
  GeneratedClosureSourceSameFamilyW25.FamilyPeriodEquations F

abbrev ClosureSource
    (F : GeneratedChainFamily) :=
  GeneratedClosureSourceSameFamilyW25.W23ClosureSource F

abbrev ReducedMetricFields
    (F : GeneratedChainFamily) : Prop :=
  ReducedMetricFieldsSameFamilyW25.ReducedMetricFields F

abbrev SeparationField
    (F : GeneratedChainFamily) : Prop :=
  ReducedMetricFieldsSameFamilyW25.SeparationField F

abbrev BaseSameBlockField
    (F : GeneratedChainFamily) : Prop :=
  ReducedMetricFieldsSameFamilyW25.BaseSameBlockField F

abbrev TransitionSameBlockField
    (F : GeneratedChainFamily) : Prop :=
  ReducedMetricFieldsSameFamilyW25.TransitionSameBlockField F

abbrev ExplicitMetricRows
    (F : GeneratedChainFamily) : Prop :=
  SeparationField F /\ BaseSameBlockField F /\ TransitionSameBlockField F

abbrev ExplicitClosureMetricFieldRows : Prop :=
  Exists fun F : GeneratedChainFamily =>
    GeneratedChainFamilyClosures F /\ ExplicitMetricRows F

/-- Source-facing row package for the remaining W30 blocker. -/
structure ExplicitGeneratedMetricSourceRows where
  family : GeneratedChainFamily
  closure_rows : GeneratedChainFamilyClosures family
  separated : SeparationField family
  base_same_block_isometry : BaseSameBlockField family
  transition_preserves_same_block_distances : TransitionSameBlockField family

namespace ExplicitGeneratedMetricSourceRows

def toExplicitMetricRows
    (R : ExplicitGeneratedMetricSourceRows) :
    ExplicitMetricRows R.family :=
  And.intro R.separated
    (And.intro R.base_same_block_isometry
      R.transition_preserves_same_block_distances)

def toClosureSource
    (R : ExplicitGeneratedMetricSourceRows) :
    ClosureSource R.family :=
  GeneratedClosureMetricPackageInhabitationW25.closureSourceOfClosures
    R.closure_rows

def toReducedMetricFields
    (R : ExplicitGeneratedMetricSourceRows) :
    ReducedMetricFields R.family :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfSameFamilyData
    R.separated R.base_same_block_isometry
    R.transition_preserves_same_block_distances

def toReducedMetricHypotheses
    (R : ExplicitGeneratedMetricSourceRows) :
    ReducedMetricHypotheses R.family :=
  ReducedMetricFieldsSameFamilyW25.reducedMetricHypothesesOfFields
    R.toReducedMetricFields

def toGeneratedClosureMetricRowPackage
    (R : ExplicitGeneratedMetricSourceRows) :
    GeneratedClosureMetricRowPackage :=
  GeneratedClosureMetricPackageInhabitationW25.generatedClosureMetricRowPackageOfClosureSourceAndReducedMetricFields
    R.toClosureSource R.toReducedMetricFields

def toSquaredOrbitClosureSourceRows
    (R : ExplicitGeneratedMetricSourceRows) :
    SquaredOrbitClosureSourceRows :=
  GeneratedClosureMetricRowsW30.sourceRowsOfClosureReducedMetric
    R.family R.closure_rows R.toReducedMetricHypotheses

def toGeneratedClosureCompletionRowsSource
    (R : ExplicitGeneratedMetricSourceRows) :
    GeneratedClosureCompletionRowsSource :=
  CompletionRowsClosureW30.GeneratedClosureCompletionRowsSource.ofPackage
    R.toGeneratedClosureMetricRowPackage

@[simp]
theorem toGeneratedClosureMetricRowPackage_family
    (R : ExplicitGeneratedMetricSourceRows) :
    R.toGeneratedClosureMetricRowPackage.family = R.family :=
  rfl

end ExplicitGeneratedMetricSourceRows

def explicitRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    ExplicitGeneratedMetricSourceRows where
  family := P.family
  closure_rows := P.closureSource.toGeneratedChainFamilyClosures
  separated := P.reducedMetric.separated
  base_same_block_isometry := P.reducedMetric.base_same_block_isometry
  transition_preserves_same_block_distances :=
    P.reducedMetric.transition_preserves_same_block_distances

@[simp]
theorem explicitRowsOfGeneratedClosureMetricRowPackage_family
    (P : GeneratedClosureMetricRowPackage) :
    (explicitRowsOfGeneratedClosureMetricRowPackage P).family = P.family :=
  rfl

/-! ## Exact row-level equivalences -/

theorem reducedMetricHypotheses_iff_explicitMetricRows
    (F : GeneratedChainFamily) :
    ReducedMetricHypotheses F <-> ExplicitMetricRows F := by
  constructor
  case mp =>
    intro metric
    exact
      And.intro
        (fun k hk => (metric.metric k hk).separated)
        (And.intro
          (fun k hk => (metric.metric k hk).base_same_block_isometry)
          (fun k hk =>
            (metric.metric k hk).transition_preserves_same_block_distances))
  case mpr =>
    intro rows
    exact
      ReducedMetricFieldsSameFamilyW25.reducedMetricHypothesesOfFields
        (ReducedMetricFieldsSameFamilyW25.fieldsOfSameFamilyData
          rows.1 rows.2.1 rows.2.2)

theorem exists_generatedClosureMetricRowPackage_with_family_iff_explicitRows
    (F : GeneratedChainFamily) :
    (Exists fun P : GeneratedClosureMetricRowPackage => P.family = F) <->
      GeneratedChainFamilyClosures F /\ ExplicitMetricRows F := by
  constructor
  case mp =>
    intro h
    have source :=
      (GeneratedClosureMetricPackageInhabitationW25.exists_generatedClosureMetricRowPackage_with_family_iff_closures_and_reducedMetricHypotheses
        F).mp h
    exact
      And.intro source.1
        ((reducedMetricHypotheses_iff_explicitMetricRows F).mp source.2)
  case mpr =>
    intro rows
    exact
      (GeneratedClosureMetricPackageInhabitationW25.exists_generatedClosureMetricRowPackage_with_family_iff_closures_and_reducedMetricHypotheses
        F).mpr
        (And.intro rows.1
          ((reducedMetricHypotheses_iff_explicitMetricRows F).mpr rows.2))

theorem minimalSourceFields_iff_explicitFieldRows :
    MinimalGeneratedClosureMetricSourceFields <->
      ExplicitClosureMetricFieldRows := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F rows =>
        exact
          Exists.intro F
            (And.intro rows.1
              ((reducedMetricHypotheses_iff_explicitMetricRows F).mp rows.2))
  case mpr =>
    intro h
    cases h with
    | intro F rows =>
        exact
          Exists.intro F
            (And.intro rows.1
              ((reducedMetricHypotheses_iff_explicitMetricRows F).mpr rows.2))

theorem generatedClosureMetricGate_iff_explicitFieldRows :
    GeneratedClosureMetricGate <-> ExplicitClosureMetricFieldRows :=
  Iff.trans
    GeneratedClosureMetricRowsW30.generatedClosureMetricGate_iff_minimalSourceFields
    minimalSourceFields_iff_explicitFieldRows

theorem nonempty_explicitGeneratedMetricSourceRows_iff_explicitFieldRows :
    Nonempty ExplicitGeneratedMetricSourceRows <->
      ExplicitClosureMetricFieldRows := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact
          Exists.intro R.family
            (And.intro R.closure_rows R.toExplicitMetricRows)
  case mpr =>
    intro h
    cases h with
    | intro F rows =>
        exact
          Nonempty.intro
            { family := F
              closure_rows := rows.1
              separated := rows.2.1
              base_same_block_isometry := rows.2.2.1
              transition_preserves_same_block_distances := rows.2.2.2 }

theorem generatedClosureMetricGate_iff_explicitGeneratedMetricSourceRows :
    GeneratedClosureMetricGate <->
      Nonempty ExplicitGeneratedMetricSourceRows :=
  Iff.trans generatedClosureMetricGate_iff_explicitFieldRows
    nonempty_explicitGeneratedMetricSourceRows_iff_explicitFieldRows.symm

theorem explicitGeneratedMetricSourceRows_iff_generatedClosureMetricGate :
    Nonempty ExplicitGeneratedMetricSourceRows <->
      GeneratedClosureMetricGate :=
  generatedClosureMetricGate_iff_explicitGeneratedMetricSourceRows.symm

theorem squaredOrbitClosureSourceRows_of_explicitGeneratedMetricSourceRows :
    Nonempty ExplicitGeneratedMetricSourceRows ->
      Nonempty SquaredOrbitClosureSourceRows := by
  intro h
  cases h with
  | intro R =>
      exact Nonempty.intro R.toSquaredOrbitClosureSourceRows

theorem generatedClosureCompletionRowsSource_of_explicitGeneratedMetricSourceRows :
    Nonempty ExplicitGeneratedMetricSourceRows ->
      Nonempty GeneratedClosureCompletionRowsSource := by
  intro h
  cases h with
  | intro R =>
      exact Nonempty.intro R.toGeneratedClosureCompletionRowsSource

/-! ## Period-equation closure rows as a sufficient source surface -/

/-- A still more source-facing sufficient package: period equations plus the
three explicit reduced metric rows for the same generated family. -/
structure ExplicitPeriodMetricSourceRows where
  family : GeneratedChainFamily
  period_rows : FamilyPeriodEquations family
  separated : SeparationField family
  base_same_block_isometry : BaseSameBlockField family
  transition_preserves_same_block_distances : TransitionSameBlockField family

namespace ExplicitPeriodMetricSourceRows

def toClosureRows
    (R : ExplicitPeriodMetricSourceRows) :
    GeneratedChainFamilyClosures R.family :=
  (GeneratedClosureSourceSameFamilyW25.SameFamilyClosureEquationPackage.mk
    R.family R.period_rows).closures

def toExplicitGeneratedMetricSourceRows
    (R : ExplicitPeriodMetricSourceRows) :
    ExplicitGeneratedMetricSourceRows where
  family := R.family
  closure_rows := R.toClosureRows
  separated := R.separated
  base_same_block_isometry := R.base_same_block_isometry
  transition_preserves_same_block_distances :=
    R.transition_preserves_same_block_distances

def toGeneratedClosureMetricRowPackage
    (R : ExplicitPeriodMetricSourceRows) :
    GeneratedClosureMetricRowPackage :=
  R.toExplicitGeneratedMetricSourceRows.toGeneratedClosureMetricRowPackage

@[simp]
theorem toGeneratedClosureMetricRowPackage_family
    (R : ExplicitPeriodMetricSourceRows) :
    R.toGeneratedClosureMetricRowPackage.family = R.family :=
  rfl

end ExplicitPeriodMetricSourceRows

theorem explicitFieldRows_of_periodMetricSourceRows :
    Nonempty ExplicitPeriodMetricSourceRows ->
      ExplicitClosureMetricFieldRows := by
  intro h
  cases h with
  | intro R =>
      exact
        Exists.intro R.family
          (And.intro R.toClosureRows
            (And.intro R.separated
              (And.intro R.base_same_block_isometry
                R.transition_preserves_same_block_distances)))

theorem generatedClosureMetricGate_of_periodMetricSourceRows :
    Nonempty ExplicitPeriodMetricSourceRows ->
      GeneratedClosureMetricGate := by
  intro h
  exact
    generatedClosureMetricGate_iff_explicitFieldRows.mpr
      (explicitFieldRows_of_periodMetricSourceRows h)

theorem sourceRowsGate_of_periodMetricSourceRows :
    Nonempty ExplicitPeriodMetricSourceRows ->
      Nonempty SquaredOrbitClosureSourceRows := by
  intro h
  exact
    GeneratedClosureMetricRowsW30.squaredOrbitClosureSourceRowsGate_of_generatedClosureMetricGate
      (generatedClosureMetricGate_of_periodMetricSourceRows h)

/-- Final W31 spelling of the remaining W30 source blocker. -/
theorem generatedMetricSourceFieldBlocker :
    GeneratedClosureMetricGate <->
      Exists fun F : GeneratedChainFamily =>
        GeneratedChainFamilyClosures F /\
          SeparationField F /\
            BaseSameBlockField F /\
              TransitionSameBlockField F :=
  generatedClosureMetricGate_iff_explicitFieldRows

end

end GeneratedMetricSourceFieldsW31
end PachToth

namespace Verified

abbrev PachTothW31ExplicitGeneratedMetricSourceRows : Type :=
  PachToth.GeneratedMetricSourceFieldsW31.ExplicitGeneratedMetricSourceRows

abbrev PachTothW31ExplicitPeriodMetricSourceRows : Type :=
  PachToth.GeneratedMetricSourceFieldsW31.ExplicitPeriodMetricSourceRows

abbrev PachTothW31GeneratedClosureMetricGate : Prop :=
  PachToth.GeneratedMetricSourceFieldsW31.GeneratedClosureMetricGate

abbrev PachTothW31ExplicitClosureMetricFieldRows : Prop :=
  PachToth.GeneratedMetricSourceFieldsW31.ExplicitClosureMetricFieldRows

theorem pachtoth_w31_generatedClosureMetricGate_iff_explicitFieldRows :
    PachTothW31GeneratedClosureMetricGate <->
      PachTothW31ExplicitClosureMetricFieldRows :=
  PachToth.GeneratedMetricSourceFieldsW31.generatedClosureMetricGate_iff_explicitFieldRows

theorem pachtoth_w31_generatedClosureMetricGate_iff_explicitSourceRows :
    PachTothW31GeneratedClosureMetricGate <->
      Nonempty PachTothW31ExplicitGeneratedMetricSourceRows :=
  PachToth.GeneratedMetricSourceFieldsW31.generatedClosureMetricGate_iff_explicitGeneratedMetricSourceRows

theorem pachtoth_w31_generatedClosureMetricGate_of_periodMetricSourceRows :
    Nonempty PachTothW31ExplicitPeriodMetricSourceRows ->
      PachTothW31GeneratedClosureMetricGate :=
  PachToth.GeneratedMetricSourceFieldsW31.generatedClosureMetricGate_of_periodMetricSourceRows

theorem pachtoth_w31_generatedMetricSourceFieldBlocker :
    PachTothW31GeneratedClosureMetricGate <->
      Exists fun F : PachToth.GeneratedMetricSourceFieldsW31.GeneratedChainFamily =>
        PachToth.GeneratedMetricSourceFieldsW31.GeneratedChainFamilyClosures F /\
          PachToth.GeneratedMetricSourceFieldsW31.SeparationField F /\
            PachToth.GeneratedMetricSourceFieldsW31.BaseSameBlockField F /\
              PachToth.GeneratedMetricSourceFieldsW31.TransitionSameBlockField F :=
  PachToth.GeneratedMetricSourceFieldsW31.generatedMetricSourceFieldBlocker

end Verified
end ErdosProblems1066
