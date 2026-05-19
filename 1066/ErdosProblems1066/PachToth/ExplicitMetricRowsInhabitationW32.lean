import ErdosProblems1066.PachToth.CompletionRowsInhabitationW31
import ErdosProblems1066.PachToth.BaseTransitionRealization
import ErdosProblems1066.PachToth.FlexibleExactLocalTransition
import ErdosProblems1066.PachToth.GeneratedMetricSourceFieldsW31

set_option autoImplicit false

/-!
# W32 explicit metric-row source packages

This file keeps the W31 generated-metric source gate on the source side.  It
does not assert an unconditioned generated metric inhabitant.  Instead it
packages the exact missing data: generated closure rows plus the three explicit
same-family reduced metric rows.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExplicitMetricRowsInhabitationW32

noncomputable section

/-! ## W31 generated-metric vocabulary -/

abbrev GeneratedChainFamily : Type :=
  GeneratedMetricSourceFieldsW31.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.ReducedMetricHypotheses F

abbrev ReducedMetricFields
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.ReducedMetricFields F

abbrev SeparationField
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.SeparationField F

abbrev BaseSameBlockField
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.BaseSameBlockField F

abbrev TransitionSameBlockField
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.TransitionSameBlockField F

abbrev ExplicitMetricRows
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.ExplicitMetricRows F

abbrev ExplicitClosureMetricFieldRows : Prop :=
  GeneratedMetricSourceFieldsW31.ExplicitClosureMetricFieldRows

abbrev MinimalGeneratedClosureMetricSourceFields : Prop :=
  GeneratedMetricSourceFieldsW31.MinimalGeneratedClosureMetricSourceFields

abbrev GeneratedClosureMetricRowPackage : Type :=
  GeneratedMetricSourceFieldsW31.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  GeneratedMetricSourceFieldsW31.GeneratedClosureMetricGate

abbrev ExplicitGeneratedMetricSourceRows : Type :=
  GeneratedMetricSourceFieldsW31.ExplicitGeneratedMetricSourceRows

abbrev ExplicitPeriodMetricSourceRows : Type :=
  GeneratedMetricSourceFieldsW31.ExplicitPeriodMetricSourceRows

abbrev FamilyPeriodEquations
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.FamilyPeriodEquations F

abbrev SquaredOrbitClosureSourceRows : Type :=
  GeneratedMetricSourceFieldsW31.SquaredOrbitClosureSourceRows

abbrev GeneratedClosureCompletionRowsSource : Type :=
  GeneratedMetricSourceFieldsW31.GeneratedClosureCompletionRowsSource

abbrev GeneratedCompletionRowSource : Type :=
  CompletionRowsInhabitationW31.GeneratedCompletionRowSource

/-! ## Cross-block lower tables into the separation row -/

abbrev RoleHingedPeriodSearchFamily : Type :=
  ReducedMetricFieldsSameFamilyW25.RoleHingedPeriodSearchFamily

abbrev RoleHingedGeneratedChainFamily
    (F : RoleHingedPeriodSearchFamily) :
    GeneratedChainFamily :=
  ReducedMetricFieldsSameFamilyW25.roleHingedGeneratedChainFamily F

abbrev CrossBlockLowerBounds
    (F : RoleHingedPeriodSearchFamily) : Type :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F

abbrev IndexedCrossBlockLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) : Type :=
  CrossBlockLowerBoundsInterface.IndexedCrossBlockLowerTableFamily F

theorem separationField_of_crossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F) :
    SeparationField (RoleHingedGeneratedChainFamily F) := by
  intro k hk
  exact H.separated k hk

theorem separationField_of_indexedCrossBlockLowerTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F) :
    SeparationField (RoleHingedGeneratedChainFamily F) := by
  exact
    separationField_of_crossBlockLowerBounds
      (CrossBlockLowerBoundsInterface.CrossBlockLowerBounds.ofIndexedTables T)

/-! ## Concrete same-block metric fields -/

/-- If a generated family uses the checked exact local block as its base for
every block count, then it has the W32 base same-block metric field. -/
theorem baseSameBlockField_of_exactBase
    {F : GeneratedChainFamily}
    (hbase :
      forall (k : Nat) (hk : 0 < k),
        F.base k hk = BaseTransitionRealization.exactBase) :
    BaseSameBlockField F := by
  intro k hk
  rw [hbase k hk]
  intro u v
  simpa [HingedTransitionInterface.referenceDistance] using
    BaseTransitionRealization.exactBase_same_block_isometry u v

/-- Same/opposite metric transition obligations provide the W32 transition
same-block metric field for any generated family using those transition maps. -/
theorem transitionSameBlockField_of_metricObligations
    {F : GeneratedChainFamily}
    (metric :
      forall (k : Nat) (_hk : 0 < k),
        HingedTransitionInterface.SameOppositeTransitionMetricObligations)
    (hO :
      forall (k : Nat) (hk : 0 < k),
        F.O k hk =
          (metric k hk).toFigure2TransitionObligations) :
    TransitionSameBlockField F := by
  intro k hk
  rw [hO k hk]
  intro orientation source u v
  exact
    HingedTransitionInterface.SameOppositeTransitionMetricObligations.transitionFor_preserves_same_block_distances
      (metric k hk) orientation source u v

/-- The base same/opposite realization interface is a concrete source of the
W32 transition same-block metric field. -/
theorem transitionSameBlockField_of_baseTransitionRealization
    {F : GeneratedChainFamily}
    (transitions :
      forall (k : Nat) (_hk : 0 < k),
        BaseTransitionRealization.BaseSameOppositeTransitionRealization)
    (hO :
      forall (k : Nat) (hk : 0 < k),
        F.O k hk =
          (transitions k hk).toFigure2TransitionObligations) :
    TransitionSameBlockField F := by
  exact
    transitionSameBlockField_of_metricObligations
      (fun k hk => (transitions k hk).toMetricObligations)
      (by
        intro k hk
        rw [hO k hk]
        rfl)

/-- The generated-chain family obtained from one concrete exact-base
same/opposite transition realization and an orientation family. -/
def generatedChainFamilyOfBaseTransitionRealization
    (transitions :
      BaseTransitionRealization.BaseSameOppositeTransitionRealization)
    (orientation :
      forall (k : Nat), 0 < k ->
        Fin k -> OrientationData.BlockOrientation) :
    GeneratedChainFamily where
  O := fun _k _hk => transitions.toFigure2TransitionObligations
  base := fun _k _hk => BaseTransitionRealization.exactBase
  orientation := orientation

@[simp]
theorem generatedChainFamilyOfBaseTransitionRealization_O
    (transitions :
      BaseTransitionRealization.BaseSameOppositeTransitionRealization)
    (orientation :
      forall (k : Nat), 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfBaseTransitionRealization
      transitions orientation).O k hk =
      transitions.toFigure2TransitionObligations := by
  rfl

@[simp]
theorem generatedChainFamilyOfBaseTransitionRealization_base
    (transitions :
      BaseTransitionRealization.BaseSameOppositeTransitionRealization)
    (orientation :
      forall (k : Nat), 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfBaseTransitionRealization
      transitions orientation).base k hk =
      BaseTransitionRealization.exactBase := by
  rfl

/-- Concrete exact-base transition realizations supply the W32 base
same-block field for their generated family. -/
theorem baseSameBlockField_of_baseTransitionRealization
    (transitions :
      BaseTransitionRealization.BaseSameOppositeTransitionRealization)
    (orientation :
      forall (k : Nat), 0 < k ->
        Fin k -> OrientationData.BlockOrientation) :
    BaseSameBlockField
      (generatedChainFamilyOfBaseTransitionRealization
        transitions orientation) := by
  exact
    baseSameBlockField_of_exactBase
      (F := generatedChainFamilyOfBaseTransitionRealization
        transitions orientation)
      (by
        intro _k _hk
        rfl)

/-- Concrete exact-base transition realizations supply the W32 transition
same-block field for their generated family. -/
theorem transitionSameBlockField_of_baseTransitionRealizationFamily
    (transitions :
      BaseTransitionRealization.BaseSameOppositeTransitionRealization)
    (orientation :
      forall (k : Nat), 0 < k ->
        Fin k -> OrientationData.BlockOrientation) :
    TransitionSameBlockField
      (generatedChainFamilyOfBaseTransitionRealization
        transitions orientation) := by
  exact
    transitionSameBlockField_of_baseTransitionRealization
      (F := generatedChainFamilyOfBaseTransitionRealization
        transitions orientation)
      (fun _k _hk => transitions)
      (by
        intro _k _hk
        rfl)

/-! ## Flexible exact-local generated closure fields -/

abbrev FlexibleGeneratedClosureFamily : Type :=
  FlexibleExactLocalTransition.GeneratedClosureFamily

abbrev flexibleGeneratedChainFamily
    (F : FlexibleGeneratedClosureFamily) :
    GeneratedChainFamily :=
  F.toGeneratedChainFamily

/-- A flexible exact-local generated-closure family supplies concrete W32
closure rows for its generated-chain family. -/
theorem closureRows_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    GeneratedChainFamilyClosures (flexibleGeneratedChainFamily F) := by
  exact F.toGeneratedChainFamilyClosures

/-- A flexible exact-local generated-closure family supplies the concrete W32
global-separation field for its generated-chain family. -/
theorem separationField_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    SeparationField (flexibleGeneratedChainFamily F) := by
  intro k hk
  exact F.separated k hk

/-- A flexible exact-local generated-closure family uses the checked exact
base, hence supplies the concrete W32 base same-block field. -/
theorem baseSameBlockField_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    BaseSameBlockField (flexibleGeneratedChainFamily F) := by
  exact
    baseSameBlockField_of_exactBase
      (F := flexibleGeneratedChainFamily F)
      (by
        intro _k _hk
        rfl)

/-- The flexible exact-local fields do not supply the stronger W32 reduced
transition field.  Such a field would force arbitrary-source same-block
preservation for a role-realizing branch, which the local role table already
rules out. -/
theorem not_transitionSameBlockField_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    Not (TransitionSameBlockField (flexibleGeneratedChainFamily F)) := by
  intro htransition
  have hpreserve :
      HingedTransitionInterface.PreservesSameBlockDistances
        F.transitions.same.placeNext := by
    intro source u v
    have hrow := htransition 1 (by decide)
    simpa [flexibleGeneratedChainFamily,
      FlexibleExactLocalTransition.GeneratedClosureFamily.toGeneratedChainFamily,
      FlexibleExactLocalTransition.SameOpposite.toFigure2TransitionObligations,
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances]
      using hrow OrientationData.BlockOrientation.same source u v
  exact
    RoleHingeTransitionSearch.false_of_preservesSameBlockDistances_and_realizes_role
      F.transitions.same.toConnectorTransitionFacts
      (by
        simpa using hpreserve)

/-! ## Metric rows alone -/

/-- The three explicit reduced metric rows for a fixed generated family. -/
structure ExplicitMetricRowPackage
    (F : GeneratedChainFamily) : Type where
  separated : SeparationField F
  base_same_block_isometry : BaseSameBlockField F
  transition_preserves_same_block_distances : TransitionSameBlockField F

namespace ExplicitMetricRowPackage

def toExplicitMetricRows
    {F : GeneratedChainFamily}
    (R : ExplicitMetricRowPackage F) :
    ExplicitMetricRows F :=
  And.intro R.separated
    (And.intro R.base_same_block_isometry
      R.transition_preserves_same_block_distances)

def toReducedMetricFields
    {F : GeneratedChainFamily}
    (R : ExplicitMetricRowPackage F) :
    ReducedMetricFields F :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfSameFamilyData
    R.separated R.base_same_block_isometry
    R.transition_preserves_same_block_distances

def toReducedMetricHypotheses
    {F : GeneratedChainFamily}
    (R : ExplicitMetricRowPackage F) :
    ReducedMetricHypotheses F :=
  ReducedMetricFieldsSameFamilyW25.reducedMetricHypothesesOfFields
    R.toReducedMetricFields

def ofReducedMetricFields
    {F : GeneratedChainFamily}
    (R : ReducedMetricFields F) :
    ExplicitMetricRowPackage F where
  separated := R.separated
  base_same_block_isometry := R.base_same_block_isometry
  transition_preserves_same_block_distances :=
    R.transition_preserves_same_block_distances

def ofReducedMetricHypotheses
    {F : GeneratedChainFamily}
    (R : ReducedMetricHypotheses F) :
    ExplicitMetricRowPackage F where
  separated := fun k hk => (R.metric k hk).separated
  base_same_block_isometry := fun k hk =>
    (R.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances := fun k hk =>
    (R.metric k hk).transition_preserves_same_block_distances

@[simp]
theorem toReducedMetricFields_separated
    {F : GeneratedChainFamily}
    (R : ExplicitMetricRowPackage F) :
    R.toReducedMetricFields.separated = R.separated :=
  rfl

@[simp]
theorem toReducedMetricFields_base_same_block_isometry
    {F : GeneratedChainFamily}
    (R : ExplicitMetricRowPackage F) :
    R.toReducedMetricFields.base_same_block_isometry =
      R.base_same_block_isometry :=
  rfl

@[simp]
theorem toReducedMetricFields_transition_preserves_same_block_distances
    {F : GeneratedChainFamily}
    (R : ExplicitMetricRowPackage F) :
    R.toReducedMetricFields.transition_preserves_same_block_distances =
      R.transition_preserves_same_block_distances :=
  rfl

end ExplicitMetricRowPackage

theorem nonempty_explicitMetricRowPackage_iff_explicitMetricRows
    (F : GeneratedChainFamily) :
    Nonempty (ExplicitMetricRowPackage F) <-> ExplicitMetricRows F := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact R.toExplicitMetricRows
  case mpr =>
    intro h
    exact
      Nonempty.intro
        { separated := h.1
          base_same_block_isometry := h.2.1
          transition_preserves_same_block_distances := h.2.2 }

theorem nonempty_explicitMetricRowPackage_iff_reducedMetricHypotheses
    (F : GeneratedChainFamily) :
    Nonempty (ExplicitMetricRowPackage F) <->
      ReducedMetricHypotheses F :=
  Iff.trans
    (nonempty_explicitMetricRowPackage_iff_explicitMetricRows F)
    (GeneratedMetricSourceFieldsW31.reducedMetricHypotheses_iff_explicitMetricRows
      F).symm

/-! ## Closure plus metric-row source package -/

/-- Source package for the generated-metric row gate: one generated family,
its closure rows, and the three explicit same-family metric rows. -/
structure ExplicitClosureMetricRowPackage where
  family : GeneratedChainFamily
  closure_rows : GeneratedChainFamilyClosures family
  metric_rows : ExplicitMetricRowPackage family

namespace ExplicitClosureMetricRowPackage

def toExplicitGeneratedMetricSourceRows
    (S : ExplicitClosureMetricRowPackage) :
    ExplicitGeneratedMetricSourceRows where
  family := S.family
  closure_rows := S.closure_rows
  separated := S.metric_rows.separated
  base_same_block_isometry := S.metric_rows.base_same_block_isometry
  transition_preserves_same_block_distances :=
    S.metric_rows.transition_preserves_same_block_distances

def ofExplicitGeneratedMetricSourceRows
    (S : ExplicitGeneratedMetricSourceRows) :
    ExplicitClosureMetricRowPackage where
  family := S.family
  closure_rows := S.closure_rows
  metric_rows :=
    { separated := S.separated
      base_same_block_isometry := S.base_same_block_isometry
      transition_preserves_same_block_distances :=
        S.transition_preserves_same_block_distances }

def toGeneratedClosureMetricRowPackage
    (S : ExplicitClosureMetricRowPackage) :
    GeneratedClosureMetricRowPackage :=
  S.toExplicitGeneratedMetricSourceRows.toGeneratedClosureMetricRowPackage

def toSquaredOrbitClosureSourceRows
    (S : ExplicitClosureMetricRowPackage) :
    SquaredOrbitClosureSourceRows :=
  S.toExplicitGeneratedMetricSourceRows.toSquaredOrbitClosureSourceRows

def toGeneratedClosureCompletionRowsSource
    (S : ExplicitClosureMetricRowPackage) :
    GeneratedClosureCompletionRowsSource :=
  S.toExplicitGeneratedMetricSourceRows.toGeneratedClosureCompletionRowsSource

def toGeneratedCompletionRowSource
    (S : ExplicitClosureMetricRowPackage) :
    GeneratedCompletionRowSource :=
  CompletionRowsInhabitationW31.generatedCompletionRowSourceOfGeneratedClosureMetricRowPackage
    S.toGeneratedClosureMetricRowPackage

@[simp]
theorem toExplicitGeneratedMetricSourceRows_family
    (S : ExplicitClosureMetricRowPackage) :
    S.toExplicitGeneratedMetricSourceRows.family = S.family :=
  rfl

@[simp]
theorem ofExplicitGeneratedMetricSourceRows_family
    (S : ExplicitGeneratedMetricSourceRows) :
    (ofExplicitGeneratedMetricSourceRows S).family = S.family :=
  rfl

@[simp]
theorem toGeneratedClosureMetricRowPackage_family
    (S : ExplicitClosureMetricRowPackage) :
    S.toGeneratedClosureMetricRowPackage.family = S.family :=
  rfl

end ExplicitClosureMetricRowPackage

def explicitClosureMetricRowPackageEquivW31 :
    Equiv ExplicitClosureMetricRowPackage
      ExplicitGeneratedMetricSourceRows where
  toFun :=
    ExplicitClosureMetricRowPackage.toExplicitGeneratedMetricSourceRows
  invFun :=
    ExplicitClosureMetricRowPackage.ofExplicitGeneratedMetricSourceRows
  left_inv := by
    intro S
    cases S with
    | mk family closure_rows metric_rows =>
        cases metric_rows
        rfl
  right_inv := by
    intro S
    cases S
    rfl

def explicitClosureMetricRowPackageOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    ExplicitClosureMetricRowPackage :=
  ExplicitClosureMetricRowPackage.ofExplicitGeneratedMetricSourceRows
    (GeneratedMetricSourceFieldsW31.explicitRowsOfGeneratedClosureMetricRowPackage
      P)

@[simp]
theorem explicitClosureMetricRowPackageOfGeneratedClosureMetricRowPackage_family
    (P : GeneratedClosureMetricRowPackage) :
    (explicitClosureMetricRowPackageOfGeneratedClosureMetricRowPackage P).family =
      P.family :=
  rfl

def generatedClosureMetricRowPackageOfExplicitClosureMetricRowPackage
    (S : ExplicitClosureMetricRowPackage) :
    GeneratedClosureMetricRowPackage :=
  S.toGeneratedClosureMetricRowPackage

def squaredOrbitClosureSourceRowsOfExplicitClosureMetricRowPackage
    (S : ExplicitClosureMetricRowPackage) :
    SquaredOrbitClosureSourceRows :=
  S.toSquaredOrbitClosureSourceRows

theorem generatedClosureMetricGate_of_explicitClosureMetricRowPackage_row
    (S : ExplicitClosureMetricRowPackage) :
    GeneratedClosureMetricGate :=
  Nonempty.intro
    (generatedClosureMetricRowPackageOfExplicitClosureMetricRowPackage S)

theorem squaredOrbitClosureSourceRowsGate_of_explicitClosureMetricRowPackage_row
    (S : ExplicitClosureMetricRowPackage) :
    Nonempty SquaredOrbitClosureSourceRows :=
  Nonempty.intro
    (squaredOrbitClosureSourceRowsOfExplicitClosureMetricRowPackage S)

def explicitClosureMetricRowPackageOfNamedFields
    (F : GeneratedChainFamily)
    (closure_rows : GeneratedChainFamilyClosures F)
    (separated : SeparationField F)
    (base_same_block_isometry : BaseSameBlockField F)
    (transition_preserves_same_block_distances :
      TransitionSameBlockField F) :
    ExplicitClosureMetricRowPackage where
  family := F
  closure_rows := closure_rows
  metric_rows :=
    { separated := separated
      base_same_block_isometry := base_same_block_isometry
      transition_preserves_same_block_distances :=
        transition_preserves_same_block_distances }

theorem nonempty_explicitClosureMetricRowPackage_iff_w31SourceRows :
    Nonempty ExplicitClosureMetricRowPackage <->
      Nonempty ExplicitGeneratedMetricSourceRows := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toExplicitGeneratedMetricSourceRows
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact
          Nonempty.intro
            (ExplicitClosureMetricRowPackage.ofExplicitGeneratedMetricSourceRows
              S)

theorem nonempty_explicitClosureMetricRowPackage_iff_explicitFieldRows :
    Nonempty ExplicitClosureMetricRowPackage <->
      ExplicitClosureMetricFieldRows := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.family
            (And.intro S.closure_rows S.metric_rows.toExplicitMetricRows)
  case mpr =>
    intro h
    cases h with
    | intro F rows =>
        exact
          Nonempty.intro
            (explicitClosureMetricRowPackageOfNamedFields
              F rows.1 rows.2.1 rows.2.2.1 rows.2.2.2)

theorem explicitFieldRows_iff_explicitClosureMetricRowPackage :
    ExplicitClosureMetricFieldRows <->
      Nonempty ExplicitClosureMetricRowPackage :=
  nonempty_explicitClosureMetricRowPackage_iff_explicitFieldRows.symm

theorem minimalSourceFields_iff_explicitClosureMetricRowPackage :
    MinimalGeneratedClosureMetricSourceFields <->
      Nonempty ExplicitClosureMetricRowPackage :=
  Iff.trans
    GeneratedMetricSourceFieldsW31.minimalSourceFields_iff_explicitFieldRows
    explicitFieldRows_iff_explicitClosureMetricRowPackage

theorem generatedClosureMetricGate_iff_explicitClosureMetricRowPackage :
    GeneratedClosureMetricGate <->
      Nonempty ExplicitClosureMetricRowPackage :=
  Iff.trans
    GeneratedMetricSourceFieldsW31.generatedClosureMetricGate_iff_explicitFieldRows
    explicitFieldRows_iff_explicitClosureMetricRowPackage

theorem explicitClosureMetricRowPackage_iff_generatedClosureMetricGate :
    Nonempty ExplicitClosureMetricRowPackage <->
      GeneratedClosureMetricGate :=
  generatedClosureMetricGate_iff_explicitClosureMetricRowPackage.symm

theorem generatedClosureMetricGate_of_explicitClosureMetricRowPackage :
    Nonempty ExplicitClosureMetricRowPackage ->
      GeneratedClosureMetricGate :=
  explicitClosureMetricRowPackage_iff_generatedClosureMetricGate.mp

theorem explicitClosureMetricRowPackage_of_generatedClosureMetricGate :
    GeneratedClosureMetricGate ->
      Nonempty ExplicitClosureMetricRowPackage :=
  generatedClosureMetricGate_iff_explicitClosureMetricRowPackage.mp

theorem generatedClosureMetricGate_of_namedFields
    (F : GeneratedChainFamily)
    (closure_rows : GeneratedChainFamilyClosures F)
    (separated : SeparationField F)
    (base_same_block_isometry : BaseSameBlockField F)
    (transition_preserves_same_block_distances :
      TransitionSameBlockField F) :
    GeneratedClosureMetricGate :=
  generatedClosureMetricGate_of_explicitClosureMetricRowPackage
    (Nonempty.intro
      (explicitClosureMetricRowPackageOfNamedFields
        F closure_rows separated base_same_block_isometry
        transition_preserves_same_block_distances))

theorem explicitClosureMetricRowPackage_blocker :
    Nonempty ExplicitClosureMetricRowPackage <->
      Exists fun F : GeneratedChainFamily =>
        GeneratedChainFamilyClosures F /\
          SeparationField F /\
            BaseSameBlockField F /\
              TransitionSameBlockField F := by
  constructor
  case mp =>
    intro h
    exact
      nonempty_explicitClosureMetricRowPackage_iff_explicitFieldRows.mp h
  case mpr =>
    intro h
    exact
      nonempty_explicitClosureMetricRowPackage_iff_explicitFieldRows.mpr h

/-! ## Period equations plus metric rows -/

/-- A more source-facing package: period equations supply closure rows, while
the same generated family carries the three explicit metric rows. -/
structure ExplicitPeriodClosureMetricRowPackage where
  family : GeneratedChainFamily
  period_rows : FamilyPeriodEquations family
  metric_rows : ExplicitMetricRowPackage family

namespace ExplicitPeriodClosureMetricRowPackage

def toExplicitPeriodMetricSourceRows
    (S : ExplicitPeriodClosureMetricRowPackage) :
    ExplicitPeriodMetricSourceRows where
  family := S.family
  period_rows := S.period_rows
  separated := S.metric_rows.separated
  base_same_block_isometry := S.metric_rows.base_same_block_isometry
  transition_preserves_same_block_distances :=
    S.metric_rows.transition_preserves_same_block_distances

def ofExplicitPeriodMetricSourceRows
    (S : ExplicitPeriodMetricSourceRows) :
    ExplicitPeriodClosureMetricRowPackage where
  family := S.family
  period_rows := S.period_rows
  metric_rows :=
    { separated := S.separated
      base_same_block_isometry := S.base_same_block_isometry
      transition_preserves_same_block_distances :=
        S.transition_preserves_same_block_distances }

def toClosureMetricRowPackage
    (S : ExplicitPeriodClosureMetricRowPackage) :
    ExplicitClosureMetricRowPackage :=
  ExplicitClosureMetricRowPackage.ofExplicitGeneratedMetricSourceRows
    S.toExplicitPeriodMetricSourceRows.toExplicitGeneratedMetricSourceRows

def toGeneratedClosureMetricRowPackage
    (S : ExplicitPeriodClosureMetricRowPackage) :
    GeneratedClosureMetricRowPackage :=
  S.toClosureMetricRowPackage.toGeneratedClosureMetricRowPackage

def toGeneratedClosureCompletionRowsSource
    (S : ExplicitPeriodClosureMetricRowPackage) :
    GeneratedClosureCompletionRowsSource :=
  S.toClosureMetricRowPackage.toGeneratedClosureCompletionRowsSource

@[simp]
theorem toExplicitPeriodMetricSourceRows_family
    (S : ExplicitPeriodClosureMetricRowPackage) :
    S.toExplicitPeriodMetricSourceRows.family = S.family :=
  rfl

@[simp]
theorem ofExplicitPeriodMetricSourceRows_family
    (S : ExplicitPeriodMetricSourceRows) :
    (ofExplicitPeriodMetricSourceRows S).family = S.family :=
  rfl

@[simp]
theorem toClosureMetricRowPackage_family
    (S : ExplicitPeriodClosureMetricRowPackage) :
    S.toClosureMetricRowPackage.family = S.family :=
  rfl

@[simp]
theorem toGeneratedClosureMetricRowPackage_family
    (S : ExplicitPeriodClosureMetricRowPackage) :
    S.toGeneratedClosureMetricRowPackage.family = S.family :=
  rfl

end ExplicitPeriodClosureMetricRowPackage

def explicitPeriodClosureMetricRowPackageEquivW31 :
    Equiv ExplicitPeriodClosureMetricRowPackage
      ExplicitPeriodMetricSourceRows where
  toFun :=
    ExplicitPeriodClosureMetricRowPackage.toExplicitPeriodMetricSourceRows
  invFun :=
    ExplicitPeriodClosureMetricRowPackage.ofExplicitPeriodMetricSourceRows
  left_inv := by
    intro S
    cases S with
    | mk family period_rows metric_rows =>
        cases metric_rows
        rfl
  right_inv := by
    intro S
    cases S
    rfl

theorem nonempty_explicitPeriodClosureMetricRowPackage_iff_w31PeriodRows :
    Nonempty ExplicitPeriodClosureMetricRowPackage <->
      Nonempty ExplicitPeriodMetricSourceRows := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toExplicitPeriodMetricSourceRows
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact
          Nonempty.intro
            (ExplicitPeriodClosureMetricRowPackage.ofExplicitPeriodMetricSourceRows
              S)

theorem explicitClosureMetricRowPackage_of_explicitPeriodClosureMetricRowPackage :
    Nonempty ExplicitPeriodClosureMetricRowPackage ->
      Nonempty ExplicitClosureMetricRowPackage := by
  intro h
  cases h with
  | intro S =>
      exact Nonempty.intro S.toClosureMetricRowPackage

theorem generatedClosureMetricGate_of_explicitPeriodClosureMetricRowPackage :
    Nonempty ExplicitPeriodClosureMetricRowPackage ->
      GeneratedClosureMetricGate := by
  intro h
  exact
    generatedClosureMetricGate_of_explicitClosureMetricRowPackage
      (explicitClosureMetricRowPackage_of_explicitPeriodClosureMetricRowPackage
        h)

theorem squaredOrbitClosureSourceRows_of_explicitClosureMetricRowPackage :
    Nonempty ExplicitClosureMetricRowPackage ->
      Nonempty SquaredOrbitClosureSourceRows := by
  intro h
  cases h with
  | intro S =>
      exact Nonempty.intro S.toSquaredOrbitClosureSourceRows

theorem generatedClosureCompletionRowsSource_of_explicitClosureMetricRowPackage :
    Nonempty ExplicitClosureMetricRowPackage ->
      Nonempty GeneratedClosureCompletionRowsSource := by
  intro h
  cases h with
  | intro S =>
      exact Nonempty.intro S.toGeneratedClosureCompletionRowsSource

theorem generatedCompletionRowSource_of_explicitClosureMetricRowPackage :
    Nonempty ExplicitClosureMetricRowPackage ->
      Nonempty GeneratedCompletionRowSource := by
  intro h
  cases h with
  | intro S =>
      exact Nonempty.intro S.toGeneratedCompletionRowSource

/-! ## Compact W32 source certificate -/

abbrev ExplicitMetricRowsInhabitationCertificate : Prop :=
  (GeneratedClosureMetricGate <->
    Nonempty ExplicitClosureMetricRowPackage) /\
    (Nonempty ExplicitClosureMetricRowPackage <->
      Exists fun F : GeneratedChainFamily =>
        GeneratedChainFamilyClosures F /\
          SeparationField F /\
            BaseSameBlockField F /\
              TransitionSameBlockField F) /\
      (Nonempty ExplicitPeriodClosureMetricRowPackage ->
        GeneratedClosureMetricGate) /\
        (Nonempty ExplicitClosureMetricRowPackage ->
          Nonempty GeneratedCompletionRowSource)

theorem explicitMetricRowsInhabitationCertificate :
    ExplicitMetricRowsInhabitationCertificate :=
  And.intro generatedClosureMetricGate_iff_explicitClosureMetricRowPackage
    (And.intro explicitClosureMetricRowPackage_blocker
      (And.intro
        generatedClosureMetricGate_of_explicitPeriodClosureMetricRowPackage
        generatedCompletionRowSource_of_explicitClosureMetricRowPackage))

end

end ExplicitMetricRowsInhabitationW32
end PachToth

namespace Verified

abbrev PachTothW32ExplicitMetricRowPackage
    (F : PachToth.ExplicitMetricRowsInhabitationW32.GeneratedChainFamily) :
    Type :=
  PachToth.ExplicitMetricRowsInhabitationW32.ExplicitMetricRowPackage F

abbrev PachTothW32ExplicitClosureMetricRowPackage : Type :=
  PachToth.ExplicitMetricRowsInhabitationW32.ExplicitClosureMetricRowPackage

abbrev PachTothW32ExplicitPeriodClosureMetricRowPackage : Type :=
  PachToth.ExplicitMetricRowsInhabitationW32.ExplicitPeriodClosureMetricRowPackage

abbrev PachTothW32GeneratedClosureMetricGate : Prop :=
  PachToth.ExplicitMetricRowsInhabitationW32.GeneratedClosureMetricGate

abbrev PachTothW32GeneratedCompletionRowSource : Type :=
  PachToth.ExplicitMetricRowsInhabitationW32.GeneratedCompletionRowSource

theorem pachtoth_w32_generatedClosureMetricGate_iff_explicitClosureMetricRowPackage :
    PachTothW32GeneratedClosureMetricGate <->
      Nonempty PachTothW32ExplicitClosureMetricRowPackage :=
  PachToth.ExplicitMetricRowsInhabitationW32.generatedClosureMetricGate_iff_explicitClosureMetricRowPackage

theorem pachtoth_w32_explicitClosureMetricRowPackage_blocker :
    Nonempty PachTothW32ExplicitClosureMetricRowPackage <->
      Exists fun F :
        PachToth.ExplicitMetricRowsInhabitationW32.GeneratedChainFamily =>
        PachToth.ExplicitMetricRowsInhabitationW32.GeneratedChainFamilyClosures
          F /\
          PachToth.ExplicitMetricRowsInhabitationW32.SeparationField F /\
            PachToth.ExplicitMetricRowsInhabitationW32.BaseSameBlockField F /\
              PachToth.ExplicitMetricRowsInhabitationW32.TransitionSameBlockField
                F :=
  PachToth.ExplicitMetricRowsInhabitationW32.explicitClosureMetricRowPackage_blocker

theorem pachtoth_w32_generatedClosureMetricGate_of_namedFields
    (F : PachToth.ExplicitMetricRowsInhabitationW32.GeneratedChainFamily)
    (closure_rows :
      PachToth.ExplicitMetricRowsInhabitationW32.GeneratedChainFamilyClosures
        F)
    (separated :
      PachToth.ExplicitMetricRowsInhabitationW32.SeparationField F)
    (base_same_block_isometry :
      PachToth.ExplicitMetricRowsInhabitationW32.BaseSameBlockField F)
    (transition_preserves_same_block_distances :
      PachToth.ExplicitMetricRowsInhabitationW32.TransitionSameBlockField F) :
    PachTothW32GeneratedClosureMetricGate :=
  PachToth.ExplicitMetricRowsInhabitationW32.generatedClosureMetricGate_of_namedFields
    F closure_rows separated base_same_block_isometry
    transition_preserves_same_block_distances

theorem pachtoth_w32_generatedCompletionRowSource_of_explicitClosureMetricRowPackage :
    Nonempty PachTothW32ExplicitClosureMetricRowPackage ->
      Nonempty PachTothW32GeneratedCompletionRowSource :=
  PachToth.ExplicitMetricRowsInhabitationW32.generatedCompletionRowSource_of_explicitClosureMetricRowPackage

theorem pachtoth_w32_explicitMetricRowsInhabitationCertificate :
    PachToth.ExplicitMetricRowsInhabitationW32.ExplicitMetricRowsInhabitationCertificate :=
  PachToth.ExplicitMetricRowsInhabitationW32.explicitMetricRowsInhabitationCertificate

end Verified
end ErdosProblems1066
