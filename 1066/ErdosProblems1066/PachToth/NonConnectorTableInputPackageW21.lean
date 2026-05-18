import ErdosProblems1066.PachToth.GeneratedChainFamilyProducerW20
import ErdosProblems1066.PachToth.GeneratedChainClosureProducerW20
import ErdosProblems1066.PachToth.ReducedMetricHypothesesProducerW20
import ErdosProblems1066.PachToth.ExplicitClosedPlacementInputPackageW20

set_option autoImplicit false

/-!
# W21 non-connector table input-package handoff

The W12/W13 non-connector table families provide the reduced metric part of
the generated-chain route.  They do not, by themselves, provide the period or
closure equations.  This file records the exact dependency: once a closure
source for the same generated family is supplied, the W20 producers assemble
the `ExplicitClosedPlacementProducerW19.InputPackage`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonConnectorTableInputPackageW21

open FiniteGraph

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  NonConnectorSeparationW12.RoleHingedPeriodSearchFamily

abbrev GeneratedNonConnectorSqDistanceTableFamily :=
  NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  NonConnectorSeparationW12.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev GeneratedChainFamily :=
  ExplicitClosedPlacementInputPackageW20.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementInputPackageW20.GeneratedChainFamilyClosures F

abbrev GeneratedChainFamilyPeriods
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.GeneratedChainFamilyPeriods F

abbrev FamilyPeriodEquations
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.FamilyPeriodEquations F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementInputPackageW20.ReducedMetricHypotheses F

abbrev W20SourceFields :=
  ExplicitClosedPlacementInputPackageW20.GeneratedFamilyClosureReducedMetricSourceFields

abbrev W19InputPackage :=
  ExplicitClosedPlacementInputPackageW20.W19InputPackage

/-- The generated-chain family canonically associated with a W12
role-hinged non-connector table family. -/
def generatedChainFamily
    (F : RoleHingedPeriodSearchFamily) :
    GeneratedChainFamily :=
  ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F

@[simp]
theorem generatedChainFamily_O
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamily F).O k hk =
      F.transitions.toFigure2TransitionObligations := by
  rfl

@[simp]
theorem generatedChainFamily_base
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamily F).base k hk =
      BaseTransitionRealization.exactBase := by
  rfl

@[simp]
theorem generatedChainFamily_orientation
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamily F).orientation k hk =
      F.orientation k hk := by
  rfl

/-- W12 generated non-connector tables supply exactly the reduced metric
hypotheses for their generated-chain family. -/
def reducedMetricOfGeneratedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F) :
    ReducedMetricHypotheses (generatedChainFamily F) :=
  ReducedMetricHypothesesProducerW20.ofGeneratedNonConnectorSqDistanceTableFamily
    T

@[simp]
theorem reducedMetricOfGeneratedTableFamily_separated
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    ((reducedMetricOfGeneratedTableFamily T).metric k hk).separated =
      T.separated k hk := by
  rfl

/-- Finite-index W12/W13 tables first become generated local-vertex tables,
then supply reduced metric hypotheses. -/
def reducedMetricOfIndexedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    ReducedMetricHypotheses (generatedChainFamily F) :=
  ReducedMetricHypothesesProducerW20.ofIndexedNonConnectorCrossBlockSqDistanceTableFamily
    T

@[simp]
theorem reducedMetricOfIndexedTableFamily_eq_generated
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    reducedMetricOfIndexedTableFamily T =
      reducedMetricOfGeneratedTableFamily
        (NonConnectorInstantiationW13.generatedTableFamilyOfIndexedTableFamily
          T) := by
  rfl

/-- W20 closure source obtained from already supplied closure equations. -/
def closureSourceOfClosures
    {F : RoleHingedPeriodSearchFamily}
    (closure : GeneratedChainFamilyClosures (generatedChainFamily F)) :
    GeneratedChainClosureProducerW20.ClosureSource (generatedChainFamily F) :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures closure

/-- W20 closure source obtained from generated periods for the same family. -/
def closureSourceOfGeneratedPeriods
    {F : RoleHingedPeriodSearchFamily}
    (periods : GeneratedChainFamilyPeriods (generatedChainFamily F)) :
    GeneratedChainClosureProducerW20.ClosureSource (generatedChainFamily F) :=
  GeneratedChainClosureProducerW20.ClosureSource.ofGeneratedPeriods
    (generatedChainFamily F) periods

/-- W20 closure source obtained from generated period equations for the same
family. -/
def closureSourceOfPeriodEquations
    {F : RoleHingedPeriodSearchFamily}
    (periods : FamilyPeriodEquations (generatedChainFamily F)) :
    GeneratedChainClosureProducerW20.ClosureSource (generatedChainFamily F) :=
  GeneratedChainClosureProducerW20.ClosureSource.ofPeriodEquations
    (generatedChainFamily F) periods

/-- Assemble the W20 source fields from a generated non-connector table family
and closure equations for the same generated-chain family. -/
def sourceFieldsOfGeneratedTableFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F)
    (closure : GeneratedChainFamilyClosures (generatedChainFamily F)) :
    W20SourceFields where
  family := generatedChainFamily F
  closure :=
    GeneratedChainClosureProducerW20.generatedChainFamilyClosures
      (closureSourceOfClosures closure)
  reducedMetric := reducedMetricOfGeneratedTableFamily T

/-- The corresponding W19 input package from generated tables plus closures. -/
def inputPackageOfGeneratedTableFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F)
    (closure : GeneratedChainFamilyClosures (generatedChainFamily F)) :
    W19InputPackage :=
  (sourceFieldsOfGeneratedTableFamilyAndClosures T closure).toInputPackage

/-- Exact dependency statement: generated non-connector tables need only
closure equations for the same generated family to produce an input package. -/
theorem nonempty_inputPackage_of_generatedTableFamily_closures
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F) :
    Nonempty (GeneratedChainFamilyClosures (generatedChainFamily F)) ->
      Nonempty W19InputPackage := by
  intro hclosure
  exact hclosure.elim
    (fun closure =>
      ⟨inputPackageOfGeneratedTableFamilyAndClosures T closure⟩)

/-- Generated periods are exactly enough closure data after the W20 closure
producer converts them. -/
def inputPackageOfGeneratedTableFamilyAndGeneratedPeriods
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F)
    (periods : GeneratedChainFamilyPeriods (generatedChainFamily F)) :
    W19InputPackage :=
  (ExplicitClosedPlacementInputPackageW20.inputPackage_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (generatedChainFamily F)
    (GeneratedChainClosureProducerW20.generatedChainFamilyClosures
      (closureSourceOfGeneratedPeriods periods))
    (reducedMetricOfGeneratedTableFamily T))

/-- Generated period equations are exactly enough after the W20 closure
producer converts them to closure equations. -/
def inputPackageOfGeneratedTableFamilyAndPeriodEquations
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F)
    (periods : FamilyPeriodEquations (generatedChainFamily F)) :
    W19InputPackage :=
  (ExplicitClosedPlacementInputPackageW20.inputPackage_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (generatedChainFamily F)
    (GeneratedChainClosureProducerW20.generatedChainFamilyClosures
      (closureSourceOfPeriodEquations periods))
    (reducedMetricOfGeneratedTableFamily T))

/-- Exact dependency statement in period form: generated non-connector tables
plus generated periods produce an input package. -/
theorem nonempty_inputPackage_of_generatedTableFamily_periods
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F) :
    Nonempty (GeneratedChainFamilyPeriods (generatedChainFamily F)) ->
      Nonempty W19InputPackage := by
  intro hperiods
  exact hperiods.elim
    (fun periods =>
      ⟨inputPackageOfGeneratedTableFamilyAndGeneratedPeriods T periods⟩)

/-- Exact dependency statement in period-equation form. -/
theorem nonempty_inputPackage_of_generatedTableFamily_periodEquations
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F) :
    Nonempty (FamilyPeriodEquations (generatedChainFamily F)) ->
      Nonempty W19InputPackage := by
  intro hperiods
  exact hperiods.elim
    (fun periods =>
      ⟨inputPackageOfGeneratedTableFamilyAndPeriodEquations T periods⟩)

/-- The same closure-dependent input package, expressed through the W20
generated-chain family producer. -/
def familyProducerSourceFieldsOfGeneratedTableFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F)
    (closure : GeneratedChainFamilyClosures (generatedChainFamily F)) :
    GeneratedChainFamilyProducerW20.ExactBaseSourceFields where
  O := F.transitions.toFigure2TransitionObligations
  orientation := F.orientation
  closure := fun k hk => closure k hk
  separated := fun k hk => T.separated k hk
  transition_preserves_same_block_distances :=
    GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      F.transitions

/-- Input package obtained through `GeneratedChainFamilyProducerW20` from the
same table-plus-closure data. -/
def inputPackageViaFamilyProducerOfGeneratedTableFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F)
    (closure : GeneratedChainFamilyClosures (generatedChainFamily F)) :
    W19InputPackage :=
  (familyProducerSourceFieldsOfGeneratedTableFamilyAndClosures T closure).toInputPackage

/-- Indexed W13 table families inherit the same closure dependency. -/
def inputPackageOfIndexedTableFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (closure : GeneratedChainFamilyClosures (generatedChainFamily F)) :
    W19InputPackage :=
  inputPackageOfGeneratedTableFamilyAndClosures
    (NonConnectorInstantiationW13.generatedTableFamilyOfIndexedTableFamily T)
    closure

/-- W13 value-matrix families inherit the same closure dependency after their
generated table-family projection. -/
def inputPackageOfValueMatrixFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (M : ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily F)
    (closure : GeneratedChainFamilyClosures (generatedChainFamily F)) :
    W19InputPackage :=
  inputPackageOfGeneratedTableFamilyAndClosures
    (NonConnectorInstantiationW13.generatedTableFamilyOfValueMatrixFamily M)
    closure

/-- Concrete W13 value-matrix packages already carry period-search data, hence
their generated periods can be used as the missing closure source. -/
def inputPackageOfConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    W19InputPackage :=
  inputPackageOfGeneratedTableFamilyAndGeneratedPeriods
    (NonConnectorInstantiationW13.generatedTableFamilyOfConcreteValueMatrixFamily
      C)
    (fun k hk => C.periodSearch.generatedPeriod k hk)

/-- Concrete value-matrix packages therefore reach the W20 source-field
package without any extra closure assumption. -/
def sourceFieldsOfConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    W20SourceFields :=
  { family := generatedChainFamily C.toRoleHingedPeriodSearchFamily
    closure :=
      GeneratedChainClosureProducerW20.generatedChainFamilyClosures
        (closureSourceOfGeneratedPeriods
          (fun k hk => C.periodSearch.generatedPeriod k hk))
    reducedMetric :=
      ReducedMetricHypothesesProducerW20.ofConcreteValueMatrixFamily C }

/-- The direct concrete-value input package agrees definitionally with the
assembled W20 source fields. -/
theorem sourceFieldsOfConcreteValueMatrixFamily_toInputPackage
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    (sourceFieldsOfConcreteValueMatrixFamily C).toInputPackage =
      inputPackageOfConcreteValueMatrixFamily C := by
  rfl

end

end NonConnectorTableInputPackageW21
end PachToth
end ErdosProblems1066
