import ErdosProblems1066.PachToth.PeriodClosureSourceW21
import ErdosProblems1066.PachToth.NonConnectorTableInputPackageW21
import ErdosProblems1066.PachToth.ConcreteCrossBlockLowerTable

set_option autoImplicit false

/-!
# W22 concrete cross-block input-package handoff

This file connects the concrete cross-block data to the W19/W20 input-package
surface.  It deliberately stops at constructors for
`ExplicitClosedPlacementProducerW19.InputPackage` and
`GeneratedChainFamilyProducerW20.SourceFields`; it does not add a final
unconditional wrapper.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteCrossBlockInputPackageW22

open FiniteGraph

noncomputable section

abbrev W19InputPackage : Type :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev W20SourceFields : Type :=
  ExplicitClosedPlacementInputPackageW20.GeneratedFamilyClosureReducedMetricSourceFields

abbrev GeneratedSourceFields : Type :=
  GeneratedChainFamilyProducerW20.SourceFields

abbrev GeneratedChainFamily : Type :=
  ExplicitClosedPlacementProducerW19.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementProducerW19.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementProducerW19.ReducedMetricHypotheses F

abbrev ClosureSource
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.ClosureSource F

abbrev ExactFamilyHypotheses : Type :=
  ExactFamilyClosure.ExactFamilyHypotheses

abbrev ConcreteCrossBlockFamily : Type :=
  ConcretePeriodSearchFamily.ConcreteCrossBlockFamily

abbrev RoleHingedPeriodSearchFamily : Type :=
  NonConnectorTableInputPackageW21.RoleHingedPeriodSearchFamily

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  NonConnectorTableInputPackageW21.IndexedNonConnectorCrossBlockSqDistanceTableFamily F

abbrev NonConnectorLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily F

abbrev ConcreteNonConnectorLowerTableFamily : Prop :=
  ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily

/-! ## Generic exact-family and W19/W20 adapters -/

/-- Flatten a W19 input package to the raw W20 generated-chain source fields. -/
def sourceFieldsOfInputPackage
    (P : W19InputPackage) :
    GeneratedSourceFields where
  O := P.family.O
  base := P.family.base
  orientation := P.family.orientation
  closure := fun k hk => P.closure k hk
  separated := fun k hk => (P.metric.metric k hk).separated
  base_same_block_isometry := fun k hk =>
    (P.metric.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances := fun k hk =>
    (P.metric.metric k hk).transition_preserves_same_block_distances

@[simp]
theorem sourceFieldsOfInputPackage_toInputPackage
    (P : W19InputPackage) :
    (sourceFieldsOfInputPackage P).toInputPackage = P := by
  cases P
  rfl

/-- The W21 exact-family facade is exactly the W20 source-field package. -/
def w20SourceFieldsOfExactFamilyHypotheses
    (H : ExactFamilyHypotheses) :
    W20SourceFields where
  family := H.family
  closure := H.closure
  reducedMetric := H.metric

/-- Convert exact-family hypotheses to the W19 input package. -/
def inputPackageOfExactFamilyHypotheses
    (H : ExactFamilyHypotheses) :
    W19InputPackage :=
  (w20SourceFieldsOfExactFamilyHypotheses H).toInputPackage

@[simp]
theorem inputPackageOfExactFamilyHypotheses_toExactFamilyHypotheses
    (H : ExactFamilyHypotheses) :
    (inputPackageOfExactFamilyHypotheses H).toExactFamilyHypotheses = H := by
  cases H
  rfl

/-- Convert exact-family hypotheses to the raw W20 generated-chain fields. -/
def sourceFieldsOfExactFamilyHypotheses
    (H : ExactFamilyHypotheses) :
    GeneratedSourceFields :=
  sourceFieldsOfInputPackage (inputPackageOfExactFamilyHypotheses H)

/-! ## Concrete cross-block families -/

/-- The W21 exact-family package associated with concrete cross-block data. -/
def exactFamilyHypothesesOfConcreteCrossBlockFamily
    (F : ConcreteCrossBlockFamily) :
    ExactFamilyHypotheses :=
  PeriodClosureSourceW21.exactFamilyHypothesesOfConcreteCrossBlockFamily F

/-- Concrete cross-block data, with period closure from W21, gives W20 source
fields. -/
def w20SourceFieldsOfConcreteCrossBlockFamily
    (F : ConcreteCrossBlockFamily) :
    W20SourceFields :=
  w20SourceFieldsOfExactFamilyHypotheses
    (exactFamilyHypothesesOfConcreteCrossBlockFamily F)

/-- Concrete cross-block data, with period closure from W21, gives the W19
input package. -/
def inputPackageOfConcreteCrossBlockFamily
    (F : ConcreteCrossBlockFamily) :
    W19InputPackage :=
  (w20SourceFieldsOfConcreteCrossBlockFamily F).toInputPackage

/-- The same concrete data flattened to `GeneratedChainFamilyProducerW20`.
-/
def sourceFieldsOfConcreteCrossBlockFamily
    (F : ConcreteCrossBlockFamily) :
    GeneratedSourceFields :=
  sourceFieldsOfInputPackage (inputPackageOfConcreteCrossBlockFamily F)

@[simp]
theorem inputPackageOfConcreteCrossBlockFamily_toExactFamilyHypotheses
    (F : ConcreteCrossBlockFamily) :
    (inputPackageOfConcreteCrossBlockFamily F).toExactFamilyHypotheses =
      exactFamilyHypothesesOfConcreteCrossBlockFamily F := by
  rfl

/-! ## Concrete lower-table route through the W21 non-connector table handoff -/

/-- Concrete non-connector lower tables also assemble to the explicit
`ConcreteCrossBlockFamily` shape. -/
def concreteCrossBlockFamilyOfConcreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    ConcreteCrossBlockFamily where
  periodSearch := C.periodSearch
  lower := C.toCrossBlockLowerBounds.lower
  lower_ge_one := C.toCrossBlockLowerBounds.lower_ge_one
  lower_bound := C.toCrossBlockLowerBounds.lower_bound

/-- W20 source fields from an indexed non-connector table family once the
period closure for the same generated family is supplied. -/
def w20SourceFieldsOfIndexedTableFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (closure :
      GeneratedChainFamilyClosures
        (NonConnectorTableInputPackageW21.generatedChainFamily F)) :
    W20SourceFields where
  family := NonConnectorTableInputPackageW21.generatedChainFamily F
  closure := closure
  reducedMetric :=
    NonConnectorTableInputPackageW21.reducedMetricOfIndexedTableFamily T

/-- W19 input package from an indexed non-connector table family plus the
period closure for the same generated family. -/
def inputPackageOfIndexedTableFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (closure :
      GeneratedChainFamilyClosures
        (NonConnectorTableInputPackageW21.generatedChainFamily F)) :
    W19InputPackage :=
  (w20SourceFieldsOfIndexedTableFamilyAndClosures T closure).toInputPackage

/-- Raw W20 source fields from an indexed non-connector table family plus
closure. -/
def sourceFieldsOfIndexedTableFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (closure :
      GeneratedChainFamilyClosures
        (NonConnectorTableInputPackageW21.generatedChainFamily F)) :
    GeneratedSourceFields :=
  sourceFieldsOfInputPackage
    (inputPackageOfIndexedTableFamilyAndClosures T closure)

/-- Lower-table wrappers inherit the W21 indexed-table input-package route. -/
def inputPackageOfNonConnectorLowerTableFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F)
    (closure :
      GeneratedChainFamilyClosures
        (NonConnectorTableInputPackageW21.generatedChainFamily F)) :
    W19InputPackage :=
  NonConnectorTableInputPackageW21.inputPackageOfIndexedTableFamilyAndClosures
    T.toNonConnectorSqDistanceTableFamily closure

/-- Lower-table wrappers inherit the raw W20 source-field route. -/
def sourceFieldsOfNonConnectorLowerTableFamilyAndClosures
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F)
    (closure :
      GeneratedChainFamilyClosures
        (NonConnectorTableInputPackageW21.generatedChainFamily F)) :
    GeneratedSourceFields :=
  sourceFieldsOfInputPackage
    (inputPackageOfNonConnectorLowerTableFamilyAndClosures T closure)

/-- The same lower-table route, with the period closure packaged as a W20
closure source. -/
def inputPackageOfNonConnectorLowerTableFamilyAndClosureSource
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F)
    (source :
      ClosureSource (NonConnectorTableInputPackageW21.generatedChainFamily F)) :
    W19InputPackage :=
  inputPackageOfNonConnectorLowerTableFamilyAndClosures T
    source.toGeneratedChainFamilyClosures

/-- Precise remaining dependency for a bare lower-table family: the only extra
field needed for W19 is closure of the same generated family. -/
theorem nonempty_inputPackage_of_nonConnectorLowerTableFamily_closures
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F) :
    Nonempty
        (GeneratedChainFamilyClosures
          (NonConnectorTableInputPackageW21.generatedChainFamily F)) ->
      Nonempty W19InputPackage := by
  intro hclosure
  cases hclosure with
  | intro closure =>
      exact
        Nonempty.intro
          (inputPackageOfNonConnectorLowerTableFamilyAndClosures T closure)

/-- The same dependency stated for raw W20 generated-chain source fields. -/
theorem nonempty_sourceFields_of_nonConnectorLowerTableFamily_closures
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F) :
    Nonempty
        (GeneratedChainFamilyClosures
          (NonConnectorTableInputPackageW21.generatedChainFamily F)) ->
      Nonempty GeneratedSourceFields := by
  intro hclosure
  cases hclosure with
  | intro closure =>
      exact
        Nonempty.intro
          (sourceFieldsOfNonConnectorLowerTableFamilyAndClosures T closure)

/-- Period-search closure carried by a concrete lower-table package, in the
generated-family spelling used by `NonConnectorTableInputPackageW21`. -/
def closuresOfConcreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedChainFamilyClosures
      (NonConnectorTableInputPackageW21.generatedChainFamily
        C.periodSearch.toRoleHingedPeriodSearchFamily) := by
  intro k hk
  exact
    (PeriodClosureSourceW21.sourceOfConcretePeriodSearchData C.periodSearch)
      |>.closure k hk

/-- The carried period-search closure as a W20 closure source. -/
def closureSourceOfConcreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    ClosureSource
      (NonConnectorTableInputPackageW21.generatedChainFamily
        C.periodSearch.toRoleHingedPeriodSearchFamily) :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures
    (closuresOfConcreteNonConnectorLowerTableFamily C)

/-- Concrete non-connector lower-table data gives the W19 input package via
the W21 non-connector table handoff and the carried period closure. -/
def inputPackageOfConcreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    W19InputPackage :=
  inputPackageOfNonConnectorLowerTableFamilyAndClosureSource
    (F := C.periodSearch.toRoleHingedPeriodSearchFamily)
    C.tables (closureSourceOfConcreteNonConnectorLowerTableFamily C)

/-- Concrete non-connector lower-table data flattened to
`GeneratedChainFamilyProducerW20.SourceFields`. -/
def sourceFieldsOfConcreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedSourceFields :=
  sourceFieldsOfInputPackage
    (inputPackageOfConcreteNonConnectorLowerTableFamily C)

end

end ConcreteCrossBlockInputPackageW22
end PachToth
end ErdosProblems1066
