import ErdosProblems1066.PachToth.GeneratedChainFamilyProducerW20
import ErdosProblems1066.PachToth.LargeKClosedPlacementSourceW20
import ErdosProblems1066.PachToth.ClosedPlacementUnconditionalAttemptW20

set_option autoImplicit false

/-!
# W21 source-field assembly

This file isolates the source-field question for the W20 generated-chain
producer.  A W19 input package already contains exactly the flattened fields
needed by `GeneratedChainFamilyProducerW20.SourceFields`; the stronger
exact-base route additionally asks for a fixed transition package and the
exact checked base block.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SourceFieldsAssemblyW21

open FiniteGraph

noncomputable section

abbrev InputPackage :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev SourceFields :=
  GeneratedChainFamilyProducerW20.SourceFields

abbrev ExactBaseSourceFields :=
  GeneratedChainFamilyProducerW20.ExactBaseSourceFields

abbrev ConnectorExactBaseSourceFields :=
  GeneratedChainFamilyProducerW20.ConnectorExactBaseSourceFields

abbrev GeneratedChainData :=
  ClosedPlacementUnconditionalAttemptW20.GeneratedChainData

abbrev GeneratedChainFamily :=
  GeneratedChainFamilyProducerW20.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) :=
  GeneratedChainFamilyProducerW20.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) :=
  GeneratedChainFamilyProducerW20.ReducedMetricHypotheses F

abbrev AllPositiveNonConnectorFields :=
  LargeKClosedPlacementSourceW20.AllPositiveNonConnectorFields

/-- Flatten a W19 package into the raw W20 source fields. -/
def sourceFieldsOfInputPackage
    (P : InputPackage) :
    SourceFields where
  O := fun k hk => P.family.O k hk
  base := fun k hk => P.family.base k hk
  orientation := fun k hk => P.family.orientation k hk
  closure := fun k hk => P.closure k hk
  separated := fun k hk => (P.metric.metric k hk).separated
  base_same_block_isometry := fun k hk =>
    (P.metric.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances := fun k hk =>
    (P.metric.metric k hk).transition_preserves_same_block_distances

@[simp]
theorem sourceFieldsOfInputPackage_family_O
    (P : InputPackage) (k : Nat) (hk : 0 < k) :
    (sourceFieldsOfInputPackage P).family.O k hk = P.family.O k hk :=
  rfl

@[simp]
theorem sourceFieldsOfInputPackage_family_base
    (P : InputPackage) (k : Nat) (hk : 0 < k) :
    (sourceFieldsOfInputPackage P).family.base k hk =
      P.family.base k hk :=
  rfl

@[simp]
theorem sourceFieldsOfInputPackage_family_orientation
    (P : InputPackage) (k : Nat) (hk : 0 < k) :
    (sourceFieldsOfInputPackage P).family.orientation k hk =
      P.family.orientation k hk :=
  rfl

/-- The W20 source-field interface is equivalent to the W19 input package. -/
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

/-- In the existing W20 accounting, source fields are present exactly when
the generated-chain data package is present. -/
theorem nonempty_sourceFields_iff_generatedChainData :
    Nonempty SourceFields <-> Nonempty GeneratedChainData := by
  exact
    Iff.trans nonempty_sourceFields_iff_inputPackage
      ClosedPlacementUnconditionalAttemptW20.nonempty_generatedChainData_iff_w19InputPackage.symm

/-- If the generated-chain data package is absent, the raw W20 source fields
are absent as well. -/
theorem no_sourceFields_without_generatedChainData
    (hmissing : Not (Nonempty GeneratedChainData)) :
    Not (Nonempty SourceFields) := by
  intro h
  exact hmissing (nonempty_sourceFields_iff_generatedChainData.1 h)

/-- Already assembled large-`K0 = 1` all-positive data gives raw source
fields through the compiled W20 large-source package. -/
def sourceFieldsOfAllPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields) :
    SourceFields :=
  sourceFieldsOfInputPackage
    (LargeKClosedPlacementSourceW20.inputPackageOfAllPositiveNonConnectorFields
      C)

/-- The same compiled all-positive data also has the exact-base shape:
fixed transition obligations and the checked base block. -/
def exactBaseSourceFieldsOfAllPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields) :
    ExactBaseSourceFields where
  O := C.transitions.toFigure2TransitionObligations
  orientation := C.orientation
  closure := fun k hk => C.period.closure k hk
  separated := fun k hk => (C.reducedMetricHypotheses k hk).separated
  transition_preserves_same_block_distances :=
    GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      C.transitions

/-- The all-positive exact-base assembly is itself blocked by the compiled
role-hinge transition contradiction. -/
theorem false_of_allPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields) :
    False :=
  GeneratedChainFamilyProducerW20.not_nonempty_roleHingeTransitions
    (Nonempty.intro C.transitions)

theorem not_nonempty_allPositiveNonConnectorFields :
    Not (Nonempty AllPositiveNonConnectorFields) := by
  intro h
  exact h.elim false_of_allPositiveNonConnectorFields

/-! ## Exact-base decomposition -/

/-- Exact-base source fields before the final same-block transition-preserving
field is attached. -/
structure ExactBaseCoreFields where
  O : Figure2Certificate.SameOppositeTransitionObligations
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        O hk BaseTransitionRealization.exactBase (orientation k hk)
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk BaseTransitionRealization.exactBase (orientation k hk)

namespace ExactBaseCoreFields

def ofExactBaseSourceFields
    (S : ExactBaseSourceFields) :
    ExactBaseCoreFields where
  O := S.O
  orientation := S.orientation
  closure := S.closure
  separated := S.separated

def toExactBaseSourceFields
    (C : ExactBaseCoreFields)
    (hpreserve :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        C.O) :
    ExactBaseSourceFields where
  O := C.O
  orientation := C.orientation
  closure := C.closure
  separated := C.separated
  transition_preserves_same_block_distances := hpreserve

end ExactBaseCoreFields

/-- Sharp exact-base equivalence: after closure and separation are known for
the exact base, the remaining field is precisely same-block preservation by
the selected transitions. -/
theorem nonempty_exactBaseSourceFields_iff_core_with_transitionPreserves :
    Nonempty ExactBaseSourceFields <->
      Exists fun C : ExactBaseCoreFields =>
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          C.O := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro S =>
            exact
              ⟨ExactBaseCoreFields.ofExactBaseSourceFields S,
                S.transition_preserves_same_block_distances⟩)
      (fun h => by
        cases h with
        | intro C hpreserve =>
            exact
              Nonempty.intro
                (ExactBaseCoreFields.toExactBaseSourceFields C hpreserve))

/-- A W19 input package has exact-base shape when its generated family uses a
single transition package and the checked base block for every positive
length. -/
structure ExactBaseInputPackage where
  package : InputPackage
  O : Figure2Certificate.SameOppositeTransitionObligations
  O_eq : forall (k : Nat) (hk : 0 < k), package.family.O k hk = O
  base_eq :
    forall (k : Nat) (hk : 0 < k),
      package.family.base k hk = BaseTransitionRealization.exactBase

namespace ExactBaseInputPackage

def toExactBaseSourceFields
    (P : ExactBaseInputPackage) :
    ExactBaseSourceFields where
  O := P.O
  orientation := P.package.family.orientation
  closure := by
    intro k hk
    simpa [P.O_eq k hk, P.base_eq k hk] using P.package.closure k hk
  separated := by
    intro k hk
    simpa [P.O_eq k hk, P.base_eq k hk] using
      (P.package.metric.metric k hk).separated
  transition_preserves_same_block_distances := by
    simpa [P.O_eq 1 (by decide : 0 < 1)] using
      (P.package.metric.metric 1 (by decide : 0 < 1)).transition_preserves_same_block_distances

end ExactBaseInputPackage

def exactBaseInputPackageOfExactBaseSourceFields
    (S : ExactBaseSourceFields) :
    ExactBaseInputPackage where
  package := S.toInputPackage
  O := S.O
  O_eq := by
    intro _k _hk
    rfl
  base_eq := by
    intro _k _hk
    rfl

/-- Exact-base source fields are equivalent to a W19 package whose family has
the exact-base shape. -/
theorem nonempty_exactBaseSourceFields_iff_exactBaseInputPackage :
    Nonempty ExactBaseSourceFields <->
      Nonempty ExactBaseInputPackage := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro S =>
            exact Nonempty.intro
              (exactBaseInputPackageOfExactBaseSourceFields S))
      (fun h => by
        cases h with
        | intro P =>
            exact Nonempty.intro P.toExactBaseSourceFields)

/-! ## Connector exact-base decomposition -/

/-- Connector exact-base fields before the reduced same-block preservation
field is added. -/
structure ConnectorExactBaseCoreFields where
  transitions :
    RoleHingeTransitionSearch.SameOppositeRoleHingeConnectorTransitionFacts
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)

namespace ConnectorExactBaseCoreFields

def ofConnectorExactBaseSourceFields
    (S : ConnectorExactBaseSourceFields) :
    ConnectorExactBaseCoreFields where
  transitions := S.transitions
  orientation := S.orientation
  closure := S.closure
  separated := S.separated

def toConnectorExactBaseSourceFields
    (C : ConnectorExactBaseCoreFields)
    (hpreserve :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        C.transitions.toFigure2TransitionObligations) :
    ConnectorExactBaseSourceFields where
  transitions := C.transitions
  orientation := C.orientation
  closure := C.closure
  separated := C.separated
  transition_preserves_same_block_distances := hpreserve

end ConnectorExactBaseCoreFields

/-- Connector exact-base source fields are exactly connector exact-base core
fields plus the same-block preservation field. -/
theorem
    nonempty_connectorExactBaseSourceFields_iff_core_with_transitionPreserves :
    Nonempty ConnectorExactBaseSourceFields <->
      Exists fun C : ConnectorExactBaseCoreFields =>
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          C.transitions.toFigure2TransitionObligations := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro S =>
            exact
              ⟨ConnectorExactBaseCoreFields.ofConnectorExactBaseSourceFields S,
                S.transition_preserves_same_block_distances⟩)
      (fun h => by
        cases h with
        | intro C hpreserve =>
            exact
              Nonempty.intro
                (ConnectorExactBaseCoreFields.toConnectorExactBaseSourceFields
                  C hpreserve))

/-- For connector-role data, the final same-block preservation field is
inconsistent with the compiled role realization facts. -/
theorem false_of_connectorExactBaseCoreFields_transitionPreserves
    (C : ConnectorExactBaseCoreFields)
    (hpreserve :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        C.transitions.toFigure2TransitionObligations) :
    False :=
  GeneratedChainFamilyProducerW20.false_of_connectorTransitions_preserveSameBlockDistances
    C.transitions hpreserve

theorem not_exists_connectorExactBaseCoreFields_transitionPreserves :
    Not
      (Exists fun C : ConnectorExactBaseCoreFields =>
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          C.transitions.toFigure2TransitionObligations) := by
  intro h
  cases h with
  | intro C hpreserve =>
      exact false_of_connectorExactBaseCoreFields_transitionPreserves
        C hpreserve

theorem not_nonempty_connectorExactBaseSourceFields :
    Not (Nonempty ConnectorExactBaseSourceFields) := by
  intro h
  exact
    not_exists_connectorExactBaseCoreFields_transitionPreserves
      (nonempty_connectorExactBaseSourceFields_iff_core_with_transitionPreserves.1
        h)

end

end SourceFieldsAssemblyW21
end PachToth
end ErdosProblems1066
