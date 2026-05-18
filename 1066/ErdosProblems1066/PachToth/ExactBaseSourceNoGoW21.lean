import ErdosProblems1066.PachToth.GeneratedChainFamilyProducerW20

set_option autoImplicit false

/-!
# W21 exact-base source no-go

This module sharpens the W20 no-go around exact-base role-hinge source
packages.  The obstruction is not the exact base and not the connector-role
facts by themselves.  The incompatible field is the reduced-metric
transition-preservation hypothesis, because it asks the connector-role
transition to preserve same-block distances for every arbitrary source.

The viable replacement is therefore stated explicitly: keep the exact base
and connector-role facts, but provide full generated same-block metric data
for each generated chain instead of the all-source transition-preservation
field.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactBaseSourceNoGoW21

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev InputPackage :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev ConnectorTransitions :=
  RoleHingeTransitionSearch.SameOppositeRoleHingeConnectorTransitionFacts

abbrev StrongRoleHingeTransitions :=
  GeneratedMetricClosure.RoleHingeTransitions

abbrev ExactBaseSourceFields :=
  GeneratedChainFamilyProducerW20.ExactBaseSourceFields

abbrev ConnectorExactBaseSourceFields :=
  GeneratedChainFamilyProducerW20.ConnectorExactBaseSourceFields

abbrev GeneratedChainFamily :=
  GeneratedSeparationInterface.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) :=
  ClosedPlacementClosure.GeneratedChainFamilyClosures F

abbrev FullMetricHypotheses
    (F : GeneratedChainFamily) :=
  GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F

/-! ## Stronger connector-role contradictions -/

/-- A single reduced metric hypothesis for connector-role transitions already
contains the impossible all-source same-block transition-preservation field. -/
theorem false_of_connector_reducedMetricHypotheses
    (T : ConnectorTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    False :=
  GeneratedChainFamilyProducerW20.false_of_connectorTransitions_preserveSameBlockDistances
    T H.transition_preserves_same_block_distances

/-- One-block exact-base connector packages with reduced metric data are
already inconsistent, before any family-level route is considered. -/
structure ConnectorExactBaseReducedMetricAt (k : Nat) (hk : 0 < k) where
  transitions : ConnectorTransitions
  orientation : Fin k -> OrientationData.BlockOrientation
  closure :
    PeriodInterface.GeneratedClosureEquation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
  reducedMetric :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation

namespace ConnectorExactBaseReducedMetricAt

theorem false
    {k : Nat} {hk : 0 < k}
    (S : ConnectorExactBaseReducedMetricAt k hk) :
    False :=
  false_of_connector_reducedMetricHypotheses
    S.transitions hk S.orientation S.reducedMetric

instance isEmpty
    {k : Nat} {hk : 0 < k} :
    IsEmpty (ConnectorExactBaseReducedMetricAt k hk) where
  false := false

end ConnectorExactBaseReducedMetricAt

/-- Even adding full generated metric data does not make the old reduced
transition-preservation field consistent with connector-role facts. -/
structure ConnectorFullMetricPlusReducedPreservationAt
    (k : Nat) (hk : 0 < k) where
  transitions : ConnectorTransitions
  orientation : Fin k -> OrientationData.BlockOrientation
  closure :
    PeriodInterface.GeneratedClosureEquation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
  fullMetric :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
  transition_preserves_same_block_distances :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      transitions.toFigure2TransitionObligations

namespace ConnectorFullMetricPlusReducedPreservationAt

theorem false
    {k : Nat} {hk : 0 < k}
    (S : ConnectorFullMetricPlusReducedPreservationAt k hk) :
    False :=
  GeneratedChainFamilyProducerW20.false_of_connectorTransitions_preserveSameBlockDistances
    S.transitions S.transition_preserves_same_block_distances

instance isEmpty
    {k : Nat} {hk : 0 < k} :
    IsEmpty (ConnectorFullMetricPlusReducedPreservationAt k hk) where
  false := false

end ConnectorFullMetricPlusReducedPreservationAt

/-- The W20 family-level connector exact-base source package is empty for the
same local reason. -/
theorem false_of_connectorExactBaseSourceFields
    (S : ConnectorExactBaseSourceFields) :
    False :=
  GeneratedChainFamilyProducerW20.false_of_connectorExactBaseSourceFields S

theorem not_nonempty_connectorExactBaseSourceFields :
    Not (Nonempty ConnectorExactBaseSourceFields) := by
  intro h
  exact h.elim false_of_connectorExactBaseSourceFields

instance connectorExactBaseSourceFields_isEmpty :
    IsEmpty ConnectorExactBaseSourceFields where
  false := false_of_connectorExactBaseSourceFields

/-- Supplying the W19 input package alongside a connector exact-base source
does not help: the connector source field itself is contradictory. -/
structure ConnectorExactBaseInputAttempt where
  source : ConnectorExactBaseSourceFields
  input : InputPackage
  input_eq : input = source.toInputPackage

theorem false_of_connectorExactBaseInputAttempt
    (A : ConnectorExactBaseInputAttempt) :
    False :=
  false_of_connectorExactBaseSourceFields A.source

theorem not_nonempty_connectorExactBaseInputAttempt :
    Not (Nonempty ConnectorExactBaseInputAttempt) := by
  intro h
  exact h.elim false_of_connectorExactBaseInputAttempt

/-! ## Strong role-hinge exact-base packages are empty even earlier -/

/-- Any strong role-hinge transition contains the all-source same-block field,
so it is inconsistent before closure and separation data enter. -/
theorem false_of_strongRoleHingeTransitions
    (T : StrongRoleHingeTransitions) :
    False :=
  GeneratedChainFamilyProducerW20.false_of_baseRoleHingeTransition T.same

theorem not_nonempty_strongRoleHingeTransitions :
    Not (Nonempty StrongRoleHingeTransitions) := by
  intro h
  exact h.elim false_of_strongRoleHingeTransitions

/-- A strong role-hinge exact-base family package cannot be inhabited. -/
structure StrongRoleHingeExactBaseFamilyAttempt where
  transitions : StrongRoleHingeTransitions
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

theorem false_of_strongRoleHingeExactBaseFamilyAttempt
    (S : StrongRoleHingeExactBaseFamilyAttempt) :
    False :=
  false_of_strongRoleHingeTransitions S.transitions

theorem not_nonempty_strongRoleHingeExactBaseFamilyAttempt :
    Not (Nonempty StrongRoleHingeExactBaseFamilyAttempt) := by
  intro h
  exact h.elim false_of_strongRoleHingeExactBaseFamilyAttempt

theorem not_nonempty_roleHingedGeneratedClosureFamily :
    Not (Nonempty GeneratedMetricClosure.RoleHingedGeneratedClosureFamily) :=
  GeneratedChainFamilyProducerW20.not_nonempty_roleHingedGeneratedClosureFamily

/-! ## The viable exact-base alternative -/

/-- Exact-base source fields using full generated metric hypotheses for each
chain.  This is the viable replacement for the reduced exact-base source
field when connector-role transitions are used: no arbitrary-source
transition-preservation field appears. -/
structure ExactBaseFullMetricSourceFields where
  O : Figure2Certificate.SameOppositeTransitionObligations
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        O hk BaseTransitionRealization.exactBase (orientation k hk)
  metric :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk BaseTransitionRealization.exactBase (orientation k hk)

namespace ExactBaseFullMetricSourceFields

def family
    (S : ExactBaseFullMetricSourceFields) :
    GeneratedChainFamily where
  O := fun _ _ => S.O
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := S.orientation

@[simp]
theorem family_O
    (S : ExactBaseFullMetricSourceFields) (k : Nat) (hk : 0 < k) :
    S.family.O k hk = S.O :=
  rfl

@[simp]
theorem family_base
    (S : ExactBaseFullMetricSourceFields) (k : Nat) (hk : 0 < k) :
    S.family.base k hk = BaseTransitionRealization.exactBase :=
  rfl

def closures
    (S : ExactBaseFullMetricSourceFields) :
    GeneratedChainFamilyClosures S.family :=
  fun k hk => S.closure k hk

def metricHypotheses
    (S : ExactBaseFullMetricSourceFields) :
    FullMetricHypotheses S.family where
  metric := fun k hk => S.metric k hk

/-- Full exact-base metric source fields give the exact Pach-Toth target. -/
theorem targetUpperConstructionFiveSixteen
    (S : ExactBaseFullMetricSourceFields) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteen_of_generatedClosure_family
      S.family S.closures S.metricHypotheses

/-- The same viable source also gives the arbitrary-vertex target through the
existing exact-to-arbitrary closure. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (S : ExactBaseFullMetricSourceFields) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (S.targetUpperConstructionFiveSixteen)

end ExactBaseFullMetricSourceFields

/-- Connector-role version of the viable exact-base source.  The metric field
is full generated same-block metric data, not reduced transition preservation. -/
structure ConnectorExactBaseFullMetricSourceFields where
  transitions : ConnectorTransitions
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)
  metric :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)

namespace ConnectorExactBaseFullMetricSourceFields

def toExactBaseFullMetricSourceFields
    (S : ConnectorExactBaseFullMetricSourceFields) :
    ExactBaseFullMetricSourceFields where
  O := S.transitions.toFigure2TransitionObligations
  orientation := S.orientation
  closure := S.closure
  metric := S.metric

def toConnectorGeneratedClosureSearchFamily
    (S : ConnectorExactBaseFullMetricSourceFields) :
    RoleHingeTransitionSearch.ConnectorGeneratedClosureSearchFamily where
  transitions := S.transitions
  orientation := S.orientation
  closure := S.closure
  metric := S.metric

theorem targetUpperConstructionFiveSixteen
    (S : ConnectorExactBaseFullMetricSourceFields) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen := by
  exact
    S.toExactBaseFullMetricSourceFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteen_via_connectorSearchFamily
    (S : ConnectorExactBaseFullMetricSourceFields) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen := by
  exact
    S.toConnectorGeneratedClosureSearchFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (S : ConnectorExactBaseFullMetricSourceFields) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (S.targetUpperConstructionFiveSixteen)

end ConnectorExactBaseFullMetricSourceFields

/-- Precise W21 route statement: connector-role exact-base sources must use
full generated metric hypotheses per chain; the reduced transition-preserve
source package is empty. -/
abbrev ViableConnectorExactBaseAlternative :=
  ConnectorExactBaseFullMetricSourceFields

theorem viableConnectorExactBaseAlternative_target
    (S : ViableConnectorExactBaseAlternative) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen :=
  S.targetUpperConstructionFiveSixteen

theorem viableConnectorExactBaseAlternative_arbitraryTarget
    (S : ViableConnectorExactBaseAlternative) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  S.targetUpperConstructionFiveSixteenArbitrary

end

end ExactBaseSourceNoGoW21
end PachToth
end ErdosProblems1066
