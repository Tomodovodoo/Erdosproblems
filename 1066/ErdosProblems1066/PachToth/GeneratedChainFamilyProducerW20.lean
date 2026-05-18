import ErdosProblems1066.PachToth.ExplicitClosedPlacementProducerW19
import ErdosProblems1066.PachToth.RoleHingeTransitionSearch

set_option autoImplicit false

/-!
# W20 generated-chain family producer

This module is a thin construction layer for the W19 explicit closed-placement
producer.  It builds the `GeneratedChainFamily` required by
`ExplicitClosedPlacementProducerW19.InputPackage` from smaller source fields
and records the precise blocker for the old role-hinged reduced-metric route:
connector-role realization is incompatible with arbitrary-source same-block
distance preservation.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedChainFamilyProducerW20

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev InputPackage :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev GeneratedChainFamily :=
  GeneratedSeparationInterface.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) :=
  ClosedPlacementClosure.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) :=
  GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses F

abbrev ExplicitClosedPlacementCertificateFamily :=
  ExplicitClosedPlacementProducerW19.ExplicitClosedPlacementCertificateFamily

/-- Raw source fields for the W19 reduced generated-chain route.  These are
exactly the data needed to build an `InputPackage`, with the
`GeneratedChainFamily` fields kept as ordinary functions. -/
structure SourceFields where
  O :
    forall (k : Nat), 0 < k ->
      Figure2Certificate.SameOppositeTransitionObligations
  base : forall (k : Nat), 0 < k -> LocalVertex -> R2
  orientation :
    forall (k : Nat) (_hk : 0 < k),
      Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        (O k hk) hk (base k hk) (orientation k hk)
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        (O k hk) hk (base k hk) (orientation k hk)
  base_same_block_isometry :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
        (base k hk)
  transition_preserves_same_block_distances :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        (O k hk)

namespace SourceFields

/-- Build the generated-chain family from raw source fields. -/
def family (S : SourceFields) : GeneratedChainFamily where
  O := S.O
  base := S.base
  orientation := S.orientation

@[simp]
theorem family_O (S : SourceFields) (k : Nat) (hk : 0 < k) :
    (S.family.O k hk) = S.O k hk :=
  rfl

@[simp]
theorem family_base (S : SourceFields) (k : Nat) (hk : 0 < k) :
    (S.family.base k hk) = S.base k hk :=
  rfl

@[simp]
theorem family_orientation (S : SourceFields)
    (k : Nat) (hk : 0 < k) :
    (S.family.orientation k hk) = S.orientation k hk :=
  rfl

/-- Algebraic closure equations for the generated-chain family. -/
def closures (S : SourceFields) : GeneratedChainFamilyClosures S.family :=
  fun k hk => S.closure k hk

/-- Reduced metric hypotheses for the generated-chain family. -/
def reducedMetric (S : SourceFields) :
    ReducedMetricHypotheses S.family where
  metric := fun k hk =>
    { separated := S.separated k hk
      base_same_block_isometry := S.base_same_block_isometry k hk
      transition_preserves_same_block_distances :=
        S.transition_preserves_same_block_distances k hk }

@[simp]
theorem reducedMetric_separated
    (S : SourceFields) (k : Nat) (hk : 0 < k) :
    ((S.reducedMetric).metric k hk).separated =
      S.separated k hk :=
  rfl

@[simp]
theorem reducedMetric_baseSameBlock
    (S : SourceFields) (k : Nat) (hk : 0 < k) :
    ((S.reducedMetric).metric k hk).base_same_block_isometry =
      S.base_same_block_isometry k hk :=
  rfl

@[simp]
theorem reducedMetric_transitionPreserves
    (S : SourceFields) (k : Nat) (hk : 0 < k) :
    ((S.reducedMetric).metric k hk).transition_preserves_same_block_distances =
      S.transition_preserves_same_block_distances k hk :=
  rfl

/-- The W19 input package produced from the raw source fields. -/
def toInputPackage (S : SourceFields) : InputPackage where
  family := S.family
  closure := S.closures
  metric := S.reducedMetric

/-- The exact-family facade produced from the same raw source fields. -/
def toExactFamilyHypotheses
    (S : SourceFields) :
    ExactFamilyClosure.ExactFamilyHypotheses :=
  S.toInputPackage.toExactFamilyHypotheses

/-- The explicit closed-placement certificate family produced by W19. -/
def explicitClosedPlacementCertificate
    (S : SourceFields) :
    ExplicitClosedPlacementCertificateFamily :=
  S.toInputPackage.explicitClosedPlacementCertificate

/-- Exact target obtained from the produced W19 input package. -/
theorem targetUpperConstructionFiveSixteen
    (S : SourceFields) :
    ExplicitClosedPlacementProducerW19.ExactTarget :=
  S.toInputPackage.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target obtained from the produced W19 input package. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (S : SourceFields) :
    ExplicitClosedPlacementProducerW19.ArbitraryTarget :=
  S.toInputPackage.targetUpperConstructionFiveSixteenArbitrary

end SourceFields

/-- Source fields specialized to a single transition package and the checked
exact local base block.  Compared with `SourceFields`, the base-block isometry
is discharged by `GeneratedMetricClosure`. -/
structure ExactBaseSourceFields where
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
  transition_preserves_same_block_distances :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      O

namespace ExactBaseSourceFields

/-- Forget exact-base specialization to the raw source-field interface. -/
def toSourceFields (S : ExactBaseSourceFields) : SourceFields where
  O := fun _ _ => S.O
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := S.orientation
  closure := fun k hk => S.closure k hk
  separated := fun k hk => S.separated k hk
  base_same_block_isometry := fun _ _ =>
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances := fun _ _ =>
    S.transition_preserves_same_block_distances

/-- Generated-chain family for the exact-base source fields. -/
def family (S : ExactBaseSourceFields) : GeneratedChainFamily :=
  S.toSourceFields.family

@[simp]
theorem family_O (S : ExactBaseSourceFields) (k : Nat) (hk : 0 < k) :
    S.family.O k hk = S.O :=
  rfl

@[simp]
theorem family_base (S : ExactBaseSourceFields) (k : Nat) (hk : 0 < k) :
    S.family.base k hk = BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem family_orientation
    (S : ExactBaseSourceFields) (k : Nat) (hk : 0 < k) :
    S.family.orientation k hk = S.orientation k hk :=
  rfl

/-- The W19 input package produced from exact-base source fields. -/
def toInputPackage (S : ExactBaseSourceFields) : InputPackage :=
  S.toSourceFields.toInputPackage

/-- The explicit certificate family produced from exact-base source fields. -/
def explicitClosedPlacementCertificate
    (S : ExactBaseSourceFields) :
    ExplicitClosedPlacementCertificateFamily :=
  S.toInputPackage.explicitClosedPlacementCertificate

theorem targetUpperConstructionFiveSixteen
    (S : ExactBaseSourceFields) :
    ExplicitClosedPlacementProducerW19.ExactTarget :=
  S.toInputPackage.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (S : ExactBaseSourceFields) :
    ExplicitClosedPlacementProducerW19.ArbitraryTarget :=
  S.toInputPackage.targetUpperConstructionFiveSixteenArbitrary

end ExactBaseSourceFields

/-- Connector-level role-hinge source fields specialized to the exact base.
The final field is the reduced-metric transition-preservation obligation; the
blocker theorems below show that this field is incompatible with the current
connector-role table. -/
structure ConnectorExactBaseSourceFields where
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
  transition_preserves_same_block_distances :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      transitions.toFigure2TransitionObligations

namespace ConnectorExactBaseSourceFields

/-- Forget connector-role facts to the exact-base W19 source fields. -/
def toExactBaseSourceFields
    (S : ConnectorExactBaseSourceFields) :
    ExactBaseSourceFields where
  O := S.transitions.toFigure2TransitionObligations
  orientation := S.orientation
  closure := S.closure
  separated := S.separated
  transition_preserves_same_block_distances :=
    S.transition_preserves_same_block_distances

/-- The W19 input package obtained if the connector-level source also supplied
the reduced same-block transition-preservation field. -/
def toInputPackage (S : ConnectorExactBaseSourceFields) : InputPackage :=
  S.toExactBaseSourceFields.toInputPackage

end ConnectorExactBaseSourceFields

/-- The reduced transition-preservation field is incompatible with a
connector-level role-hinge package. -/
theorem false_of_connectorTransitions_preserveSameBlockDistances
    (T :
      RoleHingeTransitionSearch.SameOppositeRoleHingeConnectorTransitionFacts)
    (hpreserve :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        T.toFigure2TransitionObligations) :
    False := by
  have hsame :
      HingedTransitionInterface.PreservesSameBlockDistances
        T.same.placeNext := by
    intro source u v
    simpa
      [GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances]
      using hpreserve OrientationData.BlockOrientation.same source u v
  exact
    RoleHingeTransitionSearch.false_of_preservesSameBlockDistances_and_realizes_role
      T.same hsame

/-- Therefore the connector-level exact-base W19 source fields are empty. -/
theorem false_of_connectorExactBaseSourceFields
    (S : ConnectorExactBaseSourceFields) :
    False :=
  false_of_connectorTransitions_preserveSameBlockDistances
    S.transitions S.transition_preserves_same_block_distances

theorem not_nonempty_connectorExactBaseSourceFields :
    Not (Nonempty ConnectorExactBaseSourceFields) := by
  intro h
  exact h.elim false_of_connectorExactBaseSourceFields

/-- Repackage a base role-hinge transition as the search-facing fact record,
so that the existing W19 contradiction applies to it. -/
def roleHingeTransitionFactsOfBase
    (T : BaseTransitionRealization.RoleHingeTransition) :
    RoleHingeTransitionSearch.RoleHingeTransitionFacts where
  placeNext := T.placeNext
  roleAngle := T.roleAngle
  realizes_role := T.realizes_role
  preserves_same_block_distances := T.preserves_same_block_distances

/-- The strong base role-hinge transition interface is inconsistent. -/
theorem false_of_baseRoleHingeTransition
    (T : BaseTransitionRealization.RoleHingeTransition) :
    False :=
  RoleHingeTransitionSearch.false_of_roleHingeTransitionFacts
    (roleHingeTransitionFactsOfBase T)

theorem not_nonempty_baseRoleHingeTransition :
    Not (Nonempty BaseTransitionRealization.RoleHingeTransition) := by
  intro h
  exact h.elim false_of_baseRoleHingeTransition

/-- The same/opposite strong role-hinge transition package used by the
reduced generated-metric closure route is empty. -/
theorem not_nonempty_roleHingeTransitions :
    Not (Nonempty GeneratedMetricClosure.RoleHingeTransitions) := by
  intro h
  exact h.elim (fun T => false_of_baseRoleHingeTransition T.same)

/-- Vacuous adapter from the strong role-hinged generated-closure family to
the W19 input package.  The following theorem records why this route cannot
currently supply an inhabitant. -/
def inputPackageOfRoleHingedGeneratedClosureFamily
    (F : GeneratedMetricClosure.RoleHingedGeneratedClosureFamily) :
    InputPackage where
  family := F.toGeneratedChainFamily
  closure := F.toGeneratedChainFamilyClosures
  metric := F.toReducedMetricHypotheses

theorem not_nonempty_roleHingedGeneratedClosureFamily :
    Not (Nonempty GeneratedMetricClosure.RoleHingedGeneratedClosureFamily) := by
  intro h
  exact h.elim (fun F => false_of_baseRoleHingeTransition F.transitions.same)

/-- Adapter from period-search plus cross-block lower bounds to the W19 input
package.  This is blocked by the same strong role-hinge transition field. -/
def inputPackageOfRoleHingedPeriodSearchCrossBlockFamily
    (F : ExactFamilyClosure.RoleHingedPeriodSearchCrossBlockFamily) :
    InputPackage :=
  inputPackageOfRoleHingedGeneratedClosureFamily
    F.toRoleHingedGeneratedClosureFamily

theorem not_nonempty_roleHingedPeriodSearchCrossBlockFamily :
    Not
      (Nonempty
        ExactFamilyClosure.RoleHingedPeriodSearchCrossBlockFamily) := by
  intro h
  exact h.elim (fun F => false_of_baseRoleHingeTransition F.transitions.same)

end

end GeneratedChainFamilyProducerW20
end PachToth
end ErdosProblems1066
