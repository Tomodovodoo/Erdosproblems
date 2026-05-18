import ErdosProblems1066.PachToth.ExactBaseFullMetricSourceInhabitationW22
import ErdosProblems1066.PachToth.GeneratedMetricClosure
import ErdosProblems1066.PachToth.GeneratedPointDistanceFacts
import ErdosProblems1066.PachToth.BaseTransitionRealization
import ErdosProblems1066.PachToth.RemainingSeparationInhabitationW22

set_option autoImplicit false

/-!
# W23 exact-base full-metric concrete bridge

This file keeps the W22 viable exact-base route on the full-metric side:
separation is generated-point separation, and same-block control is supplied
directly on the generated orbit.  The connector route below does not add the
old reduced all-source transition-preservation field.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactBaseFullMetricConcreteW23

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev ExactBaseFullMetricSourceFields :=
  ExactBaseFullMetricSourceInhabitationW22.ExactBaseFullMetricSourceFields

abbrev ConnectorExactBaseFullMetricSourceFields :=
  ExactBaseFullMetricSourceInhabitationW22.ConnectorExactBaseFullMetricSourceFields

abbrev ExactBaseFullMetricCoreFields :=
  ExactBaseFullMetricSourceInhabitationW22.ExactBaseFullMetricCoreFields

abbrev ConnectorExactBaseFullMetricCoreFields :=
  ExactBaseFullMetricSourceInhabitationW22.ConnectorExactBaseFullMetricCoreFields

abbrev RemainingFullMetricField :=
  ExactBaseFullMetricSourceInhabitationW22.RemainingFullMetricField

abbrev RemainingSeparationField :=
  ExactBaseFullMetricSourceInhabitationW22.RemainingSeparationField

abbrev RemainingSameBlockField :=
  ExactBaseFullMetricSourceInhabitationW22.RemainingSameBlockField

abbrev ConnectorRemainingFullMetricField :=
  ExactBaseFullMetricSourceInhabitationW22.ConnectorRemainingFullMetricField

abbrev ConnectorRemainingSeparationField :=
  ExactBaseFullMetricSourceInhabitationW22.ConnectorRemainingSeparationField

abbrev ConnectorRemainingSameBlockField :=
  ExactBaseFullMetricSourceInhabitationW22.ConnectorRemainingSameBlockField

abbrev ExactLocalPreservation
    (O : Figure2Certificate.SameOppositeTransitionObligations) : Prop :=
  GeneratedMetricClosure.GeneratedTransitionsPreserveExactLocalSqDistances O

abbrev ConnectorExactLocalPreservation
    (C : ConnectorExactBaseFullMetricCoreFields) : Prop :=
  ExactLocalPreservation C.transitions.toFigure2TransitionObligations

abbrev RoleHingedPeriodSearchFamily :=
  RemainingSeparationInhabitationW22.RoleHingedPeriodSearchFamily

abbrev RoleHingedRemainingSeparationField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  RemainingSeparationInhabitationW22.RemainingSeparationField F

/-! ## Pointwise square-distance separation -/

abbrev GeneratedSqDistSeparation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne (i, u) (j, v) ->
      1 <=
        GeneratedPointDistanceFacts.generatedPointSqDist
          O hk base orientation i u j v

def generatedGlobalSeparationOfSqDistSeparation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (sqSeparated : GeneratedSqDistSeparation O hk base orientation) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  exact
    GeneratedPointDistanceFacts.one_le_generatedPoint_eucDist_of_one_le_sqDist
      (sqSeparated i u j v hne)

abbrev RemainingSqDistSeparationField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedSqDistSeparation C.O hk BaseTransitionRealization.exactBase
      (C.orientation k hk)

def remainingSeparationOfSqDistSeparation
    (C : ExactBaseFullMetricCoreFields)
    (sqSeparated : RemainingSqDistSeparationField C) :
    RemainingSeparationField C := by
  intro k hk
  exact
    generatedGlobalSeparationOfSqDistSeparation
      C.O hk BaseTransitionRealization.exactBase
      (C.orientation k hk) (sqSeparated k hk)

abbrev ConnectorRemainingSqDistSeparationField
    (C : ConnectorExactBaseFullMetricCoreFields) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedSqDistSeparation C.transitions.toFigure2TransitionObligations
      hk BaseTransitionRealization.exactBase (C.orientation k hk)

def connectorRemainingSeparationOfSqDistSeparation
    (C : ConnectorExactBaseFullMetricCoreFields)
    (sqSeparated : ConnectorRemainingSqDistSeparationField C) :
    ConnectorRemainingSeparationField C := by
  intro k hk
  exact
    generatedGlobalSeparationOfSqDistSeparation
      C.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (C.orientation k hk)
      (sqSeparated k hk)

/-! ## Same-block isometry from exact-local preservation -/

def remainingSameBlockOfExactLocal
    (C : ExactBaseFullMetricCoreFields)
    (exactLocal : ExactLocalPreservation C.O) :
    RemainingSameBlockField C := by
  intro k hk
  exact
    GeneratedMetricClosure.generatedSameBlockIsometry_of_exactLocalSqDistances
      C.O hk BaseTransitionRealization.exactBase (C.orientation k hk)
      GeneratedMetricClosure.exactBase_matchesExactLocalSqDistances
      exactLocal

def remainingFullMetricOfSeparationAndExactLocal
    (C : ExactBaseFullMetricCoreFields)
    (separated : RemainingSeparationField C)
    (exactLocal : ExactLocalPreservation C.O) :
    RemainingFullMetricField C :=
  ExactBaseFullMetricSourceInhabitationW22.remainingFullMetricFieldOfParts
    C separated (remainingSameBlockOfExactLocal C exactLocal)

def exactBaseFullMetricSourceFieldsOfSeparationAndExactLocal
    (C : ExactBaseFullMetricCoreFields)
    (separated : RemainingSeparationField C)
    (exactLocal : ExactLocalPreservation C.O) :
    ExactBaseFullMetricSourceFields :=
  C.toExactBaseFullMetricSourceFields
    (remainingFullMetricOfSeparationAndExactLocal C separated exactLocal)

def exactBaseFullMetricSourceFieldsOfSqDistAndExactLocal
    (C : ExactBaseFullMetricCoreFields)
    (sqSeparated : RemainingSqDistSeparationField C)
    (exactLocal : ExactLocalPreservation C.O) :
    ExactBaseFullMetricSourceFields :=
  exactBaseFullMetricSourceFieldsOfSeparationAndExactLocal C
    (remainingSeparationOfSqDistSeparation C sqSeparated) exactLocal

structure ExactBaseFullMetricConcreteCoreFields where
  core : ExactBaseFullMetricCoreFields
  separated : RemainingSeparationField core
  exactLocal : ExactLocalPreservation core.O

namespace ExactBaseFullMetricConcreteCoreFields

def metric
    (D : ExactBaseFullMetricConcreteCoreFields) :
    RemainingFullMetricField D.core :=
  remainingFullMetricOfSeparationAndExactLocal D.core D.separated D.exactLocal

def sourceFields
    (D : ExactBaseFullMetricConcreteCoreFields) :
    ExactBaseFullMetricSourceFields :=
  D.core.toExactBaseFullMetricSourceFields D.metric

theorem targetUpperConstructionFiveSixteen
    (D : ExactBaseFullMetricConcreteCoreFields) :
    ExactBaseFullMetricSourceInhabitationW22.ExactTarget :=
  D.core.targetUpperConstructionFiveSixteen D.metric

theorem targetUpperConstructionFiveSixteenArbitrary
    (D : ExactBaseFullMetricConcreteCoreFields) :
    ExactBaseFullMetricSourceInhabitationW22.ArbitraryTarget :=
  D.core.targetUpperConstructionFiveSixteenArbitrary D.metric

end ExactBaseFullMetricConcreteCoreFields

def exactBaseConcreteCoreFieldsOfSqDist
    (C : ExactBaseFullMetricCoreFields)
    (sqSeparated : RemainingSqDistSeparationField C)
    (exactLocal : ExactLocalPreservation C.O) :
    ExactBaseFullMetricConcreteCoreFields where
  core := C
  separated := remainingSeparationOfSqDistSeparation C sqSeparated
  exactLocal := exactLocal

theorem nonempty_exactBaseFullMetricSourceFields_of_concreteCore :
    Nonempty ExactBaseFullMetricConcreteCoreFields ->
      Nonempty ExactBaseFullMetricSourceFields := by
  intro h
  exact h.elim (fun D => Nonempty.intro D.sourceFields)

theorem nonempty_exactBaseFullMetricSourceFields_of_core_separation_exactLocal :
    (Exists fun C : ExactBaseFullMetricCoreFields =>
      RemainingSeparationField C /\ ExactLocalPreservation C.O) ->
      Nonempty ExactBaseFullMetricSourceFields := by
  intro h
  cases h with
  | intro C hC =>
      exact
        Nonempty.intro
          (exactBaseFullMetricSourceFieldsOfSeparationAndExactLocal
            C hC.1 hC.2)

/-! ## Connector full-metric core -/

def connectorRemainingSameBlockOfExactLocal
    (C : ConnectorExactBaseFullMetricCoreFields)
    (exactLocal : ConnectorExactLocalPreservation C) :
    ConnectorRemainingSameBlockField C := by
  intro k hk
  exact
    GeneratedMetricClosure.generatedSameBlockIsometry_of_exactLocalSqDistances
      C.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (C.orientation k hk)
      GeneratedMetricClosure.exactBase_matchesExactLocalSqDistances
      exactLocal

def connectorRemainingFullMetricOfSeparationAndExactLocal
    (C : ConnectorExactBaseFullMetricCoreFields)
    (separated : ConnectorRemainingSeparationField C)
    (exactLocal : ConnectorExactLocalPreservation C) :
    ConnectorRemainingFullMetricField C :=
  ExactBaseFullMetricSourceInhabitationW22.connectorRemainingFullMetricFieldOfParts
    C separated (connectorRemainingSameBlockOfExactLocal C exactLocal)

def connectorExactBaseFullMetricSourceFieldsOfSeparationAndExactLocal
    (C : ConnectorExactBaseFullMetricCoreFields)
    (separated : ConnectorRemainingSeparationField C)
    (exactLocal : ConnectorExactLocalPreservation C) :
    ConnectorExactBaseFullMetricSourceFields :=
  C.toConnectorExactBaseFullMetricSourceFields
    (connectorRemainingFullMetricOfSeparationAndExactLocal
      C separated exactLocal)

def connectorExactBaseFullMetricSourceFieldsOfSqDistAndExactLocal
    (C : ConnectorExactBaseFullMetricCoreFields)
    (sqSeparated : ConnectorRemainingSqDistSeparationField C)
    (exactLocal : ConnectorExactLocalPreservation C) :
    ConnectorExactBaseFullMetricSourceFields :=
  connectorExactBaseFullMetricSourceFieldsOfSeparationAndExactLocal C
    (connectorRemainingSeparationOfSqDistSeparation C sqSeparated)
    exactLocal

structure ConnectorFullMetricConcreteCoreFields where
  core : ConnectorExactBaseFullMetricCoreFields
  separated : ConnectorRemainingSeparationField core
  exactLocal : ConnectorExactLocalPreservation core

namespace ConnectorFullMetricConcreteCoreFields

def metric
    (D : ConnectorFullMetricConcreteCoreFields) :
    ConnectorRemainingFullMetricField D.core :=
  connectorRemainingFullMetricOfSeparationAndExactLocal
    D.core D.separated D.exactLocal

def sourceFields
    (D : ConnectorFullMetricConcreteCoreFields) :
    ConnectorExactBaseFullMetricSourceFields :=
  D.core.toConnectorExactBaseFullMetricSourceFields D.metric

def searchFamily
    (D : ConnectorFullMetricConcreteCoreFields) :
    ExactBaseFullMetricSourceInhabitationW22.ConnectorGeneratedClosureSearchFamily :=
  D.core.toConnectorGeneratedClosureSearchFamily D.metric

theorem targetUpperConstructionFiveSixteen
    (D : ConnectorFullMetricConcreteCoreFields) :
    ExactBaseFullMetricSourceInhabitationW22.ExactTarget :=
  D.core.targetUpperConstructionFiveSixteen D.metric

theorem targetUpperConstructionFiveSixteenArbitrary
    (D : ConnectorFullMetricConcreteCoreFields) :
    ExactBaseFullMetricSourceInhabitationW22.ArbitraryTarget :=
  D.core.targetUpperConstructionFiveSixteenArbitrary D.metric

end ConnectorFullMetricConcreteCoreFields

def connectorConcreteCoreFieldsOfSqDist
    (C : ConnectorExactBaseFullMetricCoreFields)
    (sqSeparated : ConnectorRemainingSqDistSeparationField C)
    (exactLocal : ConnectorExactLocalPreservation C) :
    ConnectorFullMetricConcreteCoreFields where
  core := C
  separated := connectorRemainingSeparationOfSqDistSeparation C sqSeparated
  exactLocal := exactLocal

theorem nonempty_connectorExactBaseFullMetricSourceFields_of_concreteCore :
    Nonempty ConnectorFullMetricConcreteCoreFields ->
      Nonempty ConnectorExactBaseFullMetricSourceFields := by
  intro h
  exact h.elim (fun D => Nonempty.intro D.sourceFields)

theorem nonempty_connectorExactBaseFullMetricSourceFields_of_core_separation_exactLocal :
    (Exists fun C : ConnectorExactBaseFullMetricCoreFields =>
      ConnectorRemainingSeparationField C /\
        ConnectorExactLocalPreservation C) ->
      Nonempty ConnectorExactBaseFullMetricSourceFields := by
  intro h
  cases h with
  | intro C hC =>
      exact
        Nonempty.intro
          (connectorExactBaseFullMetricSourceFieldsOfSeparationAndExactLocal
            C hC.1 hC.2)

/-! ## Handoff from W22 remaining-separation data -/

def exactCoreOfRoleHingedPeriodSearchFamily
    (F : RoleHingedPeriodSearchFamily) :
    ExactBaseFullMetricCoreFields where
  O := F.transitions.toFigure2TransitionObligations
  orientation := F.orientation
  closure := fun k hk =>
    (F.period k hk).toGeneratedClosureEquation

def exactBaseFullMetricConcreteCoreOfRoleHingedSeparation
    (F : RoleHingedPeriodSearchFamily)
    (separated : RoleHingedRemainingSeparationField F) :
    ExactBaseFullMetricConcreteCoreFields where
  core := exactCoreOfRoleHingedPeriodSearchFamily F
  separated := separated
  exactLocal :=
    GeneratedMetricClosure.roleHingeTransitions_preserveExactLocalSqDistances
      F.transitions

def exactBaseFullMetricSourceFieldsOfRoleHingedSeparation
    (F : RoleHingedPeriodSearchFamily)
    (separated : RoleHingedRemainingSeparationField F) :
    ExactBaseFullMetricSourceFields :=
  (exactBaseFullMetricConcreteCoreOfRoleHingedSeparation F separated).sourceFields

end

end ExactBaseFullMetricConcreteW23
end PachToth
end ErdosProblems1066
