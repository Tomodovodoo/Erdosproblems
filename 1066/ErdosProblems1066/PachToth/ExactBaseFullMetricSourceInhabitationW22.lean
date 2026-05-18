import ErdosProblems1066.PachToth.ExactBaseSourceNoGoW21
import ErdosProblems1066.PachToth.BaseTransitionRealization
import ErdosProblems1066.PachToth.GeneratedMetricClosure
import ErdosProblems1066.PachToth.ExplicitClosedPlacementProducerW19
import ErdosProblems1066.PachToth.ClosedPlacementObstructionBypassW19

set_option autoImplicit false

/-!
# W22 exact-base full-metric source inhabitation

This file continues the viable route isolated in W21.  The exact-base
connector route must not ask for the reduced all-source same-block transition
preservation field.  The remaining field is instead the full generated metric
hypothesis for each positive generated chain: global separation plus
same-block isometry on the generated orbit.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactBaseFullMetricSourceInhabitationW22

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev ExactBaseFullMetricSourceFields :=
  ExactBaseSourceNoGoW21.ExactBaseFullMetricSourceFields

abbrev ConnectorExactBaseFullMetricSourceFields :=
  ExactBaseSourceNoGoW21.ConnectorExactBaseFullMetricSourceFields

abbrev ConnectorTransitions :=
  ExactBaseSourceNoGoW21.ConnectorTransitions

abbrev ConnectorGeneratedClosureSearchFamily :=
  RoleHingeTransitionSearch.ConnectorGeneratedClosureSearchFamily

abbrev FullMetricHypotheses
    (F : GeneratedSeparationInterface.GeneratedChainFamily) :=
  GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F

abbrev ExplicitClosedPlacementCertificateFamily :=
  ExplicitClosedPlacementProducerW19.ExplicitClosedPlacementCertificateFamily

abbrev ExplicitTransitionClosedPlacementCertificateFamily :=
  ArbitraryNClosedPlacementRouteW19.ExplicitTransitionClosedPlacementCertificateFamily

abbrev ExactTarget : Prop :=
  ExplicitClosedPlacementProducerW19.ExactTarget

abbrev ArbitraryTarget : Prop :=
  ExplicitClosedPlacementProducerW19.ArbitraryTarget

/-! ## Exact-base full-metric core -/

/-- Exact-base source fields before attaching the full generated metric
hypotheses. -/
structure ExactBaseFullMetricCoreFields where
  O : Figure2Certificate.SameOppositeTransitionObligations
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        O hk BaseTransitionRealization.exactBase (orientation k hk)

/-- The precise full-metric field left after exact-base transition data,
orientations, and closure equations are fixed. -/
abbrev RemainingFullMetricField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      C.O hk BaseTransitionRealization.exactBase (C.orientation k hk)

/-- The separation half of the remaining full-metric field. -/
abbrev RemainingSeparationField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.O hk BaseTransitionRealization.exactBase (C.orientation k hk)

/-- The generated-orbit same-block half of the remaining full-metric field. -/
abbrev RemainingSameBlockField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      C.O hk BaseTransitionRealization.exactBase (C.orientation k hk)

def remainingFullMetricFieldOfParts
    (C : ExactBaseFullMetricCoreFields)
    (separated : RemainingSeparationField C)
    (sameBlock : RemainingSameBlockField C) :
    RemainingFullMetricField C :=
  fun k hk =>
    { separated := separated k hk
      same_block_isometry := sameBlock k hk }

theorem remainingFullMetricField_iff_parts
    (C : ExactBaseFullMetricCoreFields) :
    RemainingFullMetricField C <->
      RemainingSeparationField C /\ RemainingSameBlockField C := by
  exact
    Iff.intro
      (fun metric =>
        And.intro
          (fun k hk => (metric k hk).separated)
          (fun k hk => (metric k hk).same_block_isometry))
      (fun h =>
        remainingFullMetricFieldOfParts C h.1 h.2)

namespace ExactBaseFullMetricCoreFields

def family
    (C : ExactBaseFullMetricCoreFields) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => C.O
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := C.orientation

@[simp]
theorem family_O
    (C : ExactBaseFullMetricCoreFields) (k : Nat) (hk : 0 < k) :
    C.family.O k hk = C.O :=
  rfl

@[simp]
theorem family_base
    (C : ExactBaseFullMetricCoreFields) (k : Nat) (hk : 0 < k) :
    C.family.base k hk = BaseTransitionRealization.exactBase :=
  rfl

def closures
    (C : ExactBaseFullMetricCoreFields) :
    ClosedPlacementClosure.GeneratedChainFamilyClosures C.family :=
  fun k hk => C.closure k hk

def metricHypotheses
    (C : ExactBaseFullMetricCoreFields)
    (metric : RemainingFullMetricField C) :
    FullMetricHypotheses C.family where
  metric := fun k hk => metric k hk

def toExactBaseFullMetricSourceFields
    (C : ExactBaseFullMetricCoreFields)
    (metric : RemainingFullMetricField C) :
    ExactBaseFullMetricSourceFields where
  O := C.O
  orientation := C.orientation
  closure := C.closure
  metric := metric

def toExplicitTransitionClosedPlacementCertificateFamily
    (C : ExactBaseFullMetricCoreFields)
    (metric : RemainingFullMetricField C) :
    ExplicitTransitionClosedPlacementCertificateFamily :=
  fun k hk =>
    ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedClosure
      C.O hk BaseTransitionRealization.exactBase (C.orientation k hk)
      (C.closure k hk) (metric k hk)

def toExplicitClosedPlacementCertificateFamily
    (C : ExactBaseFullMetricCoreFields)
    (metric : RemainingFullMetricField C) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk =>
    (C.toExplicitTransitionClosedPlacementCertificateFamily metric k hk)
      |>.toExplicitClosedPlacementCertificate

theorem targetUpperConstructionFiveSixteen
    (C : ExactBaseFullMetricCoreFields)
    (metric : RemainingFullMetricField C) :
    ExactTarget := by
  exact
    ClosedPlacementTargetWrappersW19.targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates
      (C.toExplicitClosedPlacementCertificateFamily metric)

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : ExactBaseFullMetricCoreFields)
    (metric : RemainingFullMetricField C) :
    ArbitraryTarget := by
  exact
    ArbitraryNClosedPlacementRouteW19.targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates
      (C.toExplicitClosedPlacementCertificateFamily metric)

end ExactBaseFullMetricCoreFields

def exactBaseFullMetricCoreFieldsOfSource
    (S : ExactBaseFullMetricSourceFields) :
    ExactBaseFullMetricCoreFields where
  O := S.O
  orientation := S.orientation
  closure := S.closure

theorem nonempty_exactBaseFullMetricSourceFields_iff_remainingFullMetric :
    Nonempty ExactBaseFullMetricSourceFields <->
      Exists fun C : ExactBaseFullMetricCoreFields =>
        RemainingFullMetricField C := by
  exact
    Iff.intro
      (fun h =>
        h.elim
          (fun S =>
            Exists.intro
              (exactBaseFullMetricCoreFieldsOfSource S)
              S.metric))
      (fun h =>
        Exists.elim h
          (fun C metric =>
            Nonempty.intro
              (C.toExactBaseFullMetricSourceFields metric)))

theorem nonempty_exactBaseFullMetricSourceFields_iff_parts :
    Nonempty ExactBaseFullMetricSourceFields <->
      Exists fun C : ExactBaseFullMetricCoreFields =>
        RemainingSeparationField C /\ RemainingSameBlockField C := by
  exact
    Iff.intro
      (fun h =>
        h.elim
          (fun S =>
            Exists.intro
              (exactBaseFullMetricCoreFieldsOfSource S)
              (And.intro
                (fun k hk => (S.metric k hk).separated)
                (fun k hk => (S.metric k hk).same_block_isometry))))
      (fun h =>
        Exists.elim h
          (fun C parts =>
            Nonempty.intro
              (C.toExactBaseFullMetricSourceFields
                (remainingFullMetricFieldOfParts C parts.1 parts.2))))

/-! ## Connector exact-base full-metric core -/

/-- Connector exact-base fields before attaching the full generated metric
hypotheses.  This is the connector-role route that avoids the inconsistent
reduced all-source transition-preservation field. -/
structure ConnectorExactBaseFullMetricCoreFields where
  transitions : ConnectorTransitions
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)

abbrev ConnectorRemainingFullMetricField
    (C : ConnectorExactBaseFullMetricCoreFields) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      C.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (C.orientation k hk)

abbrev ConnectorRemainingSeparationField
    (C : ConnectorExactBaseFullMetricCoreFields) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (C.orientation k hk)

abbrev ConnectorRemainingSameBlockField
    (C : ConnectorExactBaseFullMetricCoreFields) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      C.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (C.orientation k hk)

def connectorRemainingFullMetricFieldOfParts
    (C : ConnectorExactBaseFullMetricCoreFields)
    (separated : ConnectorRemainingSeparationField C)
    (sameBlock : ConnectorRemainingSameBlockField C) :
    ConnectorRemainingFullMetricField C :=
  fun k hk =>
    { separated := separated k hk
      same_block_isometry := sameBlock k hk }

theorem connectorRemainingFullMetricField_iff_parts
    (C : ConnectorExactBaseFullMetricCoreFields) :
    ConnectorRemainingFullMetricField C <->
      ConnectorRemainingSeparationField C /\
        ConnectorRemainingSameBlockField C := by
  exact
    Iff.intro
      (fun metric =>
        And.intro
          (fun k hk => (metric k hk).separated)
          (fun k hk => (metric k hk).same_block_isometry))
      (fun h =>
        connectorRemainingFullMetricFieldOfParts C h.1 h.2)

namespace ConnectorExactBaseFullMetricCoreFields

def toExactCore
    (C : ConnectorExactBaseFullMetricCoreFields) :
    ExactBaseFullMetricCoreFields where
  O := C.transitions.toFigure2TransitionObligations
  orientation := C.orientation
  closure := C.closure

def toConnectorExactBaseFullMetricSourceFields
    (C : ConnectorExactBaseFullMetricCoreFields)
    (metric : ConnectorRemainingFullMetricField C) :
    ConnectorExactBaseFullMetricSourceFields where
  transitions := C.transitions
  orientation := C.orientation
  closure := C.closure
  metric := metric

def toConnectorGeneratedClosureSearchFamily
    (C : ConnectorExactBaseFullMetricCoreFields)
    (metric : ConnectorRemainingFullMetricField C) :
    ConnectorGeneratedClosureSearchFamily where
  transitions := C.transitions
  orientation := C.orientation
  closure := C.closure
  metric := metric

theorem targetUpperConstructionFiveSixteen
    (C : ConnectorExactBaseFullMetricCoreFields)
    (metric : ConnectorRemainingFullMetricField C) :
    ExactTarget := by
  exact
    C.toExactCore.targetUpperConstructionFiveSixteen metric

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : ConnectorExactBaseFullMetricCoreFields)
    (metric : ConnectorRemainingFullMetricField C) :
    ArbitraryTarget := by
  exact
    C.toExactCore.targetUpperConstructionFiveSixteenArbitrary metric

end ConnectorExactBaseFullMetricCoreFields

def connectorExactBaseFullMetricCoreFieldsOfSource
    (S : ConnectorExactBaseFullMetricSourceFields) :
    ConnectorExactBaseFullMetricCoreFields where
  transitions := S.transitions
  orientation := S.orientation
  closure := S.closure

def connectorExactBaseFullMetricSourceFieldsOfSearchFamily
    (F : ConnectorGeneratedClosureSearchFamily) :
    ConnectorExactBaseFullMetricSourceFields where
  transitions := F.transitions
  orientation := F.orientation
  closure := F.closure
  metric := F.metric

theorem nonempty_connectorExactBaseFullMetricSourceFields_iff_remainingFullMetric :
    Nonempty ConnectorExactBaseFullMetricSourceFields <->
      Exists fun C : ConnectorExactBaseFullMetricCoreFields =>
        ConnectorRemainingFullMetricField C := by
  exact
    Iff.intro
      (fun h =>
        h.elim
          (fun S =>
            Exists.intro
              (connectorExactBaseFullMetricCoreFieldsOfSource S)
              S.metric))
      (fun h =>
        Exists.elim h
          (fun C metric =>
            Nonempty.intro
              (C.toConnectorExactBaseFullMetricSourceFields metric)))

theorem nonempty_connectorExactBaseFullMetricSourceFields_iff_parts :
    Nonempty ConnectorExactBaseFullMetricSourceFields <->
      Exists fun C : ConnectorExactBaseFullMetricCoreFields =>
        ConnectorRemainingSeparationField C /\
          ConnectorRemainingSameBlockField C := by
  exact
    Iff.intro
      (fun h =>
        h.elim
          (fun S =>
            Exists.intro
              (connectorExactBaseFullMetricCoreFieldsOfSource S)
              (And.intro
                (fun k hk => (S.metric k hk).separated)
                (fun k hk => (S.metric k hk).same_block_isometry))))
      (fun h =>
        Exists.elim h
          (fun C parts =>
            Nonempty.intro
              (C.toConnectorExactBaseFullMetricSourceFields
                (connectorRemainingFullMetricFieldOfParts C parts.1 parts.2))))

theorem nonempty_connectorExactBaseFullMetricSourceFields_iff_searchFamily :
    Nonempty ConnectorExactBaseFullMetricSourceFields <->
      Nonempty ConnectorGeneratedClosureSearchFamily := by
  exact
    Iff.intro
      (fun h =>
        h.elim
          (fun S =>
            Nonempty.intro
              S.toConnectorGeneratedClosureSearchFamily))
      (fun h =>
        h.elim
          (fun F =>
            Nonempty.intro
              (connectorExactBaseFullMetricSourceFieldsOfSearchFamily F)))

/-! ## Old route blockers retained -/

theorem false_of_connectorFullMetricPlusReducedPreservationAt
    {k : Nat} {hk : 0 < k}
    (S :
      ExactBaseSourceNoGoW21.ConnectorFullMetricPlusReducedPreservationAt
        k hk) :
    False :=
  ExactBaseSourceNoGoW21.ConnectorFullMetricPlusReducedPreservationAt.false S

theorem not_nonempty_connectorFullMetricPlusReducedPreservationAt
    {k : Nat} {hk : 0 < k} :
    Not
      (Nonempty
        (ExactBaseSourceNoGoW21.ConnectorFullMetricPlusReducedPreservationAt
          k hk)) := by
  intro h
  exact h.elim false_of_connectorFullMetricPlusReducedPreservationAt

theorem old_baseFixing_certificate_route_blocked :
    Not (Nonempty ClosedPlacementObstructionBypassW19.BaseFixingCertificate) :=
  ClosedPlacementObstructionBypassW19.not_nonempty_baseFixingCertificate

theorem old_allPositive_inputs_route_blocked :
    Not
      (Nonempty
        ClosedPlacementObstructionBypassW19.AllPositiveFinalCertificateInputs) :=
  ClosedPlacementObstructionBypassW19.not_nonempty_allPositiveFinalCertificateInputs

end

end ExactBaseFullMetricSourceInhabitationW22
end PachToth
end ErdosProblems1066
