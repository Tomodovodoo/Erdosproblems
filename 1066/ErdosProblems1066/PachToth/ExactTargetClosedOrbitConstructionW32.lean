import ErdosProblems1066.PachToth.ExactTargetCandidateClosure
import ErdosProblems1066.PachToth.ClosedPlacementConcreteConstructionW26

set_option autoImplicit false

/-!
# W32 exact-target certificate to closed-orbit construction

This file turns the minimal exact-target certificate into the live W26
closed-orbit construction surface.  It does not add another target facade:
the output is `MinimalFieldsWithOrbitClosure`, hence also
`ConcreteClosedOrbitFamily`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactTargetCandidateClosure

open Arithmetic
open FiniteGraph
open FiniteGraph.LocalVertex
open NonRigidConnectorSeparationFacts
open RoleHingeInterfaceRefinement

noncomputable section

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily

abbrev MinimalFieldsWithOrbitClosure : Type :=
  ClosedPlacementConcreteConstructionW26.MinimalFieldsWithOrbitClosure

abbrev MinimalExactTargetPartialCertificateGate : Prop :=
  Nonempty MinimalExactTargetPartialCertificate

abbrev MinimalExactTargetCertificateGate : Prop :=
  Nonempty MinimalExactTargetCertificate

abbrev SameExactLocalResidualRows : Prop :=
  forall source : LocalVertex -> R2,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
      forall u v : LocalVertex,
        Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
          RoleHingeSameBlockAlgebra.sqDist
              (RoleHingeConcreteSearch.samePlaceNext source u)
              (RoleHingeConcreteSearch.samePlaceNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

abbrev OppositeExactLocalResidualRows : Prop :=
  forall source : LocalVertex -> R2,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
      forall u v : LocalVertex,
        Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
          RoleHingeSameBlockAlgebra.sqDist
              (RoleHingeConcreteSearch.oppositePlaceNext source u)
              (RoleHingeConcreteSearch.oppositePlaceNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

abbrev ExactLocalResidualRows : Prop :=
  SameExactLocalResidualRows /\ OppositeExactLocalResidualRows

/-! ## Partial certificate route surface -/

theorem partialClosure
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  P.closure k hk

theorem partialPeriodEquation
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  P.periodEquation k hk

theorem partialPeriod
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  P.period k hk

theorem partialNonConnectorLowerBound
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) :
    GeneratedNonConnectorCrossBlockDistanceLowerBounds
        concreteObligations hk
        BaseTransitionRealization.exactBase
        (P.orientation k hk)
        (fun _i _u _j _v => (1 : Real)) :=
  P.nonConnectorLower_bound k hk

theorem partialPeriods
    (P : MinimalExactTargetPartialCertificate) :
    P.generatedChainFamily.Periods :=
  P.periods

namespace MinimalExactTargetCertificate

/-- The generated point map carried by the minimal exact certificate. -/
def closedOrbitPoint
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    Fin k -> LocalVertex -> R2 :=
  GeneratedClosedChain.generatedPoint
    concreteObligations hk
    BaseTransitionRealization.exactBase
    (C.orientation k hk)

/-- The successor transition selected by the certificate orientation word. -/
def closedOrbitStep
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.OrientedTransition :=
  GeneratedClosedChain.generatedStep concreteObligations (C.orientation k hk)

/-- The generated period equation gives the actual successor equation for the
certificate's point maps. -/
theorem closedOrbitSuccessorEq
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    C.closedOrbitPoint k hk (cyclicSucc hk i) v =
      (C.closedOrbitStep k hk i).placeNext
        (C.closedOrbitPoint k hk i) v := by
  simpa [closedOrbitPoint, closedOrbitStep] using
    GeneratedClosedChain.generatedPoint_successor_compatible
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk)
      (C.period k hk)
      i v

/-- Orbit-level exact-local squared distances supply the same-block unit edges
needed by the W26 concrete closed-orbit surface. -/
theorem closedOrbitSameBlockEdgesUnit
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (C.closedOrbitPoint k hk i u)
          (C.closedOrbitPoint k hk i v) = 1 := by
  intro i u v _huv hadj
  have hdist :=
    RoleHingeSameBlockAlgebra.matchesExactLocalDistances_of_sqDistances
      (C.orbitSqDistances k hk i) u v
  calc
    _root_.eucDist (C.closedOrbitPoint k hk i u)
        (C.closedOrbitPoint k hk i v) =
        _root_.eucDist
          (ExactLocalGeometry.localPoint u)
          (ExactLocalGeometry.localPoint v) := by
        simpa [closedOrbitPoint] using hdist
    _ = 1 := ExactLocalGeometry.adj_unit_distance u v hadj

/-- W19's generated-period/orbit-metric connector lemma supplies the four
named successor connector unit equations for the certificate's generated
chain. -/
def closedOrbitCrossConnectorNamedUnits
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementConcreteConstructionW26.ExactCrossConnectorUnitCertificate
      hk (C.closedOrbitPoint k hk) := by
  simpa [closedOrbitPoint, concreteObligations,
    ClosedPlacementCrossConnectorEdgesW19.concreteOrbitTransitionObligations]
    using
      ClosedPlacementCrossConnectorEdgesW19.ofConcreteOrbitPeriodEquation
        hk
        (C.orientation k hk)
        (C.periodEquation k hk)
        (C.separated k hk)
        (C.orbitSqDistances k hk)

/-- A minimal exact-target certificate gives the W26 minimal free-placement
fields together with the genuine generated-orbit successor closure. -/
def toMinimalFieldsWithOrbitClosure
    (C : MinimalExactTargetCertificate) :
    MinimalFieldsWithOrbitClosure where
  fields :=
    { point := C.closedOrbitPoint
      separated := fun k hk i u j v hij => by
        simpa [closedOrbitPoint] using C.separated k hk i u j v hij
      same_block_edges_unit := C.closedOrbitSameBlockEdgesUnit
      cross_connector_edges_unit := fun k hk =>
        (C.closedOrbitCrossConnectorNamedUnits k hk).crossConnectorEdgesUnit }
  step := C.closedOrbitStep
  successor_eq := C.closedOrbitSuccessorEq

/-- A minimal exact-target certificate gives the concrete W26 closed-orbit
family, not just the final exact-target wrapper. -/
def toConcreteClosedOrbitFamily
    (C : MinimalExactTargetCertificate) :
    ConcreteClosedOrbitFamily :=
  ClosedPlacementConcreteConstructionW26.MinimalFieldsWithOrbitClosure.toConcreteClosedOrbitFamily
    C.toMinimalFieldsWithOrbitClosure

theorem nonempty_minimalFieldsWithOrbitClosure_of_certificate
    (C : MinimalExactTargetCertificate) :
    Nonempty MinimalFieldsWithOrbitClosure :=
  Nonempty.intro C.toMinimalFieldsWithOrbitClosure

theorem nonempty_concreteClosedOrbitFamily_of_certificate
    (C : MinimalExactTargetCertificate) :
    Nonempty ConcreteClosedOrbitFamily :=
  Nonempty.intro C.toConcreteClosedOrbitFamily

theorem nonempty_minimalFieldsWithOrbitClosure_of_nonempty_certificate :
    Nonempty MinimalExactTargetCertificate ->
      Nonempty MinimalFieldsWithOrbitClosure := by
  intro h
  cases h with
  | intro C => exact C.nonempty_minimalFieldsWithOrbitClosure_of_certificate

theorem nonempty_concreteClosedOrbitFamily_of_nonempty_certificate :
    Nonempty MinimalExactTargetCertificate ->
      Nonempty ConcreteClosedOrbitFamily := by
  intro h
  cases h with
  | intro C => exact C.nonempty_concreteClosedOrbitFamily_of_certificate

@[simp]
theorem toMinimalFieldsWithOrbitClosure_point
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    C.toMinimalFieldsWithOrbitClosure.fields.point k hk i v =
      C.closedOrbitPoint k hk i v :=
  rfl

@[simp]
theorem toConcreteClosedOrbitFamily_point
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (C.toConcreteClosedOrbitFamily.data k hk).point i v =
      C.closedOrbitPoint k hk i v :=
  rfl

end MinimalExactTargetCertificate

/-! ## Residual extension and full-certificate blocker -/

def fullCertificateOfPartialAndResidualRows
    (P : MinimalExactTargetPartialCertificate)
    (same_rest : SameExactLocalResidualRows)
    (opposite_rest : OppositeExactLocalResidualRows) :
    MinimalExactTargetCertificate :=
  P.withExactLocalResiduals same_rest opposite_rest

theorem nonempty_minimalFieldsWithOrbitClosure_of_partial_and_residualRows
    (P : MinimalExactTargetPartialCertificate)
    (same_rest : SameExactLocalResidualRows)
    (opposite_rest : OppositeExactLocalResidualRows) :
    Nonempty MinimalFieldsWithOrbitClosure :=
  (fullCertificateOfPartialAndResidualRows P same_rest opposite_rest)
    |>.nonempty_minimalFieldsWithOrbitClosure_of_certificate

theorem nonempty_concreteClosedOrbitFamily_of_partial_and_residualRows
    (P : MinimalExactTargetPartialCertificate)
    (same_rest : SameExactLocalResidualRows)
    (opposite_rest : OppositeExactLocalResidualRows) :
    Nonempty ConcreteClosedOrbitFamily :=
  (fullCertificateOfPartialAndResidualRows P same_rest opposite_rest)
    |>.nonempty_concreteClosedOrbitFamily_of_certificate

theorem fullCertificateSource_blocked :
    Not MinimalExactTargetCertificateGate :=
  not_minimalExactTargetCertificate

theorem false_of_fullCertificateSource
    (H : MinimalExactTargetCertificateGate) :
    False :=
  fullCertificateSource_blocked H

theorem partialCertificate_with_residualRows_blocked :
    Not (MinimalExactTargetPartialCertificateGate /\ ExactLocalResidualRows) := by
  rintro ⟨⟨P⟩, same_rest, opposite_rest⟩
  exact
    fullCertificateSource_blocked
      ⟨fullCertificateOfPartialAndResidualRows P same_rest opposite_rest⟩

theorem fullCertificate_to_concreteClosedOrbitFamily :
    MinimalExactTargetCertificateGate -> Nonempty ConcreteClosedOrbitFamily :=
  MinimalExactTargetCertificate.nonempty_concreteClosedOrbitFamily_of_nonempty_certificate

theorem fullCertificate_to_minimalFieldsWithOrbitClosure :
    MinimalExactTargetCertificateGate -> Nonempty MinimalFieldsWithOrbitClosure :=
  MinimalExactTargetCertificate.nonempty_minimalFieldsWithOrbitClosure_of_nonempty_certificate

theorem blockedFullCertificateSource_noConcreteOrbitSource :
    Not (MinimalExactTargetCertificateGate /\
      (MinimalExactTargetCertificateGate -> Nonempty ConcreteClosedOrbitFamily)) := by
  intro H
  exact fullCertificateSource_blocked H.1

structure ExactTargetClosedOrbitRouteAudit : Prop where
  partial_to_closure :
    forall (P : MinimalExactTargetPartialCertificate) (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        concreteObligations hk
        BaseTransitionRealization.exactBase
        (P.orientation k hk)
  partial_to_periodEquation :
    forall (P : MinimalExactTargetPartialCertificate) (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedPeriodEquation
        concreteObligations hk
        BaseTransitionRealization.exactBase
        (P.orientation k hk)
  partial_to_period :
    forall (P : MinimalExactTargetPartialCertificate) (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedPeriod
        concreteObligations hk
        BaseTransitionRealization.exactBase
        (P.orientation k hk)
  partial_to_nonConnectorLower :
    forall (P : MinimalExactTargetPartialCertificate) (k : Nat) (hk : 0 < k),
      GeneratedNonConnectorCrossBlockDistanceLowerBounds
        concreteObligations hk
        BaseTransitionRealization.exactBase
        (P.orientation k hk)
        (fun _i _u _j _v => (1 : Real))
  partial_to_periodFamily :
    forall P : MinimalExactTargetPartialCertificate,
      P.generatedChainFamily.Periods
  partial_with_residuals_to_minimalFields :
    forall _P : MinimalExactTargetPartialCertificate,
      SameExactLocalResidualRows ->
        OppositeExactLocalResidualRows ->
          Nonempty MinimalFieldsWithOrbitClosure
  partial_with_residuals_to_concreteOrbit :
    forall _P : MinimalExactTargetPartialCertificate,
      SameExactLocalResidualRows ->
        OppositeExactLocalResidualRows ->
          Nonempty ConcreteClosedOrbitFamily
  full_to_minimalFields :
    MinimalExactTargetCertificateGate -> Nonempty MinimalFieldsWithOrbitClosure
  full_to_concreteOrbit :
    MinimalExactTargetCertificateGate -> Nonempty ConcreteClosedOrbitFamily
  full_source_blocked :
    Not MinimalExactTargetCertificateGate
  residual_extension_blocked :
    Not (MinimalExactTargetPartialCertificateGate /\ ExactLocalResidualRows)

theorem exactTargetClosedOrbitRouteAudit :
    ExactTargetClosedOrbitRouteAudit where
  partial_to_closure := partialClosure
  partial_to_periodEquation := partialPeriodEquation
  partial_to_period := partialPeriod
  partial_to_nonConnectorLower := partialNonConnectorLowerBound
  partial_to_periodFamily := partialPeriods
  partial_with_residuals_to_minimalFields :=
    nonempty_minimalFieldsWithOrbitClosure_of_partial_and_residualRows
  partial_with_residuals_to_concreteOrbit :=
    nonempty_concreteClosedOrbitFamily_of_partial_and_residualRows
  full_to_minimalFields := fullCertificate_to_minimalFieldsWithOrbitClosure
  full_to_concreteOrbit := fullCertificate_to_concreteClosedOrbitFamily
  full_source_blocked := fullCertificateSource_blocked
  residual_extension_blocked := partialCertificate_with_residualRows_blocked

end

end ExactTargetCandidateClosure
end PachToth
end ErdosProblems1066
