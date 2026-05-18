import ErdosProblems1066.PachToth.DeformedPlacement
import ErdosProblems1066.PachToth.LargeClosedPlacementW12
import ErdosProblems1066.PachToth.FiniteCertificateInstantiationW13

set_option autoImplicit false

/-!
# W14 closed-placement builders

This module connects the finite/generated certificate facades to the actual
`DeformedPlacement.ClosedPlacement` interface.  The builders below only
repackage existing metric inputs: period equations supply cyclic closure,
generated separation supplies global separation, and the role-hinge metric
facts supply the same-block and connector unit-edge obligations.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementBuilderW14

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-! ## Coordinate certificates -/

/-- An explicit coordinate certificate is already an actual deformed closed
placement. -/
def closedPlacementOfExplicitCertificate
    {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  C.toClosedPlacement

@[simp]
theorem closedPlacementOfExplicitCertificate_point
    {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfExplicitCertificate C).point i v = C.point i v :=
  rfl

/-- A transition-based coordinate certificate is also an actual deformed
closed placement. -/
def closedPlacementOfExplicitTransitionCertificate
    {k : Nat} {hk : 0 < k}
    (C :
      ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
        k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  C.toClosedPlacement

@[simp]
theorem closedPlacementOfExplicitTransitionCertificate_point
    {k : Nat} {hk : 0 < k}
    (C :
      ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
        k hk)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfExplicitTransitionCertificate C).point i v =
      C.point i v :=
  rfl

/-! ## Generated-chain builders -/

/-- Generated-chain data with reduced metric hypotheses builds the actual
closed placement whose points are the generated points. -/
def closedPlacementOfGeneratedReducedMetric
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod
        O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  (GeneratedSeparationInterface.explicitTransitionClosedPlacementCertificate_reduced
    O hk base orientation period H).toClosedPlacement

@[simp]
theorem closedPlacementOfGeneratedReducedMetric_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod
        O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfGeneratedReducedMetric
      O hk base orientation period H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- Generated-chain data with full metric hypotheses builds the actual closed
placement whose points are the generated points. -/
def closedPlacementOfGeneratedMetric
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod
        O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  (GeneratedSeparationInterface.explicitTransitionClosedPlacementCertificate
    O hk base orientation period H).toClosedPlacement

@[simp]
theorem closedPlacementOfGeneratedMetric_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod
        O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfGeneratedMetric
      O hk base orientation period H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-! ## Role-hinge and finite-certificate builders -/

/-- Role-hinged generated period and separation data build the actual
closed placement. -/
def closedPlacementOfRoleHinged
    (T : EventualRoleHingeClosure.RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod
        T.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  (EventualRoleHingeClosure.explicitTransitionClosedPlacementCertificateOfRoleHinged
    T hk orientation period separated).toClosedPlacement

@[simp]
theorem closedPlacementOfRoleHinged_point
    (T : EventualRoleHingeClosure.RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod
        T.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        orientation)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfRoleHinged
      T hk orientation period separated).point i v =
        GeneratedClosedChain.generatedPoint
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          orientation
          i v :=
  rfl

/-- The exact conditional builder for raw finite period fields: the period
row supplies cyclic closure, while generated global separation remains the
explicit metric input needed to build a closed placement. -/
def closedPlacementOfPeriodFieldsAndSeparation
    (P : FiniteCertificateObligationsW12.PeriodEquationFields)
    (k : Nat) (hk : 0 < k)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        P.transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (P.orientation k hk)) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfRoleHinged
    P.transitions
    hk
    (P.orientation k hk)
    (P.generatedPeriod k hk)
    separated

@[simp]
theorem closedPlacementOfPeriodFieldsAndSeparation_point
    (P : FiniteCertificateObligationsW12.PeriodEquationFields)
    (k : Nat) (hk : 0 < k)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        P.transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (P.orientation k hk))
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfPeriodFieldsAndSeparation
      P k hk separated).point i v =
        GeneratedClosedChain.generatedPoint
          P.transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (P.orientation k hk)
          i v :=
  rfl

/-- A family of finite period fields plus generated separation at every
positive block count gives the exact deformed-placement family. -/
def closedPlacementsOfPeriodFieldsAndSeparation
    (P : FiniteCertificateObligationsW12.PeriodEquationFields)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          P.transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (P.orientation k hk)) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk =>
    closedPlacementOfPeriodFieldsAndSeparation
      P k hk (separated k hk)

/-- Finite period fields plus generated separation route through actual
deformed closed placements to the exact block-form target. -/
theorem targetUpperConstructionFiveSixteen_of_periodFieldsAndSeparation
    (P : FiniteCertificateObligationsW12.PeriodEquationFields)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          P.transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (P.orientation k hk)) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
      (closedPlacementsOfPeriodFieldsAndSeparation P separated)

/-- Raw W12 all-positive non-connector fields build actual deformed closed
placements. -/
def closedPlacementOfAllPositiveNonConnectorFields
    (C : FiniteCertificateObligationsW12.AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfGeneratedReducedMetric
    C.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (C.orientation k hk)
    (C.period.generatedPeriod k hk)
    (C.reducedMetricHypotheses k hk)

@[simp]
theorem closedPlacementOfAllPositiveNonConnectorFields_point
    (C : FiniteCertificateObligationsW12.AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfAllPositiveNonConnectorFields C k hk).point i v =
      GeneratedClosedChain.generatedPoint
        C.transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (C.orientation k hk)
        i v :=
  rfl

/-- Raw W12 all-positive non-connector fields route through actual deformed
closed placements to the exact block-form target. -/
theorem targetUpperConstructionFiveSixteen_of_allPositiveNonConnectorFields
    (C : FiniteCertificateObligationsW12.AllPositiveNonConnectorFields) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
      (fun k hk =>
        closedPlacementOfAllPositiveNonConnectorFields C k hk)

/-- Native W12 table packages build actual deformed closed placements by first
flattening to the raw field facade. -/
def closedPlacementOfTableFamilyPackage
    (P : FiniteCertificateObligationsW12.TableFamilyPackage)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfAllPositiveNonConnectorFields P.toFields k hk

/-- Vector-grid W12 table packages build actual deformed closed placements. -/
def closedPlacementOfVectorPackage
    (P : FiniteCertificateObligationsW12.VectorPackage)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfAllPositiveNonConnectorFields P.toFields k hk

/-- Row-list W12 table packages build actual deformed closed placements. -/
def closedPlacementOfListPackage
    (P : FiniteCertificateObligationsW12.ListPackage)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfAllPositiveNonConnectorFields P.toFields k hk

/-- W13 concrete value-matrix families build actual deformed closed placements
through the W12 finite-certificate fields. -/
def closedPlacementOfConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfAllPositiveNonConnectorFields
    (FiniteCertificateInstantiationW13.fieldsOfConcreteValueMatrixFamily C)
    k hk

/-- W13 candidate value-matrix families build actual deformed closed
placements through the W12 finite-certificate fields. -/
def closedPlacementOfCandidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfAllPositiveNonConnectorFields
    (FiniteCertificateInstantiationW13.fieldsOfCandidateValueMatrixFamily C)
    k hk

/-! ## Eventual and large-certificate builders -/

/-- A large explicit closed-placement certificate family gives actual
deformed closed placements from its threshold onward. -/
def closedPlacementOfLargeExplicitClosedPlacementCertificates
    {K0 : Nat}
    (C : LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  (C.certificate k hK hk).toClosedPlacement

/-- Eventual finite-certificate obligations build actual deformed closed
placements from their threshold onward. -/
def closedPlacementOfEventualFiniteCertificateObligations
    {K0 : Nat}
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfRoleHinged
    O.transitions
    hk
    (O.orientation k hK hk)
    (O.period k hK hk)
    (O.generatedSeparation k hK hk)

@[simp]
theorem closedPlacementOfEventualFiniteCertificateObligations_point
    {K0 : Nat}
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfEventualFiniteCertificateObligations
      O k hK hk).point i v =
        GeneratedClosedChain.generatedPoint
          O.transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (O.orientation k hK hk)
          i v :=
  rfl

/-- If the eventual finite-certificate threshold is at most one, the resulting
placements cover every positive block count and hence give the exact
block-form target through `DeformedPlacement`. -/
theorem targetUpperConstructionFiveSixteen_of_eventualFiniteCertificateObligations
    {K0 : Nat}
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations K0)
    (hK0 : K0 <= 1) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
      (fun k hk =>
        closedPlacementOfEventualFiniteCertificateObligations
          O k (EventualRoleHingeClosure.threshold_le_of_atMostOne hK0 hk) hk)

end

end ClosedPlacementBuilderW14
end PachToth
end ErdosProblems1066
