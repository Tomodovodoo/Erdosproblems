import ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11
import ErdosProblems1066.PachToth.GeneratedPointCertificateW11
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11
import ErdosProblems1066.PachToth.ArbitraryNBridgeW10

set_option autoImplicit false

/-!
# W11 cross-block inequality closure

This file is a conditional closure ledger.  It does not add any numeric
cross-block data.  Instead, it records how a supplied W11 cross-block
inequality ledger projects to generated global separation, generated
closed-placement families, and the checked exact/arbitrary target facades.

The final target statements below all keep their data arguments explicit.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockInequalityClosureW11

universe u

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockInequalityLedgerW11.RoleHingedPeriodSearchFamily

abbrev CrossBlockInequalityLedger :=
  CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger

abbrev UpperTriangleGeneratedPointPolynomialRowFamilies :=
  CrossBlockInequalityLedgerW11.UpperTriangleGeneratedPointPolynomialRowFamilies

abbrev GeneratedPointNonConnectorPolynomialTableFamily :=
  CrossBlockInequalityLedgerW11.GeneratedPointNonConnectorPolynomialTableFamily

abbrev NonConnectorValueMatrixFamily :=
  CrossBlockInequalityLedgerW11.NonConnectorValueMatrixFamily

abbrev NonConnectorLowerTableFamily :=
  CrossBlockInequalityLedgerW11.NonConnectorLowerTableFamily

abbrev CrossBlockLowerBounds :=
  GeneratedPointCertificateW11.CrossBlockLowerBounds

abbrev RoleHingedGeneratedClosureFamily :=
  GeneratedPointCertificateW11.RoleHingedGeneratedClosureFamily

abbrev ClosedPlacementPackage :=
  ArbitraryNBridgeW10.ClosedPlacementPackage

abbrev CheckedRemainderRouteRow (alpha : Sort u) :=
  ArbitraryNBridgeW10.CheckedRemainderRouteRow alpha

abbrev FlexibleNonRigidRouteFields :=
  FlexibleTransitionSearchW11.NonRigidRouteFields

abbrev GeneratedGlobalSeparationAt
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  GeneratedPointCertificateW11.GeneratedGlobalSeparationAt F k hk

/-- A named closure wrapper around a supplied W11 cross-block inequality
ledger.  The wrapper adds no search rows; all downstream fields are projections
from `inequalityLedger`. -/
structure CrossBlockClosureLedger
    (F : RoleHingedPeriodSearchFamily) where
  inequalityLedger : CrossBlockInequalityLedger F

namespace CrossBlockClosureLedger

variable {F : RoleHingedPeriodSearchFamily}

/-- The row-grouped polynomial family extracted from the underlying ledger. -/
def toPolynomialRowFamilies
    (C : CrossBlockClosureLedger F) :
    UpperTriangleGeneratedPointPolynomialRowFamilies F :=
  C.inequalityLedger.toPolynomialRowFamilies

/-- The generated-point polynomial-table family extracted from the ledger. -/
def toGeneratedPointTableFamily
    (C : CrossBlockClosureLedger F) :
    GeneratedPointNonConnectorPolynomialTableFamily F :=
  C.toPolynomialRowFamilies.toGeneratedPointTableFamily

/-- The value-matrix family extracted from the ledger. -/
def toNonConnectorValueMatrixFamily
    (C : CrossBlockClosureLedger F) :
    NonConnectorValueMatrixFamily F :=
  C.inequalityLedger.toNonConnectorValueMatrixFamily

/-- The lower-table family extracted from the ledger. -/
def toNonConnectorLowerTableFamily
    (C : CrossBlockClosureLedger F) :
    NonConnectorLowerTableFamily F :=
  C.inequalityLedger.toNonConnectorLowerTableFamily

/-- The raw cross-block lower-bound facade extracted from the lower-table
family. -/
def toCrossBlockLowerBounds
    (C : CrossBlockClosureLedger F) :
    CrossBlockLowerBounds F :=
  C.toNonConnectorLowerTableFamily.toCrossBlockLowerBounds

/-- The generated closure family obtained from the lower-bound facade. -/
def toRoleHingedGeneratedClosureFamily
    (C : CrossBlockClosureLedger F) :
    RoleHingedGeneratedClosureFamily :=
  C.toCrossBlockLowerBounds.toRoleHingedGeneratedClosureFamily

/-- Generated global separation at each positive block count, projected
directly from the inequality ledger. -/
theorem generatedGlobalSeparation
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  C.inequalityLedger.separated k hk

/-- The reduced metric hypotheses obtained from the generated-separation
projection. -/
def reducedMetricHypotheses
    (C : CrossBlockClosureLedger F)
    {k : Nat} (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  GeneratedPointCertificateW11.reducedMetricHypothesesOfSeparation
    F (k := k) hk (C.generatedGlobalSeparation k hk)

/-- The explicit transition closed-placement certificate at one block count. -/
def explicitTransitionClosedPlacementCertificate
    (C : CrossBlockClosureLedger F)
    {k : Nat} (hk : 0 < k) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk :=
  GeneratedPointCertificateW11.explicitTransitionClosedPlacementCertificateOfSeparation
    F (k := k) hk (C.generatedGlobalSeparation k hk)

/-- A generated closed placement at one positive block count. -/
def closedPlacementAt
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  GeneratedPointCertificateW11.closedPlacementOfSeparation
    F (k := k) hk (C.generatedGlobalSeparation k hk)

/-- The generated closed-placement family obtained from the ledger. -/
def closedPlacementFamily
    (C : CrossBlockClosureLedger F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk => C.closedPlacementAt k hk

/-- Existence form of the generated closed-placement projection. -/
theorem exists_closedPlacementAt
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point =
        GeneratedClosedChain.generatedPoint
          F.transitions.toFigure2TransitionObligations
          hk BaseTransitionRealization.exactBase (F.orientation k hk) :=
  GeneratedPointCertificateW11.exists_closedPlacement_of_separation
    F (k := k) hk (C.generatedGlobalSeparation k hk)

/-- Exact-block target at one positive block count, still conditional on the
closure ledger. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  GeneratedPointCertificateW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_separation
    F (k := k) hk (C.generatedGlobalSeparation k hk)

/-- The closed-placement package consumed by the W10 arbitrary-`n` bridge. -/
def toClosedPlacementPackage
    (C : CrossBlockClosureLedger F) :
    ClosedPlacementPackage where
  placement := C.closedPlacementFamily

/-- Exact-block Pach--Toth target, conditional on the closure ledger. -/
theorem targetUpperConstructionFiveSixteen
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toClosedPlacementPackage.targetUpperConstructionFiveSixteen

/-- Exact target recovered through the closed-placement package route. -/
theorem targetUpperConstructionFiveSixteen_of_closedPlacementPackage
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.targetUpperConstructionFiveSixteen

/-- Combined closed-placement existence and exact-block target, conditional on
the closure ledger. -/
theorem exists_closedPlacement_and_target
    (C : CrossBlockClosureLedger F) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint
              F.transitions.toFigure2TransitionObligations
              hk BaseTransitionRealization.exactBase (F.orientation k hk))
      PachToth.targetUpperConstructionFiveSixteen :=
  And.intro
    (fun k hk => C.exists_closedPlacementAt k hk)
    C.targetUpperConstructionFiveSixteen

/-- W10 checked-remainder row for cross-block closure ledgers. -/
def checkedRemainderRouteRow
    (F : RoleHingedPeriodSearchFamily) :
    CheckedRemainderRouteRow (CrossBlockClosureLedger F) :=
  ArbitraryNBridgeW10.checkedRemainderRouteRow
    (fun C => CrossBlockClosureLedger.targetUpperConstructionFiveSixteen C)

/-- Fixed-`n` target routed through the checked remainder bridge, conditional
on the closure ledger. -/
theorem targetUpperConstructionFiveSixteenAt_checkedRemainders
    (C : CrossBlockClosureLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (checkedRemainderRouteRow F).fixedTarget C n

/-- Arbitrary-`n` target routed through the checked remainder bridge,
conditional on the closure ledger. -/
theorem targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (checkedRemainderRouteRow F).arbitraryTarget C

/-- Arbitrary-`n` target routed through the closed-placement split bridge,
conditional on the closure ledger. -/
theorem targetUpperConstructionFiveSixteenArbitrary_splitBridge
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toClosedPlacementPackage.targetUpperConstructionFiveSixteenArbitrary_splitBridge

end CrossBlockClosureLedger

/-! ## Companion route rows for flexible non-rigid transitions -/

/-- W10 checked-remainder row for a supplied W11 flexible non-rigid route. -/
def flexibleCheckedRemainderRouteRow :
    CheckedRemainderRouteRow FlexibleNonRigidRouteFields :=
  ArbitraryNBridgeW10.checkedRemainderRouteRow
    FlexibleTransitionSearchW11.NonRigidRouteFields.targetUpperConstructionFiveSixteen

/-- Exact Pach--Toth target from a supplied W11 flexible non-rigid route. -/
theorem targetUpperConstructionFiveSixteen_of_flexibleRoute
    (R : FlexibleNonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  R.targetUpperConstructionFiveSixteen

/-- Fixed-`n` target from a supplied W11 flexible route and checked
remainders. -/
theorem targetUpperConstructionFiveSixteenAt_of_flexibleRoute_checkedRemainders
    (R : FlexibleNonRigidRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  flexibleCheckedRemainderRouteRow.fixedTarget R n

/-- Arbitrary-`n` target from a supplied W11 flexible route and checked
remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_flexibleRoute_checkedRemainders
    (R : FlexibleNonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  flexibleCheckedRemainderRouteRow.arbitraryTarget R

/-- The two conditional route rows exposed by this closure module: one for
cross-block inequality ledgers and one for flexible non-rigid route fields. -/
structure ConditionalTargetRouteLedger
    (F : RoleHingedPeriodSearchFamily) where
  crossBlockClosure :
    CheckedRemainderRouteRow (CrossBlockClosureLedger F)
  flexibleRoute :
    CheckedRemainderRouteRow FlexibleNonRigidRouteFields

/-- Public conditional target-route ledger. -/
def conditionalTargetRouteLedger
    (F : RoleHingedPeriodSearchFamily) :
    ConditionalTargetRouteLedger F where
  crossBlockClosure :=
    CrossBlockClosureLedger.checkedRemainderRouteRow F
  flexibleRoute := flexibleCheckedRemainderRouteRow

end

end CrossBlockInequalityClosureW11
end PachToth
end ErdosProblems1066
