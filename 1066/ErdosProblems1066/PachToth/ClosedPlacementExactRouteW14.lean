import ErdosProblems1066.PachToth.AllPositiveFiniteFieldsW14
import ErdosProblems1066.PachToth.ClosedPlacementBuilderW14
import ErdosProblems1066.PachToth.ExactSixteenTargetW14

set_option autoImplicit false

/-!
# W14 exact route through closed placements

This module is the exact-multiple Pach--Toth route whose geometric endpoint is
an actual `DeformedPlacement.ClosedPlacement`.  The remaining finite search
input is kept explicit: all-positive period equations and non-connector
lower-bound fields are assumptions, and the theorems below route them through
the W14 closed-placement builders before applying the checked indexed-chain
target reduction.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementExactRouteW14

noncomputable section

abbrev ExactSixteenBlockTarget (k : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt (16 * k)

abbrev PeriodEquationFields :=
  FiniteCertificateObligationsW12.PeriodEquationFields

abbrev AllPositiveNonConnectorFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

abbrev TableFamilyPackage :=
  FiniteCertificateObligationsW12.TableFamilyPackage

abbrev VectorPackage :=
  FiniteCertificateObligationsW12.VectorPackage

abbrev ListPackage :=
  FiniteCertificateObligationsW12.ListPackage

abbrev ExplicitAllPositiveCertificate :=
  ExactSixteenTargetW14.ExplicitAllPositiveCertificate

abbrev ExactMissingConcreteTableFields
    (F : AllPositiveFiniteFieldsW14.PeriodCandidateFamily) :=
  AllPositiveFiniteFieldsW14.ExactMissingConcreteTableFields F

/-! ## Closed-placement route -/

/-- A single closed placement gives the exact `16 * k` target at its block
count. -/
theorem targetUpperConstructionFiveSixteenAt_of_closedPlacement
    {k : Nat} (hk : 0 < k)
    (P : DeformedPlacement.ClosedPlacement k hk) :
    ExactSixteenBlockTarget k := by
  refine Exists.elim
    (IndexedChain.exists_config_with_independent_card_le_five_mul
      hk P.toIndexedChainRealization) ?_
  intro C hC
  refine Exists.intro C ?_
  intro s hs
  have hbound := hC s hs
  have hceil : Arithmetic.ceilDiv (5 * (16 * k)) 16 = 5 * k := by
    unfold Arithmetic.ceilDiv
    omega
  simpa [hceil] using hbound

/-- A closed-placement family gives the full exact-multiple target. -/
theorem targetUpperConstructionFiveSixteen_of_closedPlacements
    (H : forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteen := by
  exact DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements H

/-! ## Raw all-positive fields -/

/-- Raw W12 all-positive fields build the exact closed placement for one
positive block count. -/
def closedPlacementOfAllPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementBuilderW14.closedPlacementOfAllPositiveNonConnectorFields
    C k hk

@[simp]
theorem closedPlacementOfAllPositiveNonConnectorFields_point
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (v : FiniteGraph.LocalVertex) :
    (closedPlacementOfAllPositiveNonConnectorFields C k hk).point i v =
      GeneratedClosedChain.generatedPoint
        C.transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (C.orientation k hk)
        i v :=
  rfl

/-- Per-block exact target from raw all-positive fields, routed through the
closed-placement builder. -/
theorem targetUpperConstructionFiveSixteenAt_of_allPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k := by
  exact
    targetUpperConstructionFiveSixteenAt_of_closedPlacement hk
      (closedPlacementOfAllPositiveNonConnectorFields C k hk)

/-- Full exact-multiple target from raw all-positive fields, routed through
closed placements. -/
theorem targetUpperConstructionFiveSixteen_of_allPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_closedPlacements
      (fun k hk => closedPlacementOfAllPositiveNonConnectorFields C k hk)

/-! ## Explicit W14 all-positive certificate -/

def closedPlacementOfExplicitAllPositiveCertificate
    (C : ExplicitAllPositiveCertificate)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfAllPositiveNonConnectorFields
    C.toAllPositiveNonConnectorFields k hk

theorem targetUpperConstructionFiveSixteenAt_of_explicitAllPositiveCertificate
    (C : ExplicitAllPositiveCertificate)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k := by
  exact
    targetUpperConstructionFiveSixteenAt_of_closedPlacement hk
      (closedPlacementOfExplicitAllPositiveCertificate C k hk)

/-- Strongest exact `16 * k` route currently exposed here: the explicit W14
all-positive finite certificate fields build a family of actual closed
placements, and that family proves the exact-multiple target. -/
theorem targetUpperConstructionFiveSixteen_of_explicitAllPositiveCertificate
    (C : ExplicitAllPositiveCertificate) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_closedPlacements
      (fun k hk => closedPlacementOfExplicitAllPositiveCertificate C k hk)

/-! ## Concrete W13/W14 certificate surfaces -/

def closedPlacementOfConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementBuilderW14.closedPlacementOfConcreteValueMatrixFamily C k hk

theorem targetUpperConstructionFiveSixteenAt_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k := by
  exact
    targetUpperConstructionFiveSixteenAt_of_closedPlacement hk
      (closedPlacementOfConcreteValueMatrixFamily C k hk)

theorem targetUpperConstructionFiveSixteen_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_closedPlacements
      (fun k hk => closedPlacementOfConcreteValueMatrixFamily C k hk)

def closedPlacementOfCandidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementBuilderW14.closedPlacementOfCandidateValueMatrixFamily C k hk

theorem targetUpperConstructionFiveSixteenAt_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k := by
  exact
    targetUpperConstructionFiveSixteenAt_of_closedPlacement hk
      (closedPlacementOfCandidateValueMatrixFamily C k hk)

theorem targetUpperConstructionFiveSixteen_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_closedPlacements
      (fun k hk => closedPlacementOfCandidateValueMatrixFamily C k hk)

/-- W14 exact remaining concrete table fields, kept as explicit assumptions,
also route through the all-positive closed-placement builder. -/
def closedPlacementOfExactMissingConcreteTableFields
    {F : AllPositiveFiniteFieldsW14.PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfAllPositiveNonConnectorFields D.toFields k hk

theorem targetUpperConstructionFiveSixteenAt_of_exactMissingConcreteTableFields
    {F : AllPositiveFiniteFieldsW14.PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k := by
  exact
    targetUpperConstructionFiveSixteenAt_of_closedPlacement hk
      (closedPlacementOfExactMissingConcreteTableFields D k hk)

theorem targetUpperConstructionFiveSixteen_of_exactMissingConcreteTableFields
    {F : AllPositiveFiniteFieldsW14.PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_closedPlacements
      (fun k hk => closedPlacementOfExactMissingConcreteTableFields D k hk)

/-! ## Native table-package variants -/

def closedPlacementOfTableFamilyPackage
    (P : TableFamilyPackage)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementBuilderW14.closedPlacementOfTableFamilyPackage P k hk

theorem targetUpperConstructionFiveSixteen_of_tableFamilyPackage
    (P : TableFamilyPackage) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_closedPlacements
      (fun k hk => closedPlacementOfTableFamilyPackage P k hk)

def closedPlacementOfVectorPackage
    (P : VectorPackage)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementBuilderW14.closedPlacementOfVectorPackage P k hk

theorem targetUpperConstructionFiveSixteen_of_vectorPackage
    (P : VectorPackage) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_closedPlacements
      (fun k hk => closedPlacementOfVectorPackage P k hk)

def closedPlacementOfListPackage
    (P : ListPackage)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementBuilderW14.closedPlacementOfListPackage P k hk

theorem targetUpperConstructionFiveSixteen_of_listPackage
    (P : ListPackage) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_closedPlacements
      (fun k hk => closedPlacementOfListPackage P k hk)

end

end ClosedPlacementExactRouteW14
end PachToth
end ErdosProblems1066
