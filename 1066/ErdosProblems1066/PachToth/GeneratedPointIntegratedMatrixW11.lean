import ErdosProblems1066.PachToth.GeneratedPointClosureW11
import ErdosProblems1066.PachToth.GeneratedPointCertificateW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11
import ErdosProblems1066.PachToth.FlexibleAssemblyTargetW11

set_option autoImplicit false

/-!
# W11 generated-point integrated matrix

This file integrates the checked generated-point certificate, closure,
cross-block inequality, and flexible target facades.  It is a routing ledger:
every target theorem below remains conditional on an explicit field package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedPointIntegratedMatrixW11

noncomputable section

universe u

abbrev RoleHingedPeriodSearchFamily :=
  GeneratedPointClosureW11.RoleHingedPeriodSearchFamily

abbrev NormalizedPolynomialFields
    (F : RoleHingedPeriodSearchFamily) :=
  GeneratedPointClosureW11.NormalizedPolynomialFields F

abbrev NormalizedValueFields
    (F : RoleHingedPeriodSearchFamily) :=
  GeneratedPointClosureW11.NormalizedValueFields F

abbrev LowerBoundFields
    (F : RoleHingedPeriodSearchFamily) :=
  GeneratedPointClosureW11.LowerBoundFields F

abbrev CrossBlockPeriodSearchFamily :=
  GeneratedPointClosureW11.CrossBlockPeriodSearchFamily

abbrev CrossBlockInequalityLedger
    (F : CrossBlockPeriodSearchFamily) :=
  GeneratedPointClosureW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger
    (F : CrossBlockPeriodSearchFamily) :=
  CrossBlockInequalityClosureW11.CrossBlockClosureLedger F

abbrev FlexibleCandidateAssemblyFields :=
  FlexibleAssemblyTargetW11.CandidateFields

abbrev FinalConditionalFamily :=
  FlexibleAssemblyTargetW11.FinalConditionalFamily

abbrev CandidateValueMatrixFamily :=
  FlexibleAssemblyTargetW11.CandidateValueMatrixFamily

abbrev GeneratedPointTargetRow (alpha : Sort u) :=
  GeneratedPointClosureW11.GeneratedPointTargetRow alpha

abbrev ThresholdSmallCaseRoute (alpha : Sort u) :=
  FlexibleAssemblyTargetW11.ThresholdSmallCaseRoute alpha

abbrev CheckedRemainderRouteRow (alpha : Sort u) :=
  ArbitraryNBridgeW10.CheckedRemainderRouteRow alpha

/-! ## Explicit data ledger -/

/-- Field packages still supplied by external numeric checks. -/
structure RequiredDataLedger where
  generatedPointFields : GeneratedPointClosureW11.ExplicitFieldShapes
  crossBlockClosureLedgers : CrossBlockPeriodSearchFamily -> Type
  flexibleCandidateAssemblyFields : Type
  candidateValueMatrices : Type
  finalConditionalFamilies : Type

/-- The data-shape ledger for this integrated module. -/
def requiredDataLedger : RequiredDataLedger where
  generatedPointFields := GeneratedPointClosureW11.explicitFieldShapes
  crossBlockClosureLedgers := CrossBlockClosureLedger
  flexibleCandidateAssemblyFields := FlexibleCandidateAssemblyFields
  candidateValueMatrices := CandidateValueMatrixFamily
  finalConditionalFamilies := FinalConditionalFamily

/-! ## Cross-block closure route -/

/-- Repackage a generated cross-block inequality ledger in the W11 closure
wrapper used by the cross-block facade. -/
def toCrossBlockClosureLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    CrossBlockClosureLedger F where
  inequalityLedger := L

/-- Cross-block ledger route through both generated-point and closure facades. -/
structure CrossBlockClosureTargetRow
    (F : CrossBlockPeriodSearchFamily) where
  generatedPoint :
    GeneratedPointTargetRow (CrossBlockInequalityLedger F)
  closure :
    CheckedRemainderRouteRow (CrossBlockClosureLedger F)
  toClosureLedger :
    CrossBlockInequalityLedger F -> CrossBlockClosureLedger F
  separated :
    CrossBlockInequalityLedger F ->
      forall (k : Nat) (hk : 0 < k),
        CrossBlockInequalityClosureW11.GeneratedGlobalSeparationAt F k hk
  exactBlockTarget :
    CrossBlockInequalityLedger F ->
      forall (k : Nat) (_hk : 0 < k),
        PachToth.targetUpperConstructionFiveSixteenAt (16 * k)
  fixedTarget :
    CrossBlockInequalityLedger F ->
      forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    CrossBlockInequalityLedger F ->
      PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    CrossBlockInequalityLedger F ->
      PachToth.targetUpperConstructionFiveSixteenArbitrary
  arbitraryTargetSplit :
    CrossBlockInequalityLedger F ->
      PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- The checked cross-block closure row for one role-hinged family. -/
def crossBlockClosureTargetRow
    (F : CrossBlockPeriodSearchFamily) :
    CrossBlockClosureTargetRow F where
  generatedPoint := GeneratedPointClosureW11.matrix.crossBlockLedger F
  closure :=
    (CrossBlockInequalityClosureW11.conditionalTargetRouteLedger F).crossBlockClosure
  toClosureLedger := toCrossBlockClosureLedger
  separated := fun L k hk =>
    CrossBlockInequalityClosureW11.CrossBlockClosureLedger.generatedGlobalSeparation
      (toCrossBlockClosureLedger L) k hk
  exactBlockTarget := fun L k hk =>
    CrossBlockInequalityClosureW11.CrossBlockClosureLedger.targetUpperConstructionFiveSixteenAt_exactBlock
      (toCrossBlockClosureLedger L) k hk
  fixedTarget := fun L n =>
    CrossBlockInequalityClosureW11.CrossBlockClosureLedger.targetUpperConstructionFiveSixteenAt_checkedRemainders
      (toCrossBlockClosureLedger L) n
  eventualTarget := fun L =>
    GeneratedPointClosureW11.GeneratedPointTargetRow.eventualTarget_of_arbitrary
      (CrossBlockInequalityClosureW11.CrossBlockClosureLedger.targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
        (toCrossBlockClosureLedger L))
  arbitraryTarget := fun L =>
    CrossBlockInequalityClosureW11.CrossBlockClosureLedger.targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
      (toCrossBlockClosureLedger L)
  arbitraryTargetSplit := fun L =>
    CrossBlockInequalityClosureW11.CrossBlockClosureLedger.targetUpperConstructionFiveSixteenArbitrary_splitBridge
      (toCrossBlockClosureLedger L)

/-! ## Integrated matrix -/

/-- Integrated W11 matrix for generated-point data.

The record stores checked routes only; it does not provide any instance of the
numeric field packages listed in `requiredDataLedger`. -/
structure Matrix where
  requiredData : RequiredDataLedger
  generatedPointClosure : GeneratedPointClosureW11.Matrix
  flexibleAssemblyTarget : FlexibleAssemblyTargetW11.Matrix
  crossBlockConditionalRoutes :
    forall F : CrossBlockPeriodSearchFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  normalizedPolynomial :
    forall F : RoleHingedPeriodSearchFamily,
      GeneratedPointTargetRow (NormalizedPolynomialFields F)
  normalizedValue :
    forall F : RoleHingedPeriodSearchFamily,
      GeneratedPointTargetRow (NormalizedValueFields F)
  lowerBound :
    forall F : RoleHingedPeriodSearchFamily,
      GeneratedPointTargetRow (LowerBoundFields F)
  crossBlockLedger :
    forall F : CrossBlockPeriodSearchFamily,
      CrossBlockClosureTargetRow F
  flexibleCandidateAssembly :
    ThresholdSmallCaseRoute FlexibleCandidateAssemblyFields
  finalConditionalFamily :
    ThresholdSmallCaseRoute FinalConditionalFamily
  candidateValueMatrices :
    CheckedRemainderRouteRow CandidateValueMatrixFamily

/-- The checked integrated W11 generated-point matrix. -/
def matrix : Matrix where
  requiredData := requiredDataLedger
  generatedPointClosure := GeneratedPointClosureW11.matrix
  flexibleAssemblyTarget := FlexibleAssemblyTargetW11.matrix
  crossBlockConditionalRoutes :=
    CrossBlockInequalityClosureW11.conditionalTargetRouteLedger
  normalizedPolynomial := GeneratedPointClosureW11.matrix.normalizedPolynomial
  normalizedValue := GeneratedPointClosureW11.matrix.normalizedValue
  lowerBound := GeneratedPointClosureW11.matrix.lowerBound
  crossBlockLedger := crossBlockClosureTargetRow
  flexibleCandidateAssembly := FlexibleAssemblyTargetW11.matrix.candidateFields
  finalConditionalFamily := FlexibleAssemblyTargetW11.matrix.finalConditionalFamily
  candidateValueMatrices :=
    FlexibleAssemblyTargetW11.matrix.w10CandidateValueMatrices

/-! ## Generated-point field package target projections -/

theorem targetUpperConstructionFiveSixteen_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.normalizedPolynomial F).exactTarget C

theorem targetUpperConstructionFiveSixteenAt_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.normalizedPolynomial F).fixedTarget C n

theorem targetUpperConstructionFiveSixteenEventually_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.normalizedPolynomial F).eventualTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.normalizedPolynomial F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.normalizedValue F).exactTarget C

theorem targetUpperConstructionFiveSixteenAt_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.normalizedValue F).fixedTarget C n

theorem targetUpperConstructionFiveSixteenEventually_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.normalizedValue F).eventualTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.normalizedValue F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.lowerBound F).exactTarget C

theorem targetUpperConstructionFiveSixteenAt_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.lowerBound F).fixedTarget C n

theorem targetUpperConstructionFiveSixteenEventually_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.lowerBound F).eventualTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.lowerBound F).arbitraryTarget C

/-! ## Cross-block ledger target projections -/

theorem separated_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    CrossBlockInequalityClosureW11.GeneratedGlobalSeparationAt F k hk :=
  (matrix.crossBlockLedger F).separated L k hk

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.crossBlockLedger F).exactBlockTarget L k hk

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.crossBlockLedger F).fixedTarget L n

theorem targetUpperConstructionFiveSixteenEventually_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockLedger F).eventualTarget L

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockLedger F).arbitraryTarget L

theorem targetUpperConstructionFiveSixteenArbitrary_split_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockLedger F).arbitraryTargetSplit L

/-! ## Flexible target-facade projections -/

theorem targetUpperConstructionFiveSixteen_of_flexibleCandidateAssemblyFields
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.flexibleCandidateAssembly.exactTarget F

theorem targetUpperConstructionFiveSixteenAt_of_flexibleCandidateAssemblyFields
    (F : FlexibleCandidateAssemblyFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.flexibleCandidateAssembly.fixedTarget F n

theorem targetUpperConstructionFiveSixteenEventually_of_flexibleCandidateAssemblyFields
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.flexibleCandidateAssembly.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_flexibleCandidateAssemblyFields
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flexibleCandidateAssembly.arbitraryTarget F

theorem smallCases_of_flexibleCandidateAssemblyFields
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo
      (matrix.flexibleCandidateAssembly.threshold F) :=
  matrix.flexibleCandidateAssembly.smallCases F

theorem targetUpperConstructionFiveSixteenEventually_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.finalConditionalFamily.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.finalConditionalFamily.arbitraryTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixFamily
    (F : CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.candidateValueMatrices.arbitraryTarget F

end

end GeneratedPointIntegratedMatrixW11
end PachToth
end ErdosProblems1066
