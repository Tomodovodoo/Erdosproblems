import ErdosProblems1066.PachToth.GeneratedPointIntegratedMatrixW11
import ErdosProblems1066.PachToth.TransitionIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix
import ErdosProblems1066.PachToth.PachTothW11ClosureMatrix
import ErdosProblems1066.PachToth.ArbitraryNTargetClosureW11
import ErdosProblems1066.PachToth.ConditionalUpper

set_option autoImplicit false

/-!
# W11 generated-point target integration

This file is a target-facing adapter over the generated-point W11 rows and
the broader Pach--Toth W11 conditional facades.  It stores route ledgers only:
the numeric polynomial, value, lower-bound, and row-grouped cross-block
packages remain explicit inputs to every public theorem below.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedTargetIntegratedW11

noncomputable section

universe u

abbrev RoleHingedPeriodSearchFamily :=
  GeneratedPointIntegratedMatrixW11.RoleHingedPeriodSearchFamily

abbrev NormalizedPolynomialFields
    (F : RoleHingedPeriodSearchFamily) :=
  GeneratedPointIntegratedMatrixW11.NormalizedPolynomialFields F

abbrev NormalizedValueFields
    (F : RoleHingedPeriodSearchFamily) :=
  GeneratedPointIntegratedMatrixW11.NormalizedValueFields F

abbrev LowerBoundFields
    (F : RoleHingedPeriodSearchFamily) :=
  GeneratedPointIntegratedMatrixW11.LowerBoundFields F

abbrev CrossBlockPeriodSearchFamily :=
  GeneratedPointIntegratedMatrixW11.CrossBlockPeriodSearchFamily

abbrev CrossBlockInequalityLedger
    (F : CrossBlockPeriodSearchFamily) :=
  GeneratedPointIntegratedMatrixW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger
    (F : CrossBlockPeriodSearchFamily) :=
  GeneratedPointIntegratedMatrixW11.CrossBlockClosureLedger F

abbrev FlexibleCandidateAssemblyFields :=
  GeneratedPointIntegratedMatrixW11.FlexibleCandidateAssemblyFields

abbrev CandidateValueMatrixFamily :=
  GeneratedPointIntegratedMatrixW11.CandidateValueMatrixFamily

abbrev FinalConditionalFamily :=
  GeneratedPointIntegratedMatrixW11.FinalConditionalFamily

abbrev GeneratedPointTargetRow (alpha : Sort u) :=
  GeneratedPointIntegratedMatrixW11.GeneratedPointTargetRow alpha

abbrev CheckedRemainderRouteRow (alpha : Sort u) :=
  ArbitraryNBridgeW10.CheckedRemainderRouteRow alpha

abbrev ThresholdSmallCaseRoute (alpha : Sort u) :=
  FlexibleAssemblyTargetW11.ThresholdSmallCaseRoute alpha

abbrev ArbitraryNTargetFacade :=
  ArbitraryNTargetClosureW11.ArbitraryNTargetFacade

abbrev ThresholdTargetFacade :=
  ArbitraryNTargetClosureW11.ThresholdTargetFacade

/-! ## Target route records -/

/-- A target-facing route from an explicit package to the exact, fixed,
eventual, arbitrary, and facade forms of the Pach--Toth target. -/
structure TargetRoute (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

namespace TargetRoute

/-- Promote an arbitrary-`n` route to the eventual facade with threshold zero. -/
theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

/-- Build a target route from an exact target and a supplied arbitrary route. -/
def ofExactAndArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    TargetRoute alpha where
  exactTarget := exactTarget
  fixedTarget := fun a =>
    (ArbitraryNTargetClosureW11.targetFacadeOfExactTargetAndArbitrary
      (exactTarget a) (arbitraryTarget a)).fixedTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (arbitraryTarget a)
  arbitraryTarget := arbitraryTarget
  targetFacade := fun a =>
    ArbitraryNTargetClosureW11.targetFacadeOfExactTargetAndArbitrary
      (exactTarget a) (arbitraryTarget a)

/-- Reuse a generated-point row as a target-facing route. -/
def ofGeneratedPointRow
    {alpha : Sort u}
    (R : GeneratedPointTargetRow alpha) :
    TargetRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := fun a =>
    { fixedTarget := R.fixedTarget a
      arbitraryTarget := R.arbitraryTarget a }

/-- Reuse a checked-remainder route as a target-facing route. -/
def ofCheckedRemainderRoute
    {alpha : Sort u}
    (R : CheckedRemainderRouteRow alpha) :
    TargetRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (R.arbitraryTarget a)
  arbitraryTarget := R.arbitraryTarget
  targetFacade := fun a =>
    { fixedTarget := R.fixedTarget a
      arbitraryTarget := R.arbitraryTarget a }

/-- Reuse an arbitrary-`n` exact-target closure row as a target route. -/
def ofExactTargetClosureRow
    {alpha : Sort u}
    (R : ArbitraryNTargetClosureW11.ExactTargetClosureRow alpha) :
    TargetRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (R.arbitraryTarget a)
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

/-- Reuse a flexible threshold/small-case row as a target route. -/
def ofThresholdSmallCaseRoute
    {alpha : Sort u}
    (R : ThresholdSmallCaseRoute alpha) :
    TargetRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := fun a => R.eventualTarget a
  arbitraryTarget := fun a => R.arbitraryTarget a
  targetFacade := fun a =>
    ArbitraryNTargetClosureW11.targetFacadeOfFlexibleTargetRoute R a

end TargetRoute

/-- A target route that also records the explicit threshold split used by the
flexible target facade. -/
structure ThresholdTargetRoute (alpha : Sort u) where
  route : TargetRoute alpha
  threshold : alpha -> Nat
  largeTarget :
    forall a : alpha, forall n : Nat, threshold a <= n ->
      PachToth.targetUpperConstructionFiveSixteenAt n
  smallCases :
    forall a : alpha,
      PachToth.targetUpperConstructionFiveSixteenSmallUpTo (threshold a)
  thresholdFacade : alpha -> ThresholdTargetFacade

namespace ThresholdTargetRoute

/-- Reuse a flexible threshold/small-case row with its threshold data. -/
def ofThresholdSmallCaseRoute
    {alpha : Sort u}
    (R : ThresholdSmallCaseRoute alpha) :
    ThresholdTargetRoute alpha where
  route := TargetRoute.ofThresholdSmallCaseRoute R
  threshold := R.threshold
  largeTarget := R.largeTarget
  smallCases := R.smallCases
  thresholdFacade := fun a =>
    ArbitraryNTargetClosureW11.thresholdFacadeOfFlexibleTargetRoute R a

end ThresholdTargetRoute

/-! ## Explicit input ledger -/

/-- Numeric and search package shapes that this target integration still
requires from external generated data. -/
structure RequiredGeneratedPointInputs where
  normalizedPolynomialFields : RoleHingedPeriodSearchFamily -> Prop
  normalizedValueFields : RoleHingedPeriodSearchFamily -> Type
  lowerBoundFields : RoleHingedPeriodSearchFamily -> Type
  crossBlockInequalityLedgers : CrossBlockPeriodSearchFamily -> Type
  flexibleCandidateAssemblyFields : Type
  candidateValueMatrices : Type
  finalConditionalFamilies : Type

/-- Public ledger of the explicit generated-point inputs. -/
def requiredGeneratedPointInputs : RequiredGeneratedPointInputs where
  normalizedPolynomialFields := NormalizedPolynomialFields
  normalizedValueFields := NormalizedValueFields
  lowerBoundFields := LowerBoundFields
  crossBlockInequalityLedgers := CrossBlockInequalityLedger
  flexibleCandidateAssemblyFields := FlexibleCandidateAssemblyFields
  candidateValueMatrices := CandidateValueMatrixFamily
  finalConditionalFamilies := FinalConditionalFamily

/-! ## Generated-point source routes -/

/-- Cross-block ledger route with separation and exact-block projections kept
next to the all-`n` target route. -/
structure CrossBlockTargetRoute
    (F : CrossBlockPeriodSearchFamily) where
  toClosureLedger :
    CrossBlockInequalityLedger F -> CrossBlockClosureLedger F
  route : TargetRoute (CrossBlockInequalityLedger F)
  separated :
    CrossBlockInequalityLedger F ->
      forall (k : Nat) (hk : 0 < k),
        CrossBlockInequalityClosureW11.GeneratedGlobalSeparationAt F k hk
  exactBlockTarget :
    CrossBlockInequalityLedger F ->
      forall (k : Nat) (_hk : 0 < k),
        PachToth.targetUpperConstructionFiveSixteenAt (16 * k)
  arbitraryTargetSplit :
    CrossBlockInequalityLedger F ->
      PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- Target route for one generated cross-block inequality ledger family. -/
def crossBlockTargetRoute
    (F : CrossBlockPeriodSearchFamily) :
    CrossBlockTargetRoute F where
  toClosureLedger := GeneratedPointIntegratedMatrixW11.toCrossBlockClosureLedger
  route :=
    { exactTarget :=
        (GeneratedPointIntegratedMatrixW11.matrix.crossBlockLedger F).generatedPoint.exactTarget
      fixedTarget :=
        (GeneratedPointIntegratedMatrixW11.matrix.crossBlockLedger F).fixedTarget
      eventualTarget :=
        (GeneratedPointIntegratedMatrixW11.matrix.crossBlockLedger F).eventualTarget
      arbitraryTarget :=
        (GeneratedPointIntegratedMatrixW11.matrix.crossBlockLedger F).arbitraryTarget
      targetFacade := fun L =>
        { fixedTarget :=
            (GeneratedPointIntegratedMatrixW11.matrix.crossBlockLedger F).fixedTarget L
          arbitraryTarget :=
            (GeneratedPointIntegratedMatrixW11.matrix.crossBlockLedger F).arbitraryTarget L } }
  separated :=
    (GeneratedPointIntegratedMatrixW11.matrix.crossBlockLedger F).separated
  exactBlockTarget :=
    (GeneratedPointIntegratedMatrixW11.matrix.crossBlockLedger F).exactBlockTarget
  arbitraryTargetSplit :=
    (GeneratedPointIntegratedMatrixW11.matrix.crossBlockLedger F).arbitraryTargetSplit

/-- Source-facing target routes from the generated-point integrated matrix. -/
structure GeneratedPointRoutes where
  normalizedPolynomial :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (NormalizedPolynomialFields F)
  normalizedValue :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (NormalizedValueFields F)
  lowerBound :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (LowerBoundFields F)
  crossBlockLedger :
    forall F : CrossBlockPeriodSearchFamily,
      CrossBlockTargetRoute F
  flexibleCandidateAssembly :
    ThresholdTargetRoute FlexibleCandidateAssemblyFields
  candidateValueMatrices :
    TargetRoute CandidateValueMatrixFamily
  finalConditionalFamily :
    ThresholdTargetRoute FinalConditionalFamily

/-- Checked source-facing generated-point routes. -/
def generatedPointRoutes : GeneratedPointRoutes where
  normalizedPolynomial := fun F =>
    TargetRoute.ofGeneratedPointRow
      (GeneratedPointIntegratedMatrixW11.matrix.normalizedPolynomial F)
  normalizedValue := fun F =>
    TargetRoute.ofGeneratedPointRow
      (GeneratedPointIntegratedMatrixW11.matrix.normalizedValue F)
  lowerBound := fun F =>
    TargetRoute.ofGeneratedPointRow
      (GeneratedPointIntegratedMatrixW11.matrix.lowerBound F)
  crossBlockLedger := crossBlockTargetRoute
  flexibleCandidateAssembly :=
    ThresholdTargetRoute.ofThresholdSmallCaseRoute
      GeneratedPointIntegratedMatrixW11.matrix.flexibleCandidateAssembly
  candidateValueMatrices :=
    TargetRoute.ofCheckedRemainderRoute
      GeneratedPointIntegratedMatrixW11.matrix.candidateValueMatrices
  finalConditionalFamily :=
    ThresholdTargetRoute.ofThresholdSmallCaseRoute
      GeneratedPointIntegratedMatrixW11.matrix.finalConditionalFamily

/-! ## Broad W11 facade routes -/

def closureNormalizedPolynomialRoute
    (F : RoleHingedPeriodSearchFamily) :
    TargetRoute (NormalizedPolynomialFields F) :=
  TargetRoute.ofExactAndArbitrary
    (fun C =>
      PachTothW11ClosureMatrix.targetUpperConstructionFiveSixteen_of_w11NormalizedPolynomialFields C)
    (fun C =>
      PachTothW11ClosureMatrix.targetUpperConstructionFiveSixteenArbitrary_of_w11NormalizedPolynomialFields C)

def closureNormalizedValueRoute
    (F : RoleHingedPeriodSearchFamily) :
    TargetRoute (NormalizedValueFields F) :=
  TargetRoute.ofExactAndArbitrary
    (fun C =>
      PachTothW11ClosureMatrix.targetUpperConstructionFiveSixteen_of_w11NormalizedValueFields C)
    (fun C =>
      PachTothW11ClosureMatrix.targetUpperConstructionFiveSixteenArbitrary_of_w11NormalizedValueFields C)

def closureLowerBoundRoute
    (F : RoleHingedPeriodSearchFamily) :
    TargetRoute (LowerBoundFields F) :=
  TargetRoute.ofExactAndArbitrary
    (fun C =>
      PachTothW11ClosureMatrix.targetUpperConstructionFiveSixteen_of_w11LowerBoundFields C)
    (fun C =>
      PachTothW11ClosureMatrix.targetUpperConstructionFiveSixteenArbitrary_of_w11LowerBoundFields C)

def integratedNormalizedPolynomialRoute
    (F : RoleHingedPeriodSearchFamily) :
    TargetRoute (NormalizedPolynomialFields F) :=
  TargetRoute.ofExactAndArbitrary
    (fun C =>
      PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_generatedPointNormalizedPolynomial C)
    (fun C =>
      PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_generatedPointNormalizedPolynomial C)

def integratedNormalizedValueRoute
    (F : RoleHingedPeriodSearchFamily) :
    TargetRoute (NormalizedValueFields F) :=
  TargetRoute.ofExactAndArbitrary
    (fun C =>
      PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_generatedPointNormalizedValue C)
    (fun C =>
      PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_generatedPointNormalizedValue C)

def integratedLowerBoundRoute
    (F : RoleHingedPeriodSearchFamily) :
    TargetRoute (LowerBoundFields F) :=
  TargetRoute.ofExactAndArbitrary
    (fun C =>
      PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_generatedPointLowerBound C)
    (fun C =>
      PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_generatedPointLowerBound C)

def arbitraryNNormalizedPolynomialRoute
    (F : RoleHingedPeriodSearchFamily) :
    TargetRoute (NormalizedPolynomialFields F) :=
  TargetRoute.ofExactTargetClosureRow
    (ArbitraryNTargetClosureW11.matrix.generatedPointNormalizedPolynomialFields F)

def arbitraryNNormalizedValueRoute
    (F : RoleHingedPeriodSearchFamily) :
    TargetRoute (NormalizedValueFields F) :=
  TargetRoute.ofExactTargetClosureRow
    (ArbitraryNTargetClosureW11.matrix.generatedPointNormalizedValueFields F)

def arbitraryNLowerBoundRoute
    (F : RoleHingedPeriodSearchFamily) :
    TargetRoute (LowerBoundFields F) :=
  TargetRoute.ofExactTargetClosureRow
    (ArbitraryNTargetClosureW11.matrix.generatedPointLowerBoundFields F)

def integratedCrossBlockClosureRoute
    (F : CrossBlockPeriodSearchFamily) :
    TargetRoute (CrossBlockClosureLedger F) :=
  TargetRoute.ofCheckedRemainderRoute
    ((PachTothW11IntegratedMatrix.matrix.crossBlockClosureRoutes F).crossBlockClosure)

def transitionRouteFieldsRoute :
    TargetRoute TransitionIntegratedW11.TransitionRouteFields :=
  TargetRoute.ofExactAndArbitrary
    TransitionIntegratedW11.targetUpperConstructionFiveSixteen_of_transitionRouteFields
    TransitionIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields

/-- Routes through the broad W11 Pach--Toth facades. -/
structure BroadW11FacadeRoutes where
  closureNormalizedPolynomial :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (NormalizedPolynomialFields F)
  closureNormalizedValue :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (NormalizedValueFields F)
  closureLowerBound :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (LowerBoundFields F)
  integratedNormalizedPolynomial :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (NormalizedPolynomialFields F)
  integratedNormalizedValue :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (NormalizedValueFields F)
  integratedLowerBound :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (LowerBoundFields F)
  arbitraryNNormalizedPolynomial :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (NormalizedPolynomialFields F)
  arbitraryNNormalizedValue :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (NormalizedValueFields F)
  arbitraryNLowerBound :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRoute (LowerBoundFields F)
  integratedCrossBlockClosure :
    forall F : CrossBlockPeriodSearchFamily,
      TargetRoute (CrossBlockClosureLedger F)
  transitionRouteFields :
    TargetRoute TransitionIntegratedW11.TransitionRouteFields

/-- Checked routes through the broad W11 facades. -/
def broadW11FacadeRoutes : BroadW11FacadeRoutes where
  closureNormalizedPolynomial := closureNormalizedPolynomialRoute
  closureNormalizedValue := closureNormalizedValueRoute
  closureLowerBound := closureLowerBoundRoute
  integratedNormalizedPolynomial := integratedNormalizedPolynomialRoute
  integratedNormalizedValue := integratedNormalizedValueRoute
  integratedLowerBound := integratedLowerBoundRoute
  arbitraryNNormalizedPolynomial := arbitraryNNormalizedPolynomialRoute
  arbitraryNNormalizedValue := arbitraryNNormalizedValueRoute
  arbitraryNLowerBound := arbitraryNLowerBoundRoute
  integratedCrossBlockClosure := integratedCrossBlockClosureRoute
  transitionRouteFields := transitionRouteFieldsRoute

/-! ## Imported ledgers and blockers -/

/-- Existing W11 ledgers imported by this target integration file. -/
structure ImportedW11Ledgers where
  generatedPointClosure : GeneratedPointClosureW11.Matrix
  generatedPointIntegrated : GeneratedPointIntegratedMatrixW11.Matrix
  transitionIntegrated : TransitionIntegratedW11.Matrix
  arbitraryNTargetClosure : ArbitraryNTargetClosureW11.Matrix
  pachTothW11Closure : PachTothW11ClosureMatrix.Matrix
  pachTothW11Integrated : PachTothW11IntegratedMatrix.Matrix

/-- Imported checked W11 ledgers. -/
def importedW11Ledgers : ImportedW11Ledgers where
  generatedPointClosure := GeneratedPointClosureW11.matrix
  generatedPointIntegrated := GeneratedPointIntegratedMatrixW11.matrix
  transitionIntegrated := TransitionIntegratedW11.matrix
  arbitraryNTargetClosure := ArbitraryNTargetClosureW11.matrix
  pachTothW11Closure := PachTothW11ClosureMatrix.matrix
  pachTothW11Integrated := PachTothW11IntegratedMatrix.matrix

/-- Concrete transition blockers carried forward from the W11 transition
integration layer. -/
structure TransitionBlockers where
  concreteFourTargetRouteClaim :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  completedFilteredRoute :
    TransitionIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  fullSameRestShortcut :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap

/-- Checked blockers imported from `TransitionIntegratedW11`. -/
def transitionBlockers : TransitionBlockers where
  concreteFourTargetRouteClaim :=
    TransitionIntegratedW11.concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    TransitionIntegratedW11.concreteFourTargetCompletedFilteredRoute_blocked
  fullSameRestShortcut :=
    TransitionIntegratedW11.concreteFourTargetFullSameRestShortcut_blocked

/-! ## Integrated target matrix -/

/-- Generated-point target integration matrix.

The record contains route ledgers only.  It provides target conclusions after
one of the explicit input packages in `requiredInputs` is supplied. -/
structure Matrix where
  requiredInputs : RequiredGeneratedPointInputs
  importedLedgers : ImportedW11Ledgers
  generatedPoint : GeneratedPointRoutes
  broadFacades : BroadW11FacadeRoutes
  blockers : TransitionBlockers

/-- Checked generated-point target integration matrix. -/
def matrix : Matrix where
  requiredInputs := requiredGeneratedPointInputs
  importedLedgers := importedW11Ledgers
  generatedPoint := generatedPointRoutes
  broadFacades := broadW11FacadeRoutes
  blockers := transitionBlockers

/-! ## Public generated-point projections -/

theorem targetFacade_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    ArbitraryNTargetFacade :=
  (matrix.generatedPoint.normalizedPolynomial F).targetFacade C

theorem targetUpperConstructionFiveSixteenAt_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.generatedPoint.normalizedPolynomial F).fixedTarget C n

theorem targetUpperConstructionFiveSixteenArbitrary_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPoint.normalizedPolynomial F).arbitraryTarget C

theorem targetFacade_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) :
    ArbitraryNTargetFacade :=
  (matrix.generatedPoint.normalizedValue F).targetFacade C

theorem targetUpperConstructionFiveSixteenAt_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.generatedPoint.normalizedValue F).fixedTarget C n

theorem targetUpperConstructionFiveSixteenArbitrary_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPoint.normalizedValue F).arbitraryTarget C

theorem targetFacade_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) :
    ArbitraryNTargetFacade :=
  (matrix.generatedPoint.lowerBound F).targetFacade C

theorem targetUpperConstructionFiveSixteenAt_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.generatedPoint.lowerBound F).fixedTarget C n

theorem targetUpperConstructionFiveSixteenArbitrary_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPoint.lowerBound F).arbitraryTarget C

/-! ## Public cross-block and broad-facade projections -/

def toCrossBlockClosureLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    CrossBlockClosureLedger F :=
  (matrix.generatedPoint.crossBlockLedger F).toClosureLedger L

theorem separated_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    CrossBlockInequalityClosureW11.GeneratedGlobalSeparationAt F k hk :=
  (matrix.generatedPoint.crossBlockLedger F).separated L k hk

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.generatedPoint.crossBlockLedger F).exactBlockTarget L k hk

theorem targetFacade_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.generatedPoint.crossBlockLedger F).route.targetFacade L

theorem targetUpperConstructionFiveSixteenArbitrary_viaClosure_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
  (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.broadFacades.integratedCrossBlockClosure F).arbitraryTarget
    (toCrossBlockClosureLedger L)

theorem targetUpperConstructionFiveSixteenArbitrary_split_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPoint.crossBlockLedger F).arbitraryTargetSplit L

theorem targetFacade_viaArbitraryNClosure_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    ArbitraryNTargetFacade :=
  (matrix.broadFacades.arbitraryNNormalizedPolynomial F).targetFacade C

theorem targetFacade_viaArbitraryNClosure_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) :
    ArbitraryNTargetFacade :=
  (matrix.broadFacades.arbitraryNNormalizedValue F).targetFacade C

theorem targetFacade_viaArbitraryNClosure_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) :
    ArbitraryNTargetFacade :=
  (matrix.broadFacades.arbitraryNLowerBound F).targetFacade C

/-! ## Final-conditional and transition projections -/

theorem targetFacade_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    ArbitraryNTargetFacade :=
  matrix.generatedPoint.finalConditionalFamily.route.targetFacade F

theorem arbitraryTarget_viaConditionalUpper_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ConditionalUpper.arbitraryTarget_of_equationPeriodSearchCrossBlockFamily F

theorem transition_concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.concreteFourTargetRouteClaim

theorem transition_concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.completedFilteredRoute

end

end GeneratedTargetIntegratedW11
end PachToth
end ErdosProblems1066
