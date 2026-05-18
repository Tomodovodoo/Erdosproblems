import ErdosProblems1066.PachToth.ArbitraryNClosureW11
import ErdosProblems1066.PachToth.FlexibleAssemblyTargetW11
import ErdosProblems1066.PachToth.GeneratedPointCertificateW11
import ErdosProblems1066.PachToth.PachTothW10ClosureMatrix

set_option autoImplicit false

/-!
# W11 arbitrary-`n` target closure matrix

This file is an adapter layer over the checked arbitrary-`n` closure spine,
the W10 Pach--Toth closure matrix, and the W11 target-facing facades that are
present in this workspace.

The matrix below keeps the data hypotheses visible:

* exact target assumptions;
* eventual large-case assumptions;
* finite small-case complements.

It does not introduce a public all-`n` theorem without one of those explicit
input packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNTargetClosureW11

noncomputable section

universe u

abbrev FiniteRemainderPackage :=
  ArbitraryNClosureW11.FiniteRemainderPackage

abbrev ArbitraryNTargetFacade :=
  ArbitraryNClosureW11.ArbitraryNTargetFacade

abbrev ThresholdTargetFacade :=
  ArbitraryNClosureW11.ThresholdTargetFacade

abbrev ExactClosedChainPackage :=
  ArbitraryNClosureW11.ExactClosedChainPackage

abbrev ExactGeneratedClosedChainPackage :=
  ArbitraryNClosureW11.ExactGeneratedClosedChainPackage

abbrev EventualClosedChainPackage :=
  ArbitraryNClosureW11.EventualClosedChainPackage

abbrev EventualGeneratedClosedChainPackage :=
  ArbitraryNClosureW11.EventualGeneratedClosedChainPackage

abbrev W10TargetProjectionRow (alpha : Sort u) :=
  PachTothW10ClosureMatrix.TargetProjectionRow alpha

abbrev W10ExactBlockProjectionRow (alpha : Sort u) :=
  PachTothW10ClosureMatrix.ExactBlockProjectionRow alpha

abbrev W10CheckedRemainderRouteRow (alpha : Sort u) :=
  ArbitraryNBridgeW10.CheckedRemainderRouteRow alpha

abbrev W10ExactTargetPackage :=
  ArbitraryNBridgeW10.ExactTargetPackage

abbrev W10PositiveExactChainPackage :=
  ArbitraryNBridgeW10.PositiveExactChainPackage

abbrev W10ClosedPlacementPackage :=
  ArbitraryNBridgeW10.ClosedPlacementPackage

abbrev FlexibleTargetRoute (alpha : Sort u) :=
  FlexibleAssemblyTargetW11.ThresholdSmallCaseRoute alpha

abbrev FlexibleCandidateFields :=
  FlexibleAssemblyTargetW11.CandidateFields

abbrev FlexibleFinalConditionalFamily :=
  FlexibleAssemblyTargetW11.FinalConditionalFamily

abbrev GeneratedPointPeriodSearchFamily :=
  GeneratedPointCertificateW11.RoleHingedPeriodSearchFamily

abbrev GeneratedPointNormalizedPolynomialFields
    (F : GeneratedPointPeriodSearchFamily) :=
  GeneratedPointCertificateW11.NormalizedPolynomialFields F

abbrev GeneratedPointNormalizedValueFields
    (F : GeneratedPointPeriodSearchFamily) :=
  GeneratedPointCertificateW11.NormalizedValueFields F

abbrev GeneratedPointLowerBoundFields
    (F : GeneratedPointPeriodSearchFamily) :=
  GeneratedPointCertificateW11.LowerBoundFields F

/-! ## Explicit target assumptions -/

/-- An exact block-form Pach--Toth target assumption. -/
structure ExactTargetAssumptions where
  exactTarget : PachToth.targetUpperConstructionFiveSixteen

/-- An eventual large-case target assumption with its threshold exposed. -/
structure EventualTargetAssumptions where
  vertexThreshold : Nat
  largeTarget :
    forall n : Nat, vertexThreshold <= n ->
      PachToth.targetUpperConstructionFiveSixteenAt n

/-- A finite small-case complement below a named threshold. -/
structure SmallCaseAssumptions (vertexThreshold : Nat) where
  smallTarget :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo vertexThreshold

/-- The exact input needed to close an eventual route. -/
structure EventualSmallCaseAssumptions where
  eventual : EventualTargetAssumptions
  small : SmallCaseAssumptions eventual.vertexThreshold

namespace ExactTargetAssumptions

/-- The checked arbitrary-`n` facade obtained from an exact target. -/
def targetFacade (A : ExactTargetAssumptions) :
    ArbitraryNTargetFacade :=
  ArbitraryNClosureW11.targetFacadeOfW10ExactTargetPackage
    { exactTarget := A.exactTarget }

/-- Fixed-`n` projection from the checked exact/remainder split. -/
theorem fixedTarget (A : ExactTargetAssumptions) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  A.targetFacade.fixedTarget n

/-- Arbitrary-`n` projection from the checked exact/remainder split. -/
theorem arbitraryTarget (A : ExactTargetAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  A.targetFacade.arbitraryTarget

end ExactTargetAssumptions

namespace EventualSmallCaseAssumptions

/-- The threshold facade assembled from explicit large and small sides. -/
def thresholdFacade (A : EventualSmallCaseAssumptions) :
    ThresholdTargetFacade where
  vertexThreshold := A.eventual.vertexThreshold
  largeTarget := A.eventual.largeTarget
  smallTarget := A.small.smallTarget
  arbitraryTarget :=
    PachToth.targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      A.eventual.vertexThreshold
      A.eventual.largeTarget
      A.small.smallTarget

/-- The arbitrary-`n` facade obtained after closing the threshold split. -/
def targetFacade (A : EventualSmallCaseAssumptions) :
    ArbitraryNTargetFacade :=
  ArbitraryNClosureW11.ThresholdTargetFacade.toArbitraryNTargetFacade
    A.thresholdFacade

/-- The closed arbitrary target from the explicit threshold split. -/
theorem arbitraryTarget (A : EventualSmallCaseAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  A.thresholdFacade.arbitraryTarget

/-- Fixed-`n` target after closing the threshold split. -/
theorem fixedTarget (A : EventualSmallCaseAssumptions) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  A.arbitraryTarget n

end EventualSmallCaseAssumptions

/-! ## Facade adapters -/

/-- Use a checked exact target for fixed counts while keeping an already
assembled arbitrary target as the facade's arbitrary projection. -/
def targetFacadeOfExactTargetAndArbitrary
    (Hexact : PachToth.targetUpperConstructionFiveSixteen)
    (Harbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    ArbitraryNTargetFacade where
  fixedTarget :=
    (ExactTargetAssumptions.targetFacade { exactTarget := Hexact }).fixedTarget
  arbitraryTarget := Harbitrary

/-- Exact target data as a target facade. -/
def targetFacadeOfExactTarget
    (Hexact : PachToth.targetUpperConstructionFiveSixteen) :
    ArbitraryNTargetFacade :=
  ExactTargetAssumptions.targetFacade { exactTarget := Hexact }

/-- Convert a W10 target row to the W11 arbitrary-`n` facade shape. -/
def targetFacadeOfW10TargetProjectionRow
    {alpha : Sort u} (R : W10TargetProjectionRow alpha) (a : alpha) :
    ArbitraryNTargetFacade :=
  targetFacadeOfExactTargetAndArbitrary
    (R.exactTarget a)
    (R.arbitraryTarget a)

/-- Convert a W10 exact-block row to the W11 arbitrary-`n` facade shape. -/
def targetFacadeOfW10ExactBlockProjectionRow
    {alpha : Sort u} (R : W10ExactBlockProjectionRow alpha) (a : alpha) :
    ArbitraryNTargetFacade :=
  targetFacadeOfExactTargetAndArbitrary
    (R.exactTarget a)
    (R.arbitraryTarget a)

/-- Convert a W10 checked-remainder row to the W11 facade shape. -/
def targetFacadeOfW10CheckedRemainderRouteRow
    {alpha : Sort u} (R : W10CheckedRemainderRouteRow alpha) (a : alpha) :
    ArbitraryNTargetFacade where
  fixedTarget := R.fixedTarget a
  arbitraryTarget := R.arbitraryTarget a

/-- Convert a W11 flexible threshold route to the shared threshold facade. -/
def thresholdFacadeOfFlexibleTargetRoute
    {alpha : Sort u} (R : FlexibleTargetRoute alpha) (a : alpha) :
    ThresholdTargetFacade where
  vertexThreshold := R.threshold a
  largeTarget := R.largeTarget a
  smallTarget := R.smallCases a
  arbitraryTarget := R.arbitraryTarget a

/-- Convert a W11 flexible threshold route to the shared arbitrary facade. -/
def targetFacadeOfFlexibleTargetRoute
    {alpha : Sort u} (R : FlexibleTargetRoute alpha) (a : alpha) :
    ArbitraryNTargetFacade where
  fixedTarget := R.fixedTarget a
  arbitraryTarget := R.arbitraryTarget a

/-- Convert a W11 flexible threshold route to explicit eventual/small-case
assumptions. -/
def eventualSmallCaseAssumptionsOfFlexibleTargetRoute
    {alpha : Sort u} (R : FlexibleTargetRoute alpha) (a : alpha) :
    EventualSmallCaseAssumptions where
  eventual :=
    { vertexThreshold := R.threshold a
      largeTarget := R.largeTarget a }
  small := { smallTarget := R.smallCases a }

/-! ## Row shapes -/

/-- A target row closed from exact data. -/
structure ExactTargetClosureRow (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

/-- A target row closed from explicit eventual and small-case data. -/
structure EventualSmallCaseClosureRow (alpha : Sort u) where
  vertexThreshold : alpha -> Nat
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  largeTarget :
    forall a : alpha, forall n : Nat, vertexThreshold a <= n ->
      PachToth.targetUpperConstructionFiveSixteenAt n
  smallTarget :
    forall a : alpha,
      PachToth.targetUpperConstructionFiveSixteenSmallUpTo
        (vertexThreshold a)
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  thresholdFacade : alpha -> ThresholdTargetFacade
  targetFacade : alpha -> ArbitraryNTargetFacade

/-! ## Generic rows -/

/-- Exact assumptions as a checked closure row. -/
def exactAssumptionsRow :
    ExactTargetClosureRow ExactTargetAssumptions where
  exactTarget := ExactTargetAssumptions.exactTarget
  fixedTarget := fun A n => A.fixedTarget n
  arbitraryTarget := ExactTargetAssumptions.arbitraryTarget
  targetFacade := ExactTargetAssumptions.targetFacade

/-- Eventual plus small-case assumptions as a checked closure row. -/
def eventualSmallCaseAssumptionsRow :
    EventualSmallCaseClosureRow EventualSmallCaseAssumptions where
  vertexThreshold := fun A => A.eventual.vertexThreshold
  fixedTarget := fun A n => A.fixedTarget n
  largeTarget := fun A => A.eventual.largeTarget
  smallTarget := fun A => A.small.smallTarget
  arbitraryTarget := EventualSmallCaseAssumptions.arbitraryTarget
  thresholdFacade := EventualSmallCaseAssumptions.thresholdFacade
  targetFacade := EventualSmallCaseAssumptions.targetFacade

/-- Build an exact closure row directly from exact-target facades. -/
def exactTargetClosureRowOfFacade
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (facade : alpha -> ArbitraryNTargetFacade) :
    ExactTargetClosureRow alpha where
  exactTarget := exactTarget
  fixedTarget := fun a => (facade a).fixedTarget
  arbitraryTarget := fun a => (facade a).arbitraryTarget
  targetFacade := facade

/-- Build an exact closure row directly from exact target data. -/
def exactTargetClosureRowOfExactTarget
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen) :
    ExactTargetClosureRow alpha :=
  exactTargetClosureRowOfFacade
    exactTarget
    (fun a => targetFacadeOfExactTarget (exactTarget a))

/-- Build an exact closure row from a W10 target projection row. -/
def exactTargetClosureRowOfW10TargetProjectionRow
    {alpha : Sort u} (R : W10TargetProjectionRow alpha) :
    ExactTargetClosureRow alpha :=
  exactTargetClosureRowOfFacade
    R.exactTarget
    (targetFacadeOfW10TargetProjectionRow R)

/-- Build an exact closure row from a W10 exact-block projection row. -/
def exactTargetClosureRowOfW10ExactBlockProjectionRow
    {alpha : Sort u} (R : W10ExactBlockProjectionRow alpha) :
    ExactTargetClosureRow alpha :=
  exactTargetClosureRowOfFacade
    R.exactTarget
    (targetFacadeOfW10ExactBlockProjectionRow R)

/-- Build an exact closure row from a W10 checked-remainder route row. -/
def exactTargetClosureRowOfW10CheckedRemainderRouteRow
    {alpha : Sort u} (R : W10CheckedRemainderRouteRow alpha) :
    ExactTargetClosureRow alpha :=
  exactTargetClosureRowOfFacade
    R.exactTarget
    (targetFacadeOfW10CheckedRemainderRouteRow R)

/-- Build an eventual/small-case row from a W11 flexible threshold route. -/
def eventualSmallCaseClosureRowOfFlexibleTargetRoute
    {alpha : Sort u} (R : FlexibleTargetRoute alpha) :
    EventualSmallCaseClosureRow alpha where
  vertexThreshold := R.threshold
  fixedTarget := R.fixedTarget
  largeTarget := R.largeTarget
  smallTarget := R.smallCases
  arbitraryTarget := R.arbitraryTarget
  thresholdFacade := thresholdFacadeOfFlexibleTargetRoute R
  targetFacade := targetFacadeOfFlexibleTargetRoute R

/-! ## Arbitrary-`n` closure spine rows -/

/-- Exact closed chains plus explicit finite remainders. -/
def exactClosedChainPackageRow
    (R : FiniteRemainderPackage) :
    ExactTargetClosureRow ExactClosedChainPackage where
  exactTarget := fun P => P.targetUpperConstructionFiveSixteen
  fixedTarget := fun P n => P.fixedTarget R n
  arbitraryTarget := fun P => P.arbitraryTarget R
  targetFacade := fun P => P.targetFacade R

/-- Exact generated closed chains plus explicit finite remainders. -/
def exactGeneratedClosedChainPackageRow
    (R : FiniteRemainderPackage) :
    ExactTargetClosureRow ExactGeneratedClosedChainPackage where
  exactTarget := fun P =>
    P.toExactClosedChainPackage.targetUpperConstructionFiveSixteen
  fixedTarget := fun P n => (P.targetFacade R).fixedTarget n
  arbitraryTarget := fun P => (P.targetFacade R).arbitraryTarget
  targetFacade := fun P => P.targetFacade R

/-- Eventual closed chains plus their finite small-case complement. -/
def eventualClosedChainPackageRow
    (R : FiniteRemainderPackage) :
    EventualSmallCaseClosureRow EventualClosedChainPackage where
  vertexThreshold := fun P => 16 * P.threshold
  fixedTarget := fun P n => (P.targetFacade R).fixedTarget n
  largeTarget := fun P n hn => P.largeTarget R n hn
  smallTarget := fun P => P.smallCases
  arbitraryTarget := fun P => P.arbitraryTarget R
  thresholdFacade := fun P => P.thresholdFacade R
  targetFacade := fun P => P.targetFacade R

/-- Eventual generated closed chains plus their finite small-case complement.
-/
def eventualGeneratedClosedChainPackageRow
    (R : FiniteRemainderPackage) :
    EventualSmallCaseClosureRow EventualGeneratedClosedChainPackage where
  vertexThreshold := fun P => 16 * P.threshold
  fixedTarget := fun P n => (P.targetFacade R).fixedTarget n
  largeTarget := fun P n hn => (P.thresholdFacade R).largeTarget n hn
  smallTarget := fun P => (P.thresholdFacade R).smallTarget
  arbitraryTarget := fun P => P.arbitraryTarget R
  thresholdFacade := fun P => P.thresholdFacade R
  targetFacade := fun P => P.targetFacade R

/-! ## W10 and W11 facade rows -/

def w10ExactTargetPackageRow :
    ExactTargetClosureRow W10ExactTargetPackage :=
  exactTargetClosureRowOfFacade
    (fun P => P.exactTarget)
    ArbitraryNClosureW11.targetFacadeOfW10ExactTargetPackage

def w10PositiveExactChainPackageRow :
    ExactTargetClosureRow W10PositiveExactChainPackage :=
  exactTargetClosureRowOfFacade
    ArbitraryNBridgeW10.PositiveExactChainPackage.targetUpperConstructionFiveSixteen
    ArbitraryNClosureW11.targetFacadeOfW10PositiveExactChainPackage

def w10ClosedPlacementPackageRow :
    ExactTargetClosureRow W10ClosedPlacementPackage :=
  exactTargetClosureRowOfW10CheckedRemainderRouteRow
    ArbitraryNBridgeW10.matrix.closedPlacements

def flexibleCandidateFieldsRow :
    EventualSmallCaseClosureRow FlexibleCandidateFields :=
  eventualSmallCaseClosureRowOfFlexibleTargetRoute
    FlexibleAssemblyTargetW11.matrix.candidateFields

def flexibleFinalConditionalFamilyRow :
    EventualSmallCaseClosureRow FlexibleFinalConditionalFamily :=
  eventualSmallCaseClosureRowOfFlexibleTargetRoute
    FlexibleAssemblyTargetW11.matrix.finalConditionalFamily

def generatedPointNormalizedPolynomialFieldsRow
    (F : GeneratedPointPeriodSearchFamily) :
    ExactTargetClosureRow (GeneratedPointNormalizedPolynomialFields F) :=
  exactTargetClosureRowOfExactTarget
    (fun C =>
      GeneratedPointCertificateW11.NormalizedPolynomialFields.targetUpperConstructionFiveSixteen
        C)

def generatedPointNormalizedValueFieldsRow
    (F : GeneratedPointPeriodSearchFamily) :
    ExactTargetClosureRow (GeneratedPointNormalizedValueFields F) :=
  exactTargetClosureRowOfExactTarget
    (fun C =>
      GeneratedPointCertificateW11.NormalizedValueFields.targetUpperConstructionFiveSixteen
        C)

def generatedPointLowerBoundFieldsRow
    (F : GeneratedPointPeriodSearchFamily) :
    ExactTargetClosureRow (GeneratedPointLowerBoundFields F) :=
  exactTargetClosureRowOfExactTarget
    (fun C =>
      GeneratedPointCertificateW11.LowerBoundFields.targetUpperConstructionFiveSixteen
        C)

/-! ## Matrix -/

/-- The checked W11 arbitrary-`n` target closure matrix. -/
structure Matrix where
  finiteRemainders : FiniteRemainderPackage
  w10ClosureMatrix : PachTothW10ClosureMatrix.Matrix
  w10ArbitraryBridge : ArbitraryNBridgeW10.Matrix
  flexibleTargetMatrix : FlexibleAssemblyTargetW11.Matrix
  exactAssumptions : ExactTargetClosureRow ExactTargetAssumptions
  eventualSmallCaseAssumptions :
    EventualSmallCaseClosureRow EventualSmallCaseAssumptions
  exactClosedChains : ExactTargetClosureRow ExactClosedChainPackage
  exactGeneratedClosedChains :
    ExactTargetClosureRow ExactGeneratedClosedChainPackage
  eventualClosedChains :
    EventualSmallCaseClosureRow EventualClosedChainPackage
  eventualGeneratedClosedChains :
    EventualSmallCaseClosureRow EventualGeneratedClosedChainPackage
  w10ExactTargets : ExactTargetClosureRow W10ExactTargetPackage
  w10PositiveExactChains :
    ExactTargetClosureRow W10PositiveExactChainPackage
  w10ClosedPlacements : ExactTargetClosureRow W10ClosedPlacementPackage
  w10MinimalExactTarget :
    ExactTargetClosureRow PachTothW10ClosureMatrix.W8MinimalExactTargetCertificate
  w10ConcreteRemainingData :
    ExactTargetClosureRow PachTothW10ClosureMatrix.W8ConcreteRemainingData
  w10ConcreteLowerTables :
    ExactTargetClosureRow PachTothW10ClosureMatrix.W8ConcreteNonConnectorLowerTableFamily
  w10ClosingFields :
    ExactTargetClosureRow PachTothW10ClosureMatrix.W9ClosingFields
  w10PeriodSearchSqValues :
    ExactTargetClosureRow PachTothW10ClosureMatrix.W9PeriodSearchSqValuePackage
  w10FinalFlexibleLowerTables :
    ExactTargetClosureRow PachTothW10ClosureMatrix.FinalFlexibleLowerTableFamily
  w10FinalFlexibleValueMatrices :
    ExactTargetClosureRow PachTothW10ClosureMatrix.FinalFlexibleValueMatrixFamily
  w10ConcreteValueMatrices :
    ExactTargetClosureRow PachTothW10ClosureMatrix.ConcreteValueMatrixFamily
  w10CandidateValueMatrices :
    ExactTargetClosureRow PachTothW10ClosureMatrix.CandidateValueMatrixFamily
  w10PackedCrossBlockInequalities :
    ExactTargetClosureRow PachTothW10ClosureMatrix.W10CandidatePackedInequalities
  flexibleCandidateFields :
    EventualSmallCaseClosureRow FlexibleCandidateFields
  flexibleFinalConditionalFamily :
    EventualSmallCaseClosureRow FlexibleFinalConditionalFamily
  generatedPointNormalizedPolynomialFields :
    forall F : GeneratedPointPeriodSearchFamily,
      ExactTargetClosureRow (GeneratedPointNormalizedPolynomialFields F)
  generatedPointNormalizedValueFields :
    forall F : GeneratedPointPeriodSearchFamily,
      ExactTargetClosureRow (GeneratedPointNormalizedValueFields F)
  generatedPointLowerBoundFields :
    forall F : GeneratedPointPeriodSearchFamily,
      ExactTargetClosureRow (GeneratedPointLowerBoundFields F)

/-- The checked W11 arbitrary-`n` target closure matrix. -/
def matrix : Matrix where
  finiteRemainders := ArbitraryNClosureW11.checkedFiniteRemainders
  w10ClosureMatrix := PachTothW10ClosureMatrix.matrix
  w10ArbitraryBridge := ArbitraryNBridgeW10.matrix
  flexibleTargetMatrix := FlexibleAssemblyTargetW11.matrix
  exactAssumptions := exactAssumptionsRow
  eventualSmallCaseAssumptions := eventualSmallCaseAssumptionsRow
  exactClosedChains :=
    exactClosedChainPackageRow ArbitraryNClosureW11.checkedFiniteRemainders
  exactGeneratedClosedChains :=
    exactGeneratedClosedChainPackageRow
      ArbitraryNClosureW11.checkedFiniteRemainders
  eventualClosedChains :=
    eventualClosedChainPackageRow ArbitraryNClosureW11.checkedFiniteRemainders
  eventualGeneratedClosedChains :=
    eventualGeneratedClosedChainPackageRow
      ArbitraryNClosureW11.checkedFiniteRemainders
  w10ExactTargets := w10ExactTargetPackageRow
  w10PositiveExactChains := w10PositiveExactChainPackageRow
  w10ClosedPlacements := w10ClosedPlacementPackageRow
  w10MinimalExactTarget :=
    exactTargetClosureRowOfW10TargetProjectionRow
      PachTothW10ClosureMatrix.matrix.w8MinimalCertificate
  w10ConcreteRemainingData :=
    exactTargetClosureRowOfW10TargetProjectionRow
      PachTothW10ClosureMatrix.matrix.w8ConcreteRemainingData
  w10ConcreteLowerTables :=
    exactTargetClosureRowOfW10TargetProjectionRow
      PachTothW10ClosureMatrix.matrix.w8ConcreteLowerTables
  w10ClosingFields :=
    exactTargetClosureRowOfW10ExactBlockProjectionRow
      PachTothW10ClosureMatrix.matrix.w9FlattenedClosingFields
  w10PeriodSearchSqValues :=
    exactTargetClosureRowOfW10ExactBlockProjectionRow
      PachTothW10ClosureMatrix.matrix.w9PeriodSearchSqValues
  w10FinalFlexibleLowerTables :=
    exactTargetClosureRowOfW10TargetProjectionRow
      PachTothW10ClosureMatrix.matrix.finalFlexibleLowerTables
  w10FinalFlexibleValueMatrices :=
    exactTargetClosureRowOfW10TargetProjectionRow
      PachTothW10ClosureMatrix.matrix.finalFlexibleValueMatrices
  w10ConcreteValueMatrices :=
    exactTargetClosureRowOfW10ExactBlockProjectionRow
      PachTothW10ClosureMatrix.matrix.concreteValueMatrices
  w10CandidateValueMatrices :=
    exactTargetClosureRowOfW10TargetProjectionRow
      PachTothW10ClosureMatrix.matrix.candidateValueMatrices
  w10PackedCrossBlockInequalities :=
    exactTargetClosureRowOfW10TargetProjectionRow
      PachTothW10ClosureMatrix.matrix.w10PackedCrossBlockInequalities
  flexibleCandidateFields := flexibleCandidateFieldsRow
  flexibleFinalConditionalFamily := flexibleFinalConditionalFamilyRow
  generatedPointNormalizedPolynomialFields :=
    generatedPointNormalizedPolynomialFieldsRow
  generatedPointNormalizedValueFields := generatedPointNormalizedValueFieldsRow
  generatedPointLowerBoundFields := generatedPointLowerBoundFieldsRow

/-! ## Public projections -/

theorem targetFacade_of_exactAssumptions
    (A : ExactTargetAssumptions) :
    ArbitraryNTargetFacade :=
  matrix.exactAssumptions.targetFacade A

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactAssumptions
    (A : ExactTargetAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactAssumptions.arbitraryTarget A

def thresholdFacade_of_eventualSmallCaseAssumptions
    (A : EventualSmallCaseAssumptions) :
    ThresholdTargetFacade :=
  matrix.eventualSmallCaseAssumptions.thresholdFacade A

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualSmallCaseAssumptions
    (A : EventualSmallCaseAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualSmallCaseAssumptions.arbitraryTarget A

theorem targetFacade_of_exactClosedChains
    (P : ExactClosedChainPackage) :
    ArbitraryNTargetFacade :=
  matrix.exactClosedChains.targetFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactClosedChains
    (P : ExactClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactClosedChains.arbitraryTarget P

def thresholdFacade_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    ThresholdTargetFacade :=
  matrix.eventualClosedChains.thresholdFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualClosedChains.arbitraryTarget P

def thresholdFacade_of_flexibleCandidateFields
    (F : FlexibleCandidateFields) :
    ThresholdTargetFacade :=
  matrix.flexibleCandidateFields.thresholdFacade F

theorem targetFacade_of_flexibleCandidateFields
    (F : FlexibleCandidateFields) :
    ArbitraryNTargetFacade :=
  matrix.flexibleCandidateFields.targetFacade F

theorem targetUpperConstructionFiveSixteenArbitrary_of_flexibleCandidateFields
    (F : FlexibleCandidateFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flexibleCandidateFields.arbitraryTarget F

def thresholdFacade_of_flexibleFinalConditionalFamily
    (F : FlexibleFinalConditionalFamily) :
    ThresholdTargetFacade :=
  matrix.flexibleFinalConditionalFamily.thresholdFacade F

theorem targetUpperConstructionFiveSixteenArbitrary_of_flexibleFinalConditionalFamily
    (F : FlexibleFinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flexibleFinalConditionalFamily.arbitraryTarget F

theorem targetFacade_of_w10PackedCrossBlockInequalities
    (C : PachTothW10ClosureMatrix.W10CandidatePackedInequalities) :
    ArbitraryNTargetFacade :=
  matrix.w10PackedCrossBlockInequalities.targetFacade C

theorem targetUpperConstructionFiveSixteenArbitrary_of_w10PackedCrossBlockInequalities
    (C : PachTothW10ClosureMatrix.W10CandidatePackedInequalities) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w10PackedCrossBlockInequalities.arbitraryTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPointNormalizedPolynomialFields
    {F : GeneratedPointPeriodSearchFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointNormalizedPolynomialFields F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPointNormalizedValueFields
    {F : GeneratedPointPeriodSearchFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointNormalizedValueFields F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPointLowerBoundFields
    {F : GeneratedPointPeriodSearchFamily}
    (C : GeneratedPointLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointLowerBoundFields F).arbitraryTarget C

end

end ArbitraryNTargetClosureW11
end PachToth
end ErdosProblems1066
