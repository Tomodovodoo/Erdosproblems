import ErdosProblems1066.PachToth.ArbitraryNClosureW11
import ErdosProblems1066.PachToth.ArbitraryNTargetClosureW11
import ErdosProblems1066.PachToth.SmallLengthClosureW11
import ErdosProblems1066.PachToth.GeneratedPointClosureW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11

set_option autoImplicit false

/-!
# W11 integrated arbitrary-`n` Pach--Toth matrix

This module gathers the W11 arbitrary-`n` target routes that are present in
the tree.  It keeps each source package as an input: exact block targets,
eventual large-chain data, finite small cases, generated-point fields, and
cross-block inequality ledgers all remain visible in the row types below.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNIntegratedW11

noncomputable section

universe u

abbrev FiniteRemainderPackage :=
  ArbitraryNClosureW11.FiniteRemainderPackage

abbrev ArbitraryNTargetFacade :=
  ArbitraryNClosureW11.ArbitraryNTargetFacade

abbrev ThresholdTargetFacade :=
  ArbitraryNClosureW11.ThresholdTargetFacade

abbrev ExactTargetAssumptions :=
  ArbitraryNTargetClosureW11.ExactTargetAssumptions

abbrev EventualSmallCaseAssumptions :=
  ArbitraryNTargetClosureW11.EventualSmallCaseAssumptions

abbrev ExactClosedChainPackage :=
  ArbitraryNClosureW11.ExactClosedChainPackage

abbrev ExactGeneratedClosedChainPackage :=
  ArbitraryNClosureW11.ExactGeneratedClosedChainPackage

abbrev EventualClosedChainPackage :=
  ArbitraryNClosureW11.EventualClosedChainPackage

abbrev EventualGeneratedClosedChainPackage :=
  ArbitraryNClosureW11.EventualGeneratedClosedChainPackage

abbrev SmallLengthPeriodSearchFamily :=
  SmallLengthClosureW11.RoleHingedPeriodSearchFamily

abbrev SmallLengthExactBlockTargets :=
  SmallLengthClosureW11.SmallLengthExactBlockTargets

abbrev SmallLengthClosureObligations
    (F : SmallLengthPeriodSearchFamily) :=
  SmallLengthClosureW11.SmallLengthClosureObligations F

abbrev SmallLengthEventualClosedChains :=
  SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix

abbrev SmallLengthEventualGeneratedClosedChains :=
  SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix

abbrev GeneratedPointPeriodSearchFamily :=
  GeneratedPointClosureW11.RoleHingedPeriodSearchFamily

abbrev GeneratedPointNormalizedPolynomialFields
    (F : GeneratedPointPeriodSearchFamily) :=
  GeneratedPointClosureW11.NormalizedPolynomialFields F

abbrev GeneratedPointNormalizedValueFields
    (F : GeneratedPointPeriodSearchFamily) :=
  GeneratedPointClosureW11.NormalizedValueFields F

abbrev GeneratedPointLowerBoundFields
    (F : GeneratedPointPeriodSearchFamily) :=
  GeneratedPointClosureW11.LowerBoundFields F

abbrev GeneratedPointFlexibleCandidateAssemblyFields :=
  GeneratedPointClosureW11.FlexibleCandidateAssemblyFields

abbrev CrossBlockPeriodSearchFamily :=
  CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily

abbrev CrossBlockInequalityLedger
    (F : CrossBlockPeriodSearchFamily) :=
  CrossBlockInequalityClosureW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger
    (F : CrossBlockPeriodSearchFamily) :=
  CrossBlockInequalityClosureW11.CrossBlockClosureLedger F

abbrev CrossBlockFlexibleRouteFields :=
  CrossBlockInequalityClosureW11.FlexibleNonRigidRouteFields

/-! ## Shared row records -/

/-- Build a target facade from fixed and arbitrary projections. -/
def targetFacadeOfFixedAndArbitrary
    (fixedTarget :
      forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n)
    (arbitraryTarget :
      PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    ArbitraryNTargetFacade where
  fixedTarget := fixedTarget
  arbitraryTarget := arbitraryTarget

/-- The eventual target supplied by an arbitrary-`n` target, with threshold
zero. -/
theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

/-- Exact block-form data routed to fixed, eventual, arbitrary, and facade
targets. -/
structure ExactBlockFacadeRow (alpha : Sort u) where
  blockTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

/-- Eventual plus finite-small-case data routed to threshold and arbitrary
facades. -/
structure ThresholdFacadeRow (alpha : Sort u) where
  vertexThreshold : alpha -> Nat
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

/-- Exact chain data for all positive block counts, with the finite remainder
package still shown in the row. -/
structure ExactClosedChainFacadeRow (alpha : Sort u) where
  finiteRemainders : FiniteRemainderPackage
  chain :
    alpha -> forall k : Nat, 0 < k -> SplitSoundness.ExactChainUpper k
  blockTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

/-- Generated exact chain data for all positive block counts, together with
the exact-chain projection used by the arbitrary-`n` facade. -/
structure ExactGeneratedClosedChainFacadeRow (alpha : Sort u) where
  finiteRemainders : FiniteRemainderPackage
  generatedData :
    alpha -> forall (k : Nat) (hk : 0 < k),
      SplitRealizationClosure.ExactGeneratedClosedChainData k hk
  chain :
    alpha -> forall k : Nat, 0 < k -> SplitSoundness.ExactChainUpper k
  blockTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

/-- Eventual exact chains, finite small cases, and target facades with both
block and vertex thresholds visible. -/
structure EventualClosedChainFacadeRow (alpha : Sort u) where
  finiteRemainders : FiniteRemainderPackage
  blockThreshold : alpha -> Nat
  vertexThreshold : alpha -> Nat
  largeChain :
    forall a : alpha, forall k : Nat, blockThreshold a <= k ->
      0 < k -> SplitSoundness.ExactChainUpper k
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

/-- Eventual generated chains, their exact-chain projection, finite small
cases, and target facades. -/
structure EventualGeneratedClosedChainFacadeRow (alpha : Sort u) where
  finiteRemainders : FiniteRemainderPackage
  blockThreshold : alpha -> Nat
  vertexThreshold : alpha -> Nat
  largeData :
    forall a : alpha, forall k : Nat, blockThreshold a <= k ->
      forall hk : 0 < k,
        SplitRealizationClosure.ExactGeneratedClosedChainData k hk
  largeChain :
    forall a : alpha, forall k : Nat, blockThreshold a <= k ->
      0 < k -> SplitSoundness.ExactChainUpper k
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

/-- A small-length package gives the finite complement below block threshold
six and becomes a full facade only after a matching large-target input is
supplied. -/
structure SmallLengthFacadeBuilder (alpha : Sort u) where
  exactBlocks : alpha -> SmallLengthExactBlockTargets
  smallTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenSmallUpTo (16 * 6)
  thresholdFacadeOfLarge :
    alpha ->
      (forall n : Nat, 16 * 6 <= n ->
        PachToth.targetUpperConstructionFiveSixteenAt n) ->
      ThresholdTargetFacade
  targetFacadeOfLarge :
    alpha ->
      (forall n : Nat, 16 * 6 <= n ->
        PachToth.targetUpperConstructionFiveSixteenAt n) ->
      ArbitraryNTargetFacade
  arbitraryTargetOfLarge :
    alpha ->
      (forall n : Nat, 16 * 6 <= n ->
        PachToth.targetUpperConstructionFiveSixteenAt n) ->
      PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- Cross-block closure ledgers expose separation, exact block targets, and
the checked arbitrary-`n` facade. -/
structure CrossBlockFacadeRow (F : CrossBlockPeriodSearchFamily) where
  separated :
    CrossBlockClosureLedger F -> forall k : Nat, forall hk : 0 < k,
      CrossBlockInequalityClosureW11.GeneratedGlobalSeparationAt F k hk
  exactBlockAt :
    CrossBlockClosureLedger F -> forall k : Nat, forall _hk : 0 < k,
      PachToth.targetUpperConstructionFiveSixteenAt (16 * k)
  blockTarget :
    CrossBlockClosureLedger F -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    CrossBlockClosureLedger F -> forall n : Nat,
      PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    CrossBlockClosureLedger F ->
      PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    CrossBlockClosureLedger F ->
      PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : CrossBlockClosureLedger F -> ArbitraryNTargetFacade

/-! ## Generic row builders -/

def exactBlockFacadeRowOfTargets
    {alpha : Sort u}
    (blockTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (fixedTarget :
      alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    ExactBlockFacadeRow alpha where
  blockTarget := blockTarget
  fixedTarget := fixedTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (arbitraryTarget a)
  arbitraryTarget := arbitraryTarget
  targetFacade := fun a =>
    targetFacadeOfFixedAndArbitrary (fixedTarget a) (arbitraryTarget a)

def exactBlockFacadeRowOfTargetClosureRow
    {alpha : Sort u}
    (R : ArbitraryNTargetClosureW11.ExactTargetClosureRow alpha) :
    ExactBlockFacadeRow alpha where
  blockTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (R.arbitraryTarget a)
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

def thresholdFacadeRowOfTargetClosureRow
    {alpha : Sort u}
    (R : ArbitraryNTargetClosureW11.EventualSmallCaseClosureRow alpha) :
    ThresholdFacadeRow alpha where
  vertexThreshold := R.vertexThreshold
  largeTarget := R.largeTarget
  smallTarget := R.smallTarget
  arbitraryTarget := R.arbitraryTarget
  thresholdFacade := R.thresholdFacade
  targetFacade := R.targetFacade

def exactBlockFacadeRowOfGeneratedPointRow
    {alpha : Sort u}
    (R : GeneratedPointClosureW11.GeneratedPointTargetRow alpha) :
    ExactBlockFacadeRow alpha where
  blockTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := fun a =>
    targetFacadeOfFixedAndArbitrary (R.fixedTarget a) (R.arbitraryTarget a)

/-! ## Exact and eventual arbitrary-`n` rows -/

def exactTargetAssumptionsRow :
    ExactBlockFacadeRow ExactTargetAssumptions :=
  exactBlockFacadeRowOfTargetClosureRow
    ArbitraryNTargetClosureW11.exactAssumptionsRow

def eventualSmallCaseAssumptionsRow :
    ThresholdFacadeRow EventualSmallCaseAssumptions :=
  thresholdFacadeRowOfTargetClosureRow
    ArbitraryNTargetClosureW11.eventualSmallCaseAssumptionsRow

def exactClosedChainFacadeRow
    (R : FiniteRemainderPackage) :
    ExactClosedChainFacadeRow ExactClosedChainPackage where
  finiteRemainders := R
  chain := fun P => P.chain
  blockTarget := fun P => P.targetUpperConstructionFiveSixteen
  fixedTarget := fun P n => P.fixedTarget R n
  eventualTarget := fun P => eventualTargetOfArbitrary (P.arbitraryTarget R)
  arbitraryTarget := fun P => P.arbitraryTarget R
  targetFacade := fun P => P.targetFacade R

def exactGeneratedClosedChainFacadeRow
    (R : FiniteRemainderPackage) :
    ExactGeneratedClosedChainFacadeRow ExactGeneratedClosedChainPackage where
  finiteRemainders := R
  generatedData := fun P => P.data
  chain := fun P => P.toExactClosedChainPackage.chain
  blockTarget := fun P =>
    P.toExactClosedChainPackage.targetUpperConstructionFiveSixteen
  fixedTarget := fun P n => (P.targetFacade R).fixedTarget n
  eventualTarget := fun P =>
    eventualTargetOfArbitrary (P.targetFacade R).arbitraryTarget
  arbitraryTarget := fun P => (P.targetFacade R).arbitraryTarget
  targetFacade := fun P => P.targetFacade R

def eventualClosedChainFacadeRow
    (R : FiniteRemainderPackage) :
    EventualClosedChainFacadeRow EventualClosedChainPackage where
  finiteRemainders := R
  blockThreshold := fun P => P.threshold
  vertexThreshold := fun P => 16 * P.threshold
  largeChain := fun P k hK hk => P.largeChain k hK hk
  largeTarget := fun P n hn => P.largeTarget R n hn
  smallTarget := fun P => P.smallCases
  arbitraryTarget := fun P => P.arbitraryTarget R
  thresholdFacade := fun P => P.thresholdFacade R
  targetFacade := fun P => P.targetFacade R

def eventualGeneratedClosedChainFacadeRow
    (R : FiniteRemainderPackage) :
    EventualGeneratedClosedChainFacadeRow EventualGeneratedClosedChainPackage where
  finiteRemainders := R
  blockThreshold := fun P => P.threshold
  vertexThreshold := fun P => 16 * P.threshold
  largeData := fun P k hK hk => P.largeData k hK hk
  largeChain := fun P k hK hk =>
    P.toEventualClosedChainPackage.largeChain k hK hk
  largeTarget := fun P n hn => (P.thresholdFacade R).largeTarget n hn
  smallTarget := fun P => (P.thresholdFacade R).smallTarget
  arbitraryTarget := fun P => P.arbitraryTarget R
  thresholdFacade := fun P => P.thresholdFacade R
  targetFacade := fun P => P.targetFacade R

/-! ## Small-length rows -/

def smallLengthExactBlockBuilder :
    SmallLengthFacadeBuilder SmallLengthExactBlockTargets where
  exactBlocks := fun C => C
  smallTarget := fun C => C.smallUpToSix
  thresholdFacadeOfLarge := fun C Hlarge =>
    C.thresholdFacadeOfEventualLarge Hlarge
  targetFacadeOfLarge := fun C Hlarge =>
    C.targetFacadeOfEventualLarge Hlarge
  arbitraryTargetOfLarge := fun C Hlarge =>
    C.arbitraryTargetOfEventualLarge Hlarge

def smallLengthClosureObligationsBuilder
    (F : SmallLengthPeriodSearchFamily) :
    SmallLengthFacadeBuilder (SmallLengthClosureObligations F) where
  exactBlocks := fun O => O.exactBlocks
  smallTarget := fun O => O.smallUpToSix
  thresholdFacadeOfLarge := fun O Hlarge =>
    O.exactBlocks.thresholdFacadeOfEventualLarge Hlarge
  targetFacadeOfLarge := fun O Hlarge =>
    O.exactBlocks.targetFacadeOfEventualLarge Hlarge
  arbitraryTargetOfLarge := fun O Hlarge =>
    O.exactBlocks.arbitraryTargetOfEventualLarge Hlarge

def smallLengthEventualClosedChainRow :
    EventualClosedChainFacadeRow SmallLengthEventualClosedChains where
  finiteRemainders := ArbitraryNClosureW11.checkedFiniteRemainders
  blockThreshold := fun _P => 6
  vertexThreshold := fun _P => 16 * 6
  largeChain := fun P k hK hk => P.largeChain k hK hk
  largeTarget := fun P n hn =>
    (SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.thresholdFacade
      P).largeTarget n hn
  smallTarget := fun P => P.exactBlocks.smallUpToSix
  arbitraryTarget := fun P =>
    SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.arbitraryTarget
      P
  thresholdFacade := fun P =>
    SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.thresholdFacade
      P
  targetFacade := fun P =>
    SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.checkedTargetFacade
      P

def smallLengthEventualGeneratedClosedChainRow :
    EventualGeneratedClosedChainFacadeRow
      SmallLengthEventualGeneratedClosedChains where
  finiteRemainders := ArbitraryNClosureW11.checkedFiniteRemainders
  blockThreshold := fun _P => 6
  vertexThreshold := fun _P => 16 * 6
  largeData := fun P k hK hk => P.largeData k hK hk
  largeChain := fun P k hK hk =>
    P.toEventualGeneratedClosedChainPackage
      |>.toEventualClosedChainPackage
      |>.largeChain k hK hk
  largeTarget := fun P n hn =>
    (SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.thresholdFacade
      P).largeTarget n hn
  smallTarget := fun P => P.exactBlocks.smallUpToSix
  arbitraryTarget := fun P =>
    SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.arbitraryTarget
      P
  thresholdFacade := fun P =>
    SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.thresholdFacade
      P
  targetFacade := fun P =>
    SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.checkedTargetFacade
      P

/-! ## Generated-point rows -/

def generatedPointNormalizedPolynomialFieldsRow
    (F : GeneratedPointPeriodSearchFamily) :
    ExactBlockFacadeRow (GeneratedPointNormalizedPolynomialFields F) :=
  exactBlockFacadeRowOfGeneratedPointRow
    (GeneratedPointClosureW11.matrix.normalizedPolynomial F)

def generatedPointNormalizedValueFieldsRow
    (F : GeneratedPointPeriodSearchFamily) :
    ExactBlockFacadeRow (GeneratedPointNormalizedValueFields F) :=
  exactBlockFacadeRowOfGeneratedPointRow
    (GeneratedPointClosureW11.matrix.normalizedValue F)

def generatedPointLowerBoundFieldsRow
    (F : GeneratedPointPeriodSearchFamily) :
    ExactBlockFacadeRow (GeneratedPointLowerBoundFields F) :=
  exactBlockFacadeRowOfGeneratedPointRow
    (GeneratedPointClosureW11.matrix.lowerBound F)

def generatedPointCrossBlockLedgerRow
    (F : CrossBlockPeriodSearchFamily) :
    ExactBlockFacadeRow (CrossBlockInequalityLedger F) :=
  exactBlockFacadeRowOfGeneratedPointRow
    (GeneratedPointClosureW11.matrix.crossBlockLedger F)

def generatedPointFlexibleCandidateAssemblyRow :
    ExactBlockFacadeRow GeneratedPointFlexibleCandidateAssemblyFields :=
  exactBlockFacadeRowOfGeneratedPointRow
    GeneratedPointClosureW11.matrix.flexibleCandidateAssembly

/-! ## Cross-block rows -/

def crossBlockClosureRow
    (F : CrossBlockPeriodSearchFamily) :
    CrossBlockFacadeRow F where
  separated := fun C k hk => C.generatedGlobalSeparation k hk
  exactBlockAt := fun C k hk =>
    C.targetUpperConstructionFiveSixteenAt_exactBlock k hk
  blockTarget := fun C => C.targetUpperConstructionFiveSixteen
  fixedTarget := fun C n =>
    C.targetUpperConstructionFiveSixteenAt_checkedRemainders n
  eventualTarget := fun C =>
    eventualTargetOfArbitrary
      C.targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
  targetFacade := fun C =>
    targetFacadeOfFixedAndArbitrary
      (fun n => C.targetUpperConstructionFiveSixteenAt_checkedRemainders n)
      C.targetUpperConstructionFiveSixteenArbitrary_checkedRemainders

def crossBlockClosureLedgerOfRaw
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    CrossBlockClosureLedger F where
  inequalityLedger := L

def fixedTargetOfRawCrossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  CrossBlockInequalityClosureW11.CrossBlockClosureLedger.targetUpperConstructionFiveSixteenAt_checkedRemainders
    (crossBlockClosureLedgerOfRaw L) n

theorem arbitraryTargetOfRawCrossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  CrossBlockInequalityClosureW11.CrossBlockClosureLedger.targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
    (crossBlockClosureLedgerOfRaw L)

def rawCrossBlockInequalityLedgerRow
    (F : CrossBlockPeriodSearchFamily) :
    ExactBlockFacadeRow (CrossBlockInequalityLedger F) where
  blockTarget := fun L =>
    (crossBlockClosureLedgerOfRaw L).targetUpperConstructionFiveSixteen
  fixedTarget := fun L n => fixedTargetOfRawCrossBlockInequalityLedger L n
  eventualTarget := fun L =>
    eventualTargetOfArbitrary
      (arbitraryTargetOfRawCrossBlockInequalityLedger L)
  arbitraryTarget := fun L =>
    arbitraryTargetOfRawCrossBlockInequalityLedger L
  targetFacade := fun L =>
    targetFacadeOfFixedAndArbitrary
      (fun n => fixedTargetOfRawCrossBlockInequalityLedger L n)
      (arbitraryTargetOfRawCrossBlockInequalityLedger L)

def crossBlockFlexibleRouteRow :
    ExactBlockFacadeRow CrossBlockFlexibleRouteFields :=
  exactBlockFacadeRowOfTargets
    CrossBlockInequalityClosureW11.targetUpperConstructionFiveSixteen_of_flexibleRoute
    CrossBlockInequalityClosureW11.targetUpperConstructionFiveSixteenAt_of_flexibleRoute_checkedRemainders
    CrossBlockInequalityClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_flexibleRoute_checkedRemainders

/-! ## Integrated matrix -/

/-- Source package shapes used by the integrated arbitrary-`n` matrix. -/
structure PackageLedger where
  exactTargetAssumptions : Prop
  eventualSmallCaseAssumptions : Type
  exactClosedChains : Type
  exactGeneratedClosedChains : Type
  eventualClosedChains : Type
  eventualGeneratedClosedChains : Type
  smallLengthExactBlocks : Prop
  smallLengthClosureObligations : SmallLengthPeriodSearchFamily -> Prop
  smallLengthEventualClosedChains : Type
  smallLengthEventualGeneratedClosedChains : Type
  generatedPointNormalizedPolynomial :
    GeneratedPointPeriodSearchFamily -> Prop
  generatedPointNormalizedValue :
    GeneratedPointPeriodSearchFamily -> Type
  generatedPointLowerBound :
    GeneratedPointPeriodSearchFamily -> Type
  generatedPointCrossBlockLedgers :
    CrossBlockPeriodSearchFamily -> Type
  generatedPointFlexibleCandidateAssembly : Type
  crossBlockInequalityLedgers :
    CrossBlockPeriodSearchFamily -> Type
  crossBlockClosureLedgers :
    CrossBlockPeriodSearchFamily -> Type
  crossBlockFlexibleRoutes : Type

def packageLedger : PackageLedger where
  exactTargetAssumptions := ExactTargetAssumptions
  eventualSmallCaseAssumptions := EventualSmallCaseAssumptions
  exactClosedChains := ExactClosedChainPackage
  exactGeneratedClosedChains := ExactGeneratedClosedChainPackage
  eventualClosedChains := EventualClosedChainPackage
  eventualGeneratedClosedChains := EventualGeneratedClosedChainPackage
  smallLengthExactBlocks := SmallLengthExactBlockTargets
  smallLengthClosureObligations := SmallLengthClosureObligations
  smallLengthEventualClosedChains := SmallLengthEventualClosedChains
  smallLengthEventualGeneratedClosedChains :=
    SmallLengthEventualGeneratedClosedChains
  generatedPointNormalizedPolynomial :=
    GeneratedPointNormalizedPolynomialFields
  generatedPointNormalizedValue := GeneratedPointNormalizedValueFields
  generatedPointLowerBound := GeneratedPointLowerBoundFields
  generatedPointCrossBlockLedgers := CrossBlockInequalityLedger
  generatedPointFlexibleCandidateAssembly :=
    GeneratedPointFlexibleCandidateAssemblyFields
  crossBlockInequalityLedgers := CrossBlockInequalityLedger
  crossBlockClosureLedgers := CrossBlockClosureLedger
  crossBlockFlexibleRoutes := CrossBlockFlexibleRouteFields

/-- Integrated W11 arbitrary-`n` matrix.  Every target row still consumes one
of the displayed source packages. -/
structure Matrix where
  packages : PackageLedger
  finiteRemainders : FiniteRemainderPackage
  targetClosure : ArbitraryNTargetClosureW11.Matrix
  generatedPointClosure : GeneratedPointClosureW11.Matrix
  crossBlockRouteLedger :
    forall F : CrossBlockPeriodSearchFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  exactTargetAssumptions : ExactBlockFacadeRow ExactTargetAssumptions
  eventualSmallCaseAssumptions :
    ThresholdFacadeRow EventualSmallCaseAssumptions
  exactClosedChains : ExactClosedChainFacadeRow ExactClosedChainPackage
  exactGeneratedClosedChains :
    ExactGeneratedClosedChainFacadeRow ExactGeneratedClosedChainPackage
  eventualClosedChains :
    EventualClosedChainFacadeRow EventualClosedChainPackage
  eventualGeneratedClosedChains :
    EventualGeneratedClosedChainFacadeRow EventualGeneratedClosedChainPackage
  smallLengthExactBlocks :
    SmallLengthFacadeBuilder SmallLengthExactBlockTargets
  smallLengthClosureObligations :
    forall F : SmallLengthPeriodSearchFamily,
      SmallLengthFacadeBuilder (SmallLengthClosureObligations F)
  smallLengthEventualClosedChains :
    EventualClosedChainFacadeRow SmallLengthEventualClosedChains
  smallLengthEventualGeneratedClosedChains :
    EventualGeneratedClosedChainFacadeRow
      SmallLengthEventualGeneratedClosedChains
  generatedPointNormalizedPolynomial :
    forall F : GeneratedPointPeriodSearchFamily,
      ExactBlockFacadeRow (GeneratedPointNormalizedPolynomialFields F)
  generatedPointNormalizedValue :
    forall F : GeneratedPointPeriodSearchFamily,
      ExactBlockFacadeRow (GeneratedPointNormalizedValueFields F)
  generatedPointLowerBound :
    forall F : GeneratedPointPeriodSearchFamily,
      ExactBlockFacadeRow (GeneratedPointLowerBoundFields F)
  generatedPointCrossBlockLedger :
    forall F : CrossBlockPeriodSearchFamily,
      ExactBlockFacadeRow (CrossBlockInequalityLedger F)
  generatedPointFlexibleCandidateAssembly :
    ExactBlockFacadeRow GeneratedPointFlexibleCandidateAssemblyFields
  rawCrossBlockInequalityLedger :
    forall F : CrossBlockPeriodSearchFamily,
      ExactBlockFacadeRow (CrossBlockInequalityLedger F)
  crossBlockClosure :
    forall F : CrossBlockPeriodSearchFamily,
      CrossBlockFacadeRow F
  crossBlockFlexibleRoute :
    ExactBlockFacadeRow CrossBlockFlexibleRouteFields

/-- The checked integrated arbitrary-`n` matrix assembled from the W11
arbitrary, small-length, generated-point, and cross-block closure layers. -/
def matrix : Matrix where
  packages := packageLedger
  finiteRemainders := ArbitraryNClosureW11.checkedFiniteRemainders
  targetClosure := ArbitraryNTargetClosureW11.matrix
  generatedPointClosure := GeneratedPointClosureW11.matrix
  crossBlockRouteLedger :=
    CrossBlockInequalityClosureW11.conditionalTargetRouteLedger
  exactTargetAssumptions := exactTargetAssumptionsRow
  eventualSmallCaseAssumptions := eventualSmallCaseAssumptionsRow
  exactClosedChains :=
    exactClosedChainFacadeRow ArbitraryNClosureW11.checkedFiniteRemainders
  exactGeneratedClosedChains :=
    exactGeneratedClosedChainFacadeRow
      ArbitraryNClosureW11.checkedFiniteRemainders
  eventualClosedChains :=
    eventualClosedChainFacadeRow ArbitraryNClosureW11.checkedFiniteRemainders
  eventualGeneratedClosedChains :=
    eventualGeneratedClosedChainFacadeRow
      ArbitraryNClosureW11.checkedFiniteRemainders
  smallLengthExactBlocks := smallLengthExactBlockBuilder
  smallLengthClosureObligations := smallLengthClosureObligationsBuilder
  smallLengthEventualClosedChains := smallLengthEventualClosedChainRow
  smallLengthEventualGeneratedClosedChains :=
    smallLengthEventualGeneratedClosedChainRow
  generatedPointNormalizedPolynomial :=
    generatedPointNormalizedPolynomialFieldsRow
  generatedPointNormalizedValue := generatedPointNormalizedValueFieldsRow
  generatedPointLowerBound := generatedPointLowerBoundFieldsRow
  generatedPointCrossBlockLedger := generatedPointCrossBlockLedgerRow
  generatedPointFlexibleCandidateAssembly :=
    generatedPointFlexibleCandidateAssemblyRow
  rawCrossBlockInequalityLedger := rawCrossBlockInequalityLedgerRow
  crossBlockClosure := crossBlockClosureRow
  crossBlockFlexibleRoute := crossBlockFlexibleRouteRow

/-! ## Public facade projections -/

def targetFacade_of_exactClosedChains
    (P : ExactClosedChainPackage) :
    ArbitraryNTargetFacade :=
  matrix.exactClosedChains.targetFacade P

def targetFacade_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    ArbitraryNTargetFacade :=
  matrix.eventualClosedChains.targetFacade P

def thresholdFacade_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    ThresholdTargetFacade :=
  matrix.eventualClosedChains.thresholdFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactClosedChains
    (P : ExactClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactClosedChains.arbitraryTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualClosedChains.arbitraryTarget P

theorem targetUpperConstructionFiveSixteenSmallUpTo_sixteen_mul_six
    (C : SmallLengthExactBlockTargets) :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo (16 * 6) :=
  matrix.smallLengthExactBlocks.smallTarget C

def targetFacade_of_smallLengthExactBlocks_and_large
    (C : SmallLengthExactBlockTargets)
    (Hlarge :
      forall n : Nat, 16 * 6 <= n ->
        PachToth.targetUpperConstructionFiveSixteenAt n) :
    ArbitraryNTargetFacade :=
  matrix.smallLengthExactBlocks.targetFacadeOfLarge C Hlarge

def targetFacade_of_smallLengthEventualClosedChains
    (P : SmallLengthEventualClosedChains) :
    ArbitraryNTargetFacade :=
  matrix.smallLengthEventualClosedChains.targetFacade P

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_smallLengthEventualClosedChains
    (P : SmallLengthEventualClosedChains) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.smallLengthEventualClosedChains.arbitraryTarget P

def targetFacade_of_generatedPointLowerBoundFields
    {F : GeneratedPointPeriodSearchFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ArbitraryNTargetFacade :=
  (matrix.generatedPointLowerBound F).targetFacade C

theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPointLowerBoundFields
    {F : GeneratedPointPeriodSearchFamily}
    (C : GeneratedPointLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointLowerBound F).arbitraryTarget C

def targetFacade_of_rawCrossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.rawCrossBlockInequalityLedger F).targetFacade L

def targetFacade_of_crossBlockClosureLedger
    {F : CrossBlockPeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.crossBlockClosure F).targetFacade C

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockClosureLedger
    {F : CrossBlockPeriodSearchFamily}
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.crossBlockClosure F).exactBlockAt C k hk

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
    {F : CrossBlockPeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockClosure F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_rawCrossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.rawCrossBlockInequalityLedger F).arbitraryTarget L

end

end ArbitraryNIntegratedW11
end PachToth
end ErdosProblems1066
