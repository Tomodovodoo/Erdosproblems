import ErdosProblems1066.PachToth.ArbitraryNIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNTargetClosureW11
import ErdosProblems1066.PachToth.SmallLengthIntegratedW11
import ErdosProblems1066.PachToth.GeneratedPointIntegratedMatrixW11
import ErdosProblems1066.PachToth.CrossBlockIntegratedW11

set_option autoImplicit false

/-!
# W11 final arbitrary-`n` aggregate matrix

This file is the final W11 Pach--Toth arbitrary-`n` ledger.  It gathers the
checked arbitrary-`n`, target-closure, small-length, generated-point, and
cross-block matrices into one record while keeping every target route attached
to an explicit input package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNFinalIntegratedW11

noncomputable section

abbrev ArbitraryNMatrix :=
  ArbitraryNIntegratedW11.Matrix

abbrev TargetClosureMatrix :=
  ArbitraryNTargetClosureW11.Matrix

abbrev SmallLengthMatrix :=
  SmallLengthIntegratedW11.Matrix

abbrev GeneratedPointMatrix :=
  GeneratedPointIntegratedMatrixW11.Matrix

abbrev CrossBlockMatrix :=
  CrossBlockIntegratedW11.Matrix

abbrev FiniteRemainderPackage :=
  ArbitraryNIntegratedW11.FiniteRemainderPackage

abbrev ArbitraryNTargetFacade :=
  ArbitraryNIntegratedW11.ArbitraryNTargetFacade

abbrev ThresholdTargetFacade :=
  ArbitraryNIntegratedW11.ThresholdTargetFacade

abbrev ExactClosedChainPackage :=
  ArbitraryNIntegratedW11.ExactClosedChainPackage

abbrev ExactGeneratedClosedChainPackage :=
  ArbitraryNIntegratedW11.ExactGeneratedClosedChainPackage

abbrev EventualClosedChainPackage :=
  ArbitraryNIntegratedW11.EventualClosedChainPackage

abbrev EventualGeneratedClosedChainPackage :=
  ArbitraryNIntegratedW11.EventualGeneratedClosedChainPackage

abbrev SmallLengthPeriodSearchFamily :=
  ArbitraryNIntegratedW11.SmallLengthPeriodSearchFamily

abbrev SmallLengthExactBlockTargets :=
  ArbitraryNIntegratedW11.SmallLengthExactBlockTargets

abbrev SmallLengthClosureObligations :=
  ArbitraryNIntegratedW11.SmallLengthClosureObligations

abbrev SmallLengthEventualClosedChains :=
  ArbitraryNIntegratedW11.SmallLengthEventualClosedChains

abbrev SmallLengthEventualGeneratedClosedChains :=
  ArbitraryNIntegratedW11.SmallLengthEventualGeneratedClosedChains

abbrev SmallLengthEventualLargeTargets :=
  SmallLengthIntegratedW11.EventualLargeTargetAssumptionsBelowSix

abbrev SmallLengthEventualFiniteCertificates :=
  SmallLengthIntegratedW11.EventualFiniteCertificateAssumptionsBelowSix

abbrev GeneratedPointPeriodSearchFamily :=
  ArbitraryNIntegratedW11.GeneratedPointPeriodSearchFamily

abbrev GeneratedPointNormalizedPolynomialFields :=
  ArbitraryNIntegratedW11.GeneratedPointNormalizedPolynomialFields

abbrev GeneratedPointNormalizedValueFields :=
  ArbitraryNIntegratedW11.GeneratedPointNormalizedValueFields

abbrev GeneratedPointLowerBoundFields :=
  ArbitraryNIntegratedW11.GeneratedPointLowerBoundFields

abbrev GeneratedPointFlexibleCandidateAssemblyFields :=
  ArbitraryNIntegratedW11.GeneratedPointFlexibleCandidateAssemblyFields

abbrev CrossBlockPeriodSearchFamily :=
  ArbitraryNIntegratedW11.CrossBlockPeriodSearchFamily

abbrev CrossBlockInequalityLedger :=
  ArbitraryNIntegratedW11.CrossBlockInequalityLedger

abbrev CrossBlockClosureLedger :=
  ArbitraryNIntegratedW11.CrossBlockClosureLedger

abbrev CrossBlockFlexibleRouteFields :=
  ArbitraryNIntegratedW11.CrossBlockFlexibleRouteFields

/-! ## Named final field groups -/

/-- Exact closed-chain rows, including generated-chain projections. -/
structure ExactClosedChainFields where
  finiteRemainders : FiniteRemainderPackage
  exactClosedChains :
    ArbitraryNIntegratedW11.ExactClosedChainFacadeRow ExactClosedChainPackage
  exactGeneratedClosedChains :
    ArbitraryNIntegratedW11.ExactGeneratedClosedChainFacadeRow
      ExactGeneratedClosedChainPackage

/-- Eventual large-chain rows together with their finite small complements. -/
structure EventualLargeChainFields where
  finiteRemainders : FiniteRemainderPackage
  eventualClosedChains :
    ArbitraryNIntegratedW11.EventualClosedChainFacadeRow
      EventualClosedChainPackage
  eventualGeneratedClosedChains :
    ArbitraryNIntegratedW11.EventualGeneratedClosedChainFacadeRow
      EventualGeneratedClosedChainPackage
  smallLengthEventualClosedChains :
    ArbitraryNIntegratedW11.EventualClosedChainFacadeRow
      SmallLengthEventualClosedChains
  smallLengthEventualGeneratedClosedChains :
    ArbitraryNIntegratedW11.EventualGeneratedClosedChainFacadeRow
      SmallLengthEventualGeneratedClosedChains

/-- Finite small-case and threshold-six rows. -/
structure SmallCaseFields where
  sourceMatrix : SmallLengthMatrix
  exactBlocks :
    SmallLengthIntegratedW11.ExactBlockRouteRow SmallLengthExactBlockTargets
  exactBlockBuilder :
    ArbitraryNIntegratedW11.SmallLengthFacadeBuilder
      SmallLengthExactBlockTargets
  closureObligationBuilders :
    forall F : SmallLengthPeriodSearchFamily,
      ArbitraryNIntegratedW11.SmallLengthFacadeBuilder
        (SmallLengthClosureObligations F)
  eventualLargeTargets :
    SmallLengthIntegratedW11.ThresholdRouteRow SmallLengthEventualLargeTargets
  eventualFiniteCertificates :
    SmallLengthIntegratedW11.ThresholdRouteRow
      SmallLengthEventualFiniteCertificates

/-- Generated-point routes with their explicit field packages visible. -/
structure GeneratedPointFields where
  sourceMatrix : GeneratedPointMatrix
  requiredData : GeneratedPointIntegratedMatrixW11.RequiredDataLedger
  normalizedPolynomial :
    forall F : GeneratedPointPeriodSearchFamily,
      ArbitraryNIntegratedW11.ExactBlockFacadeRow
        (GeneratedPointNormalizedPolynomialFields F)
  normalizedValue :
    forall F : GeneratedPointPeriodSearchFamily,
      ArbitraryNIntegratedW11.ExactBlockFacadeRow
        (GeneratedPointNormalizedValueFields F)
  lowerBound :
    forall F : GeneratedPointPeriodSearchFamily,
      ArbitraryNIntegratedW11.ExactBlockFacadeRow
        (GeneratedPointLowerBoundFields F)
  flexibleCandidateAssembly :
    ArbitraryNIntegratedW11.ExactBlockFacadeRow
      GeneratedPointFlexibleCandidateAssemblyFields

/-- Cross-block source and target-facing closure rows. -/
structure CrossBlockFields where
  sourceMatrix : CrossBlockMatrix
  routeLedger :
    forall F : CrossBlockPeriodSearchFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  generatedPointLedger :
    forall F : CrossBlockPeriodSearchFamily,
      ArbitraryNIntegratedW11.ExactBlockFacadeRow
        (CrossBlockInequalityLedger F)
  rawInequalityLedger :
    forall F : CrossBlockPeriodSearchFamily,
      ArbitraryNIntegratedW11.ExactBlockFacadeRow
        (CrossBlockInequalityLedger F)
  closureLedger :
    forall F : CrossBlockPeriodSearchFamily,
      ArbitraryNIntegratedW11.CrossBlockFacadeRow F
  flexibleRoute :
    ArbitraryNIntegratedW11.ExactBlockFacadeRow CrossBlockFlexibleRouteFields

def exactClosedChainFieldsOfArbitraryN
    (M : ArbitraryNMatrix) :
    ExactClosedChainFields where
  finiteRemainders := M.finiteRemainders
  exactClosedChains := M.exactClosedChains
  exactGeneratedClosedChains := M.exactGeneratedClosedChains

def eventualLargeChainFieldsOfArbitraryN
    (M : ArbitraryNMatrix) :
    EventualLargeChainFields where
  finiteRemainders := M.finiteRemainders
  eventualClosedChains := M.eventualClosedChains
  eventualGeneratedClosedChains := M.eventualGeneratedClosedChains
  smallLengthEventualClosedChains := M.smallLengthEventualClosedChains
  smallLengthEventualGeneratedClosedChains :=
    M.smallLengthEventualGeneratedClosedChains

def smallCaseFieldsOfMatrices
    (M : ArbitraryNMatrix) (S : SmallLengthMatrix) :
    SmallCaseFields where
  sourceMatrix := S
  exactBlocks := S.exactBlocks
  exactBlockBuilder := M.smallLengthExactBlocks
  closureObligationBuilders := M.smallLengthClosureObligations
  eventualLargeTargets := S.eventualLargeTargets
  eventualFiniteCertificates := S.eventualFiniteCertificates

def generatedPointFieldsOfMatrices
    (M : ArbitraryNMatrix) (G : GeneratedPointMatrix) :
    GeneratedPointFields where
  sourceMatrix := G
  requiredData := G.requiredData
  normalizedPolynomial := M.generatedPointNormalizedPolynomial
  normalizedValue := M.generatedPointNormalizedValue
  lowerBound := M.generatedPointLowerBound
  flexibleCandidateAssembly := M.generatedPointFlexibleCandidateAssembly

def crossBlockFieldsOfMatrices
    (M : ArbitraryNMatrix) (C : CrossBlockMatrix) :
    CrossBlockFields where
  sourceMatrix := C
  routeLedger := M.crossBlockRouteLedger
  generatedPointLedger := M.generatedPointCrossBlockLedger
  rawInequalityLedger := M.rawCrossBlockInequalityLedger
  closureLedger := M.crossBlockClosure
  flexibleRoute := M.crossBlockFlexibleRoute

/-! ## Final matrix -/

/-- Final W11 arbitrary-`n` aggregate matrix. -/
structure Matrix where
  arbitraryN : ArbitraryNMatrix
  targetClosure : TargetClosureMatrix
  smallLength : SmallLengthMatrix
  generatedPoint : GeneratedPointMatrix
  crossBlock : CrossBlockMatrix
  exactClosedChain : ExactClosedChainFields
  eventualLargeChain : EventualLargeChainFields
  smallCases : SmallCaseFields
  generatedPointFields : GeneratedPointFields
  crossBlockFields : CrossBlockFields

/-- The checked final W11 arbitrary-`n` aggregate matrix. -/
def matrix : Matrix where
  arbitraryN := ArbitraryNIntegratedW11.matrix
  targetClosure := ArbitraryNTargetClosureW11.matrix
  smallLength := SmallLengthIntegratedW11.matrix
  generatedPoint := GeneratedPointIntegratedMatrixW11.matrix
  crossBlock := CrossBlockIntegratedW11.matrix
  exactClosedChain :=
    exactClosedChainFieldsOfArbitraryN ArbitraryNIntegratedW11.matrix
  eventualLargeChain :=
    eventualLargeChainFieldsOfArbitraryN ArbitraryNIntegratedW11.matrix
  smallCases :=
    smallCaseFieldsOfMatrices
      ArbitraryNIntegratedW11.matrix
      SmallLengthIntegratedW11.matrix
  generatedPointFields :=
    generatedPointFieldsOfMatrices
      ArbitraryNIntegratedW11.matrix
      GeneratedPointIntegratedMatrixW11.matrix
  crossBlockFields :=
    crossBlockFieldsOfMatrices
      ArbitraryNIntegratedW11.matrix
      CrossBlockIntegratedW11.matrix

/-! ## Exact closed-chain projections -/

def exactChainUpper_of_exactClosedChains
    (P : ExactClosedChainPackage) (k : Nat) (hk : 0 < k) :
    SplitSoundness.ExactChainUpper k :=
  matrix.exactClosedChain.exactClosedChains.chain P k hk

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactClosedChains
    (P : ExactClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactClosedChain.exactClosedChains.arbitraryTarget P

def targetFacade_of_exactClosedChains
    (P : ExactClosedChainPackage) :
    ArbitraryNTargetFacade :=
  matrix.exactClosedChain.exactClosedChains.targetFacade P

def generatedClosedChainData_of_exactGeneratedClosedChains
    (P : ExactGeneratedClosedChainPackage)
    (k : Nat) (hk : 0 < k) :
    SplitRealizationClosure.ExactGeneratedClosedChainData k hk :=
  matrix.exactClosedChain.exactGeneratedClosedChains.generatedData P k hk

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactGeneratedClosedChains
    (P : ExactGeneratedClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactClosedChain.exactGeneratedClosedChains.arbitraryTarget P

/-! ## Eventual large-chain and small-case projections -/

def largeChain_of_eventualClosedChains
    (P : EventualClosedChainPackage)
    (k : Nat)
    (hK :
      matrix.eventualLargeChain.eventualClosedChains.blockThreshold P <= k)
    (hk : 0 < k) :
    SplitSoundness.ExactChainUpper k :=
  matrix.eventualLargeChain.eventualClosedChains.largeChain P k hK hk

theorem smallTarget_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo
      (matrix.eventualLargeChain.eventualClosedChains.vertexThreshold P) :=
  matrix.eventualLargeChain.eventualClosedChains.smallTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualLargeChain.eventualClosedChains.arbitraryTarget P

def thresholdFacade_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    ThresholdTargetFacade :=
  matrix.eventualLargeChain.eventualClosedChains.thresholdFacade P

def largeGeneratedData_of_eventualGeneratedClosedChains
    (P : EventualGeneratedClosedChainPackage)
    (k : Nat)
    (hK :
      matrix.eventualLargeChain.eventualGeneratedClosedChains.blockThreshold P
        <= k)
    (hk : 0 < k) :
    SplitRealizationClosure.ExactGeneratedClosedChainData k hk :=
  matrix.eventualLargeChain.eventualGeneratedClosedChains.largeData P k hK hk

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_eventualGeneratedClosedChains
    (P : EventualGeneratedClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualLargeChain.eventualGeneratedClosedChains.arbitraryTarget P

theorem exactBlockTarget_of_smallLengthExactBlocks
    (C : SmallLengthExactBlockTargets)
    (k : Nat) (hkLt : k < 6) (hkPos : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  matrix.smallCases.exactBlocks.exactBlock C k hkLt hkPos

theorem targetUpperConstructionFiveSixteenSmallUpTo_sixteen_mul_six
    (C : SmallLengthExactBlockTargets) :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo (16 * 6) :=
  matrix.smallCases.exactBlocks.smallTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_smallLengthEventualLarge
    (P : SmallLengthEventualLargeTargets) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.smallCases.eventualLargeTargets.arbitraryTarget P

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_smallLengthEventualClosedChains
    (P : SmallLengthEventualClosedChains) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualLargeChain.smallLengthEventualClosedChains.arbitraryTarget P

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_smallLengthFiniteCertificates
    (P : SmallLengthEventualFiniteCertificates) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.smallCases.eventualFiniteCertificates.arbitraryTarget P

/-! ## Generated-point projections -/

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_generatedPointNormalizedPolynomial
    {F : GeneratedPointPeriodSearchFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointFields.normalizedPolynomial F).arbitraryTarget C

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_generatedPointNormalizedValue
    {F : GeneratedPointPeriodSearchFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointFields.normalizedValue F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPointLowerBound
    {F : GeneratedPointPeriodSearchFamily}
    (C : GeneratedPointLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointFields.lowerBound F).arbitraryTarget C

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_generatedPointFlexibleCandidate
    (C : GeneratedPointFlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.generatedPointFields.flexibleCandidateAssembly.arbitraryTarget C

def targetFacade_of_generatedPointLowerBound
    {F : GeneratedPointPeriodSearchFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ArbitraryNTargetFacade :=
  (matrix.generatedPointFields.lowerBound F).targetFacade C

/-! ## Cross-block projections -/

theorem separated_of_crossBlockClosureLedger
    {F : CrossBlockPeriodSearchFamily}
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    CrossBlockInequalityClosureW11.GeneratedGlobalSeparationAt F k hk :=
  (matrix.crossBlockFields.closureLedger F).separated C k hk

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockClosureLedger
    {F : CrossBlockPeriodSearchFamily}
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.crossBlockFields.closureLedger F).exactBlockAt C k hk

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
    {F : CrossBlockPeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockFields.closureLedger F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockFields.rawInequalityLedger F).arbitraryTarget L

def targetFacade_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.crossBlockFields.rawInequalityLedger F).targetFacade L

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockFlexibleRoute
    (R : CrossBlockFlexibleRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.crossBlockFields.flexibleRoute.arbitraryTarget R

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_crossBlockSourceInequalityLedger
    {F : CrossBlockIntegratedW11.PeriodSearchFamily}
    (L : CrossBlockIntegratedW11.CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockFields.sourceMatrix.inequalityLedgers F).arbitraryTarget L

end

end ArbitraryNFinalIntegratedW11
end PachToth
end ErdosProblems1066
