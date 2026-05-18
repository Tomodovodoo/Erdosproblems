import ErdosProblems1066.PachToth.GeneratedTargetIntegratedW11
import ErdosProblems1066.PachToth.GeneratedPointIntegratedMatrixW11
import ErdosProblems1066.PachToth.CrossBlockIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix

set_option autoImplicit false

/-!
# W11 generated and cross-block final integration

This file is a final source-facing aggregate for the generated-point and
cross-block W11 ledgers.  It records explicit generated-point field shapes,
explicit inequality-ledger field shapes, and checked routes through the
target, cross-block, arbitrary-`n`, and broad Pach--Toth W11 matrices.

Every public target projection below remains conditional on an explicit
generated-point package, inequality ledger, closure ledger, or final
conditional package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedFinalIntegratedW11

noncomputable section

universe u

abbrev GeneratedPointFamily :=
  GeneratedPointIntegratedMatrixW11.RoleHingedPeriodSearchFamily

abbrev GeneratedPointNormalizedPolynomialFields
    (F : GeneratedPointFamily) :=
  GeneratedPointIntegratedMatrixW11.NormalizedPolynomialFields F

abbrev GeneratedPointNormalizedValueFields
    (F : GeneratedPointFamily) :=
  GeneratedPointIntegratedMatrixW11.NormalizedValueFields F

abbrev GeneratedPointLowerBoundFields
    (F : GeneratedPointFamily) :=
  GeneratedPointIntegratedMatrixW11.LowerBoundFields F

abbrev CrossBlockFamily :=
  GeneratedPointIntegratedMatrixW11.CrossBlockPeriodSearchFamily

abbrev CrossBlockInequalityLedger (F : CrossBlockFamily) :=
  GeneratedPointIntegratedMatrixW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger (F : CrossBlockFamily) :=
  GeneratedPointIntegratedMatrixW11.CrossBlockClosureLedger F

abbrev FlexibleCandidateAssemblyFields :=
  GeneratedPointIntegratedMatrixW11.FlexibleCandidateAssemblyFields

abbrev CandidateValueMatrixFamily :=
  GeneratedPointIntegratedMatrixW11.CandidateValueMatrixFamily

abbrev FinalConditionalFamily :=
  GeneratedPointIntegratedMatrixW11.FinalConditionalFamily

abbrev CrossBlockIntegratedFamily :=
  CrossBlockIntegratedW11.PeriodSearchFamily

abbrev CrossBlockIntegratedInequalityLedger
    (F : CrossBlockIntegratedFamily) :=
  CrossBlockIntegratedW11.CrossBlockInequalityLedger F

abbrev CrossBlockIntegratedClosureLedger
    (F : CrossBlockIntegratedFamily) :=
  CrossBlockIntegratedW11.CrossBlockClosureLedger F

abbrev ArbitraryNCrossBlockFamily :=
  ArbitraryNIntegratedW11.CrossBlockPeriodSearchFamily

abbrev ArbitraryNCrossBlockInequalityLedger
    (F : ArbitraryNCrossBlockFamily) :=
  ArbitraryNIntegratedW11.CrossBlockInequalityLedger F

abbrev ArbitraryNCrossBlockClosureLedger
    (F : ArbitraryNCrossBlockFamily) :=
  ArbitraryNIntegratedW11.CrossBlockClosureLedger F

/-! ## Shared conditional target rows -/

/-- Exact, eventual, and arbitrary Pach--Toth projections from one explicit
source package. -/
structure ConditionalTargetRoute (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

namespace ConditionalTargetRoute

/-- An arbitrary-`n` target gives an eventual route with threshold zero. -/
theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

/-- Forget the fixed-`n` field of a generated target route. -/
def ofGeneratedTargetRoute
    {alpha : Sort u}
    (R : GeneratedTargetIntegratedW11.TargetRoute alpha) :
    ConditionalTargetRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

/-- Forget the fixed-`n` field of a generated-point target row. -/
def ofGeneratedPointTargetRow
    {alpha : Sort u}
    (R : GeneratedPointIntegratedMatrixW11.GeneratedPointTargetRow alpha) :
    ConditionalTargetRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

/-- Add the eventual projection to a checked finite-remainder row. -/
def ofCheckedRemainderRouteRow
    {alpha : Sort u}
    (R : GeneratedPointIntegratedMatrixW11.CheckedRemainderRouteRow alpha) :
    ConditionalTargetRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (R.arbitraryTarget a)
  arbitraryTarget := R.arbitraryTarget

/-- Add the eventual projection to a cross-block integrated checked row. -/
def ofCrossBlockIntegratedCheckedRow
    {alpha : Sort u}
    (R : CrossBlockIntegratedW11.CheckedTargetRow alpha) :
    ConditionalTargetRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (R.arbitraryTarget a)
  arbitraryTarget := R.arbitraryTarget

/-- Reuse an arbitrary-`n` exact block facade row. -/
def ofArbitraryNExactBlockFacadeRow
    {alpha : Sort u}
    (R : ArbitraryNIntegratedW11.ExactBlockFacadeRow alpha) :
    ConditionalTargetRoute alpha where
  exactTarget := R.blockTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

/-- Reuse a broad W11 exact/arbitrary pair and derive the eventual route. -/
def ofExactAndArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    ConditionalTargetRoute alpha where
  exactTarget := exactTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (arbitraryTarget a)
  arbitraryTarget := arbitraryTarget

end ConditionalTargetRoute

/-! ## Explicit source ledgers -/

/-- Explicit generated-point field shapes consumed by this final aggregate. -/
structure GeneratedPointFieldLedger where
  normalizedPolynomial :
    GeneratedPointFamily -> Prop
  normalizedValue :
    GeneratedPointFamily -> Type
  lowerBound :
    GeneratedPointFamily -> Type
  flexibleCandidateAssembly : Type
  candidateValueMatrices : Type
  finalConditionalFamilies : Type

/-- The generated-point package shapes, with no package inhabitants supplied. -/
def generatedPointFieldLedger : GeneratedPointFieldLedger where
  normalizedPolynomial := GeneratedPointNormalizedPolynomialFields
  normalizedValue := GeneratedPointNormalizedValueFields
  lowerBound := GeneratedPointLowerBoundFields
  flexibleCandidateAssembly := FlexibleCandidateAssemblyFields
  candidateValueMatrices := CandidateValueMatrixFamily
  finalConditionalFamilies := FinalConditionalFamily

/-- Explicit cross-block inequality and closure shapes consumed by this final
aggregate. -/
structure InequalityLedgerFieldLedger where
  generatedCrossBlockInequality :
    CrossBlockFamily -> Type
  generatedCrossBlockClosure :
    CrossBlockFamily -> Type
  integratedCrossBlockInequality :
    CrossBlockIntegratedFamily -> Type
  integratedCrossBlockClosure :
    CrossBlockIntegratedFamily -> Type
  crossBlockIntegratedFieldShapes :
    CrossBlockIntegratedW11.ExplicitFieldShapes
  arbitraryNCrossBlockInequality :
    ArbitraryNCrossBlockFamily -> Type
  arbitraryNCrossBlockClosure :
    ArbitraryNCrossBlockFamily -> Type

/-- The cross-block package shapes, with all numeric inequality rows still
external. -/
def inequalityLedgerFieldLedger : InequalityLedgerFieldLedger where
  generatedCrossBlockInequality := CrossBlockInequalityLedger
  generatedCrossBlockClosure := CrossBlockClosureLedger
  integratedCrossBlockInequality := CrossBlockIntegratedInequalityLedger
  integratedCrossBlockClosure := CrossBlockIntegratedClosureLedger
  crossBlockIntegratedFieldShapes := CrossBlockIntegratedW11.explicitFieldShapes
  arbitraryNCrossBlockInequality := ArbitraryNCrossBlockInequalityLedger
  arbitraryNCrossBlockClosure := ArbitraryNCrossBlockClosureLedger

/-! ## Imported checked matrices -/

/-- Checked W11 matrices imported by the final generated/cross-block aggregate. -/
structure ImportedMatrices where
  generatedTarget :
    GeneratedTargetIntegratedW11.Matrix
  generatedPointIntegrated :
    GeneratedPointIntegratedMatrixW11.Matrix
  crossBlockIntegrated :
    CrossBlockIntegratedW11.Matrix
  arbitraryNIntegrated :
    ArbitraryNIntegratedW11.Matrix
  pachTothW11Integrated :
    PachTothW11IntegratedMatrix.Matrix

/-- Imported checked W11 matrices. -/
def importedMatrices : ImportedMatrices where
  generatedTarget := GeneratedTargetIntegratedW11.matrix
  generatedPointIntegrated := GeneratedPointIntegratedMatrixW11.matrix
  crossBlockIntegrated := CrossBlockIntegratedW11.matrix
  arbitraryNIntegrated := ArbitraryNIntegratedW11.matrix
  pachTothW11Integrated := PachTothW11IntegratedMatrix.matrix

/-! ## Generated-point and cross-block routes -/

/-- Conditional generated-point routes visible in the final aggregate. -/
structure GeneratedPointRoutes where
  normalizedPolynomial :
    forall F : GeneratedPointFamily,
      ConditionalTargetRoute (GeneratedPointNormalizedPolynomialFields F)
  normalizedValue :
    forall F : GeneratedPointFamily,
      ConditionalTargetRoute (GeneratedPointNormalizedValueFields F)
  lowerBound :
    forall F : GeneratedPointFamily,
      ConditionalTargetRoute (GeneratedPointLowerBoundFields F)
  flexibleCandidateAssembly :
    ConditionalTargetRoute FlexibleCandidateAssemblyFields
  candidateValueMatrices :
    ConditionalTargetRoute CandidateValueMatrixFamily
  finalConditionalFamily :
    ConditionalTargetRoute FinalConditionalFamily

/-- Checked generated-point routes. -/
def generatedPointRoutes : GeneratedPointRoutes where
  normalizedPolynomial := fun F =>
    ConditionalTargetRoute.ofGeneratedTargetRoute
      (GeneratedTargetIntegratedW11.matrix.generatedPoint.normalizedPolynomial F)
  normalizedValue := fun F =>
    ConditionalTargetRoute.ofGeneratedTargetRoute
      (GeneratedTargetIntegratedW11.matrix.generatedPoint.normalizedValue F)
  lowerBound := fun F =>
    ConditionalTargetRoute.ofGeneratedTargetRoute
      (GeneratedTargetIntegratedW11.matrix.generatedPoint.lowerBound F)
  flexibleCandidateAssembly :=
    ConditionalTargetRoute.ofGeneratedTargetRoute
      (GeneratedTargetIntegratedW11.matrix.generatedPoint
        |>.flexibleCandidateAssembly
        |>.route)
  candidateValueMatrices :=
    ConditionalTargetRoute.ofCheckedRemainderRouteRow
      GeneratedPointIntegratedMatrixW11.matrix.candidateValueMatrices
  finalConditionalFamily :=
    ConditionalTargetRoute.ofGeneratedTargetRoute
      (GeneratedTargetIntegratedW11.matrix.generatedPoint
        |>.finalConditionalFamily
        |>.route)

/-- Final route for a generated cross-block inequality ledger. -/
structure GeneratedCrossBlockRoute (F : CrossBlockFamily) where
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
  directRoute :
    ConditionalTargetRoute (CrossBlockInequalityLedger F)
  closureRoute :
    ConditionalTargetRoute (CrossBlockClosureLedger F)

/-- Checked generated cross-block route. -/
def generatedCrossBlockRoute
    (F : CrossBlockFamily) :
    GeneratedCrossBlockRoute F where
  toClosureLedger :=
    GeneratedPointIntegratedMatrixW11.toCrossBlockClosureLedger
  separated :=
    (GeneratedTargetIntegratedW11.matrix.generatedPoint.crossBlockLedger F)
      |>.separated
  exactBlockTarget :=
    (GeneratedTargetIntegratedW11.matrix.generatedPoint.crossBlockLedger F)
      |>.exactBlockTarget
  directRoute :=
    ConditionalTargetRoute.ofGeneratedTargetRoute
      ((GeneratedTargetIntegratedW11.matrix.generatedPoint.crossBlockLedger F)
        |>.route)
  closureRoute :=
    ConditionalTargetRoute.ofGeneratedTargetRoute
      (GeneratedTargetIntegratedW11.matrix.broadFacades
        |>.integratedCrossBlockClosure F)

/-- Final route for cross-block integrated inequality and closure ledgers. -/
structure IntegratedCrossBlockRoutes where
  inequality :
    forall F : CrossBlockIntegratedFamily,
      ConditionalTargetRoute (CrossBlockIntegratedInequalityLedger F)
  closure :
    forall F : CrossBlockIntegratedFamily,
      ConditionalTargetRoute (CrossBlockIntegratedClosureLedger F)

/-- Checked routes from `CrossBlockIntegratedW11`. -/
def integratedCrossBlockRoutes : IntegratedCrossBlockRoutes where
  inequality := fun F =>
    { exactTarget := fun L =>
        CrossBlockIntegratedW11.targetUpperConstructionFiveSixteen_of_crossBlockInequalityLedger
          (F := F) L
      eventualTarget := fun L =>
        ConditionalTargetRoute.eventualTargetOfArbitrary
          (CrossBlockIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockInequalityLedger
            (F := F) L)
      arbitraryTarget := fun L =>
        CrossBlockIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockInequalityLedger
          (F := F) L }
  closure := fun F =>
    { exactTarget := fun C =>
        (CrossBlockIntegratedW11.matrix.closureLedgers F).exactTarget C
      eventualTarget := fun C =>
        ConditionalTargetRoute.eventualTargetOfArbitrary
          ((CrossBlockIntegratedW11.matrix.closureLedgers F).arbitraryTarget C)
      arbitraryTarget := fun C =>
        (CrossBlockIntegratedW11.matrix.closureLedgers F).arbitraryTarget C }

/-- Final route for arbitrary-`n` cross-block ledgers. -/
structure ArbitraryNCrossBlockRoutes where
  rawInequality :
    forall F : ArbitraryNCrossBlockFamily,
      ConditionalTargetRoute (ArbitraryNCrossBlockInequalityLedger F)
  closure :
    forall F : ArbitraryNCrossBlockFamily,
      ConditionalTargetRoute (ArbitraryNCrossBlockClosureLedger F)

/-- Checked routes from `ArbitraryNIntegratedW11`. -/
def arbitraryNCrossBlockRoutes : ArbitraryNCrossBlockRoutes where
  rawInequality := fun F =>
    ConditionalTargetRoute.ofArbitraryNExactBlockFacadeRow
      (ArbitraryNIntegratedW11.matrix.rawCrossBlockInequalityLedger F)
  closure := fun F =>
    { exactTarget := fun C =>
        (ArbitraryNIntegratedW11.matrix.crossBlockClosure F).blockTarget C
      eventualTarget := fun C =>
        (ArbitraryNIntegratedW11.matrix.crossBlockClosure F).eventualTarget C
      arbitraryTarget := fun C =>
        (ArbitraryNIntegratedW11.matrix.crossBlockClosure F).arbitraryTarget C }

/-- Routes through the broad W11 Pach--Toth integrated matrix. -/
structure BroadIntegratedRoutes where
  generatedPointNormalizedPolynomial :
    forall F : GeneratedPointFamily,
      ConditionalTargetRoute (GeneratedPointNormalizedPolynomialFields F)
  generatedPointNormalizedValue :
    forall F : GeneratedPointFamily,
      ConditionalTargetRoute (GeneratedPointNormalizedValueFields F)
  generatedPointLowerBound :
    forall F : GeneratedPointFamily,
      ConditionalTargetRoute (GeneratedPointLowerBoundFields F)
  generatedPointCrossBlockLedger :
    forall F : CrossBlockFamily,
      ConditionalTargetRoute (CrossBlockInequalityLedger F)
  crossBlockClosure :
    forall F : CrossBlockFamily,
      ConditionalTargetRoute (CrossBlockClosureLedger F)

/-- Checked routes through `PachTothW11IntegratedMatrix`. -/
def broadIntegratedRoutes : BroadIntegratedRoutes where
  generatedPointNormalizedPolynomial := fun F =>
    ConditionalTargetRoute.ofExactAndArbitrary
      (fun C =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_generatedPointNormalizedPolynomial
          (F := F) C)
      (fun C =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_generatedPointNormalizedPolynomial
          (F := F) C)
  generatedPointNormalizedValue := fun F =>
    ConditionalTargetRoute.ofExactAndArbitrary
      (fun C =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_generatedPointNormalizedValue
          (F := F) C)
      (fun C =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_generatedPointNormalizedValue
          (F := F) C)
  generatedPointLowerBound := fun F =>
    ConditionalTargetRoute.ofExactAndArbitrary
      (fun C =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_generatedPointLowerBound
          (F := F) C)
      (fun C =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_generatedPointLowerBound
          (F := F) C)
  generatedPointCrossBlockLedger := fun F =>
    ConditionalTargetRoute.ofExactAndArbitrary
      (fun L =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_generatedPointCrossBlockLedger
          (F := F) L)
      (fun L =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_generatedPointCrossBlockLedger
          (F := F) L)
  crossBlockClosure := fun F =>
    ConditionalTargetRoute.ofExactAndArbitrary
      (fun C =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
          (F := F) C)
      (fun C =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
          (F := F) C)

/-! ## Final aggregate matrix -/

/-- Final W11 generated/cross-block aggregate.

The matrix contains route ledgers only.  It does not contain inhabitants of
the generated-point or inequality packages listed in the explicit ledgers. -/
structure Matrix where
  generatedPointFields : GeneratedPointFieldLedger
  inequalityLedgerFields : InequalityLedgerFieldLedger
  imported : ImportedMatrices
  generatedPoint : GeneratedPointRoutes
  generatedCrossBlock :
    forall F : CrossBlockFamily, GeneratedCrossBlockRoute F
  integratedCrossBlock : IntegratedCrossBlockRoutes
  arbitraryNCrossBlock : ArbitraryNCrossBlockRoutes
  broadIntegrated : BroadIntegratedRoutes
  blockers : GeneratedTargetIntegratedW11.TransitionBlockers

/-- Checked final generated/cross-block aggregate. -/
def matrix : Matrix where
  generatedPointFields := generatedPointFieldLedger
  inequalityLedgerFields := inequalityLedgerFieldLedger
  imported := importedMatrices
  generatedPoint := generatedPointRoutes
  generatedCrossBlock := generatedCrossBlockRoute
  integratedCrossBlock := integratedCrossBlockRoutes
  arbitraryNCrossBlock := arbitraryNCrossBlockRoutes
  broadIntegrated := broadIntegratedRoutes
  blockers := GeneratedTargetIntegratedW11.transitionBlockers

/-! ## Public generated-point projections -/

theorem exactTarget_of_normalizedPolynomialFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedPoint.normalizedPolynomial F).exactTarget C

theorem eventualTarget_of_normalizedPolynomialFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.generatedPoint.normalizedPolynomial F).eventualTarget C

theorem arbitraryTarget_of_normalizedPolynomialFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPoint.normalizedPolynomial F).arbitraryTarget C

theorem exactTarget_of_normalizedValueFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedPoint.normalizedValue F).exactTarget C

theorem eventualTarget_of_normalizedValueFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.generatedPoint.normalizedValue F).eventualTarget C

theorem arbitraryTarget_of_normalizedValueFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPoint.normalizedValue F).arbitraryTarget C

theorem exactTarget_of_lowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedPoint.lowerBound F).exactTarget C

theorem eventualTarget_of_lowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.generatedPoint.lowerBound F).eventualTarget C

theorem arbitraryTarget_of_lowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPoint.lowerBound F).arbitraryTarget C

theorem exactTarget_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.generatedPoint.finalConditionalFamily.exactTarget F

theorem eventualTarget_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.generatedPoint.finalConditionalFamily.eventualTarget F

theorem arbitraryTarget_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.generatedPoint.finalConditionalFamily.arbitraryTarget F

/-! ## Public generated cross-block projections -/

def toCrossBlockClosureLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    CrossBlockClosureLedger F :=
  (matrix.generatedCrossBlock F).toClosureLedger L

theorem separated_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    CrossBlockInequalityClosureW11.GeneratedGlobalSeparationAt F k hk :=
  (matrix.generatedCrossBlock F).separated L k hk

theorem exactBlockTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.generatedCrossBlock F).exactBlockTarget L k hk

theorem exactTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedCrossBlock F).directRoute.exactTarget L

theorem eventualTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.generatedCrossBlock F).directRoute.eventualTarget L

theorem arbitraryTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedCrossBlock F).directRoute.arbitraryTarget L

theorem exactTarget_viaClosure_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedCrossBlock F).closureRoute.exactTarget
    (toCrossBlockClosureLedger L)

theorem arbitraryTarget_viaClosure_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedCrossBlock F).closureRoute.arbitraryTarget
    (toCrossBlockClosureLedger L)

/-! ## Public integrated cross-block projections -/

theorem exactTarget_viaCrossBlockIntegrated_of_inequalityLedger
    {F : CrossBlockIntegratedFamily}
    (L : CrossBlockIntegratedInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.integratedCrossBlock.inequality F).exactTarget L

theorem eventualTarget_viaCrossBlockIntegrated_of_inequalityLedger
    {F : CrossBlockIntegratedFamily}
    (L : CrossBlockIntegratedInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.integratedCrossBlock.inequality F).eventualTarget L

theorem arbitraryTarget_viaCrossBlockIntegrated_of_inequalityLedger
    {F : CrossBlockIntegratedFamily}
    (L : CrossBlockIntegratedInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.integratedCrossBlock.inequality F).arbitraryTarget L

theorem exactTarget_viaArbitraryNIntegrated_of_rawInequalityLedger
    {F : ArbitraryNCrossBlockFamily}
    (L : ArbitraryNCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.arbitraryNCrossBlock.rawInequality F).exactTarget L

theorem eventualTarget_viaArbitraryNIntegrated_of_rawInequalityLedger
    {F : ArbitraryNCrossBlockFamily}
    (L : ArbitraryNCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.arbitraryNCrossBlock.rawInequality F).eventualTarget L

theorem arbitraryTarget_viaArbitraryNIntegrated_of_rawInequalityLedger
    {F : ArbitraryNCrossBlockFamily}
    (L : ArbitraryNCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.arbitraryNCrossBlock.rawInequality F).arbitraryTarget L

/-! ## Public broad W11 projections -/

theorem exactTarget_viaBroadW11_of_lowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.broadIntegrated.generatedPointLowerBound F).exactTarget C

theorem eventualTarget_viaBroadW11_of_lowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.broadIntegrated.generatedPointLowerBound F).eventualTarget C

theorem arbitraryTarget_viaBroadW11_of_lowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.broadIntegrated.generatedPointLowerBound F).arbitraryTarget C

theorem exactTarget_viaBroadW11_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.broadIntegrated.crossBlockClosure F).exactTarget C

theorem eventualTarget_viaBroadW11_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.broadIntegrated.crossBlockClosure F).eventualTarget C

theorem arbitraryTarget_viaBroadW11_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.broadIntegrated.crossBlockClosure F).arbitraryTarget C

/-! ## Imported blockers -/

theorem transition_concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.concreteFourTargetRouteClaim

theorem transition_concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.completedFilteredRoute

end

end GeneratedFinalIntegratedW11
end PachToth
end ErdosProblems1066
