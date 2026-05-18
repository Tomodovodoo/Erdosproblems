import ErdosProblems1066.PachToth.GeneratedCrossBlockSummaryFinalW11
import ErdosProblems1066.PachToth.GeneratedCrossBlockFinalW11
import ErdosProblems1066.PachToth.CrossBlockTargetFinalW11
import ErdosProblems1066.PachToth.CrossBlockFinalIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate

set_option autoImplicit false

/-!
# W11 generated/cross-block terminal route summary

This leaf summary records the checked generated and cross-block ledgers,
keeps the numeric block scales as fields, and exposes target conclusions only
as projections from caller-supplied packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedCrossBlockTerminalSummaryW11

noncomputable section

universe u

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev TargetFacade :=
  CrossBlockTargetFinalW11.ArbitraryNTargetFacade

abbrev GeneratedPointFamily :=
  GeneratedCrossBlockSummaryFinalW11.GeneratedPointFamily

abbrev GeneratedPointNormalizedPolynomialFields
    (F : GeneratedPointFamily) :=
  GeneratedCrossBlockSummaryFinalW11.GeneratedPointNormalizedPolynomialFields F

abbrev GeneratedPointNormalizedValueFields
    (F : GeneratedPointFamily) :=
  GeneratedCrossBlockSummaryFinalW11.GeneratedPointNormalizedValueFields F

abbrev GeneratedPointLowerBoundFields
    (F : GeneratedPointFamily) :=
  GeneratedCrossBlockSummaryFinalW11.GeneratedPointLowerBoundFields F

abbrev GeneratedCrossBlockFamily :=
  GeneratedCrossBlockSummaryFinalW11.GeneratedCrossBlockFamily

abbrev GeneratedCrossBlockInequalityLedger
    (F : GeneratedCrossBlockFamily) :=
  GeneratedCrossBlockSummaryFinalW11.GeneratedCrossBlockInequalityLedger F

abbrev GeneratedCrossBlockClosureLedger
    (F : GeneratedCrossBlockFamily) :=
  GeneratedCrossBlockSummaryFinalW11.GeneratedCrossBlockClosureLedger F

abbrev CrossBlockFamily :=
  GeneratedCrossBlockSummaryFinalW11.CrossBlockFamily

abbrev RoleHingeCrossBlockFamily :=
  GeneratedCrossBlockSummaryFinalW11.RoleHingeCrossBlockFamily

abbrev PolynomialRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedCrossBlockSummaryFinalW11.PolynomialRows F k hk

abbrev PolynomialRowFamilies (F : CrossBlockFamily) :=
  GeneratedCrossBlockSummaryFinalW11.PolynomialRowFamilies F

abbrev ValueRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedCrossBlockSummaryFinalW11.ValueRows F k hk

abbrev ValueRowFamilies (F : CrossBlockFamily) :=
  GeneratedCrossBlockSummaryFinalW11.ValueRowFamilies F

abbrev CrossBlockInequalityLedger (F : CrossBlockFamily) :=
  GeneratedCrossBlockSummaryFinalW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger (F : CrossBlockFamily) :=
  GeneratedCrossBlockSummaryFinalW11.CrossBlockClosureLedger F

abbrev RoleHingeCrossBlockInequalityPackage
    (F : RoleHingeCrossBlockFamily) :=
  GeneratedCrossBlockSummaryFinalW11.RoleHingeCrossBlockInequalityPackage F

abbrev CrossBlockSeparationAt
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) : Prop :=
  CrossBlockTargetFinalW11.GeneratedGlobalSeparationAt F k hk

/-! ## Checked ledgers -/

/-- Checked W11 ledgers summarized by this terminal leaf. -/
structure CheckedLedgers where
  generatedCrossBlockSummary : GeneratedCrossBlockSummaryFinalW11.Matrix
  generatedCrossBlockFinal : GeneratedCrossBlockFinalW11.Matrix
  crossBlockTargetFinal : CrossBlockTargetFinalW11.Matrix
  crossBlockFinalIntegrated : CrossBlockFinalIntegratedW11.Matrix
  pachTothFinalAggregate : PachTothW11FinalAggregate.Matrix

/-- Imported checked ledgers. -/
def checkedLedgers : CheckedLedgers where
  generatedCrossBlockSummary := GeneratedCrossBlockSummaryFinalW11.matrix
  generatedCrossBlockFinal := GeneratedCrossBlockFinalW11.matrix
  crossBlockTargetFinal := CrossBlockTargetFinalW11.matrix
  crossBlockFinalIntegrated := CrossBlockFinalIntegratedW11.matrix
  pachTothFinalAggregate := PachTothW11FinalAggregate.matrix

/-! ## Explicit numeric fields -/

/-- Numeric block-scale fields retained at the terminal summary layer. -/
structure NumericFields where
  generatedBlockScale : Nat
  generatedBlockScale_eq : generatedBlockScale = 16
  generatedCrossBlockInequalityTarget :
    forall {F : GeneratedCrossBlockFamily},
      GeneratedCrossBlockInequalityLedger F -> forall k : Nat, 0 < k ->
        FixedTarget (generatedBlockScale * k)
  crossBlockScale : Nat
  crossBlockScale_eq : crossBlockScale = 16
  polynomialRows :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      PolynomialRows F k hk -> FixedTarget (crossBlockScale * k)
  valueRows :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      ValueRows F k hk -> FixedTarget (crossBlockScale * k)
  inequalityLedgers :
    forall {F : CrossBlockFamily},
      CrossBlockInequalityLedger F -> forall k : Nat, 0 < k ->
        FixedTarget (crossBlockScale * k)
  closureLedgers :
    forall {F : CrossBlockFamily},
      CrossBlockClosureLedger F -> forall k : Nat, 0 < k ->
        FixedTarget (crossBlockScale * k)
  inequalitySeparation :
    forall {F : CrossBlockFamily},
      CrossBlockInequalityLedger F -> forall k : Nat, forall hk : 0 < k,
        CrossBlockSeparationAt F k hk
  closureSeparation :
    forall {F : CrossBlockFamily},
      CrossBlockClosureLedger F -> forall k : Nat, forall hk : 0 < k,
        CrossBlockSeparationAt F k hk

/-- Checked numeric block-scale fields. -/
def numericFields : NumericFields where
  generatedBlockScale := 16
  generatedBlockScale_eq := rfl
  generatedCrossBlockInequalityTarget := fun L k hk => by
    simpa using
      GeneratedCrossBlockSummaryFinalW11.targetAt_generatedCrossBlockInequalityLedger
        L k hk
  crossBlockScale := 16
  crossBlockScale_eq := rfl
  polynomialRows := fun hk R => by
    simpa using
      CrossBlockTargetFinalW11.targetAt_of_polynomialRows (hk := hk) R
  valueRows := fun hk R => by
    simpa using
      CrossBlockTargetFinalW11.targetAt_of_valueRows (hk := hk) R
  inequalityLedgers := fun L k hk => by
    simpa using
      CrossBlockTargetFinalW11.targetAt_of_crossBlockInequalityLedger L k hk
  closureLedgers := fun C k hk => by
    simpa using
      CrossBlockTargetFinalW11.targetAt_of_crossBlockClosureLedger C k hk
  inequalitySeparation := fun L k hk =>
    CrossBlockTargetFinalW11.separated_of_crossBlockInequalityLedger L k hk
  closureSeparation := fun C k hk =>
    CrossBlockTargetFinalW11.separated_of_crossBlockClosureLedger C k hk

/-! ## Conditional projection rows -/

/-- Exact, eventual, and arbitrary target projections from one package. -/
structure ConditionalProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

namespace ConditionalProjection

def ofSummary
    {alpha : Sort u}
    (R : GeneratedCrossBlockSummaryFinalW11.ConditionalProjection alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end ConditionalProjection

/-- Exact, fixed, eventual, arbitrary, and facade projections from one
cross-block package. -/
structure FacadeProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget
  targetFacade : alpha -> TargetFacade

namespace FacadeProjection

def ofCrossBlockTarget
    {alpha : Sort u}
    (R : CrossBlockTargetFinalW11.ConditionalProjectionRoute alpha) :
    FacadeProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

end FacadeProjection

/-- Generated-point and generated cross-block package projections. -/
structure GeneratedRoutes where
  normalizedPolynomial :
    forall F : GeneratedPointFamily,
      ConditionalProjection (GeneratedPointNormalizedPolynomialFields F)
  normalizedValue :
    forall F : GeneratedPointFamily,
      ConditionalProjection (GeneratedPointNormalizedValueFields F)
  lowerBound :
    forall F : GeneratedPointFamily,
      ConditionalProjection (GeneratedPointLowerBoundFields F)
  crossBlockInequality :
    forall F : GeneratedCrossBlockFamily,
      ConditionalProjection (GeneratedCrossBlockInequalityLedger F)
  crossBlockClosure :
    forall F : GeneratedCrossBlockFamily,
      ConditionalProjection (GeneratedCrossBlockClosureLedger F)

/-- Checked generated package projections. -/
def generatedRoutes : GeneratedRoutes where
  normalizedPolynomial := fun F =>
    ConditionalProjection.ofSummary
      (GeneratedCrossBlockSummaryFinalW11.matrix.generated
        |>.normalizedPolynomial F)
  normalizedValue := fun F =>
    ConditionalProjection.ofSummary
      (GeneratedCrossBlockSummaryFinalW11.matrix.generated.normalizedValue F)
  lowerBound := fun F =>
    ConditionalProjection.ofSummary
      (GeneratedCrossBlockSummaryFinalW11.matrix.generated.lowerBound F)
  crossBlockInequality := fun F =>
    ConditionalProjection.ofSummary
      (GeneratedCrossBlockSummaryFinalW11.matrix.generated
        |>.crossBlockInequality F)
  crossBlockClosure := fun F =>
    ConditionalProjection.ofSummary
      (GeneratedCrossBlockSummaryFinalW11.matrix.generated
        |>.crossBlockClosure F)

/-- Cross-block package projections through the target-final facade. -/
structure CrossBlockRoutes where
  polynomialRowFamilies :
    forall F : CrossBlockFamily,
      FacadeProjection (PolynomialRowFamilies F)
  valueRowFamilies :
    forall F : CrossBlockFamily,
      FacadeProjection (ValueRowFamilies F)
  inequalityLedgers :
    forall F : CrossBlockFamily,
      FacadeProjection (CrossBlockInequalityLedger F)
  closureLedgers :
    forall F : CrossBlockFamily,
      FacadeProjection (CrossBlockClosureLedger F)
  roleHingeInequalityPackages :
    forall F : RoleHingeCrossBlockFamily,
      FacadeProjection (RoleHingeCrossBlockInequalityPackage F)

/-- Checked cross-block package projections through the target-final facade. -/
def crossBlockRoutes : CrossBlockRoutes where
  polynomialRowFamilies := fun F =>
    FacadeProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.polynomial.rowFamilies F)
  valueRowFamilies := fun F =>
    FacadeProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.value.rowFamilies F)
  inequalityLedgers := fun F =>
    FacadeProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.ledger.inequalityLedgers F)
  closureLedgers := fun F =>
    FacadeProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.ledger.closureLedgers F)
  roleHingeInequalityPackages := fun F =>
    FacadeProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.ledger.roleHingeInequalityPackages F)

/-- Terminal aggregate projections retained for comparison with the broad
Pach--Toth aggregate. -/
structure AggregateRoutes where
  generatedLowerBound :
    forall F : GeneratedPointFamily,
      GeneratedPointLowerBoundFields F -> ArbitraryTarget
  generatedCrossBlockInequality :
    forall F : GeneratedCrossBlockFamily,
      GeneratedCrossBlockInequalityLedger F -> ArbitraryTarget
  crossBlockPolynomialRows :
    forall {F : CrossBlockFamily} {k : Nat} {hk : 0 < k},
      PolynomialRows F k hk -> FixedTarget (16 * k)
  crossBlockClosure :
    forall F : CrossBlockFamily,
      CrossBlockClosureLedger F -> ArbitraryTarget

/-- Checked terminal aggregate projections. -/
def aggregateRoutes : AggregateRoutes where
  generatedLowerBound := fun _F C =>
    PachTothW11FinalAggregate.arbitraryTarget_of_generatedPointLowerBoundFields
      C
  generatedCrossBlockInequality := fun _F L =>
    PachTothW11FinalAggregate.arbitraryTarget_of_generatedCrossBlockInequalityLedger
      L
  crossBlockPolynomialRows := fun R =>
    PachTothW11FinalAggregate.fixedTarget_of_crossBlockPolynomialRows R
  crossBlockClosure := fun _F C =>
    PachTothW11FinalAggregate.arbitraryTarget_of_crossBlockClosureLedger C

/-! ## Terminal matrix -/

/-- Terminal generated/cross-block route summary matrix. -/
structure Matrix where
  checked : CheckedLedgers
  numeric : NumericFields
  generated : GeneratedRoutes
  crossBlock : CrossBlockRoutes
  aggregate : AggregateRoutes

/-- The checked terminal generated/cross-block route summary. -/
def matrix : Matrix where
  checked := checkedLedgers
  numeric := numericFields
  generated := generatedRoutes
  crossBlock := crossBlockRoutes
  aggregate := aggregateRoutes

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

theorem checked_summary :
    matrix.checked.generatedCrossBlockSummary =
      GeneratedCrossBlockSummaryFinalW11.matrix :=
  rfl

theorem checked_generatedCrossBlockFinal :
    matrix.checked.generatedCrossBlockFinal =
      GeneratedCrossBlockFinalW11.matrix :=
  rfl

theorem checked_crossBlockTargetFinal :
    matrix.checked.crossBlockTargetFinal =
      CrossBlockTargetFinalW11.matrix :=
  rfl

theorem checked_crossBlockFinalIntegrated :
    matrix.checked.crossBlockFinalIntegrated =
      CrossBlockFinalIntegratedW11.matrix :=
  rfl

theorem checked_pachTothFinalAggregate :
    matrix.checked.pachTothFinalAggregate =
      PachTothW11FinalAggregate.matrix :=
  rfl

/-! ## Public numeric projections -/

theorem generatedBlockScale_eq_sixteen :
    matrix.numeric.generatedBlockScale = 16 :=
  matrix.numeric.generatedBlockScale_eq

theorem crossBlockScale_eq_sixteen :
    matrix.numeric.crossBlockScale = 16 :=
  matrix.numeric.crossBlockScale_eq

theorem targetAt_generatedCrossBlockInequalityLedger
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    FixedTarget (matrix.numeric.generatedBlockScale * k) :=
  matrix.numeric.generatedCrossBlockInequalityTarget L k hk

theorem targetAt_crossBlockPolynomialRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : PolynomialRows F k hk) :
    FixedTarget (matrix.numeric.crossBlockScale * k) :=
  matrix.numeric.polynomialRows hk R

theorem targetAt_crossBlockValueRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : ValueRows F k hk) :
    FixedTarget (matrix.numeric.crossBlockScale * k) :=
  matrix.numeric.valueRows hk R

theorem targetAt_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    FixedTarget (matrix.numeric.crossBlockScale * k) :=
  matrix.numeric.inequalityLedgers L k hk

theorem targetAt_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    FixedTarget (matrix.numeric.crossBlockScale * k) :=
  matrix.numeric.closureLedgers C k hk

theorem separated_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    CrossBlockSeparationAt F k hk :=
  matrix.numeric.inequalitySeparation L k hk

theorem separated_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    CrossBlockSeparationAt F k hk :=
  matrix.numeric.closureSeparation C k hk

/-! ## Public generated projections -/

theorem exactTarget_of_generatedLowerBound
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ExactTarget :=
  (matrix.generated.lowerBound F).exactTarget C

theorem eventualTarget_of_generatedLowerBound
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    EventualTarget :=
  (matrix.generated.lowerBound F).eventualTarget C

theorem arbitraryTarget_of_generatedLowerBound
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.generated.lowerBound F).arbitraryTarget C

theorem arbitraryTarget_of_generatedLowerBound_viaAggregate
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  matrix.aggregate.generatedLowerBound F C

theorem exactTarget_of_generatedCrossBlockInequalityLedger
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F) :
    ExactTarget :=
  (matrix.generated.crossBlockInequality F).exactTarget L

theorem arbitraryTarget_of_generatedCrossBlockInequalityLedger
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.generated.crossBlockInequality F).arbitraryTarget L

theorem arbitraryTarget_of_generatedCrossBlockInequalityLedger_viaAggregate
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  matrix.aggregate.generatedCrossBlockInequality F L

theorem exactTarget_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    ExactTarget :=
  (matrix.generated.crossBlockClosure F).exactTarget C

theorem eventualTarget_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    EventualTarget :=
  (matrix.generated.crossBlockClosure F).eventualTarget C

theorem arbitraryTarget_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.generated.crossBlockClosure F).arbitraryTarget C

/-! ## Public cross-block projections -/

theorem fixedTarget_of_crossBlockPolynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) (n : Nat) :
    FixedTarget n :=
  (matrix.crossBlock.polynomialRowFamilies F).fixedTarget R n

theorem arbitraryTarget_of_crossBlockPolynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    ArbitraryTarget :=
  (matrix.crossBlock.polynomialRowFamilies F).arbitraryTarget R

theorem targetFacade_of_crossBlockPolynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    TargetFacade :=
  (matrix.crossBlock.polynomialRowFamilies F).targetFacade R

theorem fixedTarget_of_crossBlockValueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) (n : Nat) :
    FixedTarget n :=
  (matrix.crossBlock.valueRowFamilies F).fixedTarget R n

theorem arbitraryTarget_of_crossBlockValueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) :
    ArbitraryTarget :=
  (matrix.crossBlock.valueRowFamilies F).arbitraryTarget R

theorem targetFacade_of_crossBlockValueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) :
    TargetFacade :=
  (matrix.crossBlock.valueRowFamilies F).targetFacade R

theorem fixedTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) (n : Nat) :
    FixedTarget n :=
  (matrix.crossBlock.inequalityLedgers F).fixedTarget L n

theorem arbitraryTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlock.inequalityLedgers F).arbitraryTarget L

theorem targetFacade_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    TargetFacade :=
  (matrix.crossBlock.inequalityLedgers F).targetFacade L

theorem fixedTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) (n : Nat) :
    FixedTarget n :=
  (matrix.crossBlock.closureLedgers F).fixedTarget C n

theorem exactTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ExactTarget :=
  (matrix.crossBlock.closureLedgers F).exactTarget C

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlock.closureLedgers F).arbitraryTarget C

theorem targetFacade_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    TargetFacade :=
  (matrix.crossBlock.closureLedgers F).targetFacade C

theorem arbitraryTarget_of_roleHingeInequalityPackage
    {F : RoleHingeCrossBlockFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    ArbitraryTarget :=
  (matrix.crossBlock.roleHingeInequalityPackages F).arbitraryTarget R

/-! ## Public terminal aggregate projections -/

theorem targetAt_viaAggregate_of_crossBlockPolynomialRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : PolynomialRows F k hk) :
    FixedTarget (16 * k) :=
  matrix.aggregate.crossBlockPolynomialRows R

theorem arbitraryTarget_viaAggregate_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.aggregate.crossBlockClosure F C

end

end GeneratedCrossBlockTerminalSummaryW11
end PachToth
end ErdosProblems1066
