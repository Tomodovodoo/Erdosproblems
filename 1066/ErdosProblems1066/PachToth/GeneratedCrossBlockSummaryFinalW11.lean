import ErdosProblems1066.PachToth.GeneratedCrossBlockFinalW11
import ErdosProblems1066.PachToth.GeneratedTargetFinalW11
import ErdosProblems1066.PachToth.CrossBlockFinalIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockTargetFinalW11
import ErdosProblems1066.PachToth.ArbitraryNFinalAggregateW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate

set_option autoImplicit false

/-!
# W11 generated/cross-block route summary

This leaf module summarizes the checked generated and cross-block final
routes.  Numeric block sizes are retained as fields, and every target-facing
projection below remains indexed by an explicit source package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedCrossBlockSummaryFinalW11

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

abbrev GeneratedPointFamily :=
  GeneratedCrossBlockFinalW11.GeneratedPointFamily

abbrev GeneratedPointNormalizedPolynomialFields
    (F : GeneratedPointFamily) :=
  GeneratedCrossBlockFinalW11.GeneratedPointNormalizedPolynomialFields F

abbrev GeneratedPointNormalizedValueFields
    (F : GeneratedPointFamily) :=
  GeneratedCrossBlockFinalW11.GeneratedPointNormalizedValueFields F

abbrev GeneratedPointLowerBoundFields
    (F : GeneratedPointFamily) :=
  GeneratedCrossBlockFinalW11.GeneratedPointLowerBoundFields F

abbrev GeneratedCrossBlockFamily :=
  GeneratedCrossBlockFinalW11.GeneratedCrossBlockFamily

abbrev GeneratedCrossBlockInequalityLedger
    (F : GeneratedCrossBlockFamily) :=
  GeneratedCrossBlockFinalW11.GeneratedCrossBlockInequalityLedger F

abbrev GeneratedCrossBlockClosureLedger
    (F : GeneratedCrossBlockFamily) :=
  GeneratedCrossBlockFinalW11.GeneratedCrossBlockClosureLedger F

abbrev CrossBlockFamily :=
  GeneratedCrossBlockFinalW11.CrossBlockFamily

abbrev RoleHingeCrossBlockFamily :=
  GeneratedCrossBlockFinalW11.RoleHingeCrossBlockFamily

abbrev PolynomialRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedCrossBlockFinalW11.PolynomialRows F k hk

abbrev PolynomialRowFamilies (F : CrossBlockFamily) :=
  GeneratedCrossBlockFinalW11.PolynomialRowFamilies F

abbrev ValueRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedCrossBlockFinalW11.ValueRows F k hk

abbrev ValueRowFamilies (F : CrossBlockFamily) :=
  GeneratedCrossBlockFinalW11.ValueRowFamilies F

abbrev CrossBlockInequalityLedger (F : CrossBlockFamily) :=
  GeneratedCrossBlockFinalW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger (F : CrossBlockFamily) :=
  GeneratedCrossBlockFinalW11.CrossBlockClosureLedger F

abbrev RoleHingeCrossBlockInequalityPackage
    (F : RoleHingeCrossBlockFamily) :=
  GeneratedCrossBlockFinalW11.RoleHingeCrossBlockInequalityPackage F

/-! ## Checked ledgers -/

/-- Checked W11 ledgers used by this summary. -/
structure CheckedLedgers where
  generatedCrossBlockFinal : GeneratedCrossBlockFinalW11.Matrix
  generatedTargetFinal : GeneratedTargetFinalW11.Matrix
  crossBlockFinal : CrossBlockFinalIntegratedW11.Matrix
  crossBlockTargetFinal : CrossBlockTargetFinalW11.Matrix
  arbitraryNFinalAggregate : ArbitraryNFinalAggregateW11.Matrix
  pachTothFinalAggregate : PachTothW11FinalAggregate.Matrix

/-- Imported checked ledgers. -/
def checkedLedgers : CheckedLedgers where
  generatedCrossBlockFinal := GeneratedCrossBlockFinalW11.matrix
  generatedTargetFinal := GeneratedTargetFinalW11.matrix
  crossBlockFinal := CrossBlockFinalIntegratedW11.matrix
  crossBlockTargetFinal := CrossBlockTargetFinalW11.matrix
  arbitraryNFinalAggregate := ArbitraryNFinalAggregateW11.matrix
  pachTothFinalAggregate := PachTothW11FinalAggregate.matrix

/-! ## Numeric block fields -/

/-- Numeric block fields retained by the summary. -/
structure NumericFieldSummary where
  generatedBlockScale : Nat
  generatedBlockScale_eq : generatedBlockScale = 16
  generatedInequalityBlocks :
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

/-- Checked numeric block fields. -/
def numericFieldSummary : NumericFieldSummary where
  generatedBlockScale := 16
  generatedBlockScale_eq := rfl
  generatedInequalityBlocks := fun L k hk => by
    simpa using
      GeneratedCrossBlockFinalW11.targetAt_generatedCrossBlockInequalityLedger
        L k hk
  crossBlockScale := 16
  crossBlockScale_eq := rfl
  polynomialRows := fun hk R => by
    simpa using
      GeneratedCrossBlockFinalW11.targetAt_crossBlockPolynomialRows
        (hk := hk) R
  valueRows := fun hk R => by
    simpa using
      GeneratedCrossBlockFinalW11.matrix.numeric.valueRows hk R
  inequalityLedgers := fun L k hk => by
    simpa using
      GeneratedCrossBlockFinalW11.targetAt_crossBlockInequalityLedger
        L k hk
  closureLedgers := fun C k hk => by
    simpa using
      GeneratedCrossBlockFinalW11.targetAt_crossBlockClosureLedger
        C k hk

/-! ## Route fields -/

/-- Exact, eventual, and arbitrary projections from an explicit package. -/
structure ConditionalProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Exact, fixed, eventual, and arbitrary projections from an explicit
package. -/
structure FixedConditionalProjection (alpha : Sort u) :
    Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

namespace ConditionalProjection

def ofGenerated
    {alpha : Sort u}
    (R : GeneratedCrossBlockFinalW11.ConditionalRoute alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end ConditionalProjection

namespace FixedConditionalProjection

def ofCrossBlock
    {alpha : Sort u}
    (R : GeneratedCrossBlockFinalW11.FixedConditionalRoute alpha) :
    FixedConditionalProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end FixedConditionalProjection

/-- Generated-point and generated cross-block route fields. -/
structure GeneratedProjectionSummary where
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

/-- Checked generated route fields. -/
def generatedProjectionSummary : GeneratedProjectionSummary where
  normalizedPolynomial := fun F =>
    ConditionalProjection.ofGenerated
      (GeneratedCrossBlockFinalW11.matrix.generated.normalizedPolynomial F)
  normalizedValue := fun F =>
    ConditionalProjection.ofGenerated
      (GeneratedCrossBlockFinalW11.matrix.generated.normalizedValue F)
  lowerBound := fun F =>
    ConditionalProjection.ofGenerated
      (GeneratedCrossBlockFinalW11.matrix.generated.lowerBound F)
  crossBlockInequality := fun F =>
    ConditionalProjection.ofGenerated
      (GeneratedCrossBlockFinalW11.matrix.generated.crossBlockInequality F)
  crossBlockClosure := fun F =>
    ConditionalProjection.ofGenerated
      (GeneratedCrossBlockFinalW11.matrix.generated.crossBlockClosure F)

/-- Cross-block route fields. -/
structure CrossBlockProjectionSummary where
  polynomialRowFamilies :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (PolynomialRowFamilies F)
  valueRowFamilies :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (ValueRowFamilies F)
  inequalityLedgers :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (CrossBlockInequalityLedger F)
  closureLedgers :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (CrossBlockClosureLedger F)
  roleHingeInequalityPackages :
    forall F : RoleHingeCrossBlockFamily,
      FixedConditionalProjection (RoleHingeCrossBlockInequalityPackage F)

/-- Checked cross-block route fields. -/
def crossBlockProjectionSummary : CrossBlockProjectionSummary where
  polynomialRowFamilies := fun F =>
    FixedConditionalProjection.ofCrossBlock
      (GeneratedCrossBlockFinalW11.matrix.crossBlock.polynomialRowFamilies F)
  valueRowFamilies := fun F =>
    FixedConditionalProjection.ofCrossBlock
      (GeneratedCrossBlockFinalW11.matrix.crossBlock.valueRowFamilies F)
  inequalityLedgers := fun F =>
    FixedConditionalProjection.ofCrossBlock
      (GeneratedCrossBlockFinalW11.matrix.crossBlock.inequalityLedgers F)
  closureLedgers := fun F =>
    FixedConditionalProjection.ofCrossBlock
      (GeneratedCrossBlockFinalW11.matrix.crossBlock.closureLedgers F)
  roleHingeInequalityPackages := fun F =>
    FixedConditionalProjection.ofCrossBlock
      (GeneratedCrossBlockFinalW11.matrix.crossBlock.roleHingeInequalityPackages
        F)

/-- Aggregate route fields imported for cross-layer comparison. -/
structure AggregateProjectionSummary where
  arbitraryNGeneratedLowerBound :
    forall F : GeneratedPointFamily,
      GeneratedPointLowerBoundFields F -> ArbitraryTarget
  arbitraryNGeneratedCrossBlockClosure :
    forall F : GeneratedCrossBlockFamily,
      GeneratedCrossBlockClosureLedger F -> ArbitraryTarget
  arbitraryNCrossBlockClosure :
    forall F : CrossBlockFamily,
      CrossBlockClosureLedger F -> ArbitraryTarget
  pachTothCrossBlockPolynomialRows :
    forall {F : CrossBlockFamily} {k : Nat} {hk : 0 < k},
      PolynomialRows F k hk -> FixedTarget (16 * k)
  pachTothCrossBlockClosure :
    forall F : CrossBlockFamily,
      CrossBlockClosureLedger F -> ArbitraryTarget

/-- Checked aggregate route fields. -/
def aggregateProjectionSummary : AggregateProjectionSummary where
  arbitraryNGeneratedLowerBound := fun _F C =>
    ArbitraryNFinalAggregateW11.arbitraryTarget_of_generatedLowerBound C
  arbitraryNGeneratedCrossBlockClosure := fun _F C =>
    ArbitraryNFinalAggregateW11.arbitraryTarget_of_generatedCrossBlockClosureLedger
      C
  arbitraryNCrossBlockClosure := fun _F C =>
    ArbitraryNFinalAggregateW11.arbitraryTarget_of_crossBlockClosureLedger C
  pachTothCrossBlockPolynomialRows := fun R =>
    PachTothW11FinalAggregate.fixedTarget_of_crossBlockPolynomialRows R
  pachTothCrossBlockClosure := fun _F C =>
    PachTothW11FinalAggregate.arbitraryTarget_of_crossBlockClosureLedger C

/-! ## Summary matrix -/

/-- Final generated/cross-block route summary matrix. -/
structure Matrix where
  checked : CheckedLedgers
  numeric : NumericFieldSummary
  generated : GeneratedProjectionSummary
  crossBlock : CrossBlockProjectionSummary
  aggregate : AggregateProjectionSummary
  blockers : GeneratedTargetIntegratedW11.TransitionBlockers

/-- The checked final generated/cross-block route summary. -/
def matrix : Matrix where
  checked := checkedLedgers
  numeric := numericFieldSummary
  generated := generatedProjectionSummary
  crossBlock := crossBlockProjectionSummary
  aggregate := aggregateProjectionSummary
  blockers := GeneratedCrossBlockFinalW11.matrix.blockers

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

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
  matrix.numeric.generatedInequalityBlocks L k hk

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

theorem exactTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ExactTarget :=
  (matrix.crossBlock.inequalityLedgers F).exactTarget L

theorem fixedTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) (n : Nat) :
    FixedTarget n :=
  (matrix.crossBlock.inequalityLedgers F).fixedTarget L n

theorem eventualTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    EventualTarget :=
  (matrix.crossBlock.inequalityLedgers F).eventualTarget L

theorem arbitraryTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlock.inequalityLedgers F).arbitraryTarget L

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

theorem arbitraryTarget_of_roleHingeInequalityPackage
    {F : RoleHingeCrossBlockFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    ArbitraryTarget :=
  (matrix.crossBlock.roleHingeInequalityPackages F).arbitraryTarget R

/-! ## Public aggregate projections -/

theorem arbitraryTarget_viaArbitraryN_of_generatedLowerBound
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  matrix.aggregate.arbitraryNGeneratedLowerBound F C

theorem arbitraryTarget_viaArbitraryN_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.aggregate.arbitraryNGeneratedCrossBlockClosure F C

theorem arbitraryTarget_viaArbitraryN_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.aggregate.arbitraryNCrossBlockClosure F C

theorem targetAt_viaPachTothAggregate_of_crossBlockPolynomialRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : PolynomialRows F k hk) :
    FixedTarget (16 * k) :=
  matrix.aggregate.pachTothCrossBlockPolynomialRows R

theorem arbitraryTarget_viaPachTothAggregate_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.aggregate.pachTothCrossBlockClosure F C

/-! ## Public blocker projections -/

theorem transition_concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.concreteFourTargetRouteClaim

theorem transition_concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.completedFilteredRoute

theorem transition_concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.fullSameRestShortcut

end

end GeneratedCrossBlockSummaryFinalW11
end PachToth
end ErdosProblems1066
