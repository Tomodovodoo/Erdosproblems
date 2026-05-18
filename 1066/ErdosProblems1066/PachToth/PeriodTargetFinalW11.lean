import ErdosProblems1066.PachToth.PeriodFinalIntegratedW11
import ErdosProblems1066.PachToth.PeriodTargetIntegratedW11
import ErdosProblems1066.PachToth.TransitionPeriodFinalW11
import ErdosProblems1066.PachToth.ArbitraryNTargetFinalW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate

set_option autoImplicit false

/-!
# Final W11 period target consistency layer

This module is the target-facing endpoint for the W11 period route.  It keeps
the checked word, separated family, explicit lower-bound, and exact-candidate
packages visible, then exposes only package-indexed target projections.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodTargetFinalW11

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

abbrev Candidate :=
  PeriodTargetIntegratedW11.Candidate

abbrev BaseWordSeparationFields (T : Candidate) :=
  PeriodTargetIntegratedW11.CheckedWordSeparationFields T

abbrev BaseSeparatedFamilyFields (T : Candidate) :=
  PeriodTargetIntegratedW11.GeneratedFamilyRemainingFields T

abbrev BaseLowerBoundFields (T : Candidate) :=
  PeriodTargetIntegratedW11.ExplicitLowerBoundClosureFields T

abbrev BaseExactCandidateFields (T : Candidate) :=
  PeriodTargetIntegratedW11.ExactCandidatePeriodFields T

abbrev WordSeparationFields (T : Candidate) :=
  PeriodFinalIntegratedW11.WordSeparationFields T

abbrev SeparatedFamilyFields (T : Candidate) :=
  PeriodFinalIntegratedW11.SeparatedFamilyFields T

abbrev LowerBoundFields (T : Candidate) :=
  PeriodFinalIntegratedW11.LowerBoundFields T

abbrev ExactCandidateFields (T : Candidate) :=
  PeriodFinalIntegratedW11.ExactCandidateFields T

abbrev AggregateFields (T : Candidate) :=
  PeriodFinalIntegratedW11.AggregateFields T

abbrev TransitionPeriodRoutePackage :=
  TransitionPeriodFinalW11.RoutePackage

abbrev TransitionPeriodPeriodPackage :=
  TransitionPeriodFinalW11.PeriodPackage

abbrev TransitionPeriodBlockPackage :=
  TransitionPeriodFinalW11.PeriodBlockPackage

abbrev ArbitraryNExactTargetAssumptions :=
  ArbitraryNTargetFinalW11.ExactTargetAssumptions

abbrev ArbitraryNExactClosedChainPackage :=
  ArbitraryNTargetFinalW11.ExactClosedChainPackage

abbrev ArbitraryNEventualClosedChainPackage :=
  ArbitraryNTargetFinalW11.EventualClosedChainPackage

/-! ## Shared route shapes -/

/-- Exact, eventual, and arbitrary target projections from one displayed
package. -/
structure TargetProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

namespace TargetProjection

def ofPeriodTargetRoute
    {alpha : Sort u}
    (R : PeriodTargetIntegratedW11.TargetRoute alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofPeriodFinalRoute
    {alpha : Sort u}
    (R : PeriodFinalIntegratedW11.TargetRoute alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofTransitionPeriodRow
    {alpha : Type}
    (R : TransitionPeriodFinalW11.TargetRow alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofArbitraryNExactRoute
    {alpha : Sort u}
    (R : ArbitraryNTargetFinalW11.ExactTargetRoute alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end TargetProjection

/-- Fixed-block target projection from one displayed package. -/
structure BlockProjection (alpha : Sort u) : Sort (max 1 u) where
  blockIndex : alpha -> Nat
  fixedBlockTarget :
    forall package : alpha, FixedTarget (16 * blockIndex package)

/-! ## Period package routes -/

/-- The checked period word route retains the word and its separation witness. -/
structure WordSeparationRoute (T : Candidate) where
  length : WordSeparationFields T -> Nat
  positiveLength : forall D : WordSeparationFields T, 0 < length D
  word :
    forall D : WordSeparationFields T,
      OrientationWord.Word (length D)
  orientation :
    forall D : WordSeparationFields T,
      Fin (length D) -> PeriodEquationSearchW11.Orientation
  separated :
    forall D : WordSeparationFields T,
      PeriodFinalIntegratedW11.GeneratedGlobalSeparation
        T (positiveLength D) (orientation D)
  fixedBlockTarget :
    forall D : WordSeparationFields T, FixedTarget (16 * length D)

def wordSeparationRoute (T : Candidate) : WordSeparationRoute T where
  length := PeriodFinalIntegratedW11.WordSeparationFields.length
  positiveLength :=
    PeriodFinalIntegratedW11.WordSeparationFields.positiveLength
  word := PeriodFinalIntegratedW11.WordSeparationFields.word
  orientation := PeriodFinalIntegratedW11.WordSeparationFields.orientation
  separated :=
    PeriodFinalIntegratedW11.WordSeparationFields.separationWitness
  fixedBlockTarget :=
    PeriodFinalIntegratedW11.WordSeparationFields.exactBlockTarget

/-- Separated period families with exact-block and global target projections. -/
structure SeparatedFamilyRoute (T : Candidate) where
  word :
    SeparatedFamilyFields T -> forall k : Nat, 0 < k ->
      OrientationWord.Word k
  orientation :
    SeparatedFamilyFields T -> forall k : Nat, 0 < k ->
      Fin k -> PeriodEquationSearchW11.Orientation
  separated :
    forall D : SeparatedFamilyFields T, forall k : Nat, forall hk : 0 < k,
      PeriodFinalIntegratedW11.GeneratedGlobalSeparation
        T hk (orientation D k hk)
  fixedBlockTarget :
    SeparatedFamilyFields T -> forall k : Nat, 0 < k ->
      FixedTarget (16 * k)
  projection : TargetProjection (SeparatedFamilyFields T)

def separatedFamilyRoute (T : Candidate) : SeparatedFamilyRoute T where
  word := PeriodFinalIntegratedW11.SeparatedFamilyFields.word
  orientation := PeriodFinalIntegratedW11.SeparatedFamilyFields.orientation
  separated :=
    PeriodFinalIntegratedW11.SeparatedFamilyFields.separationWitness
  fixedBlockTarget :=
    PeriodFinalIntegratedW11.SeparatedFamilyFields.exactBlockTarget
  projection :=
    TargetProjection.ofPeriodFinalRoute
      (PeriodFinalIntegratedW11.matrix.separatedFamily T)

/-- Explicit lower-bound tables with their target projections. -/
structure LowerBoundRoute (T : Candidate) where
  orientation :
    LowerBoundFields T -> forall k : Nat, 0 < k ->
      Fin k -> PeriodEquationSearchW11.Orientation
  lower :
    LowerBoundFields T -> forall k : Nat, 0 < k ->
      Fin k -> FiniteGraph.LocalVertex ->
      Fin k -> FiniteGraph.LocalVertex -> Real
  lowerGeOne :
    forall D : LowerBoundFields T, forall k : Nat, forall hk : 0 < k,
      forall i : Fin k, forall u : FiniteGraph.LocalVertex,
      forall j : Fin k, forall v : FiniteGraph.LocalVertex,
        Ne i j -> 1 <= lower D k hk i u j v
  lowerBound :
    forall D : LowerBoundFields T, forall k : Nat, forall hk : 0 < k,
      forall i : Fin k, forall u : FiniteGraph.LocalVertex,
      forall j : Fin k, forall v : FiniteGraph.LocalVertex,
        Ne i j ->
          lower D k hk i u j v <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint
                T.toFigure2TransitionObligations
                hk
                BaseTransitionRealization.exactBase
                (orientation D k hk)
                i u)
              (GeneratedClosedChain.generatedPoint
                T.toFigure2TransitionObligations
                hk
                BaseTransitionRealization.exactBase
                (orientation D k hk)
                j v)
  fixedBlockTarget :
    LowerBoundFields T -> forall k : Nat, 0 < k -> FixedTarget (16 * k)
  projection : TargetProjection (LowerBoundFields T)

def lowerBoundRoute (T : Candidate) : LowerBoundRoute T where
  orientation := fun D => D.period.orientation
  lower := fun D => D.lower
  lowerGeOne :=
    PeriodFinalIntegratedW11.LowerBoundFields.lowerGeOne
  lowerBound :=
    PeriodFinalIntegratedW11.LowerBoundFields.lowerBound
  fixedBlockTarget :=
    PeriodFinalIntegratedW11.LowerBoundFields.exactBlockTarget
  projection :=
    TargetProjection.ofPeriodFinalRoute
      (PeriodFinalIntegratedW11.matrix.lowerBound T)

/-- Exact-candidate period data with conditional target projections. -/
structure ExactCandidateRoute (T : Candidate) where
  period :
    ExactCandidateFields T ->
      PeriodTargetIntegratedW11.CheckedWordEquationFamily T
  projection : TargetProjection (ExactCandidateFields T)

def exactCandidateRoute (T : Candidate) : ExactCandidateRoute T where
  period := fun D => D.period
  projection :=
    TargetProjection.ofPeriodFinalRoute
      (PeriodFinalIntegratedW11.matrix.exactCandidate T)

/-! ## External consistency ledgers -/

/-- Transition/period final rows imported into this final target layer. -/
structure TransitionPeriodProjectionLedger where
  routePackage : TargetProjection TransitionPeriodRoutePackage
  periodPackage : TargetProjection TransitionPeriodPeriodPackage
  periodBlockPackage : BlockProjection TransitionPeriodBlockPackage

def transitionPeriodProjectionLedger :
    TransitionPeriodProjectionLedger where
  routePackage :=
    TargetProjection.ofTransitionPeriodRow
      TransitionPeriodFinalW11.matrix.projections.route
  periodPackage :=
    TargetProjection.ofTransitionPeriodRow
      TransitionPeriodFinalW11.matrix.projections.period
  periodBlockPackage :=
    { blockIndex := TransitionPeriodFinalW11.PeriodBlockPackage.blockIndex
      fixedBlockTarget :=
        TransitionPeriodFinalW11.targetUpperConstructionFiveSixteenAt_of_periodBlockPackage }

/-- Arbitrary-`n` target rows used as a consistency cross-check. -/
structure ArbitraryNProjectionLedger where
  exactAssumptions :
    TargetProjection ArbitraryNExactTargetAssumptions
  exactClosedChainsArbitrary :
    ArbitraryNExactClosedChainPackage -> ArbitraryTarget
  eventualClosedChainsArbitrary :
    ArbitraryNEventualClosedChainPackage -> ArbitraryTarget

def arbitraryNProjectionLedger : ArbitraryNProjectionLedger where
  exactAssumptions :=
    TargetProjection.ofArbitraryNExactRoute
      ArbitraryNTargetFinalW11.matrix.exact.exactAssumptions
  exactClosedChainsArbitrary :=
    ArbitraryNTargetFinalW11.arbitraryTarget_of_exactClosedChains
  eventualClosedChainsArbitrary :=
    ArbitraryNTargetFinalW11.arbitraryTarget_of_eventualClosedChains

/-- Broad final aggregate projections that touch the period surface. -/
structure FinalAggregateProjectionLedger where
  baseWordSeparationFixed :
    forall {T : Candidate}, forall D : BaseWordSeparationFields T,
      FixedTarget (16 * D.checkedWord.length)
  baseExactCandidateArbitrary :
    forall {T : Candidate}, BaseExactCandidateFields T -> ArbitraryTarget
  transitionPeriodArbitrary :
    TransitionFinalIntegratedW11.PeriodPackage -> ArbitraryTarget

def finalAggregateProjectionLedger : FinalAggregateProjectionLedger where
  baseWordSeparationFixed := fun D =>
    PachTothW11FinalAggregate.fixedTarget_of_periodCheckedWordSeparation D
  baseExactCandidateArbitrary := fun D =>
    PachTothW11FinalAggregate.arbitraryTarget_of_periodExactCandidateFields D
  transitionPeriodArbitrary := fun package =>
    PachTothW11FinalAggregate.arbitraryTarget_of_transitionPeriodPackage
      package

/-! ## Final matrix -/

/-- Package-shape ledger for the final period target layer. -/
structure ExplicitPackageLedger where
  periodTargetInputs : PeriodTargetIntegratedW11.ExplicitPeriodTargetInputs
  periodFinalFields : PeriodFinalIntegratedW11.FieldLedger
  transitionPeriodFields :
    TransitionPeriodFinalW11.ExplicitRoutePeriodPackageFields
  aggregatePeriodData : PachTothW11FinalAggregate.ExplicitPeriodData
  wordSeparationFields : Candidate -> Type
  separatedFamilyFields : Candidate -> Type
  lowerBoundFields : Candidate -> Type
  exactCandidateFields : Candidate -> Type

def explicitPackageLedger : ExplicitPackageLedger where
  periodTargetInputs := PeriodTargetIntegratedW11.explicitPeriodTargetInputs
  periodFinalFields := PeriodFinalIntegratedW11.fieldLedger
  transitionPeriodFields :=
    TransitionPeriodFinalW11.explicitRoutePeriodPackageFields
  aggregatePeriodData := PachTothW11FinalAggregate.explicitPeriodData
  wordSeparationFields := WordSeparationFields
  separatedFamilyFields := SeparatedFamilyFields
  lowerBoundFields := LowerBoundFields
  exactCandidateFields := ExactCandidateFields

/-- Checked matrices imported by this final target layer. -/
structure ImportedLedgers where
  periodTarget : PeriodTargetIntegratedW11.Matrix
  periodFinal : PeriodFinalIntegratedW11.Matrix
  transitionPeriodFinal : TransitionPeriodFinalW11.Matrix
  arbitraryNTargetFinal : ArbitraryNTargetFinalW11.Matrix
  pachTothFinalAggregate : PachTothW11FinalAggregate.Matrix

def importedLedgers : ImportedLedgers where
  periodTarget := PeriodTargetIntegratedW11.matrix
  periodFinal := PeriodFinalIntegratedW11.matrix
  transitionPeriodFinal := TransitionPeriodFinalW11.matrix
  arbitraryNTargetFinal := ArbitraryNTargetFinalW11.matrix
  pachTothFinalAggregate := PachTothW11FinalAggregate.matrix

/-- Period package projections retained by the final target layer. -/
structure PeriodProjectionLedger where
  wordSeparation : forall T : Candidate, WordSeparationRoute T
  separatedFamily : forall T : Candidate, SeparatedFamilyRoute T
  lowerBound : forall T : Candidate, LowerBoundRoute T
  exactCandidate : forall T : Candidate, ExactCandidateRoute T
  aggregateSeparatedFamily :
    forall T : Candidate, TargetProjection (AggregateFields T)
  aggregateLowerBound :
    forall T : Candidate, TargetProjection (AggregateFields T)
  aggregateExactCandidate :
    forall T : Candidate, TargetProjection (AggregateFields T)

def periodProjectionLedger : PeriodProjectionLedger where
  wordSeparation := wordSeparationRoute
  separatedFamily := separatedFamilyRoute
  lowerBound := lowerBoundRoute
  exactCandidate := exactCandidateRoute
  aggregateSeparatedFamily := fun T =>
    TargetProjection.ofPeriodFinalRoute
      ((PeriodFinalIntegratedW11.matrix.aggregate T).separatedFamily)
  aggregateLowerBound := fun T =>
    TargetProjection.ofPeriodFinalRoute
      ((PeriodFinalIntegratedW11.matrix.aggregate T).lowerBound)
  aggregateExactCandidate := fun T =>
    TargetProjection.ofPeriodFinalRoute
      ((PeriodFinalIntegratedW11.matrix.aggregate T).exactCandidate)

/-- Final period target consistency matrix.

All target rows are functions out of displayed packages.
-/
structure Matrix where
  packages : ExplicitPackageLedger
  imported : ImportedLedgers
  period : PeriodProjectionLedger
  transitionPeriod : TransitionPeriodProjectionLedger
  arbitraryN : ArbitraryNProjectionLedger
  finalAggregate : FinalAggregateProjectionLedger

/-- Checked final W11 period target consistency matrix. -/
def matrix : Matrix where
  packages := explicitPackageLedger
  imported := importedLedgers
  period := periodProjectionLedger
  transitionPeriod := transitionPeriodProjectionLedger
  arbitraryN := arbitraryNProjectionLedger
  finalAggregate := finalAggregateProjectionLedger

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public word and separation projections -/

theorem positiveLength_of_wordSeparationFields
    {T : Candidate}
    (D : WordSeparationFields T) :
    0 < D.length :=
  (matrix.period.wordSeparation T).positiveLength D

theorem separated_of_wordSeparationFields
    {T : Candidate}
    (D : WordSeparationFields T) :
    PeriodFinalIntegratedW11.GeneratedGlobalSeparation
      T D.checkedWord.positive_length D.checkedWord.orientation :=
  PeriodFinalIntegratedW11.WordSeparationFields.separationWitness D

theorem fixedTarget_of_wordSeparationFields
    {T : Candidate}
    (D : WordSeparationFields T) :
    FixedTarget (16 * D.length) :=
  (matrix.period.wordSeparation T).fixedBlockTarget D

theorem separated_of_separatedFamilyFields
    {T : Candidate}
    (D : SeparatedFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    PeriodFinalIntegratedW11.GeneratedGlobalSeparation
      T hk (D.orientation k hk) :=
  (matrix.period.separatedFamily T).separated D k hk

theorem fixedBlockTarget_of_separatedFamilyFields
    {T : Candidate}
    (D : SeparatedFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    FixedTarget (16 * k) :=
  (matrix.period.separatedFamily T).fixedBlockTarget D k hk

theorem exactTarget_of_separatedFamilyFields
    {T : Candidate}
    (D : SeparatedFamilyFields T) :
    ExactTarget :=
  (matrix.period.separatedFamily T).projection.exactTarget D

theorem eventualTarget_of_separatedFamilyFields
    {T : Candidate}
    (D : SeparatedFamilyFields T) :
    EventualTarget :=
  (matrix.period.separatedFamily T).projection.eventualTarget D

theorem arbitraryTarget_of_separatedFamilyFields
    {T : Candidate}
    (D : SeparatedFamilyFields T) :
    ArbitraryTarget :=
  (matrix.period.separatedFamily T).projection.arbitraryTarget D

/-! ## Public lower-bound projections -/

theorem lower_ge_one_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : FiniteGraph.LocalVertex)
    (j : Fin k) (v : FiniteGraph.LocalVertex)
    (hij : Ne i j) :
    1 <= D.lower k hk i u j v :=
  (matrix.period.lowerBound T).lowerGeOne D k hk i u j v hij

theorem lower_bound_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : FiniteGraph.LocalVertex)
    (j : Fin k) (v : FiniteGraph.LocalVertex)
    (hij : Ne i j) :
    D.lower k hk i u j v <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (D.period.orientation k hk)
          i u)
        (GeneratedClosedChain.generatedPoint
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (D.period.orientation k hk)
          j v) :=
  (matrix.period.lowerBound T).lowerBound D k hk i u j v hij

theorem fixedBlockTarget_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T)
    (k : Nat) (hk : 0 < k) :
    FixedTarget (16 * k) :=
  (matrix.period.lowerBound T).fixedBlockTarget D k hk

theorem exactTarget_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T) :
    ExactTarget :=
  (matrix.period.lowerBound T).projection.exactTarget D

theorem eventualTarget_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T) :
    EventualTarget :=
  (matrix.period.lowerBound T).projection.eventualTarget D

theorem arbitraryTarget_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T) :
    ArbitraryTarget :=
  (matrix.period.lowerBound T).projection.arbitraryTarget D

/-! ## Public exact-candidate projections -/

def periodFamily_of_exactCandidateFields
    {T : Candidate}
    (D : ExactCandidateFields T) :
    PeriodTargetIntegratedW11.CheckedWordEquationFamily T :=
  (matrix.period.exactCandidate T).period D

theorem exactTarget_of_exactCandidateFields
    {T : Candidate}
    (D : ExactCandidateFields T) :
    ExactTarget :=
  (matrix.period.exactCandidate T).projection.exactTarget D

theorem eventualTarget_of_exactCandidateFields
    {T : Candidate}
    (D : ExactCandidateFields T) :
    EventualTarget :=
  (matrix.period.exactCandidate T).projection.eventualTarget D

theorem arbitraryTarget_of_exactCandidateFields
    {T : Candidate}
    (D : ExactCandidateFields T) :
    ArbitraryTarget :=
  (matrix.period.exactCandidate T).projection.arbitraryTarget D

/-! ## Public aggregate projections -/

theorem exactTarget_of_aggregateSeparatedFamily
    {T : Candidate}
    (A : AggregateFields T) :
    ExactTarget :=
  (matrix.period.aggregateSeparatedFamily T).exactTarget A

theorem eventualTarget_of_aggregateSeparatedFamily
    {T : Candidate}
    (A : AggregateFields T) :
    EventualTarget :=
  (matrix.period.aggregateSeparatedFamily T).eventualTarget A

theorem arbitraryTarget_of_aggregateSeparatedFamily
    {T : Candidate}
    (A : AggregateFields T) :
    ArbitraryTarget :=
  (matrix.period.aggregateSeparatedFamily T).arbitraryTarget A

theorem exactTarget_of_aggregateLowerBound
    {T : Candidate}
    (A : AggregateFields T) :
    ExactTarget :=
  (matrix.period.aggregateLowerBound T).exactTarget A

theorem eventualTarget_of_aggregateLowerBound
    {T : Candidate}
    (A : AggregateFields T) :
    EventualTarget :=
  (matrix.period.aggregateLowerBound T).eventualTarget A

theorem arbitraryTarget_of_aggregateLowerBound
    {T : Candidate}
    (A : AggregateFields T) :
    ArbitraryTarget :=
  (matrix.period.aggregateLowerBound T).arbitraryTarget A

theorem exactTarget_of_aggregateExactCandidate
    {T : Candidate}
    (A : AggregateFields T) :
    ExactTarget :=
  (matrix.period.aggregateExactCandidate T).exactTarget A

theorem eventualTarget_of_aggregateExactCandidate
    {T : Candidate}
    (A : AggregateFields T) :
    EventualTarget :=
  (matrix.period.aggregateExactCandidate T).eventualTarget A

theorem arbitraryTarget_of_aggregateExactCandidate
    {T : Candidate}
    (A : AggregateFields T) :
    ArbitraryTarget :=
  (matrix.period.aggregateExactCandidate T).arbitraryTarget A

/-! ## Public consistency projections -/

theorem exactTarget_of_transitionPeriodPackage
    (package : TransitionPeriodPeriodPackage) :
    ExactTarget :=
  matrix.transitionPeriod.periodPackage.exactTarget package

theorem eventualTarget_of_transitionPeriodPackage
    (package : TransitionPeriodPeriodPackage) :
    EventualTarget :=
  matrix.transitionPeriod.periodPackage.eventualTarget package

theorem arbitraryTarget_of_transitionPeriodPackage
    (package : TransitionPeriodPeriodPackage) :
    ArbitraryTarget :=
  matrix.transitionPeriod.periodPackage.arbitraryTarget package

theorem fixedTarget_of_transitionPeriodBlockPackage
    (package : TransitionPeriodBlockPackage) :
    FixedTarget
      (16 * TransitionPeriodFinalW11.PeriodBlockPackage.blockIndex package) :=
  matrix.transitionPeriod.periodBlockPackage.fixedBlockTarget package

theorem exactTarget_of_arbitraryNExactAssumptions
    (A : ArbitraryNExactTargetAssumptions) :
    ExactTarget :=
  matrix.arbitraryN.exactAssumptions.exactTarget A

theorem arbitraryTarget_of_arbitraryNExactClosedChains
    (P : ArbitraryNExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.arbitraryN.exactClosedChainsArbitrary P

theorem arbitraryTarget_of_arbitraryNEventualClosedChains
    (P : ArbitraryNEventualClosedChainPackage) :
    ArbitraryTarget :=
  matrix.arbitraryN.eventualClosedChainsArbitrary P

theorem aggregate_fixedTarget_of_baseWordSeparationFields
    {T : Candidate}
    (D : BaseWordSeparationFields T) :
    FixedTarget (16 * D.checkedWord.length) :=
  matrix.finalAggregate.baseWordSeparationFixed D

theorem aggregate_arbitraryTarget_of_baseExactCandidateFields
    {T : Candidate}
    (D : BaseExactCandidateFields T) :
    ArbitraryTarget :=
  matrix.finalAggregate.baseExactCandidateArbitrary D

end

end PeriodTargetFinalW11
end PachToth
end ErdosProblems1066
