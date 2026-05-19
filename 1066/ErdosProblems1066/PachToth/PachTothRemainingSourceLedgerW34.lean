import ErdosProblems1066.PachToth.CrossBlockMetricInequalitiesW33
import ErdosProblems1066.PachToth.AlternativeNonRigidClosedPlacementW34
import ErdosProblems1066.PachToth.ClosedPlacementSmallKCertificatesW19
import ErdosProblems1066.PachToth.DeformedPlacementConstructionW33
import ErdosProblems1066.PachToth.FiniteReducedMetricCandidateSearchW33
import ErdosProblems1066.PachToth.FlexibleCandidateMetricInhabitationW33
import ErdosProblems1066.PachToth.FreePlacementClosedPlacementSourceW34
import ErdosProblems1066.PachToth.PachTothW32FinalAssembly

set_option autoImplicit false

/-!
# W34 remaining Pach-Toth source ledger

This file records the final source audit after the W33 exact-base flexible
obstruction.  It does not add public endpoint wrappers.  Its purpose is only to
pin down:

* the W32 final conditional gate is still the inherited W31 source gate;
* the direct exact-base flexible payload and its equivalent table/lower-table
  forms are uninhabited;
* the generated-closure route through that exact-base payload is also blocked;
* the remaining positive closed-placement source is the deformed metric-field
  family, equivalently a checked deformed closed-placement family.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothRemainingSourceLedgerW34

noncomputable section

open FlexibleTransitionSearchW11

abbrev FinalConditionalSourceGate : Prop :=
  PachTothW32FinalAssembly.FinalConditionalSourceGate

abbrev InheritedW31FinalConditionalSourceGate : Prop :=
  PachTothW31FinalAssembly.FinalConditionalSourceGate

abbrev DirectFlexibleSourcePayload : Type :=
  FlexibleTransitionSearchW11.DirectFlexibleSourcePayload

abbrev DirectFlexibleSourcePayloadGate : Prop :=
  Nonempty DirectFlexibleSourcePayload

abbrev NonRigidRouteSourceFields : Type :=
  FlexibleTransitionSearchW11.NonRigidRouteSourceFields

abbrev NonRigidRouteSourceFieldsGate : Prop :=
  Nonempty NonRigidRouteSourceFields

abbrev FlexiblePeriodLowerTableFamily : Type :=
  PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily

abbrev FlexiblePeriodLowerTableFamilyGate : Prop :=
  Nonempty FlexiblePeriodLowerTableFamily

abbrev FlexibleGeneratedClosureFamily : Type :=
  FlexibleExactLocalTransition.GeneratedClosureFamily

abbrev FlexibleGeneratedClosureFamilyGate : Prop :=
  Nonempty FlexibleGeneratedClosureFamily

abbrev CandidatePeriodMetricData : Type :=
  FlexibleTransitionSearchW11.CandidatePeriodMetricData

abbrev CandidatePeriodMetricDataGate : Prop :=
  Nonempty CandidatePeriodMetricData

abbrev IndexedCandidatePeriodMetricTableData : Type :=
  FlexibleCandidateMetricInhabitationW33.IndexedCandidatePeriodMetricTableData

abbrev IndexedCandidatePeriodMetricTableDataGate : Prop :=
  Nonempty IndexedCandidatePeriodMetricTableData

abbrev ClosedPlacementFamily : Type :=
  forall (k : Nat) (hk : 0 < k), DeformedPlacement.ClosedPlacement k hk

abbrev ClosedPlacementFamilyGate : Prop :=
  Nonempty ClosedPlacementFamily

abbrev DeformedMetricFieldFamily : Type :=
  DeformedPlacement.ClosedPlacementMetricFieldFamily

abbrev DeformedMetricFieldFamilyGate : Prop :=
  Nonempty DeformedMetricFieldFamily

abbrev ExactAndArbitraryTargets : Prop :=
  PachTothW32FinalAssembly.ExactAndArbitraryTargets

abbrev MinimalExactRemainderSplitSourceBlocker : Prop :=
  RemainderSplitSourceClosureW32.MinimalExactRemainderSplitSourceBlocker

abbrev ExactBlocksOneThroughFive : Prop :=
  RemainderSplitSourceClosureW32.ExactBlocksOneThroughFive

abbrev LargeExactBlockTargetsFromSix : Prop :=
  RemainderSplitSourceClosureW32.LargeExactBlockTargetsFromSix

abbrev DeformedLengthOneExactBlocksTwoThroughFiveSource : Type :=
  RemainderSplitSourceClosureW32.DeformedLengthOneExactBlocksTwoThroughFiveSource

abbrev FreePlacementSourceFields : Type :=
  _root_.ErdosProblems1066.PachToth.FreePlacementClosedPlacementSourceW34.MinimalFreePlacementFields

abbrev FreePlacementSourceFieldsGate : Prop :=
  Nonempty FreePlacementSourceFields

abbrev LargeClosedPlacementFieldsSix : Type :=
  LargeClosedPlacementInstantiationW13.LargeClosedPlacementFields 6

def asAlternativeLargeClosedPlacementFieldsSix
    (L : LargeClosedPlacementFieldsSix) :
    AlternativeNonRigidClosedPlacementW34.LargeClosedPlacementFields 6 :=
  L

def asRemainderLargeClosedPlacementFieldsFromSix
    (L : LargeClosedPlacementFieldsSix) :
    RemainderSplitSourceClosureW32.LargeClosedPlacementFieldsFromSix :=
  L

/-- The exact finite metric-field complement needed below the threshold-six
large closed-placement source. -/
structure BelowThresholdMetricFieldsSix where
  fields :
    forall (k : Nat), k < 6 -> forall hk : 0 < k,
      DeformedPlacement.ClosedPlacementMetricFields k hk

/-! ## The inherited final gate -/

theorem finalConditionalSourceGate_iff_w31 :
    FinalConditionalSourceGate <->
      InheritedW31FinalConditionalSourceGate :=
  PachTothW32FinalAssembly.finalConditionalSourceGate_iff_w31

/-! ## Exact-base flexible source equivalences and blockers -/

theorem directFlexibleSourcePayloadGate_iff_candidatePeriodMetricDataGate :
    DirectFlexibleSourcePayloadGate <-> CandidatePeriodMetricDataGate :=
  FlexibleTransitionSearchW11.nonempty_directFlexibleSourcePayload_iff_candidatePeriodMetricData

theorem directFlexibleSourcePayloadGate_iff_indexedCandidatePeriodMetricTableDataGate :
    DirectFlexibleSourcePayloadGate <->
      IndexedCandidatePeriodMetricTableDataGate :=
  FlexibleCandidateMetricInhabitationW33.nonempty_directFlexibleSourcePayload_iff_indexedTables

theorem flexiblePeriodLowerTableFamilyGate_iff_directFlexibleSourcePayloadGate :
    FlexiblePeriodLowerTableFamilyGate <->
      DirectFlexibleSourcePayloadGate :=
  nonempty_flexiblePeriodLowerTableFamily_iff_directFlexibleSourcePayload

theorem not_directFlexibleSourcePayloadGate :
    Not DirectFlexibleSourcePayloadGate :=
  FlexibleCandidateMetricInhabitationW33.not_nonempty_directFlexibleSourcePayload

theorem not_candidatePeriodMetricDataGate :
    Not CandidatePeriodMetricDataGate :=
  FlexibleCandidateMetricInhabitationW33.not_nonempty_candidatePeriodMetricData

theorem not_indexedCandidatePeriodMetricTableDataGate :
    Not IndexedCandidatePeriodMetricTableDataGate :=
  FlexibleCandidateMetricInhabitationW33.not_nonempty_indexedCandidatePeriodMetricTableData

theorem not_flexiblePeriodLowerTableFamilyGate :
    Not FlexiblePeriodLowerTableFamilyGate := by
  intro H
  exact not_directFlexibleSourcePayloadGate
    (flexiblePeriodLowerTableFamilyGate_iff_directFlexibleSourcePayloadGate.1 H)

theorem not_nonRigidRouteSourceFieldsGate :
    Not NonRigidRouteSourceFieldsGate :=
  FlexibleTransitionSearchW11.sourceFields_blocked_without_directFlexibleSourcePayload
    not_directFlexibleSourcePayloadGate

theorem not_exists_crossBlockMetricData :
    Not
      (Exists fun T : FlexibleTransitionSearchW11.SameOppositeCandidate =>
        Exists fun P : FlexibleTransitionSearchW11.PeriodSearchData T =>
          Nonempty (RoleHingeCandidateSearchSurface.CrossBlockMetricData P)) :=
  CrossBlockMetricInequalitiesW33.not_exists_crossBlockMetricData

/-! ## The exact-base generated-closure route is blocked too -/

def periodSearchDataOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    FlexibleTransitionSearchW11.PeriodSearchData
      (FlexibleTransitionSearchW11.sameOppositeCandidateOfFlexibleSameOpposite
        F.transitions) where
  word := fun k hk => OrientationWord.Word.ofFin (F.orientation k hk)
  equation := by
    intro k hk i
    simpa [RoleHingeCandidateSearchSurface.ExactPeriodEquations,
      PeriodWordCertificates.AlgebraicEquationsForWord,
      PeriodWordCertificates.finiteOrientationWordOfWord,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation,
      PeriodSearchInterface.FiniteOrientationWord.iteratedTransitionBlock,
      FlexibleTransitionSearchW11.sameOppositeCandidateOfFlexibleSameOpposite,
      OrientationWord.Word.ofFin] using
        PeriodInterface.generatedClosureEquation_apply
          F.transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (F.orientation k hk)
          (F.closure k hk)
          (BlockPartition.localVertexEquivFin16.symm i)

theorem not_flexibleGeneratedClosureFamilyGate :
    Not FlexibleGeneratedClosureFamilyGate := by
  intro H
  cases H with
  | intro F =>
      exact
        FlexibleCandidateMetricInhabitationW33.not_nonempty_periodSearchData
          (FlexibleTransitionSearchW11.sameOppositeCandidateOfFlexibleSameOpposite
            F.transitions)
          (Nonempty.intro
            (periodSearchDataOfFlexibleGeneratedClosureFamily F))

/-! ## Remaining positive deformed source -/

def deformedMetricFieldsOfClosedPlacement
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    DeformedPlacement.ClosedPlacementMetricFields k hk where
  point := P.point
  separated := P.separated
  same_block_edges_unit := P.same_block_edges_unit
  cross_connector_named_units :=
    ClosedPlacementCrossConnectorEdgesW19.ofClosedPlacement P

def belowThresholdMetricFieldsSixOfSmallExplicitTransitionCertificateSource
    (S : ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource) :
    BelowThresholdMetricFieldsSix where
  fields := by
    intro k hklt hk
    interval_cases k
    · have hproof :
          ClosedPlacementSmallKCertificatesW19.onePositive = hk :=
        Subsingleton.elim _ _
      cases hproof
      exact
        deformedMetricFieldsOfClosedPlacement
          S.lengthOneClosedPlacement
    · have hproof :
          ClosedPlacementSmallKCertificatesW19.twoPositive = hk :=
        Subsingleton.elim _ _
      cases hproof
      exact
        deformedMetricFieldsOfClosedPlacement
          S.lengthTwo.toClosedPlacement
    · have hproof :
          ClosedPlacementSmallKCertificatesW19.threePositive = hk :=
        Subsingleton.elim _ _
      cases hproof
      exact
        deformedMetricFieldsOfClosedPlacement
          S.lengthThree.toClosedPlacement
    · have hproof :
          ClosedPlacementSmallKCertificatesW19.fourPositive = hk :=
        Subsingleton.elim _ _
      cases hproof
      exact
        deformedMetricFieldsOfClosedPlacement
          S.lengthFour.toClosedPlacement
    · have hproof :
          ClosedPlacementSmallKCertificatesW19.fivePositive = hk :=
        Subsingleton.elim _ _
      cases hproof
      exact
        deformedMetricFieldsOfClosedPlacement
          S.lengthFive.toClosedPlacement

theorem nonempty_belowThresholdMetricFieldsSix_of_smallExplicitTransitionCertificateSource
    (H :
      Nonempty
        ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource) :
    Nonempty BelowThresholdMetricFieldsSix := by
  rcases H with ⟨S⟩
  exact
    ⟨belowThresholdMetricFieldsSixOfSmallExplicitTransitionCertificateSource S⟩

def lengthOneMetricFieldsOfBelowThresholdMetricFieldsSix
    (B : BelowThresholdMetricFieldsSix) :
    DeformedPlacement.ClosedPlacementMetricFields 1
      ClosedPlacementSmallKCertificatesW19.onePositive :=
  B.fields 1 (by decide) ClosedPlacementSmallKCertificatesW19.onePositive

def lengthOneGeometryOfMetricFields
    (F :
      DeformedPlacement.ClosedPlacementMetricFields 1
        ClosedPlacementSmallKCertificatesW19.onePositive) :
    DeformedPlacement.LengthOneGeometry :=
  DeformedPlacement.lengthOneGeometryOfClosedPlacement F.toClosedPlacement

theorem nonempty_lengthOneMetricFields_of_belowThresholdMetricFieldsSix
    (H : Nonempty BelowThresholdMetricFieldsSix) :
    Nonempty
      (DeformedPlacement.ClosedPlacementMetricFields 1
        ClosedPlacementSmallKCertificatesW19.onePositive) := by
  rcases H with ⟨B⟩
  exact ⟨lengthOneMetricFieldsOfBelowThresholdMetricFieldsSix B⟩

theorem nonempty_lengthOneGeometry_of_lengthOneMetricFields
    (H :
      Nonempty
        (DeformedPlacement.ClosedPlacementMetricFields 1
          ClosedPlacementSmallKCertificatesW19.onePositive)) :
    Nonempty DeformedPlacement.LengthOneGeometry := by
  rcases H with ⟨F⟩
  exact ⟨lengthOneGeometryOfMetricFields F⟩

theorem nonempty_lengthOneGeometry_of_belowThresholdMetricFieldsSix
    (H : Nonempty BelowThresholdMetricFieldsSix) :
    Nonempty DeformedPlacement.LengthOneGeometry :=
  nonempty_lengthOneGeometry_of_lengthOneMetricFields
    (nonempty_lengthOneMetricFields_of_belowThresholdMetricFieldsSix H)

theorem not_belowThresholdMetricFieldsSix_of_no_lengthOneMetricFields
    (h :
      Not
        (Nonempty
          (DeformedPlacement.ClosedPlacementMetricFields 1
            ClosedPlacementSmallKCertificatesW19.onePositive))) :
    Not (Nonempty BelowThresholdMetricFieldsSix) := by
  intro H
  exact h (nonempty_lengthOneMetricFields_of_belowThresholdMetricFieldsSix H)

theorem not_belowThresholdMetricFieldsSix_of_no_lengthOneGeometry
    (h : Not (Nonempty DeformedPlacement.LengthOneGeometry)) :
    Not (Nonempty BelowThresholdMetricFieldsSix) := by
  intro H
  exact h (nonempty_lengthOneGeometry_of_belowThresholdMetricFieldsSix H)

/-- Honest status of the threshold-six complement: any inhabitant must provide
the collapsed `k = 1` metric row.  The final field is the checked algebraic
obstruction already recorded for the forced length-one branch. -/
structure BelowThresholdMetricFieldsSixBlockerCertificate : Prop where
  lengthOneMetricFieldsRequired :
    Nonempty BelowThresholdMetricFieldsSix ->
      Nonempty
        (DeformedPlacement.ClosedPlacementMetricFields 1
          ClosedPlacementSmallKCertificatesW19.onePositive)
  lengthOneGeometryRequired :
    Nonempty BelowThresholdMetricFieldsSix ->
      Nonempty DeformedPlacement.LengthOneGeometry
  noBelowThresholdOfNoLengthOneGeometry :
    Not (Nonempty DeformedPlacement.LengthOneGeometry) ->
      Not (Nonempty BelowThresholdMetricFieldsSix)
  forcedBranchT2CompletionObstruction :
    Not
      (Exists fun s : Real =>
        Exists fun x : Real =>
          Exists fun y : Real =>
            s ^ 2 = (3 : Real) / 4 /\
            (x - (3 / 2 : Real)) ^ 2 + (y - s) ^ 2 = 1 /\
            (x - (-1 : Real)) ^ 2 + (y - (-2 * s)) ^ 2 = 1)

theorem belowThresholdMetricFieldsSix_blockerCertificate :
    BelowThresholdMetricFieldsSixBlockerCertificate where
  lengthOneMetricFieldsRequired :=
    nonempty_lengthOneMetricFields_of_belowThresholdMetricFieldsSix
  lengthOneGeometryRequired :=
    nonempty_lengthOneGeometry_of_belowThresholdMetricFieldsSix
  noBelowThresholdOfNoLengthOneGeometry :=
    not_belowThresholdMetricFieldsSix_of_no_lengthOneGeometry
  forcedBranchT2CompletionObstruction :=
    DeformedPlacement.not_lengthOne_forcedBranch_t2Completion

def closedPlacementFamilyOfDeformedMetricFieldFamily
    (F : DeformedMetricFieldFamily) :
    ClosedPlacementFamily :=
  fun k hk => (F k hk).toClosedPlacement

def deformedMetricFieldFamilyOfClosedPlacementFamily
    (F : ClosedPlacementFamily) :
    DeformedMetricFieldFamily :=
  fun k hk => deformedMetricFieldsOfClosedPlacement (F k hk)

theorem deformedMetricFieldFamilyGate_iff_closedPlacementFamilyGate :
    DeformedMetricFieldFamilyGate <-> ClosedPlacementFamilyGate := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro F =>
        exact Nonempty.intro
          (closedPlacementFamilyOfDeformedMetricFieldFamily F)
  case mpr =>
    intro H
    cases H with
    | intro F =>
        exact Nonempty.intro
          (deformedMetricFieldFamilyOfClosedPlacementFamily F)

theorem deformedMetricFieldFamilyGate_iff_freePlacementSourceFieldsGate :
    DeformedMetricFieldFamilyGate <-> FreePlacementSourceFieldsGate := by
  constructor
  · intro H
    exact
      FreePlacementClosedPlacementSourceW34.nonempty_minimalFreePlacementFields_of_metricFieldFamily
        H
  · intro H
    exact
      FreePlacementClosedPlacementSourceW34.nonempty_metricFieldFamily_of_minimalFreePlacementFields
        H

def deformedMetricFieldFamilyOfLargeClosedPlacementFieldsSixAndBelow
    (L : LargeClosedPlacementFieldsSix) (B : BelowThresholdMetricFieldsSix) :
    DeformedMetricFieldFamily :=
  fun k hk =>
    if hK : 6 <= k then
      AlternativeNonRigidClosedPlacementW34.metricFieldsOfLargeClosedPlacementFields
        (asAlternativeLargeClosedPlacementFieldsSix L) hK hk
    else
      B.fields k (by omega) hk

theorem deformedMetricFieldFamilyGate_of_largeClosedPlacementFieldsSix_and_below
    (L : LargeClosedPlacementFieldsSix) (B : BelowThresholdMetricFieldsSix) :
    DeformedMetricFieldFamilyGate :=
  Nonempty.intro
    (deformedMetricFieldFamilyOfLargeClosedPlacementFieldsSixAndBelow L B)

theorem largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsSix
    (L : LargeClosedPlacementFieldsSix) :
    LargeExactBlockTargetsFromSix :=
  RemainderSplitSourceClosureW32.largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsFromSix
    (asRemainderLargeClosedPlacementFieldsFromSix L)

def deformedLengthOneExactBlocksTwoThroughFiveSourceOfBelowThresholdMetricFieldsSix
    (B : BelowThresholdMetricFieldsSix) :
    DeformedLengthOneExactBlocksTwoThroughFiveSource where
  lengthOne :=
    (B.fields 1 (by norm_num)
      SmallLengthExactTargetsConcreteW24.deformedLengthOnePositive).toClosedPlacement
  blocksTwoThroughFive :=
    { lengthTwo :=
        SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_deformedClosedPlacement
          ((B.fields 2 (by norm_num) (by norm_num)).toClosedPlacement)
      lengthThree :=
        SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_deformedClosedPlacement
          ((B.fields 3 (by norm_num) (by norm_num)).toClosedPlacement)
      lengthFourFive :=
        { lengthFour :=
            SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_deformedClosedPlacement
              ((B.fields 4 (by norm_num) (by norm_num)).toClosedPlacement)
          lengthFive :=
            SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_deformedClosedPlacement
              ((B.fields 5 (by norm_num) (by norm_num)).toClosedPlacement) } }

theorem exactBlocksOneThroughFive_of_belowThresholdMetricFieldsSix
    (B : BelowThresholdMetricFieldsSix) :
    ExactBlocksOneThroughFive :=
  (deformedLengthOneExactBlocksTwoThroughFiveSourceOfBelowThresholdMetricFieldsSix
    B).exactBlocksOneThroughFive

theorem minimalExactRemainderSplitSourceBlocker_of_largeClosedPlacementFieldsSix_and_deformedSmallSource
    (L : LargeClosedPlacementFieldsSix)
    (small : DeformedLengthOneExactBlocksTwoThroughFiveSource) :
    MinimalExactRemainderSplitSourceBlocker :=
  RemainderSplitSourceClosureW32.minimalBlocker_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
    small (asRemainderLargeClosedPlacementFieldsFromSix L)

theorem minimalExactRemainderSplitSourceBlocker_of_largeClosedPlacementFieldsSix_and_below
    (L : LargeClosedPlacementFieldsSix) (B : BelowThresholdMetricFieldsSix) :
    MinimalExactRemainderSplitSourceBlocker :=
  minimalExactRemainderSplitSourceBlocker_of_largeClosedPlacementFieldsSix_and_deformedSmallSource
    L
    (deformedLengthOneExactBlocksTwoThroughFiveSourceOfBelowThresholdMetricFieldsSix
      B)

theorem exactAndArbitraryTargets_of_minimalExactRemainderSplitSourceBlocker
    (H : MinimalExactRemainderSplitSourceBlocker) :
    ExactAndArbitraryTargets :=
  PachTothW32FinalAssembly.exactAndArbitraryTargets_of_remainderSplitSource
    (RemainderSplitSourceClosureW32.packageGate_of_minimalBlocker H)

theorem exactAndArbitraryTargets_of_largeClosedPlacementFieldsSix_and_deformedSmallSource
    (L : LargeClosedPlacementFieldsSix)
    (small : DeformedLengthOneExactBlocksTwoThroughFiveSource) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_minimalExactRemainderSplitSourceBlocker
    (minimalExactRemainderSplitSourceBlocker_of_largeClosedPlacementFieldsSix_and_deformedSmallSource
      L small)

theorem finalConditionalSourceGate_of_deformedMetricFieldFamilyGate
    (H : DeformedMetricFieldFamilyGate) :
    FinalConditionalSourceGate := by
  have Hclosed : ClosedPlacementFamilyGate :=
    deformedMetricFieldFamilyGate_iff_closedPlacementFamilyGate.1 H
  exact
    PachTothW32FinalAssembly.finalConditionalSourceGate_of_remainderSplitClosedPlacementFamily
      Hclosed

theorem exactAndArbitraryTargets_of_deformedMetricFieldFamilyGate
    (H : DeformedMetricFieldFamilyGate) :
    PachTothW32FinalAssembly.ExactAndArbitraryTargets :=
  PachTothW32FinalAssembly.exactAndArbitraryTargets_of_finalConditionalSourceGate
    (finalConditionalSourceGate_of_deformedMetricFieldFamilyGate H)

theorem exactAndArbitraryTargets_of_freePlacementSourceFieldsGate
    (H : FreePlacementSourceFieldsGate) :
    PachTothW32FinalAssembly.ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_deformedMetricFieldFamilyGate
    (deformedMetricFieldFamilyGate_iff_freePlacementSourceFieldsGate.2 H)

theorem exactAndArbitraryTargets_of_largeClosedPlacementFieldsSix_and_below
    (L : LargeClosedPlacementFieldsSix) (B : BelowThresholdMetricFieldsSix) :
    PachTothW32FinalAssembly.ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_deformedMetricFieldFamilyGate
    (deformedMetricFieldFamilyGate_of_largeClosedPlacementFieldsSix_and_below
      L B)

theorem exactAndArbitraryTargets_of_largeSix_and_smallSource
    (L : LargeClosedPlacementFieldsSix)
    (S : ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource) :
    PachTothW32FinalAssembly.ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_largeClosedPlacementFieldsSix_and_below L
    (belowThresholdMetricFieldsSixOfSmallExplicitTransitionCertificateSource S)

structure RemainingSourceAuditCertificate : Prop where
  finalGateInherited :
    FinalConditionalSourceGate <-> InheritedW31FinalConditionalSourceGate
  directPayloadIffCandidateMetric :
    DirectFlexibleSourcePayloadGate <-> CandidatePeriodMetricDataGate
  directPayloadIffIndexedTables :
    DirectFlexibleSourcePayloadGate <->
      IndexedCandidatePeriodMetricTableDataGate
  lowerTableIffDirectPayload :
    FlexiblePeriodLowerTableFamilyGate <->
      DirectFlexibleSourcePayloadGate
  noDirectPayload :
    Not DirectFlexibleSourcePayloadGate
  noCandidateMetric :
    Not CandidatePeriodMetricDataGate
  noIndexedTables :
    Not IndexedCandidatePeriodMetricTableDataGate
  noFlexibleLowerTable :
    Not FlexiblePeriodLowerTableFamilyGate
  noNonRigidSourceFields :
    Not NonRigidRouteSourceFieldsGate
  noExactBaseGeneratedClosure :
    Not FlexibleGeneratedClosureFamilyGate
  deformedFieldsIffClosedPlacementFamily :
    DeformedMetricFieldFamilyGate <-> ClosedPlacementFamilyGate
  deformedFieldsIffFreePlacementSourceFields :
    DeformedMetricFieldFamilyGate <-> FreePlacementSourceFieldsGate
  largeSixAndBelowToDeformedFields :
    LargeClosedPlacementFieldsSix ->
      BelowThresholdMetricFieldsSix ->
        DeformedMetricFieldFamilyGate
  largeSixToLargeExactTail :
    LargeClosedPlacementFieldsSix -> LargeExactBlockTargetsFromSix
  belowToExactBlocksOneThroughFive :
    BelowThresholdMetricFieldsSix -> ExactBlocksOneThroughFive
  largeSixAndBelowToMinimalExactRemainderSplitBlocker :
    LargeClosedPlacementFieldsSix ->
      BelowThresholdMetricFieldsSix ->
        MinimalExactRemainderSplitSourceBlocker
  largeSixAndDeformedSmallToMinimalExactRemainderSplitBlocker :
    LargeClosedPlacementFieldsSix ->
      DeformedLengthOneExactBlocksTwoThroughFiveSource ->
        MinimalExactRemainderSplitSourceBlocker
  minimalExactRemainderSplitBlockerToTargets :
    MinimalExactRemainderSplitSourceBlocker ->
      ExactAndArbitraryTargets
  deformedFieldsToFinalGate :
    DeformedMetricFieldFamilyGate -> FinalConditionalSourceGate
  deformedFieldsToTargets :
    DeformedMetricFieldFamilyGate ->
      PachTothW32FinalAssembly.ExactAndArbitraryTargets

theorem remainingSourceAuditCertificate :
    RemainingSourceAuditCertificate where
  finalGateInherited := finalConditionalSourceGate_iff_w31
  directPayloadIffCandidateMetric :=
    directFlexibleSourcePayloadGate_iff_candidatePeriodMetricDataGate
  directPayloadIffIndexedTables :=
    directFlexibleSourcePayloadGate_iff_indexedCandidatePeriodMetricTableDataGate
  lowerTableIffDirectPayload :=
    flexiblePeriodLowerTableFamilyGate_iff_directFlexibleSourcePayloadGate
  noDirectPayload := not_directFlexibleSourcePayloadGate
  noCandidateMetric := not_candidatePeriodMetricDataGate
  noIndexedTables := not_indexedCandidatePeriodMetricTableDataGate
  noFlexibleLowerTable := not_flexiblePeriodLowerTableFamilyGate
  noNonRigidSourceFields := not_nonRigidRouteSourceFieldsGate
  noExactBaseGeneratedClosure := not_flexibleGeneratedClosureFamilyGate
  deformedFieldsIffClosedPlacementFamily :=
    deformedMetricFieldFamilyGate_iff_closedPlacementFamilyGate
  deformedFieldsIffFreePlacementSourceFields :=
    deformedMetricFieldFamilyGate_iff_freePlacementSourceFieldsGate
  largeSixAndBelowToDeformedFields :=
    deformedMetricFieldFamilyGate_of_largeClosedPlacementFieldsSix_and_below
  largeSixToLargeExactTail :=
    largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsSix
  belowToExactBlocksOneThroughFive :=
    exactBlocksOneThroughFive_of_belowThresholdMetricFieldsSix
  largeSixAndBelowToMinimalExactRemainderSplitBlocker :=
    minimalExactRemainderSplitSourceBlocker_of_largeClosedPlacementFieldsSix_and_below
  largeSixAndDeformedSmallToMinimalExactRemainderSplitBlocker :=
    minimalExactRemainderSplitSourceBlocker_of_largeClosedPlacementFieldsSix_and_deformedSmallSource
  minimalExactRemainderSplitBlockerToTargets :=
    exactAndArbitraryTargets_of_minimalExactRemainderSplitSourceBlocker
  deformedFieldsToFinalGate :=
    finalConditionalSourceGate_of_deformedMetricFieldFamilyGate
  deformedFieldsToTargets :=
    exactAndArbitraryTargets_of_deformedMetricFieldFamilyGate

end

end PachTothRemainingSourceLedgerW34
end PachToth
end ErdosProblems1066
