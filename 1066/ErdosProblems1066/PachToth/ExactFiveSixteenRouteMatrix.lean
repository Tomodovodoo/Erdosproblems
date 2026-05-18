import ErdosProblems1066.PachToth.SplitArbitraryNNonRigidBridge
import ErdosProblems1066.PachToth.SplitRealizationFinal
import ErdosProblems1066.PachToth.ClosedPlacementComponentsAssembly
import ErdosProblems1066.PachToth.IndexedCrossBlockTableConcrete
import ErdosProblems1066.PachToth.CrossBlockUpperTriangleConcrete
import ErdosProblems1066.PachToth.CrossBlockPolynomialNormalization
import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.ConcretePeriodCandidateSearch
import ErdosProblems1066.PachToth.FiniteSearchCertificate
import ErdosProblems1066.PachToth.FiniteCertificateObligationSummary
import ErdosProblems1066.PachToth.EventualRoleHingeClosure
import ErdosProblems1066.PachToth.RoleHingeFiniteFamilyBridge
import ErdosProblems1066.PachToth.SmallCaseCertificates

set_option autoImplicit false

/-!
# Exact and arbitrary `5 / 16` route matrix

This module is a Lean-level routing table for the currently checked
conditional Pach--Toth `5 / 16` facades.  It does not add geometric data.
Instead, each row records how one input shape proves both the exact
`16 * k` target and the arbitrary-`n` target, using the newest non-rigid,
small-case, split, and finite-table wrappers.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactFiveSixteenRouteMatrix

open SplitRealizationFinal
open SplitArbitraryNNonRigidBridge
open IndexedCrossBlockTableConcrete
open NonRigidConnectorSeparationFacts
open EventualRoleHingeClosure
open FiniteSearchCertificate

universe u

noncomputable section

/-- One route row: the same input shape supplies the exact target and the
arbitrary target. -/
structure RouteRow (alpha : Sort u) where
  exactTarget : alpha -> targetUpperConstructionFiveSixteen
  arbitraryTarget : alpha -> targetUpperConstructionFiveSixteenArbitrary

/-- Input for the finite-index cross-block lower-bound route. -/
structure CrossBlockLowerBoundsInput where
  family : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily
  lowerBounds : CrossBlockLowerBoundsInterface.CrossBlockLowerBounds family

/-- Input for the upper-triangle polynomial table route. -/
structure UpperTrianglePolynomialTableInput where
  family : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily
  tables : CrossBlockSqTableSearch.UpperTrianglePolynomialTableFamily family

/-- Input for the upper-triangle square-value table route. -/
structure UpperTriangleSqValueTableInput where
  family : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily
  tables : CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily family

/-- Input for the reduced upper-triangle polynomial table route: only
non-connector cross-block pairs remain as explicit inequalities. -/
structure UpperTriangleNonConnectorPolynomialTableInput where
  family : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily
  tables :
    CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTableFamily
      family

/-- Input for the reduced upper-triangle computed-value table route: only
non-connector cross-block pairs remain as explicit checked values. -/
structure UpperTriangleNonConnectorSqValueTableInput where
  family : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily
  tables :
    CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily
      family

/-- Input for the finite-index lower-table route. -/
structure IndexedCrossBlockLowerTablesInput where
  family : IndexedCrossBlockTableConcrete.RoleHingedPeriodSearchFamily
  tables : IndexedCrossBlockTableConcrete.IndexedCrossBlockLowerTableFamily
    family

/-- Input for the reduced non-connector square-distance table route.

Connector pairs are discharged by the checked non-rigid connector lemmas; this
row keeps only the remaining non-connector finite square-distance table as
explicit data. -/
structure NonConnectorSqDistanceTablesInput where
  family : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily
  tables :
    NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily
      family

/-- Search-facing finite candidate family plus the explicit separation data
needed by the fully checked exact and arbitrary routes. -/
abbrev FiniteCandidateFamilyInput : Type :=
  ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily

/-- Raw search-facing period candidates plus pointwise cross-block lower-bound
facts.  This is the unbundled field shape behind
`ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily`. -/
structure CandidateWordEquationsLowerBoundsInput where
  transitions : ConcretePeriodCandidateSearch.TransitionFacts
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equations :
    forall (k : Nat) (hk : 0 < k),
      ConcretePeriodCandidateSearch.ExactCandidateEquations
        transitions hk (word k hk)
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> FiniteGraph.LocalVertex ->
      Fin k -> FiniteGraph.LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : FiniteGraph.LocalVertex)
      (j : Fin k) (v : FiniteGraph.LocalVertex),
        Ne i j -> 1 <= lower k hk i u j v
  lower_bound :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : FiniteGraph.LocalVertex)
      (j : Fin k) (v : FiniteGraph.LocalVertex),
        Ne i j ->
          lower k hk i u j v <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint
                (ConcretePeriodCandidateSearch.transitionObligationsOfFacts
                  transitions)
                hk
                BaseTransitionRealization.exactBase
                ((word k hk).toFin)
                i u)
              (GeneratedClosedChain.generatedPoint
                (ConcretePeriodCandidateSearch.transitionObligationsOfFacts
                  transitions)
                hk
                BaseTransitionRealization.exactBase
                ((word k hk).toFin)
                j v)

/-- Concrete period-search data plus explicit cross-block lower-bound facts. -/
abbrev ConcreteCrossBlockFamilyInput : Type :=
  ConcretePeriodSearchFamily.ConcreteCrossBlockFamily

/-- The current compact finite-certificate obligation package: transition
data, one word and sixteen period equations for every positive block count,
and upper-triangle square-value tables. -/
abbrev FiniteCertificateObligationsInput : Type :=
  FiniteCertificateObligationSummary.Obligations

/-- Compact all-positive finite-search certificate with non-connector
square-value tables. -/
abbrev AllPositiveNonConnectorSqValueCertificateInput : Type :=
  FiniteSearchCertificate.AllPositiveNonConnectorSqValueCertificate

/-- Split all-positive finite-search period data plus non-connector
square-value tables. -/
structure AllPositivePeriodSearchNonConnectorSqValueInput where
  periodSearch : FiniteSearchCertificate.AllPositivePeriodSearchData
  sqValue :
    FiniteSearchCertificate.NonConnectorSqValueCertificate periodSearch

/-- Existing period-search data plus the remaining upper-triangle square-value
certificate. -/
structure PeriodSearchSqValueCertificateInput where
  periodSearch : FiniteCertificateObligationSummary.PeriodSearchData
  sqValue :
    FiniteCertificateObligationSummary.SqValueCertificate periodSearch

/-- Existing period-search data plus the raw square-value generator facts. -/
structure PeriodSearchSqValueFactsInput where
  periodSearch : FiniteCertificateObligationSummary.PeriodSearchData
  sqValue :
    forall (k : Nat), 0 < k ->
      Fin k -> FiniteCertificateObligationSummary.LocalVertexIndex ->
      Fin k -> FiniteCertificateObligationSummary.LocalVertexIndex -> Real
  sqValue_eq_polynomial_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : FiniteCertificateObligationSummary.LocalVertexIndex)
      (j : Fin k) (v : FiniteCertificateObligationSummary.LocalVertexIndex),
        i.val < j.val ->
          sqValue k hk i u j v =
            CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
              periodSearch.toRoleHingedPeriodSearchFamily hk i u j v
  sqValue_ge_one_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : FiniteCertificateObligationSummary.LocalVertexIndex)
      (j : Fin k) (v : FiniteCertificateObligationSummary.LocalVertexIndex),
        i.val < j.val -> 1 <= sqValue k hk i u j v

/-- Non-rigid component data for every positive block count. -/
abbrev ComponentFamilyInput : Type :=
  forall (k : Nat) (hk : 0 < k),
    ClosedPlacementNonRigidComponents.Components k hk

/-- The smallest explicit field package for the direct non-rigid component
route. -/
abbrev ComponentFamilyFieldsInput : Type :=
  ClosedPlacementComponentsAssembly.ComponentFamilyFields

/-- Normalized vector-backed upper-triangle certificates, consumed through the
non-connector route where cyclic connector pairs are discharged separately. -/
structure NormalizedVectorCertificateFamilyInput where
  family : CrossBlockPolynomialNormalization.RoleHingedPeriodSearchFamily
  certificates :
    CrossBlockPolynomialNormalization.UpperTriangleVectorCertificateFamily
      family

/-- Normalized list-backed upper-triangle certificates, consumed through the
non-connector route where cyclic connector pairs are discharged separately. -/
structure NormalizedListCertificateFamilyInput where
  family : CrossBlockPolynomialNormalization.RoleHingedPeriodSearchFamily
  certificates :
    CrossBlockPolynomialNormalization.UpperTriangleListCertificateFamily
      family

/-- Eventual role-hinge closure data whose block threshold is at most one.
The threshold side condition is what turns the eventual route into an exact
`16 * k` route for every positive `k`. -/
structure EventualRoleHingedClosureAtMostOneInput where
  K0 : Nat
  transitions : EventualRoleHingeClosure.RoleHingeTransitions
  orientation :
    forall (k : Nat), K0 <= k -> 0 < k ->
      Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase
        (orientation k hK hk)
  separated :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase
        (orientation k hK hk)
  threshold_at_most_one : K0 <= 1

/-- Eventual finite-certificate obligations whose block threshold is at most
one.  This is the compact search-facing spelling of the eventual closure
route. -/
structure EventualFiniteCertificateObligationsAtMostOneInput where
  K0 : Nat
  obligations : EventualRoleHingeClosure.EventualFiniteCertificateObligations K0
  threshold_at_most_one : K0 <= 1

namespace CandidateWordEquationsLowerBoundsInput

/-- Bundle the raw candidate/lower-bound fields into the checked search-family
facade. -/
def toPeriodCandidateSearchFamily
    (I : CandidateWordEquationsLowerBoundsInput) :
    ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily :=
  ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily.ofWordEquationsAndLowerBounds
    I.transitions I.word I.equations I.lower I.lower_ge_one
    I.lower_bound

/-- Exact target from raw candidate/lower-bound fields. -/
theorem targetUpperConstructionFiveSixteen
    (I : CandidateWordEquationsLowerBoundsInput) :
    targetUpperConstructionFiveSixteen :=
  I.toPeriodCandidateSearchFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary target from raw candidate/lower-bound fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (I : CandidateWordEquationsLowerBoundsInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  I.toPeriodCandidateSearchFamily.targetUpperConstructionFiveSixteenArbitrary

end CandidateWordEquationsLowerBoundsInput

namespace PeriodSearchSqValueFactsInput

/-- Bundle raw square-value facts into the checked finite-certificate
square-value certificate. -/
def toSqValueCertificate
    (I : PeriodSearchSqValueFactsInput) :
    FiniteCertificateObligationSummary.SqValueCertificate I.periodSearch where
  value := I.sqValue
  value_eq_polynomial_lt := I.sqValue_eq_polynomial_lt
  value_ge_one_lt := I.sqValue_ge_one_lt

/-- Exact target from period-search data plus raw square-value facts. -/
theorem targetUpperConstructionFiveSixteen
    (I : PeriodSearchSqValueFactsInput) :
    targetUpperConstructionFiveSixteen :=
  I.toSqValueCertificate.targetUpperConstructionFiveSixteen

/-- Arbitrary target from period-search data plus raw square-value facts. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (I : PeriodSearchSqValueFactsInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  I.toSqValueCertificate.targetUpperConstructionFiveSixteenArbitrary

end PeriodSearchSqValueFactsInput

/-- Checked small cases below one period block. -/
theorem targetUpperConstructionFiveSixteenSmallUpTo_sixteen :
    targetUpperConstructionFiveSixteenSmallUpTo 16 :=
  SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_sixteen

/-- Exact target plus the checked small cases below sixteen gives the full
arbitrary-`n` target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedSmallCases
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      16
      (fun n hn =>
        ExactFamilyClosure.targetUpperConstructionFiveSixteenAt_of_exactTarget_large
          Hexact hn)
      targetUpperConstructionFiveSixteenSmallUpTo_sixteen

namespace NormalizedVectorCertificateFamilyInput

/-- Exact target from normalized vector-backed upper-triangle certificates via
the non-connector connector-separated route. -/
theorem targetUpperConstructionFiveSixteen
    (I : NormalizedVectorCertificateFamilyInput) :
    targetUpperConstructionFiveSixteen :=
  (I.certificates.toNonConnectorSqDistanceTableFamily).targetUpperConstructionFiveSixteen

/-- Arbitrary target from normalized vector-backed upper-triangle certificates
via the non-connector connector-separated route and checked small cases. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (I : NormalizedVectorCertificateFamilyInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedSmallCases
    I.targetUpperConstructionFiveSixteen

end NormalizedVectorCertificateFamilyInput

namespace NormalizedListCertificateFamilyInput

/-- Exact target from normalized list-backed upper-triangle certificates via
the non-connector connector-separated route. -/
theorem targetUpperConstructionFiveSixteen
    (I : NormalizedListCertificateFamilyInput) :
    targetUpperConstructionFiveSixteen :=
  (I.certificates.toNonConnectorSqDistanceTableFamily).targetUpperConstructionFiveSixteen

/-- Arbitrary target from normalized list-backed upper-triangle certificates
via the non-connector connector-separated route and checked small cases. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (I : NormalizedListCertificateFamilyInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedSmallCases
    I.targetUpperConstructionFiveSixteen

end NormalizedListCertificateFamilyInput

namespace EventualRoleHingedClosureAtMostOneInput

/-- Exact target from eventual role-hinge closure data once the eventual block
threshold is at most one. -/
theorem targetUpperConstructionFiveSixteen
    (I : EventualRoleHingedClosureAtMostOneInput) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily.targetUpperConstructionFiveSixteen
      { transitions := I.transitions
        orientation := fun k hk =>
          I.orientation k (by
            have hk1 : 1 <= k := Nat.succ_le_of_lt hk
            exact le_trans I.threshold_at_most_one hk1) hk
        closure := fun k hk =>
          I.closure k (by
            have hk1 : 1 <= k := Nat.succ_le_of_lt hk
            exact le_trans I.threshold_at_most_one hk1) hk
        separated := fun k hk =>
          I.separated k (by
            have hk1 : 1 <= k := Nat.succ_le_of_lt hk
            exact le_trans I.threshold_at_most_one hk1) hk }

/-- Arbitrary target from eventual role-hinge closure data with `K0 <= 1`,
using the checked below-sixteen small cases. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (I : EventualRoleHingedClosureAtMostOneInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHingedClosure_checkedSmallCases
    I.K0 I.transitions I.orientation I.closure I.separated
    I.threshold_at_most_one

end EventualRoleHingedClosureAtMostOneInput

namespace EventualFiniteCertificateObligationsAtMostOneInput

/-- Exact target from eventual finite-certificate obligations once the
eventual block threshold is at most one. -/
theorem targetUpperConstructionFiveSixteen
    (I : EventualFiniteCertificateObligationsAtMostOneInput) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily.targetUpperConstructionFiveSixteen
      { transitions := I.obligations.transitions
        orientation := fun k hk =>
          I.obligations.orientation k (by
            have hk1 : 1 <= k := Nat.succ_le_of_lt hk
            exact le_trans I.threshold_at_most_one hk1) hk
        closure := fun k hk =>
          I.obligations.closure k (by
            have hk1 : 1 <= k := Nat.succ_le_of_lt hk
            exact le_trans I.threshold_at_most_one hk1) hk
        separated := fun k hk =>
          I.obligations.generatedSeparation k (by
            have hk1 : 1 <= k := Nat.succ_le_of_lt hk
            exact le_trans I.threshold_at_most_one hk1) hk }

/-- Arbitrary target from eventual finite-certificate obligations with
`K0 <= 1`, using the checked below-sixteen small cases. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (I : EventualFiniteCertificateObligationsAtMostOneInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  I.obligations.targetUpperConstructionFiveSixteenArbitrary_checkedSmallCases
    I.threshold_at_most_one

end EventualFiniteCertificateObligationsAtMostOneInput

/-- The route matrix.  Rows are deliberately conditional: a row says how to
turn that row's explicit data shape into the exact and arbitrary targets. -/
structure Matrix where
  exactTarget :
    RouteRow targetUpperConstructionFiveSixteen
  nonRigidClosedPlacements :
    RouteRow
      (forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk)
  nonRigidComponents :
    RouteRow
      (forall (k : Nat) (hk : 0 < k),
        ClosedPlacementNonRigidComponents.Components k hk)
  componentFamilyFields :
    RouteRow ComponentFamilyFieldsInput
  finiteSearchFamily :
    RouteRow FiniteSearchCertificate.RoleHingedFiniteSearchFamily
  allPositiveNonConnectorSqValueCertificate :
    RouteRow AllPositiveNonConnectorSqValueCertificateInput
  allPositivePeriodSearchNonConnectorSqValue :
    RouteRow AllPositivePeriodSearchNonConnectorSqValueInput
  candidateWordEquationsLowerBounds :
    RouteRow CandidateWordEquationsLowerBoundsInput
  transitionFactsFiniteSearchFamily :
    RouteRow
      RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily
  concreteCrossBlockFamily :
    RouteRow ConcreteCrossBlockFamilyInput
  finiteCertificateObligations :
    RouteRow FiniteCertificateObligationsInput
  periodSearchSqValueCertificate :
    RouteRow PeriodSearchSqValueCertificateInput
  periodSearchSqValueFacts :
    RouteRow PeriodSearchSqValueFactsInput
  eventualRoleHingedClosureAtMostOne :
    RouteRow EventualRoleHingedClosureAtMostOneInput
  eventualFiniteCertificateObligationsAtMostOne :
    RouteRow EventualFiniteCertificateObligationsAtMostOneInput
  crossBlockLowerBounds :
    RouteRow CrossBlockLowerBoundsInput
  indexedCrossBlockLowerTables :
    RouteRow IndexedCrossBlockLowerTablesInput
  indexedConcreteCrossBlock :
    RouteRow IndexedCrossBlockTableConcrete.IndexedConcreteCrossBlockFamily
  nonConnectorSqDistanceTables :
    RouteRow NonConnectorSqDistanceTablesInput
  upperTriangleNonConnectorPolynomialTables :
    RouteRow UpperTriangleNonConnectorPolynomialTableInput
  upperTriangleNonConnectorSqValueTables :
    RouteRow UpperTriangleNonConnectorSqValueTableInput
  upperTrianglePolynomialTables :
    RouteRow UpperTrianglePolynomialTableInput
  upperTriangleSqValueTables :
    RouteRow UpperTriangleSqValueTableInput
  normalizedVectorCertificateFamily :
    RouteRow NormalizedVectorCertificateFamilyInput
  normalizedListCertificateFamily :
    RouteRow NormalizedListCertificateFamilyInput
  vectorConcreteCrossBlock :
    RouteRow CrossBlockUpperTriangleConcrete.VectorConcreteCrossBlockFamily
  listConcreteCrossBlock :
    RouteRow CrossBlockUpperTriangleConcrete.ListConcreteCrossBlockFamily

/-- The checked conditional route matrix. -/
def matrix : Matrix where
  exactTarget :=
    { exactTarget := fun Hexact => Hexact
      arbitraryTarget := fun Hexact =>
        targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedSmallCases
          Hexact }
  nonRigidClosedPlacements :=
    { exactTarget := fun H =>
        NonRigidClosedPlacementInterface.targetUpperConstructionFiveSixteen_of_closedPlacements
          H
      arbitraryTarget := fun H =>
        targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
          H }
  nonRigidComponents :=
    { exactTarget := fun H =>
        ClosedPlacementNonRigidComponents.targetUpperConstructionFiveSixteen_of_components
          H
      arbitraryTarget := fun H =>
        targetUpperConstructionFiveSixteenArbitrary_of_components
          H }
  componentFamilyFields :=
    { exactTarget := fun H =>
        H.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun H =>
        H.targetUpperConstructionFiveSixteenArbitrary }
  finiteSearchFamily :=
    { exactTarget := fun F =>
        F.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun F =>
        targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedSmallCases
          F.targetUpperConstructionFiveSixteen }
  allPositiveNonConnectorSqValueCertificate :=
    { exactTarget := fun C =>
        C.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun C =>
        C.targetUpperConstructionFiveSixteenArbitrary }
  allPositivePeriodSearchNonConnectorSqValue :=
    { exactTarget := fun I =>
        let C : FiniteSearchCertificate.AllPositiveNonConnectorSqValueCertificate :=
          { periodSearch := I.periodSearch
            sqValue := I.sqValue }
        C.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        let C : FiniteSearchCertificate.AllPositiveNonConnectorSqValueCertificate :=
          { periodSearch := I.periodSearch
            sqValue := I.sqValue }
        C.targetUpperConstructionFiveSixteenArbitrary }
  candidateWordEquationsLowerBounds :=
    { exactTarget := fun I =>
        I.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.targetUpperConstructionFiveSixteenArbitrary }
  transitionFactsFiniteSearchFamily :=
    { exactTarget := fun F =>
        F.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun F =>
        targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedSmallCases
          F.targetUpperConstructionFiveSixteen }
  concreteCrossBlockFamily :=
    { exactTarget := fun F =>
        F.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun F =>
        F.targetUpperConstructionFiveSixteenArbitrary }
  finiteCertificateObligations :=
    { exactTarget := fun O =>
        O.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun O =>
        O.targetUpperConstructionFiveSixteenArbitrary }
  periodSearchSqValueCertificate :=
    { exactTarget := fun I =>
        I.sqValue.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.sqValue.targetUpperConstructionFiveSixteenArbitrary }
  periodSearchSqValueFacts :=
    { exactTarget := fun I =>
        I.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.targetUpperConstructionFiveSixteenArbitrary }
  eventualRoleHingedClosureAtMostOne :=
    { exactTarget := fun I =>
        I.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.targetUpperConstructionFiveSixteenArbitrary }
  eventualFiniteCertificateObligationsAtMostOne :=
    { exactTarget := fun I =>
        I.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.targetUpperConstructionFiveSixteenArbitrary }
  crossBlockLowerBounds :=
    { exactTarget := fun I =>
        I.lowerBounds.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.lowerBounds.targetUpperConstructionFiveSixteenArbitrary }
  indexedCrossBlockLowerTables :=
    { exactTarget := fun I =>
        IndexedCrossBlockLowerTableFamily.targetUpperConstructionFiveSixteen
          I.tables
      arbitraryTarget := fun I =>
        IndexedCrossBlockLowerTableFamily.targetUpperConstructionFiveSixteenArbitrary
          I.tables }
  indexedConcreteCrossBlock :=
    { exactTarget := fun C =>
        C.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun C =>
        C.targetUpperConstructionFiveSixteenArbitrary }
  nonConnectorSqDistanceTables :=
    { exactTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedSmallCases
          I.tables.targetUpperConstructionFiveSixteen }
  upperTriangleNonConnectorPolynomialTables :=
    { exactTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedSmallCases
          I.tables.targetUpperConstructionFiveSixteen }
  upperTriangleNonConnectorSqValueTables :=
    { exactTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedSmallCases
          I.tables.targetUpperConstructionFiveSixteen }
  upperTrianglePolynomialTables :=
    { exactTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteenArbitrary }
  upperTriangleSqValueTables :=
    { exactTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteenArbitrary }
  normalizedVectorCertificateFamily :=
    { exactTarget := fun I =>
        I.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.targetUpperConstructionFiveSixteenArbitrary }
  normalizedListCertificateFamily :=
    { exactTarget := fun I =>
        I.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.targetUpperConstructionFiveSixteenArbitrary }
  vectorConcreteCrossBlock :=
    { exactTarget := fun C =>
        C.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun C =>
        C.targetUpperConstructionFiveSixteenArbitrary }
  listConcreteCrossBlock :=
    { exactTarget := fun C =>
        C.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun C =>
        C.targetUpperConstructionFiveSixteenArbitrary }

/-- Compact checklist for the shortest currently exposed fully formal routes.

This is only a facade over checked conditional implications: it records the
current compact finite-certificate, reduced non-connector, raw candidate, and
direct non-rigid component input shapes that reach both target facades.  It
does not assert that any input has been supplied, and it is not a global
minimality theorem about all possible future routes. -/
structure ShortestRouteChecklist where
  finiteCertificateObligations :
    RouteRow FiniteCertificateObligationsInput
  periodSearchSqValueCertificate :
    RouteRow PeriodSearchSqValueCertificateInput
  periodSearchSqValueFacts :
    RouteRow PeriodSearchSqValueFactsInput
  allPositiveNonConnectorSqValueCertificate :
    RouteRow AllPositiveNonConnectorSqValueCertificateInput
  allPositivePeriodSearchNonConnectorSqValue :
    RouteRow AllPositivePeriodSearchNonConnectorSqValueInput
  eventualRoleHingedClosureAtMostOne :
    RouteRow EventualRoleHingedClosureAtMostOneInput
  eventualFiniteCertificateObligationsAtMostOne :
    RouteRow EventualFiniteCertificateObligationsAtMostOneInput
  finiteCandidateFamily :
    RouteRow FiniteCandidateFamilyInput
  candidateWordEquationsLowerBounds :
    RouteRow CandidateWordEquationsLowerBoundsInput
  concreteCrossBlockFamily :
    RouteRow ConcreteCrossBlockFamilyInput
  componentFamilyFields :
    RouteRow ComponentFamilyFieldsInput
  components :
    RouteRow ComponentFamilyInput
  nonConnectorSqDistanceTables :
    RouteRow NonConnectorSqDistanceTablesInput
  upperTriangleNonConnectorPolynomialTables :
    RouteRow UpperTriangleNonConnectorPolynomialTableInput
  upperTriangleNonConnectorSqValueTables :
    RouteRow UpperTriangleNonConnectorSqValueTableInput
  normalizedVectorCertificateFamily :
    RouteRow NormalizedVectorCertificateFamilyInput
  normalizedListCertificateFamily :
    RouteRow NormalizedListCertificateFamilyInput

/-- The current shortest checked conditional route checklist from compact
finite certificates, reduced non-connector tables, raw candidates, or
non-rigid components to the exact and arbitrary targets. -/
def shortestRouteChecklist : ShortestRouteChecklist where
  finiteCertificateObligations :=
    matrix.finiteCertificateObligations
  periodSearchSqValueCertificate :=
    matrix.periodSearchSqValueCertificate
  periodSearchSqValueFacts :=
    matrix.periodSearchSqValueFacts
  allPositiveNonConnectorSqValueCertificate :=
    matrix.allPositiveNonConnectorSqValueCertificate
  allPositivePeriodSearchNonConnectorSqValue :=
    matrix.allPositivePeriodSearchNonConnectorSqValue
  eventualRoleHingedClosureAtMostOne :=
    matrix.eventualRoleHingedClosureAtMostOne
  eventualFiniteCertificateObligationsAtMostOne :=
    matrix.eventualFiniteCertificateObligationsAtMostOne
  finiteCandidateFamily :=
    { exactTarget := fun F =>
        F.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun F =>
        F.targetUpperConstructionFiveSixteenArbitrary }
  candidateWordEquationsLowerBounds :=
    matrix.candidateWordEquationsLowerBounds
  concreteCrossBlockFamily :=
    matrix.concreteCrossBlockFamily
  componentFamilyFields :=
    matrix.componentFamilyFields
  components :=
    matrix.nonRigidComponents
  nonConnectorSqDistanceTables :=
    matrix.nonConnectorSqDistanceTables
  upperTriangleNonConnectorPolynomialTables :=
    matrix.upperTriangleNonConnectorPolynomialTables
  upperTriangleNonConnectorSqValueTables :=
    matrix.upperTriangleNonConnectorSqValueTables
  normalizedVectorCertificateFamily :=
    matrix.normalizedVectorCertificateFamily
  normalizedListCertificateFamily :=
    matrix.normalizedListCertificateFamily

/-- Exact target from the compact finite-certificate obligation package. -/
theorem targetUpperConstructionFiveSixteen_of_finiteCertificateObligations
    (O : FiniteCertificateObligationsInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.finiteCertificateObligations.exactTarget O

/-- Arbitrary target from the compact finite-certificate obligation package. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_finiteCertificateObligations
    (O : FiniteCertificateObligationsInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.finiteCertificateObligations.arbitraryTarget O

/-- Exact target from period-search data plus a square-value certificate. -/
theorem targetUpperConstructionFiveSixteen_of_periodSearchSqValueCertificate
    (I : PeriodSearchSqValueCertificateInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.periodSearchSqValueCertificate.exactTarget I

/-- Arbitrary target from period-search data plus a square-value certificate. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchSqValueCertificate
    (I : PeriodSearchSqValueCertificateInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.periodSearchSqValueCertificate.arbitraryTarget I

/-- Exact target from a dependent square-value certificate over fixed
period-search data. -/
theorem targetUpperConstructionFiveSixteen_of_sqValueCertificate
    {periodSearch : FiniteCertificateObligationSummary.PeriodSearchData}
    (S :
      FiniteCertificateObligationSummary.SqValueCertificate periodSearch) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_periodSearchSqValueCertificate
    { periodSearch := periodSearch
      sqValue := S }

/-- Arbitrary target from a dependent square-value certificate over fixed
period-search data. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_sqValueCertificate
    {periodSearch : FiniteCertificateObligationSummary.PeriodSearchData}
    (S :
      FiniteCertificateObligationSummary.SqValueCertificate periodSearch) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_periodSearchSqValueCertificate
    { periodSearch := periodSearch
      sqValue := S }

/-- Exact target from period-search data plus raw square-value facts. -/
theorem targetUpperConstructionFiveSixteen_of_periodSearchSqValueFacts
    (I : PeriodSearchSqValueFactsInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.periodSearchSqValueFacts.exactTarget I

/-- Arbitrary target from period-search data plus raw square-value facts. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchSqValueFacts
    (I : PeriodSearchSqValueFactsInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.periodSearchSqValueFacts.arbitraryTarget I

/-- Exact target from the finite candidate-family route in
`shortestRouteChecklist`. -/
theorem targetUpperConstructionFiveSixteen_of_finiteCandidateFamily
    (F : FiniteCandidateFamilyInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.finiteCandidateFamily.exactTarget F

/-- Arbitrary target from the finite candidate-family route in
`shortestRouteChecklist`. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_finiteCandidateFamily
    (F : FiniteCandidateFamilyInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.finiteCandidateFamily.arbitraryTarget F

/-- Exact target from raw word/equation/lower-bound candidate fields. -/
theorem targetUpperConstructionFiveSixteen_of_candidateWordEquationsLowerBounds
    (I : CandidateWordEquationsLowerBoundsInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.candidateWordEquationsLowerBounds.exactTarget I

/-- Arbitrary target from raw word/equation/lower-bound candidate fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateWordEquationsLowerBounds
    (I : CandidateWordEquationsLowerBoundsInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.candidateWordEquationsLowerBounds.arbitraryTarget I

/-- Exact target from concrete period-search data and cross-block lower-bound
facts. -/
theorem targetUpperConstructionFiveSixteen_of_concreteCrossBlockFamily
    (F : ConcreteCrossBlockFamilyInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.concreteCrossBlockFamily.exactTarget F

/-- Arbitrary target from concrete period-search data and cross-block
lower-bound facts. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteCrossBlockFamily
    (F : ConcreteCrossBlockFamilyInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.concreteCrossBlockFamily.arbitraryTarget F

/-- Exact target from the direct non-rigid component field package in
`shortestRouteChecklist`. -/
theorem targetUpperConstructionFiveSixteen_of_componentFamilyFields
    (H : ComponentFamilyFieldsInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.componentFamilyFields.exactTarget H

/-- Arbitrary target from the direct non-rigid component field package in
`shortestRouteChecklist`. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_componentFamilyFields
    (H : ComponentFamilyFieldsInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.componentFamilyFields.arbitraryTarget H

/-- Exact target from the component-family route in
`shortestRouteChecklist`. -/
theorem targetUpperConstructionFiveSixteen_of_componentFamily
    (H : ComponentFamilyInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.components.exactTarget H

/-- Arbitrary target from the component-family route in
`shortestRouteChecklist`. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_componentFamily
    (H : ComponentFamilyInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.components.arbitraryTarget H

/-- Exact target from reduced non-connector cross-block square-distance
tables in `shortestRouteChecklist`. -/
theorem targetUpperConstructionFiveSixteen_of_nonConnectorSqDistanceTables
    (I : NonConnectorSqDistanceTablesInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.nonConnectorSqDistanceTables.exactTarget I

/-- Arbitrary target from reduced non-connector cross-block square-distance
tables in `shortestRouteChecklist`. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_nonConnectorSqDistanceTables
    (I : NonConnectorSqDistanceTablesInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.nonConnectorSqDistanceTables.arbitraryTarget I

/-- Exact target from reduced upper-triangle non-connector polynomial tables. -/
theorem targetUpperConstructionFiveSixteen_of_upperTriangleNonConnectorPolynomialTables
    (I : UpperTriangleNonConnectorPolynomialTableInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.upperTriangleNonConnectorPolynomialTables.exactTarget I

/-- Arbitrary target from reduced upper-triangle non-connector polynomial
tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleNonConnectorPolynomialTables
    (I : UpperTriangleNonConnectorPolynomialTableInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.upperTriangleNonConnectorPolynomialTables.arbitraryTarget I

/-- Exact target from a dependent reduced upper-triangle non-connector
polynomial table family. -/
theorem targetUpperConstructionFiveSixteen_of_upperTriangleNonConnectorPolynomialTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T :
      CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTableFamily
        F) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_upperTriangleNonConnectorPolynomialTables
    { family := F
      tables := T }

/-- Arbitrary target from a dependent reduced upper-triangle non-connector
polynomial table family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_nonConnectorPolynomialTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T :
      CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTableFamily
        F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleNonConnectorPolynomialTables
    { family := F
      tables := T }

/-- Compatibility spelling for the dependent reduced upper-triangle
non-connector polynomial table route. -/
theorem
    targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleNonConnectorPolynomialTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T :
      CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTableFamily
        F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_nonConnectorPolynomialTableFamily
    T

/-- Exact target from reduced upper-triangle non-connector square-value
tables. -/
theorem targetUpperConstructionFiveSixteen_of_upperTriangleNonConnectorSqValueTables
    (I : UpperTriangleNonConnectorSqValueTableInput) :
    targetUpperConstructionFiveSixteen :=
  shortestRouteChecklist.upperTriangleNonConnectorSqValueTables.exactTarget I

/-- Arbitrary target from reduced upper-triangle non-connector square-value
tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleNonConnectorSqValueTables
    (I : UpperTriangleNonConnectorSqValueTableInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  shortestRouteChecklist.upperTriangleNonConnectorSqValueTables.arbitraryTarget I

/-- Exact target from a dependent reduced upper-triangle non-connector
square-value table family. -/
theorem targetUpperConstructionFiveSixteen_of_upperTriangleNonConnectorSqValueTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T :
      CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily F) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_upperTriangleNonConnectorSqValueTables
    { family := F
      tables := T }

/-- Arbitrary target from a dependent reduced upper-triangle non-connector
square-value table family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleNonConnectorSqValueTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T :
      CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleNonConnectorSqValueTables
    { family := F
      tables := T }

/-- The exact-target row exposed from the route matrix. -/
theorem targetUpperConstructionFiveSixteen_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteen :=
  matrix.exactTarget.exactTarget Hexact

/-- Exact-to-arbitrary split route, exposed from the route matrix. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactTarget.arbitraryTarget Hexact

/-- Exact target from checked non-rigid closed placements. -/
theorem targetUpperConstructionFiveSixteen_of_nonRigidClosedPlacements
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteen :=
  matrix.nonRigidClosedPlacements.exactTarget H

/-- Arbitrary target from checked non-rigid closed placements via the split
route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_nonRigidClosedPlacements
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.nonRigidClosedPlacements.arbitraryTarget H

/-- Exact target from concrete non-rigid component fields. -/
theorem targetUpperConstructionFiveSixteen_of_nonRigidComponents
    (H :
      forall (k : Nat) (hk : 0 < k),
        ClosedPlacementNonRigidComponents.Components k hk) :
    targetUpperConstructionFiveSixteen :=
  matrix.nonRigidComponents.exactTarget H

/-- Arbitrary target from concrete non-rigid component fields via the split
route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_nonRigidComponents
    (H :
      forall (k : Nat) (hk : 0 < k),
        ClosedPlacementNonRigidComponents.Components k hk) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.nonRigidComponents.arbitraryTarget H

/-- Exact target from a finite search family. -/
theorem targetUpperConstructionFiveSixteen_of_finiteSearchFamily
    (F : FiniteSearchCertificate.RoleHingedFiniteSearchFamily) :
    targetUpperConstructionFiveSixteen :=
  matrix.finiteSearchFamily.exactTarget F

/-- Arbitrary target from a finite search family, routed through the split
exact-to-arbitrary bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_finiteSearchFamily
    (F : FiniteSearchCertificate.RoleHingedFiniteSearchFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.finiteSearchFamily.arbitraryTarget F

/-- Exact target from the compact all-positive non-connector square-value
finite-search certificate. -/
theorem targetUpperConstructionFiveSixteen_of_allPositiveNonConnectorSqValueCertificate
    (C : AllPositiveNonConnectorSqValueCertificateInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.allPositiveNonConnectorSqValueCertificate.exactTarget C

/-- Arbitrary target from the compact all-positive non-connector square-value
finite-search certificate. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_allPositiveNonConnectorSqValueCertificate
    (C : AllPositiveNonConnectorSqValueCertificateInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.allPositiveNonConnectorSqValueCertificate.arbitraryTarget C

/-- Exact target from all-positive period-search data plus non-connector
square-value tables. -/
theorem targetUpperConstructionFiveSixteen_of_allPositivePeriodSearchNonConnectorSqValue
    (I : AllPositivePeriodSearchNonConnectorSqValueInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.allPositivePeriodSearchNonConnectorSqValue.exactTarget I

/-- Arbitrary target from all-positive period-search data plus non-connector
square-value tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_allPositivePeriodSearchNonConnectorSqValue
    (I : AllPositivePeriodSearchNonConnectorSqValueInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.allPositivePeriodSearchNonConnectorSqValue.arbitraryTarget I

/-- Exact target from a dependent all-positive period-search package and its
non-connector square-value certificate. -/
theorem targetUpperConstructionFiveSixteen_of_allPositivePeriodSearchData_nonConnectorSqValue
    (periodSearch : FiniteSearchCertificate.AllPositivePeriodSearchData)
    (sqValue :
      FiniteSearchCertificate.NonConnectorSqValueCertificate periodSearch) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_allPositivePeriodSearchNonConnectorSqValue
    { periodSearch := periodSearch
      sqValue := sqValue }

/-- Arbitrary target from a dependent all-positive period-search package and
its non-connector square-value certificate. -/
theorem
    targetUpperConstructionFiveSixteenArbitrary_of_allPositivePeriodSearchData_nonConnectorSqValue
    (periodSearch : FiniteSearchCertificate.AllPositivePeriodSearchData)
    (sqValue :
      FiniteSearchCertificate.NonConnectorSqValueCertificate periodSearch) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_allPositivePeriodSearchNonConnectorSqValue
    { periodSearch := periodSearch
      sqValue := sqValue }

/-- Exact target from search-facing role-hinge transition facts and finite
data. -/
theorem targetUpperConstructionFiveSixteen_of_transitionFactsFiniteSearchFamily
    (F : RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily) :
    targetUpperConstructionFiveSixteen :=
  matrix.transitionFactsFiniteSearchFamily.exactTarget F

/-- Arbitrary target from search-facing role-hinge transition facts and finite
data. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionFactsFiniteSearchFamily
    (F : RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.transitionFactsFiniteSearchFamily.arbitraryTarget F

/-- Exact target from the compact finite-certificate obligation package,
exposed from the route matrix. -/
theorem targetUpperConstructionFiveSixteen_of_finiteCertificateObligationPackage
    (O : FiniteCertificateObligationsInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.finiteCertificateObligations.exactTarget O

/-- Arbitrary target from the compact finite-certificate obligation package,
exposed from the route matrix. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_finiteCertificateObligationPackage
    (O : FiniteCertificateObligationsInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.finiteCertificateObligations.arbitraryTarget O

/-- Exact target from eventual role-hinge closure data, conditional on
eventual block threshold at most one. -/
theorem targetUpperConstructionFiveSixteen_of_eventualRoleHingedClosureAtMostOne
    (I : EventualRoleHingedClosureAtMostOneInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.eventualRoleHingedClosureAtMostOne.exactTarget I

/-- Arbitrary target from eventual role-hinge closure data, conditional on
eventual block threshold at most one. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualRoleHingedClosureAtMostOne
    (I : EventualRoleHingedClosureAtMostOneInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualRoleHingedClosureAtMostOne.arbitraryTarget I

/-- Exact target from eventual finite-certificate obligations, conditional on
eventual block threshold at most one. -/
theorem targetUpperConstructionFiveSixteen_of_eventualFiniteCertificateObligationsAtMostOne
    (I : EventualFiniteCertificateObligationsAtMostOneInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.eventualFiniteCertificateObligationsAtMostOne.exactTarget I

/-- Arbitrary target from eventual finite-certificate obligations, conditional
on eventual block threshold at most one. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualFiniteCertificateObligationsAtMostOne
    (I : EventualFiniteCertificateObligationsAtMostOneInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualFiniteCertificateObligationsAtMostOne.arbitraryTarget I

/-- Arbitrary target from eventual finite-certificate obligations from one
block onward.  No exact target is hidden here; the exact theorem above uses
the explicit threshold-at-most-one input package. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualFiniteCertificateObligations_one
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations 1) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_eventualFiniteCertificateObligationsAtMostOne
    { K0 := 1
      obligations := O
      threshold_at_most_one := by norm_num }

/-- Exact target from period-search data plus finite-index cross-block lower
bounds. -/
theorem targetUpperConstructionFiveSixteen_of_crossBlockLowerBounds
    (I : CrossBlockLowerBoundsInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.crossBlockLowerBounds.exactTarget I

/-- Arbitrary target from period-search data plus finite-index cross-block
lower bounds. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLowerBounds
    (I : CrossBlockLowerBoundsInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.crossBlockLowerBounds.arbitraryTarget I

/-- Exact target from a dependent cross-block lower-bound family. -/
theorem targetUpperConstructionFiveSixteen_of_crossBlockLowerBoundsFamily
    {F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F) :
    targetUpperConstructionFiveSixteen :=
  matrix.crossBlockLowerBounds.exactTarget
    { family := F
      lowerBounds := H }

/-- Arbitrary target from a dependent cross-block lower-bound family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLowerBoundsFamily
    {F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.crossBlockLowerBounds.arbitraryTarget
    { family := F
      lowerBounds := H }

/-- Exact target from finite-index cross-block lower tables. -/
theorem targetUpperConstructionFiveSixteen_of_indexedCrossBlockLowerTables
    (I : IndexedCrossBlockLowerTablesInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.indexedCrossBlockLowerTables.exactTarget I

/-- Arbitrary target from finite-index cross-block lower tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_indexedCrossBlockLowerTables
    (I : IndexedCrossBlockLowerTablesInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.indexedCrossBlockLowerTables.arbitraryTarget I

/-- Exact target from a dependent finite-index cross-block lower-table
family. -/
theorem targetUpperConstructionFiveSixteen_of_indexedCrossBlockLowerTableFamily
    {F : IndexedCrossBlockTableConcrete.RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockTableConcrete.IndexedCrossBlockLowerTableFamily F) :
    targetUpperConstructionFiveSixteen :=
  matrix.indexedCrossBlockLowerTables.exactTarget
    { family := F
      tables := T }

/-- Arbitrary target from a dependent finite-index cross-block lower-table
family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_indexedCrossBlockLowerTableFamily
    {F : IndexedCrossBlockTableConcrete.RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockTableConcrete.IndexedCrossBlockLowerTableFamily F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.indexedCrossBlockLowerTables.arbitraryTarget
    { family := F
      tables := T }

/-- Exact target from concrete period-search data plus finite-index lower
tables. -/
theorem targetUpperConstructionFiveSixteen_of_indexedConcreteCrossBlock
    (C : IndexedCrossBlockTableConcrete.IndexedConcreteCrossBlockFamily) :
    targetUpperConstructionFiveSixteen :=
  matrix.indexedConcreteCrossBlock.exactTarget C

/-- Arbitrary target from concrete period-search data plus finite-index lower
tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_indexedConcreteCrossBlock
    (C : IndexedCrossBlockTableConcrete.IndexedConcreteCrossBlockFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.indexedConcreteCrossBlock.arbitraryTarget C

/-- Exact target from a dependent reduced non-connector square-distance table
family. -/
theorem targetUpperConstructionFiveSixteen_of_nonConnectorSqDistanceTableFamily
    {F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily}
    (T :
      NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily
        F) :
    targetUpperConstructionFiveSixteen :=
  matrix.nonConnectorSqDistanceTables.exactTarget
    { family := F
      tables := T }

/-- Arbitrary target from a dependent reduced non-connector square-distance
table family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_nonConnectorSqDistanceTableFamily
    {F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily}
    (T :
      NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily
        F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.nonConnectorSqDistanceTables.arbitraryTarget
    { family := F
      tables := T }

/-- Exact target from an upper-triangle polynomial table family. -/
theorem targetUpperConstructionFiveSixteen_of_upperTrianglePolynomialTables
    (I : UpperTrianglePolynomialTableInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.upperTrianglePolynomialTables.exactTarget I

/-- Arbitrary target from an upper-triangle polynomial table family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTrianglePolynomialTables
    (I : UpperTrianglePolynomialTableInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.upperTrianglePolynomialTables.arbitraryTarget I

/-- Exact target from a dependent upper-triangle polynomial table family. -/
theorem targetUpperConstructionFiveSixteen_of_upperTrianglePolynomialTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTrianglePolynomialTableFamily F) :
    targetUpperConstructionFiveSixteen :=
  matrix.upperTrianglePolynomialTables.exactTarget
    { family := F
      tables := T }

/-- Arbitrary target from a dependent upper-triangle polynomial table family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTrianglePolynomialTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTrianglePolynomialTableFamily F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.upperTrianglePolynomialTables.arbitraryTarget
    { family := F
      tables := T }

/-- Exact target from an upper-triangle computed square-value table family. -/
theorem targetUpperConstructionFiveSixteen_of_upperTriangleSqValueTables
    (I : UpperTriangleSqValueTableInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.upperTriangleSqValueTables.exactTarget I

/-- Arbitrary target from an upper-triangle computed square-value table
family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleSqValueTables
    (I : UpperTriangleSqValueTableInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.upperTriangleSqValueTables.arbitraryTarget I

/-- Exact target from a dependent upper-triangle computed square-value table
family. -/
theorem targetUpperConstructionFiveSixteen_of_upperTriangleSqValueTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily F) :
    targetUpperConstructionFiveSixteen :=
  matrix.upperTriangleSqValueTables.exactTarget
    { family := F
      tables := T }

/-- Arbitrary target from a dependent upper-triangle computed square-value
table family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleSqValueTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.upperTriangleSqValueTables.arbitraryTarget
    { family := F
      tables := T }

/-- Exact target from normalized vector-backed upper-triangle certificates via
the non-connector connector-separated route. -/
theorem targetUpperConstructionFiveSixteen_of_normalizedVectorCertificateFamily
    (I : NormalizedVectorCertificateFamilyInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.normalizedVectorCertificateFamily.exactTarget I

/-- Arbitrary target from normalized vector-backed upper-triangle certificates
via the non-connector connector-separated route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_normalizedVectorCertificateFamily
    (I : NormalizedVectorCertificateFamilyInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.normalizedVectorCertificateFamily.arbitraryTarget I

/-- Exact target from a dependent normalized vector-backed upper-triangle
certificate family. -/
theorem targetUpperConstructionFiveSixteen_of_normalizedVectorCertificateFamily'
    {F : CrossBlockPolynomialNormalization.RoleHingedPeriodSearchFamily}
    (C :
      CrossBlockPolynomialNormalization.UpperTriangleVectorCertificateFamily
        F) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_normalizedVectorCertificateFamily
    { family := F
      certificates := C }

/-- Arbitrary target from a dependent normalized vector-backed upper-triangle
certificate family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_normalizedVectorCertificateFamily'
    {F : CrossBlockPolynomialNormalization.RoleHingedPeriodSearchFamily}
    (C :
      CrossBlockPolynomialNormalization.UpperTriangleVectorCertificateFamily
        F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_normalizedVectorCertificateFamily
    { family := F
      certificates := C }

/-- Exact target from normalized list-backed upper-triangle certificates via
the non-connector connector-separated route. -/
theorem targetUpperConstructionFiveSixteen_of_normalizedListCertificateFamily
    (I : NormalizedListCertificateFamilyInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.normalizedListCertificateFamily.exactTarget I

/-- Arbitrary target from normalized list-backed upper-triangle certificates
via the non-connector connector-separated route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_normalizedListCertificateFamily
    (I : NormalizedListCertificateFamilyInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.normalizedListCertificateFamily.arbitraryTarget I

/-- Exact target from a dependent normalized list-backed upper-triangle
certificate family. -/
theorem targetUpperConstructionFiveSixteen_of_normalizedListCertificateFamily'
    {F : CrossBlockPolynomialNormalization.RoleHingedPeriodSearchFamily}
    (C :
      CrossBlockPolynomialNormalization.UpperTriangleListCertificateFamily
        F) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_normalizedListCertificateFamily
    { family := F
      certificates := C }

/-- Arbitrary target from a dependent normalized list-backed upper-triangle
certificate family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_normalizedListCertificateFamily'
    {F : CrossBlockPolynomialNormalization.RoleHingedPeriodSearchFamily}
    (C :
      CrossBlockPolynomialNormalization.UpperTriangleListCertificateFamily
        F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_normalizedListCertificateFamily
    { family := F
      certificates := C }

/-- Exact target from concrete vector-backed upper-triangle tables. -/
theorem targetUpperConstructionFiveSixteen_of_vectorConcreteCrossBlock
    (C : CrossBlockUpperTriangleConcrete.VectorConcreteCrossBlockFamily) :
    targetUpperConstructionFiveSixteen :=
  matrix.vectorConcreteCrossBlock.exactTarget C

/-- Arbitrary target from concrete vector-backed upper-triangle tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_vectorConcreteCrossBlock
    (C : CrossBlockUpperTriangleConcrete.VectorConcreteCrossBlockFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.vectorConcreteCrossBlock.arbitraryTarget C

/-- Exact target from concrete list-backed upper-triangle tables. -/
theorem targetUpperConstructionFiveSixteen_of_listConcreteCrossBlock
    (C : CrossBlockUpperTriangleConcrete.ListConcreteCrossBlockFamily) :
    targetUpperConstructionFiveSixteen :=
  matrix.listConcreteCrossBlock.exactTarget C

/-- Arbitrary target from concrete list-backed upper-triangle tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_listConcreteCrossBlock
    (C : CrossBlockUpperTriangleConcrete.ListConcreteCrossBlockFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.listConcreteCrossBlock.arbitraryTarget C

end

end ExactFiveSixteenRouteMatrix
end PachToth
end ErdosProblems1066
