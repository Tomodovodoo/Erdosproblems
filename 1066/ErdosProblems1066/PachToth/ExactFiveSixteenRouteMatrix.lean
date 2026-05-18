import ErdosProblems1066.PachToth.SplitArbitraryNNonRigidBridge
import ErdosProblems1066.PachToth.SplitRealizationFinal
import ErdosProblems1066.PachToth.ClosedPlacementComponentsAssembly
import ErdosProblems1066.PachToth.IndexedCrossBlockTableConcrete
import ErdosProblems1066.PachToth.CrossBlockUpperTriangleConcrete
import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.ConcretePeriodCandidateSearch
import ErdosProblems1066.PachToth.FiniteCertificateObligationSummary
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
  FiniteCertificateObligationSummary.targetUpperConstructionFiveSixteen_of_periodSearchData_sqValueCertificate
    I.periodSearch I.toSqValueCertificate

/-- Arbitrary target from period-search data plus raw square-value facts. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (I : PeriodSearchSqValueFactsInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  FiniteCertificateObligationSummary.targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_sqValueFacts
    I.periodSearch I.sqValue I.sqValue_eq_polynomial_lt
    I.sqValue_ge_one_lt

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
        FiniteCertificateObligationSummary.targetUpperConstructionFiveSixteen_of_periodSearchData_sqValueCertificate
          I.periodSearch I.sqValue
      arbitraryTarget := fun I =>
        FiniteCertificateObligationSummary.targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_sqValueCertificate
          I.periodSearch I.sqValue }
  periodSearchSqValueFacts :=
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
        IndexedNonConnectorCrossBlockSqDistanceTableFamily.targetUpperConstructionFiveSixteen
          I.tables
      arbitraryTarget := fun I =>
        targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedSmallCases
          (IndexedNonConnectorCrossBlockSqDistanceTableFamily.targetUpperConstructionFiveSixteen
            I.tables) }
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
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleNonConnectorPolynomialTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T :
      CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTableFamily
        F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleNonConnectorPolynomialTables
    { family := F
      tables := T }

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
