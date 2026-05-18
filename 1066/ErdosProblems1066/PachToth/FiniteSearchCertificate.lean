import ErdosProblems1066.PachToth.PeriodCertificateExamples
import ErdosProblems1066.PachToth.GeneratedMetricClosure
import ErdosProblems1066.PachToth.GeneratedSeparationFarApart
import ErdosProblems1066.PachToth.CrossBlockSqTableSearch

set_option autoImplicit false

/-!
# Finite search certificate wrapper

This module is a Lean-side wrapper for finite search output.  It packages a
candidate orientation word, exact indexed period equations, and explicit
cross-block lower-bound data, then projects those fields to the generated
closure and separation interfaces already used downstream.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FiniteSearchCertificate

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev Orientation := OrientationWord.Orientation
abbrev RoleHingeTransitions := GeneratedMetricClosure.RoleHingeTransitions
abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily
abbrev LocalVertexIndex := CrossBlockSqTableSearch.LocalVertexIndex
abbrev UpperTriangleNonConnectorSqValueTable :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTable
abbrev UpperTriangleNonConnectorSqValueTableFamily :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily
abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily

/-- The period-search finite word associated to an `OrientationWord.SearchData`
candidate. -/
def finiteWordOfSearchData
    (D : OrientationWord.SearchData) :
    PeriodSearchInterface.FiniteOrientationWord :=
  PeriodCertificateExamples.finiteOrientationWordOfSearchData D

@[simp]
theorem finiteWordOfSearchData_length
    (D : OrientationWord.SearchData) :
    (finiteWordOfSearchData D).length = D.k :=
  rfl

@[simp]
theorem finiteWordOfSearchData_letter
    (D : OrientationWord.SearchData) (i : Fin D.k) :
    (finiteWordOfSearchData D).letter i = D.orientation i :=
  rfl

/-- One finite role-hinged certificate for a candidate period word.

The fields are exactly the remaining finite data: a positive orientation word,
the indexed algebraic period equations for the sixteen local vertices, and
cross-block lower bounds for distinct generated blocks. -/
structure RoleHingedCandidateCertificate
    (T : RoleHingeTransitions) where
  data : OrientationWord.SearchData
  period :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (finiteWordOfSearchData data)
  lower :
    Fin data.k -> LocalVertex -> Fin data.k -> LocalVertex -> Real
  lower_ge_one :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      lower
  lower_bound :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      T.toFigure2TransitionObligations
      data.hk
      BaseTransitionRealization.exactBase
      data.orientation
      lower

namespace RoleHingedCandidateCertificate

/-- The finite word consumed by `PeriodSearchInterface`. -/
def finiteWord
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    PeriodSearchInterface.FiniteOrientationWord :=
  finiteWordOfSearchData C.data

/-- Repackage the stored data as a standard period-search certificate. -/
def toPeriodSearchCertificate
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    PeriodSearchInterface.PeriodSearchCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase where
  word := C.finiteWord
  period := C.period

/-- The stored indexed algebraic equations imply generated closure for the
candidate word. -/
def closure
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    PeriodInterface.GeneratedClosureEquation
      T.toFigure2TransitionObligations
      C.data.hk
      BaseTransitionRealization.exactBase
      C.data.orientation := by
  simpa [finiteWord, finiteWordOfSearchData] using
    C.period.toGeneratedClosureEquation

/-- The same indexed equations also imply the generated period equation. -/
def periodEquation
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    PeriodInterface.GeneratedPeriodEquation
      T.toFigure2TransitionObligations
      C.data.hk
      BaseTransitionRealization.exactBase
      C.data.orientation := by
  simpa [finiteWord, finiteWordOfSearchData] using
    C.period.toGeneratedPeriodEquation

/-- Cross-block lower bounds plus the exact base metric supply global
generated separation for the candidate word. -/
def separated
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      T.toFigure2TransitionObligations
      C.data.hk
      BaseTransitionRealization.exactBase
      C.data.orientation :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
    T.toFigure2TransitionObligations
    C.data.hk
    BaseTransitionRealization.exactBase
    C.data.orientation
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
    (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances T)
    C.lower
    C.lower_ge_one
    C.lower_bound

/-- The reduced metric package associated to the candidate certificate. -/
def reducedMetricHypotheses
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      T.toFigure2TransitionObligations
      C.data.hk
      BaseTransitionRealization.exactBase
      C.data.orientation where
  separated := C.separated
  base_same_block_isometry :=
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances :=
    GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances T

/-- Forget the candidate certificate to the generated-closure data wrapper. -/
def toRoleHingedGeneratedClosureData
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureData C.data.k C.data.hk
      where
  transitions := T
  orientation := C.data.orientation
  closure := C.closure
  separated := C.separated

/-- A finite candidate certificate gives the exact-block target at its period
length. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    targetUpperConstructionFiveSixteenAt (16 * C.data.k) := by
  let G := C.toRoleHingedGeneratedClosureData
  exact G.targetUpperConstructionFiveSixteenAt_exactBlock

end RoleHingedCandidateCertificate

/-- A family version of the finite wrapper, with one role-hinged transition
package and one candidate word/lower-bound table for every positive length. -/
structure RoleHingedFiniteSearchFamily where
  transitions : RoleHingeTransitions
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  period :
    forall (k : Nat) (hk : 0 < k),
      PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (PeriodCertificateExamples.finiteOrientationWordOfWord hk
          (word k hk))
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
        (lower k hk)
  lower_bound :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((word k hk).toFin)
        (lower k hk)

namespace RoleHingedFiniteSearchFamily

/-- The raw orientation function expected by generated-chain APIs. -/
def orientation
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

/-- The indexed period certificate projected to generated closure for one
positive length. -/
def closure
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) := by
  simpa [orientation, PeriodCertificateExamples.finiteOrientationWordOfWord]
    using (F.period k hk).toGeneratedClosureEquation

/-- The indexed period certificate projected to generated period for one
positive length. -/
def periodEquation
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) := by
  simpa [orientation, PeriodCertificateExamples.finiteOrientationWordOfWord]
    using (F.period k hk).toGeneratedPeriodEquation

/-- Cross-block lower bounds projected to generated global separation for one
positive length. -/
def separated
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
    F.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk)
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
    (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      F.transitions)
    (F.lower k hk)
    (F.lower_ge_one k hk)
    (F.lower_bound k hk)

/-- The reduced metric package obtained from one family member. -/
def reducedMetricHypotheses
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) where
  separated := F.separated k hk
  base_same_block_isometry :=
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances :=
    GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      F.transitions

/-- Forget the finite search family to the generated-closure family facade. -/
def toRoleHingedGeneratedClosureFamily
    (F : RoleHingedFiniteSearchFamily) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily where
  transitions := F.transitions
  orientation := F.orientation
  closure := F.closure
  separated := F.separated

/-- One member of the finite search family gives the exact-block target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  let G : GeneratedMetricClosure.RoleHingedGeneratedClosureData k hk :=
    { transitions := F.transitions
      orientation := F.orientation k hk
      closure := F.closure k hk
      separated := F.separated k hk }
  exact G.targetUpperConstructionFiveSixteenAt_exactBlock

/-- A finite search family for every positive period length gives the exact
Pach-Toth target. -/
theorem targetUpperConstructionFiveSixteen
    (F : RoleHingedFiniteSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily.targetUpperConstructionFiveSixteen
      F.toRoleHingedGeneratedClosureFamily

end RoleHingedFiniteSearchFamily

/-! ## All-positive non-connector square-value certificates -/

/-- Period-search data for every positive block count, before adding the
remaining non-connector square-distance tables.

This is deliberately only a data shape: it records the words and exact indexed
period equations supplied by a finite search, but it does not assert that any
particular search output exists. -/
structure AllPositivePeriodSearchData where
  transitions : RoleHingeTransitions
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  period :
    forall (k : Nat) (hk : 0 < k),
      PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (PeriodCertificateExamples.finiteOrientationWordOfWord hk
          (word k hk))

namespace AllPositivePeriodSearchData

/-- The raw generated-chain orientation function carried by the finite words. -/
def orientation
    (F : AllPositivePeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    (F : AllPositivePeriodSearchData)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

/-- The period-search finite word associated to one positive block count. -/
def finiteWord
    (F : AllPositivePeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.FiniteOrientationWord :=
  PeriodCertificateExamples.finiteOrientationWordOfWord hk (F.word k hk)

@[simp]
theorem finiteWord_length
    (F : AllPositivePeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    (F.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    (F : AllPositivePeriodSearchData)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (F.finiteWord k hk).letter i = F.orientation k hk i :=
  rfl

/-- Rephrase the stored indexed period certificate in the exact-family finite
word spelling expected by the generated-family interfaces. -/
def indexedCertificate
    (F : AllPositivePeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      F.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (ExactFamilyClosure.finiteOrientationWord k hk
        (F.orientation k hk)) where
  equation := by
    intro i
    simpa [ExactFamilyClosure.finiteOrientationWord, finiteWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord, orientation]
      using (F.period k hk).equation i

/-- Project the all-positive period data to the role-hinged period-search
family consumed by the square-table and cross-block routes. -/
def toRoleHingedPeriodSearchFamily
    (F : AllPositivePeriodSearchData) :
    RoleHingedPeriodSearchFamily where
  transitions := F.transitions
  orientation := F.orientation
  period := F.indexedCertificate

@[simp]
theorem toRoleHingedPeriodSearchFamily_transitions
    (F : AllPositivePeriodSearchData) :
    F.toRoleHingedPeriodSearchFamily.transitions = F.transitions :=
  rfl

@[simp]
theorem toRoleHingedPeriodSearchFamily_orientation
    (F : AllPositivePeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    F.toRoleHingedPeriodSearchFamily.orientation k hk =
      F.orientation k hk :=
  rfl

/-- Generated closure obtained from the stored period equations. -/
def closure
    (F : AllPositivePeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  (F.indexedCertificate k hk).toGeneratedClosureEquation

/-- Generated final-block period equation obtained from the same indexed
period certificate. -/
def periodEquation
    (F : AllPositivePeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  (F.indexedCertificate k hk).toGeneratedPeriodEquation

end AllPositivePeriodSearchData

/-- Non-connector square-value data for a fixed all-positive period-search
family.

Only upper-triangle pairs that are not cyclic connector pairs need a stored
value.  Connector pairs are handled by the role-hinge connector facts in the
existing non-connector route. -/
structure NonConnectorSqValueCertificate
    (periodSearch : AllPositivePeriodSearchData) where
  value :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_polynomial_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (CrossBlockSqTableSearch.IndexedCyclicConnectorPair
            hk i u j v) ->
            value k hk i u j v =
              CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                periodSearch.toRoleHingedPeriodSearchFamily hk i u j v
  value_ge_one_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (CrossBlockSqTableSearch.IndexedCyclicConnectorPair
            hk i u j v) ->
            1 <= value k hk i u j v

namespace NonConnectorSqValueCertificate

/-- Rebuild the one-period non-connector upper-triangle value table consumed
by `CrossBlockSqTableSearch`. -/
def toSqValueTable
    {periodSearch : AllPositivePeriodSearchData}
    (S : NonConnectorSqValueCertificate periodSearch)
    (k : Nat) (hk : 0 < k) :
    UpperTriangleNonConnectorSqValueTable
      periodSearch.toRoleHingedPeriodSearchFamily k hk where
  value := S.value k hk
  value_eq_polynomial_lt := by
    intro i u j v hlt hnot_connector
    exact S.value_eq_polynomial_lt k hk i u j v hlt hnot_connector
  value_ge_one_lt := by
    intro i u j v hlt hnot_connector
    exact S.value_ge_one_lt k hk i u j v hlt hnot_connector

@[simp]
theorem toSqValueTable_value
    {periodSearch : AllPositivePeriodSearchData}
    (S : NonConnectorSqValueCertificate periodSearch)
    (k : Nat) (hk : 0 < k) :
    (S.toSqValueTable k hk).value = S.value k hk :=
  rfl

/-- Project the non-connector value checklist to the all-positive table
family used by the existing connector-separated route. -/
def toSqValueTableFamily
    {periodSearch : AllPositivePeriodSearchData}
    (S : NonConnectorSqValueCertificate periodSearch) :
    UpperTriangleNonConnectorSqValueTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily where
  table := fun k hk => S.toSqValueTable k hk

@[simp]
theorem toSqValueTableFamily_table
    {periodSearch : AllPositivePeriodSearchData}
    (S : NonConnectorSqValueCertificate periodSearch)
    (k : Nat) (hk : 0 < k) :
    S.toSqValueTableFamily.table k hk = S.toSqValueTable k hk :=
  rfl

/-- The non-connector square-distance table family obtained from the stored
computed values. -/
def toNonConnectorSqDistanceTableFamily
    {periodSearch : AllPositivePeriodSearchData}
    (S : NonConnectorSqValueCertificate periodSearch) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily :=
  S.toSqValueTableFamily.toNonConnectorSqDistanceTableFamily

/-- Generated global separation for one positive block count, routed through
the non-connector square-distance table and connector facts. -/
def separated
    {periodSearch : AllPositivePeriodSearchData}
    (S : NonConnectorSqValueCertificate periodSearch)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (periodSearch.orientation k hk) :=
  S.toNonConnectorSqDistanceTableFamily.separated k hk

/-- The role-hinged generated-closure family obtained from period equations
and non-connector square-value tables. -/
def toRoleHingedGeneratedClosureFamily
    {periodSearch : AllPositivePeriodSearchData}
    (S : NonConnectorSqValueCertificate periodSearch) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily where
  transitions := periodSearch.transitions
  orientation := periodSearch.orientation
  closure := periodSearch.closure
  separated := S.separated

/-- One member of the non-connector square-value certificate gives the
exact-block target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {periodSearch : AllPositivePeriodSearchData}
    (S : NonConnectorSqValueCertificate periodSearch)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  let G : GeneratedMetricClosure.RoleHingedGeneratedClosureData k hk :=
    { transitions := periodSearch.transitions
      orientation := periodSearch.orientation k hk
      closure := periodSearch.closure k hk
      separated := S.separated k hk }
  exact G.targetUpperConstructionFiveSixteenAt_exactBlock

/-- Exact-multiple Pach-Toth target from all-positive period data and
non-connector square-value tables. -/
theorem targetUpperConstructionFiveSixteen
    {periodSearch : AllPositivePeriodSearchData}
    (S : NonConnectorSqValueCertificate periodSearch) :
    PachToth.targetUpperConstructionFiveSixteen :=
  S.toSqValueTableFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach-Toth target from the exact target supplied by the
non-connector square-value route. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {periodSearch : AllPositivePeriodSearchData}
    (S : NonConnectorSqValueCertificate periodSearch) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    S.targetUpperConstructionFiveSixteen

end NonConnectorSqValueCertificate

/-- Compact all-positive finite-search certificate: role-hinge transitions,
one finite word and indexed period certificate for every `k > 0`, and the
non-connector square-value tables for those same candidates. -/
structure AllPositiveNonConnectorSqValueCertificate where
  periodSearch : AllPositivePeriodSearchData
  sqValue : NonConnectorSqValueCertificate periodSearch

namespace AllPositiveNonConnectorSqValueCertificate

def transitions
    (C : AllPositiveNonConnectorSqValueCertificate) :
    RoleHingeTransitions :=
  C.periodSearch.transitions

def word
    (C : AllPositiveNonConnectorSqValueCertificate)
    (k : Nat) (hk : 0 < k) :
    OrientationWord.Word k :=
  C.periodSearch.word k hk

def orientation
    (C : AllPositiveNonConnectorSqValueCertificate)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  C.periodSearch.orientation k hk

@[simp]
theorem orientation_apply
    (C : AllPositiveNonConnectorSqValueCertificate)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    C.orientation k hk i = C.word k hk i :=
  rfl

/-- The role-hinged period-search family exposed by the compact certificate. -/
def toRoleHingedPeriodSearchFamily
    (C : AllPositiveNonConnectorSqValueCertificate) :
    RoleHingedPeriodSearchFamily :=
  C.periodSearch.toRoleHingedPeriodSearchFamily

/-- The non-connector upper-triangle square-value table for one period. -/
def toSqValueTable
    (C : AllPositiveNonConnectorSqValueCertificate)
    (k : Nat) (hk : 0 < k) :
    UpperTriangleNonConnectorSqValueTable
      C.toRoleHingedPeriodSearchFamily k hk :=
  C.sqValue.toSqValueTable k hk

/-- The all-positive non-connector square-value table family. -/
def toSqValueTableFamily
    (C : AllPositiveNonConnectorSqValueCertificate) :
    UpperTriangleNonConnectorSqValueTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.sqValue.toSqValueTableFamily

/-- Projection to the existing non-connector square-distance table family. -/
def toNonConnectorSqDistanceTableFamily
    (C : AllPositiveNonConnectorSqValueCertificate) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.sqValue.toNonConnectorSqDistanceTableFamily

/-- Generated closure for one positive block count. -/
def closure
    (C : AllPositiveNonConnectorSqValueCertificate)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      C.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) :=
  C.periodSearch.closure k hk

/-- Generated final-block period equation for one positive block count. -/
def periodEquation
    (C : AllPositiveNonConnectorSqValueCertificate)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      C.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) :=
  C.periodSearch.periodEquation k hk

/-- Generated separation for one positive block count, routed through the
connector-separated non-connector table path. -/
def separated
    (C : AllPositiveNonConnectorSqValueCertificate)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) :=
  C.sqValue.separated k hk

/-- Projection to the generated-closure family facade already used by the
exact target route. -/
def toRoleHingedGeneratedClosureFamily
    (C : AllPositiveNonConnectorSqValueCertificate) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily :=
  C.sqValue.toRoleHingedGeneratedClosureFamily

/-- Exact-block target at a chosen positive period length. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (C : AllPositiveNonConnectorSqValueCertificate)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  C.sqValue.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact-multiple Pach-Toth target from the compact all-positive
non-connector certificate. -/
theorem targetUpperConstructionFiveSixteen
    (C : AllPositiveNonConnectorSqValueCertificate) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.sqValue.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach-Toth target from the compact all-positive
non-connector certificate. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (C : AllPositiveNonConnectorSqValueCertificate) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.sqValue.targetUpperConstructionFiveSixteenArbitrary

end AllPositiveNonConnectorSqValueCertificate

/-- Exact target from an already split all-positive period package and its
non-connector square-value tables. -/
theorem targetUpperConstructionFiveSixteen_of_allPositivePeriodSearchData
    (periodSearch : AllPositivePeriodSearchData)
    (sqValue : NonConnectorSqValueCertificate periodSearch) :
    PachToth.targetUpperConstructionFiveSixteen :=
  ({ periodSearch := periodSearch
     sqValue := sqValue } :
      AllPositiveNonConnectorSqValueCertificate)
    |>.targetUpperConstructionFiveSixteen

/-- Arbitrary target from an already split all-positive period package and its
non-connector square-value tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_allPositivePeriodSearchData
    (periodSearch : AllPositivePeriodSearchData)
    (sqValue : NonConnectorSqValueCertificate periodSearch) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ({ periodSearch := periodSearch
     sqValue := sqValue } :
      AllPositiveNonConnectorSqValueCertificate)
    |>.targetUpperConstructionFiveSixteenArbitrary

end

end FiniteSearchCertificate
end PachToth
end ErdosProblems1066
