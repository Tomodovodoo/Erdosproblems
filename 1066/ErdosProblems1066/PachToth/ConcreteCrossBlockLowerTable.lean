import ErdosProblems1066.PachToth.CrossBlockUpperTriangleConcrete
import ErdosProblems1066.PachToth.IndexedCrossBlockTableConcrete
import ErdosProblems1066.PachToth.GeneratedSeparationFarApart
import ErdosProblems1066.PachToth.ConcretePeriodCandidateSearch

set_option autoImplicit false

/-!
# Concrete non-connector cross-block lower tables

This module packages the finite-table route for a small non-connector
cross-block certificate.  The table data is still the concrete upper-triangle
certificate from `CrossBlockUpperTriangleConcrete`; this file only records the
honest projections from that finite data to the generated lower-bound
predicates and, for a tagged small candidate period, to the exact-block target.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteCrossBlockLowerTable

open FiniteGraph
open CrossBlockUpperTriangleConcrete
open IndexedCrossBlockTableConcrete

noncomputable section

abbrev PeriodSearchData := ConcretePeriodSearchFamily.PeriodSearchData

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev IndexedCrossBlockLowerTable :=
  CrossBlockLowerBoundsInterface.IndexedCrossBlockLowerTable

abbrev IndexedCrossBlockLowerTableFamily :=
  CrossBlockLowerBoundsInterface.IndexedCrossBlockLowerTableFamily

abbrev CrossBlockLowerBounds :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds

abbrev UpperTriangleNonConnectorVectorCertificate :=
  CrossBlockUpperTriangleConcrete.UpperTriangleNonConnectorVectorCertificate

abbrev UpperTriangleNonConnectorListCertificate :=
  CrossBlockUpperTriangleConcrete.UpperTriangleNonConnectorListCertificate

abbrev UpperTriangleNonConnectorVectorCertificateFamily :=
  CrossBlockUpperTriangleConcrete.UpperTriangleNonConnectorVectorCertificateFamily

abbrev UpperTriangleNonConnectorListCertificateFamily :=
  CrossBlockUpperTriangleConcrete.UpperTriangleNonConnectorListCertificateFamily

abbrev SmallCandidateTag :=
  ConcretePeriodCandidateSearch.SmallWords.CandidateTag

namespace SqTableFamily

export IndexedNonConnectorCrossBlockSqDistanceTableFamilyConcrete
  (toIndexedCrossBlockLowerTableFamily
   toCrossBlockLowerBounds
   toCrossBlockLowerBounds_ge_one
   toCrossBlockLowerBounds_bound
   separated
   targetUpperConstructionFiveSixteen
   targetUpperConstructionFiveSixteenArbitrary)

export NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily
  (toCrossBlockLowerTableFamily)

end SqTableFamily

/-- A concrete non-connector cross-block lower table for one period length.

The stored square-distance table is the finite checked data.  The local lower
table used downstream is the induced everywhere-one table, with successor
connector slots justified separately by the role-hinge connector facts. -/
structure NonConnectorLowerTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  sqTable : IndexedNonConnectorCrossBlockSqDistanceTable F k hk

namespace NonConnectorLowerTable

/-- Build the lower-table wrapper from a vector-backed upper-triangle
non-connector certificate. -/
def ofVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    NonConnectorLowerTable F k hk where
  sqTable := C.toNonConnectorSqDistanceTable

/-- Build the lower-table wrapper from a list-backed upper-triangle
non-connector certificate. -/
def ofListCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    NonConnectorLowerTable F k hk where
  sqTable := C.toNonConnectorSqDistanceTable

/-- The local-vertex lower table induced by the finite non-connector
square-distance data. -/
def lower
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorLowerTable F k hk) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  T.sqTable.lower

@[simp]
theorem lower_apply
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorLowerTable F k hk)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    T.lower i u j v = 1 := by
  simp [lower]

/-- Expand the non-connector table to the existing indexed cross-block lower
table by filling connector slots with the checked connector value. -/
def toIndexedCrossBlockLowerTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorLowerTable F k hk) :
    IndexedCrossBlockLowerTable F k hk :=
  T.sqTable.toCrossBlockLowerTable

@[simp]
theorem toIndexedCrossBlockLowerTable_lower
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorLowerTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    T.toIndexedCrossBlockLowerTable.lower i u j v = 1 := by
  rfl

/-- The induced table is at least one on every remaining non-connector
cross-block pair. -/
theorem nonConnectorLower_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorLowerTable F k hk) :
    NonRigidConnectorSeparationFacts.GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne
      hk T.lower := by
  simpa [lower] using T.sqTable.lower_ge_one

/-- The finite square-distance entries bound the generated non-connector
cross-block distances. -/
theorem nonConnectorDistanceLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorLowerTable F k hk) :
    NonRigidConnectorSeparationFacts.GeneratedNonConnectorCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      T.lower := by
  simpa [lower] using T.sqTable.lower_bound

/-- After connector slots are supplied by the role-hinge equations, the
induced cross-block lower table is at least one everywhere off the diagonal
of block indices. -/
theorem crossBlockLower_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorLowerTable F k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      T.lower := by
  simpa [lower] using T.sqTable.crossBlock_lower_ge_one

/-- After connector slots are supplied by the role-hinge equations, the
induced cross-block lower table is bounded by the generated distances. -/
theorem crossBlockDistanceLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorLowerTable F k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      T.lower := by
  simpa [lower] using T.sqTable.crossBlock_lower_bound

/-- The finite table gives generated global separation for this one period
length. -/
theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorLowerTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.sqTable.generatedGlobalSeparation

end NonConnectorLowerTable

/-- A family of concrete non-connector lower tables, one for every positive
period length. -/
structure NonConnectorLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      NonConnectorLowerTable F k hk

namespace NonConnectorLowerTableFamily

/-- Build a family from vector-backed upper-triangle non-connector
certificates. -/
def ofVectorCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorVectorCertificateFamily F) :
    NonConnectorLowerTableFamily F where
  table := fun k hk => NonConnectorLowerTable.ofVectorCertificate (C.table k hk)

/-- Build a family from list-backed upper-triangle non-connector
certificates. -/
def ofListCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorListCertificateFamily F) :
    NonConnectorLowerTableFamily F where
  table := fun k hk => NonConnectorLowerTable.ofListCertificate (C.table k hk)

/-- The finite non-connector square-distance table family obtained from the
wrapped per-period tables. -/
def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk => (T.table k hk).sqTable

/-- The expanded indexed cross-block lower-table family. -/
def toIndexedCrossBlockLowerTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F) :
    IndexedCrossBlockLowerTableFamily F :=
  SqTableFamily.toIndexedCrossBlockLowerTableFamily
    T.toNonConnectorSqDistanceTableFamily

/-- The downstream cross-block lower-bound facade. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F) :
    CrossBlockLowerBounds F :=
  SqTableFamily.toCrossBlockLowerBounds
    T.toNonConnectorSqDistanceTableFamily

@[simp]
theorem toCrossBlockLowerBounds_lower_apply
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    (T.toCrossBlockLowerBounds).lower k hk i u j v = 1 := by
  simp [toCrossBlockLowerBounds,
    SqTableFamily.toCrossBlockLowerBounds,
    SqTableFamily.toCrossBlockLowerTableFamily,
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds.ofIndexedTables,
    CrossBlockLowerBoundsInterface.IndexedCrossBlockLowerTableFamily.lower,
    CrossBlockLowerBoundsInterface.IndexedCrossBlockLowerTable.toLocalLower]

/-- The finite family gives the generated far-apart `>= 1` predicate at each
period length. -/
theorem crossBlockLower_ge_one
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      ((T.toCrossBlockLowerBounds).lower k hk) :=
  SqTableFamily.toCrossBlockLowerBounds_ge_one
    T.toNonConnectorSqDistanceTableFamily k hk

/-- The finite family gives the generated far-apart distance lower-bound
predicate at each period length. -/
theorem crossBlockDistanceLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      ((T.toCrossBlockLowerBounds).lower k hk) :=
  SqTableFamily.toCrossBlockLowerBounds_bound
    T.toNonConnectorSqDistanceTableFamily k hk

/-- The finite family gives generated global separation at each period
length. -/
theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  SqTableFamily.separated
    T.toNonConnectorSqDistanceTableFamily k hk

/-- Exact-multiple Pach--Toth target from the table family. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  SqTableFamily.targetUpperConstructionFiveSixteen
    T.toNonConnectorSqDistanceTableFamily

/-- Arbitrary-`n` Pach--Toth target from the table family and the checked
small cases already imported downstream. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  SqTableFamily.targetUpperConstructionFiveSixteenArbitrary
    T.toNonConnectorSqDistanceTableFamily

end NonConnectorLowerTableFamily

/-- Concrete period-search data plus non-connector lower tables. -/
structure ConcreteNonConnectorLowerTableFamily where
  periodSearch : PeriodSearchData
  tables :
    NonConnectorLowerTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace ConcreteNonConnectorLowerTableFamily

def ofVectorCertificateFamily
    (periodSearch : PeriodSearchData)
    (C :
      UpperTriangleNonConnectorVectorCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily) :
    ConcreteNonConnectorLowerTableFamily where
  periodSearch := periodSearch
  tables := NonConnectorLowerTableFamily.ofVectorCertificateFamily C

def ofListCertificateFamily
    (periodSearch : PeriodSearchData)
    (C :
      UpperTriangleNonConnectorListCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily) :
    ConcreteNonConnectorLowerTableFamily where
  periodSearch := periodSearch
  tables := NonConnectorLowerTableFamily.ofListCertificateFamily C

@[simp]
theorem ofVectorCertificateFamily_periodSearch
    (periodSearch : PeriodSearchData)
    (C :
      UpperTriangleNonConnectorVectorCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily) :
    (ofVectorCertificateFamily periodSearch C).periodSearch =
      periodSearch := by
  rfl

@[simp]
theorem ofListCertificateFamily_periodSearch
    (periodSearch : PeriodSearchData)
    (C :
      UpperTriangleNonConnectorListCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily) :
    (ofListCertificateFamily periodSearch C).periodSearch =
      periodSearch := by
  rfl

theorem nonempty_iff_exists_periodSearch_tables :
    Nonempty ConcreteNonConnectorLowerTableFamily <->
      Exists fun periodSearch : PeriodSearchData =>
        Nonempty
          (NonConnectorLowerTableFamily
            periodSearch.toRoleHingedPeriodSearchFamily) := by
  constructor
  · intro H
    cases H with
    | intro C =>
        exact Exists.intro C.periodSearch (Nonempty.intro C.tables)
  · intro H
    cases H with
    | intro periodSearch HT =>
        cases HT with
        | intro tables =>
            exact Nonempty.intro
              { periodSearch := periodSearch
                tables := tables }

theorem nonempty_periodSearch_of_nonempty
    (H : Nonempty ConcreteNonConnectorLowerTableFamily) :
    Nonempty PeriodSearchData := by
  cases H with
  | intro C =>
      exact Nonempty.intro C.periodSearch

theorem nonempty_roleHingedPeriodSearchFamily_of_nonempty
    (H : Nonempty ConcreteNonConnectorLowerTableFamily) :
    Nonempty RoleHingedPeriodSearchFamily := by
  cases H with
  | intro C =>
      exact Nonempty.intro C.periodSearch.toRoleHingedPeriodSearchFamily

def toRoleHingedPeriodSearchFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    RoleHingedPeriodSearchFamily :=
  C.periodSearch.toRoleHingedPeriodSearchFamily

def toNonConnectorSqDistanceTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toNonConnectorSqDistanceTableFamily

def toIndexedCrossBlockLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    IndexedCrossBlockLowerTableFamily C.toRoleHingedPeriodSearchFamily :=
  C.tables.toIndexedCrossBlockLowerTableFamily

def toCrossBlockLowerBounds
    (C : ConcreteNonConnectorLowerTableFamily) :
    CrossBlockLowerBounds C.toRoleHingedPeriodSearchFamily :=
  C.tables.toCrossBlockLowerBounds

theorem crossBlockLower_ge_one
    (C : ConcreteNonConnectorLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      ((C.toCrossBlockLowerBounds).lower k hk) :=
  C.tables.crossBlockLower_ge_one k hk

theorem crossBlockDistanceLowerBounds
    (C : ConcreteNonConnectorLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      C.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (C.periodSearch.orientation k hk)
      ((C.toCrossBlockLowerBounds).lower k hk) :=
  C.tables.crossBlockDistanceLowerBounds k hk

theorem separated
    (C : ConcreteNonConnectorLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (C.periodSearch.orientation k hk) :=
  C.tables.separated k hk

theorem targetUpperConstructionFiveSixteen
    (C : ConcreteNonConnectorLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.tables.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : ConcreteNonConnectorLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.tables.targetUpperConstructionFiveSixteenArbitrary

end ConcreteNonConnectorLowerTableFamily

/-- One tagged small candidate period together with its concrete
non-connector lower table.  The word equality records that the selected entry
of the period-search family is the requested small candidate word. -/
structure SmallCandidateNonConnectorLowerTable
    (periodSearch : PeriodSearchData)
    (tag : SmallCandidateTag) where
  word_eq :
    periodSearch.word tag.length tag.positiveLength = tag.word
  table :
    NonConnectorLowerTable
      periodSearch.toRoleHingedPeriodSearchFamily
      tag.length tag.positiveLength

namespace SmallCandidateNonConnectorLowerTable

/-- Build a tagged small-candidate table from a vector-backed certificate. -/
def ofVectorCertificate
    {periodSearch : PeriodSearchData}
    {tag : SmallCandidateTag}
    {n : Nat}
    (word_eq :
      periodSearch.word tag.length tag.positiveLength = tag.word)
    (C :
      UpperTriangleNonConnectorVectorCertificate
        periodSearch.toRoleHingedPeriodSearchFamily
        tag.length tag.positiveLength n) :
    SmallCandidateNonConnectorLowerTable periodSearch tag where
  word_eq := word_eq
  table := NonConnectorLowerTable.ofVectorCertificate C

/-- Build a tagged small-candidate table from a list-backed certificate. -/
def ofListCertificate
    {periodSearch : PeriodSearchData}
    {tag : SmallCandidateTag}
    (word_eq :
      periodSearch.word tag.length tag.positiveLength = tag.word)
    (C :
      UpperTriangleNonConnectorListCertificate
        periodSearch.toRoleHingedPeriodSearchFamily
        tag.length tag.positiveLength) :
    SmallCandidateNonConnectorLowerTable periodSearch tag where
  word_eq := word_eq
  table := NonConnectorLowerTable.ofListCertificate C

/-- The tagged period-search orientation is the small candidate word. -/
theorem orientation_eq_word
    {periodSearch : PeriodSearchData}
    {tag : SmallCandidateTag}
    (T : SmallCandidateNonConnectorLowerTable periodSearch tag) :
    periodSearch.orientation tag.length tag.positiveLength =
      tag.word.toFin := by
  funext i
  simp [ConcretePeriodSearchFamily.PeriodSearchData.orientation, T.word_eq]

theorem crossBlockLower_ge_one
    {periodSearch : PeriodSearchData}
    {tag : SmallCandidateTag}
    (T : SmallCandidateNonConnectorLowerTable periodSearch tag) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      T.table.lower :=
  T.table.crossBlockLower_ge_one

theorem crossBlockDistanceLowerBounds
    {periodSearch : PeriodSearchData}
    {tag : SmallCandidateTag}
    (T : SmallCandidateNonConnectorLowerTable periodSearch tag) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      periodSearch.transitions.toFigure2TransitionObligations
      tag.positiveLength
      BaseTransitionRealization.exactBase
      (periodSearch.orientation tag.length tag.positiveLength)
      T.table.lower :=
  T.table.crossBlockDistanceLowerBounds

/-- Generated global separation for the tagged small candidate period. -/
theorem generatedGlobalSeparation
    {periodSearch : PeriodSearchData}
    {tag : SmallCandidateTag}
    (T : SmallCandidateNonConnectorLowerTable periodSearch tag) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      periodSearch.transitions.toFigure2TransitionObligations
      tag.positiveLength
      BaseTransitionRealization.exactBase
      (periodSearch.orientation tag.length tag.positiveLength) :=
  T.table.generatedGlobalSeparation

/-- Reduced metric hypotheses for the tagged small candidate period. -/
def reducedMetricHypotheses
    {periodSearch : PeriodSearchData}
    {tag : SmallCandidateTag}
    (T : SmallCandidateNonConnectorLowerTable periodSearch tag) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      periodSearch.transitions.toFigure2TransitionObligations
      tag.positiveLength
      BaseTransitionRealization.exactBase
      (periodSearch.orientation tag.length tag.positiveLength) :=
  GeneratedMetricClosure.generatedReducedMetricHypotheses
    periodSearch.transitions tag.positiveLength
    (periodSearch.orientation tag.length tag.positiveLength)
    T.generatedGlobalSeparation

/-- Exact-block target for the tagged small candidate period, obtained from
the finite non-connector table and the candidate's stored period equations. -/
theorem targetUpperConstructionFiveSixteenAt
    {periodSearch : PeriodSearchData}
    {tag : SmallCandidateTag}
    (T : SmallCandidateNonConnectorLowerTable periodSearch tag) :
    targetUpperConstructionFiveSixteenAt (16 * tag.length) := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteenAt_exactBlock_reduced
      periodSearch.transitions.toFigure2TransitionObligations
      tag.positiveLength
      BaseTransitionRealization.exactBase
      (periodSearch.orientation tag.length tag.positiveLength)
      (periodSearch.generatedPeriod tag.length tag.positiveLength)
      T.reducedMetricHypotheses

end SmallCandidateNonConnectorLowerTable

end

end ConcreteCrossBlockLowerTable
end PachToth
end ErdosProblems1066
