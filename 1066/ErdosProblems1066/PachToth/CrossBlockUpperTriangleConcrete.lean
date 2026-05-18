import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.CrossBlockSqTableSearch
import ErdosProblems1066.PachToth.NonRigidConnectorSeparationFacts

set_option autoImplicit false

/-!
# Concrete upper-triangle cross-block square tables

This module is a lightweight concrete layer for generated cross-block
certificates.  It packages a finite list or vector of checked upper-triangle
square-distance values and projects it to the `CrossBlockSqTableSearch`
interfaces.

The constructors intentionally keep all numerical work explicit: users must
provide, for every stored upper-triangle position, both the equality with the
coordinate square polynomial and the lower bound `1 <= value`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockUpperTriangleConcrete

open CrossBlockDistanceSqReduction
open CrossBlockLowerBoundsInterface
open CrossBlockSqTableSearch
open ConcretePeriodSearchFamily
open FiniteGraph
open NonRigidConnectorSeparationFacts

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

abbrev UpperTrianglePolynomialTable :=
  CrossBlockSqTableSearch.UpperTrianglePolynomialTable

abbrev UpperTrianglePolynomialTableFamily :=
  CrossBlockSqTableSearch.UpperTrianglePolynomialTableFamily

abbrev UpperTriangleSqValueTable :=
  CrossBlockSqTableSearch.UpperTriangleSqValueTable

abbrev UpperTriangleSqValueTableFamily :=
  CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily

abbrev UpperTriangleNonConnectorPolynomialTable :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTable

abbrev UpperTriangleNonConnectorPolynomialTableFamily :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTableFamily

abbrev UpperTriangleNonConnectorSqValueTable :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTable

abbrev UpperTriangleNonConnectorSqValueTableFamily :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily

abbrev IndexedCrossBlockSqDistanceTable :=
  CrossBlockDistanceSqReduction.IndexedCrossBlockSqDistanceTable

abbrev IndexedCrossBlockSqDistanceTableFamily :=
  CrossBlockDistanceSqReduction.IndexedCrossBlockSqDistanceTableFamily

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  CrossBlockSqTableSearch.IndexedCyclicConnectorPair hk i u j v

/-- One packed upper-triangle table position: a pair of distinct block
indices in increasing order, together with the two local `Fin 16` vertices. -/
structure UpperTrianglePosition (k : Nat) where
  left : Fin k
  leftVertex : LocalVertexIndex
  right : Fin k
  rightVertex : LocalVertexIndex
  left_lt_right : left.val < right.val

namespace UpperTrianglePosition

/-- The coordinate square polynomial attached to a packed upper-triangle
position. -/
def polynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (p : UpperTrianglePosition k) : Real :=
  indexedGeneratedSqPolynomial F hk
    p.left p.leftVertex p.right p.rightVertex

/-- The generated square distance attached to a packed upper-triangle
position. -/
def sqDist
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (p : UpperTrianglePosition k) : Real :=
  indexedGeneratedSqDist F hk
    p.left p.leftVertex p.right p.rightVertex

@[simp]
theorem sqDist_eq_polynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (p : UpperTrianglePosition k) :
    p.sqDist F hk = p.polynomial F hk := by
  rfl

end UpperTrianglePosition

/-- Non-connector status for a packed upper-triangle position. -/
def UpperTrianglePosition.nonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  Not (IndexedCyclicConnectorPair hk
    p.left p.leftVertex p.right p.rightVertex)

/-- A generated local-vertex non-connector side condition projects to the
finite-index connector spelling used by upper-triangle certificates. -/
theorem not_indexedCyclicConnectorPair_of_not_generatedCyclicConnectorPair
    {k : Nat} {hk : 0 < k}
    {i : Fin k} {u : LocalVertex}
    {j : Fin k} {v : LocalVertex}
    (hnot :
      Not (GeneratedSeparationFarApart.GeneratedCyclicConnectorPair
        hk i u j v)) :
    Not (IndexedCyclicConnectorPair hk i (localVertexIndex u)
      j (localVertexIndex v)) := by
  intro hidx
  exact hnot (by
    simpa [GeneratedSeparationFarApart.GeneratedCyclicConnectorPair,
      GeneratedSeparationFarApart.GeneratedSuccessorConnectorPair,
      IndexedCyclicConnectorPair, CrossBlockSqTableSearch.IndexedCyclicConnectorPair,
      NonRigidConnectorSeparationFacts.IndexedCyclicConnectorPair,
      NonRigidConnectorSeparationFacts.CyclicConnectorPair,
      NonRigidConnectorSeparationFacts.SuccessorConnectorPair] using hidx)

/-- A vector-backed upper-triangle certificate.  The `index` field lets a
generator choose any packing order for the supplied vector. -/
structure UpperTriangleVectorCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) (n : Nat) where
  values : Vector Real n
  index : UpperTrianglePosition k -> Fin n
  value_eq_polynomial :
    forall p : UpperTrianglePosition k,
      values.get (index p) = p.polynomial F hk
  value_ge_one :
    forall p : UpperTrianglePosition k,
      1 <= values.get (index p)

namespace UpperTriangleVectorCertificate

/-- Read the stored value at an upper-triangle position. -/
def value
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (p : UpperTrianglePosition k) : Real :=
  C.values.get (C.index p)

/-- Convert a vector-backed certificate to the value-table interface in
`CrossBlockSqTableSearch`. -/
def toSqValueTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n) :
    UpperTriangleSqValueTable F k hk where
  value := fun i u j v =>
    if hlt : i.val < j.val then
      C.value
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }
    else
      0
  value_eq_polynomial_lt := by
    intro i u j v hlt
    rw [dif_pos hlt]
    exact
      C.value_eq_polynomial
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }
  value_ge_one_lt := by
    intro i u j v hlt
    rw [dif_pos hlt]
    exact
      C.value_ge_one
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }

/-- Vector-backed certificates reduce to upper-triangle polynomial tables. -/
def toPolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n) :
    UpperTrianglePolynomialTable F k hk :=
  C.toSqValueTable.toPolynomialTable

/-- Vector-backed certificates reduce to full square-distance tables. -/
def toSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n) :
    IndexedCrossBlockSqDistanceTable F k hk :=
  C.toSqValueTable.toSqDistanceTable

/-- Vector-backed certificates also feed the non-connector square-distance
table used by the connector-separated route.  The certificate proves the
stronger all-cross-block table, so the connector side condition is ignored. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij _hnot_connector
    exact (C.toSqDistanceTable).sqDist_ge_one i u j v hij

theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toSqValueTable.generatedGlobalSeparation

end UpperTriangleVectorCertificate

/-- Constructor form for vector-backed upper-triangle value tables. -/
def upperTriangleSqValueTableOfVector
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k) {n : Nat}
    (values : Vector Real n)
    (index : UpperTrianglePosition k -> Fin n)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        1 <= values.get (index p)) :
    UpperTriangleSqValueTable F k hk :=
  (UpperTriangleVectorCertificate.mk
    values index value_eq_polynomial value_ge_one).toSqValueTable

/-- Constructor form for vector-backed upper-triangle polynomial tables. -/
def upperTrianglePolynomialTableOfVector
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k) {n : Nat}
    (values : Vector Real n)
    (index : UpperTrianglePosition k -> Fin n)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        1 <= values.get (index p)) :
    UpperTrianglePolynomialTable F k hk :=
  (upperTriangleSqValueTableOfVector hk
    values index value_eq_polynomial value_ge_one).toPolynomialTable

/-- Constructor form for vector-backed full square-distance tables. -/
def indexedCrossBlockSqDistanceTableOfVector
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k) {n : Nat}
    (values : Vector Real n)
    (index : UpperTrianglePosition k -> Fin n)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        1 <= values.get (index p)) :
    IndexedCrossBlockSqDistanceTable F k hk :=
  (upperTriangleSqValueTableOfVector hk
    values index value_eq_polynomial value_ge_one).toSqDistanceTable

/-- Constructor form for vector-backed non-connector square-distance tables. -/
def indexedNonConnectorCrossBlockSqDistanceTableOfVector
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k) {n : Nat}
    (values : Vector Real n)
    (index : UpperTrianglePosition k -> Fin n)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        1 <= values.get (index p)) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  (UpperTriangleVectorCertificate.mk
    values index value_eq_polynomial value_ge_one).toNonConnectorSqDistanceTable

/-- A list-backed upper-triangle certificate.  The `index` field is a finite
index into the supplied list, so the list length obligation stays visible. -/
structure UpperTriangleListCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  values : List Real
  index : UpperTrianglePosition k -> Fin values.length
  value_eq_polynomial :
    forall p : UpperTrianglePosition k,
      values.get (index p) = p.polynomial F hk
  value_ge_one :
    forall p : UpperTrianglePosition k,
      1 <= values.get (index p)

namespace UpperTriangleListCertificate

/-- Read the stored list entry at an upper-triangle position. -/
def value
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (p : UpperTrianglePosition k) : Real :=
  C.values.get (C.index p)

/-- Convert a list-backed certificate to the value-table interface in
`CrossBlockSqTableSearch`. -/
def toSqValueTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk) :
    UpperTriangleSqValueTable F k hk where
  value := fun i u j v =>
    if hlt : i.val < j.val then
      C.value
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }
    else
      0
  value_eq_polynomial_lt := by
    intro i u j v hlt
    rw [dif_pos hlt]
    exact
      C.value_eq_polynomial
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }
  value_ge_one_lt := by
    intro i u j v hlt
    rw [dif_pos hlt]
    exact
      C.value_ge_one
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }

/-- List-backed certificates reduce to upper-triangle polynomial tables. -/
def toPolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk) :
    UpperTrianglePolynomialTable F k hk :=
  C.toSqValueTable.toPolynomialTable

/-- List-backed certificates reduce to full square-distance tables. -/
def toSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk) :
    IndexedCrossBlockSqDistanceTable F k hk :=
  C.toSqValueTable.toSqDistanceTable

/-- List-backed certificates also feed the non-connector square-distance
table used by the connector-separated route.  The certificate proves the
stronger all-cross-block table, so the connector side condition is ignored. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij _hnot_connector
    exact (C.toSqDistanceTable).sqDist_ge_one i u j v hij

theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toSqValueTable.generatedGlobalSeparation

end UpperTriangleListCertificate

/-- Constructor form for list-backed upper-triangle value tables. -/
def upperTriangleSqValueTableOfList
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (values : List Real)
    (index : UpperTrianglePosition k -> Fin values.length)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        1 <= values.get (index p)) :
    UpperTriangleSqValueTable F k hk :=
  (UpperTriangleListCertificate.mk
    values index value_eq_polynomial value_ge_one).toSqValueTable

/-- Constructor form for list-backed upper-triangle polynomial tables. -/
def upperTrianglePolynomialTableOfList
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (values : List Real)
    (index : UpperTrianglePosition k -> Fin values.length)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        1 <= values.get (index p)) :
    UpperTrianglePolynomialTable F k hk :=
  (upperTriangleSqValueTableOfList hk
    values index value_eq_polynomial value_ge_one).toPolynomialTable

/-- Constructor form for list-backed full square-distance tables. -/
def indexedCrossBlockSqDistanceTableOfList
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (values : List Real)
    (index : UpperTrianglePosition k -> Fin values.length)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        1 <= values.get (index p)) :
    IndexedCrossBlockSqDistanceTable F k hk :=
  (upperTriangleSqValueTableOfList hk
    values index value_eq_polynomial value_ge_one).toSqDistanceTable

/-- Constructor form for list-backed non-connector square-distance tables. -/
def indexedNonConnectorCrossBlockSqDistanceTableOfList
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (values : List Real)
    (index : UpperTrianglePosition k -> Fin values.length)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        1 <= values.get (index p)) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  (UpperTriangleListCertificate.mk
    values index value_eq_polynomial value_ge_one).toNonConnectorSqDistanceTable

/-! ## Concrete non-connector upper-triangle certificates -/

/-- A vector-backed upper-triangle certificate for the connector-separated
route.  Only non-connector packed positions require checked values. -/
structure UpperTriangleNonConnectorVectorCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) (n : Nat) where
  values : Vector Real n
  index : UpperTrianglePosition k -> Fin n
  value_eq_polynomial :
    forall p : UpperTrianglePosition k,
      p.nonConnector hk ->
        values.get (index p) = p.polynomial F hk
  value_ge_one :
    forall p : UpperTrianglePosition k,
      p.nonConnector hk ->
        1 <= values.get (index p)

namespace UpperTriangleNonConnectorVectorCertificate

/-- Read the stored value at a non-connector upper-triangle position. -/
def value
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n)
    (p : UpperTrianglePosition k) : Real :=
  C.values.get (C.index p)

/-- Convert a vector-backed non-connector certificate to the native
non-connector value-table interface. -/
def toSqValueTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    UpperTriangleNonConnectorSqValueTable F k hk where
  value := fun i u j v =>
    if hlt : i.val < j.val then
      C.value
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }
    else
      0
  value_eq_polynomial_lt := by
    intro i u j v hlt hnot_connector
    rw [dif_pos hlt]
    exact
      C.value_eq_polynomial
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }
        hnot_connector
  value_ge_one_lt := by
    intro i u j v hlt hnot_connector
    rw [dif_pos hlt]
    exact
      C.value_ge_one
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }
        hnot_connector

/-- Concrete non-connector values reduce to non-connector polynomial
inequalities. -/
def toPolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    UpperTriangleNonConnectorPolynomialTable F k hk :=
  C.toSqValueTable.toPolynomialTable

/-- Concrete non-connector values reduce to the finite non-connector
square-distance table needed by the connector-separated route. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  C.toSqValueTable.toNonConnectorSqDistanceTable

/-- Vector-backed non-connector certificates project to the generated
far-apart non-connector `>= 1` lower-table predicate. -/
theorem generatedNonConnectorCrossBlockLowerBoundsAtLeastOne
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    GeneratedSeparationFarApart.GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne
      hk C.toNonConnectorSqDistanceTable.lower := by
  intro _i _u _j _v _hij _hnot_connector
  norm_num [NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable.lower]

/-- Vector-backed non-connector certificates project to the generated
far-apart non-connector squared-distance lower-bound predicate. -/
theorem generatedNonConnectorCrossBlockSqDistanceLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    GeneratedSeparationFarApart.GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      C.toNonConnectorSqDistanceTable.lower := by
  intro i u j v hij hnot_connector
  have hnot_index :
      Not (IndexedCyclicConnectorPair hk i (localVertexIndex u)
        j (localVertexIndex v)) :=
    not_indexedCyclicConnectorPair_of_not_generatedCyclicConnectorPair
      hnot_connector
  simpa [NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable.lower,
    indexedGeneratedSqDist, indexedGeneratedPoint] using
    C.toNonConnectorSqDistanceTable.sqDist_ge_one i (localVertexIndex u)
      j (localVertexIndex v) hij hnot_index

/-- Filling connector slots with their exact squared value gives an all
cross-block generated far-apart `>= 1` lower table. -/
theorem generatedCrossBlockSqLower_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (GeneratedSeparationFarApart.generatedConnectorSeparatedSqLower
        hk C.toNonConnectorSqDistanceTable.lower) :=
  GeneratedSeparationFarApart.generatedConnectorSeparatedSqLower_ge_one
    hk C.toNonConnectorSqDistanceTable.lower
    C.generatedNonConnectorCrossBlockLowerBoundsAtLeastOne

/-- Filling connector slots with their exact squared value gives an all
cross-block generated far-apart squared-distance lower table. -/
theorem generatedCrossBlockSqLower_bound
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    GeneratedSeparationFarApart.GeneratedCrossBlockSqDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      (GeneratedSeparationFarApart.generatedConnectorSeparatedSqLower
        hk C.toNonConnectorSqDistanceTable.lower) :=
  GeneratedSeparationFarApart.generatedConnectorSeparatedSqLower_bound
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (F.orientation k hk)
    C.toNonConnectorSqDistanceTable.periodEquation
    C.toNonConnectorSqDistanceTable.lower
    C.generatedNonConnectorCrossBlockSqDistanceLowerBounds

/-- The connector-completed uniform lower table is at least one on every
generated cross-block pair. -/
theorem generatedCrossBlockLowerBoundsAtLeastOne
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      C.toNonConnectorSqDistanceTable.lower :=
  C.toNonConnectorSqDistanceTable.crossBlock_lower_ge_one

/-- The connector-completed uniform lower table is bounded by generated
cross-block distances. -/
theorem generatedCrossBlockDistanceLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      C.toNonConnectorSqDistanceTable.lower :=
  C.toNonConnectorSqDistanceTable.crossBlock_lower_bound

/-- The actual upper-triangle non-connector square-distance inequality
projected from the stored concrete value. -/
theorem sqDist_ge_one_lt
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= indexedGeneratedSqDist F hk i u j v :=
  C.toPolynomialTable.toUpperTriangleNonConnectorSqDistanceTable
    |>.sqDist_ge_one_lt i u j v hlt hnot_connector

theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleNonConnectorVectorCertificate F k hk n) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toNonConnectorSqDistanceTable.generatedGlobalSeparation

end UpperTriangleNonConnectorVectorCertificate

/-- Constructor form for vector-backed non-connector upper-triangle value
tables. -/
def upperTriangleNonConnectorSqValueTableOfVector
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k) {n : Nat}
    (values : Vector Real n)
    (index : UpperTrianglePosition k -> Fin n)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          1 <= values.get (index p)) :
    UpperTriangleNonConnectorSqValueTable F k hk :=
  (UpperTriangleNonConnectorVectorCertificate.mk
    values index value_eq_polynomial value_ge_one).toSqValueTable

/-- Constructor form for vector-backed non-connector polynomial tables. -/
def upperTriangleNonConnectorPolynomialTableOfVector
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k) {n : Nat}
    (values : Vector Real n)
    (index : UpperTrianglePosition k -> Fin n)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          1 <= values.get (index p)) :
    UpperTriangleNonConnectorPolynomialTable F k hk :=
  (upperTriangleNonConnectorSqValueTableOfVector hk
    values index value_eq_polynomial value_ge_one).toPolynomialTable

/-- Constructor form for vector-backed non-connector square-distance
tables. -/
def indexedNonConnectorCrossBlockSqDistanceTableOfNonConnectorVector
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k) {n : Nat}
    (values : Vector Real n)
    (index : UpperTrianglePosition k -> Fin n)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          1 <= values.get (index p)) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  (UpperTriangleNonConnectorVectorCertificate.mk
    values index value_eq_polynomial value_ge_one).toNonConnectorSqDistanceTable

/-- A list-backed upper-triangle certificate for the connector-separated
route.  Only non-connector packed positions require checked values. -/
structure UpperTriangleNonConnectorListCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  values : List Real
  index : UpperTrianglePosition k -> Fin values.length
  value_eq_polynomial :
    forall p : UpperTrianglePosition k,
      p.nonConnector hk ->
        values.get (index p) = p.polynomial F hk
  value_ge_one :
    forall p : UpperTrianglePosition k,
      p.nonConnector hk ->
        1 <= values.get (index p)

namespace UpperTriangleNonConnectorListCertificate

/-- Read the stored value at a non-connector upper-triangle position. -/
def value
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk)
    (p : UpperTrianglePosition k) : Real :=
  C.values.get (C.index p)

/-- Convert a list-backed non-connector certificate to the native
non-connector value-table interface. -/
def toSqValueTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    UpperTriangleNonConnectorSqValueTable F k hk where
  value := fun i u j v =>
    if hlt : i.val < j.val then
      C.value
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }
    else
      0
  value_eq_polynomial_lt := by
    intro i u j v hlt hnot_connector
    rw [dif_pos hlt]
    exact
      C.value_eq_polynomial
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }
        hnot_connector
  value_ge_one_lt := by
    intro i u j v hlt hnot_connector
    rw [dif_pos hlt]
    exact
      C.value_ge_one
        { left := i
          leftVertex := u
          right := j
          rightVertex := v
          left_lt_right := hlt }
        hnot_connector

/-- Concrete non-connector values reduce to non-connector polynomial
inequalities. -/
def toPolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    UpperTriangleNonConnectorPolynomialTable F k hk :=
  C.toSqValueTable.toPolynomialTable

/-- Concrete non-connector values reduce to the finite non-connector
square-distance table needed by the connector-separated route. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  C.toSqValueTable.toNonConnectorSqDistanceTable

/-- List-backed non-connector certificates project to the generated far-apart
non-connector `>= 1` lower-table predicate. -/
theorem generatedNonConnectorCrossBlockLowerBoundsAtLeastOne
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    GeneratedSeparationFarApart.GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne
      hk C.toNonConnectorSqDistanceTable.lower := by
  intro _i _u _j _v _hij _hnot_connector
  norm_num [NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable.lower]

/-- List-backed non-connector certificates project to the generated far-apart
non-connector squared-distance lower-bound predicate. -/
theorem generatedNonConnectorCrossBlockSqDistanceLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    GeneratedSeparationFarApart.GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      C.toNonConnectorSqDistanceTable.lower := by
  intro i u j v hij hnot_connector
  have hnot_index :
      Not (IndexedCyclicConnectorPair hk i (localVertexIndex u)
        j (localVertexIndex v)) :=
    not_indexedCyclicConnectorPair_of_not_generatedCyclicConnectorPair
      hnot_connector
  simpa [NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable.lower,
    indexedGeneratedSqDist, indexedGeneratedPoint] using
    C.toNonConnectorSqDistanceTable.sqDist_ge_one i (localVertexIndex u)
      j (localVertexIndex v) hij hnot_index

/-- Filling connector slots with their exact squared value gives an all
cross-block generated far-apart `>= 1` lower table. -/
theorem generatedCrossBlockSqLower_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (GeneratedSeparationFarApart.generatedConnectorSeparatedSqLower
        hk C.toNonConnectorSqDistanceTable.lower) :=
  GeneratedSeparationFarApart.generatedConnectorSeparatedSqLower_ge_one
    hk C.toNonConnectorSqDistanceTable.lower
    C.generatedNonConnectorCrossBlockLowerBoundsAtLeastOne

/-- Filling connector slots with their exact squared value gives an all
cross-block generated far-apart squared-distance lower table. -/
theorem generatedCrossBlockSqLower_bound
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockSqDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      (GeneratedSeparationFarApart.generatedConnectorSeparatedSqLower
        hk C.toNonConnectorSqDistanceTable.lower) :=
  GeneratedSeparationFarApart.generatedConnectorSeparatedSqLower_bound
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (F.orientation k hk)
    C.toNonConnectorSqDistanceTable.periodEquation
    C.toNonConnectorSqDistanceTable.lower
    C.generatedNonConnectorCrossBlockSqDistanceLowerBounds

/-- The connector-completed uniform lower table is at least one on every
generated cross-block pair. -/
theorem generatedCrossBlockLowerBoundsAtLeastOne
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      C.toNonConnectorSqDistanceTable.lower :=
  C.toNonConnectorSqDistanceTable.crossBlock_lower_ge_one

/-- The connector-completed uniform lower table is bounded by generated
cross-block distances. -/
theorem generatedCrossBlockDistanceLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      C.toNonConnectorSqDistanceTable.lower :=
  C.toNonConnectorSqDistanceTable.crossBlock_lower_bound

/-- The actual upper-triangle non-connector square-distance inequality
projected from the stored concrete value. -/
theorem sqDist_ge_one_lt
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= indexedGeneratedSqDist F hk i u j v :=
  C.toPolynomialTable.toUpperTriangleNonConnectorSqDistanceTable
    |>.sqDist_ge_one_lt i u j v hlt hnot_connector

theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorListCertificate F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toNonConnectorSqDistanceTable.generatedGlobalSeparation

end UpperTriangleNonConnectorListCertificate

/-- Constructor form for list-backed non-connector upper-triangle value
tables. -/
def upperTriangleNonConnectorSqValueTableOfList
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (values : List Real)
    (index : UpperTrianglePosition k -> Fin values.length)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          1 <= values.get (index p)) :
    UpperTriangleNonConnectorSqValueTable F k hk :=
  (UpperTriangleNonConnectorListCertificate.mk
    values index value_eq_polynomial value_ge_one).toSqValueTable

/-- Constructor form for list-backed non-connector polynomial tables. -/
def upperTriangleNonConnectorPolynomialTableOfList
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (values : List Real)
    (index : UpperTrianglePosition k -> Fin values.length)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          1 <= values.get (index p)) :
    UpperTriangleNonConnectorPolynomialTable F k hk :=
  (upperTriangleNonConnectorSqValueTableOfList hk
    values index value_eq_polynomial value_ge_one).toPolynomialTable

/-- Constructor form for list-backed non-connector square-distance tables. -/
def indexedNonConnectorCrossBlockSqDistanceTableOfNonConnectorList
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (values : List Real)
    (index : UpperTrianglePosition k -> Fin values.length)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        p.nonConnector hk ->
          1 <= values.get (index p)) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  (UpperTriangleNonConnectorListCertificate.mk
    values index value_eq_polynomial value_ge_one).toNonConnectorSqDistanceTable

/-- A family of vector-backed upper-triangle certificates.  The vector length
may depend on the block count. -/
structure UpperTriangleVectorCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  length : forall (k : Nat), 0 < k -> Nat
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleVectorCertificate F k hk (length k hk)

namespace UpperTriangleVectorCertificateFamily

def toSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleVectorCertificateFamily F) :
    UpperTriangleSqValueTableFamily F where
  table := fun k hk => (C.table k hk).toSqValueTable

def toPolynomialTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleVectorCertificateFamily F) :
    UpperTrianglePolynomialTableFamily F :=
  C.toSqValueTableFamily.toPolynomialTableFamily

def toSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleVectorCertificateFamily F) :
    IndexedCrossBlockSqDistanceTableFamily F :=
  C.toSqValueTableFamily.toSqDistanceTableFamily

/-- Vector-backed certificate families provide the non-connector
square-distance table family used when connector pairs are handled separately. -/
def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleVectorCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk =>
    (C.table k hk).toNonConnectorSqDistanceTable

def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleVectorCertificateFamily F) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F :=
  C.toSqValueTableFamily.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleVectorCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleVectorCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteenArbitrary

end UpperTriangleVectorCertificateFamily

/-- A family of list-backed upper-triangle certificates. -/
structure UpperTriangleListCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleListCertificate F k hk

namespace UpperTriangleListCertificateFamily

def toSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleListCertificateFamily F) :
    UpperTriangleSqValueTableFamily F where
  table := fun k hk => (C.table k hk).toSqValueTable

def toPolynomialTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleListCertificateFamily F) :
    UpperTrianglePolynomialTableFamily F :=
  C.toSqValueTableFamily.toPolynomialTableFamily

def toSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleListCertificateFamily F) :
    IndexedCrossBlockSqDistanceTableFamily F :=
  C.toSqValueTableFamily.toSqDistanceTableFamily

/-- List-backed certificate families provide the non-connector
square-distance table family used when connector pairs are handled separately. -/
def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleListCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk =>
    (C.table k hk).toNonConnectorSqDistanceTable

def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleListCertificateFamily F) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F :=
  C.toSqValueTableFamily.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleListCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleListCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteenArbitrary

end UpperTriangleListCertificateFamily

/-! ## Families of concrete non-connector upper-triangle certificates -/

/-- A family of vector-backed non-connector upper-triangle certificates.  The
vector length may depend on the block count. -/
structure UpperTriangleNonConnectorVectorCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  length : forall (k : Nat), 0 < k -> Nat
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleNonConnectorVectorCertificate F k hk (length k hk)

namespace UpperTriangleNonConnectorVectorCertificateFamily

def toSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorVectorCertificateFamily F) :
    UpperTriangleNonConnectorSqValueTableFamily F where
  table := fun k hk => (C.table k hk).toSqValueTable

def toPolynomialTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorVectorCertificateFamily F) :
    UpperTriangleNonConnectorPolynomialTableFamily F :=
  C.toSqValueTableFamily.toPolynomialTableFamily

def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorVectorCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  C.toSqValueTableFamily.toNonConnectorSqDistanceTableFamily

/-- Vector-backed non-connector certificate families expand to the downstream
cross-block lower-bound facade by filling connector slots with `1`. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorVectorCertificateFamily F) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F :=
  C.toNonConnectorSqDistanceTableFamily.toCrossBlockLowerBounds

/-- The induced lower facade supplies the generated far-apart `>= 1`
cross-block predicate at every positive block count. -/
theorem generatedCrossBlockLowerBoundsAtLeastOne
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorVectorCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (C.toCrossBlockLowerBounds.lower k hk) :=
  C.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk

/-- The induced lower facade supplies the generated far-apart cross-block
distance lower-bound predicate at every positive block count. -/
theorem generatedCrossBlockDistanceLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorVectorCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      (C.toCrossBlockLowerBounds.lower k hk) :=
  C.toCrossBlockLowerBounds.toDistanceLowerBounds k hk

/-- Vector-backed non-connector certificate families provide generated global
separation at every positive block count. -/
theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorVectorCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toCrossBlockLowerBounds.separated k hk

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorVectorCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorVectorCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    C.targetUpperConstructionFiveSixteen

end UpperTriangleNonConnectorVectorCertificateFamily

/-- A family of list-backed non-connector upper-triangle certificates. -/
structure UpperTriangleNonConnectorListCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleNonConnectorListCertificate F k hk

namespace UpperTriangleNonConnectorListCertificateFamily

def toSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorListCertificateFamily F) :
    UpperTriangleNonConnectorSqValueTableFamily F where
  table := fun k hk => (C.table k hk).toSqValueTable

def toPolynomialTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorListCertificateFamily F) :
    UpperTriangleNonConnectorPolynomialTableFamily F :=
  C.toSqValueTableFamily.toPolynomialTableFamily

def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorListCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  C.toSqValueTableFamily.toNonConnectorSqDistanceTableFamily

/-- List-backed non-connector certificate families expand to the downstream
cross-block lower-bound facade by filling connector slots with `1`. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorListCertificateFamily F) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F :=
  C.toNonConnectorSqDistanceTableFamily.toCrossBlockLowerBounds

/-- The induced lower facade supplies the generated far-apart `>= 1`
cross-block predicate at every positive block count. -/
theorem generatedCrossBlockLowerBoundsAtLeastOne
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorListCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (C.toCrossBlockLowerBounds.lower k hk) :=
  C.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk

/-- The induced lower facade supplies the generated far-apart cross-block
distance lower-bound predicate at every positive block count. -/
theorem generatedCrossBlockDistanceLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorListCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      (C.toCrossBlockLowerBounds.lower k hk) :=
  C.toCrossBlockLowerBounds.toDistanceLowerBounds k hk

/-- List-backed non-connector certificate families provide generated global
separation at every positive block count. -/
theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorListCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toCrossBlockLowerBounds.separated k hk

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorListCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorListCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    C.targetUpperConstructionFiveSixteen

end UpperTriangleNonConnectorListCertificateFamily

/-- Concrete period-search data plus vector-backed upper-triangle
cross-block certificates. -/
structure VectorConcreteCrossBlockFamily where
  periodSearch : PeriodSearchData
  tables :
    UpperTriangleVectorCertificateFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace VectorConcreteCrossBlockFamily

def toRoleHingedPeriodSearchFamily
    (C : VectorConcreteCrossBlockFamily) :
    RoleHingedPeriodSearchFamily :=
  C.periodSearch.toRoleHingedPeriodSearchFamily

def toSqValueTableFamily
    (C : VectorConcreteCrossBlockFamily) :
    UpperTriangleSqValueTableFamily C.toRoleHingedPeriodSearchFamily :=
  C.tables.toSqValueTableFamily

def toSqDistanceTableFamily
    (C : VectorConcreteCrossBlockFamily) :
    IndexedCrossBlockSqDistanceTableFamily C.toRoleHingedPeriodSearchFamily :=
  C.tables.toSqDistanceTableFamily

def toNonConnectorSqDistanceTableFamily
    (C : VectorConcreteCrossBlockFamily) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : VectorConcreteCrossBlockFamily) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    (C : VectorConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.tables.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : VectorConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.tables.targetUpperConstructionFiveSixteenArbitrary

end VectorConcreteCrossBlockFamily

/-- Concrete period-search data plus list-backed upper-triangle cross-block
certificates. -/
structure ListConcreteCrossBlockFamily where
  periodSearch : PeriodSearchData
  tables :
    UpperTriangleListCertificateFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace ListConcreteCrossBlockFamily

def toRoleHingedPeriodSearchFamily
    (C : ListConcreteCrossBlockFamily) :
    RoleHingedPeriodSearchFamily :=
  C.periodSearch.toRoleHingedPeriodSearchFamily

def toSqValueTableFamily
    (C : ListConcreteCrossBlockFamily) :
    UpperTriangleSqValueTableFamily C.toRoleHingedPeriodSearchFamily :=
  C.tables.toSqValueTableFamily

def toSqDistanceTableFamily
    (C : ListConcreteCrossBlockFamily) :
    IndexedCrossBlockSqDistanceTableFamily C.toRoleHingedPeriodSearchFamily :=
  C.tables.toSqDistanceTableFamily

def toNonConnectorSqDistanceTableFamily
    (C : ListConcreteCrossBlockFamily) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : ListConcreteCrossBlockFamily) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    (C : ListConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.tables.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : ListConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.tables.targetUpperConstructionFiveSixteenArbitrary

end ListConcreteCrossBlockFamily

/-! ## Concrete period-search data with non-connector certificates -/

/-- Concrete period-search data plus vector-backed non-connector
upper-triangle cross-block certificates. -/
structure NonConnectorVectorConcreteCrossBlockFamily where
  periodSearch : PeriodSearchData
  tables :
    UpperTriangleNonConnectorVectorCertificateFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace NonConnectorVectorConcreteCrossBlockFamily

def toRoleHingedPeriodSearchFamily
    (C : NonConnectorVectorConcreteCrossBlockFamily) :
    RoleHingedPeriodSearchFamily :=
  C.periodSearch.toRoleHingedPeriodSearchFamily

def toSqValueTableFamily
    (C : NonConnectorVectorConcreteCrossBlockFamily) :
    UpperTriangleNonConnectorSqValueTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toSqValueTableFamily

def toPolynomialTableFamily
    (C : NonConnectorVectorConcreteCrossBlockFamily) :
    UpperTriangleNonConnectorPolynomialTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toPolynomialTableFamily

def toNonConnectorSqDistanceTableFamily
    (C : NonConnectorVectorConcreteCrossBlockFamily) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : NonConnectorVectorConcreteCrossBlockFamily) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toCrossBlockLowerBounds

theorem generatedCrossBlockLowerBoundsAtLeastOne
    (C : NonConnectorVectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (C.toCrossBlockLowerBounds.lower k hk) :=
  C.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk

theorem generatedCrossBlockDistanceLowerBounds
    (C : NonConnectorVectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      C.toRoleHingedPeriodSearchFamily.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (C.toRoleHingedPeriodSearchFamily.orientation k hk)
      (C.toCrossBlockLowerBounds.lower k hk) :=
  C.toCrossBlockLowerBounds.toDistanceLowerBounds k hk

theorem separated
    (C : NonConnectorVectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.toRoleHingedPeriodSearchFamily.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (C.toRoleHingedPeriodSearchFamily.orientation k hk) :=
  C.toCrossBlockLowerBounds.separated k hk

theorem targetUpperConstructionFiveSixteen
    (C : NonConnectorVectorConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.tables.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : NonConnectorVectorConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.tables.targetUpperConstructionFiveSixteenArbitrary

end NonConnectorVectorConcreteCrossBlockFamily

/-- Concrete period-search data plus list-backed non-connector upper-triangle
cross-block certificates. -/
structure NonConnectorListConcreteCrossBlockFamily where
  periodSearch : PeriodSearchData
  tables :
    UpperTriangleNonConnectorListCertificateFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace NonConnectorListConcreteCrossBlockFamily

def toRoleHingedPeriodSearchFamily
    (C : NonConnectorListConcreteCrossBlockFamily) :
    RoleHingedPeriodSearchFamily :=
  C.periodSearch.toRoleHingedPeriodSearchFamily

def toSqValueTableFamily
    (C : NonConnectorListConcreteCrossBlockFamily) :
    UpperTriangleNonConnectorSqValueTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toSqValueTableFamily

def toPolynomialTableFamily
    (C : NonConnectorListConcreteCrossBlockFamily) :
    UpperTriangleNonConnectorPolynomialTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toPolynomialTableFamily

def toNonConnectorSqDistanceTableFamily
    (C : NonConnectorListConcreteCrossBlockFamily) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : NonConnectorListConcreteCrossBlockFamily) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      C.toRoleHingedPeriodSearchFamily :=
  C.tables.toCrossBlockLowerBounds

theorem generatedCrossBlockLowerBoundsAtLeastOne
    (C : NonConnectorListConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (C.toCrossBlockLowerBounds.lower k hk) :=
  C.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk

theorem generatedCrossBlockDistanceLowerBounds
    (C : NonConnectorListConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      C.toRoleHingedPeriodSearchFamily.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (C.toRoleHingedPeriodSearchFamily.orientation k hk)
      (C.toCrossBlockLowerBounds.lower k hk) :=
  C.toCrossBlockLowerBounds.toDistanceLowerBounds k hk

theorem separated
    (C : NonConnectorListConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.toRoleHingedPeriodSearchFamily.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (C.toRoleHingedPeriodSearchFamily.orientation k hk) :=
  C.toCrossBlockLowerBounds.separated k hk

theorem targetUpperConstructionFiveSixteen
    (C : NonConnectorListConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.tables.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : NonConnectorListConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.tables.targetUpperConstructionFiveSixteenArbitrary

end NonConnectorListConcreteCrossBlockFamily

end

end CrossBlockUpperTriangleConcrete
end PachToth
end ErdosProblems1066
