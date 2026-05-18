import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.CrossBlockSqTableSearch

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

abbrev IndexedCrossBlockSqDistanceTable :=
  CrossBlockDistanceSqReduction.IndexedCrossBlockSqDistanceTable

abbrev IndexedCrossBlockSqDistanceTableFamily :=
  CrossBlockDistanceSqReduction.IndexedCrossBlockSqDistanceTableFamily

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

end

end CrossBlockUpperTriangleConcrete
end PachToth
end ErdosProblems1066
