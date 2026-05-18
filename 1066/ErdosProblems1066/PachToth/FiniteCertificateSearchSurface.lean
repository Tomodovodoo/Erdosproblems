import ErdosProblems1066.PachToth.FiniteCertificateObligationSummary

set_option autoImplicit false

/-!
# Finite certificate search surface

This module gives generated finite-search output a small, inspectable Lean
surface.  Numeric tables can be supplied either as literal nested `Vector`
grids or as explicit `List` rows.  Lean does not trust the fact that a row came
from an external computation: each consumed entry carries the exact equality to
the generated coordinate polynomial and the required lower-bound inequality.

The definitions below are adapters into the existing Pach--Toth square-table
interfaces.  They introduce no unchecked target theorem; the remaining work is
precisely the finite row/grid equalities and inequalities.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FiniteCertificateSearchSurface

universe u

open CrossBlockSqTableSearch

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockSqTableSearch.LocalVertexIndex

abbrev UpperTriangleSqValueTable :=
  CrossBlockSqTableSearch.UpperTriangleSqValueTable

abbrev UpperTriangleSqValueTableFamily :=
  CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily

abbrev UpperTriangleNonConnectorSqValueTable :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTable

abbrev UpperTriangleNonConnectorSqValueTableFamily :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily

abbrev PeriodSearchData :=
  FiniteCertificateObligationSummary.PeriodSearchData

abbrev SqValueCertificate :=
  FiniteCertificateObligationSummary.SqValueCertificate

/-! ## Literal vector grids -/

namespace Grid4

/-- A four-dimensional finite table, stored as nested literal vectors. -/
abbrev Table (alpha : Type u) (a b c d : Nat) :=
  Vector (Vector (Vector (Vector alpha d) c) b) a

/-- Read a four-dimensional finite table by its checked finite indices. -/
def get {alpha : Type u} {a b c d : Nat}
    (values : Table alpha a b c d)
    (i : Fin a) (u : Fin b) (j : Fin c) (v : Fin d) : alpha :=
  (((values.get i).get u).get j).get v

end Grid4

/-- The literal generated square-value grid for one block count. -/
abbrev SqValueGrid (k : Nat) :=
  Grid4.Table Real k 16 k 16

namespace SqValueGrid

/-- Read the value stored for one generated cross-block local-vertex pair. -/
def get {k : Nat}
    (values : SqValueGrid k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  Grid4.get values i u j v

end SqValueGrid

/-- A checked upper-triangle square-value grid.

The `values` field is the literal table generated externally.  The two proof
fields are the exact remaining obligations for every consumed upper-triangle
entry. -/
structure UpperTriangleSqValueVectorCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  values : SqValueGrid k
  value_eq_polynomial_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          SqValueGrid.get values i u j v =
            indexedGeneratedSqPolynomial F hk i u j v
  value_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val -> 1 <= SqValueGrid.get values i u j v

namespace UpperTriangleSqValueVectorCertificate

/-- The total value function induced by the literal vector grid. -/
def value
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleSqValueVectorCertificate F k hk) :
    Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real :=
  SqValueGrid.get C.values

@[simp]
theorem value_apply
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleSqValueVectorCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    C.value i u j v = SqValueGrid.get C.values i u j v :=
  rfl

/-- Project a checked literal grid to the existing upper-triangle table
interface. -/
def toSqValueTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleSqValueVectorCertificate F k hk) :
    UpperTriangleSqValueTable F k hk where
  value := C.value
  value_eq_polynomial_lt := by
    intro i u j v hlt
    exact C.value_eq_polynomial_lt i u j v hlt
  value_ge_one_lt := by
    intro i u j v hlt
    exact C.value_ge_one_lt i u j v hlt

@[simp]
theorem toSqValueTable_value
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleSqValueVectorCertificate F k hk) :
    C.toSqValueTable.value = C.value :=
  rfl

end UpperTriangleSqValueVectorCertificate

/-- A checked literal grid for the connector-separated non-connector route. -/
structure UpperTriangleNonConnectorSqValueVectorCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  values : SqValueGrid k
  value_eq_polynomial_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            SqValueGrid.get values i u j v =
              indexedGeneratedSqPolynomial F hk i u j v
  value_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= SqValueGrid.get values i u j v

namespace UpperTriangleNonConnectorSqValueVectorCertificate

def value
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F k hk) :
    Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real :=
  SqValueGrid.get C.values

@[simp]
theorem value_apply
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    C.value i u j v = SqValueGrid.get C.values i u j v :=
  rfl

def toSqValueTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F k hk) :
    UpperTriangleNonConnectorSqValueTable F k hk where
  value := C.value
  value_eq_polynomial_lt := by
    intro i u j v hlt hnot_connector
    exact C.value_eq_polynomial_lt i u j v hlt hnot_connector
  value_ge_one_lt := by
    intro i u j v hlt hnot_connector
    exact C.value_ge_one_lt i u j v hlt hnot_connector

@[simp]
theorem toSqValueTable_value
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F k hk) :
    C.toSqValueTable.value = C.value :=
  rfl

end UpperTriangleNonConnectorSqValueVectorCertificate

/-! ## Explicit list rows -/

/-- The address and numeric value of one square-table entry. -/
structure SqValueRow (k : Nat) where
  i : Fin k
  u : LocalVertexIndex
  j : Fin k
  v : LocalVertexIndex
  value : Real

namespace SqValueRow

/-- The row addresses a particular generated local-vertex pair. -/
def Matches {k : Nat}
    (row : SqValueRow k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  row.i = i /\ row.u = u /\ row.j = j /\ row.v = v

@[simp]
theorem matches_self {k : Nat} (row : SqValueRow k) :
    row.Matches row.i row.u row.j row.v := by
  exact And.intro rfl (And.intro rfl (And.intro rfl rfl))

end SqValueRow

/-- A list row whose value has already been checked against the generated
coordinate polynomial and the `>= 1` bound. -/
structure UpperTriangleSqValueRowCertificate
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k) extends SqValueRow k where
  upper : i.val < j.val
  value_eq_polynomial :
    value = indexedGeneratedSqPolynomial F hk i u j v
  value_ge_one : 1 <= value

namespace UpperTriangleSqValueRowCertificate

def Matches
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (row : UpperTriangleSqValueRowCertificate F hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  row.toSqValueRow.Matches i u j v

end UpperTriangleSqValueRowCertificate

/-- A row-list certificate for all upper-triangle entries.

The list itself is explicit.  The `complete` field is the finite coverage
obligation: every upper-triangle address consumed downstream appears in the
list with row-local equality and inequality proofs. -/
structure UpperTriangleSqValueListCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  rows : List (UpperTriangleSqValueRowCertificate F hk)
  complete :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Exists fun row =>
            List.Mem row rows /\
              UpperTriangleSqValueRowCertificate.Matches row i u j v

namespace UpperTriangleSqValueListCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

/-- The checked row selected by finite coverage for an upper-triangle entry. -/
def rowFor
    (C : UpperTriangleSqValueListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    UpperTriangleSqValueRowCertificate F hk :=
  Classical.choose (C.complete i u j v hlt)

theorem rowFor_mem
    (C : UpperTriangleSqValueListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    List.Mem (C.rowFor i u j v hlt) C.rows :=
  (Classical.choose_spec (C.complete i u j v hlt)).1

theorem rowFor_matches
    (C : UpperTriangleSqValueListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    UpperTriangleSqValueRowCertificate.Matches
      (C.rowFor i u j v hlt) i u j v :=
  (Classical.choose_spec (C.complete i u j v hlt)).2

/-- Total value function induced by the row list.  Non-upper-triangle slots
are irrelevant to the downstream interface and are filled with `0`. -/
def value
    (C : UpperTriangleSqValueListCertificate F k hk) :
    Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real := by
  classical
  exact fun i u j v =>
    if hlt : i.val < j.val then
      (C.rowFor i u j v hlt).value
    else
      0

theorem value_eq_polynomial_lt
    (C : UpperTriangleSqValueListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    C.value i u j v = indexedGeneratedSqPolynomial F hk i u j v := by
  classical
  dsimp [value]
  rw [dif_pos hlt]
  have hrow := (C.rowFor i u j v hlt).value_eq_polynomial
  have hm := C.rowFor_matches i u j v hlt
  have hi := hm.1
  have hu := hm.2.1
  have hj := hm.2.2.1
  have hv := hm.2.2.2
  simpa [UpperTriangleSqValueRowCertificate.Matches,
    SqValueRow.Matches, hi, hu, hj, hv] using hrow

theorem value_ge_one_lt
    (C : UpperTriangleSqValueListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    1 <= C.value i u j v := by
  classical
  dsimp [value]
  rw [dif_pos hlt]
  exact (C.rowFor i u j v hlt).value_ge_one

def toSqValueTable
    (C : UpperTriangleSqValueListCertificate F k hk) :
    UpperTriangleSqValueTable F k hk where
  value := C.value
  value_eq_polynomial_lt := by
    intro i u j v hlt
    exact C.value_eq_polynomial_lt i u j v hlt
  value_ge_one_lt := by
    intro i u j v hlt
    exact C.value_ge_one_lt i u j v hlt

end UpperTriangleSqValueListCertificate

/-- A checked list row for the connector-separated non-connector route. -/
structure UpperTriangleNonConnectorSqValueRowCertificate
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k) extends SqValueRow k where
  upper : i.val < j.val
  not_connector : Not (IndexedCyclicConnectorPair hk i u j v)
  value_eq_polynomial :
    value = indexedGeneratedSqPolynomial F hk i u j v
  value_ge_one : 1 <= value

namespace UpperTriangleNonConnectorSqValueRowCertificate

def Matches
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (row : UpperTriangleNonConnectorSqValueRowCertificate F hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  row.toSqValueRow.Matches i u j v

end UpperTriangleNonConnectorSqValueRowCertificate

/-- Explicit row-list certificate for all upper-triangle non-connector
entries. -/
structure UpperTriangleNonConnectorSqValueListCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  rows : List (UpperTriangleNonConnectorSqValueRowCertificate F hk)
  complete :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            Exists fun row =>
              List.Mem row rows /\
                UpperTriangleNonConnectorSqValueRowCertificate.Matches
                  row i u j v

namespace UpperTriangleNonConnectorSqValueListCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

def rowFor
    (C : UpperTriangleNonConnectorSqValueListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    UpperTriangleNonConnectorSqValueRowCertificate F hk :=
  Classical.choose (C.complete i u j v hlt hnot_connector)

theorem rowFor_mem
    (C : UpperTriangleNonConnectorSqValueListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    List.Mem (C.rowFor i u j v hlt hnot_connector) C.rows :=
  (Classical.choose_spec
    (C.complete i u j v hlt hnot_connector)).1

theorem rowFor_matches
    (C : UpperTriangleNonConnectorSqValueListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    UpperTriangleNonConnectorSqValueRowCertificate.Matches
      (C.rowFor i u j v hlt hnot_connector) i u j v :=
  (Classical.choose_spec
    (C.complete i u j v hlt hnot_connector)).2

/-- Total value function induced by the non-connector row list.  Entries not
used by the non-connector table are filled with `0`. -/
def value
    (C : UpperTriangleNonConnectorSqValueListCertificate F k hk) :
    Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real := by
  classical
  exact fun i u j v =>
    if hlt : i.val < j.val then
      if hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v) then
        (C.rowFor i u j v hlt hnot_connector).value
      else
        0
    else
      0

theorem value_eq_polynomial_lt
    (C : UpperTriangleNonConnectorSqValueListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    C.value i u j v = indexedGeneratedSqPolynomial F hk i u j v := by
  classical
  dsimp [value]
  rw [dif_pos hlt, dif_pos hnot_connector]
  have hrow :=
    (C.rowFor i u j v hlt hnot_connector).value_eq_polynomial
  have hm := C.rowFor_matches i u j v hlt hnot_connector
  have hi := hm.1
  have hu := hm.2.1
  have hj := hm.2.2.1
  have hv := hm.2.2.2
  simpa [UpperTriangleNonConnectorSqValueRowCertificate.Matches,
    SqValueRow.Matches, hi, hu, hj, hv] using hrow

theorem value_ge_one_lt
    (C : UpperTriangleNonConnectorSqValueListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= C.value i u j v := by
  classical
  dsimp [value]
  rw [dif_pos hlt, dif_pos hnot_connector]
  exact (C.rowFor i u j v hlt hnot_connector).value_ge_one

def toSqValueTable
    (C : UpperTriangleNonConnectorSqValueListCertificate F k hk) :
    UpperTriangleNonConnectorSqValueTable F k hk where
  value := C.value
  value_eq_polynomial_lt := by
    intro i u j v hlt hnot_connector
    exact C.value_eq_polynomial_lt i u j v hlt hnot_connector
  value_ge_one_lt := by
    intro i u j v hlt hnot_connector
    exact C.value_ge_one_lt i u j v hlt hnot_connector

end UpperTriangleNonConnectorSqValueListCertificate

/-! ## Family adapters -/

structure UpperTriangleSqValueVectorCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleSqValueVectorCertificate F k hk

namespace UpperTriangleSqValueVectorCertificateFamily

def toSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleSqValueVectorCertificateFamily F) :
    UpperTriangleSqValueTableFamily F where
  table := fun k hk => (C.table k hk).toSqValueTable

def toSqValueCertificate
    {periodSearch : PeriodSearchData}
    (C :
      UpperTriangleSqValueVectorCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily) :
    SqValueCertificate periodSearch where
  value := fun k hk => (C.table k hk).value
  value_eq_polynomial_lt := by
    intro k hk i u j v hlt
    exact (C.table k hk).value_eq_polynomial_lt i u j v hlt
  value_ge_one_lt := by
    intro k hk i u j v hlt
    exact (C.table k hk).value_ge_one_lt i u j v hlt

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleSqValueVectorCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleSqValueVectorCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteenArbitrary

end UpperTriangleSqValueVectorCertificateFamily

structure UpperTriangleSqValueListCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleSqValueListCertificate F k hk

namespace UpperTriangleSqValueListCertificateFamily

def toSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleSqValueListCertificateFamily F) :
    UpperTriangleSqValueTableFamily F where
  table := fun k hk => (C.table k hk).toSqValueTable

def toSqValueCertificate
    {periodSearch : PeriodSearchData}
    (C :
      UpperTriangleSqValueListCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily) :
    SqValueCertificate periodSearch where
  value := fun k hk => (C.table k hk).value
  value_eq_polynomial_lt := by
    intro k hk i u j v hlt
    exact (C.table k hk).value_eq_polynomial_lt i u j v hlt
  value_ge_one_lt := by
    intro k hk i u j v hlt
    exact (C.table k hk).value_ge_one_lt i u j v hlt

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleSqValueListCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleSqValueListCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteenArbitrary

end UpperTriangleSqValueListCertificateFamily

structure UpperTriangleNonConnectorSqValueVectorCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleNonConnectorSqValueVectorCertificate F k hk

namespace UpperTriangleNonConnectorSqValueVectorCertificateFamily

def toSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificateFamily F) :
    UpperTriangleNonConnectorSqValueTableFamily F where
  table := fun k hk => (C.table k hk).toSqValueTable

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    C.targetUpperConstructionFiveSixteen

end UpperTriangleNonConnectorSqValueVectorCertificateFamily

structure UpperTriangleNonConnectorSqValueListCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleNonConnectorSqValueListCertificate F k hk

namespace UpperTriangleNonConnectorSqValueListCertificateFamily

def toSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificateFamily F) :
    UpperTriangleNonConnectorSqValueTableFamily F where
  table := fun k hk => (C.table k hk).toSqValueTable

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toSqValueTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    C.targetUpperConstructionFiveSixteen

end UpperTriangleNonConnectorSqValueListCertificateFamily

end

end FiniteCertificateSearchSurface
end PachToth
end ErdosProblems1066
