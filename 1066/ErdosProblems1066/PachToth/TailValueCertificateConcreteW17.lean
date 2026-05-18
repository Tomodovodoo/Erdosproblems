import ErdosProblems1066.PachToth.TailPolynomialRowsW16

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace TailValueCertificateConcreteW17

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  TailPolynomialRowsW16.RoleHingedPeriodSearchFamily

abbrev PeriodCandidateFamily :=
  TailPolynomialRowsW16.PeriodCandidateFamily

abbrev LocalVertexIndex :=
  TailPolynomialRowsW16.LocalVertexIndex

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  TailPolynomialRowsW16.IndexedCyclicConnectorPair hk i u j v

abbrev TailPolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  TailPolynomialRowsW16.TailPolynomial F hk i u j v

abbrev TailValueRows :=
  TailPolynomialRowsW16.TailValueRows

abbrev TailBlockPairGeneratedPointInequalities :=
  TailPolynomialRowsW16.TailBlockPairGeneratedPointInequalities

abbrev CandidateTailBlockPairInequalities :=
  TailPolynomialRowsW16.CandidateTailBlockPairInequalities

abbrev MissingNonConnectorRows :=
  TailPolynomialRowsW16.MissingNonConnectorRows

abbrev ExactMissingConcreteTableFields :=
  AllPositiveFiniteFieldsW14.ExactMissingConcreteTableFields

structure TailPolynomialCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) (_hgt : 5 < k) where
  polynomial_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= TailPolynomial F hk i u j v

structure TailValueFunctionCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) (_hgt : 5 < k) where
  value : Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_polynomial_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            value i u j v = TailPolynomial F hk i u j v
  value_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= value i u j v

namespace TailPolynomialCertificate

def toValueCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {hgt : 5 < k}
    (C : TailPolynomialCertificate F k hk hgt) :
    TailValueFunctionCertificate F k hk hgt where
  value := fun i u j v => TailPolynomial F hk i u j v
  value_eq_polynomial_lt := by
    intro _i _u _j _v _hlt _hnot
    rfl
  value_ge_one_lt := C.polynomial_ge_one_lt

end TailPolynomialCertificate

namespace TailValueFunctionCertificate

def toPolynomialCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {hgt : 5 < k}
    (C : TailValueFunctionCertificate F k hk hgt) :
    TailPolynomialCertificate F k hk hgt where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot
    have hvalue := C.value_eq_polynomial_lt i u j v hlt hnot
    have hge := C.value_ge_one_lt i u j v hlt hnot
    simpa [hvalue] using hge

end TailValueFunctionCertificate

structure TailPolynomialCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k) (hgt : 5 < k),
      TailPolynomialCertificate F k hk hgt

namespace TailPolynomialCertificateFamily

def toTailValueRows
    {F : RoleHingedPeriodSearchFamily}
    (C : TailPolynomialCertificateFamily F) :
    TailValueRows F where
  value := fun k hk _hgt i u j v => TailPolynomial F hk i u j v
  value_eq_polynomial_lt := by
    intro _k _hk _hgt _i _u _j _v _hlt _hnot
    rfl
  value_ge_one_lt := by
    intro k hk hgt i u j v hlt hnot
    exact
      (C.certificate k hk hgt).polynomial_ge_one_lt
        i u j v hlt hnot

def toBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (C : TailPolynomialCertificateFamily F) :
    TailBlockPairGeneratedPointInequalities F :=
  C.toTailValueRows.toBlockPairInequalities

def toMissingRows
    {F : RoleHingedPeriodSearchFamily}
    (C : TailPolynomialCertificateFamily F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k) :
    MissingNonConnectorRows F k hk :=
  C.toTailValueRows.toMissingRows k hk hgt

end TailPolynomialCertificateFamily

structure TailValueFunctionCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k) (hgt : 5 < k),
      TailValueFunctionCertificate F k hk hgt

namespace TailValueFunctionCertificateFamily

def toTailValueRows
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueFunctionCertificateFamily F) :
    TailValueRows F where
  value := fun k hk hgt =>
    (C.certificate k hk hgt).value
  value_eq_polynomial_lt := by
    intro k hk hgt i u j v hlt hnot
    exact
      (C.certificate k hk hgt).value_eq_polynomial_lt
        i u j v hlt hnot
  value_ge_one_lt := by
    intro k hk hgt i u j v hlt hnot
    exact
      (C.certificate k hk hgt).value_ge_one_lt
        i u j v hlt hnot

def toPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueFunctionCertificateFamily F) :
    TailPolynomialCertificateFamily F where
  certificate := fun k hk hgt =>
    (C.certificate k hk hgt).toPolynomialCertificate

def toBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueFunctionCertificateFamily F) :
    TailBlockPairGeneratedPointInequalities F :=
  C.toTailValueRows.toBlockPairInequalities

def toMissingRows
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueFunctionCertificateFamily F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k) :
    MissingNonConnectorRows F k hk :=
  C.toTailValueRows.toMissingRows k hk hgt

end TailValueFunctionCertificateFamily

structure TailValueRow
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  i : Fin k
  u : LocalVertexIndex
  j : Fin k
  v : LocalVertexIndex
  value : Real
  upper : i.val < j.val
  not_connector : Not (IndexedCyclicConnectorPair hk i u j v)
  value_eq_polynomial : value = TailPolynomial F hk i u j v
  value_ge_one : 1 <= value

namespace TailValueRow

def Matches
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (row : TailValueRow F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  row.i = i /\ row.u = u /\ row.j = j /\ row.v = v

@[simp]
theorem matches_self
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (row : TailValueRow F k hk) :
    row.Matches row.i row.u row.j row.v :=
  And.intro rfl (And.intro rfl (And.intro rfl rfl))

end TailValueRow

structure TailValueListCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) (_hgt : 5 < k) where
  rows : List (TailValueRow F k hk)
  complete :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            Exists fun row =>
              List.Mem row rows /\ TailValueRow.Matches row i u j v

namespace TailValueListCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k} {hgt : 5 < k}

def rowFor
    (C : TailValueListCertificate F k hk hgt)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot : Not (IndexedCyclicConnectorPair hk i u j v)) :
    TailValueRow F k hk :=
  Classical.choose (C.complete i u j v hlt hnot)

theorem rowFor_mem
    (C : TailValueListCertificate F k hk hgt)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot : Not (IndexedCyclicConnectorPair hk i u j v)) :
    List.Mem (C.rowFor i u j v hlt hnot) C.rows :=
  (Classical.choose_spec (C.complete i u j v hlt hnot)).1

theorem rowFor_matches
    (C : TailValueListCertificate F k hk hgt)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot : Not (IndexedCyclicConnectorPair hk i u j v)) :
    TailValueRow.Matches (C.rowFor i u j v hlt hnot) i u j v :=
  (Classical.choose_spec (C.complete i u j v hlt hnot)).2

def value
    (C : TailValueListCertificate F k hk hgt) :
    Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real := by
  classical
  exact fun i u j v =>
    if hlt : i.val < j.val then
      if hnot : Not (IndexedCyclicConnectorPair hk i u j v) then
        (C.rowFor i u j v hlt hnot).value
      else
        TailPolynomial F hk i u j v
    else
      TailPolynomial F hk i u j v

theorem value_eq_polynomial_lt
    (C : TailValueListCertificate F k hk hgt)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot : Not (IndexedCyclicConnectorPair hk i u j v)) :
    C.value i u j v = TailPolynomial F hk i u j v := by
  classical
  dsimp [value]
  rw [dif_pos hlt, dif_pos hnot]
  have hrow :=
    (C.rowFor i u j v hlt hnot).value_eq_polynomial
  have hm := C.rowFor_matches i u j v hlt hnot
  have hi := hm.1
  have hu := hm.2.1
  have hj := hm.2.2.1
  have hv := hm.2.2.2
  simpa [TailValueRow.Matches, hi, hu, hj, hv] using hrow

theorem value_ge_one_lt
    (C : TailValueListCertificate F k hk hgt)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= C.value i u j v := by
  classical
  dsimp [value]
  rw [dif_pos hlt, dif_pos hnot]
  exact (C.rowFor i u j v hlt hnot).value_ge_one

def toValueFunctionCertificate
    (C : TailValueListCertificate F k hk hgt) :
    TailValueFunctionCertificate F k hk hgt where
  value := C.value
  value_eq_polynomial_lt := C.value_eq_polynomial_lt
  value_ge_one_lt := C.value_ge_one_lt

def toPolynomialCertificate
    (C : TailValueListCertificate F k hk hgt) :
    TailPolynomialCertificate F k hk hgt :=
  C.toValueFunctionCertificate.toPolynomialCertificate

end TailValueListCertificate

structure TailValueListCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k) (hgt : 5 < k),
      TailValueListCertificate F k hk hgt

namespace TailValueListCertificateFamily

def toValueFunctionCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueListCertificateFamily F) :
    TailValueFunctionCertificateFamily F where
  certificate := fun k hk hgt =>
    (C.certificate k hk hgt).toValueFunctionCertificate

def toPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueListCertificateFamily F) :
    TailPolynomialCertificateFamily F :=
  C.toValueFunctionCertificateFamily.toPolynomialCertificateFamily

def toTailValueRows
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueListCertificateFamily F) :
    TailValueRows F :=
  C.toValueFunctionCertificateFamily.toTailValueRows

def toBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueListCertificateFamily F) :
    TailBlockPairGeneratedPointInequalities F :=
  C.toTailValueRows.toBlockPairInequalities

def toMissingRows
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueListCertificateFamily F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k) :
    MissingNonConnectorRows F k hk :=
  C.toTailValueRows.toMissingRows k hk hgt

end TailValueListCertificateFamily

def tailValueRowsOfBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (T : TailBlockPairGeneratedPointInequalities F) :
    TailValueRows F where
  value := fun k hk _hgt i u j v => TailPolynomial F hk i u j v
  value_eq_polynomial_lt := by
    intro _k _hk _hgt _i _u _j _v _hlt _hnot
    rfl
  value_ge_one_lt := by
    intro k hk hgt i u j v hlt hnot
    exact T.polynomial_ge_one_lt k hk hgt i u j v hlt hnot

def candidateTailRowsOfValueListCertificateFamily
    {F : PeriodCandidateFamily}
    (C :
      TailValueListCertificateFamily
        F.toRoleHingedPeriodSearchFamily) :
    CandidateTailBlockPairInequalities F :=
  C.toBlockPairInequalities

def exactMissingFieldsOfTailValueRows
    {F : PeriodCandidateFamily}
    (lengthTwo :
      LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthThree :
      LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthFour :
      LengthFourFiveCaseW11.LengthFourMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthFive :
      LengthFourFiveCaseW11.LengthFiveMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (tail :
      TailValueRows F.toRoleHingedPeriodSearchFamily) :
    ExactMissingConcreteTableFields F :=
  TailPolynomialRowsW16.exactMissingFieldsOfMissingRows
    lengthTwo lengthThree lengthFour lengthFive
    (fun k hk hgt => tail.toMissingRows k hk hgt)

def exactMissingFieldsOfTailValueListCertificateFamily
    {F : PeriodCandidateFamily}
    (lengthTwo :
      LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthThree :
      LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthFour :
      LengthFourFiveCaseW11.LengthFourMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthFive :
      LengthFourFiveCaseW11.LengthFiveMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (tail :
      TailValueListCertificateFamily
        F.toRoleHingedPeriodSearchFamily) :
    ExactMissingConcreteTableFields F :=
  exactMissingFieldsOfTailValueRows
    lengthTwo lengthThree lengthFour lengthFive tail.toTailValueRows

end

end TailValueCertificateConcreteW17
end PachToth
end ErdosProblems1066
