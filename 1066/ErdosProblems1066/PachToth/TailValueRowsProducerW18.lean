import ErdosProblems1066.PachToth.TailValueCertificateConcreteW17

set_option autoImplicit false

/-!
# W18 tail value row producer

This module owns the W18 tail-row handoff.  It deliberately does not assert
any generated table data.  Instead, it proves that the only data needed to
produce `TailPolynomialRowsW16.TailValueRows` is the explicit upper-triangle,
non-connector polynomial inequality family, or equivalently the same family
with a concrete value function.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TailValueRowsProducerW18

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
  TailValueCertificateConcreteW17.ExactMissingConcreteTableFields

abbrev TailPolynomialCertificate :=
  TailValueCertificateConcreteW17.TailPolynomialCertificate

abbrev TailValueFunctionCertificate :=
  TailValueCertificateConcreteW17.TailValueFunctionCertificate

abbrev TailPolynomialCertificateFamily :=
  TailValueCertificateConcreteW17.TailPolynomialCertificateFamily

abbrev TailValueFunctionCertificateFamily :=
  TailValueCertificateConcreteW17.TailValueFunctionCertificateFamily

abbrev TailValueListCertificateFamily :=
  TailValueCertificateConcreteW17.TailValueListCertificateFamily

/-- The fully expanded polynomial inequality target for every tail length. -/
abbrev ExplicitTailPolynomialInequalities
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k), 5 < k ->
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= TailPolynomial F hk i u j v

/-- Value-row spelling of the same expanded tail target. -/
structure ExplicitTailValueInequalities
    (F : RoleHingedPeriodSearchFamily) where
  value :
    forall (k : Nat) (_hk : 0 < k), 5 < k ->
      Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_polynomial_lt :
    forall (k : Nat) (hk : 0 < k) (hgt : 5 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            value k hk hgt i u j v = TailPolynomial F hk i u j v
  value_ge_one_lt :
    forall (k : Nat) (hk : 0 < k) (hgt : 5 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= value k hk hgt i u j v

namespace ExplicitTailValueInequalities

def toTailValueRows
    {F : RoleHingedPeriodSearchFamily}
    (V : ExplicitTailValueInequalities F) :
    TailValueRows F where
  value := V.value
  value_eq_polynomial_lt := V.value_eq_polynomial_lt
  value_ge_one_lt := V.value_ge_one_lt

def toPolynomialInequalities
    {F : RoleHingedPeriodSearchFamily}
    (V : ExplicitTailValueInequalities F) :
    ExplicitTailPolynomialInequalities F := by
  intro k hk hgt i u j v hlt hnot
  have hvalue := V.value_ge_one_lt k hk hgt i u j v hlt hnot
  have hpoly := V.value_eq_polynomial_lt k hk hgt i u j v hlt hnot
  simpa [hpoly] using hvalue

end ExplicitTailValueInequalities

/-- A minimal producer: one explicit polynomial lower-bound family. -/
structure TailValueRowsProducer
    (F : RoleHingedPeriodSearchFamily) where
  polynomial_ge_one_lt : ExplicitTailPolynomialInequalities F

namespace TailValueRowsProducer

def toTailValueRows
    {F : RoleHingedPeriodSearchFamily}
    (P : TailValueRowsProducer F) :
    TailValueRows F where
  value := fun k hk _hgt i u j v =>
    TailPolynomial F hk i u j v
  value_eq_polynomial_lt := by
    intro _k _hk _hgt _i _u _j _v _hlt _hnot
    rfl
  value_ge_one_lt := by
    intro k hk hgt i u j v hlt hnot
    exact P.polynomial_ge_one_lt k hk hgt i u j v hlt hnot

def toExplicitValueInequalities
    {F : RoleHingedPeriodSearchFamily}
    (P : TailValueRowsProducer F) :
    ExplicitTailValueInequalities F where
  value := fun k hk _hgt i u j v =>
    TailPolynomial F hk i u j v
  value_eq_polynomial_lt := by
    intro _k _hk _hgt _i _u _j _v _hlt _hnot
    rfl
  value_ge_one_lt := by
    intro k hk hgt i u j v hlt hnot
    exact P.polynomial_ge_one_lt k hk hgt i u j v hlt hnot

def toBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (P : TailValueRowsProducer F) :
    TailBlockPairGeneratedPointInequalities F :=
  P.toTailValueRows.toBlockPairInequalities

def toMissingRows
    {F : RoleHingedPeriodSearchFamily}
    (P : TailValueRowsProducer F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k) :
    MissingNonConnectorRows F k hk :=
  P.toTailValueRows.toMissingRows k hk hgt

def toPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (P : TailValueRowsProducer F) :
    TailPolynomialCertificateFamily F where
  certificate := by
    intro k hk hgt
    exact
      { polynomial_ge_one_lt := by
          intro i u j v hlt hnot
          exact P.polynomial_ge_one_lt k hk hgt i u j v hlt hnot }

def toValueFunctionCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (P : TailValueRowsProducer F) :
    TailValueFunctionCertificateFamily F where
  certificate := by
    intro k hk hgt
    exact (P.toPolynomialCertificateFamily.certificate k hk hgt).toValueCertificate

@[simp]
theorem toTailValueRows_value
    {F : RoleHingedPeriodSearchFamily}
    (P : TailValueRowsProducer F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    P.toTailValueRows.value k hk hgt i u j v =
      TailPolynomial F hk i u j v :=
  rfl

@[simp]
theorem toExplicitValueInequalities_value
    {F : RoleHingedPeriodSearchFamily}
    (P : TailValueRowsProducer F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    P.toExplicitValueInequalities.value k hk hgt i u j v =
      TailPolynomial F hk i u j v :=
  rfl

end TailValueRowsProducer

def producerOfPolynomialInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : ExplicitTailPolynomialInequalities F) :
    TailValueRowsProducer F where
  polynomial_ge_one_lt := H

def tailValueRowsOfPolynomialInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : ExplicitTailPolynomialInequalities F) :
    TailValueRows F :=
  (producerOfPolynomialInequalities H).toTailValueRows

def polynomialInequalitiesOfTailValueRows
    {F : RoleHingedPeriodSearchFamily}
    (V : TailValueRows F) :
    ExplicitTailPolynomialInequalities F := by
  intro k hk hgt i u j v hlt hnot
  exact V.polynomial_ge_one_lt k hk hgt i u j v hlt hnot

def producerOfTailValueRows
    {F : RoleHingedPeriodSearchFamily}
    (V : TailValueRows F) :
    TailValueRowsProducer F where
  polynomial_ge_one_lt := polynomialInequalitiesOfTailValueRows V

def explicitValueInequalitiesOfTailValueRows
    {F : RoleHingedPeriodSearchFamily}
    (V : TailValueRows F) :
    ExplicitTailValueInequalities F where
  value := V.value
  value_eq_polynomial_lt := V.value_eq_polynomial_lt
  value_ge_one_lt := V.value_ge_one_lt

theorem polynomialInequalities_iff_nonempty_tailValueRows
    (F : RoleHingedPeriodSearchFamily) :
    ExplicitTailPolynomialInequalities F <-> Nonempty (TailValueRows F) := by
  exact Iff.intro
    (fun H => Nonempty.intro (tailValueRowsOfPolynomialInequalities H))
    (fun H => H.elim polynomialInequalitiesOfTailValueRows)

def producerOfPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : TailPolynomialCertificateFamily F) :
    TailValueRowsProducer F where
  polynomial_ge_one_lt := by
    intro k hk hgt i u j v hlt hnot
    exact (C.certificate k hk hgt).polynomial_ge_one_lt i u j v hlt hnot

def producerOfValueFunctionCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueFunctionCertificateFamily F) :
    TailValueRowsProducer F :=
  producerOfPolynomialCertificateFamily C.toPolynomialCertificateFamily

def producerOfValueListCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : TailValueListCertificateFamily F) :
    TailValueRowsProducer F :=
  producerOfPolynomialCertificateFamily C.toPolynomialCertificateFamily

abbrev CandidateExplicitTailPolynomialInequalities
    (F : PeriodCandidateFamily) : Prop :=
  ExplicitTailPolynomialInequalities F.toRoleHingedPeriodSearchFamily

abbrev CandidateTailValueRowsProducer
    (F : PeriodCandidateFamily) :=
  TailValueRowsProducer F.toRoleHingedPeriodSearchFamily

abbrev CandidateTailValueRows
    (F : PeriodCandidateFamily) :=
  TailValueRows F.toRoleHingedPeriodSearchFamily

def candidateProducerOfPolynomialInequalities
    {F : PeriodCandidateFamily}
    (H : CandidateExplicitTailPolynomialInequalities F) :
    CandidateTailValueRowsProducer F :=
  producerOfPolynomialInequalities H

def candidateTailValueRowsOfPolynomialInequalities
    {F : PeriodCandidateFamily}
    (H : CandidateExplicitTailPolynomialInequalities F) :
    CandidateTailValueRows F :=
  tailValueRowsOfPolynomialInequalities H

def candidateTailBlockPairInequalitiesOfProducer
    {F : PeriodCandidateFamily}
    (P : CandidateTailValueRowsProducer F) :
    CandidateTailBlockPairInequalities F :=
  P.toBlockPairInequalities

def exactMissingFieldsOfProducer
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
    (tail : CandidateTailValueRowsProducer F) :
    ExactMissingConcreteTableFields F :=
  TailValueCertificateConcreteW17.exactMissingFieldsOfTailValueRows
    lengthTwo lengthThree lengthFour lengthFive tail.toTailValueRows

end

end TailValueRowsProducerW18
end PachToth
end ErdosProblems1066
