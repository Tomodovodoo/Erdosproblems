import ErdosProblems1066.PachToth.ConcreteNonConnectorValueMatrix

set_option autoImplicit false

/-!
# Concrete value-certificate examples

This module gives small checked examples for the non-connector value-matrix
surface.  It only instantiates a concrete matrix when the required facts are
already forced by the finite shape itself.  For the next small shape, it names
the exact per-position inequalities that remain to be supplied by a real
finite search.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteValueCertificateExamples

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  ConcreteNonConnectorValueMatrix.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  ConcreteNonConnectorValueMatrix.LocalVertexIndex

abbrev UpperTrianglePosition :=
  ConcreteNonConnectorValueMatrix.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  ConcreteNonConnectorValueMatrix.PositionNonConnector hk p

abbrev NonConnectorValueMatrix :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrix

abbrev PositionValueCertificate :=
  NonConnectorPolynomialCertificates.PositionValueCertificate

abbrev UpperTriangleNonConnectorSqValueVectorCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueVectorCertificate

abbrev UpperTriangleNonConnectorSqValueListCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueListCertificate

def onePositive : 0 < 1 :=
  Nat.zero_lt_succ 0

def twoPositive : 0 < 2 :=
  Nat.zero_lt_succ 1

theorem noUpperTrianglePosition_length_one
    (p : UpperTrianglePosition 1) : False := by
  have hleft : p.left.val < 1 := p.left.isLt
  have hright : p.right.val < 1 := p.right.isLt
  have hlt : p.left.val < p.right.val := p.left_lt_right
  omega

/-- The length-one upper-triangle is empty, so the non-connector value matrix
has no numeric obligations.  The stored value is the polynomial itself rather
than a fabricated numeral. -/
def lengthOneMatrix
    (F : RoleHingedPeriodSearchFamily) :
    NonConnectorValueMatrix F 1 onePositive where
  value := fun p => p.polynomial F onePositive
  value_eq_polynomial := by
    intro _p _hp
    rfl
  value_ge_one := by
    intro p _hp
    exact False.elim (noUpperTrianglePosition_length_one p)

def lengthOnePositionValueCertificate
    (F : RoleHingedPeriodSearchFamily) :
    PositionValueCertificate F 1 onePositive :=
  (lengthOneMatrix F).toPositionValueCertificate

def lengthOneSqValueTable
    (F : RoleHingedPeriodSearchFamily) :
    FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueTable
      F 1 onePositive :=
  (lengthOneMatrix F).toSqValueTable

/-- A generic value-matrix constructor for the case where the finite search
proves the exact polynomial inequality directly at each non-connector packed
position. -/
def matrixOfPerPositionPolynomialInequalities
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k,
        PositionNonConnector hk p ->
          1 <= p.polynomial F hk) :
    NonConnectorValueMatrix F k hk where
  value := fun p => p.polynomial F hk
  value_eq_polynomial := by
    intro _p _hp
    rfl
  value_ge_one := polynomial_ge_one

/-- Repackage an already checked finite vector certificate as a value matrix.
The proof obligations are exactly those of
`FiniteCertificateSearchSurface`; this definition adds no numeric facts. -/
def matrixOfVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F k hk) :
    NonConnectorValueMatrix F k hk :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrix.ofVectorCertificate C

/-- Repackage an already checked finite row-list certificate as a value
matrix. -/
def matrixOfListCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorSqValueListCertificate F k hk) :
    NonConnectorValueMatrix F k hk :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrix.ofListCertificate C

/-- The only strict block pair for length two, with local vertices left
explicit. -/
def lengthTwoPosition
    (u v : LocalVertexIndex) : UpperTrianglePosition 2 where
  left := 0
  leftVertex := u
  right := 1
  rightVertex := v
  left_lt_right := by
    norm_num

/-- The exact missing inequality for one length-two non-connector position.
There is no value assertion here: a generator may fill this only after proving
this concrete packed-position inequality. -/
abbrev LengthTwoMissingNonConnectorInequality
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector twoPositive (lengthTwoPosition u v) ->
    1 <= (lengthTwoPosition u v).polynomial F twoPositive

/-- The full ledger of length-two missing value-matrix inequalities, one for
each local-vertex pair in the unique upper-triangle block position. -/
structure LengthTwoMissingNonConnectorInequalities
    (F : RoleHingedPeriodSearchFamily) where
  inequality :
    forall u v : LocalVertexIndex,
      LengthTwoMissingNonConnectorInequality F u v

end

end ConcreteValueCertificateExamples
end PachToth
end ErdosProblems1066
