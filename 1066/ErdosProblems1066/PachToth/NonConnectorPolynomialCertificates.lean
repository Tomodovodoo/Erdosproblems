import ErdosProblems1066.PachToth.ConcretePeriodCandidateSearch
import ErdosProblems1066.PachToth.CrossBlockPolynomialNormalization
import ErdosProblems1066.PachToth.ExactFamilyClosure
import ErdosProblems1066.PachToth.IndexedCrossBlockTableConcrete

set_option autoImplicit false

/-!
# Non-connector polynomial certificates

This module is the search-facing reduction for the active non-rigid
candidate route.  It does not assert any numerical fact.  Instead, it names
the genuinely reduced finite obligations:

* only upper-triangle block pairs are inspected;
* only non-connector positions require certificates; and
* a generator may either prove the coordinate polynomial is at least `1`
  directly, or provide a computed numeric value equal to that polynomial and
  prove the value is at least `1`.

The endpoint-order normalization and the expansion to the downstream
non-connector square-distance tables are delegated to
`CrossBlockPolynomialNormalization`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonConnectorPolynomialCertificates

open CrossBlockPolynomialNormalization

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockPolynomialNormalization.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockPolynomialNormalization.LocalVertexIndex

abbrev UpperTrianglePosition :=
  CrossBlockPolynomialNormalization.UpperTrianglePosition

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  CrossBlockPolynomialNormalization.IndexedCyclicConnectorPair
    hk i u j v

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  CrossBlockPolynomialNormalization.upperTrianglePositionNonConnector hk p

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  CrossBlockPolynomialNormalization.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  CrossBlockPolynomialNormalization.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev UpperTriangleNonConnectorPolynomialTable :=
  CrossBlockPolynomialNormalization.UpperTriangleNonConnectorPolynomialTable

abbrev UpperTriangleNonConnectorSqValueTable :=
  CrossBlockPolynomialNormalization.UpperTriangleNonConnectorSqValueTable

abbrev PeriodCandidateFamily :=
  ConcretePeriodCandidateSearch.PeriodCandidateFamily

/-! ## One-period reduced obligations -/

/-- The reduced polynomial obligation for one positive block count.

The finite generator only has to certify packed upper-triangle positions that
are not cyclic connector pairs. -/
structure PositionPolynomialCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  polynomial_ge_one :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        1 <= p.polynomial F hk

namespace PositionPolynomialCertificate

/-- Convert reduced position-indexed polynomial facts to the native
upper-triangle non-connector polynomial table interface. -/
def toUpperTriangleNonConnectorPolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionPolynomialCertificate F k hk) :
    UpperTriangleNonConnectorPolynomialTable F k hk :=
  upperTriangleNonConnectorPolynomialTableOfPositionFacts
    hk C.polynomial_ge_one

/-- Convert reduced position-indexed polynomial facts to the downstream
non-connector square-distance table. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionPolynomialCertificate F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  indexedNonConnectorCrossBlockSqDistanceTableOfNonConnectorPositionFacts
    hk C.polynomial_ge_one

/-- The normalized polynomial inequality obtained from the reduced finite
position facts. -/
theorem normalizedPolynomial_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionPolynomialCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= normalizedIndexedGeneratedSqPolynomial F hk i u j v :=
  normalizedPolynomial_ge_one_of_nonConnectorPositionFacts
    hk C.polynomial_ge_one i u j v hij hnot_connector

/-- The original ordered polynomial inequality obtained after endpoint
normalization. -/
theorem orderedPolynomial_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionPolynomialCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
        F hk i u j v :=
  polynomial_ge_one_of_nonConnectorPositionFacts
    hk C.polynomial_ge_one i u j v hij hnot_connector

/-- The normalized squared-distance inequality obtained from the reduced
finite position facts. -/
theorem normalizedSqDist_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionPolynomialCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= normalizedIndexedGeneratedSqDist F hk i u j v :=
  normalizedSqDist_ge_one_of_nonConnectorPositionFacts
    hk C.polynomial_ge_one i u j v hij hnot_connector

/-- The downstream ordered squared-distance inequality, derived from the
polynomial obligation by normalization and square-distance reduction. -/
theorem sqDist_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionPolynomialCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      CrossBlockDistanceSqReduction.indexedGeneratedSqDist
        F hk i u j v :=
  sqDist_ge_one_of_nonConnectorPositionFacts
    hk C.polynomial_ge_one i u j v hij hnot_connector

end PositionPolynomialCertificate

/-- Numeric value facts for one positive block count.

This is the value-table variant of `PositionPolynomialCertificate`: the
generator may compute a value first, prove it equals the normalized
coordinate polynomial on non-connector positions, and prove the value is at
least `1`. -/
structure PositionValueCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  value : UpperTrianglePosition k -> Real
  value_eq_polynomial :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        value p = p.polynomial F hk
  value_ge_one :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        1 <= value p

namespace PositionValueCertificate

/-- Numeric value facts imply the reduced polynomial certificate. -/
def toPositionPolynomialCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionValueCertificate F k hk) :
    PositionPolynomialCertificate F k hk where
  polynomial_ge_one := by
    intro p hp
    have hvalue := C.value_eq_polynomial p hp
    have hge := C.value_ge_one p hp
    simpa [hvalue] using hge

/-- Convert numeric value facts to the native non-connector value-table
interface. -/
def toUpperTriangleNonConnectorSqValueTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionValueCertificate F k hk) :
    UpperTriangleNonConnectorSqValueTable F k hk :=
  upperTriangleNonConnectorSqValueTableOfPositionValueFacts
    hk C.value C.value_eq_polynomial C.value_ge_one

/-- Numeric value facts converted to the downstream non-connector
square-distance table. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionValueCertificate F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  indexedNonConnectorCrossBlockSqDistanceTableOfNonConnectorPositionValueFacts
    hk C.value C.value_eq_polynomial C.value_ge_one

theorem normalizedPolynomial_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionValueCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= normalizedIndexedGeneratedSqPolynomial F hk i u j v :=
  C.toPositionPolynomialCertificate.normalizedPolynomial_ge_one
    i u j v hij hnot_connector

theorem sqDist_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionValueCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      CrossBlockDistanceSqReduction.indexedGeneratedSqDist
        F hk i u j v :=
  C.toPositionPolynomialCertificate.sqDist_ge_one
    i u j v hij hnot_connector

end PositionValueCertificate

/-! ## All-positive families -/

/-- Reduced polynomial certificates for every positive block count of a fixed
period-search family. -/
structure PositionPolynomialCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k),
      PositionPolynomialCertificate F k hk

namespace PositionPolynomialCertificateFamily

def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : PositionPolynomialCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk =>
    (C.certificate k hk).toNonConnectorSqDistanceTable

def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (C : PositionPolynomialCertificateFamily F) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F :=
  C.toNonConnectorSqDistanceTableFamily.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : PositionPolynomialCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toNonConnectorSqDistanceTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : PositionPolynomialCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    C.targetUpperConstructionFiveSixteen

end PositionPolynomialCertificateFamily

/-- Reduced numeric value certificates for every positive block count of a
fixed period-search family. -/
structure PositionValueCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k),
      PositionValueCertificate F k hk

namespace PositionValueCertificateFamily

def toPositionPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : PositionValueCertificateFamily F) :
    PositionPolynomialCertificateFamily F where
  certificate := fun k hk =>
    (C.certificate k hk).toPositionPolynomialCertificate

def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : PositionValueCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk =>
    (C.certificate k hk).toNonConnectorSqDistanceTable

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : PositionValueCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toPositionPolynomialCertificateFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : PositionValueCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toPositionPolynomialCertificateFamily.targetUpperConstructionFiveSixteenArbitrary

end PositionValueCertificateFamily

/-! ## Active candidate-family route -/

/-- Period candidates plus reduced non-connector polynomial certificates.

This is the active search route with finite period equations supplied by
`ConcretePeriodCandidateSearch.PeriodCandidateFamily`; the only remaining
metric obligations are the upper-triangle non-connector polynomial facts. -/
structure CandidatePolynomialCertificateFamily where
  period : PeriodCandidateFamily
  certificates :
    PositionPolynomialCertificateFamily
      period.toRoleHingedPeriodSearchFamily

namespace CandidatePolynomialCertificateFamily

def toRoleHingedPeriodSearchFamily
    (C : CandidatePolynomialCertificateFamily) :
    RoleHingedPeriodSearchFamily :=
  C.period.toRoleHingedPeriodSearchFamily

def toNonConnectorSqDistanceTableFamily
    (C : CandidatePolynomialCertificateFamily) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.certificates.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : CandidatePolynomialCertificateFamily) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      C.toRoleHingedPeriodSearchFamily :=
  C.certificates.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    (C : CandidatePolynomialCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.certificates.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : CandidatePolynomialCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.certificates.targetUpperConstructionFiveSixteenArbitrary

end CandidatePolynomialCertificateFamily

/-- Period candidates plus reduced non-connector numeric value certificates. -/
structure CandidateValueCertificateFamily where
  period : PeriodCandidateFamily
  certificates :
    PositionValueCertificateFamily
      period.toRoleHingedPeriodSearchFamily

namespace CandidateValueCertificateFamily

def toCandidatePolynomialCertificateFamily
    (C : CandidateValueCertificateFamily) :
    CandidatePolynomialCertificateFamily where
  period := C.period
  certificates := C.certificates.toPositionPolynomialCertificateFamily

def toRoleHingedPeriodSearchFamily
    (C : CandidateValueCertificateFamily) :
    RoleHingedPeriodSearchFamily :=
  C.period.toRoleHingedPeriodSearchFamily

def toNonConnectorSqDistanceTableFamily
    (C : CandidateValueCertificateFamily) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      C.toRoleHingedPeriodSearchFamily :=
  C.certificates.toNonConnectorSqDistanceTableFamily

theorem targetUpperConstructionFiveSixteen
    (C : CandidateValueCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toCandidatePolynomialCertificateFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : CandidateValueCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toCandidatePolynomialCertificateFamily.targetUpperConstructionFiveSixteenArbitrary

end CandidateValueCertificateFamily

end

end NonConnectorPolynomialCertificates
end PachToth
end ErdosProblems1066
