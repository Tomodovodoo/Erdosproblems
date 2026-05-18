import ErdosProblems1066.PachToth.GeneratedPointPolynomialFacts
import ErdosProblems1066.PachToth.GeneratedPointDistanceFacts
import ErdosProblems1066.PachToth.PolynomialCertificateExtraction
import ErdosProblems1066.PachToth.GeneratedPolynomialLowerTableRoute
import ErdosProblems1066.PachToth.CrossBlockLowerBoundSearchW9

set_option autoImplicit false

/-!
# W10 generated-point normalization adapters

This module keeps generated-point square-polynomial normalization reusable at
the certificate boundary.  It adds no numeric certificates: every route below
only transports caller-supplied polynomial or value facts from the normalized
generated-point spelling to the existing W9 polynomial, value-matrix, and lower
table interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedPointNormalizationW10

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  PolynomialCertificateExtraction.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  PolynomialCertificateExtraction.LocalVertexIndex

abbrev UpperTrianglePosition :=
  PolynomialCertificateExtraction.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  PolynomialCertificateExtraction.PositionNonConnector hk p

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  PolynomialCertificateExtraction.IndexedCyclicConnectorPair hk i u j v

abbrev GeneratedPointPositionPolynomialCertificate :=
  PolynomialCertificateExtraction.GeneratedPointPositionPolynomialCertificate

abbrev GeneratedPointPositionValueCertificate :=
  PolynomialCertificateExtraction.GeneratedPointPositionValueCertificate

abbrev GeneratedPointPolynomialCertificateFamily :=
  PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily

abbrev GeneratedPointValueCertificateFamily :=
  PolynomialCertificateExtraction.GeneratedPointValueCertificateFamily

abbrev GeneratedPointNonConnectorPolynomialTable :=
  GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTable

abbrev GeneratedPointNonConnectorPolynomialTableFamily :=
  GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTableFamily

abbrev NonConnectorValueMatrix :=
  PolynomialCertificateExtraction.NonConnectorValueMatrix

abbrev NonConnectorValueMatrixFamily :=
  PolynomialCertificateExtraction.NonConnectorValueMatrixFamily

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  PolynomialCertificateExtraction.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  PolynomialCertificateExtraction.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev CrossBlockLowerBounds :=
  PolynomialCertificateExtraction.CrossBlockLowerBounds

abbrev W9GeneratedPolynomialCertificate :=
  CrossBlockLowerBoundSearchW9.GeneratedPolynomialCertificate

abbrev W9GeneratedPolynomialCertificateFamily :=
  CrossBlockLowerBoundSearchW9.GeneratedPolynomialCertificateFamily

/-- A packed upper-triangle position always has distinct block endpoints. -/
theorem upperTrianglePosition_ne
    {k : Nat} (p : UpperTrianglePosition k) :
    Ne p.left p.right := by
  intro h
  exact (Nat.lt_irrefl p.left.val) (by
    simpa [h] using p.left_lt_right)

/-! ## Generated-point spelling equalities -/

/-- The generated-polynomial route spelling is the normalized local generated
point polynomial. -/
theorem indexedGeneratedPointSqPolynomial_eq_normalizedGeneratedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
        F hk i u j v =
      GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
  calc
    GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
        F hk i u j v =
        CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
          F hk i u j v := by
      exact
        (GeneratedPolynomialLowerTableRoute.indexedGeneratedSqPolynomial_eq_generatedPoint
          F hk i u j v).symm
    _ =
      GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
      exact
        GeneratedPointPolynomialFacts.indexedGeneratedSqPolynomial_eq_normalizedGeneratedPoint
          F hk i u j v

/-- The generated-polynomial route spelling is the normalized indexed
polynomial used by the cross-block normalization layer. -/
theorem indexedGeneratedPointSqPolynomial_eq_normalizedIndexed
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
        F hk i u j v =
      CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial
        F hk i u j v := by
  calc
    GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
        F hk i u j v =
        CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
          F hk i u j v := by
      exact
        (GeneratedPolynomialLowerTableRoute.indexedGeneratedSqPolynomial_eq_generatedPoint
          F hk i u j v).symm
    _ =
        CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial
          F hk i u j v := by
      exact
        CrossBlockPolynomialNormalization.indexedGeneratedSqPolynomial_eq_normalized
          F hk i u j v

/-- Packed upper-triangle polynomials are normalized generated-point
polynomials at the same endpoints. -/
theorem upperTrianglePosition_polynomial_eq_normalizedGeneratedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (p : UpperTrianglePosition k) :
    p.polynomial F hk =
      GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        p.left (CrossBlockLowerBoundsInterface.localVertexOfIndex p.leftVertex)
        p.right (CrossBlockLowerBoundsInterface.localVertexOfIndex p.rightVertex) := by
  exact
    GeneratedPointPolynomialFacts.indexedGeneratedSqPolynomial_eq_normalizedGeneratedPoint
      F hk p.left p.leftVertex p.right p.rightVertex

/-- Packed upper-triangle square distances are normalized generated-point
square distances at the same endpoints. -/
theorem upperTrianglePosition_sqDist_eq_normalizedGeneratedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (p : UpperTrianglePosition k) :
    p.sqDist F hk =
      GeneratedPointPolynomialFacts.normalizedGeneratedPointSqDist
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        p.left (CrossBlockLowerBoundsInterface.localVertexOfIndex p.leftVertex)
        p.right (CrossBlockLowerBoundsInterface.localVertexOfIndex p.rightVertex) := by
  exact
    GeneratedPointPolynomialFacts.indexedGeneratedSqDist_eq_normalizedGeneratedPoint
      F hk p.left p.leftVertex p.right p.rightVertex

/-! ## Position-indexed normalized polynomial certificates -/

/-- Reduced upper-triangle facts whose target is already the normalized
generated-point polynomial. -/
structure NormalizedGeneratedPointPositionPolynomialCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  polynomial_ge_one :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        1 <=
          GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
            F.transitions.toFigure2TransitionObligations
            hk BaseTransitionRealization.exactBase (F.orientation k hk)
            p.left
            (CrossBlockLowerBoundsInterface.localVertexOfIndex p.leftVertex)
            p.right
            (CrossBlockLowerBoundsInterface.localVertexOfIndex p.rightVertex)

namespace NormalizedGeneratedPointPositionPolynomialCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

def toGeneratedPointPositionPolynomialCertificate
    (C : NormalizedGeneratedPointPositionPolynomialCertificate F k hk) :
    GeneratedPointPositionPolynomialCertificate F k hk where
  polynomial_ge_one := by
    intro p hp
    have h := C.polynomial_ge_one p hp
    simpa [indexedGeneratedPointSqPolynomial_eq_normalizedGeneratedPoint
        F hk p.left p.leftVertex p.right p.rightVertex] using h

def toW9GeneratedPolynomialCertificate
    (C : NormalizedGeneratedPointPositionPolynomialCertificate F k hk) :
    W9GeneratedPolynomialCertificate F k hk where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot_connector
    exact
      C.toGeneratedPointPositionPolynomialCertificate
        |>.toGeneratedPointNonConnectorPolynomialTable
        |>.polynomial_ge_one_lt i u j v hlt hnot_connector

def toGeneratedPointNonConnectorPolynomialTable
    (C : NormalizedGeneratedPointPositionPolynomialCertificate F k hk) :
    GeneratedPointNonConnectorPolynomialTable F k hk :=
  C.toGeneratedPointPositionPolynomialCertificate
    |>.toGeneratedPointNonConnectorPolynomialTable

def toNonConnectorValueFreeSqDistanceTable
    (C : NormalizedGeneratedPointPositionPolynomialCertificate F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  C.toGeneratedPointPositionPolynomialCertificate.toNonConnectorSqDistanceTable

theorem normalizedIndexedPolynomial_ge_one
    (C : NormalizedGeneratedPointPositionPolynomialCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial
        F hk i u j v :=
  C.toGeneratedPointPositionPolynomialCertificate.normalizedIndexedPolynomial_ge_one
    i u j v hij hnot_connector

theorem normalizedGeneratedPointPolynomial_ge_one
    (C : NormalizedGeneratedPointPositionPolynomialCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) :=
  C.toGeneratedPointPositionPolynomialCertificate
    |>.normalizedGeneratedPointPolynomial_ge_one
      i u j v hij hnot_connector

theorem indexedGeneratedPointPolynomial_ge_one
    (C : NormalizedGeneratedPointPositionPolynomialCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
        F hk i u j v := by
  rw [indexedGeneratedPointSqPolynomial_eq_normalizedGeneratedPoint F hk i u j v]
  exact C.normalizedGeneratedPointPolynomial_ge_one
    i u j v hij hnot_connector

theorem generatedGlobalSeparation
    (C : NormalizedGeneratedPointPositionPolynomialCertificate F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toGeneratedPointPositionPolynomialCertificate.generatedGlobalSeparation

end NormalizedGeneratedPointPositionPolynomialCertificate

/-! ## Position-indexed normalized value certificates -/

/-- Reduced upper-triangle value facts whose equality target is the
normalized generated-point polynomial. -/
structure NormalizedGeneratedPointPositionValueCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  value : UpperTrianglePosition k -> Real
  value_eq_normalizedGeneratedPointPolynomial :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        value p =
          GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
            F.transitions.toFigure2TransitionObligations
            hk BaseTransitionRealization.exactBase (F.orientation k hk)
            p.left
            (CrossBlockLowerBoundsInterface.localVertexOfIndex p.leftVertex)
            p.right
            (CrossBlockLowerBoundsInterface.localVertexOfIndex p.rightVertex)
  value_ge_one :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p -> 1 <= value p

namespace NormalizedGeneratedPointPositionValueCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

def toNormalizedGeneratedPointPositionPolynomialCertificate
    (C : NormalizedGeneratedPointPositionValueCertificate F k hk) :
    NormalizedGeneratedPointPositionPolynomialCertificate F k hk where
  polynomial_ge_one := by
    intro p hp
    have hvalue := C.value_eq_normalizedGeneratedPointPolynomial p hp
    have hge := C.value_ge_one p hp
    simpa [hvalue] using hge

def toGeneratedPointPositionValueCertificate
    (C : NormalizedGeneratedPointPositionValueCertificate F k hk) :
    GeneratedPointPositionValueCertificate F k hk where
  value := C.value
  value_eq_generatedPolynomial := by
    intro p hp
    have h := C.value_eq_normalizedGeneratedPointPolynomial p hp
    simpa [indexedGeneratedPointSqPolynomial_eq_normalizedGeneratedPoint
        F hk p.left p.leftVertex p.right p.rightVertex] using h
  value_ge_one := C.value_ge_one

def toNonConnectorValueMatrix
    (C : NormalizedGeneratedPointPositionValueCertificate F k hk) :
    NonConnectorValueMatrix F k hk :=
  C.toGeneratedPointPositionValueCertificate.toNonConnectorValueMatrix

def toW9GeneratedPolynomialCertificate
    (C : NormalizedGeneratedPointPositionValueCertificate F k hk) :
    W9GeneratedPolynomialCertificate F k hk :=
  C.toNormalizedGeneratedPointPositionPolynomialCertificate
    |>.toW9GeneratedPolynomialCertificate

def toGeneratedPointNonConnectorPolynomialTable
    (C : NormalizedGeneratedPointPositionValueCertificate F k hk) :
    GeneratedPointNonConnectorPolynomialTable F k hk :=
  C.toGeneratedPointPositionValueCertificate
    |>.toGeneratedPointNonConnectorPolynomialTable

def toNonConnectorSqDistanceTable
    (C : NormalizedGeneratedPointPositionValueCertificate F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  C.toGeneratedPointPositionValueCertificate.toNonConnectorSqDistanceTable

theorem normalizedGeneratedPointPolynomial_ge_one
    (C : NormalizedGeneratedPointPositionValueCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) :=
  C.toNormalizedGeneratedPointPositionPolynomialCertificate
    |>.normalizedGeneratedPointPolynomial_ge_one
      i u j v hij hnot_connector

theorem indexedGeneratedPointPolynomial_ge_one
    (C : NormalizedGeneratedPointPositionValueCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
        F hk i u j v :=
  C.toNormalizedGeneratedPointPositionPolynomialCertificate
    |>.indexedGeneratedPointPolynomial_ge_one
      i u j v hij hnot_connector

theorem generatedGlobalSeparation
    (C : NormalizedGeneratedPointPositionValueCertificate F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toGeneratedPointPositionValueCertificate
    |>.toGeneratedPointPositionPolynomialCertificate
    |>.generatedGlobalSeparation

end NormalizedGeneratedPointPositionValueCertificate

/-! ## Arbitrary indexed normalized certificates -/

/-- Arbitrary ordered non-connector facts for normalized generated-point
polynomials.  Transport to packed upper-triangle positions supplies the W9
certificate surface. -/
structure NormalizedIndexedGeneratedPointPolynomialCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  polynomial_ge_one :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <=
              GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
                F.transitions.toFigure2TransitionObligations
                hk BaseTransitionRealization.exactBase (F.orientation k hk)
                i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
                j (CrossBlockLowerBoundsInterface.localVertexOfIndex v)

namespace NormalizedIndexedGeneratedPointPolynomialCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

def toNormalizedGeneratedPointPositionPolynomialCertificate
    (C : NormalizedIndexedGeneratedPointPolynomialCertificate F k hk) :
    NormalizedGeneratedPointPositionPolynomialCertificate F k hk where
  polynomial_ge_one := by
    intro p hp
    exact C.polynomial_ge_one
      p.left p.leftVertex p.right p.rightVertex
      (upperTrianglePosition_ne p) hp

def toGeneratedPointPositionPolynomialCertificate
    (C : NormalizedIndexedGeneratedPointPolynomialCertificate F k hk) :
    GeneratedPointPositionPolynomialCertificate F k hk :=
  C.toNormalizedGeneratedPointPositionPolynomialCertificate
    |>.toGeneratedPointPositionPolynomialCertificate

def toW9GeneratedPolynomialCertificate
    (C : NormalizedIndexedGeneratedPointPolynomialCertificate F k hk) :
    W9GeneratedPolynomialCertificate F k hk :=
  C.toNormalizedGeneratedPointPositionPolynomialCertificate
    |>.toW9GeneratedPolynomialCertificate

theorem indexedGeneratedPointPolynomial_ge_one
    (C : NormalizedIndexedGeneratedPointPolynomialCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
        F hk i u j v := by
  rw [indexedGeneratedPointSqPolynomial_eq_normalizedGeneratedPoint F hk i u j v]
  exact C.polynomial_ge_one i u j v hij hnot_connector

theorem generatedGlobalSeparation
    (C : NormalizedIndexedGeneratedPointPolynomialCertificate F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toGeneratedPointPositionPolynomialCertificate.generatedGlobalSeparation

end NormalizedIndexedGeneratedPointPolynomialCertificate

/-- Arbitrary ordered non-connector value facts for normalized generated-point
polynomials. -/
structure NormalizedIndexedGeneratedPointValueCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  value :
    forall (i : Fin k) (_u : LocalVertexIndex)
      (j : Fin k) (_v : LocalVertexIndex), Ne i j -> Real
  value_eq_normalizedGeneratedPointPolynomial :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex)
      (hij : Ne i j),
        Not (IndexedCyclicConnectorPair hk i u j v) ->
          value i u j v hij =
            GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
              F.transitions.toFigure2TransitionObligations
              hk BaseTransitionRealization.exactBase (F.orientation k hk)
              i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
              j (CrossBlockLowerBoundsInterface.localVertexOfIndex v)
  value_ge_one :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex)
      (hij : Ne i j),
        Not (IndexedCyclicConnectorPair hk i u j v) ->
          1 <= value i u j v hij

namespace NormalizedIndexedGeneratedPointValueCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

def toNormalizedGeneratedPointPositionValueCertificate
    (C : NormalizedIndexedGeneratedPointValueCertificate F k hk) :
    NormalizedGeneratedPointPositionValueCertificate F k hk where
  value := fun p =>
    C.value p.left p.leftVertex p.right p.rightVertex
      (upperTrianglePosition_ne p)
  value_eq_normalizedGeneratedPointPolynomial := by
    intro p hp
    exact C.value_eq_normalizedGeneratedPointPolynomial
      p.left p.leftVertex p.right p.rightVertex
      (upperTrianglePosition_ne p) hp
  value_ge_one := by
    intro p hp
    exact C.value_ge_one
      p.left p.leftVertex p.right p.rightVertex
      (upperTrianglePosition_ne p) hp

def toNormalizedIndexedGeneratedPointPolynomialCertificate
    (C : NormalizedIndexedGeneratedPointValueCertificate F k hk) :
    NormalizedIndexedGeneratedPointPolynomialCertificate F k hk where
  polynomial_ge_one := by
    intro i u j v hij hnot_connector
    have hvalue :=
      C.value_eq_normalizedGeneratedPointPolynomial
        i u j v hij hnot_connector
    have hge := C.value_ge_one i u j v hij hnot_connector
    simpa [hvalue] using hge

def toGeneratedPointPositionValueCertificate
    (C : NormalizedIndexedGeneratedPointValueCertificate F k hk) :
    GeneratedPointPositionValueCertificate F k hk :=
  C.toNormalizedGeneratedPointPositionValueCertificate
    |>.toGeneratedPointPositionValueCertificate

def toNonConnectorValueMatrix
    (C : NormalizedIndexedGeneratedPointValueCertificate F k hk) :
    NonConnectorValueMatrix F k hk :=
  C.toGeneratedPointPositionValueCertificate.toNonConnectorValueMatrix

def toW9GeneratedPolynomialCertificate
    (C : NormalizedIndexedGeneratedPointValueCertificate F k hk) :
    W9GeneratedPolynomialCertificate F k hk :=
  C.toNormalizedIndexedGeneratedPointPolynomialCertificate
    |>.toW9GeneratedPolynomialCertificate

theorem indexedGeneratedPointPolynomial_ge_one
    (C : NormalizedIndexedGeneratedPointValueCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
        F hk i u j v :=
  C.toNormalizedIndexedGeneratedPointPolynomialCertificate
    |>.indexedGeneratedPointPolynomial_ge_one
      i u j v hij hnot_connector

theorem generatedGlobalSeparation
    (C : NormalizedIndexedGeneratedPointValueCertificate F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toGeneratedPointPositionValueCertificate
    |>.toGeneratedPointPositionPolynomialCertificate
    |>.generatedGlobalSeparation

end NormalizedIndexedGeneratedPointValueCertificate

/-! ## Family wrappers -/

structure NormalizedGeneratedPointPositionPolynomialCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k),
      NormalizedGeneratedPointPositionPolynomialCertificate F k hk

namespace NormalizedGeneratedPointPositionPolynomialCertificateFamily

variable {F : RoleHingedPeriodSearchFamily}

def toGeneratedPointPolynomialCertificateFamily
    (C : NormalizedGeneratedPointPositionPolynomialCertificateFamily F) :
    GeneratedPointPolynomialCertificateFamily F where
  certificate := fun k hk =>
    (C.certificate k hk).toGeneratedPointPositionPolynomialCertificate

def toW9GeneratedPolynomialCertificateFamily
    (C : NormalizedGeneratedPointPositionPolynomialCertificateFamily F) :
    W9GeneratedPolynomialCertificateFamily F where
  certificate := fun k hk =>
    (C.certificate k hk).toW9GeneratedPolynomialCertificate

def toGeneratedPointNonConnectorPolynomialTableFamily
    (C : NormalizedGeneratedPointPositionPolynomialCertificateFamily F) :
    GeneratedPointNonConnectorPolynomialTableFamily F :=
  C.toGeneratedPointPolynomialCertificateFamily
    |>.toGeneratedPointNonConnectorPolynomialTableFamily

def toNonConnectorSqDistanceTableFamily
    (C : NormalizedGeneratedPointPositionPolynomialCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  C.toGeneratedPointPolynomialCertificateFamily.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : NormalizedGeneratedPointPositionPolynomialCertificateFamily F) :
    CrossBlockLowerBounds F :=
  C.toGeneratedPointPolynomialCertificateFamily.toCrossBlockLowerBounds

theorem separated
    (C : NormalizedGeneratedPointPositionPolynomialCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toGeneratedPointPolynomialCertificateFamily.separated k hk

end NormalizedGeneratedPointPositionPolynomialCertificateFamily

structure NormalizedGeneratedPointPositionValueCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k),
      NormalizedGeneratedPointPositionValueCertificate F k hk

namespace NormalizedGeneratedPointPositionValueCertificateFamily

variable {F : RoleHingedPeriodSearchFamily}

def toGeneratedPointValueCertificateFamily
    (C : NormalizedGeneratedPointPositionValueCertificateFamily F) :
    GeneratedPointValueCertificateFamily F where
  certificate := fun k hk =>
    (C.certificate k hk).toGeneratedPointPositionValueCertificate

def toNormalizedGeneratedPointPositionPolynomialCertificateFamily
    (C : NormalizedGeneratedPointPositionValueCertificateFamily F) :
    NormalizedGeneratedPointPositionPolynomialCertificateFamily F where
  certificate := fun k hk =>
    (C.certificate k hk).toNormalizedGeneratedPointPositionPolynomialCertificate

def toNonConnectorValueMatrixFamily
    (C : NormalizedGeneratedPointPositionValueCertificateFamily F) :
    NonConnectorValueMatrixFamily F :=
  C.toGeneratedPointValueCertificateFamily.toNonConnectorValueMatrixFamily

def toW9GeneratedPolynomialCertificateFamily
    (C : NormalizedGeneratedPointPositionValueCertificateFamily F) :
    W9GeneratedPolynomialCertificateFamily F :=
  C.toNormalizedGeneratedPointPositionPolynomialCertificateFamily
    |>.toW9GeneratedPolynomialCertificateFamily

def toCrossBlockLowerBounds
    (C : NormalizedGeneratedPointPositionValueCertificateFamily F) :
    CrossBlockLowerBounds F :=
  C.toGeneratedPointValueCertificateFamily.toCrossBlockLowerBounds

theorem separated
    (C : NormalizedGeneratedPointPositionValueCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toGeneratedPointValueCertificateFamily
    |>.toGeneratedPointPolynomialCertificateFamily
    |>.separated k hk

end NormalizedGeneratedPointPositionValueCertificateFamily

end

end GeneratedPointNormalizationW10
end PachToth
end ErdosProblems1066
