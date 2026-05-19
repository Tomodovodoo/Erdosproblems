import ErdosProblems1066.Swanepoel.TopologyToBoundaryArcW14
import ErdosProblems1066.Swanepoel.BoundaryWalkFinitePartitions
import ErdosProblems1066.Swanepoel.Lemma8ExistenceConcrete

set_option autoImplicit false

/-!
# W15 boundary-arc extraction proof surface

This file does not assert the paper's boundary-arc extraction for free.  It
reduces the W14 `BoundaryArcExtractionTheorem` to exact finite boundary-walk
data over the selected planar boundary.

The finite data below is deliberately field-by-field: it names the two marked
endpoints, the fourteen boundary-cycle indices `p_0, ..., p_13`, the thirteen
common-neighbor labels `q_0, ..., q_12`, the cyclic successor checks along the
selected outer boundary walk, and the common-neighbor witnesses.  `BoundaryArcW12`
then verifies the deterministic bookkeeping from those fields to the finite
`p/q` spine certificate used downstream.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryArcExtractionProofW15

open BoundaryArcW12
open BoundarySpineFiniteCertificate
open ExactOuterBoundaryTopologyW13
open M8LabelsFromBoundaryInterface
open TopologyToBoundaryArcW14

universe u

noncomputable section

variable {n : Nat}

/-- The canonical graph used by the W14 extraction target. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  TopologyToBoundaryArcW14.CanonicalGraph C

/-! ## Exact finite boundary-walk data -/

/--
Exact checked finite data for the selected `m = 8` boundary arc.

The fields are intentionally the source data needed by `BoundaryArcW12`:
the selected boundary-walk indices and the triangle witnesses.  Boundary-edge
adjacency is not a field here; it is checked from `cyclicOrder` and the
selected planar boundary's outer-cycle adjacency theorem.
-/
structure BoundaryArcFiniteWalkData
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)) where
  leftEndpoint : Fin D.core.outerCycle.length
  rightEndpoint : Fin D.core.outerCycle.length
  pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length
  q : M8TriangleIndex -> Fin n
  leftEndpoint_eq_p0 :
    pIndex m8ArcFirstBoundaryIndex = leftEndpoint
  rightEndpoint_eq_p13 :
    pIndex m8ArcLastBoundaryIndex = rightEndpoint
  cyclicOrder :
    forall i : M8TriangleIndex,
      pIndex (m8BoundaryIndexRight i) =
        PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
          (pIndex (m8BoundaryIndexLeft i))
  triangleWitness :
    forall i : M8TriangleIndex,
      (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor
        (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
        (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i)

namespace BoundaryArcFiniteWalkData

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalGraph C)}

/-- The thirteen concrete cyclic-successor rows for a finite `p/q` spine.

These are the exact rows `p_{i+1} = succ(p_i)` for `i = 0, ..., 12`,
kept field-by-field so source certificates can prove the visible equalities
directly. -/
structure M8FinitePQSpineCyclicSuccessorRows
    (K : M8FinitePQSpineCertificate D) : Prop where
  cyclicOrder0 :
    K.pIndex (Subtype.mk 1 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 0 (by norm_num)))
  cyclicOrder1 :
    K.pIndex (Subtype.mk 2 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 1 (by norm_num)))
  cyclicOrder2 :
    K.pIndex (Subtype.mk 3 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 2 (by norm_num)))
  cyclicOrder3 :
    K.pIndex (Subtype.mk 4 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 3 (by norm_num)))
  cyclicOrder4 :
    K.pIndex (Subtype.mk 5 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 4 (by norm_num)))
  cyclicOrder5 :
    K.pIndex (Subtype.mk 6 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 5 (by norm_num)))
  cyclicOrder6 :
    K.pIndex (Subtype.mk 7 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 6 (by norm_num)))
  cyclicOrder7 :
    K.pIndex (Subtype.mk 8 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 7 (by norm_num)))
  cyclicOrder8 :
    K.pIndex (Subtype.mk 9 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 8 (by norm_num)))
  cyclicOrder9 :
    K.pIndex (Subtype.mk 10 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 9 (by norm_num)))
  cyclicOrder10 :
    K.pIndex (Subtype.mk 11 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 10 (by norm_num)))
  cyclicOrder11 :
    K.pIndex (Subtype.mk 12 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 11 (by norm_num)))
  cyclicOrder12 :
    K.pIndex (Subtype.mk 13 (by norm_num)) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (Subtype.mk 12 (by norm_num)))

namespace M8FinitePQSpineCyclicSuccessorRows

variable {K : M8FinitePQSpineCertificate D}

def ofCyclicOrder
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i))) :
    M8FinitePQSpineCyclicSuccessorRows K where
  cyclicOrder0 := by
    exact cyclicOrder (Subtype.mk 0 (by norm_num))
  cyclicOrder1 := by
    exact cyclicOrder (Subtype.mk 1 (by norm_num))
  cyclicOrder2 := by
    exact cyclicOrder (Subtype.mk 2 (by norm_num))
  cyclicOrder3 := by
    exact cyclicOrder (Subtype.mk 3 (by norm_num))
  cyclicOrder4 := by
    exact cyclicOrder (Subtype.mk 4 (by norm_num))
  cyclicOrder5 := by
    exact cyclicOrder (Subtype.mk 5 (by norm_num))
  cyclicOrder6 := by
    exact cyclicOrder (Subtype.mk 6 (by norm_num))
  cyclicOrder7 := by
    exact cyclicOrder (Subtype.mk 7 (by norm_num))
  cyclicOrder8 := by
    exact cyclicOrder (Subtype.mk 8 (by norm_num))
  cyclicOrder9 := by
    exact cyclicOrder (Subtype.mk 9 (by norm_num))
  cyclicOrder10 := by
    exact cyclicOrder (Subtype.mk 10 (by norm_num))
  cyclicOrder11 := by
    exact cyclicOrder (Subtype.mk 11 (by norm_num))
  cyclicOrder12 := by
    exact cyclicOrder (Subtype.mk 12 (by norm_num))

theorem cyclicOrder
    (R : M8FinitePQSpineCyclicSuccessorRows K)
    (i : M8TriangleIndex) :
    K.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (m8BoundaryIndexLeft i)) := by
  cases i with
  | mk i hi =>
      interval_cases i <;>
        first
        | exact R.cyclicOrder0
        | exact R.cyclicOrder1
        | exact R.cyclicOrder2
        | exact R.cyclicOrder3
        | exact R.cyclicOrder4
        | exact R.cyclicOrder5
        | exact R.cyclicOrder6
        | exact R.cyclicOrder7
        | exact R.cyclicOrder8
        | exact R.cyclicOrder9
        | exact R.cyclicOrder10
        | exact R.cyclicOrder11
        | exact R.cyclicOrder12

end M8FinitePQSpineCyclicSuccessorRows

/-- The boundary vertex named by the finite boundary-walk data. -/
def p (W : BoundaryArcFiniteWalkData D)
    (i : M8BoundaryIndex) : Fin n :=
  D.core.outerCycle.vertex (W.pIndex i)

@[simp]
theorem p_eq_outerCycle
    (W : BoundaryArcFiniteWalkData D) (i : M8BoundaryIndex) :
    W.p i = D.core.outerCycle.vertex (W.pIndex i) :=
  rfl

/-- Package the exact finite walk data as the W12 boundary-arc certificate. -/
def toBoundaryArcCertificate
    (W : BoundaryArcFiniteWalkData D) :
    M8BoundaryArcCertificate D where
  leftEndpoint := W.leftEndpoint
  rightEndpoint := W.rightEndpoint
  pIndex := W.pIndex
  q := W.q
  leftEndpoint_eq_p0 := W.leftEndpoint_eq_p0
  rightEndpoint_eq_p13 := W.rightEndpoint_eq_p13
  cyclicOrder := W.cyclicOrder
  triangleWitness := W.triangleWitness

@[simp]
theorem toBoundaryArcCertificate_leftEndpoint
    (W : BoundaryArcFiniteWalkData D) :
    W.toBoundaryArcCertificate.leftEndpoint = W.leftEndpoint :=
  rfl

@[simp]
theorem toBoundaryArcCertificate_rightEndpoint
    (W : BoundaryArcFiniteWalkData D) :
    W.toBoundaryArcCertificate.rightEndpoint = W.rightEndpoint :=
  rfl

@[simp]
theorem toBoundaryArcCertificate_pIndex
    (W : BoundaryArcFiniteWalkData D) (i : M8BoundaryIndex) :
    W.toBoundaryArcCertificate.pIndex i = W.pIndex i :=
  rfl

@[simp]
theorem toBoundaryArcCertificate_p
    (W : BoundaryArcFiniteWalkData D) (i : M8BoundaryIndex) :
    W.toBoundaryArcCertificate.p i = W.p i :=
  rfl

@[simp]
theorem toBoundaryArcCertificate_q
    (W : BoundaryArcFiniteWalkData D) (i : M8TriangleIndex) :
    W.toBoundaryArcCertificate.q i = W.q i :=
  rfl

/-- The W12 certificate forgets to the finite `p/q` spine certificate. -/
def toFinitePQSpineCertificate
    (W : BoundaryArcFiniteWalkData D) :
    M8FinitePQSpineCertificate D :=
  W.toBoundaryArcCertificate.toFinitePQSpineCertificate

@[simp]
theorem toFinitePQSpineCertificate_pIndex
    (W : BoundaryArcFiniteWalkData D) (i : M8BoundaryIndex) :
    W.toFinitePQSpineCertificate.pIndex i = W.pIndex i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_p
    (W : BoundaryArcFiniteWalkData D) (i : M8BoundaryIndex) :
    W.toFinitePQSpineCertificate.p i = W.p i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_q
    (W : BoundaryArcFiniteWalkData D) (i : M8TriangleIndex) :
    W.toFinitePQSpineCertificate.q i = W.q i :=
  rfl

theorem toFinitePQSpineCertificate_cyclicOrder
    (W : BoundaryArcFiniteWalkData D) (i : M8TriangleIndex) :
    W.toFinitePQSpineCertificate.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (W.toFinitePQSpineCertificate.pIndex (m8BoundaryIndexLeft i)) :=
  W.cyclicOrder i

def cyclicSuccessorRowsOfBoundaryArcCertificate
    (A : M8BoundaryArcCertificate D) :
    M8FinitePQSpineCyclicSuccessorRows A.toFinitePQSpineCertificate :=
  M8FinitePQSpineCyclicSuccessorRows.ofCyclicOrder
    A.toFinitePQSpineCertificate_cyclicOrder

def cyclicSuccessorRowsOfFiniteWalkData
    (W : BoundaryArcFiniteWalkData D) :
    M8FinitePQSpineCyclicSuccessorRows W.toFinitePQSpineCertificate :=
  M8FinitePQSpineCyclicSuccessorRows.ofCyclicOrder
    W.toFinitePQSpineCertificate_cyclicOrder

theorem toFinitePQSpineCertificate_triangleWitness
    (W : BoundaryArcFiniteWalkData D) (i : M8TriangleIndex) :
    (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor
      (W.toFinitePQSpineCertificate.p (m8BoundaryIndexLeft i))
      (W.toFinitePQSpineCertificate.p (m8BoundaryIndexRight i))
      (W.toFinitePQSpineCertificate.q i) := by
  exact W.toBoundaryArcCertificate.toFinitePQSpineCertificate_triangleWitness i

/-- The exact finite walk data supplies the W14 extraction field. -/
def toBoundaryArcExtractionFields
    (W : BoundaryArcFiniteWalkData D) :
    BoundaryArcExtractionFields D where
  boundaryArc := W.toBoundaryArcCertificate

@[simp]
theorem toBoundaryArcExtractionFields_boundaryArc
    (W : BoundaryArcFiniteWalkData D) :
    W.toBoundaryArcExtractionFields.boundaryArc =
      W.toBoundaryArcCertificate :=
  rfl

@[simp]
theorem toBoundaryArcExtractionFields_spineCertificate
    (W : BoundaryArcFiniteWalkData D) :
    W.toBoundaryArcExtractionFields.toFinitePQSpineCertificate =
      W.toFinitePQSpineCertificate :=
  rfl

/-! ## Constructors from existing boundary-arc and finite-spine rows -/

/-- A W12 boundary-arc certificate is exactly the finite-walk data expected by
W15. -/
def ofBoundaryArcCertificate
    (A : M8BoundaryArcCertificate D) :
    BoundaryArcFiniteWalkData D where
  leftEndpoint := A.leftEndpoint
  rightEndpoint := A.rightEndpoint
  pIndex := A.pIndex
  q := A.q
  leftEndpoint_eq_p0 := A.leftEndpoint_eq_p0
  rightEndpoint_eq_p13 := A.rightEndpoint_eq_p13
  cyclicOrder := A.cyclicOrder
  triangleWitness := A.triangleWitness

@[simp]
theorem ofBoundaryArcCertificate_toBoundaryArcCertificate
    (A : M8BoundaryArcCertificate D) :
    (ofBoundaryArcCertificate A).toBoundaryArcCertificate = A :=
  rfl

@[simp]
theorem ofBoundaryArcCertificate_pIndex
    (A : M8BoundaryArcCertificate D) (i : M8BoundaryIndex) :
    (ofBoundaryArcCertificate A).pIndex i = A.pIndex i :=
  rfl

@[simp]
theorem ofBoundaryArcCertificate_q
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    (ofBoundaryArcCertificate A).q i = A.q i :=
  rfl

@[simp]
theorem ofBoundaryArcCertificate_toFinitePQSpineCertificate
    (A : M8BoundaryArcCertificate D) :
    (ofBoundaryArcCertificate A).toFinitePQSpineCertificate =
      A.toFinitePQSpineCertificate :=
  rfl

/-- W14 extraction fields contain exactly the boundary-arc certificate needed
for W15 finite checked boundary-walk data. -/
def ofBoundaryArcExtractionFields
    (A : BoundaryArcExtractionFields D) :
    BoundaryArcFiniteWalkData D :=
  ofBoundaryArcCertificate A.boundaryArc

@[simp]
theorem ofBoundaryArcExtractionFields_toBoundaryArcCertificate
    (A : BoundaryArcExtractionFields D) :
    (ofBoundaryArcExtractionFields A).toBoundaryArcCertificate =
      A.boundaryArc :=
  rfl

@[simp]
theorem ofBoundaryArcExtractionFields_toBoundaryArcExtractionFields
    (A : BoundaryArcExtractionFields D) :
    (ofBoundaryArcExtractionFields A).toBoundaryArcExtractionFields =
      A := by
  cases A
  rfl

@[simp]
theorem ofBoundaryArcExtractionFields_toFinitePQSpineCertificate
    (A : BoundaryArcExtractionFields D) :
    (ofBoundaryArcExtractionFields A).toFinitePQSpineCertificate =
      A.toFinitePQSpineCertificate :=
  rfl

/--
Promote an existing finite `p/q` spine certificate to W15 finite-walk data once
the same-boundary arc endpoints and cyclic-successor run are supplied.

This isolates the exact remaining fields when the available source is already a
finite spine: the endpoint markers and the thirteen cyclic-order equalities.
-/
def ofFinitePQSpineCertificate
    (K : M8FinitePQSpineCertificate D)
    (leftEndpoint rightEndpoint : Fin D.core.outerCycle.length)
    (leftEndpoint_eq_p0 :
      K.pIndex m8ArcFirstBoundaryIndex = leftEndpoint)
    (rightEndpoint_eq_p13 :
      K.pIndex m8ArcLastBoundaryIndex = rightEndpoint)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i))) :
    BoundaryArcFiniteWalkData D where
  leftEndpoint := leftEndpoint
  rightEndpoint := rightEndpoint
  pIndex := K.pIndex
  q := K.q
  leftEndpoint_eq_p0 := leftEndpoint_eq_p0
  rightEndpoint_eq_p13 := rightEndpoint_eq_p13
  cyclicOrder := cyclicOrder
  triangleWitness := by
    intro i
    have h := K.triangleWitness i
    rw [K.p_eq_outerCycle (m8BoundaryIndexLeft i),
      K.p_eq_outerCycle (m8BoundaryIndexRight i)] at h
    exact h

/-- Promote a finite `p/q` spine certificate using the thirteen concrete
cyclic-successor rows. -/
def ofFinitePQSpineCertificateRows
    (K : M8FinitePQSpineCertificate D)
    (leftEndpoint rightEndpoint : Fin D.core.outerCycle.length)
    (leftEndpoint_eq_p0 :
      K.pIndex m8ArcFirstBoundaryIndex = leftEndpoint)
    (rightEndpoint_eq_p13 :
      K.pIndex m8ArcLastBoundaryIndex = rightEndpoint)
    (cyclicRows : M8FinitePQSpineCyclicSuccessorRows K) :
    BoundaryArcFiniteWalkData D :=
  ofFinitePQSpineCertificate K leftEndpoint rightEndpoint
    leftEndpoint_eq_p0 rightEndpoint_eq_p13 cyclicRows.cyclicOrder

@[simp]
theorem ofFinitePQSpineCertificate_pIndex
    (K : M8FinitePQSpineCertificate D)
    (leftEndpoint rightEndpoint : Fin D.core.outerCycle.length)
    (leftEndpoint_eq_p0 :
      K.pIndex m8ArcFirstBoundaryIndex = leftEndpoint)
    (rightEndpoint_eq_p13 :
      K.pIndex m8ArcLastBoundaryIndex = rightEndpoint)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (i : M8BoundaryIndex) :
    (ofFinitePQSpineCertificate K leftEndpoint rightEndpoint
      leftEndpoint_eq_p0 rightEndpoint_eq_p13 cyclicOrder).pIndex i =
        K.pIndex i :=
  rfl

@[simp]
theorem ofFinitePQSpineCertificate_q
    (K : M8FinitePQSpineCertificate D)
    (leftEndpoint rightEndpoint : Fin D.core.outerCycle.length)
    (leftEndpoint_eq_p0 :
      K.pIndex m8ArcFirstBoundaryIndex = leftEndpoint)
    (rightEndpoint_eq_p13 :
      K.pIndex m8ArcLastBoundaryIndex = rightEndpoint)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (i : M8TriangleIndex) :
    (ofFinitePQSpineCertificate K leftEndpoint rightEndpoint
      leftEndpoint_eq_p0 rightEndpoint_eq_p13 cyclicOrder).q i =
        K.q i :=
  rfl

@[simp]
theorem ofFinitePQSpineCertificateRows_pIndex
    (K : M8FinitePQSpineCertificate D)
    (leftEndpoint rightEndpoint : Fin D.core.outerCycle.length)
    (leftEndpoint_eq_p0 :
      K.pIndex m8ArcFirstBoundaryIndex = leftEndpoint)
    (rightEndpoint_eq_p13 :
      K.pIndex m8ArcLastBoundaryIndex = rightEndpoint)
    (cyclicRows : M8FinitePQSpineCyclicSuccessorRows K)
    (i : M8BoundaryIndex) :
    (ofFinitePQSpineCertificateRows K leftEndpoint rightEndpoint
      leftEndpoint_eq_p0 rightEndpoint_eq_p13 cyclicRows).pIndex i =
        K.pIndex i :=
  rfl

@[simp]
theorem ofFinitePQSpineCertificateRows_q
    (K : M8FinitePQSpineCertificate D)
    (leftEndpoint rightEndpoint : Fin D.core.outerCycle.length)
    (leftEndpoint_eq_p0 :
      K.pIndex m8ArcFirstBoundaryIndex = leftEndpoint)
    (rightEndpoint_eq_p13 :
      K.pIndex m8ArcLastBoundaryIndex = rightEndpoint)
    (cyclicRows : M8FinitePQSpineCyclicSuccessorRows K)
    (i : M8TriangleIndex) :
    (ofFinitePQSpineCertificateRows K leftEndpoint rightEndpoint
      leftEndpoint_eq_p0 rightEndpoint_eq_p13 cyclicRows).q i =
        K.q i :=
  rfl

end BoundaryArcFiniteWalkData

/-! ## Finite boundary-walk data with frame-core facts -/

/--
Finite boundary-walk data together with the actual frame-core facts for the
generated `p/q` spine.

The `finiteWalk` field still owns the honest boundary spine.  The
`frameCoreFields` field adds only the five finite facts per Lemma 8 index
needed to produce the four-forbidden frame core downstream.
-/
structure BoundaryArcFiniteWalkFrameCoreData
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  finiteWalk : BoundaryArcFiniteWalkData D
  frameCoreFields :
    M8FinitePQSpineFrameCoreFields
      finiteWalk.toFinitePQSpineCertificate connectedNoCut hmin

namespace BoundaryArcFiniteWalkFrameCoreData

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalGraph C)}
variable {connectedNoCut :
  CutVertexClosure.PreconnectedNoCutVertexCertificate C}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def ofRawFiniteWalkFacts
    (finiteWalk : BoundaryArcFiniteWalkData D)
    (prev_adj :
      forall i : M8ExtraIndex,
        (GraphBridge.unitDistanceLocalGraph C).Adj
          (finiteWalk.q (m8TriangleIndexOfExtra i))
          (finiteWalk.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (GraphBridge.unitDistanceLocalGraph C).Adj
          (finiteWalk.q (m8TriangleIndexOfExtra i))
          (finiteWalk.q (m8TriangleIndexNextOfExtra i)))
    (left_ne_next :
      forall i : M8ExtraIndex,
        Not
          (finiteWalk.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
            finiteWalk.q (m8TriangleIndexNextOfExtra i)))
    (right_ne_prev :
      forall i : M8ExtraIndex,
        Not
          (finiteWalk.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
            finiteWalk.q (m8TriangleIndexPrevOfExtra i)))
    (prev_ne_next :
      forall i : M8ExtraIndex,
        Not
          (finiteWalk.q (m8TriangleIndexPrevOfExtra i) =
            finiteWalk.q (m8TriangleIndexNextOfExtra i))) :
    BoundaryArcFiniteWalkFrameCoreData (D := D) connectedNoCut hmin where
  finiteWalk := finiteWalk
  frameCoreFields := by
    refine
      M8FinitePQSpineFrameCoreFields.ofRawFinitePQFacts
        (K := finiteWalk.toFinitePQSpineCertificate)
        (connectedNoCut := connectedNoCut) (hmin := hmin)
        ?_ ?_ ?_ ?_ ?_
    · intro i
      simpa using prev_adj i
    · intro i
      simpa using next_adj i
    · intro i
      exact left_ne_next i
    · intro i
      exact right_ne_prev i
    · intro i
      simpa using prev_ne_next i

/-- Add frame-core facts to the finite walk extracted from a W12 boundary-arc
certificate.  The generated finite `p/q` certificate is definitionally the
certificate already attached to the boundary arc. -/
def ofBoundaryArcCertificateAndFrameCoreFields
    (boundaryArc : M8BoundaryArcCertificate D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        boundaryArc.toFinitePQSpineCertificate connectedNoCut hmin) :
    BoundaryArcFiniteWalkFrameCoreData (D := D) connectedNoCut hmin where
  finiteWalk :=
    BoundaryArcFiniteWalkData.ofBoundaryArcCertificate boundaryArc
  frameCoreFields := by
    simpa using frameCoreFields

@[simp]
theorem ofBoundaryArcCertificateAndFrameCoreFields_finiteWalk
    (boundaryArc : M8BoundaryArcCertificate D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        boundaryArc.toFinitePQSpineCertificate connectedNoCut hmin) :
    (ofBoundaryArcCertificateAndFrameCoreFields
      (D := D) (connectedNoCut := connectedNoCut) (hmin := hmin)
      boundaryArc frameCoreFields).finiteWalk =
        BoundaryArcFiniteWalkData.ofBoundaryArcCertificate boundaryArc :=
  rfl

@[simp]
theorem ofBoundaryArcCertificateAndFrameCoreFields_boundaryArc
    (boundaryArc : M8BoundaryArcCertificate D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        boundaryArc.toFinitePQSpineCertificate connectedNoCut hmin) :
    ((ofBoundaryArcCertificateAndFrameCoreFields
      (D := D) (connectedNoCut := connectedNoCut) (hmin := hmin)
      boundaryArc frameCoreFields).finiteWalk.toBoundaryArcCertificate) =
        boundaryArc :=
  rfl

theorem frameCoreFields_iff_rawFiniteWalkFacts
    (finiteWalk : BoundaryArcFiniteWalkData D) :
    M8FinitePQSpineFrameCoreFields
        finiteWalk.toFinitePQSpineCertificate connectedNoCut hmin <->
      (forall i : M8ExtraIndex,
        (GraphBridge.unitDistanceLocalGraph C).Adj
          (finiteWalk.q (m8TriangleIndexOfExtra i))
          (finiteWalk.q (m8TriangleIndexPrevOfExtra i))) /\
      (forall i : M8ExtraIndex,
        (GraphBridge.unitDistanceLocalGraph C).Adj
          (finiteWalk.q (m8TriangleIndexOfExtra i))
          (finiteWalk.q (m8TriangleIndexNextOfExtra i))) /\
      (forall i : M8ExtraIndex,
        Not
          (finiteWalk.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
            finiteWalk.q (m8TriangleIndexNextOfExtra i))) /\
      (forall i : M8ExtraIndex,
        Not
          (finiteWalk.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
            finiteWalk.q (m8TriangleIndexPrevOfExtra i))) /\
      (forall i : M8ExtraIndex,
        Not
          (finiteWalk.q (m8TriangleIndexPrevOfExtra i) =
            finiteWalk.q (m8TriangleIndexNextOfExtra i))) := by
  exact
    M8FinitePQSpineFrameCoreFields.fields_iff_rawFinitePQFacts
      (K := finiteWalk.toFinitePQSpineCertificate)
      (connectedNoCut := connectedNoCut) (hmin := hmin)

variable
  (W : BoundaryArcFiniteWalkFrameCoreData
    (D := D) connectedNoCut hmin)

def toFiniteWalkData :
    BoundaryArcFiniteWalkData D :=
  W.finiteWalk

def toFinitePQSpineCertificate :
    M8FinitePQSpineCertificate D :=
  W.finiteWalk.toFinitePQSpineCertificate

def toBoundaryArcExtractionFields :
    BoundaryArcExtractionFields D :=
  W.finiteWalk.toBoundaryArcExtractionFields

@[simp]
theorem toFinitePQSpineCertificate_eq :
    W.toFinitePQSpineCertificate =
      W.finiteWalk.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem toBoundaryArcExtractionFields_eq :
    W.toBoundaryArcExtractionFields =
      W.finiteWalk.toBoundaryArcExtractionFields :=
  rfl

theorem frameCoreFields_holds :
    M8FinitePQSpineFrameCoreFields
      W.toFinitePQSpineCertificate connectedNoCut hmin := by
  simpa [toFinitePQSpineCertificate] using W.frameCoreFields

end BoundaryArcFiniteWalkFrameCoreData

/-! ## Reduction of W14 extraction to finite checked data -/

/--
Pointwise finite checked boundary-walk target over a fixed
topology/angle/subpolygon/long-arc row.
-/
def BoundaryArcFiniteWalkTarget
    {C : _root_.UDConfig n}
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C))
    (_longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) : Prop :=
  Nonempty
    (BoundaryArcFiniteWalkData
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))

/-- Pointwise finite checked boundary-walk plus frame-core target over a
fixed topology/angle/subpolygon/long-arc row and no-cut certificate. -/
def BoundaryArcFiniteWalkFrameCoreTarget
    {C : _root_.UDConfig n}
    (connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C))
    (_longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) : Prop :=
  Nonempty
    (BoundaryArcFiniteWalkFrameCoreData
      (D := T.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)
      connectedNoCut hmin)

theorem finiteWalkTarget_of_frameCoreTarget
    {C : _root_.UDConfig n}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (h :
      BoundaryArcFiniteWalkFrameCoreTarget
        connectedNoCut hmin T outerAngleBounds Subpolygon subpolygonData
        longArc) :
    BoundaryArcFiniteWalkTarget
      T outerAngleBounds Subpolygon subpolygonData longArc := by
  cases h with
  | intro W =>
      exact Nonempty.intro W.toFiniteWalkData

/-- An existing boundary-arc certificate over the same planar boundary closes
the W15 finite-walk target. -/
theorem finiteWalkTarget_of_boundaryArcCertificate
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (boundaryArc :
      M8BoundaryArcCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    BoundaryArcFiniteWalkTarget
      T outerAngleBounds Subpolygon subpolygonData longArc :=
  Nonempty.intro
    (BoundaryArcFiniteWalkData.ofBoundaryArcCertificate boundaryArc)

/-- Existing W14 extraction fields over the same planar boundary close the W15
finite-walk target. -/
theorem finiteWalkTarget_of_boundaryArcExtractionFields
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (arcExtraction :
      BoundaryArcExtractionFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    BoundaryArcFiniteWalkTarget
      T outerAngleBounds Subpolygon subpolygonData longArc :=
  Nonempty.intro
    (BoundaryArcFiniteWalkData.ofBoundaryArcExtractionFields arcExtraction)

/-- A pointwise W14 extraction target is already finite checked W15
boundary-walk data. -/
theorem finiteWalkTarget_of_extractionTarget
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (h :
      BoundaryArcExtractionTarget
        T outerAngleBounds Subpolygon subpolygonData longArc) :
    BoundaryArcFiniteWalkTarget
      T outerAngleBounds Subpolygon subpolygonData longArc := by
  cases h with
  | intro arcExtraction =>
      exact finiteWalkTarget_of_boundaryArcExtractionFields arcExtraction

/--
An existing finite `p/q` spine certificate closes the W15 finite-walk target
once the same-boundary endpoint markers and cyclic-successor rows are supplied.
-/
theorem finiteWalkTarget_of_finitePQSpineCertificate
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (K :
      M8FinitePQSpineCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (leftEndpoint rightEndpoint :
      Fin ((T.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData).core.outerCycle.length))
    (leftEndpoint_eq_p0 :
      K.pIndex m8ArcFirstBoundaryIndex = leftEndpoint)
    (rightEndpoint_eq_p13 :
      K.pIndex m8ArcLastBoundaryIndex = rightEndpoint)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc
            ((T.toPlanarBoundaryData outerAngleBounds Subpolygon
                subpolygonData).core.outerCycle.length_pos)
            (K.pIndex (m8BoundaryIndexLeft i))) :
    BoundaryArcFiniteWalkTarget
      T outerAngleBounds Subpolygon subpolygonData longArc :=
  Nonempty.intro
    (BoundaryArcFiniteWalkData.ofFinitePQSpineCertificate
      K leftEndpoint rightEndpoint leftEndpoint_eq_p0 rightEndpoint_eq_p13
      cyclicOrder)

/-- A finite `p/q` spine plus the thirteen concrete cyclic-successor rows
closes the W15 finite-walk target. -/
theorem finiteWalkTarget_of_finitePQSpineCertificateRows
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (K :
      M8FinitePQSpineCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (leftEndpoint rightEndpoint :
      Fin ((T.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData).core.outerCycle.length))
    (leftEndpoint_eq_p0 :
      K.pIndex m8ArcFirstBoundaryIndex = leftEndpoint)
    (rightEndpoint_eq_p13 :
      K.pIndex m8ArcLastBoundaryIndex = rightEndpoint)
    (cyclicRows :
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K) :
    BoundaryArcFiniteWalkTarget
      T outerAngleBounds Subpolygon subpolygonData longArc :=
  Nonempty.intro
    (BoundaryArcFiniteWalkData.ofFinitePQSpineCertificateRows
      K leftEndpoint rightEndpoint leftEndpoint_eq_p0 rightEndpoint_eq_p13
      cyclicRows)

/--
Uniform finite-walk theorem shape sufficient for W14
`BoundaryArcExtractionTheorem`.
-/
def BoundaryArcFiniteWalkTheorem : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalGraph C))
    (longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)),
      BoundaryArcFiniteWalkTarget
        T outerAngleBounds Subpolygon subpolygonData longArc

/-- Pointwise finite checked boundary-walk data gives the W14 extraction target. -/
theorem extractionTarget_of_finiteWalkTarget
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (h :
      BoundaryArcFiniteWalkTarget
        T outerAngleBounds Subpolygon subpolygonData longArc) :
    BoundaryArcExtractionTarget
      T outerAngleBounds Subpolygon subpolygonData longArc := by
  rcases h with ⟨W⟩
  exact Nonempty.intro W.toBoundaryArcExtractionFields

/--
A uniform finite checked boundary-walk theorem is enough to discharge the W14
boundary-arc extraction theorem shape.
-/
theorem boundaryArcExtractionTheorem_of_finiteWalkTheorem
    (H : BoundaryArcFiniteWalkTheorem.{u}) :
    BoundaryArcExtractionTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  exact
    extractionTarget_of_finiteWalkTarget
      (H C T outerAngleBounds Subpolygon subpolygonData longArc)

/-- A uniform W14 extraction theorem supplies the W15 finite boundary-walk
theorem by forgetting each extraction field to its finite walk data. -/
theorem finiteWalkTheorem_of_boundaryArcExtractionTheorem
    (H : BoundaryArcExtractionTheorem.{u}) :
    BoundaryArcFiniteWalkTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  exact
    finiteWalkTarget_of_extractionTarget
      (H C T outerAngleBounds Subpolygon subpolygonData longArc)

/--
Build the full W14 conditional row directly from finite checked boundary-walk
data.
-/
theorem topologyBoundaryArcFields_of_finiteWalkTarget
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (h :
      BoundaryArcFiniteWalkTarget
        T outerAngleBounds Subpolygon subpolygonData longArc) :
    Nonempty (TopologyBoundaryArcFields.{u} C) :=
  topologyBoundaryArcFields_of_extractionTarget
    (extractionTarget_of_finiteWalkTarget h)

end

end BoundaryArcExtractionProofW15
end Swanepoel
end ErdosProblems1066
