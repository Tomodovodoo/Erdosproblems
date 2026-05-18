import ErdosProblems1066.Swanepoel.BoundaryLabelInstantiationW10
import ErdosProblems1066.Swanepoel.BoundaryLabelCertificateAssembly
import ErdosProblems1066.Swanepoel.BoundaryLabelExtractionTasks
import ErdosProblems1066.Swanepoel.OuterBoundaryLabelFacts
import ErdosProblems1066.Swanepoel.MinimalFailureDirectMatrixW10

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 boundary-label row packages

This module packages the boundary-label inputs used by the W10
minimal-failure direct matrix.  It keeps the raw finite `p/q` labels, the
explicit Lemma 8 `r/s` row, and the remaining Lemma 8 existence payload
visible, then proves the checked projections into the W10 label and base rows.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelRowsW11

open BoundaryLabelCertificateAssembly
open BoundarySpineFiniteCertificate
open CutVertexFinal
open GraphBridge
open Lemma8ExistenceConcrete
open M8BoundaryLabelsConcrete
open M8LabelsFromBoundaryInterface
open MinimalFailureDirectMatrixW10
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-- The cut/no-cut package derived from minimality and the explicit no-cut
slack field. -/
def cutVertexFactsOfSlack
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackFact C) :
    MinimalFailureComponentPackage.MinimalFailureCutVertexFacts C hmin where
  positiveCard :=
    MinimalFailureW8RowAssembly.positiveCard_of_minimalClearedFailure hmin
  remainingSlack := remainingNoCutSlack

/-- The no-cut certificate used by the boundary-label row. -/
def connectedNoCutOfSlack
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackFact C) :
    CutVertexClosure.PreconnectedNoCutVertexCertificate C :=
  (cutVertexFactsOfSlack hmin remainingNoCutSlack).preconnectedNoCut

/-! ## Raw finite `p/q` labels -/

/-- Raw finite `p/q` label data over the planar boundary chosen by the W10
topology/partition/angle row. -/
structure ExplicitPQLabelData
    (C : _root_.UDConfig n)
    (topology : TopologyComponentFields C)
    (partitionAngle : PartitionAngleComponentFields.{u} C topology) where
  pIndex :
    M8BoundaryIndex ->
      Fin partitionAngle.planarBoundary.core.outerCycle.length
  p : M8BoundaryIndex -> Fin n
  q : M8TriangleIndex -> Fin n
  p_eq_outerCycle :
    forall i : M8BoundaryIndex,
      p i = partitionAngle.planarBoundary.core.outerCycle.vertex (pIndex i)
  boundaryEdge :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).Adj
        (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i))
  triangleWitness :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).CommonNeighbor
        (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)) (q i)

namespace ExplicitPQLabelData

variable {C : _root_.UDConfig n}
variable {topology : TopologyComponentFields C}
variable {partitionAngle : PartitionAngleComponentFields.{u} C topology}

/-- Forget raw `p/q` fields to the existing finite spine certificate. -/
def toFinitePQSpineCertificate
    (P : ExplicitPQLabelData.{u} C topology partitionAngle) :
    M8FinitePQSpineCertificate partitionAngle.planarBoundary where
  pIndex := P.pIndex
  p := P.p
  q := P.q
  p_eq_outerCycle := P.p_eq_outerCycle
  boundaryEdge := P.boundaryEdge
  triangleWitness := P.triangleWitness

@[simp]
theorem toFinitePQSpineCertificate_pIndex
    (P : ExplicitPQLabelData.{u} C topology partitionAngle)
    (i : M8BoundaryIndex) :
    P.toFinitePQSpineCertificate.pIndex i = P.pIndex i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_p
    (P : ExplicitPQLabelData.{u} C topology partitionAngle)
    (i : M8BoundaryIndex) :
    P.toFinitePQSpineCertificate.p i = P.p i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_q
    (P : ExplicitPQLabelData.{u} C topology partitionAngle)
    (i : M8TriangleIndex) :
    P.toFinitePQSpineCertificate.q i = P.q i :=
  rfl

theorem toFinitePQSpineCertificate_boundaryEdge
    (P : ExplicitPQLabelData.{u} C topology partitionAngle)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (P.toFinitePQSpineCertificate.p (m8BoundaryIndexLeft i))
      (P.toFinitePQSpineCertificate.p (m8BoundaryIndexRight i)) :=
  P.boundaryEdge i

theorem toFinitePQSpineCertificate_triangleWitness
    (P : ExplicitPQLabelData.{u} C topology partitionAngle)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (P.toFinitePQSpineCertificate.p (m8BoundaryIndexLeft i))
      (P.toFinitePQSpineCertificate.p (m8BoundaryIndexRight i))
      (P.toFinitePQSpineCertificate.q i) :=
  P.triangleWitness i

end ExplicitPQLabelData

/-! ## Explicit boundary labels and Lemma 8 data -/

/-- Explicit finite boundary labels together with an explicit Lemma 8 row.

The later W10 row consumes the finite `p/q` certificate and a
`M8Lemma8MissingExistenceConditions` value.  This record keeps the visible
`M8Lemma8Combinatorics` row as the source label data; the W10 bridge below
adds the remaining existence payload and an agreement proof. -/
structure ExplicitBoundaryLabelData
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (topology : TopologyComponentFields C)
    (partitionAngle : PartitionAngleComponentFields.{u} C topology) where
  remainingNoCutSlack : RemainingNoCutSlackFact C
  pq : ExplicitPQLabelData.{u} C topology partitionAngle
  lemma8 :
    M8Lemma8Combinatorics
      (pq.toFinitePQSpineCertificate.toM8BoundarySpine
        (connectedNoCutOfSlack hmin remainingNoCutSlack) hmin)

namespace ExplicitBoundaryLabelData

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {topology : TopologyComponentFields C}
variable {partitionAngle : PartitionAngleComponentFields.{u} C topology}

/-- The no-cut certificate selected by the no-cut slack field. -/
def connectedNoCut
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle) :
    CutVertexClosure.PreconnectedNoCutVertexCertificate C :=
  connectedNoCutOfSlack hmin D.remainingNoCutSlack

/-- The finite `p/q` spine certificate selected by the raw labels. -/
def spineCertificate
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle) :
    M8FinitePQSpineCertificate partitionAngle.planarBoundary :=
  D.pq.toFinitePQSpineCertificate

/-- The boundary spine obtained from the explicit finite labels. -/
def spine
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle) :
    M8BoundarySpine
      (D.spineCertificate.context D.connectedNoCut hmin) :=
  D.spineCertificate.toM8BoundarySpine D.connectedNoCut hmin

/-- The finite certificate view used by the W10 boundary-label assembly. -/
def toFiniteBoundaryLabelCertificate
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle) :
    M8FiniteBoundaryLabelCertificate
      partitionAngle.planarBoundary D.connectedNoCut hmin where
  finiteLabels := D.spineCertificate
  lemma8 := D.lemma8

/-- The concrete boundary-label package obtained from the explicit labels. -/
def toBoundaryLabelPackage
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle) :
    M8BoundaryLabelPackage C :=
  D.toFiniteBoundaryLabelCertificate.toBoundaryLabelPackage

/-- The local labels obtained from the explicit labels. -/
def localLabels
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle) :
    M8ConstructionInterface.M8LocalLabels C :=
  D.toFiniteBoundaryLabelCertificate.toM8LocalLabels

@[simp]
theorem spineCertificate_p
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle)
    (i : M8BoundaryIndex) :
    D.spineCertificate.p i = D.pq.p i :=
  rfl

@[simp]
theorem spineCertificate_q
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle)
    (i : M8TriangleIndex) :
    D.spineCertificate.q i = D.pq.q i :=
  rfl

@[simp]
theorem localLabels_p
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle)
    (i : M8BoundaryIndex) :
    D.localLabels.labels.p i = D.pq.p i :=
  rfl

@[simp]
theorem localLabels_q
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle)
    (i : M8TriangleIndex) :
    D.localLabels.labels.q i = D.pq.q i :=
  rfl

@[simp]
theorem localLabels_r
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle)
    (i : M8ExtraIndex) :
    D.localLabels.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem localLabels_s
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle)
    (i : M8ExtraIndex) :
    D.localLabels.labels.s i = D.lemma8.s i :=
  rfl

theorem boundaryEdge
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle)
    (i : M8TriangleIndex) :
    D.localLabels.predicates.data.boundaryEdge i :=
  BoundaryLabelCertificateAssembly.M8FiniteBoundaryLabelCertificate.boundaryEdge
    D.toFiniteBoundaryLabelCertificate i

theorem triangleWitness
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle)
    (i : M8TriangleIndex) :
    D.localLabels.predicates.data.triangleWitness i :=
  BoundaryLabelCertificateAssembly.M8FiniteBoundaryLabelCertificate.triangleWitness
    D.toFiniteBoundaryLabelCertificate i

theorem extraNeighborWitness
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle)
    (i : M8ExtraIndex) :
    D.localLabels.predicates.data.extraNeighborWitness i :=
  BoundaryLabelCertificateAssembly.M8FiniteBoundaryLabelCertificate.extraNeighborWitness
    D.toFiniteBoundaryLabelCertificate i

theorem p_onOuterBoundary
    (D : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle)
    (i : M8BoundaryIndex) :
    D.toBoundaryLabelPackage.context.outerBoundary.outerEnclosure.onBoundary
      (D.localLabels.labels.p i) := by
  simpa using
    OuterBoundaryLabelFacts.M8BoundaryLabelPackage.p_onOuterBoundary
      D.toBoundaryLabelPackage i

end ExplicitBoundaryLabelData

/-! ## W10 label-row packages -/

/-- W11 boundary-label package feeding the W10 minimal-failure direct matrix.

The `lemma8Existence` field is the exact remaining Lemma 8 payload consumed by
the W10 row.  The agreement field states that the generated Lemma 8 row is the
same explicit `r/s` row carried by `explicit`. -/
structure BoundaryLabelRowPackage
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (topology : TopologyComponentFields C)
    (partitionAngle : PartitionAngleComponentFields.{u} C topology) where
  explicit : ExplicitBoundaryLabelData.{u} C hmin topology partitionAngle
  lemma8Existence : M8Lemma8MissingExistenceConditions explicit.spine
  lemma8Agreement :
    lemma8Existence.toLemma8Combinatorics = explicit.lemma8

namespace BoundaryLabelRowPackage

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {topology : TopologyComponentFields C}
variable {partitionAngle : PartitionAngleComponentFields.{u} C topology}

/-- The W10 label component obtained from the explicit W11 label package. -/
def toW10LabelComponentFields
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    LabelComponentFields.{u} C hmin topology partitionAngle where
  remainingNoCutSlack := R.explicit.remainingNoCutSlack
  spineCertificate := R.explicit.spineCertificate
  lemma8Existence := R.lemma8Existence

/-- The W9 boundary-label row underlying the W10 label component. -/
def toW9BoundaryLabelRow
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
      C hmin partitionAngle.toTopologyAngleSubpolygonRow :=
  R.toW10LabelComponentFields.toBoundaryLabelRow

/-- The W9 base row assembled from the W10 topology, partition/angle, and W11
label package. -/
def toW10BaseRow
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin :=
  baseRowOfComponents topology partitionAngle R.toW10LabelComponentFields

@[simp]
theorem toW10LabelComponentFields_remainingNoCutSlack
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    R.toW10LabelComponentFields.remainingNoCutSlack =
      R.explicit.remainingNoCutSlack :=
  rfl

@[simp]
theorem toW10LabelComponentFields_spineCertificate
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    R.toW10LabelComponentFields.spineCertificate =
      R.explicit.spineCertificate :=
  rfl

@[simp]
theorem toW10LabelComponentFields_lemma8Existence
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    R.toW10LabelComponentFields.lemma8Existence =
      R.lemma8Existence :=
  rfl

@[simp]
theorem toW9BoundaryLabelRow_remainingNoCutSlack
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    R.toW9BoundaryLabelRow.remainingNoCutSlack =
      R.explicit.remainingNoCutSlack :=
  rfl

@[simp]
theorem toW9BoundaryLabelRow_spineCertificate
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    R.toW9BoundaryLabelRow.spineCertificate =
      R.explicit.spineCertificate :=
  rfl

@[simp]
theorem toW9BoundaryLabelRow_lemma8Existence
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    R.toW9BoundaryLabelRow.lemma8Existence =
      R.lemma8Existence :=
  rfl

@[simp]
theorem toW10BaseRow_topology
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    R.toW10BaseRow.topology =
      partitionAngle.toTopologyAngleSubpolygonRow :=
  rfl

@[simp]
theorem toW10BaseRow_boundaryLabels
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle) :
    R.toW10BaseRow.boundaryLabels = R.toW9BoundaryLabelRow :=
  rfl

@[simp]
theorem toW10BaseRow_localLabels_p
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle)
    (i : M8BoundaryIndex) :
    R.toW10BaseRow.localLabels.labels.p i = R.explicit.pq.p i :=
  rfl

@[simp]
theorem toW10BaseRow_localLabels_q
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle)
    (i : M8TriangleIndex) :
    R.toW10BaseRow.localLabels.labels.q i = R.explicit.pq.q i :=
  rfl

@[simp]
theorem toW10BaseRow_localLabels_r
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle)
    (i : M8ExtraIndex) :
    R.toW10BaseRow.localLabels.labels.r i = R.explicit.lemma8.r i := by
  have h :=
    congrArg
      (fun E : M8Lemma8Combinatorics R.explicit.spine => E.r i)
      R.lemma8Agreement
  simpa [toW10BaseRow, toW9BoundaryLabelRow, toW10LabelComponentFields,
    ExplicitBoundaryLabelData.spine, ExplicitBoundaryLabelData.spineCertificate,
    ExplicitBoundaryLabelData.connectedNoCut, connectedNoCutOfSlack,
    cutVertexFactsOfSlack] using h

@[simp]
theorem toW10BaseRow_localLabels_s
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle)
    (i : M8ExtraIndex) :
    R.toW10BaseRow.localLabels.labels.s i = R.explicit.lemma8.s i := by
  have h :=
    congrArg
      (fun E : M8Lemma8Combinatorics R.explicit.spine => E.s i)
      R.lemma8Agreement
  simpa [toW10BaseRow, toW9BoundaryLabelRow, toW10LabelComponentFields,
    ExplicitBoundaryLabelData.spine, ExplicitBoundaryLabelData.spineCertificate,
    ExplicitBoundaryLabelData.connectedNoCut, connectedNoCutOfSlack,
    cutVertexFactsOfSlack] using h

theorem toW10BaseRow_boundaryEdge
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle)
    (i : M8TriangleIndex) :
    R.toW10BaseRow.localLabels.predicates.data.boundaryEdge i := by
  simpa [toW10BaseRow, toW9BoundaryLabelRow, toW10LabelComponentFields] using
    R.explicit.pq.boundaryEdge i

theorem toW10BaseRow_triangleWitness
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle)
    (i : M8TriangleIndex) :
    R.toW10BaseRow.localLabels.predicates.data.triangleWitness i := by
  simpa [toW10BaseRow, toW9BoundaryLabelRow, toW10LabelComponentFields] using
    R.explicit.pq.triangleWitness i

theorem toW10BaseRow_extraNeighborWitness
    (R : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle)
    (i : M8ExtraIndex) :
    R.toW10BaseRow.localLabels.predicates.data.extraNeighborWitness i := by
  have h :
      R.lemma8Existence.toLemma8Combinatorics.extraNeighborWitness i := by
    rw [R.lemma8Agreement]
    exact R.explicit.lemma8.extraNeighborWitness_holds i
  simpa [toW10BaseRow, toW9BoundaryLabelRow, toW10LabelComponentFields,
    ExplicitBoundaryLabelData.spine, ExplicitBoundaryLabelData.spineCertificate,
    ExplicitBoundaryLabelData.connectedNoCut, connectedNoCutOfSlack,
    cutVertexFactsOfSlack] using h

/-- Boundary-label base packages are the prefix needed before the W10 direct
matrix asks for containment and no-early rows. -/
structure BasePrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  topology : TopologyComponentFields C
  partitionAngle : PartitionAngleComponentFields.{u} C topology
  labels : BoundaryLabelRowPackage.{u} C hmin topology partitionAngle

namespace BasePrefix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Project a W11 boundary-label prefix to the W10 base row consumed by later
direct-matrix fields. -/
def toW10BaseRow
    (B : BasePrefix.{u} C hmin) :
    SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin :=
  B.labels.toW10BaseRow

/-- Project a W11 boundary-label prefix to the W10 label component. -/
def toW10LabelComponentFields
    (B : BasePrefix.{u} C hmin) :
    LabelComponentFields.{u} C hmin B.topology B.partitionAngle :=
  B.labels.toW10LabelComponentFields

@[simp]
theorem toW10BaseRow_eq
    (B : BasePrefix.{u} C hmin) :
    B.toW10BaseRow = B.labels.toW10BaseRow :=
  rfl

@[simp]
theorem toW10LabelComponentFields_eq
    (B : BasePrefix.{u} C hmin) :
    B.toW10LabelComponentFields =
      B.labels.toW10LabelComponentFields :=
  rfl

end BasePrefix

end BoundaryLabelRowPackage

end

end BoundaryLabelRowsW11
end Swanepoel
end ErdosProblems1066
