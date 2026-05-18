import ErdosProblems1066.Swanepoel.BoundarySpineConcrete

set_option autoImplicit false

/-!
# Finite-label certificates for the `m = 8` boundary spine

`BoundarySpineConcrete` lets a caller choose the `p_i` labels as vertices of
the selected outer boundary cycle.  This file adds a slightly more convenient
certificate layer for later finite work: the caller names the finite labels
`p_i` and `q_i` directly, and separately proves that each `p_i` is the selected
outer-cycle vertex at an explicit finite index.

No paper existence theorem is proved here.  The adjacency and common-neighbor
facts remain explicit fields.  The checked content is just the deterministic
bookkeeping from those finite labels to `M8BoundarySpine` and
`M8BoundaryRouteData`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundarySpineFiniteCertificate

open BoundaryFaceCountingToM8
open BoundarySpineConcrete
open CutVertexClosure
open GraphBridge
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-! ## Explicit finite `p/q` certificates -/

/--
Finite labels for the `m = 8` boundary spine over a selected planar boundary.

The `pIndex` field records where each explicitly named `p_i` is found on the
selected outer cycle.  The `p` and `q` fields are the labels intended to appear
in the downstream `M8BoundarySpine`.
-/
structure M8FinitePQSpineCertificate
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C)) where
  pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length
  p : M8BoundaryIndex -> Fin n
  q : M8TriangleIndex -> Fin n
  p_eq_outerCycle :
    forall i : M8BoundaryIndex,
      p i = D.core.outerCycle.vertex (pIndex i)
  boundaryEdge :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).Adj
        (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i))
  triangleWitness :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).CommonNeighbor
        (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)) (q i)

namespace M8FinitePQSpineCertificate

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}
variable {connectedNoCut : PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/-- Constructor with the proof fields kept as explicit arguments. -/
def ofLabels
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (p : M8BoundaryIndex -> Fin n)
    (q : M8TriangleIndex -> Fin n)
    (p_eq_outerCycle :
      forall i : M8BoundaryIndex,
        p i = D.core.outerCycle.vertex (pIndex i))
    (boundaryEdge :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).Adj
          (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)) (q i)) :
    M8FinitePQSpineCertificate D where
  pIndex := pIndex
  p := p
  q := q
  p_eq_outerCycle := p_eq_outerCycle
  boundaryEdge := boundaryEdge
  triangleWitness := triangleWitness

@[simp]
theorem ofLabels_pIndex
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (p : M8BoundaryIndex -> Fin n)
    (q : M8TriangleIndex -> Fin n)
    (p_eq_outerCycle :
      forall i : M8BoundaryIndex,
        p i = D.core.outerCycle.vertex (pIndex i))
    (boundaryEdge :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).Adj
          (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)) (q i))
    (i : M8BoundaryIndex) :
    (ofLabels (D := D) pIndex p q
      p_eq_outerCycle boundaryEdge triangleWitness).pIndex i =
        pIndex i :=
  rfl

@[simp]
theorem ofLabels_p
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (p : M8BoundaryIndex -> Fin n)
    (q : M8TriangleIndex -> Fin n)
    (p_eq_outerCycle :
      forall i : M8BoundaryIndex,
        p i = D.core.outerCycle.vertex (pIndex i))
    (boundaryEdge :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).Adj
          (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)) (q i))
    (i : M8BoundaryIndex) :
    (ofLabels (D := D) pIndex p q
      p_eq_outerCycle boundaryEdge triangleWitness).p i =
        p i :=
  rfl

@[simp]
theorem ofLabels_q
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (p : M8BoundaryIndex -> Fin n)
    (q : M8TriangleIndex -> Fin n)
    (p_eq_outerCycle :
      forall i : M8BoundaryIndex,
        p i = D.core.outerCycle.vertex (pIndex i))
    (boundaryEdge :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).Adj
          (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)) (q i))
    (i : M8TriangleIndex) :
    (ofLabels (D := D) pIndex p q
      p_eq_outerCycle boundaryEdge triangleWitness).q i =
        q i :=
  rfl

/-- The structural context attached to the selected planar boundary. -/
def context
    (_K : M8FinitePQSpineCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    M8BoundaryCutDegreeContext C :=
  boundaryCutDegreeContextOfPlanarBoundary D connectedNoCut hmin

@[simp]
theorem context_eq
    (K : M8FinitePQSpineCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    K.context connectedNoCut hmin =
      boundaryCutDegreeContextOfPlanarBoundary D connectedNoCut hmin :=
  rfl

/--
Forget the explicit `p` labels to the outer-cycle-index skeleton used by
`BoundarySpineConcrete`.
-/
def toSkeleton
    (K : M8FinitePQSpineCertificate D) :
    M8PlanarBoundarySpineSkeleton D :=
  (K.pIndex, K.q)

@[simp]
theorem toSkeleton_pIndex
    (K : M8FinitePQSpineCertificate D)
    (i : M8BoundaryIndex) :
    K.toSkeleton.pIndex i = K.pIndex i :=
  rfl

@[simp]
theorem toSkeleton_q
    (K : M8FinitePQSpineCertificate D)
    (i : M8TriangleIndex) :
    K.toSkeleton.q i = K.q i :=
  rfl

@[simp]
theorem toSkeleton_p
    (K : M8FinitePQSpineCertificate D)
    (i : M8BoundaryIndex) :
    K.toSkeleton.p i = K.p i := by
  simpa [toSkeleton, M8PlanarBoundarySpineSkeleton.p] using
    (K.p_eq_outerCycle i).symm

/-- The explicit finite labels supply a valid concrete skeleton. -/
def toSkeletonValid
    (K : M8FinitePQSpineCertificate D) :
    M8PlanarBoundarySpineSkeleton.Valid connectedNoCut hmin K.toSkeleton where
  boundaryEdge := by
    intro i
    simpa using K.boundaryEdge i
  triangleWitness := by
    intro i
    simpa using K.triangleWitness i

/-- The explicitly named `p_i` lies on the selected outer boundary. -/
theorem p_onBoundary
    (K : M8FinitePQSpineCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (i : M8BoundaryIndex) :
    (K.context connectedNoCut hmin).outerBoundary.outerEnclosure.onBoundary
      (K.p i) := by
  change D.core.outerEnclosure.onBoundary (K.p i)
  rw [K.p_eq_outerCycle i]
  simpa [OuterBoundaryCore.outerCycle] using
    D.core.boundary_vertex_onBoundary (K.pIndex i)

/-- Convert explicit finite `p/q` labels into the boundary spine interface. -/
def toM8BoundarySpine
    (K : M8FinitePQSpineCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    M8BoundarySpine (K.context connectedNoCut hmin) where
  p := K.p
  q := K.q
  p_onBoundary := K.p_onBoundary connectedNoCut hmin
  boundaryEdge := K.boundaryEdge
  triangleWitness := K.triangleWitness

@[simp]
theorem toM8BoundarySpine_p
    (K : M8FinitePQSpineCertificate D)
    (i : M8BoundaryIndex) :
    (K.toM8BoundarySpine connectedNoCut hmin).p i = K.p i :=
  rfl

@[simp]
theorem toM8BoundarySpine_q
    (K : M8FinitePQSpineCertificate D)
    (i : M8TriangleIndex) :
    (K.toM8BoundarySpine connectedNoCut hmin).q i = K.q i :=
  rfl

theorem toM8BoundarySpine_boundaryEdge
    (K : M8FinitePQSpineCertificate D)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      ((K.toM8BoundarySpine connectedNoCut hmin).p (m8BoundaryIndexLeft i))
      ((K.toM8BoundarySpine connectedNoCut hmin).p
        (m8BoundaryIndexRight i)) :=
  K.boundaryEdge i

theorem toM8BoundarySpine_triangleWitness
    (K : M8FinitePQSpineCertificate D)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      ((K.toM8BoundarySpine connectedNoCut hmin).p (m8BoundaryIndexLeft i))
      ((K.toM8BoundarySpine connectedNoCut hmin).p
        (m8BoundaryIndexRight i))
      ((K.toM8BoundarySpine connectedNoCut hmin).q i) :=
  K.triangleWitness i

/-- A finite certificate is enough to produce a nonempty boundary spine. -/
theorem nonempty_spine_of_exists_certificate
    (h : Nonempty (M8FinitePQSpineCertificate D)) :
    Nonempty (M8BoundarySpine
      (boundaryCutDegreeContextOfPlanarBoundary D connectedNoCut hmin)) := by
  rcases h with ⟨K⟩
  exact Nonempty.intro (K.toM8BoundarySpine connectedNoCut hmin)

/--
Promote the finite `p/q` certificate to the planar M8 boundary route once the
still-explicit Lemma 8 package is supplied for the resulting spine.
-/
def toM8BoundaryRouteData
    (K : M8FinitePQSpineCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    M8BoundaryRouteData.{u} C hmin where
  planarBoundary := D
  connectedNoCut := connectedNoCut
  spine := K.toM8BoundarySpine connectedNoCut hmin
  lemma8 := lemma8

@[simp]
theorem toM8BoundaryRouteData_context
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    (K.toM8BoundaryRouteData connectedNoCut hmin lemma8).context =
      K.context connectedNoCut hmin :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_planarBoundary
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    (K.toM8BoundaryRouteData connectedNoCut hmin lemma8).planarBoundary =
      D :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_connectedNoCut
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    (K.toM8BoundaryRouteData connectedNoCut hmin lemma8).connectedNoCut =
      connectedNoCut :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_spine
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    (K.toM8BoundaryRouteData connectedNoCut hmin lemma8).spine =
      K.toM8BoundarySpine connectedNoCut hmin :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_lemma8
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    (K.toM8BoundaryRouteData connectedNoCut hmin lemma8).lemma8 =
      lemma8 :=
  rfl

theorem toM8BoundaryRouteData_boundaryEdge
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toM8BoundaryRouteData
      connectedNoCut hmin lemma8).toBoundaryLabelPackage.predicates.data.boundaryEdge
        i :=
  K.boundaryEdge i

theorem toM8BoundaryRouteData_triangleWitness
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toM8BoundaryRouteData
      connectedNoCut hmin lemma8).toBoundaryLabelPackage.predicates.data.triangleWitness
        i :=
  K.triangleWitness i

theorem toM8BoundaryRouteData_extraNeighborWitness
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    (K.toM8BoundaryRouteData
      connectedNoCut hmin lemma8).toBoundaryLabelPackage.predicates.data.extraNeighborWitness
        i :=
  lemma8.extraNeighborWitness_holds i

@[simp]
theorem toM8BoundaryRouteData_labels_p
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8BoundaryIndex) :
    (((K.toM8BoundaryRouteData connectedNoCut hmin lemma8).toM8LocalLabels).labels).p
      i =
      K.p i :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_labels_q
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (((K.toM8BoundaryRouteData connectedNoCut hmin lemma8).toM8LocalLabels).labels).q
      i =
      K.q i :=
  rfl

/-- Forget the finite certificate route to the concrete M8 boundary-label
package. -/
def toBoundaryLabelPackage
    (K : M8FinitePQSpineCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    M8BoundaryLabelPackage C :=
  (K.toM8BoundaryRouteData connectedNoCut hmin lemma8).toBoundaryLabelPackage

@[simp]
theorem toBoundaryLabelPackage_context
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).context =
      K.context connectedNoCut hmin :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_spine
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).spine =
      K.toM8BoundarySpine connectedNoCut hmin :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_lemma8
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).lemma8 =
      lemma8 :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_p
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8BoundaryIndex) :
    (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).labels.p i =
      K.p i :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_q
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).labels.q i =
      K.q i :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_r
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).labels.r i =
      lemma8.r i :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_s
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).labels.s i =
      lemma8.s i :=
  rfl

theorem toBoundaryLabelPackage_boundaryEdge
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toBoundaryLabelPackage
      connectedNoCut hmin lemma8).predicates.data.boundaryEdge i :=
  K.boundaryEdge i

theorem toBoundaryLabelPackage_triangleWitness
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toBoundaryLabelPackage
      connectedNoCut hmin lemma8).predicates.data.triangleWitness i :=
  K.triangleWitness i

theorem toBoundaryLabelPackage_extraNeighborWitness
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    (K.toBoundaryLabelPackage
      connectedNoCut hmin lemma8).predicates.data.extraNeighborWitness i :=
  lemma8.extraNeighborWitness_holds i

theorem toBoundaryLabelPackage_named_of_extra_neighbor
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    {i : M8ExtraIndex} {x : Fin n}
    (hadj :
      (unitDistanceLocalGraph C).Adj
        ((K.toM8BoundarySpine connectedNoCut hmin).centerQ i) x)
    (hnot :
      Not
        ((K.toM8BoundarySpine
          connectedNoCut hmin).forbiddenExtraNeighbor i x)) :
    x = lemma8.r i \/ x = lemma8.s i :=
  lemma8.named_of_extra_neighbor hadj hnot

theorem toBoundaryLabelPackage_positiveCyclicOrder
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    lemma8.positiveCyclicOrderAt i
      (lemma8.s i) (lemma8.r i)
      ((K.toM8BoundarySpine connectedNoCut hmin).prevQ i)
      ((K.toM8BoundarySpine connectedNoCut hmin).leftP i)
      ((K.toM8BoundarySpine connectedNoCut hmin).rightP i)
      ((K.toM8BoundarySpine connectedNoCut hmin).nextQ i) :=
  lemma8.positiveCyclicOrder_holds i

/-- The local-label field determined by finite boundary labels and the
explicit Lemma 8 package. -/
def toM8LocalLabels
    (K : M8FinitePQSpineCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    M8LocalLabels C :=
  (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).toM8LocalLabels

@[simp]
theorem toM8LocalLabels_eq
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    K.toM8LocalLabels connectedNoCut hmin lemma8 =
      (K.toM8BoundaryRouteData connectedNoCut hmin lemma8).toM8LocalLabels :=
  rfl

@[simp]
theorem toM8LocalLabels_labels
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    (K.toM8LocalLabels connectedNoCut hmin lemma8).labels =
      (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).labels :=
  rfl

@[simp]
theorem toM8LocalLabels_labels_p
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8BoundaryIndex) :
    (K.toM8LocalLabels connectedNoCut hmin lemma8).labels.p i =
      K.p i :=
  rfl

@[simp]
theorem toM8LocalLabels_labels_q
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toM8LocalLabels connectedNoCut hmin lemma8).labels.q i =
      K.q i :=
  rfl

@[simp]
theorem toM8LocalLabels_labels_r
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    (K.toM8LocalLabels connectedNoCut hmin lemma8).labels.r i =
      lemma8.r i :=
  rfl

@[simp]
theorem toM8LocalLabels_labels_s
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    (K.toM8LocalLabels connectedNoCut hmin lemma8).labels.s i =
      lemma8.s i :=
  rfl

theorem toM8LocalLabels_boundaryEdge
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toM8LocalLabels
      connectedNoCut hmin lemma8).predicates.data.boundaryEdge i :=
  K.boundaryEdge i

theorem toM8LocalLabels_triangleWitness
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toM8LocalLabels
      connectedNoCut hmin lemma8).predicates.data.triangleWitness i :=
  K.triangleWitness i

theorem toM8LocalLabels_extraNeighborWitness
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    (K.toM8LocalLabels
      connectedNoCut hmin lemma8).predicates.data.extraNeighborWitness i :=
  lemma8.extraNeighborWitness_holds i

/-- The route preserves the selected planar-boundary face-counting context. -/
theorem route_faceCounting_outerBoundary
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin)) :
    ((K.toM8BoundaryRouteData connectedNoCut hmin lemma8).faceCounting).context_outerBoundary_eq =
      rfl :=
  rfl

end M8FinitePQSpineCertificate

end

end BoundarySpineFiniteCertificate
end Swanepoel
end ErdosProblems1066
