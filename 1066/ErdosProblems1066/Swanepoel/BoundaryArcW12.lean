import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate

set_option autoImplicit false

/-!
# Boundary arc bookkeeping for the `m = 8` label spine

This module records the source-shaped boundary arc data used before the
finite `p/q` spine certificate.  The caller still supplies the selected arc
indices and triangle witnesses.  The checked content here is the deterministic
bookkeeping:

* the fourteen `p_i` labels form a cyclic successor run on the selected outer
  boundary cycle;
* the first and last arc endpoint markers are tied to `p_0` and `p_13`; and
* this data forgets to `M8FinitePQSpineCertificate`, with boundary edges
  derived from the recorded cyclic order.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryArcW12

open BoundaryFaceCountingToM8
open BoundarySpineConcrete
open BoundarySpineFiniteCertificate
open CutVertexClosure
open GraphBridge
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-! ## Fixed `m = 8` endpoint indices -/

/-- The first boundary label on the selected `m = 8` arc, namely `p_0`. -/
def m8ArcFirstBoundaryIndex : M8BoundaryIndex :=
  Subtype.mk 0 (by norm_num)

/-- The last boundary label on the selected `m = 8` arc, namely `p_13`. -/
def m8ArcLastBoundaryIndex : M8BoundaryIndex :=
  Subtype.mk 13 (by norm_num)

@[simp]
theorem m8ArcFirstBoundaryIndex_val :
    m8ArcFirstBoundaryIndex.1 = 0 :=
  rfl

@[simp]
theorem m8ArcLastBoundaryIndex_val :
    m8ArcLastBoundaryIndex.1 = 13 :=
  rfl

/-! ## Boundary arc certificate -/

/--
Boundary-cycle arc data for the `m = 8` labels.

The `pIndex` fields name the fourteen boundary vertices.  The `cyclicOrder`
field says that every consecutive pair `p_i, p_{i+1}` is one cyclic successor
step on the selected outer cycle, so the boundary-edge adjacency needed by
`M8FinitePQSpineCertificate` is checked from the planar-boundary package.
-/
structure M8BoundaryArcCertificate
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C)) where
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
      (unitDistanceLocalGraph C).CommonNeighbor
        (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
        (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i)

namespace M8BoundaryArcCertificate

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}

/-- The boundary vertex label determined by the arc index `p_i`. -/
def p (A : M8BoundaryArcCertificate D)
    (i : M8BoundaryIndex) : Fin n :=
  D.core.outerCycle.vertex (A.pIndex i)

/-- The boundary-cycle edge marker supporting the triangle indexed by `i`. -/
def edgeIndex (A : M8BoundaryArcCertificate D)
    (i : M8TriangleIndex) :
    Fin D.core.outerCycle.length :=
  A.pIndex (m8BoundaryIndexLeft i)

/-- The first marked endpoint vertex of the arc. -/
def leftEndpointVertex (A : M8BoundaryArcCertificate D) : Fin n :=
  D.core.outerCycle.vertex A.leftEndpoint

/-- The last marked endpoint vertex of the arc. -/
def rightEndpointVertex (A : M8BoundaryArcCertificate D) : Fin n :=
  D.core.outerCycle.vertex A.rightEndpoint

@[simp]
theorem p_eq_outerCycle
    (A : M8BoundaryArcCertificate D) (i : M8BoundaryIndex) :
    A.p i = D.core.outerCycle.vertex (A.pIndex i) :=
  rfl

@[simp]
theorem edgeIndex_eq_left
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    A.edgeIndex i = A.pIndex (m8BoundaryIndexLeft i) :=
  rfl

@[simp]
theorem pIndex_first
    (A : M8BoundaryArcCertificate D) :
    A.pIndex m8ArcFirstBoundaryIndex = A.leftEndpoint :=
  A.leftEndpoint_eq_p0

@[simp]
theorem pIndex_last
    (A : M8BoundaryArcCertificate D) :
    A.pIndex m8ArcLastBoundaryIndex = A.rightEndpoint :=
  A.rightEndpoint_eq_p13

@[simp]
theorem leftEndpointVertex_eq_p_first
    (A : M8BoundaryArcCertificate D) :
    A.leftEndpointVertex = A.p m8ArcFirstBoundaryIndex := by
  simp [leftEndpointVertex, p]

@[simp]
theorem rightEndpointVertex_eq_p_last
    (A : M8BoundaryArcCertificate D) :
    A.rightEndpointVertex = A.p m8ArcLastBoundaryIndex := by
  simp [rightEndpointVertex, p]

theorem cyclicOrder_holds
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    A.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (A.edgeIndex i) := by
  simpa [edgeIndex] using A.cyclicOrder i

theorem right_p_eq_outerCycle_successor
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    A.p (m8BoundaryIndexRight i) =
      D.core.outerCycle.vertex
        (PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
          (A.edgeIndex i)) := by
  simp [p, A.cyclicOrder_holds i]

/-- Boundary-edge adjacency follows from the cyclic order on the outer cycle. -/
theorem boundaryEdge
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (A.p (m8BoundaryIndexLeft i)) (A.p (m8BoundaryIndexRight i)) := by
  have h :=
    D.core.outerCycle_adjacent_unitDistanceAdj
      (A.pIndex (m8BoundaryIndexLeft i))
  simpa [p, GraphBridge.unitDistanceLocalGraph, CanonicalUDGraph,
    A.cyclicOrder i] using h

theorem triangleWitness_holds
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (A.p (m8BoundaryIndexLeft i)) (A.p (m8BoundaryIndexRight i)) (A.q i) :=
  A.triangleWitness i

/-! ## Projection to the finite `p/q` spine certificate -/

/-- Forget the boundary-arc metadata to the existing finite `p/q` certificate. -/
def toFinitePQSpineCertificate
    (A : M8BoundaryArcCertificate D) :
    M8FinitePQSpineCertificate D where
  pIndex := A.pIndex
  p := A.p
  q := A.q
  p_eq_outerCycle := A.p_eq_outerCycle
  boundaryEdge := A.boundaryEdge
  triangleWitness := A.triangleWitness_holds

@[simp]
theorem toFinitePQSpineCertificate_pIndex
    (A : M8BoundaryArcCertificate D) (i : M8BoundaryIndex) :
    A.toFinitePQSpineCertificate.pIndex i = A.pIndex i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_p
    (A : M8BoundaryArcCertificate D) (i : M8BoundaryIndex) :
    A.toFinitePQSpineCertificate.p i = A.p i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_q
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    A.toFinitePQSpineCertificate.q i = A.q i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_leftEndpoint
    (A : M8BoundaryArcCertificate D) :
    A.toFinitePQSpineCertificate.pIndex m8ArcFirstBoundaryIndex =
      A.leftEndpoint :=
  A.leftEndpoint_eq_p0

@[simp]
theorem toFinitePQSpineCertificate_rightEndpoint
    (A : M8BoundaryArcCertificate D) :
    A.toFinitePQSpineCertificate.pIndex m8ArcLastBoundaryIndex =
      A.rightEndpoint :=
  A.rightEndpoint_eq_p13

theorem toFinitePQSpineCertificate_cyclicOrder
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    A.toFinitePQSpineCertificate.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (A.toFinitePQSpineCertificate.pIndex (m8BoundaryIndexLeft i)) :=
  A.cyclicOrder i

theorem toFinitePQSpineCertificate_boundaryEdge
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (A.toFinitePQSpineCertificate.p (m8BoundaryIndexLeft i))
      (A.toFinitePQSpineCertificate.p (m8BoundaryIndexRight i)) :=
  A.boundaryEdge i

theorem toFinitePQSpineCertificate_triangleWitness
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (A.toFinitePQSpineCertificate.p (m8BoundaryIndexLeft i))
      (A.toFinitePQSpineCertificate.p (m8BoundaryIndexRight i))
      (A.toFinitePQSpineCertificate.q i) :=
  A.triangleWitness_holds i

/-! ## Projection to the older planar-boundary skeleton -/

/-- The boundary-arc data also forgets to the planar-boundary spine skeleton. -/
def toSkeleton
    (A : M8BoundaryArcCertificate D) :
    M8PlanarBoundarySpineSkeleton D :=
  A.toFinitePQSpineCertificate.toSkeleton

@[simp]
theorem toSkeleton_pIndex
    (A : M8BoundaryArcCertificate D) (i : M8BoundaryIndex) :
    A.toSkeleton.pIndex i = A.pIndex i :=
  rfl

@[simp]
theorem toSkeleton_p
    (A : M8BoundaryArcCertificate D) (i : M8BoundaryIndex) :
    A.toSkeleton.p i = A.p i :=
  rfl

@[simp]
theorem toSkeleton_q
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    A.toSkeleton.q i = A.q i :=
  rfl

theorem toSkeleton_cyclicOrder
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    A.toSkeleton.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (A.toSkeleton.pIndex (m8BoundaryIndexLeft i)) :=
  A.cyclicOrder i

/-- The arc certificate supplies the skeleton validity facts. -/
def toSkeletonValid
    (A : M8BoundaryArcCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    M8PlanarBoundarySpineSkeleton.Valid
      connectedNoCut hmin A.toSkeleton where
  boundaryEdge := by
    intro i
    simpa using A.boundaryEdge i
  triangleWitness := by
    intro i
    simpa using A.triangleWitness_holds i

end M8BoundaryArcCertificate

end

end BoundaryArcW12
end Swanepoel
end ErdosProblems1066
