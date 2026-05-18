import ErdosProblems1066.Swanepoel.M8LabelsFromBoundaryInterface
import ErdosProblems1066.Swanepoel.BoundaryFaceCountingToM8
import ErdosProblems1066.Swanepoel.BoundaryLabelExtractionTasks

set_option autoImplicit false

/-!
# Concrete boundary spine reducers for `m = 8`

This file advances the boundary-spine side of the `m = 8` route from the
planar boundary/no-cut/degree context.

The selected planar outer boundary deterministically supplies the boundary
membership facts for the `p_i` labels once the finite boundary-cycle indices
are named.  The actual index choices and the common-neighbor labels remain
explicit.  The checked content here is the finite reduction from those choices
to `M8BoundarySpine`, plus projections through the existing boundary-label
and face-counting packages.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundarySpineConcrete

open BoundaryFaceCountingToM8
open BoundaryLabelExtractionTasks
open CutVertexClosure
open GraphBridge
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-! ## Finite planar-boundary skeleton -/

/--
A finite choice skeleton for the `m = 8` boundary spine over a selected
planar-boundary package.

The first component chooses the fourteen boundary labels as indices in the
selected outer boundary cycle.  The second component chooses the thirteen
common-neighbor labels `q_i`.
-/
abbrev M8PlanarBoundarySpineSkeleton
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C)) : Type :=
  Prod (M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (M8TriangleIndex -> Fin n)

namespace M8PlanarBoundarySpineSkeleton

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}

/-- The chosen outer-boundary cycle index for `p_i`. -/
def pIndex (X : M8PlanarBoundarySpineSkeleton D)
    (i : M8BoundaryIndex) :
    Fin D.core.outerCycle.length :=
  X.1 i

/-- The boundary label determined by the chosen outer-cycle index. -/
def p (X : M8PlanarBoundarySpineSkeleton D)
    (i : M8BoundaryIndex) :
    Fin n :=
  D.core.outerCycle.vertex (X.pIndex i)

/-- The explicitly chosen common-neighbor label `q_i`. -/
def q (X : M8PlanarBoundarySpineSkeleton D)
    (i : M8TriangleIndex) :
    Fin n :=
  X.2 i

@[simp]
theorem pIndex_apply (X : M8PlanarBoundarySpineSkeleton D)
    (i : M8BoundaryIndex) :
    X.pIndex i = X.1 i :=
  rfl

@[simp]
theorem q_apply (X : M8PlanarBoundarySpineSkeleton D)
    (i : M8TriangleIndex) :
    X.q i = X.2 i :=
  rfl

/-- The finite search space for the spine skeleton is finite. -/
instance fintype : Fintype (M8PlanarBoundarySpineSkeleton D) := by
  infer_instance

/--
The non-deterministic facts still needed after the planar boundary has
supplied the `p_i` boundary membership facts.
-/
structure Valid
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (X : M8PlanarBoundarySpineSkeleton D) : Prop where
  boundaryEdge :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).Adj
        (X.p (m8BoundaryIndexLeft i)) (X.p (m8BoundaryIndexRight i))
  triangleWitness :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).CommonNeighbor
        (X.p (m8BoundaryIndexLeft i)) (X.p (m8BoundaryIndexRight i))
        (X.q i)

variable {connectedNoCut : PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/-- The structural context attached to the planar-boundary skeleton. -/
def context
    (_X : M8PlanarBoundarySpineSkeleton D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    M8BoundaryCutDegreeContext C :=
  boundaryCutDegreeContextOfPlanarBoundary D connectedNoCut hmin

@[simp]
theorem context_eq
    (X : M8PlanarBoundarySpineSkeleton D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    X.context connectedNoCut hmin =
      boundaryCutDegreeContextOfPlanarBoundary D connectedNoCut hmin :=
  rfl

/-- The chosen `p_i` lies on the selected outer boundary. -/
theorem p_onBoundary
    (X : M8PlanarBoundarySpineSkeleton D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (i : M8BoundaryIndex) :
    (X.context connectedNoCut hmin).outerBoundary.outerEnclosure.onBoundary
      (X.p i) := by
  change D.core.outerEnclosure.onBoundary
    (D.core.outerCycle.vertex (X.pIndex i))
  simpa [p, OuterBoundaryCore.outerCycle] using
    D.core.boundary_vertex_onBoundary (X.pIndex i)

/-- Convert a valid finite skeleton into the spine interface. -/
def toM8BoundarySpine
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X) :
    M8BoundarySpine (X.context connectedNoCut hmin) where
  p := X.p
  q := X.q
  p_onBoundary := X.p_onBoundary connectedNoCut hmin
  boundaryEdge := hvalid.boundaryEdge
  triangleWitness := hvalid.triangleWitness

@[simp]
theorem toM8BoundarySpine_p
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X)
    (i : M8BoundaryIndex) :
    (X.toM8BoundarySpine hvalid).p i = X.p i :=
  rfl

@[simp]
theorem toM8BoundarySpine_q
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X)
    (i : M8TriangleIndex) :
    (X.toM8BoundarySpine hvalid).q i = X.q i :=
  rfl

theorem toM8BoundarySpine_boundaryEdge
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      ((X.toM8BoundarySpine hvalid).p (m8BoundaryIndexLeft i))
      ((X.toM8BoundarySpine hvalid).p (m8BoundaryIndexRight i)) :=
  hvalid.boundaryEdge i

theorem toM8BoundarySpine_triangleWitness
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      ((X.toM8BoundarySpine hvalid).p (m8BoundaryIndexLeft i))
      ((X.toM8BoundarySpine hvalid).p (m8BoundaryIndexRight i))
      ((X.toM8BoundarySpine hvalid).q i) :=
  hvalid.triangleWitness i

/-- A valid finite skeleton is exactly enough to produce a nonempty spine. -/
theorem nonempty_spine_of_exists_valid_skeleton
    (h :
      Exists fun X : M8PlanarBoundarySpineSkeleton D =>
        Valid connectedNoCut hmin X) :
    Nonempty (M8BoundarySpine
      (boundaryCutDegreeContextOfPlanarBoundary D connectedNoCut hmin)) := by
  exact Exists.elim h fun X hvalid =>
    Nonempty.intro (X.toM8BoundarySpine hvalid)

/-- The finite skeleton can be promoted to the planar M8 route once Lemma 8
extra-neighbor data is supplied for the resulting spine. -/
def toM8BoundaryRouteData
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X)
    (lemma8 : M8Lemma8Combinatorics (X.toM8BoundarySpine hvalid)) :
    M8BoundaryRouteData.{u} C hmin where
  planarBoundary := D
  connectedNoCut := connectedNoCut
  spine := X.toM8BoundarySpine hvalid
  lemma8 := lemma8

@[simp]
theorem toM8BoundaryRouteData_context
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X)
    (lemma8 : M8Lemma8Combinatorics (X.toM8BoundarySpine hvalid)) :
    (X.toM8BoundaryRouteData hvalid lemma8).context =
      X.context connectedNoCut hmin :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_spine
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X)
    (lemma8 : M8Lemma8Combinatorics (X.toM8BoundarySpine hvalid)) :
    (X.toM8BoundaryRouteData hvalid lemma8).spine =
      X.toM8BoundarySpine hvalid :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_labels_p
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X)
    (lemma8 : M8Lemma8Combinatorics (X.toM8BoundarySpine hvalid))
    (i : M8BoundaryIndex) :
    (X.toM8BoundaryRouteData hvalid lemma8).toM8LocalLabels.labels.p i =
      X.p i :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_labels_q
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X)
    (lemma8 : M8Lemma8Combinatorics (X.toM8BoundarySpine hvalid))
    (i : M8TriangleIndex) :
    (X.toM8BoundaryRouteData hvalid lemma8).toM8LocalLabels.labels.q i =
      X.q i :=
  rfl

/-- The route keeps the checked planar face-counting fields attached to the
same selected outer boundary. -/
theorem route_faceCounting_outerBoundary
    (X : M8PlanarBoundarySpineSkeleton D)
    (hvalid : Valid connectedNoCut hmin X)
    (lemma8 : M8Lemma8Combinatorics (X.toM8BoundarySpine hvalid)) :
    (X.toM8BoundaryRouteData hvalid lemma8).faceCounting.context_outerBoundary_eq =
      rfl :=
  rfl

end M8PlanarBoundarySpineSkeleton

end

end BoundarySpineConcrete
end Swanepoel
end ErdosProblems1066
