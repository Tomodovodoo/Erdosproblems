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

end BoundaryArcFiniteWalkData

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
