import ErdosProblems1066.Swanepoel.BoundaryArcFiniteWalkConstructionW16

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace TriangleRunSelectorW17

open BoundaryArcExtractionProofW15
open BoundaryArcFiniteWalkConstructionW16
open BoundaryArcW12
open BoundaryWalkClassificationConcrete
open ExactOuterBoundaryTopologyW13
open M8LabelsFromBoundaryInterface
open TopologyToBoundaryArcW14

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  BoundaryArcFiniteWalkConstructionW16.CanonicalGraph C

namespace BoundaryArcSelector

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalGraph C)}

theorem triangleEdge_of_boundaryArc
    (A : M8BoundaryArcCertificate D) (i : M8TriangleIndex) :
    IsTriangleEdge (CanonicalGraph C)
      (D.core.outerCycle.edge (A.pIndex (m8BoundaryIndexLeft i))) := by
  have hadj :
      (GraphBridge.unitDistanceLocalGraph C).Adj
        (D.core.outerCycle.vertex (A.pIndex (m8BoundaryIndexLeft i)))
        (D.core.outerCycle.vertex
          (PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (A.pIndex (m8BoundaryIndexLeft i)))) := by
    have h := A.boundaryEdge i
    change
      (GraphBridge.unitDistanceLocalGraph C).Adj
        (D.core.outerCycle.vertex (A.pIndex (m8BoundaryIndexLeft i)))
        (D.core.outerCycle.vertex (A.pIndex (m8BoundaryIndexRight i))) at h
    rw [A.cyclicOrder i] at h
    exact h
  have hcommon :
      (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor
        (D.core.outerCycle.vertex (A.pIndex (m8BoundaryIndexLeft i)))
        (D.core.outerCycle.vertex
          (PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (A.pIndex (m8BoundaryIndexLeft i))))
        (A.q i) := by
    have h := A.triangleWitness_holds i
    change
      (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor
        (D.core.outerCycle.vertex (A.pIndex (m8BoundaryIndexLeft i)))
        (D.core.outerCycle.vertex (A.pIndex (m8BoundaryIndexRight i)))
        (A.q i) at h
    rw [A.cyclicOrder i] at h
    exact h
  exact And.intro hadj (Exists.intro (A.q i) hcommon)

def triangleRunOfBoundaryArc
    (A : M8BoundaryArcCertificate D) :
    BoundaryArcTriangleRun D where
  pIndex := A.pIndex
  cyclicOrder := A.cyclicOrder
  triangleEdge := triangleEdge_of_boundaryArc A

@[simp]
theorem triangleRunOfBoundaryArc_pIndex
    (A : M8BoundaryArcCertificate D) (i : M8BoundaryIndex) :
    (triangleRunOfBoundaryArc A).pIndex i = A.pIndex i :=
  rfl

@[simp]
theorem triangleRunOfBoundaryArc_leftEndpoint
    (A : M8BoundaryArcCertificate D) :
    (triangleRunOfBoundaryArc A).leftEndpoint = A.leftEndpoint :=
  A.leftEndpoint_eq_p0

@[simp]
theorem triangleRunOfBoundaryArc_rightEndpoint
    (A : M8BoundaryArcCertificate D) :
    (triangleRunOfBoundaryArc A).rightEndpoint = A.rightEndpoint :=
  A.rightEndpoint_eq_p13

def triangleRunOfExtractionFields
    (A : BoundaryArcExtractionFields D) :
    BoundaryArcTriangleRun D :=
  triangleRunOfBoundaryArc A.boundaryArc

@[simp]
theorem triangleRunOfExtractionFields_pIndex
    (A : BoundaryArcExtractionFields D) (i : M8BoundaryIndex) :
    (triangleRunOfExtractionFields A).pIndex i =
      A.boundaryArc.pIndex i :=
  rfl

def triangleRunOfFiniteWalkData
    (W : BoundaryArcFiniteWalkData D) :
    BoundaryArcTriangleRun D :=
  triangleRunOfBoundaryArc W.toBoundaryArcCertificate

@[simp]
theorem triangleRunOfFiniteWalkData_pIndex
    (W : BoundaryArcFiniteWalkData D) (i : M8BoundaryIndex) :
    (triangleRunOfFiniteWalkData W).pIndex i = W.pIndex i :=
  rfl

end BoundaryArcSelector

namespace TopologyBoundaryArcFields

variable {C : _root_.UDConfig n}

def triangleRun
    (R : TopologyBoundaryArcFields.{u} C) :
    BoundaryArcTriangleRun R.planarBoundary :=
  BoundaryArcSelector.triangleRunOfExtractionFields R.arcExtraction

@[simp]
theorem triangleRun_pIndex
    (R : TopologyBoundaryArcFields.{u} C) (i : M8BoundaryIndex) :
    (triangleRun R).pIndex i = R.boundaryArc.pIndex i :=
  rfl

end TopologyBoundaryArcFields

theorem triangleRunTarget_of_extractionTarget
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
    Nonempty
      (BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) := by
  cases h with
  | intro A =>
      exact Nonempty.intro
        (BoundaryArcSelector.triangleRunOfExtractionFields A)

theorem triangleRunTarget_of_finiteWalkTarget
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
    Nonempty
      (BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) := by
  cases h with
  | intro W =>
      exact Nonempty.intro
        (BoundaryArcSelector.triangleRunOfFiniteWalkData W)

theorem triangleRunTheorem_of_extractionTheorem
    (H : BoundaryArcExtractionTheorem.{u}) :
    BoundaryArcTriangleRunTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  exact
    triangleRunTarget_of_extractionTarget
      (H C T outerAngleBounds Subpolygon subpolygonData longArc)

theorem triangleRunTheorem_of_finiteWalkTheorem
    (H : BoundaryArcFiniteWalkTheorem.{u}) :
    BoundaryArcTriangleRunTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  exact
    triangleRunTarget_of_finiteWalkTarget
      (H C T outerAngleBounds Subpolygon subpolygonData longArc)

theorem boundaryArcExtractionTheorem_iff_triangleRunTheorem :
    BoundaryArcExtractionTheorem.{u} <->
      BoundaryArcTriangleRunTheorem.{u} := by
  constructor
  case mp =>
    exact triangleRunTheorem_of_extractionTheorem
  case mpr =>
    exact extractionTheorem_of_triangleRunTheorem

theorem boundaryArcFiniteWalkTheorem_iff_triangleRunTheorem :
    BoundaryArcFiniteWalkTheorem.{u} <->
      BoundaryArcTriangleRunTheorem.{u} := by
  constructor
  case mp =>
    exact triangleRunTheorem_of_finiteWalkTheorem
  case mpr =>
    exact finiteWalkTheorem_of_triangleRunTheorem

end

end TriangleRunSelectorW17
end Swanepoel
end ErdosProblems1066
