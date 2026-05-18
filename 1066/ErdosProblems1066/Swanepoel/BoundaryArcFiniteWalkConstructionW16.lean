import ErdosProblems1066.Swanepoel.BoundaryArcExtractionProofW15
import ErdosProblems1066.Swanepoel.ExactOuterBoundaryTopologyW13
import ErdosProblems1066.Swanepoel.TopologyToBoundaryArcW14
import ErdosProblems1066.Swanepoel.BoundaryArcW12
import ErdosProblems1066.Swanepoel.BoundaryClassificationW12

set_option autoImplicit false

/-!
# W16 finite boundary-walk construction

This file extracts the W15 finite boundary-walk data from the topology and
boundary-classification surfaces already present in W12--W14.

The new source package is a run of thirteen consecutive classified triangular
boundary edges on the selected outer cycle.  The boundary-classification layer
then supplies the common-neighbor witnesses required by
`BoundaryArcFiniteWalkData`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryArcFiniteWalkConstructionW16

open BoundaryArcExtractionProofW15
open BoundaryArcW12
open BoundaryWalkClassificationConcrete
open ExactOuterBoundaryTopologyW13
open M8LabelsFromBoundaryInterface
open TopologyToBoundaryArcW14

universe u

noncomputable section

variable {n : Nat}

/-- The canonical graph used by the W15 finite-walk target. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  BoundaryArcExtractionProofW15.CanonicalGraph C

/-! ## Consecutive triangular runs on the outer boundary -/

/--
A concrete run of the thirteen boundary edges needed for the selected
`m = 8` arc.

The indices are the fourteen boundary positions `p_0, ..., p_13`.  The step
field says that consecutive positions follow the selected outer cycle, while
`triangleEdge` says that each of those thirteen boundary edges is classified as
triangular in the concrete boundary-walk classification layer.
-/
structure BoundaryArcTriangleRun
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)) where
  pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length
  cyclicOrder :
    forall i : M8TriangleIndex,
      pIndex (m8BoundaryIndexRight i) =
        PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
          (pIndex (m8BoundaryIndexLeft i))
  triangleEdge :
    forall i : M8TriangleIndex,
      IsTriangleEdge (CanonicalGraph C)
        (D.core.outerCycle.edge (pIndex (m8BoundaryIndexLeft i)))

namespace BoundaryArcTriangleRun

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalGraph C)}

/-- The first selected boundary position. -/
def leftEndpoint (R : BoundaryArcTriangleRun D) :
    Fin D.core.outerCycle.length :=
  R.pIndex m8ArcFirstBoundaryIndex

/-- The last selected boundary position. -/
def rightEndpoint (R : BoundaryArcTriangleRun D) :
    Fin D.core.outerCycle.length :=
  R.pIndex m8ArcLastBoundaryIndex

/-- The common-neighbor label supplied by the triangular-edge classification. -/
def q (R : BoundaryArcTriangleRun D) (i : M8TriangleIndex) : Fin n :=
  Classical.choose (R.triangleEdge i).2

/-- The chosen `q_i` is the required common neighbor of the consecutive
boundary vertices. -/
theorem q_commonNeighbor
    (R : BoundaryArcTriangleRun D) (i : M8TriangleIndex) :
    (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor
      (D.core.outerCycle.vertex (R.pIndex (m8BoundaryIndexLeft i)))
      (D.core.outerCycle.vertex (R.pIndex (m8BoundaryIndexRight i)))
      (R.q i) := by
  have hq :
      (BoundaryWalkClassificationConcrete.unitLocalGraph (CanonicalGraph C)).CommonNeighbor
        (D.core.outerCycle.edge (R.pIndex (m8BoundaryIndexLeft i))).1
        (D.core.outerCycle.edge (R.pIndex (m8BoundaryIndexLeft i))).2
        (R.q i) :=
    Classical.choose_spec (R.triangleEdge i).2
  change
      (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor
        (D.core.outerCycle.vertex (R.pIndex (m8BoundaryIndexLeft i)))
        (D.core.outerCycle.vertex
          (PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (R.pIndex (m8BoundaryIndexLeft i))))
        (R.q i) at hq
  have hstep := R.cyclicOrder i
  rw [hstep]
  exact hq

/-- A consecutive triangular run gives the W15 finite boundary-walk data. -/
def toFiniteWalkData
    (R : BoundaryArcTriangleRun D) :
    BoundaryArcFiniteWalkData D where
  leftEndpoint := R.leftEndpoint
  rightEndpoint := R.rightEndpoint
  pIndex := R.pIndex
  q := R.q
  leftEndpoint_eq_p0 := rfl
  rightEndpoint_eq_p13 := rfl
  cyclicOrder := R.cyclicOrder
  triangleWitness := R.q_commonNeighbor

@[simp]
theorem toFiniteWalkData_pIndex
    (R : BoundaryArcTriangleRun D) (i : M8BoundaryIndex) :
    R.toFiniteWalkData.pIndex i = R.pIndex i :=
  rfl

@[simp]
theorem toFiniteWalkData_q
    (R : BoundaryArcTriangleRun D) (i : M8TriangleIndex) :
    R.toFiniteWalkData.q i = R.q i :=
  rfl

@[simp]
theorem toFiniteWalkData_leftEndpoint
    (R : BoundaryArcTriangleRun D) :
    R.toFiniteWalkData.leftEndpoint = R.leftEndpoint :=
  rfl

@[simp]
theorem toFiniteWalkData_rightEndpoint
    (R : BoundaryArcTriangleRun D) :
    R.toFiniteWalkData.rightEndpoint = R.rightEndpoint :=
  rfl

theorem toFiniteWalkData_cyclicOrder
    (R : BoundaryArcTriangleRun D) (i : M8TriangleIndex) :
    R.toFiniteWalkData.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (R.toFiniteWalkData.pIndex (m8BoundaryIndexLeft i)) :=
  R.cyclicOrder i

theorem toFiniteWalkData_triangleWitness
    (R : BoundaryArcTriangleRun D) (i : M8TriangleIndex) :
    (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor
      (R.toFiniteWalkData.p (m8BoundaryIndexLeft i))
      (R.toFiniteWalkData.p (m8BoundaryIndexRight i))
      (R.toFiniteWalkData.q i) := by
  change
    (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor
      (D.core.outerCycle.vertex (R.pIndex (m8BoundaryIndexLeft i)))
      (D.core.outerCycle.vertex (R.pIndex (m8BoundaryIndexRight i)))
      (R.q i)
  exact R.q_commonNeighbor i

end BoundaryArcTriangleRun

/-! ## Closing the W15 target from a supplied triangular run -/

/-- A pointwise triangular run closes the W15 finite-walk target. -/
theorem finiteWalkTarget_of_triangleRun
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
    (R :
      BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    BoundaryArcFiniteWalkTarget
      T outerAngleBounds Subpolygon subpolygonData longArc :=
  Nonempty.intro R.toFiniteWalkData

/-- A pointwise triangular run also closes the W14 extraction target. -/
theorem extractionTarget_of_triangleRun
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
    (R :
      BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    BoundaryArcExtractionTarget
      T outerAngleBounds Subpolygon subpolygonData longArc :=
  extractionTarget_of_finiteWalkTarget (finiteWalkTarget_of_triangleRun R)

/--
Uniform source theorem: every W14 topology/angle/subpolygon/long-arc row has a
thirteen-edge triangular successor run on its selected boundary.
-/
def BoundaryArcTriangleRunTheorem : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalGraph C))
    (_longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)),
      Nonempty
        (BoundaryArcTriangleRun
          (T.toPlanarBoundaryData outerAngleBounds Subpolygon
            subpolygonData))

/-- A uniform triangular-run theorem closes the W15 finite-walk theorem. -/
theorem finiteWalkTheorem_of_triangleRunTheorem
    (H : BoundaryArcTriangleRunTheorem.{u}) :
    BoundaryArcFiniteWalkTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro R =>
      exact finiteWalkTarget_of_triangleRun R

/-- A uniform triangular-run theorem closes the W14 extraction theorem. -/
theorem extractionTheorem_of_triangleRunTheorem
    (H : BoundaryArcTriangleRunTheorem.{u}) :
    BoundaryArcExtractionTheorem.{u} :=
  boundaryArcExtractionTheorem_of_finiteWalkTheorem
    (finiteWalkTheorem_of_triangleRunTheorem H)

end

end BoundaryArcFiniteWalkConstructionW16
end Swanepoel
end ErdosProblems1066
