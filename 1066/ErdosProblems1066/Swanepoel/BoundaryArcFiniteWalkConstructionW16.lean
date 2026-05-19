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
open BoundarySpineFiniteCertificate
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

/-! ## Triangle-run extraction from existing finite rows -/

theorem triangleEdge_of_boundaryArcCertificate
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
  change
    (GraphBridge.unitDistanceLocalGraph C).IsTriangleEdge
      (D.core.outerCycle.vertex (A.pIndex (m8BoundaryIndexLeft i)))
      (D.core.outerCycle.vertex
        (PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
          (A.pIndex (m8BoundaryIndexLeft i))))
  exact And.intro hadj (Exists.intro (A.q i) hcommon)

def ofBoundaryArcCertificate
    (A : M8BoundaryArcCertificate D) :
    BoundaryArcTriangleRun D where
  pIndex := A.pIndex
  cyclicOrder := A.cyclicOrder
  triangleEdge := triangleEdge_of_boundaryArcCertificate A

@[simp]
theorem ofBoundaryArcCertificate_pIndex
    (A : M8BoundaryArcCertificate D) (i : M8BoundaryIndex) :
    (ofBoundaryArcCertificate A).pIndex i = A.pIndex i :=
  rfl

@[simp]
theorem ofBoundaryArcCertificate_leftEndpoint
    (A : M8BoundaryArcCertificate D) :
    (ofBoundaryArcCertificate A).leftEndpoint = A.leftEndpoint :=
  A.leftEndpoint_eq_p0

@[simp]
theorem ofBoundaryArcCertificate_rightEndpoint
    (A : M8BoundaryArcCertificate D) :
    (ofBoundaryArcCertificate A).rightEndpoint = A.rightEndpoint :=
  A.rightEndpoint_eq_p13

theorem triangleEdge_of_finiteWalkData
    (W : BoundaryArcFiniteWalkData D) (i : M8TriangleIndex) :
    IsTriangleEdge (CanonicalGraph C)
      (D.core.outerCycle.edge (W.pIndex (m8BoundaryIndexLeft i))) :=
  triangleEdge_of_boundaryArcCertificate W.toBoundaryArcCertificate i

def ofFiniteWalkData
    (W : BoundaryArcFiniteWalkData D) :
    BoundaryArcTriangleRun D where
  pIndex := W.pIndex
  cyclicOrder := W.cyclicOrder
  triangleEdge := triangleEdge_of_finiteWalkData W

@[simp]
theorem ofFiniteWalkData_pIndex
    (W : BoundaryArcFiniteWalkData D) (i : M8BoundaryIndex) :
    (ofFiniteWalkData W).pIndex i = W.pIndex i :=
  rfl

/-- A finite `p/q` spine certificate gives a triangle run once its selected
`p_i` labels are known to be consecutive along the same outer boundary. -/
def ofFinitePQSpineCertificate
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i))) :
    BoundaryArcTriangleRun D :=
  ofFiniteWalkData
    (BoundaryArcFiniteWalkData.ofFinitePQSpineCertificate
      K (K.pIndex m8ArcFirstBoundaryIndex)
      (K.pIndex m8ArcLastBoundaryIndex) rfl rfl cyclicOrder)

/-- A finite `p/q` spine certificate gives a triangle run from the thirteen
concrete cyclic-successor equality rows. -/
def ofFinitePQSpineCertificateRows
    (K : M8FinitePQSpineCertificate D)
    (cyclicRows :
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K) :
    BoundaryArcTriangleRun D :=
  ofFiniteWalkData
    (BoundaryArcFiniteWalkData.ofFinitePQSpineCertificateRows
      K (K.pIndex m8ArcFirstBoundaryIndex)
      (K.pIndex m8ArcLastBoundaryIndex) rfl rfl cyclicRows)

@[simp]
theorem ofFinitePQSpineCertificate_pIndex
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (i : M8BoundaryIndex) :
    (ofFinitePQSpineCertificate K cyclicOrder).pIndex i = K.pIndex i :=
  rfl

@[simp]
theorem ofFinitePQSpineCertificateRows_pIndex
    (K : M8FinitePQSpineCertificate D)
    (cyclicRows :
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K)
    (i : M8BoundaryIndex) :
    (ofFinitePQSpineCertificateRows K cyclicRows).pIndex i = K.pIndex i :=
  rfl

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

/-- A boundary-arc certificate over the same planar boundary gives the
pointwise triangle-run row. -/
theorem triangleRunTarget_of_boundaryArcCertificate
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (boundaryArc :
      M8BoundaryArcCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    Nonempty
      (BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :=
  Nonempty.intro
    (BoundaryArcTriangleRun.ofBoundaryArcCertificate boundaryArc)

/-- W15 finite-walk data over the same planar boundary gives the pointwise
triangle-run row. -/
theorem triangleRunTarget_of_finiteWalkData
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (finiteWalk :
      BoundaryArcFiniteWalkData
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    Nonempty
      (BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :=
  Nonempty.intro
    (BoundaryArcTriangleRun.ofFiniteWalkData finiteWalk)

/-- A finite `p/q` spine over the same planar boundary gives the pointwise
triangle-run row once the selected `p_i` labels are consecutive. -/
theorem triangleRunTarget_of_finitePQSpineCertificate
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (K :
      M8FinitePQSpineCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc
            ((T.toPlanarBoundaryData outerAngleBounds Subpolygon
                subpolygonData).core.outerCycle.length_pos)
            (K.pIndex (m8BoundaryIndexLeft i))) :
    Nonempty
      (BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :=
  Nonempty.intro
    (BoundaryArcTriangleRun.ofFinitePQSpineCertificate K cyclicOrder)

/-- A finite `p/q` spine over the same planar boundary gives the pointwise
triangle-run row from the thirteen concrete cyclic-successor equality rows. -/
theorem triangleRunTarget_of_finitePQSpineCertificateRows
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (K :
      M8FinitePQSpineCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (cyclicRows :
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K) :
    Nonempty
      (BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :=
  Nonempty.intro
    (BoundaryArcTriangleRun.ofFinitePQSpineCertificateRows K cyclicRows)

/-! ## Boundary-arc certificates from upstream finite-spine fields -/

/-- Upstream finite-spine boundary-arc fields construct the W12 boundary-arc
certificate over the same selected planar boundary. -/
def boundaryArcCertificateOfFinitePQSpineBoundaryArcCertificateFields
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (K : M8FinitePQSpineCertificate D)
    (boundaryArcFields :
      M8FinitePQSpineBoundaryArcCertificateFields K) :
    M8BoundaryArcCertificate D where
  leftEndpoint := K.pIndex m8ArcFirstBoundaryIndex
  rightEndpoint := K.pIndex m8ArcLastBoundaryIndex
  pIndex := K.pIndex
  q := K.q
  leftEndpoint_eq_p0 := rfl
  rightEndpoint_eq_p13 := rfl
  cyclicOrder := boundaryArcFields.cyclicOrder_holds
  triangleWitness := by
    intro i
    have h := K.triangleWitness i
    rw [K.p_eq_outerCycle (m8BoundaryIndexLeft i),
      K.p_eq_outerCycle (m8BoundaryIndexRight i)] at h
    exact h

/-- Upstream finite-spine boundary-arc/frame-core fields also construct the
W12 boundary-arc certificate; the frame-core part is retained by generated
order consumers and is not needed for the boundary-arc projection itself. -/
def boundaryArcCertificateOfFinitePQSpineBoundaryArcFrameCoreFields
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (boundaryArcFrameCoreFields :
      M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin) :
    M8BoundaryArcCertificate D :=
  boundaryArcCertificateOfFinitePQSpineBoundaryArcCertificateFields
    K boundaryArcFrameCoreFields.boundaryArcFields

@[simp]
theorem boundaryArcCertificateOfFinitePQSpineBoundaryArcCertificateFields_pIndex
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (K : M8FinitePQSpineCertificate D)
    (boundaryArcFields :
      M8FinitePQSpineBoundaryArcCertificateFields K)
    (i : M8BoundaryIndex) :
    (boundaryArcCertificateOfFinitePQSpineBoundaryArcCertificateFields
      K boundaryArcFields).pIndex i =
        K.pIndex i :=
  rfl

@[simp]
theorem boundaryArcCertificateOfFinitePQSpineBoundaryArcCertificateFields_q
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (K : M8FinitePQSpineCertificate D)
    (boundaryArcFields :
      M8FinitePQSpineBoundaryArcCertificateFields K)
    (i : M8TriangleIndex) :
    (boundaryArcCertificateOfFinitePQSpineBoundaryArcCertificateFields
      K boundaryArcFields).q i =
        K.q i :=
  rfl

@[simp]
theorem boundaryArcCertificateOfFinitePQSpineBoundaryArcFrameCoreFields_pIndex
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (boundaryArcFrameCoreFields :
      M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin)
    (i : M8BoundaryIndex) :
    (boundaryArcCertificateOfFinitePQSpineBoundaryArcFrameCoreFields
      K boundaryArcFrameCoreFields).pIndex i =
        K.pIndex i :=
  rfl

@[simp]
theorem boundaryArcCertificateOfFinitePQSpineBoundaryArcFrameCoreFields_q
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (boundaryArcFrameCoreFields :
      M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin)
    (i : M8TriangleIndex) :
    (boundaryArcCertificateOfFinitePQSpineBoundaryArcFrameCoreFields
      K boundaryArcFrameCoreFields).q i =
        K.q i :=
  rfl

/-! ## Finite `p/q` cyclic-successor rows from finite walk data -/

/-- A finite spine certificate together with its concrete successor rows is
already the pointwise W16 finite-`p/q` successor-row target. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_finitePQSpineCertificateRows
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (K :
      M8FinitePQSpineCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (cyclicRows :
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Nonempty.intro (Subtype.mk K cyclicRows)

/-- Finite boundary-walk data packages its generated finite `p/q` spine with
the thirteen cyclic-successor equality rows. -/
def finitePQSpineCyclicSuccessorRowsOfFiniteWalkData
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (W : BoundaryArcFiniteWalkData D) :
    { K : M8FinitePQSpineCertificate D //
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Subtype.mk W.toFinitePQSpineCertificate
    (BoundaryArcFiniteWalkData.cyclicSuccessorRowsOfFiniteWalkData W)

def finitePQSpineCyclicSuccessorRowsOfFrameCoreData
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (W :
      BoundaryArcFiniteWalkFrameCoreData
        (D := D) connectedNoCut hmin) :
    { K : M8FinitePQSpineCertificate D //
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  finitePQSpineCyclicSuccessorRowsOfFiniteWalkData W.finiteWalk

/-- A boundary-arc certificate directly packages the generated finite `p/q`
spine with its thirteen cyclic-successor rows. -/
def finitePQSpineCyclicSuccessorRowsOfBoundaryArcCertificate
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (boundaryArc : M8BoundaryArcCertificate D) :
    { K : M8FinitePQSpineCertificate D //
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Subtype.mk boundaryArc.toFinitePQSpineCertificate
    (BoundaryArcFiniteWalkData.cyclicSuccessorRowsOfBoundaryArcCertificate
      boundaryArc)

/-- Raw finite-spine facts plus the boundary-arc successor rows give the W16
finite `p/q` cyclic-successor package.  The frame-core raw facts are included
so this matches the generated-order source surface without importing W32. -/
def finitePQSpineCyclicSuccessorRowsOfRawFinitePQFacts
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (prev_adj :
      forall i : M8ExtraIndex,
        (GraphBridge.unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (GraphBridge.unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexNextOfExtra i)))
    (left_ne_next :
      forall i : M8ExtraIndex,
        Not
          (K.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
            K.q (m8TriangleIndexNextOfExtra i)))
    (right_ne_prev :
      forall i : M8ExtraIndex,
        Not
          (K.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
            K.q (m8TriangleIndexPrevOfExtra i)))
    (prev_ne_next :
      forall i : M8ExtraIndex,
        Not
          (K.q (m8TriangleIndexPrevOfExtra i) =
            K.q (m8TriangleIndexNextOfExtra i))) :
    { K : M8FinitePQSpineCertificate D //
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  let boundaryArcFrameCoreFields :
      M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin :=
    M8FinitePQSpineBoundaryArcFrameCoreFields.ofCyclicOrderAndRawFinitePQFacts
      (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
      cyclicOrder prev_adj next_adj left_ne_next right_ne_prev prev_ne_next
  Subtype.mk K
    (BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows.ofCyclicOrder
      (K := K) boundaryArcFrameCoreFields.cyclicOrder_holds)

/-- Named raw frame-core facts plus row-wise cyclic successor rows give the
finite `p/q` cyclic-successor package, through the shared upstream
boundary-arc/frame-core source. -/
def finitePQSpineCyclicSuccessorRowsOfCyclicOrderAndRawFacts
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    { K : M8FinitePQSpineCertificate D //
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  let boundaryArcFrameCoreFields :
      M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin :=
    K.toBoundaryArcFrameCoreFieldsOfCyclicOrderAndRawFacts
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      cyclicOrder rawFacts
  Subtype.mk K
    (BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows.ofCyclicOrder
      (K := K) boundaryArcFrameCoreFields.cyclicOrder_holds)

/-- Explicit cyclic rows plus named raw frame-core facts give the finite
`p/q` cyclic-successor package. -/
def finitePQSpineCyclicSuccessorRowsOfExplicitCyclicOrderRowsAndRawFacts
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrderRows : M8FinitePQSpineCertificate.ExplicitCyclicOrderRows K)
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    { K : M8FinitePQSpineCertificate D //
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  finitePQSpineCyclicSuccessorRowsOfCyclicOrderAndRawFacts
    (connectedNoCut := connectedNoCut) (hmin := hmin)
    K cyclicOrderRows.cyclicOrder rawFacts

/-- Boundary-arc data plus frame-core fields is already enough for the finite
`p/q` cyclic-successor package; the successor rows are the ones carried by the
same boundary arc. -/
def finitePQSpineCyclicSuccessorRowsOfBoundaryArcFrameCoreFields
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryArc : M8BoundaryArcCertificate D)
    (_frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        boundaryArc.toFinitePQSpineCertificate connectedNoCut hmin) :
    { K : M8FinitePQSpineCertificate D //
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  finitePQSpineCyclicSuccessorRowsOfBoundaryArcCertificate boundaryArc

/-- Upstream finite-spine boundary-arc fields package the same finite spine
with the concrete W15 cyclic-successor rows. -/
def finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcCertificateFields
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (K : M8FinitePQSpineCertificate D)
    (boundaryArcFields :
      M8FinitePQSpineBoundaryArcCertificateFields K) :
    { K : M8FinitePQSpineCertificate D //
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Subtype.mk K
    (BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows.ofCyclicOrder
      boundaryArcFields.cyclicOrder_holds)

/-- Upstream finite-spine boundary-arc/frame-core fields package the same
finite spine with the concrete W15 cyclic-successor rows. -/
def finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcFrameCoreFields
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (boundaryArcFrameCoreFields :
      M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin) :
    { K : M8FinitePQSpineCertificate D //
      BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcCertificateFields
    K boundaryArcFrameCoreFields.boundaryArcFields

@[simp]
theorem finitePQSpineCyclicSuccessorRowsOfFiniteWalkData_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (W : BoundaryArcFiniteWalkData D) :
    (finitePQSpineCyclicSuccessorRowsOfFiniteWalkData W).1 =
      W.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem finitePQSpineCyclicSuccessorRowsOfFrameCoreData_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (W :
      BoundaryArcFiniteWalkFrameCoreData
        (D := D) connectedNoCut hmin) :
    (finitePQSpineCyclicSuccessorRowsOfFrameCoreData W).1 =
      W.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem finitePQSpineCyclicSuccessorRowsOfBoundaryArcCertificate_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (boundaryArc : M8BoundaryArcCertificate D) :
    (finitePQSpineCyclicSuccessorRowsOfBoundaryArcCertificate
      boundaryArc).1 =
      boundaryArc.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem finitePQSpineCyclicSuccessorRowsOfRawFinitePQFacts_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (prev_adj :
      forall i : M8ExtraIndex,
        (GraphBridge.unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (GraphBridge.unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexNextOfExtra i)))
    (left_ne_next :
      forall i : M8ExtraIndex,
        Not
          (K.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
            K.q (m8TriangleIndexNextOfExtra i)))
    (right_ne_prev :
      forall i : M8ExtraIndex,
        Not
          (K.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
            K.q (m8TriangleIndexPrevOfExtra i)))
    (prev_ne_next :
      forall i : M8ExtraIndex,
        Not
          (K.q (m8TriangleIndexPrevOfExtra i) =
            K.q (m8TriangleIndexNextOfExtra i))) :
    (finitePQSpineCyclicSuccessorRowsOfRawFinitePQFacts
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      K cyclicOrder prev_adj next_adj left_ne_next right_ne_prev
      prev_ne_next).1 = K :=
  rfl

@[simp]
theorem finitePQSpineCyclicSuccessorRowsOfCyclicOrderAndRawFacts_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    (finitePQSpineCyclicSuccessorRowsOfCyclicOrderAndRawFacts
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      K cyclicOrder rawFacts).1 = K :=
  rfl

@[simp]
theorem finitePQSpineCyclicSuccessorRowsOfExplicitCyclicOrderRowsAndRawFacts_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrderRows : M8FinitePQSpineCertificate.ExplicitCyclicOrderRows K)
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    (finitePQSpineCyclicSuccessorRowsOfExplicitCyclicOrderRowsAndRawFacts
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      K cyclicOrderRows rawFacts).1 = K :=
  rfl

@[simp]
theorem finitePQSpineCyclicSuccessorRowsOfBoundaryArcFrameCoreFields_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryArc : M8BoundaryArcCertificate D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        boundaryArc.toFinitePQSpineCertificate connectedNoCut hmin) :
    (finitePQSpineCyclicSuccessorRowsOfBoundaryArcFrameCoreFields
      boundaryArc frameCoreFields).1 =
      boundaryArc.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcCertificateFields_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (K : M8FinitePQSpineCertificate D)
    (boundaryArcFields :
      M8FinitePQSpineBoundaryArcCertificateFields K) :
    (finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcCertificateFields
      K boundaryArcFields).1 =
        K :=
  rfl

@[simp]
theorem finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcFrameCoreFields_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (K : M8FinitePQSpineCertificate D)
    (boundaryArcFrameCoreFields :
      M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin) :
    (finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcFrameCoreFields
      K boundaryArcFrameCoreFields).1 =
        K :=
  rfl

/-- A nonempty frame-core-data row over any fixed planar boundary immediately
supplies the finite `p/q` cyclic-successor row package. -/
theorem finitePQSpineCyclicSuccessorRows_nonempty_of_frameCoreData
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (h :
      Nonempty
        (BoundaryArcFiniteWalkFrameCoreData
          (D := D) connectedNoCut hmin)) :
    Nonempty
      { K : M8FinitePQSpineCertificate D //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } := by
  cases h with
  | intro finiteWalkFrameCore =>
      exact
        Nonempty.intro
          (finitePQSpineCyclicSuccessorRowsOfFrameCoreData
            finiteWalkFrameCore)

/-- Pointwise finite boundary-walk data supplies the W16 finite-`p/q`
successor-row target. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_finiteWalkData
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (finiteWalk :
      BoundaryArcFiniteWalkData
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Nonempty.intro
    (finitePQSpineCyclicSuccessorRowsOfFiniteWalkData finiteWalk)

/-- A pointwise boundary-arc certificate supplies the W16 finite-`p/q`
successor-row target directly. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_boundaryArcCertificate
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (boundaryArc :
      M8BoundaryArcCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Nonempty.intro
    (finitePQSpineCyclicSuccessorRowsOfBoundaryArcCertificate boundaryArc)

/-- Raw finite-spine facts, together with boundary-arc successor rows, close
the W16 finite-`p/q` successor-row target. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_rawFinitePQFacts
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
    (K :
      M8FinitePQSpineCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc
            ((T.toPlanarBoundaryData outerAngleBounds Subpolygon
                subpolygonData).core.outerCycle.length_pos)
            (K.pIndex (m8BoundaryIndexLeft i)))
    (prev_adj :
      forall i : M8ExtraIndex,
        (GraphBridge.unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (GraphBridge.unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexNextOfExtra i)))
    (left_ne_next :
      forall i : M8ExtraIndex,
        Not
          (K.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
            K.q (m8TriangleIndexNextOfExtra i)))
    (right_ne_prev :
      forall i : M8ExtraIndex,
        Not
          (K.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
            K.q (m8TriangleIndexPrevOfExtra i)))
    (prev_ne_next :
      forall i : M8ExtraIndex,
        Not
          (K.q (m8TriangleIndexPrevOfExtra i) =
            K.q (m8TriangleIndexNextOfExtra i))) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Nonempty.intro
    (finitePQSpineCyclicSuccessorRowsOfRawFinitePQFacts
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      K cyclicOrder prev_adj next_adj left_ne_next right_ne_prev
      prev_ne_next)

/-- Named raw frame-core facts, together with boundary-arc successor rows,
close the W16 finite-`p/q` successor-row target. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_cyclicOrderAndRawFacts
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
    (K :
      M8FinitePQSpineCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc
            ((T.toPlanarBoundaryData outerAngleBounds Subpolygon
                subpolygonData).core.outerCycle.length_pos)
            (K.pIndex (m8BoundaryIndexLeft i)))
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Nonempty.intro
    (finitePQSpineCyclicSuccessorRowsOfCyclicOrderAndRawFacts
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      K cyclicOrder rawFacts)

/-- Explicit cyclic successor rows plus named raw frame-core facts close the
W16 finite-`p/q` successor-row target. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_explicitCyclicOrderRowsAndRawFacts
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
    (K :
      M8FinitePQSpineCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (cyclicOrderRows :
      M8FinitePQSpineCertificate.ExplicitCyclicOrderRows K)
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Nonempty.intro
    (finitePQSpineCyclicSuccessorRowsOfExplicitCyclicOrderRowsAndRawFacts
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      K cyclicOrderRows rawFacts)

/-- A pointwise boundary-arc certificate with matching frame-core fields closes
the W16 finite-`p/q` successor-row target without first materializing the
frame-core data package. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_boundaryArcFrameCoreFields
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
    (boundaryArc :
      M8BoundaryArcCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        boundaryArc.toFinitePQSpineCertificate connectedNoCut hmin) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Nonempty.intro
    (finitePQSpineCyclicSuccessorRowsOfBoundaryArcFrameCoreFields
      boundaryArc frameCoreFields)

/-- Upstream finite-spine boundary-arc fields close the W16 finite-`p/q`
successor-row target while preserving the source finite spine. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_finitePQSpineBoundaryArcCertificateFields
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (K :
      M8FinitePQSpineCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (boundaryArcFields :
      M8FinitePQSpineBoundaryArcCertificateFields K) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Nonempty.intro
    (finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcCertificateFields
      K boundaryArcFields)

/-- Upstream finite-spine boundary-arc/frame-core fields close the W16
finite-`p/q` successor-row target while preserving the source finite spine. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_finitePQSpineBoundaryArcFrameCoreFields
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
    (K :
      M8FinitePQSpineCertificate
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (boundaryArcFrameCoreFields :
      M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  Nonempty.intro
    (finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcFrameCoreFields
      K boundaryArcFrameCoreFields)

/-- Pointwise finite boundary-walk frame-core data still carries the same
finite `p/q` spine and therefore supplies the W16 successor-row target. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_frameCoreData
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
    (finiteWalkFrameCore :
      BoundaryArcFiniteWalkFrameCoreData
        (D := T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)
        connectedNoCut hmin) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  finitePQSpineCyclicSuccessorRows_nonempty_of_frameCoreData
    (Nonempty.intro finiteWalkFrameCore)

/-- A pointwise finite-walk frame-core target is stronger than the W16
finite-`p/q` successor-row target.  The successor rows are read from the owned
finite walk, without using generated-order or actual-component closure data. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_frameCoreTarget
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
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } := by
  exact finitePQSpineCyclicSuccessorRows_nonempty_of_frameCoreData h

/-- A pointwise W15 finite-walk target supplies the W16 finite-`p/q`
successor-row target by forgetting to the generated finite spine. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_finiteWalkTarget
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
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } := by
  cases h with
  | intro finiteWalk =>
      exact
        finitePQSpineCyclicSuccessorRowsTarget_of_finiteWalkData
          (C := C) (T := T) (outerAngleBounds := outerAngleBounds)
          (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
          finiteWalk

/-- A pointwise W14 extraction target supplies the W16 finite-`p/q`
successor-row target through the W15 finite-walk data bridge. -/
theorem finitePQSpineCyclicSuccessorRowsTarget_of_extractionTarget
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
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K } :=
  finitePQSpineCyclicSuccessorRowsTarget_of_finiteWalkTarget
    (finiteWalkTarget_of_extractionTarget h)

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

/-!
## Direct finite-walk data source over S2/S3 boundary fields

This is the finite-walk owner surface for the non-circular S4 route.  It asks
for the actual W15 `BoundaryArcFiniteWalkData` over the planar boundary
assembled from the S2 topology rows and S3 angle/subpolygon rows, before any
generated-order or actual-component-closure data exists.
-/

/-- Uniform source theorem for finite boundary-walk data over the S2/S3
assembled planar boundary. -/
def BoundaryArcFiniteWalkDataTheorem : Prop :=
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
        (BoundaryArcFiniteWalkData
          (T.toPlanarBoundaryData outerAngleBounds Subpolygon
            subpolygonData))

/-- The direct finite-walk data source is exactly the W15 finite-walk theorem
surface, expressed without generated-order inputs. -/
theorem boundaryArcFiniteWalkTheorem_of_finiteWalkDataTheorem
    (H : BoundaryArcFiniteWalkDataTheorem.{u}) :
    BoundaryArcFiniteWalkTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  exact H C T outerAngleBounds Subpolygon subpolygonData longArc

/-- A W15 finite-walk theorem can be read as the direct W16 finite-walk data
source surface. -/
theorem finiteWalkDataTheorem_of_boundaryArcFiniteWalkTheorem
    (H : BoundaryArcFiniteWalkTheorem.{u}) :
    BoundaryArcFiniteWalkDataTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  exact H C T outerAngleBounds Subpolygon subpolygonData longArc

/-- A uniform triangular-run theorem constructs the direct finite-walk data
source over the same S2/S3 boundary fields. -/
theorem finiteWalkDataTheorem_of_triangleRunTheorem
    (H : BoundaryArcTriangleRunTheorem.{u}) :
    BoundaryArcFiniteWalkDataTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro R =>
      exact Nonempty.intro R.toFiniteWalkData

/--
Uniform finite-`p/q` successor-row source theorem.

This is the non-circular source surface for the S4 missing-field route: it is
keyed only to an arbitrary W14 topology/angle/subpolygon/long-arc row and does
not mention the selected actual-component closure that is later built from the
missing long-arc/triangle-run field.
-/
def FinitePQSpineCyclicSuccessorRowsTheorem : Prop :=
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
        { K :
            M8FinitePQSpineCertificate
              (T.toPlanarBoundaryData outerAngleBounds Subpolygon
                subpolygonData) //
          BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows K }

/--
Uniform source theorem from the upstream finite-spine boundary-arc fields.

This is the exact theorem-level input needed by W16: a selected finite
`p_i/q_i` certificate together with the thirteen cyclic-successor rows exposed
by `BoundarySpineFiniteCertificate`.
-/
def FinitePQSpineBoundaryArcCertificateFieldsTheorem : Prop :=
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
        { K :
            M8FinitePQSpineCertificate
              (T.toPlanarBoundaryData outerAngleBounds Subpolygon
                subpolygonData) //
          M8FinitePQSpineBoundaryArcCertificateFields K }

/--
Uniform source theorem from raw finite `p_i/q_i` facts.

The first component is the boundary-arc cyclic order needed by W16.  The
remaining five components are the raw finite frame-core facts used by the later
generated-order route; they are retained here so the same upstream source can
feed both consumers without rebuilding the raw rows.
-/
def FinitePQSpineRawFinitePQFactsTheorem : Prop :=
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
        { K :
            M8FinitePQSpineCertificate
              (T.toPlanarBoundaryData outerAngleBounds Subpolygon
                subpolygonData) //
          (forall i : M8TriangleIndex,
            K.pIndex (m8BoundaryIndexRight i) =
              PlanarInterface.cyclicSucc
                ((T.toPlanarBoundaryData outerAngleBounds Subpolygon
                    subpolygonData).core.outerCycle.length_pos)
                (K.pIndex (m8BoundaryIndexLeft i))) /\
          (forall i : M8ExtraIndex,
            (GraphBridge.unitDistanceLocalGraph C).Adj
              (K.q (m8TriangleIndexOfExtra i))
              (K.q (m8TriangleIndexPrevOfExtra i))) /\
          (forall i : M8ExtraIndex,
            (GraphBridge.unitDistanceLocalGraph C).Adj
              (K.q (m8TriangleIndexOfExtra i))
              (K.q (m8TriangleIndexNextOfExtra i))) /\
          (forall i : M8ExtraIndex,
            Not
              (K.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
                K.q (m8TriangleIndexNextOfExtra i))) /\
          (forall i : M8ExtraIndex,
            Not
              (K.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
                K.q (m8TriangleIndexPrevOfExtra i))) /\
          (forall i : M8ExtraIndex,
            Not
              (K.q (m8TriangleIndexPrevOfExtra i) =
                K.q (m8TriangleIndexNextOfExtra i))) }

/--
Uniform source theorem from a finite `p_i/q_i` label certificate, named
explicit cyclic-order rows, and named raw frame-core facts.

The cyclic rows are the W16-facing payload needed to materialize
`FinitePQSpineCyclicSuccessorRowsTheorem`; the raw facts are retained on the
same source surface so final assembly can pass the current finite-label source
without projecting or rebuilding the shared raw package elsewhere.
-/
def FinitePQSpineExplicitCyclicOrderRowsAndRawFactsTheorem : Prop :=
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
        { K :
            M8FinitePQSpineCertificate
              (T.toPlanarBoundaryData outerAngleBounds Subpolygon
                subpolygonData) //
          M8FinitePQSpineCertificate.ExplicitCyclicOrderRows K /\
          M8FinitePQSpineRawFrameCoreFacts K }

/-! ## Positive source inhabitation from finite walks and triangle runs -/

/-- A concrete finite walk already carries the upstream finite-spine
boundary-arc fields: keep its generated finite `p/q` spine and read the
cyclic-successor rows from the walk. -/
def finitePQSpineBoundaryArcCertificateFieldsOfFiniteWalkData
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (finiteWalk : BoundaryArcFiniteWalkData D) :
    { K : M8FinitePQSpineCertificate D //
      M8FinitePQSpineBoundaryArcCertificateFields K } :=
  Subtype.mk finiteWalk.toFinitePQSpineCertificate
    (M8FinitePQSpineBoundaryArcCertificateFields.ofCyclicOrder
      finiteWalk.toFinitePQSpineCertificate_cyclicOrder)

/-- A concrete triangle run gives the upstream finite-spine boundary-arc
fields via its associated finite walk. -/
def finitePQSpineBoundaryArcCertificateFieldsOfTriangleRun
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (R : BoundaryArcTriangleRun D) :
    { K : M8FinitePQSpineCertificate D //
      M8FinitePQSpineBoundaryArcCertificateFields K } :=
  finitePQSpineBoundaryArcCertificateFieldsOfFiniteWalkData R.toFiniteWalkData

@[simp]
theorem finitePQSpineBoundaryArcCertificateFieldsOfFiniteWalkData_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (finiteWalk : BoundaryArcFiniteWalkData D) :
    (finitePQSpineBoundaryArcCertificateFieldsOfFiniteWalkData finiteWalk).1 =
      finiteWalk.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem finitePQSpineBoundaryArcCertificateFieldsOfTriangleRun_val
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)}
    (R : BoundaryArcTriangleRun D) :
    (finitePQSpineBoundaryArcCertificateFieldsOfTriangleRun R).1 =
      R.toFiniteWalkData.toFinitePQSpineCertificate :=
  rfl

/-- Pointwise finite-walk data positively inhabits the W16 theorem-level
boundary-arc source package over the same S2/S3 boundary fields. -/
theorem finitePQSpineBoundaryArcCertificateFieldsTarget_of_finiteWalkData
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (finiteWalk :
      BoundaryArcFiniteWalkData
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        M8FinitePQSpineBoundaryArcCertificateFields K } :=
  Nonempty.intro
    (finitePQSpineBoundaryArcCertificateFieldsOfFiniteWalkData finiteWalk)

/-- Pointwise triangle-run data positively inhabits the W16 theorem-level
boundary-arc source package over the same S2/S3 boundary fields. -/
theorem finitePQSpineBoundaryArcCertificateFieldsTarget_of_triangleRun
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (R :
      BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    Nonempty
      { K :
          M8FinitePQSpineCertificate
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData) //
        M8FinitePQSpineBoundaryArcCertificateFields K } :=
  Nonempty.intro
    (finitePQSpineBoundaryArcCertificateFieldsOfTriangleRun R)

/-- A uniform finite-walk data source positively inhabits the theorem-level
upstream finite-spine boundary-arc source. -/
theorem finitePQSpineBoundaryArcCertificateFieldsTheorem_of_finiteWalkDataTheorem
    (H : BoundaryArcFiniteWalkDataTheorem.{u}) :
    FinitePQSpineBoundaryArcCertificateFieldsTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro finiteWalk =>
      exact
        finitePQSpineBoundaryArcCertificateFieldsTarget_of_finiteWalkData
          (C := C) (T := T) (outerAngleBounds := outerAngleBounds)
          (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
          finiteWalk

/-- A uniform triangle-run source positively inhabits the theorem-level
upstream finite-spine boundary-arc source. -/
theorem finitePQSpineBoundaryArcCertificateFieldsTheorem_of_triangleRunTheorem
    (H : BoundaryArcTriangleRunTheorem.{u}) :
    FinitePQSpineBoundaryArcCertificateFieldsTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro R =>
      exact
        finitePQSpineBoundaryArcCertificateFieldsTarget_of_triangleRun
          (C := C) (T := T) (outerAngleBounds := outerAngleBounds)
          (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
          R

/-- Upstream boundary-arc fields are exactly enough to close the W16
finite-`p/q` theorem. -/
theorem finitePQSpineCyclicSuccessorRowsTheorem_of_finitePQSpineBoundaryArcCertificateFieldsTheorem
    (H : FinitePQSpineBoundaryArcCertificateFieldsTheorem.{u}) :
    FinitePQSpineCyclicSuccessorRowsTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro S =>
      exact
        finitePQSpineCyclicSuccessorRowsTarget_of_finitePQSpineBoundaryArcCertificateFields
          (C := C) (T := T) (outerAngleBounds := outerAngleBounds)
          (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
          S.1 S.2

/-- Raw finite `p/q` facts supply the upstream boundary-arc fields used by
the actual W16 finite-`p/q` theorem. -/
theorem finitePQSpineBoundaryArcCertificateFieldsTheorem_of_rawFinitePQFactsTheorem
    (H : FinitePQSpineRawFinitePQFactsTheorem.{u}) :
    FinitePQSpineBoundaryArcCertificateFieldsTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro S =>
      exact
        Nonempty.intro
          (Subtype.mk S.1
            (M8FinitePQSpineBoundaryArcCertificateFields.ofCyclicOrder
              S.2.1))

/-- Raw finite `p/q` facts reduce directly to the actual W16 finite-`p/q`
successor-row theorem. -/
theorem finitePQSpineCyclicSuccessorRowsTheorem_of_rawFinitePQFactsTheorem
    (H : FinitePQSpineRawFinitePQFactsTheorem.{u}) :
    FinitePQSpineCyclicSuccessorRowsTheorem.{u} :=
  finitePQSpineCyclicSuccessorRowsTheorem_of_finitePQSpineBoundaryArcCertificateFieldsTheorem
    (finitePQSpineBoundaryArcCertificateFieldsTheorem_of_rawFinitePQFactsTheorem
      H)

/-- Explicit cyclic-order rows plus named raw frame-core facts reduce directly
to the actual W16 finite-`p/q` successor-row theorem. -/
theorem finitePQSpineCyclicSuccessorRowsTheorem_of_explicitCyclicOrderRowsAndRawFactsTheorem
    (H : FinitePQSpineExplicitCyclicOrderRowsAndRawFactsTheorem.{u}) :
    FinitePQSpineCyclicSuccessorRowsTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro S =>
      exact
        finitePQSpineCyclicSuccessorRowsTarget_of_finitePQSpineCertificateRows
          (C := C) (T := T) (outerAngleBounds := outerAngleBounds)
          (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
          S.1
          (BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows.ofCyclicOrder
            S.2.1.cyclicOrder)

/-- Uniform finite-`p/q` successor rows supply the W16 triangle-run theorem. -/
theorem triangleRunTheorem_of_finitePQSpineCyclicSuccessorRowsTheorem
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    BoundaryArcTriangleRunTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro S =>
      exact triangleRunTarget_of_finitePQSpineCertificateRows S.1 S.2

/-- Uniform finite-`p/q` successor rows close the W15 finite-walk theorem. -/
theorem finiteWalkTheorem_of_finitePQSpineCyclicSuccessorRowsTheorem
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    BoundaryArcFiniteWalkTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro S =>
      exact
        finiteWalkTarget_of_triangleRun
          (BoundaryArcTriangleRun.ofFinitePQSpineCertificateRows S.1 S.2)

/-- A uniform W15 finite-walk theorem supplies the W16 finite-`p/q`
successor-row theorem by keeping the finite spine and its successor rows. -/
theorem finitePQSpineCyclicSuccessorRowsTheorem_of_finiteWalkTheorem
    (H : BoundaryArcFiniteWalkTheorem.{u}) :
    FinitePQSpineCyclicSuccessorRowsTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  exact
    finitePQSpineCyclicSuccessorRowsTarget_of_finiteWalkTarget
      (C := C) (T := T) (outerAngleBounds := outerAngleBounds)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
      (longArc := longArc)
      (H C T outerAngleBounds Subpolygon subpolygonData longArc)

/-- A uniform W14 extraction theorem directly supplies the W16 finite-`p/q`
successor-row theorem through the W15 finite-walk bridge. -/
theorem finitePQSpineCyclicSuccessorRowsTheorem_of_boundaryArcExtractionTheorem
    (H : BoundaryArcExtractionTheorem.{u}) :
    FinitePQSpineCyclicSuccessorRowsTheorem.{u} :=
  finitePQSpineCyclicSuccessorRowsTheorem_of_finiteWalkTheorem
    (finiteWalkTheorem_of_boundaryArcExtractionTheorem H)

/-- Direct finite-walk data over the S2/S3 boundary fields supplies the W16
finite-`p/q` successor-row theorem by retaining the finite spine and its
thirteen successor equalities. -/
theorem finitePQSpineCyclicSuccessorRowsTheorem_of_finiteWalkDataTheorem
    (H : BoundaryArcFiniteWalkDataTheorem.{u}) :
    FinitePQSpineCyclicSuccessorRowsTheorem.{u} :=
  finitePQSpineCyclicSuccessorRowsTheorem_of_finiteWalkTheorem
    (boundaryArcFiniteWalkTheorem_of_finiteWalkDataTheorem H)

/-- A uniform rowwise triangle-run source supplies the W16 finite-`p/q`
successor-row theorem through the direct finite-walk data bridge. -/
theorem finitePQSpineCyclicSuccessorRowsTheorem_of_triangleRunTheorem
    (H : BoundaryArcTriangleRunTheorem.{u}) :
    FinitePQSpineCyclicSuccessorRowsTheorem.{u} :=
  finitePQSpineCyclicSuccessorRowsTheorem_of_finiteWalkDataTheorem
    (finiteWalkDataTheorem_of_triangleRunTheorem H)

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
