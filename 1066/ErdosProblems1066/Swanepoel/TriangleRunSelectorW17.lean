import ErdosProblems1066.Swanepoel.BoundaryArcFiniteWalkConstructionW16

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace TriangleRunSelectorW17

open BoundaryArcExtractionProofW15
open BoundaryArcFiniteWalkConstructionW16
open BoundaryArcW12
open BoundarySpineFiniteCertificate
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

/-! ## Explicit triangle-run rows -/

/--
Explicit source rows for the selected `m = 8` thirteen-edge triangle run.

This is the field-by-field surface that a geometric construction must provide:
the fourteen boundary indices `p_0, ..., p_13`, the thirteen cyclic-successor
equalities, and the thirteen proofs that the corresponding outer-cycle edge is
triangular.  No indices are chosen here.
-/
structure ExplicitM8TriangleRunIndices
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

namespace ExplicitM8TriangleRunIndices

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalGraph C)}

/-- The concrete boundary index `p_0` selected by the run. -/
def p0 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 0 (by norm_num))

/-- The concrete boundary index `p_1` selected by the run. -/
def p1 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 1 (by norm_num))

/-- The concrete boundary index `p_2` selected by the run. -/
def p2 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 2 (by norm_num))

/-- The concrete boundary index `p_3` selected by the run. -/
def p3 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 3 (by norm_num))

/-- The concrete boundary index `p_4` selected by the run. -/
def p4 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 4 (by norm_num))

/-- The concrete boundary index `p_5` selected by the run. -/
def p5 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 5 (by norm_num))

/-- The concrete boundary index `p_6` selected by the run. -/
def p6 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 6 (by norm_num))

/-- The concrete boundary index `p_7` selected by the run. -/
def p7 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 7 (by norm_num))

/-- The concrete boundary index `p_8` selected by the run. -/
def p8 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 8 (by norm_num))

/-- The concrete boundary index `p_9` selected by the run. -/
def p9 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 9 (by norm_num))

/-- The concrete boundary index `p_10` selected by the run. -/
def p10 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 10 (by norm_num))

/-- The concrete boundary index `p_11` selected by the run. -/
def p11 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 11 (by norm_num))

/-- The concrete boundary index `p_12` selected by the run. -/
def p12 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 12 (by norm_num))

/-- The concrete boundary index `p_13` selected by the run. -/
def p13 (R : ExplicitM8TriangleRunIndices D) :
    Fin D.core.outerCycle.length :=
  R.pIndex (Subtype.mk 13 (by norm_num))

theorem cyclicOrder0 (R : ExplicitM8TriangleRunIndices D) :
    R.p1 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p0 := by
  simpa only [p0, p1, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 0 (by norm_num))

theorem cyclicOrder1 (R : ExplicitM8TriangleRunIndices D) :
    R.p2 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p1 := by
  simpa only [p1, p2, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 1 (by norm_num))

theorem cyclicOrder2 (R : ExplicitM8TriangleRunIndices D) :
    R.p3 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p2 := by
  simpa only [p2, p3, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 2 (by norm_num))

theorem cyclicOrder3 (R : ExplicitM8TriangleRunIndices D) :
    R.p4 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p3 := by
  simpa only [p3, p4, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 3 (by norm_num))

theorem cyclicOrder4 (R : ExplicitM8TriangleRunIndices D) :
    R.p5 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p4 := by
  simpa only [p4, p5, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 4 (by norm_num))

theorem cyclicOrder5 (R : ExplicitM8TriangleRunIndices D) :
    R.p6 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p5 := by
  simpa only [p5, p6, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 5 (by norm_num))

theorem cyclicOrder6 (R : ExplicitM8TriangleRunIndices D) :
    R.p7 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p6 := by
  simpa only [p6, p7, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 6 (by norm_num))

theorem cyclicOrder7 (R : ExplicitM8TriangleRunIndices D) :
    R.p8 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p7 := by
  simpa only [p7, p8, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 7 (by norm_num))

theorem cyclicOrder8 (R : ExplicitM8TriangleRunIndices D) :
    R.p9 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p8 := by
  simpa only [p8, p9, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 8 (by norm_num))

theorem cyclicOrder9 (R : ExplicitM8TriangleRunIndices D) :
    R.p10 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p9 := by
  simpa only [p9, p10, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 9 (by norm_num))

theorem cyclicOrder10 (R : ExplicitM8TriangleRunIndices D) :
    R.p11 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p10 := by
  simpa only [p10, p11, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 10 (by norm_num))

theorem cyclicOrder11 (R : ExplicitM8TriangleRunIndices D) :
    R.p12 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p11 := by
  simpa only [p11, p12, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 11 (by norm_num))

theorem cyclicOrder12 (R : ExplicitM8TriangleRunIndices D) :
    R.p13 =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos R.p12 := by
  simpa only [p12, p13, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
    R.cyclicOrder (Subtype.mk 12 (by norm_num))

theorem triangleEdge0 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p0) := by
  simpa only [p0, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 0 (by norm_num))

theorem triangleEdge1 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p1) := by
  simpa only [p1, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 1 (by norm_num))

theorem triangleEdge2 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p2) := by
  simpa only [p2, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 2 (by norm_num))

theorem triangleEdge3 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p3) := by
  simpa only [p3, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 3 (by norm_num))

theorem triangleEdge4 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p4) := by
  simpa only [p4, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 4 (by norm_num))

theorem triangleEdge5 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p5) := by
  simpa only [p5, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 5 (by norm_num))

theorem triangleEdge6 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p6) := by
  simpa only [p6, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 6 (by norm_num))

theorem triangleEdge7 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p7) := by
  simpa only [p7, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 7 (by norm_num))

theorem triangleEdge8 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p8) := by
  simpa only [p8, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 8 (by norm_num))

theorem triangleEdge9 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p9) := by
  simpa only [p9, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 9 (by norm_num))

theorem triangleEdge10 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p10) := by
  simpa only [p10, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 10 (by norm_num))

theorem triangleEdge11 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p11) := by
  simpa only [p11, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 11 (by norm_num))

theorem triangleEdge12 (R : ExplicitM8TriangleRunIndices D) :
    IsTriangleEdge (CanonicalGraph C) (D.core.outerCycle.edge R.p12) := by
  simpa only [p12, m8BoundaryIndexLeft] using
    R.triangleEdge (Subtype.mk 12 (by norm_num))

def toTriangleRun
    (R : ExplicitM8TriangleRunIndices D) :
    BoundaryArcTriangleRun D where
  pIndex := R.pIndex
  cyclicOrder := R.cyclicOrder
  triangleEdge := R.triangleEdge

def ofTriangleRun
    (R : BoundaryArcTriangleRun D) :
    ExplicitM8TriangleRunIndices D where
  pIndex := R.pIndex
  cyclicOrder := R.cyclicOrder
  triangleEdge := R.triangleEdge

@[simp]
theorem toTriangleRun_pIndex
    (R : ExplicitM8TriangleRunIndices D) (i : M8BoundaryIndex) :
    R.toTriangleRun.pIndex i = R.pIndex i :=
  rfl

@[simp]
theorem ofTriangleRun_pIndex
    (R : BoundaryArcTriangleRun D) (i : M8BoundaryIndex) :
    (ofTriangleRun R).pIndex i = R.pIndex i :=
  rfl

theorem toTriangleRun_cyclicOrder
    (R : ExplicitM8TriangleRunIndices D) (i : M8TriangleIndex) :
    R.toTriangleRun.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (R.toTriangleRun.pIndex (m8BoundaryIndexLeft i)) :=
  R.cyclicOrder i

theorem toTriangleRun_triangleEdge
    (R : ExplicitM8TriangleRunIndices D) (i : M8TriangleIndex) :
    IsTriangleEdge (CanonicalGraph C)
      (D.core.outerCycle.edge
        (R.toTriangleRun.pIndex (m8BoundaryIndexLeft i))) :=
  R.triangleEdge i

def equivTriangleRun :
    ExplicitM8TriangleRunIndices D ≃ BoundaryArcTriangleRun D where
  toFun := toTriangleRun
  invFun := ofTriangleRun
  left_inv := by
    intro R
    cases R
    rfl
  right_inv := by
    intro R
    cases R
    rfl

theorem nonempty_iff_triangleRun :
    Nonempty (ExplicitM8TriangleRunIndices D) <->
      Nonempty (BoundaryArcTriangleRun D) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R => exact Nonempty.intro R.toTriangleRun
  case mpr =>
    intro h
    cases h with
    | intro R => exact Nonempty.intro (ofTriangleRun R)

end ExplicitM8TriangleRunIndices

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

theorem triangleRunTarget_of_explicitM8TriangleRunIndices
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    (R :
      ExplicitM8TriangleRunIndices
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :
    Nonempty
      (BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :=
  Nonempty.intro R.toTriangleRun

theorem explicitM8TriangleRunIndicesTarget_of_triangleRun
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
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :
    Nonempty
      (ExplicitM8TriangleRunIndices
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :=
  Nonempty.intro (ExplicitM8TriangleRunIndices.ofTriangleRun R)

theorem explicitM8TriangleRunIndicesTarget_of_extractionTarget
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
      (ExplicitM8TriangleRunIndices
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) := by
  cases h with
  | intro A =>
      exact
        explicitM8TriangleRunIndicesTarget_of_triangleRun
          (BoundaryArcSelector.triangleRunOfExtractionFields A)

theorem explicitM8TriangleRunIndicesTarget_of_finiteWalkTarget
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
      (ExplicitM8TriangleRunIndices
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) := by
  cases h with
  | intro W =>
      exact
        explicitM8TriangleRunIndicesTarget_of_triangleRun
          (BoundaryArcSelector.triangleRunOfFiniteWalkData W)

theorem explicitM8TriangleRunIndicesTarget_of_finiteWalkData
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
      (ExplicitM8TriangleRunIndices
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :=
  explicitM8TriangleRunIndicesTarget_of_triangleRun
    (BoundaryArcSelector.triangleRunOfFiniteWalkData finiteWalk)

theorem explicitM8TriangleRunIndicesTarget_of_finitePQSpineCertificateRows
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
      (ExplicitM8TriangleRunIndices
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :=
  explicitM8TriangleRunIndicesTarget_of_triangleRun
    (BoundaryArcTriangleRun.ofFinitePQSpineCertificateRows K cyclicRows)

theorem explicitM8TriangleRunIndicesTarget_of_finitePQSpineBoundaryArcCertificateFields
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
      (ExplicitM8TriangleRunIndices
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :=
  explicitM8TriangleRunIndicesTarget_of_finitePQSpineCertificateRows
    K
    (BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows.ofCyclicOrder
      boundaryArcFields.cyclicOrder_holds)

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

/--
Uniform source theorem for explicit triangle-run indices over the S2/S3
boundary fields.  This is the row surface to prove from geometry: it asks for
the actual selected `p_i` indices and triangular-edge proofs, not merely an
already-packaged `BoundaryArcTriangleRun`.
-/
def ExplicitM8TriangleRunIndicesTheorem : Prop :=
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
        (ExplicitM8TriangleRunIndices
          (T.toPlanarBoundaryData outerAngleBounds Subpolygon
            subpolygonData))

theorem explicitM8TriangleRunIndicesTheorem_of_triangleRunTheorem
    (H : BoundaryArcTriangleRunTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro R =>
      exact explicitM8TriangleRunIndicesTarget_of_triangleRun R

theorem explicitM8TriangleRunIndicesTheorem_of_extractionTheorem
    (H : BoundaryArcExtractionTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  exact
    explicitM8TriangleRunIndicesTarget_of_extractionTarget
      (H C T outerAngleBounds Subpolygon subpolygonData longArc)

theorem explicitM8TriangleRunIndicesTheorem_of_finiteWalkTheorem
    (H : BoundaryArcFiniteWalkTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  exact
    explicitM8TriangleRunIndicesTarget_of_finiteWalkTarget
      (H C T outerAngleBounds Subpolygon subpolygonData longArc)

theorem explicitM8TriangleRunIndicesTheorem_of_finiteWalkDataTheorem
    (H : BoundaryArcFiniteWalkDataTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro finiteWalk =>
      exact explicitM8TriangleRunIndicesTarget_of_finiteWalkData finiteWalk

/--
W16 finite-`p/q` successor rows supply the named explicit `p_0, ..., p_13`
triangle-run indices over the same S2/S3 boundary row.
-/
theorem explicitM8TriangleRunIndicesTheorem_of_finitePQSpineCyclicSuccessorRowsTheorem
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro S =>
      exact
        explicitM8TriangleRunIndicesTarget_of_finitePQSpineCertificateRows
          S.1 S.2

theorem explicitM8TriangleRunIndicesTheorem_of_finitePQSpineBoundaryArcCertificateFieldsTheorem
    (H : FinitePQSpineBoundaryArcCertificateFieldsTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro S =>
      exact
        explicitM8TriangleRunIndicesTarget_of_finitePQSpineBoundaryArcCertificateFields
          S.1 S.2

theorem explicitM8TriangleRunIndicesTheorem_of_rawFinitePQFactsTheorem
    (H : FinitePQSpineRawFinitePQFactsTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} :=
  explicitM8TriangleRunIndicesTheorem_of_finitePQSpineCyclicSuccessorRowsTheorem
    (finitePQSpineCyclicSuccessorRowsTheorem_of_rawFinitePQFactsTheorem H)

theorem triangleRunTheorem_of_explicitM8TriangleRunIndicesTheorem
    (H : ExplicitM8TriangleRunIndicesTheorem.{u}) :
    BoundaryArcTriangleRunTheorem.{u} := by
  intro n C T outerAngleBounds Subpolygon subpolygonData longArc
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro R =>
      exact triangleRunTarget_of_explicitM8TriangleRunIndices R

theorem finitePQSpineCyclicSuccessorRowsTheorem_of_explicitM8TriangleRunIndicesTheorem
    (H : ExplicitM8TriangleRunIndicesTheorem.{u}) :
    FinitePQSpineCyclicSuccessorRowsTheorem.{u} :=
  finitePQSpineCyclicSuccessorRowsTheorem_of_triangleRunTheorem
    (triangleRunTheorem_of_explicitM8TriangleRunIndicesTheorem H)

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

theorem explicitM8TriangleRunIndicesTheorem_iff_triangleRunTheorem :
    ExplicitM8TriangleRunIndicesTheorem.{u} <->
      BoundaryArcTriangleRunTheorem.{u} := by
  constructor
  case mp =>
    exact triangleRunTheorem_of_explicitM8TriangleRunIndicesTheorem
  case mpr =>
    exact explicitM8TriangleRunIndicesTheorem_of_triangleRunTheorem

namespace ExplicitM8TriangleRunIndicesTheorem

theorem ofTriangleRunTheorem
    (H : BoundaryArcTriangleRunTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} :=
  explicitM8TriangleRunIndicesTheorem_of_triangleRunTheorem H

theorem ofExtractionTheorem
    (H : BoundaryArcExtractionTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} :=
  explicitM8TriangleRunIndicesTheorem_of_extractionTheorem H

theorem ofFiniteWalkTheorem
    (H : BoundaryArcFiniteWalkTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} :=
  explicitM8TriangleRunIndicesTheorem_of_finiteWalkTheorem H

theorem ofFiniteWalkDataTheorem
    (H : BoundaryArcFiniteWalkDataTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} :=
  explicitM8TriangleRunIndicesTheorem_of_finiteWalkDataTheorem H

theorem ofFinitePQSpineCyclicSuccessorRowsTheorem
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} :=
  explicitM8TriangleRunIndicesTheorem_of_finitePQSpineCyclicSuccessorRowsTheorem H

theorem ofFinitePQSpineBoundaryArcCertificateFieldsTheorem
    (H : FinitePQSpineBoundaryArcCertificateFieldsTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} :=
  explicitM8TriangleRunIndicesTheorem_of_finitePQSpineBoundaryArcCertificateFieldsTheorem H

theorem ofRawFinitePQFactsTheorem
    (H : FinitePQSpineRawFinitePQFactsTheorem.{u}) :
    ExplicitM8TriangleRunIndicesTheorem.{u} :=
  explicitM8TriangleRunIndicesTheorem_of_rawFinitePQFactsTheorem H

theorem toFinitePQSpineCyclicSuccessorRowsTheorem
    (H : ExplicitM8TriangleRunIndicesTheorem.{u}) :
    FinitePQSpineCyclicSuccessorRowsTheorem.{u} :=
  finitePQSpineCyclicSuccessorRowsTheorem_of_explicitM8TriangleRunIndicesTheorem H

end ExplicitM8TriangleRunIndicesTheorem

namespace BoundaryArcTriangleRunTheorem

theorem ofExtractionTheorem
    (H : BoundaryArcExtractionTheorem.{u}) :
    BoundaryArcTriangleRunTheorem.{u} :=
  triangleRunTheorem_of_extractionTheorem H

theorem ofFiniteWalkTheorem
    (H : BoundaryArcFiniteWalkTheorem.{u}) :
    BoundaryArcTriangleRunTheorem.{u} :=
  triangleRunTheorem_of_finiteWalkTheorem H

/--
The non-circular finite-`p/q` successor-row theorem supplies the uniform
triangle-run theorem.  The supplier is the W16 source surface
`BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem`,
not a generated-order row family derived from an actual component closure.
-/
theorem ofFinitePQSpineCyclicSuccessorRowsTheorem
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    BoundaryArcTriangleRunTheorem.{u} :=
  triangleRunTheorem_of_finitePQSpineCyclicSuccessorRowsTheorem H

theorem ofFinitePQSpineCertificateRows
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    BoundaryArcTriangleRunTheorem.{u} :=
  ofFinitePQSpineCyclicSuccessorRowsTheorem H

theorem ofExplicitM8TriangleRunIndicesTheorem
    (H : ExplicitM8TriangleRunIndicesTheorem.{u}) :
    BoundaryArcTriangleRunTheorem.{u} :=
  triangleRunTheorem_of_explicitM8TriangleRunIndicesTheorem H

end BoundaryArcTriangleRunTheorem

end

end TriangleRunSelectorW17

end Swanepoel
end ErdosProblems1066
