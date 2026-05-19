import ErdosProblems1066.Swanepoel.BoundarySpineConcrete
import ErdosProblems1066.Swanepoel.BoundaryWalkConstruction

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
open BoundaryWalkConstruction
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

/-! ## Boundary-arc fields internal to finite spine certificates -/

/-- The first boundary label in the selected finite `m = 8` arc. -/
def m8FinitePQSpineArcFirstBoundaryIndex : M8BoundaryIndex :=
  Subtype.mk 0 (by norm_num)

/-- The last boundary label in the selected finite `m = 8` arc. -/
def m8FinitePQSpineArcLastBoundaryIndex : M8BoundaryIndex :=
  Subtype.mk 13 (by norm_num)

@[simp]
theorem m8FinitePQSpineArcFirstBoundaryIndex_val :
    m8FinitePQSpineArcFirstBoundaryIndex.1 = 0 :=
  rfl

@[simp]
theorem m8FinitePQSpineArcLastBoundaryIndex_val :
    m8FinitePQSpineArcLastBoundaryIndex.1 = 13 :=
  rfl

/--
The exact boundary-arc rows carried by a finite `p/q` spine certificate.

Downstream `BoundaryArcW12` constructs the actual `M8BoundaryArcCertificate`
from the same rows.  This upstream form records only the non-definitional
payload: the thirteen cyclic-successor equalities.  The endpoint markers are
the finite spine's own `p_0` and `p_13` indices, exposed by the projection
theorems below.
-/
structure M8FinitePQSpineBoundaryArcCertificateFields
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C)}
    (K : M8FinitePQSpineCertificate D) : Prop where
  cyclicOrder :
    forall i : M8TriangleIndex,
      K.pIndex (m8BoundaryIndexRight i) =
        PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
          (K.pIndex (m8BoundaryIndexLeft i))

namespace M8FinitePQSpineBoundaryArcCertificateFields

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}
variable {K : M8FinitePQSpineCertificate D}

/-- Constructor from the row-wise cyclic-successor proof. -/
def ofCyclicOrder
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i))) :
    M8FinitePQSpineBoundaryArcCertificateFields K where
  cyclicOrder := cyclicOrder

/-- Projection of the row-wise cyclic successor equality. -/
theorem cyclicOrder_holds
    (A : M8FinitePQSpineBoundaryArcCertificateFields K)
    (i : M8TriangleIndex) :
    K.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (m8BoundaryIndexLeft i)) := by
  exact A.cyclicOrder i

/-- The arc-field package is exactly the finite cyclic-successor row family. -/
theorem fields_iff_cyclicOrder :
    M8FinitePQSpineBoundaryArcCertificateFields K <->
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)) := by
  constructor
  case mp =>
    intro A
    exact cyclicOrder_holds A
  case mpr =>
    intro cyclicOrder
    exact ofCyclicOrder cyclicOrder

end M8FinitePQSpineBoundaryArcCertificateFields

namespace M8FinitePQSpineCertificate

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}
variable {connectedNoCut : PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/-- The left endpoint marker used by downstream boundary-arc certificates. -/
def boundaryArcLeftEndpoint
    (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex m8FinitePQSpineArcFirstBoundaryIndex

/-- The right endpoint marker used by downstream boundary-arc certificates. -/
def boundaryArcRightEndpoint
    (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex m8FinitePQSpineArcLastBoundaryIndex

@[simp]
theorem boundaryArcLeftEndpoint_eq_p0
    (K : M8FinitePQSpineCertificate D) :
    K.pIndex m8FinitePQSpineArcFirstBoundaryIndex =
      K.boundaryArcLeftEndpoint :=
  rfl

@[simp]
theorem boundaryArcRightEndpoint_eq_p13
    (K : M8FinitePQSpineCertificate D) :
    K.pIndex m8FinitePQSpineArcLastBoundaryIndex =
      K.boundaryArcRightEndpoint :=
  rfl

/-- Package the cyclic-successor rows as finite boundary-arc fields. -/
def toBoundaryArcCertificateFields
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i))) :
    M8FinitePQSpineBoundaryArcCertificateFields K :=
  M8FinitePQSpineBoundaryArcCertificateFields.ofCyclicOrder cyclicOrder

theorem toBoundaryArcCertificateFields_cyclicOrder
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (i : M8TriangleIndex) :
    K.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (m8BoundaryIndexLeft i)) :=
  (K.toBoundaryArcCertificateFields cyclicOrder).cyclicOrder_holds i

/-! ### Explicit projection rows for finite triangle runs -/

/-- The boundary position `p_0` selected by a finite spine certificate. -/
def p0 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 0 (by norm_num))

/-- The boundary position `p_1` selected by a finite spine certificate. -/
def p1 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 1 (by norm_num))

/-- The boundary position `p_2` selected by a finite spine certificate. -/
def p2 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 2 (by norm_num))

/-- The boundary position `p_3` selected by a finite spine certificate. -/
def p3 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 3 (by norm_num))

/-- The boundary position `p_4` selected by a finite spine certificate. -/
def p4 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 4 (by norm_num))

/-- The boundary position `p_5` selected by a finite spine certificate. -/
def p5 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 5 (by norm_num))

/-- The boundary position `p_6` selected by a finite spine certificate. -/
def p6 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 6 (by norm_num))

/-- The boundary position `p_7` selected by a finite spine certificate. -/
def p7 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 7 (by norm_num))

/-- The boundary position `p_8` selected by a finite spine certificate. -/
def p8 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 8 (by norm_num))

/-- The boundary position `p_9` selected by a finite spine certificate. -/
def p9 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 9 (by norm_num))

/-- The boundary position `p_10` selected by a finite spine certificate. -/
def p10 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 10 (by norm_num))

/-- The boundary position `p_11` selected by a finite spine certificate. -/
def p11 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 11 (by norm_num))

/-- The boundary position `p_12` selected by a finite spine certificate. -/
def p12 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 12 (by norm_num))

/-- The boundary position `p_13` selected by a finite spine certificate. -/
def p13 (K : M8FinitePQSpineCertificate D) :
    Fin D.core.outerCycle.length :=
  K.pIndex (Subtype.mk 13 (by norm_num))

/-- Named cyclic-successor rows for the explicit finite `p_0, ..., p_13` run. -/
structure ExplicitCyclicOrderRows
    (K : M8FinitePQSpineCertificate D) : Prop where
  cyclicOrder0 :
    K.p1 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p0
  cyclicOrder1 :
    K.p2 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p1
  cyclicOrder2 :
    K.p3 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p2
  cyclicOrder3 :
    K.p4 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p3
  cyclicOrder4 :
    K.p5 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p4
  cyclicOrder5 :
    K.p6 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p5
  cyclicOrder6 :
    K.p7 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p6
  cyclicOrder7 :
    K.p8 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p7
  cyclicOrder8 :
    K.p9 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p8
  cyclicOrder9 :
    K.p10 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p9
  cyclicOrder10 :
    K.p11 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p10
  cyclicOrder11 :
    K.p12 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p11
  cyclicOrder12 :
    K.p13 = PlanarInterface.cyclicSucc D.core.outerCycle.length_pos K.p12

namespace ExplicitCyclicOrderRows

variable {K : M8FinitePQSpineCertificate D}

/-- Build the named cyclic rows from the row-wise successor family. -/
def ofCyclicOrder
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i))) :
    ExplicitCyclicOrderRows K where
  cyclicOrder0 := by
    simpa only [p0, p1, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 0 (by norm_num))
  cyclicOrder1 := by
    simpa only [p1, p2, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 1 (by norm_num))
  cyclicOrder2 := by
    simpa only [p2, p3, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 2 (by norm_num))
  cyclicOrder3 := by
    simpa only [p3, p4, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 3 (by norm_num))
  cyclicOrder4 := by
    simpa only [p4, p5, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 4 (by norm_num))
  cyclicOrder5 := by
    simpa only [p5, p6, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 5 (by norm_num))
  cyclicOrder6 := by
    simpa only [p6, p7, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 6 (by norm_num))
  cyclicOrder7 := by
    simpa only [p7, p8, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 7 (by norm_num))
  cyclicOrder8 := by
    simpa only [p8, p9, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 8 (by norm_num))
  cyclicOrder9 := by
    simpa only [p9, p10, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 9 (by norm_num))
  cyclicOrder10 := by
    simpa only [p10, p11, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 10 (by norm_num))
  cyclicOrder11 := by
    simpa only [p11, p12, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 11 (by norm_num))
  cyclicOrder12 := by
    simpa only [p12, p13, m8BoundaryIndexLeft, m8BoundaryIndexRight] using
      cyclicOrder (Subtype.mk 12 (by norm_num))

/-- Repack named cyclic rows as the row-wise successor family. -/
theorem cyclicOrder
    (R : ExplicitCyclicOrderRows K) :
    forall i : M8TriangleIndex,
      K.pIndex (m8BoundaryIndexRight i) =
        PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
          (K.pIndex (m8BoundaryIndexLeft i)) := by
  intro i
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

/-- Build the upstream boundary-arc fields from named explicit rows. -/
def boundaryArcCertificateFields
    (R : ExplicitCyclicOrderRows K) :
    M8FinitePQSpineBoundaryArcCertificateFields K :=
  M8FinitePQSpineBoundaryArcCertificateFields.ofCyclicOrder R.cyclicOrder

/-- Named cyclic rows are equivalent to the row-wise successor family. -/
theorem rows_iff_cyclicOrder :
    ExplicitCyclicOrderRows K <->
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)) := by
  constructor
  case mp =>
    intro R
    exact R.cyclicOrder
  case mpr =>
    intro cyclicOrder
    exact ofCyclicOrder cyclicOrder

end ExplicitCyclicOrderRows

/-- The concrete triangular-edge predicate at a selected outer-cycle index. -/
def triangleEdgeAt
    (_K : M8FinitePQSpineCertificate D)
    (j : Fin D.core.outerCycle.length) : Prop :=
  (unitDistanceLocalGraph C).IsTriangleEdge
    (D.core.outerCycle.edge j).1 (D.core.outerCycle.edge j).2

theorem triangleEdgeAt_of_cyclicOrder
    (K : M8FinitePQSpineCertificate D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (i : M8TriangleIndex) :
    K.triangleEdgeAt (K.pIndex (m8BoundaryIndexLeft i)) := by
  have hadj :
      (unitDistanceLocalGraph C).Adj
        (D.core.outerCycle.vertex (K.pIndex (m8BoundaryIndexLeft i)))
        (D.core.outerCycle.vertex (K.pIndex (m8BoundaryIndexRight i))) := by
    simpa [K.p_eq_outerCycle (m8BoundaryIndexLeft i),
      K.p_eq_outerCycle (m8BoundaryIndexRight i)] using K.boundaryEdge i
  have hcommon :
      (unitDistanceLocalGraph C).CommonNeighbor
        (D.core.outerCycle.vertex (K.pIndex (m8BoundaryIndexLeft i)))
        (D.core.outerCycle.vertex (K.pIndex (m8BoundaryIndexRight i)))
        (K.q i) := by
    simpa [K.p_eq_outerCycle (m8BoundaryIndexLeft i),
      K.p_eq_outerCycle (m8BoundaryIndexRight i)] using K.triangleWitness i
  rw [cyclicOrder i] at hadj hcommon
  change
    (unitDistanceLocalGraph C).IsTriangleEdge
      (D.core.outerCycle.vertex (K.pIndex (m8BoundaryIndexLeft i)))
      (D.core.outerCycle.vertex
        (PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
          (K.pIndex (m8BoundaryIndexLeft i))))
  exact And.intro hadj (Exists.intro (K.q i) hcommon)

/-- Named triangular-edge row at `p_0`, derived from the finite spine fields. -/
theorem triangleEdge0
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p0 := by
  simpa only [p0, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 0 (by norm_num))

/-- Named triangular-edge row at `p_1`, derived from the finite spine fields. -/
theorem triangleEdge1
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p1 := by
  simpa only [p1, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 1 (by norm_num))

/-- Named triangular-edge row at `p_2`, derived from the finite spine fields. -/
theorem triangleEdge2
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p2 := by
  simpa only [p2, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 2 (by norm_num))

/-- Named triangular-edge row at `p_3`, derived from the finite spine fields. -/
theorem triangleEdge3
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p3 := by
  simpa only [p3, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 3 (by norm_num))

/-- Named triangular-edge row at `p_4`, derived from the finite spine fields. -/
theorem triangleEdge4
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p4 := by
  simpa only [p4, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 4 (by norm_num))

/-- Named triangular-edge row at `p_5`, derived from the finite spine fields. -/
theorem triangleEdge5
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p5 := by
  simpa only [p5, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 5 (by norm_num))

/-- Named triangular-edge row at `p_6`, derived from the finite spine fields. -/
theorem triangleEdge6
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p6 := by
  simpa only [p6, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 6 (by norm_num))

/-- Named triangular-edge row at `p_7`, derived from the finite spine fields. -/
theorem triangleEdge7
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p7 := by
  simpa only [p7, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 7 (by norm_num))

/-- Named triangular-edge row at `p_8`, derived from the finite spine fields. -/
theorem triangleEdge8
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p8 := by
  simpa only [p8, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 8 (by norm_num))

/-- Named triangular-edge row at `p_9`, derived from the finite spine fields. -/
theorem triangleEdge9
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p9 := by
  simpa only [p9, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 9 (by norm_num))

/-- Named triangular-edge row at `p_10`, derived from the finite spine fields. -/
theorem triangleEdge10
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p10 := by
  simpa only [p10, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 10 (by norm_num))

/-- Named triangular-edge row at `p_11`, derived from the finite spine fields. -/
theorem triangleEdge11
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p11 := by
  simpa only [p11, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 11 (by norm_num))

/-- Named triangular-edge row at `p_12`, derived from the finite spine fields. -/
theorem triangleEdge12
    (K : M8FinitePQSpineCertificate D)
    (R : ExplicitCyclicOrderRows K) :
    K.triangleEdgeAt K.p12 := by
  simpa only [p12, m8BoundaryIndexLeft] using
    K.triangleEdgeAt_of_cyclicOrder R.cyclicOrder
      (Subtype.mk 12 (by norm_num))

/-- Explicit triangle-run projections generated from cyclic rows and the
existing finite-spine edge/common-neighbor fields. -/
structure ExplicitTriangleRunRows
    (K : M8FinitePQSpineCertificate D) : Prop where
  cyclicOrderRows : ExplicitCyclicOrderRows K
  triangleEdge0 : K.triangleEdgeAt K.p0
  triangleEdge1 : K.triangleEdgeAt K.p1
  triangleEdge2 : K.triangleEdgeAt K.p2
  triangleEdge3 : K.triangleEdgeAt K.p3
  triangleEdge4 : K.triangleEdgeAt K.p4
  triangleEdge5 : K.triangleEdgeAt K.p5
  triangleEdge6 : K.triangleEdgeAt K.p6
  triangleEdge7 : K.triangleEdgeAt K.p7
  triangleEdge8 : K.triangleEdgeAt K.p8
  triangleEdge9 : K.triangleEdgeAt K.p9
  triangleEdge10 : K.triangleEdgeAt K.p10
  triangleEdge11 : K.triangleEdgeAt K.p11
  triangleEdge12 : K.triangleEdgeAt K.p12

namespace ExplicitTriangleRunRows

variable {K : M8FinitePQSpineCertificate D}

/-- Constructor from named cyclic rows; triangle-edge rows come from the
finite certificate's boundary-edge and common-neighbor fields. -/
def ofCyclicOrderRows
    (R : ExplicitCyclicOrderRows K) :
    ExplicitTriangleRunRows K where
  cyclicOrderRows := R
  triangleEdge0 := K.triangleEdge0 R
  triangleEdge1 := K.triangleEdge1 R
  triangleEdge2 := K.triangleEdge2 R
  triangleEdge3 := K.triangleEdge3 R
  triangleEdge4 := K.triangleEdge4 R
  triangleEdge5 := K.triangleEdge5 R
  triangleEdge6 := K.triangleEdge6 R
  triangleEdge7 := K.triangleEdge7 R
  triangleEdge8 := K.triangleEdge8 R
  triangleEdge9 := K.triangleEdge9 R
  triangleEdge10 := K.triangleEdge10 R
  triangleEdge11 := K.triangleEdge11 R
  triangleEdge12 := K.triangleEdge12 R

/-- Repack explicit triangle-run rows as the row-wise successor family. -/
theorem cyclicOrder
    (R : ExplicitTriangleRunRows K) :
    forall i : M8TriangleIndex,
      K.pIndex (m8BoundaryIndexRight i) =
        PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
          (K.pIndex (m8BoundaryIndexLeft i)) :=
  R.cyclicOrderRows.cyclicOrder

/-- Forget to upstream boundary-arc fields for the same finite spine. -/
def boundaryArcCertificateFields
    (R : ExplicitTriangleRunRows K) :
    M8FinitePQSpineBoundaryArcCertificateFields K :=
  R.cyclicOrderRows.boundaryArcCertificateFields

end ExplicitTriangleRunRows

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

/-! ## Honest boundary-core extraction rows -/

/--
Concrete source rows for extracting the finite `p_i/q_i` spine from an honest
selected outer boundary.

Compared with `M8FinitePQSpineCertificate`, these rows record the actual
outer-cycle edge that supports each boundary edge `p_i p_{i+1}`.  The bridge
below derives the finite certificate's boundary-edge field from that honest
edge provenance.
-/
structure M8BoundaryCorePQSpineRows
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C)) where
  pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length
  q : M8TriangleIndex -> Fin n
  edgeIndex : M8TriangleIndex -> Fin D.core.outerCycle.length
  boundaryEdge_left :
    forall i : M8TriangleIndex,
      D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)) =
        (D.core.outerCycle.edge (edgeIndex i)).1
  boundaryEdge_right :
    forall i : M8TriangleIndex,
      D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)) =
        (D.core.outerCycle.edge (edgeIndex i)).2
  triangleWitness :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).CommonNeighbor
        (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
        (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i)

namespace M8BoundaryCorePQSpineRows

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}

/-- The boundary label selected by the core rows. -/
def p (R : M8BoundaryCorePQSpineRows D)
    (i : M8BoundaryIndex) : Fin n :=
  D.core.outerCycle.vertex (R.pIndex i)

@[simp]
theorem p_eq_outerCycle
    (R : M8BoundaryCorePQSpineRows D) (i : M8BoundaryIndex) :
    R.p i = D.core.outerCycle.vertex (R.pIndex i) :=
  rfl

/-- Boundary-edge adjacency derived from the recorded honest outer-cycle edge. -/
theorem boundaryEdge
    (R : M8BoundaryCorePQSpineRows D) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (R.p (m8BoundaryIndexLeft i)) (R.p (m8BoundaryIndexRight i)) := by
  have h := D.core.outerCycle.edge_unitDistanceAdj (R.edgeIndex i)
  simpa [p, GraphBridge.unitDistanceLocalGraph, CanonicalUDGraph,
    R.boundaryEdge_left i, R.boundaryEdge_right i] using h

/-- Projection of the supplied common-neighbor rows in finite-label notation. -/
theorem triangleWitness_holds
    (R : M8BoundaryCorePQSpineRows D) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (R.p (m8BoundaryIndexLeft i)) (R.p (m8BoundaryIndexRight i)) (R.q i) :=
  R.triangleWitness i

/--
Convert honest boundary-core rows into the finite `p_i/q_i` spine certificate
consumed by the Lemma 8 label packages.
-/
def toFinitePQSpineCertificate
    (R : M8BoundaryCorePQSpineRows D) :
    M8FinitePQSpineCertificate D where
  pIndex := R.pIndex
  p := R.p
  q := R.q
  p_eq_outerCycle := R.p_eq_outerCycle
  boundaryEdge := R.boundaryEdge
  triangleWitness := R.triangleWitness_holds

@[simp]
theorem toFinitePQSpineCertificate_pIndex
    (R : M8BoundaryCorePQSpineRows D) (i : M8BoundaryIndex) :
    R.toFinitePQSpineCertificate.pIndex i = R.pIndex i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_p
    (R : M8BoundaryCorePQSpineRows D) (i : M8BoundaryIndex) :
    R.toFinitePQSpineCertificate.p i = R.p i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_q
    (R : M8BoundaryCorePQSpineRows D) (i : M8TriangleIndex) :
    R.toFinitePQSpineCertificate.q i = R.q i :=
  rfl

theorem toFinitePQSpineCertificate_boundaryEdge
    (R : M8BoundaryCorePQSpineRows D) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (R.toFinitePQSpineCertificate.p (m8BoundaryIndexLeft i))
      (R.toFinitePQSpineCertificate.p (m8BoundaryIndexRight i)) :=
  R.boundaryEdge i

theorem toFinitePQSpineCertificate_triangleWitness
    (R : M8BoundaryCorePQSpineRows D) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (R.toFinitePQSpineCertificate.p (m8BoundaryIndexLeft i))
      (R.toFinitePQSpineCertificate.p (m8BoundaryIndexRight i))
      (R.toFinitePQSpineCertificate.q i) :=
  R.triangleWitness_holds i

/--
Build core rows from a consecutive run on the selected outer cycle.  This is
the W15-shaped source: the right endpoint of each selected edge is the cyclic
successor of its left endpoint.
-/
def ofCyclicOrder
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i)) :
    M8BoundaryCorePQSpineRows D where
  pIndex := pIndex
  q := q
  edgeIndex := fun i => pIndex (m8BoundaryIndexLeft i)
  boundaryEdge_left := by
    intro i
    simp
  boundaryEdge_right := by
    intro i
    simpa using congrArg D.core.outerCycle.vertex (cyclicOrder i)
  triangleWitness := triangleWitness

@[simp]
theorem ofCyclicOrder_pIndex
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i))
    (i : M8BoundaryIndex) :
    (ofCyclicOrder (D := D) pIndex q cyclicOrder triangleWitness).pIndex i =
      pIndex i :=
  rfl

@[simp]
theorem ofCyclicOrder_q
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i))
    (i : M8TriangleIndex) :
    (ofCyclicOrder (D := D) pIndex q cyclicOrder triangleWitness).q i =
      q i :=
  rfl

@[simp]
theorem ofCyclicOrder_edgeIndex
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i))
    (i : M8TriangleIndex) :
    (ofCyclicOrder (D := D) pIndex q cyclicOrder triangleWitness).edgeIndex i =
      pIndex (m8BoundaryIndexLeft i) :=
  rfl

/-- Consecutive core rows give the finite `p_i/q_i` spine certificate. -/
def finitePQSpineCertificateOfCyclicOrder
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i)) :
    M8FinitePQSpineCertificate D :=
  (ofCyclicOrder (D := D) pIndex q cyclicOrder
    triangleWitness).toFinitePQSpineCertificate

@[simp]
theorem finitePQSpineCertificateOfCyclicOrder_pIndex
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i))
    (i : M8BoundaryIndex) :
    (finitePQSpineCertificateOfCyclicOrder
      (D := D) pIndex q cyclicOrder triangleWitness).pIndex i =
        pIndex i :=
  rfl

@[simp]
theorem finitePQSpineCertificateOfCyclicOrder_p
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i))
    (i : M8BoundaryIndex) :
    (finitePQSpineCertificateOfCyclicOrder
      (D := D) pIndex q cyclicOrder triangleWitness).p i =
        D.core.outerCycle.vertex (pIndex i) :=
  rfl

@[simp]
theorem finitePQSpineCertificateOfCyclicOrder_q
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i))
    (i : M8TriangleIndex) :
    (finitePQSpineCertificateOfCyclicOrder
      (D := D) pIndex q cyclicOrder triangleWitness).q i =
        q i :=
  rfl

theorem finitePQSpineCertificateOfCyclicOrder_cyclicOrder
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i))
    (i : M8TriangleIndex) :
    (finitePQSpineCertificateOfCyclicOrder
      (D := D) pIndex q cyclicOrder triangleWitness).pIndex
        (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        ((finitePQSpineCertificateOfCyclicOrder
          (D := D) pIndex q cyclicOrder triangleWitness).pIndex
            (m8BoundaryIndexLeft i)) := by
  simpa using cyclicOrder i

theorem finitePQSpineCertificateOfCyclicOrder_triangleWitness
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i))
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      ((finitePQSpineCertificateOfCyclicOrder
        (D := D) pIndex q cyclicOrder triangleWitness).p
          (m8BoundaryIndexLeft i))
      ((finitePQSpineCertificateOfCyclicOrder
        (D := D) pIndex q cyclicOrder triangleWitness).p
          (m8BoundaryIndexRight i))
      ((finitePQSpineCertificateOfCyclicOrder
        (D := D) pIndex q cyclicOrder triangleWitness).q i) :=
  triangleWitness i

/--
Consecutive core rows directly inhabit the upstream boundary-arc fields for
their generated finite `p/q` spine certificate.
-/
theorem finitePQSpineCertificateOfCyclicOrder_boundaryArcCertificateFields
    (pIndex : M8BoundaryIndex -> Fin D.core.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (D.core.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)))
          (q i)) :
    M8FinitePQSpineBoundaryArcCertificateFields
      (finitePQSpineCertificateOfCyclicOrder
        (D := D) pIndex q cyclicOrder triangleWitness) :=
  M8FinitePQSpineBoundaryArcCertificateFields.ofCyclicOrder
    (K := finitePQSpineCertificateOfCyclicOrder
      (D := D) pIndex q cyclicOrder triangleWitness)
    (finitePQSpineCertificateOfCyclicOrder_cyclicOrder
      (D := D) pIndex q cyclicOrder triangleWitness)

theorem nonempty_finitePQSpineCertificate_of_coreRows
    (h : Nonempty (M8BoundaryCorePQSpineRows D)) :
    Nonempty (M8FinitePQSpineCertificate D) := by
  rcases h with ⟨R⟩
  exact Nonempty.intro R.toFinitePQSpineCertificate

end M8BoundaryCorePQSpineRows

/-! ## Boundary-walk extraction rows -/

/--
Boundary-walk version of the honest core rows.

The planar-boundary data is the one generated by
`OuterBoundaryWalkBookkeeping.toPlanarBoundaryData`, while each selected
boundary edge is still tied to an explicit edge of the underlying outer cycle.
-/
structure M8BoundaryWalkPQSpineRows
    {C : _root_.UDConfig n}
    {P : OuterBoundaryCore (CanonicalUDGraph C)}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
        (CanonicalUDGraph C)) where
  pIndex : M8BoundaryIndex -> Fin P.outerCycle.length
  q : M8TriangleIndex -> Fin n
  edgeIndex : M8TriangleIndex -> Fin P.outerCycle.length
  boundaryEdge_left :
    forall i : M8TriangleIndex,
      P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)) =
        (P.outerCycle.edge (edgeIndex i)).1
  boundaryEdge_right :
    forall i : M8TriangleIndex,
      P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)) =
        (P.outerCycle.edge (edgeIndex i)).2
  triangleWitness :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).CommonNeighbor
        (P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
        (P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i)

namespace M8BoundaryWalkPQSpineRows

variable {C : _root_.UDConfig n}
variable {P : OuterBoundaryCore (CanonicalUDGraph C)}
variable {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
variable {walk :
  OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
    IsDegree3 IsDegree4 IsDegree5 IsDegree6}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= walk.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
    (CanonicalUDGraph C)}

/-- The planar-boundary package generated by the boundary walk. -/
def toPlanarBoundaryData
    (_R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C) :=
  walk.toPlanarBoundaryData geometricAngleSum forced_le_geometric
    geometric_le_polygon Subpolygon subpolygonData

@[simp]
theorem toPlanarBoundaryData_core
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    R.toPlanarBoundaryData.core = P :=
  rfl

/-- The boundary label selected by the boundary-walk rows. -/
def p
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (i : M8BoundaryIndex) : Fin n :=
  P.outerCycle.vertex (R.pIndex i)

@[simp]
theorem p_eq_outerCycle
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (i : M8BoundaryIndex) :
    R.p i = R.toPlanarBoundaryData.core.outerCycle.vertex (R.pIndex i) :=
  rfl

/-- Boundary-edge adjacency derived through the existing walk certificate. -/
theorem boundaryEdge
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (R.p (m8BoundaryIndexLeft i)) (R.p (m8BoundaryIndexRight i)) := by
  have h :=
    OuterBoundaryWalkBookkeeping.edgeCertificate_unitDistanceAdj
      walk (R.edgeIndex i)
  have hedge :
      (OuterBoundaryWalkBookkeeping.edgeCertificate
        walk (R.edgeIndex i)).edge =
        P.outerCycle.edge (R.edgeIndex i) :=
    OuterBoundaryWalkBookkeeping.edgeCertificate_edge walk (R.edgeIndex i)
  simpa [p, GraphBridge.unitDistanceLocalGraph, CanonicalUDGraph, hedge,
    R.boundaryEdge_left i, R.boundaryEdge_right i] using h

/--
Build boundary-walk rows from a consecutive run on the underlying outer cycle.
The selected edge for row `i` is the edge leaving the selected left endpoint.
-/
def ofCyclicOrder
    (pIndex : M8BoundaryIndex -> Fin P.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i)) :
    M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
      geometric_le_polygon Subpolygon subpolygonData where
  pIndex := pIndex
  q := q
  edgeIndex := fun i => pIndex (m8BoundaryIndexLeft i)
  boundaryEdge_left := by
    intro i
    simp
  boundaryEdge_right := by
    intro i
    simpa using congrArg P.outerCycle.vertex (cyclicOrder i)
  triangleWitness := triangleWitness

@[simp]
theorem ofCyclicOrder_pIndex
    (pIndex : M8BoundaryIndex -> Fin P.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i))
    (i : M8BoundaryIndex) :
    (ofCyclicOrder (walk := walk) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
      pIndex q cyclicOrder triangleWitness).pIndex i = pIndex i :=
  rfl

@[simp]
theorem ofCyclicOrder_q
    (pIndex : M8BoundaryIndex -> Fin P.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i))
    (i : M8TriangleIndex) :
    (ofCyclicOrder (walk := walk) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
      pIndex q cyclicOrder triangleWitness).q i = q i :=
  rfl

@[simp]
theorem ofCyclicOrder_edgeIndex
    (pIndex : M8BoundaryIndex -> Fin P.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i))
    (i : M8TriangleIndex) :
    (ofCyclicOrder (walk := walk) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
      pIndex q cyclicOrder triangleWitness).edgeIndex i =
        pIndex (m8BoundaryIndexLeft i) :=
  rfl

/-- Forget the walk bookkeeping to honest boundary-core rows. -/
def toCoreRows
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    M8BoundaryCorePQSpineRows R.toPlanarBoundaryData where
  pIndex := R.pIndex
  q := R.q
  edgeIndex := R.edgeIndex
  boundaryEdge_left := R.boundaryEdge_left
  boundaryEdge_right := R.boundaryEdge_right
  triangleWitness := R.triangleWitness

@[simp]
theorem toCoreRows_pIndex
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (i : M8BoundaryIndex) :
    R.toCoreRows.pIndex i = R.pIndex i :=
  rfl

@[simp]
theorem toCoreRows_q
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (i : M8TriangleIndex) :
    R.toCoreRows.q i = R.q i :=
  rfl

/-- Convert boundary-walk rows into the finite `p_i/q_i` spine certificate. -/
def toFinitePQSpineCertificate
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    M8FinitePQSpineCertificate R.toPlanarBoundaryData :=
  R.toCoreRows.toFinitePQSpineCertificate

@[simp]
theorem toFinitePQSpineCertificate_pIndex
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (i : M8BoundaryIndex) :
    R.toFinitePQSpineCertificate.pIndex i = R.pIndex i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_p
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (i : M8BoundaryIndex) :
    R.toFinitePQSpineCertificate.p i = R.p i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_q
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (i : M8TriangleIndex) :
    R.toFinitePQSpineCertificate.q i = R.q i :=
  rfl

theorem toFinitePQSpineCertificate_boundaryEdge
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (R.toFinitePQSpineCertificate.p (m8BoundaryIndexLeft i))
      (R.toFinitePQSpineCertificate.p (m8BoundaryIndexRight i)) :=
  R.boundaryEdge i

theorem ofCyclicOrder_toFinitePQSpineCertificate_cyclicOrder
    (pIndex : M8BoundaryIndex -> Fin P.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i))
    (i : M8TriangleIndex) :
    ((ofCyclicOrder (walk := walk)
      (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
      pIndex q cyclicOrder triangleWitness).toFinitePQSpineCertificate).pIndex
        (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc P.outerCycle.length_pos
        (((ofCyclicOrder (walk := walk)
          (geometricAngleSum := geometricAngleSum)
          (forced_le_geometric := forced_le_geometric)
          (geometric_le_polygon := geometric_le_polygon)
          (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
          pIndex q cyclicOrder triangleWitness).toFinitePQSpineCertificate).pIndex
            (m8BoundaryIndexLeft i)) := by
  simpa using cyclicOrder i

/--
Consecutive boundary-walk rows directly inhabit the upstream boundary-arc
fields for their generated finite `p/q` spine certificate.
-/
theorem ofCyclicOrder_toFinitePQSpineCertificate_boundaryArcCertificateFields
    (pIndex : M8BoundaryIndex -> Fin P.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i)) :
    M8FinitePQSpineBoundaryArcCertificateFields
      ((ofCyclicOrder (walk := walk)
        (geometricAngleSum := geometricAngleSum)
        (forced_le_geometric := forced_le_geometric)
        (geometric_le_polygon := geometric_le_polygon)
        (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
        pIndex q cyclicOrder triangleWitness).toFinitePQSpineCertificate) :=
  M8FinitePQSpineBoundaryArcCertificateFields.ofCyclicOrder
    (K :=
      (ofCyclicOrder (walk := walk)
        (geometricAngleSum := geometricAngleSum)
        (forced_le_geometric := forced_le_geometric)
        (geometric_le_polygon := geometric_le_polygon)
        (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
        pIndex q cyclicOrder triangleWitness).toFinitePQSpineCertificate)
    (ofCyclicOrder_toFinitePQSpineCertificate_cyclicOrder
      (walk := walk) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
      pIndex q cyclicOrder triangleWitness)

theorem ofCyclicOrder_toFinitePQSpineCertificate_triangleWitness
    (pIndex : M8BoundaryIndex -> Fin P.outerCycle.length)
    (q : M8TriangleIndex -> Fin n)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (pIndex (m8BoundaryIndexLeft i)))
    (triangleWitness :
      forall i : M8TriangleIndex,
        (unitDistanceLocalGraph C).CommonNeighbor
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
          (P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i))
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      ((ofCyclicOrder (walk := walk)
        (geometricAngleSum := geometricAngleSum)
        (forced_le_geometric := forced_le_geometric)
        (geometric_le_polygon := geometric_le_polygon)
        (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
        pIndex q cyclicOrder triangleWitness).toFinitePQSpineCertificate.p
          (m8BoundaryIndexLeft i))
      ((ofCyclicOrder (walk := walk)
        (geometricAngleSum := geometricAngleSum)
        (forced_le_geometric := forced_le_geometric)
        (geometric_le_polygon := geometric_le_polygon)
        (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
        pIndex q cyclicOrder triangleWitness).toFinitePQSpineCertificate.p
          (m8BoundaryIndexRight i))
      ((ofCyclicOrder (walk := walk)
        (geometricAngleSum := geometricAngleSum)
        (forced_le_geometric := forced_le_geometric)
        (geometric_le_polygon := geometric_le_polygon)
        (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
        pIndex q cyclicOrder triangleWitness).toFinitePQSpineCertificate.q i) :=
  triangleWitness i

theorem nonempty_finitePQSpineCertificate_of_walkRows
    (h :
      Nonempty
        (M8BoundaryWalkPQSpineRows walk geometricAngleSum
          forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)) :
    Nonempty
      (M8FinitePQSpineCertificate
        (walk.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData)) := by
  rcases h with ⟨R⟩
  exact Nonempty.intro R.toFinitePQSpineCertificate

end M8BoundaryWalkPQSpineRows

/-! ## Finite frame-core fields for the generated spine -/

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}
variable {connectedNoCut : PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/--
The exact finite frame-core facts for the `M8BoundarySpine` generated from a
finite `p/q` spine certificate.

This is intentionally the raw boundary-spine payload, not the downstream
Lemma 8 package: it records adjacency from each center `q_i` to the
neighboring triangle labels `q_{i-1}, q_{i+1}` and the three no-collision
facts not already forced by boundary edges and neighboring triangle witnesses.
-/
structure M8FinitePQSpineFrameCoreFields
    (K : M8FinitePQSpineCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) : Prop where
  prev_adj :
    forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        ((K.toM8BoundarySpine connectedNoCut hmin).centerQ i)
        ((K.toM8BoundarySpine connectedNoCut hmin).prevQ i)
  next_adj :
    forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        ((K.toM8BoundarySpine connectedNoCut hmin).centerQ i)
        ((K.toM8BoundarySpine connectedNoCut hmin).nextQ i)
  left_ne_next :
    forall i : M8ExtraIndex,
      Not
        ((K.toM8BoundarySpine connectedNoCut hmin).leftP i =
          (K.toM8BoundarySpine connectedNoCut hmin).nextQ i)
  right_ne_prev :
    forall i : M8ExtraIndex,
      Not
        ((K.toM8BoundarySpine connectedNoCut hmin).rightP i =
          (K.toM8BoundarySpine connectedNoCut hmin).prevQ i)
  prev_ne_next :
    forall i : M8ExtraIndex,
      Not
        ((K.toM8BoundarySpine connectedNoCut hmin).prevQ i =
          (K.toM8BoundarySpine connectedNoCut hmin).nextQ i)

namespace M8FinitePQSpineFrameCoreFields

variable (K : M8FinitePQSpineCertificate D)

theorem prev_adj_holds
    (F : M8FinitePQSpineFrameCoreFields K connectedNoCut hmin)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      ((K.toM8BoundarySpine connectedNoCut hmin).centerQ i)
      ((K.toM8BoundarySpine connectedNoCut hmin).prevQ i) := by
  rcases F with ⟨prev_adj, _next_adj, _left_ne_next, _right_ne_prev,
    _prev_ne_next⟩
  exact prev_adj i

theorem next_adj_holds
    (F : M8FinitePQSpineFrameCoreFields K connectedNoCut hmin)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      ((K.toM8BoundarySpine connectedNoCut hmin).centerQ i)
      ((K.toM8BoundarySpine connectedNoCut hmin).nextQ i) := by
  rcases F with ⟨_prev_adj, next_adj, _left_ne_next, _right_ne_prev,
    _prev_ne_next⟩
  exact next_adj i

theorem remaining_three_noCollision
    (F : M8FinitePQSpineFrameCoreFields K connectedNoCut hmin)
    (i : M8ExtraIndex) :
    Not
      ((K.toM8BoundarySpine connectedNoCut hmin).leftP i =
        (K.toM8BoundarySpine connectedNoCut hmin).nextQ i) /\
    Not
      ((K.toM8BoundarySpine connectedNoCut hmin).rightP i =
        (K.toM8BoundarySpine connectedNoCut hmin).prevQ i) /\
    Not
      ((K.toM8BoundarySpine connectedNoCut hmin).prevQ i =
        (K.toM8BoundarySpine connectedNoCut hmin).nextQ i) := by
  rcases F with ⟨_prev_adj, _next_adj, left_ne_next, right_ne_prev,
    prev_ne_next⟩
  exact And.intro (left_ne_next i)
    (And.intro (right_ne_prev i) (prev_ne_next i))

theorem raw_prev_adj
    (F : M8FinitePQSpineFrameCoreFields K connectedNoCut hmin)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (K.q (m8TriangleIndexOfExtra i))
      (K.q (m8TriangleIndexPrevOfExtra i)) := by
  simpa [M8BoundarySpine.centerQ, M8BoundarySpine.prevQ] using
    prev_adj_holds (K := K) F i

theorem raw_next_adj
    (F : M8FinitePQSpineFrameCoreFields K connectedNoCut hmin)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (K.q (m8TriangleIndexOfExtra i))
      (K.q (m8TriangleIndexNextOfExtra i)) := by
  simpa [M8BoundarySpine.centerQ, M8BoundarySpine.nextQ] using
    next_adj_holds (K := K) F i

theorem raw_left_ne_next
    (F : M8FinitePQSpineFrameCoreFields K connectedNoCut hmin)
    (i : M8ExtraIndex) :
    Not
      (K.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
        K.q (m8TriangleIndexNextOfExtra i)) := by
  simpa [M8BoundarySpine.leftP, M8BoundarySpine.nextQ] using
    (remaining_three_noCollision (K := K) F i).1

theorem raw_right_ne_prev
    (F : M8FinitePQSpineFrameCoreFields K connectedNoCut hmin)
    (i : M8ExtraIndex) :
    Not
      (K.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
        K.q (m8TriangleIndexPrevOfExtra i)) := by
  simpa [M8BoundarySpine.rightP, M8BoundarySpine.prevQ] using
    (remaining_three_noCollision (K := K) F i).2.1

theorem raw_prev_ne_next
    (F : M8FinitePQSpineFrameCoreFields K connectedNoCut hmin)
    (i : M8ExtraIndex) :
    Not
      (K.q (m8TriangleIndexPrevOfExtra i) =
        K.q (m8TriangleIndexNextOfExtra i)) := by
  simpa [M8BoundarySpine.prevQ, M8BoundarySpine.nextQ] using
    (remaining_three_noCollision (K := K) F i).2.2

/--
Constructor from the raw finite `p_i/q_i` facts.  This is the exact
boundary-spine payload needed to inhabit `M8FinitePQSpineFrameCoreFields`:
the adjacent triangle tips `q_{i-1}, q_{i+1}` must be adjacent to the center
`q_i`, and the three remaining finite collisions must be excluded.
-/
def ofRawFinitePQFacts
    (prev_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
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
    M8FinitePQSpineFrameCoreFields K connectedNoCut hmin where
  prev_adj := by
    intro i
    simpa [M8BoundarySpine.centerQ, M8BoundarySpine.prevQ] using prev_adj i
  next_adj := by
    intro i
    simpa [M8BoundarySpine.centerQ, M8BoundarySpine.nextQ] using next_adj i
  left_ne_next := by
    intro i
    simpa [M8BoundarySpine.leftP, M8BoundarySpine.nextQ] using
      left_ne_next i
  right_ne_prev := by
    intro i
    simpa [M8BoundarySpine.rightP, M8BoundarySpine.prevQ] using
      right_ne_prev i
  prev_ne_next := by
    intro i
    simpa [M8BoundarySpine.prevQ, M8BoundarySpine.nextQ] using
      prev_ne_next i

theorem rawFinitePQFacts_of_fields
    (F : M8FinitePQSpineFrameCoreFields K connectedNoCut hmin) :
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        (K.q (m8TriangleIndexOfExtra i))
        (K.q (m8TriangleIndexPrevOfExtra i))) /\
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
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
          K.q (m8TriangleIndexNextOfExtra i))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact raw_prev_adj (K := K) F
  · exact raw_next_adj (K := K) F
  · exact raw_left_ne_next (K := K) F
  · exact raw_right_ne_prev (K := K) F
  · exact raw_prev_ne_next (K := K) F

theorem fields_iff_rawFinitePQFacts :
    M8FinitePQSpineFrameCoreFields K connectedNoCut hmin <->
      (forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexPrevOfExtra i))) /\
      (forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
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
            K.q (m8TriangleIndexNextOfExtra i))) := by
  constructor
  · intro F
    exact rawFinitePQFacts_of_fields (K := K) F
  · intro h
    exact ofRawFinitePQFacts (K := K) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

end M8FinitePQSpineFrameCoreFields

/-! ## Raw finite `p/q` frame-core facts -/

/-- Named raw finite `p_i/q_i` frame-core facts.

This is the import-safe source shape shared by W16-style finite-walk
construction and generated-order consumers.  It deliberately mentions only
the finite labels in `K`, not any downstream Lemma 8 package.
-/
structure M8FinitePQSpineRawFrameCoreFacts
    (K : M8FinitePQSpineCertificate D) : Prop where
  prev_adj :
    forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        (K.q (m8TriangleIndexOfExtra i))
        (K.q (m8TriangleIndexPrevOfExtra i))
  next_adj :
    forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        (K.q (m8TriangleIndexOfExtra i))
        (K.q (m8TriangleIndexNextOfExtra i))
  left_ne_next :
    forall i : M8ExtraIndex,
      Not
        (K.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
          K.q (m8TriangleIndexNextOfExtra i))
  right_ne_prev :
    forall i : M8ExtraIndex,
      Not
        (K.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
          K.q (m8TriangleIndexPrevOfExtra i))
  prev_ne_next :
    forall i : M8ExtraIndex,
      Not
        (K.q (m8TriangleIndexPrevOfExtra i) =
          K.q (m8TriangleIndexNextOfExtra i))

namespace M8FinitePQSpineRawFrameCoreFacts

variable {K : M8FinitePQSpineCertificate D}

/-- Turn named raw facts into the existing finite frame-core field package. -/
def toFrameCoreFields
    (R : M8FinitePQSpineRawFrameCoreFacts K) :
    M8FinitePQSpineFrameCoreFields K connectedNoCut hmin :=
  M8FinitePQSpineFrameCoreFields.ofRawFinitePQFacts
    (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
    R.prev_adj R.next_adj R.left_ne_next R.right_ne_prev R.prev_ne_next

/-- Extract named raw facts from the existing finite frame-core field package. -/
def ofFrameCoreFields
    (F : M8FinitePQSpineFrameCoreFields K connectedNoCut hmin) :
    M8FinitePQSpineRawFrameCoreFacts K where
  prev_adj := M8FinitePQSpineFrameCoreFields.raw_prev_adj (K := K) F
  next_adj := M8FinitePQSpineFrameCoreFields.raw_next_adj (K := K) F
  left_ne_next :=
    M8FinitePQSpineFrameCoreFields.raw_left_ne_next (K := K) F
  right_ne_prev :=
    M8FinitePQSpineFrameCoreFields.raw_right_ne_prev (K := K) F
  prev_ne_next :=
    M8FinitePQSpineFrameCoreFields.raw_prev_ne_next (K := K) F

/-- Existing frame-core fields are equivalent to the named raw fact package. -/
theorem frameCoreFields_iff :
    M8FinitePQSpineFrameCoreFields K connectedNoCut hmin <->
      M8FinitePQSpineRawFrameCoreFacts K := by
  constructor
  case mp =>
    exact ofFrameCoreFields
  case mpr =>
    intro R
    exact R.toFrameCoreFields

/-- Project named raw facts to the conjunction form used by older bridges. -/
theorem conjunction
    (R : M8FinitePQSpineRawFrameCoreFacts K) :
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        (K.q (m8TriangleIndexOfExtra i))
        (K.q (m8TriangleIndexPrevOfExtra i))) /\
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
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
          K.q (m8TriangleIndexNextOfExtra i))) :=
  And.intro R.prev_adj
    (And.intro R.next_adj
      (And.intro R.left_ne_next
        (And.intro R.right_ne_prev R.prev_ne_next)))

/-- Constructor from the five row-wise raw finite frame-core fact families. -/
def ofRows
    (prev_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
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
    M8FinitePQSpineRawFrameCoreFacts K where
  prev_adj := prev_adj
  next_adj := next_adj
  left_ne_next := left_ne_next
  right_ne_prev := right_ne_prev
  prev_ne_next := prev_ne_next

end M8FinitePQSpineRawFrameCoreFacts

/-! ## Boundary-arc rows with finite frame-core fields -/

/--
Boundary-arc cyclic rows together with the frame-core payload for the same
finite spine certificate.

This is the upstream counterpart of the downstream W16
boundary-arc/frame-core route: the boundary-arc part records the concrete
successor run, while the frame-core part records the finite `q_i` adjacency
and no-collision facts used by generated-order consumers.
-/
structure M8FinitePQSpineBoundaryArcFrameCoreFields
    (K : M8FinitePQSpineCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) : Prop where
  boundaryArcFields :
    M8FinitePQSpineBoundaryArcCertificateFields K
  frameCoreFields :
    M8FinitePQSpineFrameCoreFields K connectedNoCut hmin

namespace M8FinitePQSpineBoundaryArcFrameCoreFields

variable {K : M8FinitePQSpineCertificate D}

/-- Constructor from separately proved boundary-arc and frame-core fields. -/
def ofBoundaryArcCertificateFieldsAndFrameCoreFields
    (boundaryArcFields :
      M8FinitePQSpineBoundaryArcCertificateFields K)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields K connectedNoCut hmin) :
    M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin where
  boundaryArcFields := boundaryArcFields
  frameCoreFields := frameCoreFields

/-- Constructor from cyclic-successor rows and frame-core fields. -/
def ofCyclicOrderAndFrameCoreFields
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields K connectedNoCut hmin) :
    M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin :=
  ofBoundaryArcCertificateFieldsAndFrameCoreFields
    (M8FinitePQSpineBoundaryArcCertificateFields.ofCyclicOrder cyclicOrder)
    frameCoreFields

/-- Constructor from cyclic-successor rows and raw finite frame-core facts. -/
def ofCyclicOrderAndRawFinitePQFacts
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (prev_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
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
    M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin :=
  ofCyclicOrderAndFrameCoreFields cyclicOrder
    (M8FinitePQSpineFrameCoreFields.ofRawFinitePQFacts
      (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
      prev_adj next_adj left_ne_next right_ne_prev prev_ne_next)

/-- Projection of the boundary-arc cyclic-successor equality. -/
theorem cyclicOrder_holds
    (F : M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin)
    (i : M8TriangleIndex) :
    K.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (m8BoundaryIndexLeft i)) :=
  F.boundaryArcFields.cyclicOrder_holds i

/-- Projection of the finite frame-core fields. -/
theorem frameCoreFields_holds
    (F : M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin) :
    M8FinitePQSpineFrameCoreFields K connectedNoCut hmin :=
  F.frameCoreFields

/-- Project the bundled route back to raw finite `p/q` frame-core facts. -/
theorem rawFinitePQFacts_of_fields
    (F : M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin) :
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        (K.q (m8TriangleIndexOfExtra i))
        (K.q (m8TriangleIndexPrevOfExtra i))) /\
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
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
          K.q (m8TriangleIndexNextOfExtra i))) :=
  M8FinitePQSpineFrameCoreFields.rawFinitePQFacts_of_fields
    (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
    F.frameCoreFields_holds

/-- The bundled route is exactly boundary-arc rows plus frame-core fields. -/
theorem fields_iff_boundaryArcCertificateFields_and_frameCoreFields :
    M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin <->
      M8FinitePQSpineBoundaryArcCertificateFields K /\
        M8FinitePQSpineFrameCoreFields K connectedNoCut hmin := by
  constructor
  case mp =>
    intro F
    exact And.intro F.boundaryArcFields F.frameCoreFields
  case mpr =>
    intro h
    exact
      ofBoundaryArcCertificateFieldsAndFrameCoreFields h.1 h.2

/--
The bundled upstream boundary-arc/frame-core package is exactly the cyclic
successor row family together with the raw finite `p/q` frame-core facts.
-/
theorem fields_iff_cyclicOrder_and_rawFinitePQFacts :
    M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin <->
      (forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i))) /\
      (forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexPrevOfExtra i))) /\
      (forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
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
            K.q (m8TriangleIndexNextOfExtra i))) := by
  constructor
  case mp =>
    intro F
    exact And.intro (cyclicOrder_holds F) (rawFinitePQFacts_of_fields F)
  case mpr =>
    intro h
    exact
      ofCyclicOrderAndRawFinitePQFacts
        (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

end M8FinitePQSpineBoundaryArcFrameCoreFields

/-! ## Explicit finite-spine source package -/

/-- Direct source package for the finite `p/q` frame core.

The triangle-run part is expressed through the named finite-spine projections
`p0`, ..., `p13`, `cyclicOrder0`, ..., `cyclicOrder12`, and the corresponding
derived triangular-edge rows.  The raw part is exactly the finite `q`
adjacency/no-collision payload required later by W16 and generated-order
consumers.
-/
structure M8FinitePQSpineExplicitFrameCoreSource
    (K : M8FinitePQSpineCertificate D)
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) : Prop where
  triangleRunRows :
    M8FinitePQSpineCertificate.ExplicitTriangleRunRows K
  rawFacts :
    M8FinitePQSpineRawFrameCoreFacts K

namespace M8FinitePQSpineExplicitFrameCoreSource

variable {K : M8FinitePQSpineCertificate D}

/-- Constructor from named cyclic rows and named raw frame-core facts. -/
def ofCyclicOrderRowsAndRawFacts
    (cyclicOrderRows :
      M8FinitePQSpineCertificate.ExplicitCyclicOrderRows K)
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin where
  triangleRunRows :=
    M8FinitePQSpineCertificate.ExplicitTriangleRunRows.ofCyclicOrderRows
      cyclicOrderRows
  rawFacts := rawFacts

/-- Constructor from named cyclic rows and the existing frame-core fields. -/
def ofCyclicOrderRowsAndFrameCoreFields
    (cyclicOrderRows :
      M8FinitePQSpineCertificate.ExplicitCyclicOrderRows K)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields K connectedNoCut hmin) :
    M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin :=
  ofCyclicOrderRowsAndRawFacts
    (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
    cyclicOrderRows
    (M8FinitePQSpineRawFrameCoreFacts.ofFrameCoreFields
      (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
      frameCoreFields)

/-- Row-wise cyclic order from the explicit triangle-run rows. -/
theorem cyclicOrder
    (S : M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin) :
    forall i : M8TriangleIndex,
      K.pIndex (m8BoundaryIndexRight i) =
        PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
          (K.pIndex (m8BoundaryIndexLeft i)) :=
  S.triangleRunRows.cyclicOrder

/-- The raw finite `p/q` facts stored by the source package. -/
theorem rawFacts_holds
    (S : M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin) :
    M8FinitePQSpineRawFrameCoreFacts K :=
  S.rawFacts

/-- Existing frame-core fields generated from the stored raw facts. -/
def frameCoreFields
    (S : M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin) :
    M8FinitePQSpineFrameCoreFields K connectedNoCut hmin :=
  S.rawFacts.toFrameCoreFields

/-- Boundary-arc fields generated from the stored explicit triangle-run rows. -/
def boundaryArcCertificateFields
    (S : M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin) :
    M8FinitePQSpineBoundaryArcCertificateFields K :=
  S.triangleRunRows.boundaryArcCertificateFields

/-- The combined upstream boundary-arc/frame-core payload for W16 consumers. -/
def boundaryArcFrameCoreFields
    (S : M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin) :
    M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin :=
  M8FinitePQSpineBoundaryArcFrameCoreFields.ofBoundaryArcCertificateFieldsAndFrameCoreFields
    S.boundaryArcCertificateFields S.frameCoreFields

/-- Project the source package to the conjunction form of raw finite facts. -/
theorem rawFinitePQFacts
    (S : M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin) :
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        (K.q (m8TriangleIndexOfExtra i))
        (K.q (m8TriangleIndexPrevOfExtra i))) /\
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
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
          K.q (m8TriangleIndexNextOfExtra i))) :=
  S.rawFacts.conjunction

/-- The explicit finite-spine source is exactly named cyclic rows plus raw
finite frame-core facts. -/
theorem source_iff_cyclicOrderRows_and_rawFacts :
    M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin <->
      M8FinitePQSpineCertificate.ExplicitCyclicOrderRows K /\
        M8FinitePQSpineRawFrameCoreFacts K := by
  constructor
  case mp =>
    intro S
    exact And.intro S.triangleRunRows.cyclicOrderRows S.rawFacts
  case mpr =>
    intro h
    exact ofCyclicOrderRowsAndRawFacts
      (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
      h.1 h.2

/-- Project the bundled explicit source to the W16-facing subtype: the same
finite spine together with named cyclic-order rows and named raw facts. -/
def explicitCyclicOrderRowsAndRawFacts
    (S : M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin) :
    { K : M8FinitePQSpineCertificate D //
      M8FinitePQSpineCertificate.ExplicitCyclicOrderRows K /\
      M8FinitePQSpineRawFrameCoreFacts K } :=
  Subtype.mk K
    (And.intro S.triangleRunRows.cyclicOrderRows S.rawFacts)

@[simp]
theorem explicitCyclicOrderRowsAndRawFacts_val
    (S : M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin) :
    S.explicitCyclicOrderRowsAndRawFacts.1 = K :=
  rfl

/-- Construct the explicit source package from the sharp row-wise inputs:
cyclic successor rows plus the five raw finite frame-core fact families. -/
def ofCyclicOrderAndRawFactRows
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (prev_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (K.q (m8TriangleIndexOfExtra i))
          (K.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
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
    M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin :=
  ofCyclicOrderRowsAndRawFacts
    (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
    (M8FinitePQSpineCertificate.ExplicitCyclicOrderRows.ofCyclicOrder
      cyclicOrder)
    (M8FinitePQSpineRawFrameCoreFacts.ofRows
      (K := K) prev_adj next_adj left_ne_next right_ne_prev prev_ne_next)

end M8FinitePQSpineExplicitFrameCoreSource

namespace M8FinitePQSpineCertificate

variable (K : M8FinitePQSpineCertificate D)

/-- Package cyclic-successor rows and frame-core fields for W16 consumers. -/
def toBoundaryArcFrameCoreFields
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields K connectedNoCut hmin) :
    M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin :=
  M8FinitePQSpineBoundaryArcFrameCoreFields.ofCyclicOrderAndFrameCoreFields
    cyclicOrder frameCoreFields

theorem toBoundaryArcFrameCoreFields_cyclicOrder
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields K connectedNoCut hmin)
    (i : M8TriangleIndex) :
    K.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
        (K.pIndex (m8BoundaryIndexLeft i)) :=
  (K.toBoundaryArcFrameCoreFields cyclicOrder frameCoreFields).cyclicOrder_holds i

theorem toBoundaryArcFrameCoreFields_frameCoreFields
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields K connectedNoCut hmin) :
    (K.toBoundaryArcFrameCoreFields
      cyclicOrder frameCoreFields).frameCoreFields_holds =
        frameCoreFields :=
  rfl

/-- Package named explicit cyclic rows and raw finite frame-core facts. -/
def toExplicitFrameCoreSource
    (cyclicOrderRows : ExplicitCyclicOrderRows K)
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin :=
  M8FinitePQSpineExplicitFrameCoreSource.ofCyclicOrderRowsAndRawFacts
    (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
    cyclicOrderRows rawFacts

/-- Package row-wise cyclic successor rows as the named explicit row source. -/
def toExplicitCyclicOrderRows
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i))) :
    ExplicitCyclicOrderRows K :=
  ExplicitCyclicOrderRows.ofCyclicOrder cyclicOrder

/-- Package row-wise cyclic successor rows and raw finite frame-core facts in
the exact subtype shape consumed by W16's explicit source theorem. -/
def toExplicitCyclicOrderRowsAndRawFacts
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    { K : M8FinitePQSpineCertificate D //
      ExplicitCyclicOrderRows K /\ M8FinitePQSpineRawFrameCoreFacts K } :=
  Subtype.mk K
    (And.intro (K.toExplicitCyclicOrderRows cyclicOrder) rawFacts)

@[simp]
theorem toExplicitCyclicOrderRowsAndRawFacts_val
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    (K.toExplicitCyclicOrderRowsAndRawFacts cyclicOrder rawFacts).1 = K :=
  rfl

/-- Boundary-arc/frame-core fields reduce to explicit cyclic rows plus raw
facts for the same finite spine. -/
def toExplicitCyclicOrderRowsAndRawFactsOfBoundaryArcFrameCoreFields
    (fields :
      M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin) :
    { K : M8FinitePQSpineCertificate D //
      ExplicitCyclicOrderRows K /\ M8FinitePQSpineRawFrameCoreFacts K } :=
  K.toExplicitCyclicOrderRowsAndRawFacts
    (M8FinitePQSpineBoundaryArcFrameCoreFields.cyclicOrder_holds fields)
    (M8FinitePQSpineRawFrameCoreFacts.ofFrameCoreFields
      (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
      fields.frameCoreFields_holds)

@[simp]
theorem toExplicitCyclicOrderRowsAndRawFactsOfBoundaryArcFrameCoreFields_val
    (fields :
      M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin) :
    (K.toExplicitCyclicOrderRowsAndRawFactsOfBoundaryArcFrameCoreFields
      fields).1 = K :=
  rfl

/-- Package row-wise cyclic successor rows and raw finite frame-core facts. -/
def toExplicitFrameCoreSourceOfCyclicOrderAndRawFacts
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin :=
  K.toExplicitFrameCoreSource
    (connectedNoCut := connectedNoCut) (hmin := hmin)
    (K.toExplicitCyclicOrderRows cyclicOrder) rawFacts

/-- Package named explicit cyclic rows and existing finite frame-core fields. -/
def toExplicitFrameCoreSourceOfFrameCoreFields
    (cyclicOrderRows : ExplicitCyclicOrderRows K)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields K connectedNoCut hmin) :
    M8FinitePQSpineExplicitFrameCoreSource K connectedNoCut hmin :=
  M8FinitePQSpineExplicitFrameCoreSource.ofCyclicOrderRowsAndFrameCoreFields
    (K := K) (connectedNoCut := connectedNoCut) (hmin := hmin)
    cyclicOrderRows frameCoreFields

/-- Named explicit cyclic rows plus raw facts give the bundled W16-facing
boundary-arc/frame-core fields. -/
def toBoundaryArcFrameCoreFieldsOfExplicitRawFacts
    (cyclicOrderRows : ExplicitCyclicOrderRows K)
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin :=
  (K.toExplicitFrameCoreSource
    (connectedNoCut := connectedNoCut) (hmin := hmin)
    cyclicOrderRows rawFacts).boundaryArcFrameCoreFields

/-- Row-wise cyclic successor rows plus raw facts give the explicit source
package consumed by generated-order and W16-facing finite-spine routes. -/
def toBoundaryArcFrameCoreFieldsOfCyclicOrderAndRawFacts
    (cyclicOrder :
      forall i : M8TriangleIndex,
        K.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (K.pIndex (m8BoundaryIndexLeft i)))
    (rawFacts : M8FinitePQSpineRawFrameCoreFacts K) :
    M8FinitePQSpineBoundaryArcFrameCoreFields K connectedNoCut hmin :=
  (K.toExplicitFrameCoreSourceOfCyclicOrderAndRawFacts
    (connectedNoCut := connectedNoCut) (hmin := hmin)
    cyclicOrder rawFacts).boundaryArcFrameCoreFields

end M8FinitePQSpineCertificate

namespace M8BoundaryCorePQSpineRows

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}
variable {connectedNoCut : PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/--
Construct the generated-order frame-core payload directly from raw facts
written in honest boundary-core row notation.
-/
theorem frameCoreFieldsOfRawFacts
    (R : M8BoundaryCorePQSpineRows D)
    (prev_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (R.q (m8TriangleIndexOfExtra i))
          (R.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (R.q (m8TriangleIndexOfExtra i))
          (R.q (m8TriangleIndexNextOfExtra i)))
    (left_ne_next :
      forall i : M8ExtraIndex,
        Not
          (R.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
            R.q (m8TriangleIndexNextOfExtra i)))
    (right_ne_prev :
      forall i : M8ExtraIndex,
        Not
          (R.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
            R.q (m8TriangleIndexPrevOfExtra i)))
    (prev_ne_next :
      forall i : M8ExtraIndex,
        Not
          (R.q (m8TriangleIndexPrevOfExtra i) =
            R.q (m8TriangleIndexNextOfExtra i))) :
    M8FinitePQSpineFrameCoreFields
      R.toFinitePQSpineCertificate connectedNoCut hmin := by
  refine
    M8FinitePQSpineFrameCoreFields.ofRawFinitePQFacts
      (K := R.toFinitePQSpineCertificate)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      ?_ ?_ ?_ ?_ ?_
  · intro i
    simpa using prev_adj i
  · intro i
    simpa using next_adj i
  · intro i
    simpa using left_ne_next i
  · intro i
    simpa using right_ne_prev i
  · intro i
    simpa using prev_ne_next i

/-- Construct boundary-arc fields from cyclic-order rows in core-row notation. -/
theorem boundaryArcCertificateFieldsOfCyclicOrder
    (R : M8BoundaryCorePQSpineRows D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        R.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (R.pIndex (m8BoundaryIndexLeft i))) :
    M8FinitePQSpineBoundaryArcCertificateFields R.toFinitePQSpineCertificate := by
  refine
    M8FinitePQSpineBoundaryArcCertificateFields.ofCyclicOrder ?_
  intro i
  simpa using cyclicOrder i

/--
Construct the bundled boundary-arc/frame-core payload directly from raw facts
written in honest boundary-core row notation.
-/
theorem boundaryArcFrameCoreFieldsOfRawFacts
    (R : M8BoundaryCorePQSpineRows D)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        R.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc D.core.outerCycle.length_pos
            (R.pIndex (m8BoundaryIndexLeft i)))
    (prev_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (R.q (m8TriangleIndexOfExtra i))
          (R.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (R.q (m8TriangleIndexOfExtra i))
          (R.q (m8TriangleIndexNextOfExtra i)))
    (left_ne_next :
      forall i : M8ExtraIndex,
        Not
          (R.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
            R.q (m8TriangleIndexNextOfExtra i)))
    (right_ne_prev :
      forall i : M8ExtraIndex,
        Not
          (R.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
            R.q (m8TriangleIndexPrevOfExtra i)))
    (prev_ne_next :
      forall i : M8ExtraIndex,
        Not
          (R.q (m8TriangleIndexPrevOfExtra i) =
            R.q (m8TriangleIndexNextOfExtra i))) :
    M8FinitePQSpineBoundaryArcFrameCoreFields
      R.toFinitePQSpineCertificate connectedNoCut hmin :=
  M8FinitePQSpineBoundaryArcFrameCoreFields.ofBoundaryArcCertificateFieldsAndFrameCoreFields
      (boundaryArcCertificateFieldsOfCyclicOrder
        (D := D) R cyclicOrder)
      (frameCoreFieldsOfRawFacts
        (D := D) (connectedNoCut := connectedNoCut) (hmin := hmin)
        R prev_adj next_adj left_ne_next right_ne_prev prev_ne_next)

/-- Project finite frame-core fields back to raw boundary-core row facts. -/
theorem rawFactsOfFrameCoreFields
    (R : M8BoundaryCorePQSpineRows D)
    (F :
      M8FinitePQSpineFrameCoreFields
        R.toFinitePQSpineCertificate connectedNoCut hmin) :
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        (R.q (m8TriangleIndexOfExtra i))
        (R.q (m8TriangleIndexPrevOfExtra i))) /\
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        (R.q (m8TriangleIndexOfExtra i))
        (R.q (m8TriangleIndexNextOfExtra i))) /\
    (forall i : M8ExtraIndex,
      Not
        (R.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
          R.q (m8TriangleIndexNextOfExtra i))) /\
    (forall i : M8ExtraIndex,
      Not
        (R.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
          R.q (m8TriangleIndexPrevOfExtra i))) /\
    (forall i : M8ExtraIndex,
      Not
        (R.q (m8TriangleIndexPrevOfExtra i) =
          R.q (m8TriangleIndexNextOfExtra i))) := by
  simpa using
    (M8FinitePQSpineFrameCoreFields.rawFinitePQFacts_of_fields
      (K := R.toFinitePQSpineCertificate)
      (connectedNoCut := connectedNoCut) (hmin := hmin) F)

end M8BoundaryCorePQSpineRows

namespace M8BoundaryWalkPQSpineRows

variable {C : _root_.UDConfig n}
variable {P : OuterBoundaryCore (CanonicalUDGraph C)}
variable {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
variable {walk :
  OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
    IsDegree3 IsDegree4 IsDegree5 IsDegree6}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= walk.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
    (CanonicalUDGraph C)}
variable {connectedNoCut : PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/--
Construct the generated-order frame-core payload directly from raw facts
written in boundary-walk row notation.
-/
theorem frameCoreFieldsOfRawFacts
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (prev_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (R.q (m8TriangleIndexOfExtra i))
          (R.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (R.q (m8TriangleIndexOfExtra i))
          (R.q (m8TriangleIndexNextOfExtra i)))
    (left_ne_next :
      forall i : M8ExtraIndex,
        Not
          (R.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
            R.q (m8TriangleIndexNextOfExtra i)))
    (right_ne_prev :
      forall i : M8ExtraIndex,
        Not
          (R.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
            R.q (m8TriangleIndexPrevOfExtra i)))
    (prev_ne_next :
      forall i : M8ExtraIndex,
        Not
          (R.q (m8TriangleIndexPrevOfExtra i) =
            R.q (m8TriangleIndexNextOfExtra i))) :
    M8FinitePQSpineFrameCoreFields
      R.toFinitePQSpineCertificate connectedNoCut hmin := by
  refine
    M8FinitePQSpineFrameCoreFields.ofRawFinitePQFacts
      (K := R.toFinitePQSpineCertificate)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      ?_ ?_ ?_ ?_ ?_
  · intro i
    simpa using prev_adj i
  · intro i
    simpa using next_adj i
  · intro i
    simpa using left_ne_next i
  · intro i
    simpa using right_ne_prev i
  · intro i
    simpa using prev_ne_next i

/-- Construct boundary-arc fields from cyclic-order rows in walk-row notation. -/
theorem boundaryArcCertificateFieldsOfCyclicOrder
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        R.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (R.pIndex (m8BoundaryIndexLeft i))) :
    M8FinitePQSpineBoundaryArcCertificateFields R.toFinitePQSpineCertificate := by
  refine
    M8FinitePQSpineBoundaryArcCertificateFields.ofCyclicOrder ?_
  intro i
  simpa using cyclicOrder i

/--
Construct the bundled boundary-arc/frame-core payload directly from raw facts
written in boundary-walk row notation.
-/
theorem boundaryArcFrameCoreFieldsOfRawFacts
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (cyclicOrder :
      forall i : M8TriangleIndex,
        R.pIndex (m8BoundaryIndexRight i) =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (R.pIndex (m8BoundaryIndexLeft i)))
    (prev_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (R.q (m8TriangleIndexOfExtra i))
          (R.q (m8TriangleIndexPrevOfExtra i)))
    (next_adj :
      forall i : M8ExtraIndex,
        (unitDistanceLocalGraph C).Adj
          (R.q (m8TriangleIndexOfExtra i))
          (R.q (m8TriangleIndexNextOfExtra i)))
    (left_ne_next :
      forall i : M8ExtraIndex,
        Not
          (R.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
            R.q (m8TriangleIndexNextOfExtra i)))
    (right_ne_prev :
      forall i : M8ExtraIndex,
        Not
          (R.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
            R.q (m8TriangleIndexPrevOfExtra i)))
    (prev_ne_next :
      forall i : M8ExtraIndex,
        Not
          (R.q (m8TriangleIndexPrevOfExtra i) =
            R.q (m8TriangleIndexNextOfExtra i))) :
    M8FinitePQSpineBoundaryArcFrameCoreFields
      R.toFinitePQSpineCertificate connectedNoCut hmin :=
  M8FinitePQSpineBoundaryArcFrameCoreFields.ofBoundaryArcCertificateFieldsAndFrameCoreFields
      (boundaryArcCertificateFieldsOfCyclicOrder
        (walk := walk) (geometricAngleSum := geometricAngleSum)
        (forced_le_geometric := forced_le_geometric)
        (geometric_le_polygon := geometric_le_polygon)
        (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
        R cyclicOrder)
      (frameCoreFieldsOfRawFacts
        (walk := walk) (geometricAngleSum := geometricAngleSum)
        (forced_le_geometric := forced_le_geometric)
        (geometric_le_polygon := geometric_le_polygon)
        (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
        (connectedNoCut := connectedNoCut) (hmin := hmin)
        R prev_adj next_adj left_ne_next right_ne_prev prev_ne_next)

/-- Project finite frame-core fields back to raw boundary-walk row facts. -/
theorem rawFactsOfFrameCoreFields
    (R :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    (F :
      M8FinitePQSpineFrameCoreFields
        R.toFinitePQSpineCertificate connectedNoCut hmin) :
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        (R.q (m8TriangleIndexOfExtra i))
        (R.q (m8TriangleIndexPrevOfExtra i))) /\
    (forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj
        (R.q (m8TriangleIndexOfExtra i))
        (R.q (m8TriangleIndexNextOfExtra i))) /\
    (forall i : M8ExtraIndex,
      Not
        (R.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) =
          R.q (m8TriangleIndexNextOfExtra i))) /\
    (forall i : M8ExtraIndex,
      Not
        (R.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) =
          R.q (m8TriangleIndexPrevOfExtra i))) /\
    (forall i : M8ExtraIndex,
      Not
        (R.q (m8TriangleIndexPrevOfExtra i) =
          R.q (m8TriangleIndexNextOfExtra i))) := by
  simpa using
    (M8FinitePQSpineFrameCoreFields.rawFinitePQFacts_of_fields
      (K := R.toFinitePQSpineCertificate)
      (connectedNoCut := connectedNoCut) (hmin := hmin) F)

end M8BoundaryWalkPQSpineRows

end

end BoundarySpineFiniteCertificate
end Swanepoel
end ErdosProblems1066
