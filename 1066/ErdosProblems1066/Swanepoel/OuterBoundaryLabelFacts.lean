import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate
import ErdosProblems1066.Swanepoel.MinimalFailureW8RowAssembly

set_option autoImplicit false

/-!
# Outer-boundary label facts

This module collects the exact boundary-label projections used by the `m = 8`
outer-boundary route.  The facts here do not construct the geometric input:
they expose the labels and witnesses already present in the outer-boundary
core, finite `p/q` spine certificate, and explicit Lemma 8 data.
-/

namespace ErdosProblems1066
namespace Swanepoel

open BoundarySpineFiniteCertificate
open BoundaryFaceCountingToM8
open CutVertexClosure
open GraphBridge
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalFailureW8RowAssembly
open MinimalGraphFacts

universe u

noncomputable section

namespace OuterBoundaryLabelFacts

variable {n : Nat}

/-! ## Core outer-boundary projections -/

namespace OuterBoundaryCore

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

theorem outerCycle_vertex_onBoundary
    (P : Swanepoel.OuterBoundaryCore G)
    (k : Fin P.outerCycle.length) :
    P.outerEnclosure.onBoundary (P.outerCycle.vertex k) := by
  simpa [Swanepoel.OuterBoundaryCore.outerCycle] using
    P.boundary_vertex_onBoundary k

theorem outerCycle_successor_edge
    (P : Swanepoel.OuterBoundaryCore G)
    (k : Fin P.outerCycle.length) :
    GraphBridge.UnitDistanceAdj G.config (P.outerCycle.vertex k)
      (P.outerCycle.vertex
        (PlanarInterface.cyclicSucc P.outerCycle.length_pos k)) :=
  P.outerCycle_adjacent_unitDistanceAdj k

theorem outerCycle_successor_dist_eq_one
    (P : Swanepoel.OuterBoundaryCore G)
    (k : Fin P.outerCycle.length) :
    Geometry.Distance.eucDist (P.outerCycle.point k)
      (P.outerCycle.point
        (PlanarInterface.cyclicSucc P.outerCycle.length_pos k)) = 1 :=
  P.outerCycle_edge_geometry_dist_eq_one k

end OuterBoundaryCore

/-! ## Boundary spine label and witness projections -/

namespace M8BoundarySpine

variable {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}

theorem p_onOuterBoundary
    (S : M8BoundarySpine H) (i : M8BoundaryIndex) :
    H.outerBoundary.outerEnclosure.onBoundary (S.p i) :=
  S.p_onBoundary i

theorem boundaryEdge
    (S : M8BoundarySpine H) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (S.p (m8BoundaryIndexLeft i)) (S.p (m8BoundaryIndexRight i)) :=
  S.boundaryEdge i

theorem triangleWitness
    (S : M8BoundarySpine H) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (S.p (m8BoundaryIndexLeft i)) (S.p (m8BoundaryIndexRight i)) (S.q i) :=
  S.triangleWitness i

@[simp]
theorem leftP_eq_p
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    S.leftP i = S.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) :=
  rfl

@[simp]
theorem rightP_eq_p
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    S.rightP i = S.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) :=
  rfl

@[simp]
theorem centerQ_eq_q
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    S.centerQ i = S.q (m8TriangleIndexOfExtra i) :=
  rfl

@[simp]
theorem prevQ_eq_q
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    S.prevQ i = S.q (m8TriangleIndexPrevOfExtra i) :=
  rfl

@[simp]
theorem nextQ_eq_q
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    S.nextQ i = S.q (m8TriangleIndexNextOfExtra i) :=
  rfl

theorem centerQ_adj_leftP
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (S.leftP i) :=
  S.centerQ_adj_leftP i

theorem centerQ_adj_rightP
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (S.rightP i) :=
  S.centerQ_adj_rightP i

end M8BoundarySpine

/-! ## Explicit Lemma 8 extra-neighbor projections -/

namespace M8Lemma8Combinatorics

variable {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

theorem r_neighbor
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (E.r i) :=
  E.r_neighbor i

theorem s_neighbor
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (E.s i) :=
  E.s_neighbor i

theorem r_not_forbidden
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (E.r i)) :=
  E.r_not_forbidden i

theorem s_not_forbidden
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (E.s i)) :=
  E.s_not_forbidden i

theorem r_ne_s
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.r i = E.s i) :=
  E.r_ne_s i

theorem extraNeighborWitness
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    E.extraNeighborWitness i :=
  E.extraNeighborWitness_holds i

theorem named_of_extra_neighbor
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    x = E.r i \/ x = E.s i :=
  E.named_of_extra_neighbor hadj hnot

end M8Lemma8Combinatorics

/-! ## Boundary-derived label package projections -/

namespace M8LabelsFromBoundaryData

variable {C : _root_.UDConfig n}

@[simp]
theorem labels_p_projection
    (D : M8LabelsFromBoundaryData C) (i : M8BoundaryIndex) :
    D.labels.p i = D.spine.p i :=
  rfl

@[simp]
theorem labels_q_projection
    (D : M8LabelsFromBoundaryData C) (i : M8TriangleIndex) :
    D.labels.q i = D.spine.q i :=
  rfl

@[simp]
theorem labels_r_projection
    (D : M8LabelsFromBoundaryData C) (i : M8ExtraIndex) :
    D.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem labels_s_projection
    (D : M8LabelsFromBoundaryData C) (i : M8ExtraIndex) :
    D.labels.s i = D.lemma8.s i :=
  rfl

theorem p_onOuterBoundary
    (D : M8LabelsFromBoundaryData C) (i : M8BoundaryIndex) :
    D.context.outerBoundary.outerEnclosure.onBoundary (D.labels.p i) := by
  simpa using D.spine.p_onBoundary i

theorem boundaryEdge
    (D : M8LabelsFromBoundaryData C) (i : M8TriangleIndex) :
    D.predicates.boundaryEdge i :=
  D.boundaryEdge_holds i

theorem boundaryEdge_raw
    (D : M8LabelsFromBoundaryData C) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.labels.p (m8BoundaryIndexLeft i))
      (D.labels.p (m8BoundaryIndexRight i)) := by
  simpa using D.spine.boundaryEdge i

theorem triangleWitness
    (D : M8LabelsFromBoundaryData C) (i : M8TriangleIndex) :
    D.predicates.triangleWitness i :=
  D.triangleWitness_holds i

theorem triangleWitness_raw
    (D : M8LabelsFromBoundaryData C) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (D.labels.p (m8BoundaryIndexLeft i))
      (D.labels.p (m8BoundaryIndexRight i)) (D.labels.q i) := by
  simpa using D.spine.triangleWitness i

theorem extraNeighborWitness
    (D : M8LabelsFromBoundaryData C) (i : M8ExtraIndex) :
    D.predicates.extraNeighborWitness i :=
  D.extraNeighborWitness_holds i

theorem extra_r_neighbor
    (D : M8LabelsFromBoundaryData C) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) (D.labels.r i) := by
  simpa using D.lemma8.r_neighbor i

theorem extra_s_neighbor
    (D : M8LabelsFromBoundaryData C) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) (D.labels.s i) := by
  simpa using D.lemma8.s_neighbor i

end M8LabelsFromBoundaryData

namespace M8BoundaryLabelPackage

variable {C : _root_.UDConfig n}

@[simp]
theorem labels_p_projection
    (D : M8BoundaryLabelPackage C) (i : M8BoundaryIndex) :
    D.labels.p i = D.spine.p i :=
  rfl

@[simp]
theorem labels_q_projection
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    D.labels.q i = D.spine.q i :=
  rfl

@[simp]
theorem labels_r_projection
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    D.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem labels_s_projection
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    D.labels.s i = D.lemma8.s i :=
  rfl

theorem p_onOuterBoundary
    (D : M8BoundaryLabelPackage C) (i : M8BoundaryIndex) :
    D.context.outerBoundary.outerEnclosure.onBoundary (D.labels.p i) := by
  simpa using D.spine.p_onBoundary i

theorem boundaryEdge
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    D.predicates.data.boundaryEdge i :=
  D.boundaryEdge i

theorem boundaryEdge_raw
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.labels.p (m8BoundaryIndexLeft i))
      (D.labels.p (m8BoundaryIndexRight i)) := by
  simpa using D.spine.boundaryEdge i

theorem triangleWitness
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    D.predicates.data.triangleWitness i :=
  D.triangleWitness i

theorem triangleWitness_raw
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (D.labels.p (m8BoundaryIndexLeft i))
      (D.labels.p (m8BoundaryIndexRight i)) (D.labels.q i) := by
  simpa using D.spine.triangleWitness i

theorem extraNeighborWitness
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    D.predicates.data.extraNeighborWitness i :=
  D.extraNeighborWitness i

theorem extra_r_neighbor
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) (D.labels.r i) := by
  simpa using D.lemma8.r_neighbor i

theorem extra_s_neighbor
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) (D.labels.s i) := by
  simpa using D.lemma8.s_neighbor i

end M8BoundaryLabelPackage

/-! ## Finite certificate projections -/

namespace M8FinitePQSpineCertificate

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}
variable {connectedNoCut : PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

theorem p_eq_outerCycle_vertex
    (K : M8FinitePQSpineCertificate D) (i : M8BoundaryIndex) :
    K.p i = D.core.outerCycle.vertex (K.pIndex i) :=
  K.p_eq_outerCycle i

theorem p_onOuterBoundary
    (K : M8FinitePQSpineCertificate D) (i : M8BoundaryIndex) :
    (K.context connectedNoCut hmin).outerBoundary.outerEnclosure.onBoundary
      (K.p i) :=
  K.p_onBoundary connectedNoCut hmin i

theorem spine_p_projection
    (K : M8FinitePQSpineCertificate D) (i : M8BoundaryIndex) :
    (K.toM8BoundarySpine connectedNoCut hmin).p i = K.p i :=
  rfl

theorem spine_q_projection
    (K : M8FinitePQSpineCertificate D) (i : M8TriangleIndex) :
    (K.toM8BoundarySpine connectedNoCut hmin).q i = K.q i :=
  rfl

theorem spine_boundaryEdge
    (K : M8FinitePQSpineCertificate D) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      ((K.toM8BoundarySpine connectedNoCut hmin).p (m8BoundaryIndexLeft i))
      ((K.toM8BoundarySpine connectedNoCut hmin).p
        (m8BoundaryIndexRight i)) :=
  K.boundaryEdge i

theorem spine_triangleWitness
    (K : M8FinitePQSpineCertificate D) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      ((K.toM8BoundarySpine connectedNoCut hmin).p (m8BoundaryIndexLeft i))
      ((K.toM8BoundarySpine connectedNoCut hmin).p
        (m8BoundaryIndexRight i))
      ((K.toM8BoundarySpine connectedNoCut hmin).q i) :=
  K.triangleWitness i

theorem localLabels_boundaryEdge
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toM8LocalLabels
      connectedNoCut hmin lemma8).predicates.data.boundaryEdge i :=
  K.toM8LocalLabels_boundaryEdge lemma8 i

theorem localLabels_triangleWitness
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toM8LocalLabels
      connectedNoCut hmin lemma8).predicates.data.triangleWitness i :=
  K.toM8LocalLabels_triangleWitness lemma8 i

theorem localLabels_extraNeighborWitness
    (K : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    (K.toM8LocalLabels
      connectedNoCut hmin lemma8).predicates.data.extraNeighborWitness i :=
  K.toM8LocalLabels_extraNeighborWitness lemma8 i

end M8FinitePQSpineCertificate

end OuterBoundaryLabelFacts

/-! ## Minimal-failure W8 source-row projections -/

namespace MinimalFailureW8RowAssembly
namespace MinimalFailureW8BoundaryLongArcData

variable {n : Nat}
variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

@[simp]
theorem labels_p_projection
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8BoundaryIndex) :
    D.labels.toM8LocalLabels.labels.p i = D.spine.p i :=
  rfl

@[simp]
theorem labels_q_projection
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8TriangleIndex) :
    D.labels.toM8LocalLabels.labels.q i = D.spine.q i :=
  rfl

@[simp]
theorem labels_r_projection
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8ExtraIndex) :
    D.labels.toM8LocalLabels.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem labels_s_projection
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8ExtraIndex) :
    D.labels.toM8LocalLabels.labels.s i = D.lemma8.s i :=
  rfl

theorem p_onOuterBoundary
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8BoundaryIndex) :
    D.planarBoundary.core.outerEnclosure.onBoundary (D.spine.p i) :=
  D.spine.p_onBoundary i

theorem boundaryEdge
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8TriangleIndex) :
    D.labels.predicates.boundaryEdge i :=
  D.labels.boundaryEdge_holds i

theorem boundaryEdge_raw
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.p (m8BoundaryIndexLeft i))
      (D.spine.p (m8BoundaryIndexRight i)) :=
  D.spine.boundaryEdge i

theorem triangleWitness
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8TriangleIndex) :
    D.labels.predicates.triangleWitness i :=
  D.labels.triangleWitness_holds i

theorem triangleWitness_raw
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (D.spine.p (m8BoundaryIndexLeft i))
      (D.spine.p (m8BoundaryIndexRight i)) (D.spine.q i) :=
  D.spine.triangleWitness i

theorem extraNeighborWitness
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8ExtraIndex) :
    D.labels.predicates.extraNeighborWitness i :=
  D.labels.extraNeighborWitness_holds i

theorem extra_r_neighbor
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) (D.labels.toM8LocalLabels.labels.r i) := by
  simpa using D.lemma8.r_neighbor i

theorem extra_s_neighbor
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) (D.labels.toM8LocalLabels.labels.s i) := by
  simpa using D.lemma8.s_neighbor i

end MinimalFailureW8BoundaryLongArcData
end MinimalFailureW8RowAssembly

end

end Swanepoel
end ErdosProblems1066
