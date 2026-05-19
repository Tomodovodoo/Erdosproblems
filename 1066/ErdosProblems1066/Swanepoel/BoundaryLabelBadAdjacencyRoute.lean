import ErdosProblems1066.Swanepoel.BoundaryLabelCertificateAssembly
import ErdosProblems1066.Swanepoel.K23RouteCoverageSourceW34

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-!
# Boundary-label bad-adjacency route bridge

This file is deliberately downstream from both the finite boundary-label
assembly and the W34 route-facing K23 source.  Importing the W34 route source
back into the assembly file would make an import cycle, so the conversion from
finite-label incidence rows to route-facing common-neighbor rows lives here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelBadAdjacencyRoute

open BoundaryLabelCertificateAssembly
open BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
open BoundaryFaceCountingToM8
open CutVertexClosure
open GraphBridge
open K23RouteCoverageSourceW34
open Lemma10Bridge
open MinimalGraphFacts
open SwanepoelW32RouteAudit.ActualRouteSource

universe u

noncomputable section

def badAdjacencyCommonNeighborDatumOfStart
    {n : Nat} {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C)}
    {connectedNoCut : PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10)
    (histart : i + 2 <= 10)
    (hbad :
      (unitDistanceLocalGraph C).Adj
        (K.spine.centerQ (badAdjacencyLeftExtraOfNat i hi hi10))
        (K.lemma8.s (badAdjacencyRightExtraOfNat i hi hi10)))
    (htriple :
      K.toM8LocalLabels.predicates.data.tripleEquality
        (m8TripleStartIndexOfNat i (And.intro hi histart))) :
    BadAdjacencyCommonNeighborDatum (unitDistanceLocalGraph C) := by
  let left := badAdjacencyLeftExtraOfNat i hi hi10
  let right := badAdjacencyRightExtraOfNat i hi hi10
  let p := K.spine.rightP left
  let q0 := K.spine.centerQ left
  let q1 := K.spine.centerQ right
  let s0 := K.lemma8.s left
  let s1 := K.lemma8.s right
  refine
    { left0 := q0
      left1 := q1
      standard0 := p
      standard1 := s0
      third := s1
      left_ne := ?_
      standard01_ne := ?_
      standard0_ne_third := ?_
      standard1_ne_third := ?_
      standard0_common := ?_
      standard1_common := ?_
      third_adj_left0 := ?_
      third_adj_left1 := ?_ }
  · change
      Not
        (K.spine.centerQ left =
          K.spine.centerQ right)
    exact
      centerQ_badAdjacencyLeft_ne_centerQ_badAdjacencyRight (K := K) hi hi10
  · change
      Not
        (K.spine.rightP left =
          K.lemma8.s left)
    exact rightP_badAdjacencyLeft_ne_s_left (K := K) hi hi10
  · change
      Not
        (K.spine.rightP left =
          K.lemma8.s right)
    exact rightP_badAdjacencyLeft_ne_s_right (K := K) hi hi10
  · change
      Not
        (K.lemma8.s left =
          K.lemma8.s right)
    exact
      s_badAdjacencyLeft_ne_s_badAdjacencyRight_of_tripleStart
        (K := K) hi hi10 histart htriple
  · constructor
    · change
        (unitDistanceLocalGraph C).Adj
          (K.spine.rightP left) (K.spine.centerQ left)
      exact
        GraphBridge.unitDistanceAdj_symm C (K.spine.centerQ_adj_rightP left)
    · have hq1p :
          (unitDistanceLocalGraph C).Adj q1 p := by
        change
          (unitDistanceLocalGraph C).Adj
            (K.spine.centerQ right) (K.spine.rightP left)
        rw [rightP_badAdjacencyLeft_eq_leftP_badAdjacencyRight
          (K := K) hi hi10]
        exact K.spine.centerQ_adj_leftP right
      exact GraphBridge.unitDistanceAdj_symm C hq1p
  · have heq :=
      labelEquality_of_badAdjacencyTripleStart
        (K := K) hi hi10 histart htriple
    constructor
    · change
        (unitDistanceLocalGraph C).Adj
          (K.lemma8.s left) (K.spine.centerQ left)
      exact GraphBridge.unitDistanceAdj_symm C (K.lemma8.s_neighbor left)
    · have hq1s0 :
          (unitDistanceLocalGraph C).Adj q1 s0 := by
        change
          (unitDistanceLocalGraph C).Adj
            (K.spine.centerQ right) (K.lemma8.s left)
        rw [heq]
        exact K.lemma8.r_neighbor right
      exact GraphBridge.unitDistanceAdj_symm C hq1s0
  · change
      (unitDistanceLocalGraph C).Adj
        (K.lemma8.s right) (K.spine.centerQ left)
    exact GraphBridge.unitDistanceAdj_symm C hbad
  · change
      (unitDistanceLocalGraph C).Adj
        (K.lemma8.s right) (K.spine.centerQ right)
    exact GraphBridge.unitDistanceAdj_symm C (K.lemma8.s_neighbor right)

def badAdjacencyCommonNeighborObstructionInputsOfRows
    {n : Nat} {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C)}
    {connectedNoCut : PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (H : BadAdjacencyIncidenceRows K) :
    M8ConcreteBadAdjacencyCommonNeighborObstructionInputs
      K.toM8LocalLabels.predicates.data where
  witness_start1 h :=
    badAdjacencyCommonNeighborDatumOfStart (K := K) (i := 1)
      (by omega) (by omega) (by omega) H.adj_q1_s2
      (by simpa [NoEarlyTripleConcrete.start1] using h)
  witness_start2 h :=
    badAdjacencyCommonNeighborDatumOfStart (K := K) (i := 2)
      (by omega) (by omega) (by omega) H.adj_q2_s3
      (by simpa [NoEarlyTripleConcrete.start2] using h)
  witness_start3 h :=
    badAdjacencyCommonNeighborDatumOfStart (K := K) (i := 3)
      (by omega) (by omega) (by omega) H.adj_q3_s4
      (by simpa [NoEarlyTripleConcrete.start3] using h)
  witness_start4 h :=
    badAdjacencyCommonNeighborDatumOfStart (K := K) (i := 4)
      (by omega) (by omega) (by omega) H.adj_q4_s5
      (by simpa [NoEarlyTripleConcrete.start4] using h)
  witness_start5 h :=
    badAdjacencyCommonNeighborDatumOfStart (K := K) (i := 5)
      (by omega) (by omega) (by omega) H.adj_q5_s6
      (by simpa [NoEarlyTripleConcrete.start5] using h)

def k23ObstructionInputsOfBadAdjacencyIncidenceRows
    {n : Nat} {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C)}
    {connectedNoCut : PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (H : BadAdjacencyIncidenceRows K) :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs
      K.toM8LocalLabels.predicates.data :=
  (badAdjacencyCommonNeighborObstructionInputsOfRows (K := K) H).toK23ObstructionInputs

structure SelectedFrameFiniteLabelBadAdjacencyIncidenceRow
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Type (u + 1) where
  D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C)
  connectedNoCut : PreconnectedNoCutVertexCertificate C
  labelCertificate :
    M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin
  predicates_eq :
    labelCertificate.toM8LocalLabels.predicates.data =
      badAdjacencyCommonNeighborRowPredicates
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) C hmin
  incidenceRows : BadAdjacencyIncidenceRows labelCertificate

def badAdjacencyCommonNeighborObstructionInputsOfFiniteLabelIncidenceRow
    {H : NoCutVertexFamily}
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (R :
      SelectedFrameFiniteLabelBadAdjacencyIncidenceRow
        H componentClosure frameSource C hmin) :
    M8ConcreteBadAdjacencyCommonNeighborObstructionInputs
      (badAdjacencyCommonNeighborRowPredicates
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) C hmin) := by
  cases R with
  | mk D connectedNoCut labelCertificate predicates_eq incidenceRows =>
      simpa [predicates_eq] using
        (badAdjacencyCommonNeighborObstructionInputsOfRows
          (K := labelCertificate) incidenceRows)

def k23ObstructionInputsOfFiniteLabelIncidenceRow
    {H : NoCutVertexFamily}
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (R :
      SelectedFrameFiniteLabelBadAdjacencyIncidenceRow
        H componentClosure frameSource C hmin) :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs
      (badAdjacencyCommonNeighborRowPredicates
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) C hmin) :=
  (badAdjacencyCommonNeighborObstructionInputsOfFiniteLabelIncidenceRow R).toK23ObstructionInputs

structure SelectedFrameFiniteLabelBadAdjacencyIncidenceRows :
    Type (u + 1) where
  row :
    forall
      (H : NoCutVertexFamily)
      (componentClosure : ActualTopologyComponentClosurePackage.{u})
      (frameSource :
        FrameCyclicSourcePackage.{u}
          (noCutDependencyOfNoCutVertexFamily H)
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
      {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        SelectedFrameFiniteLabelBadAdjacencyIncidenceRow
          H componentClosure frameSource C hmin

def badAdjacencyCommonNeighborObstructionFamilyOfFiniteLabelIncidenceRows
    (R : SelectedFrameFiniteLabelBadAdjacencyIncidenceRows.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    BadAdjacencyCommonNeighborObstructionFamily
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) where
  row := fun C hmin =>
    badAdjacencyCommonNeighborObstructionInputsOfFiniteLabelIncidenceRow
      (R.row H componentClosure frameSource C hmin)

def k23ObstructionFamilyOfFiniteLabelBadAdjacencyIncidenceRows
    (R : SelectedFrameFiniteLabelBadAdjacencyIncidenceRows.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    K23ObstructionFamily
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) where
  row := fun C hmin =>
    k23ObstructionInputsOfFiniteLabelIncidenceRow
      (R.row H componentClosure frameSource C hmin)

theorem selectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem_of_finiteLabelBadAdjacencyIncidenceRows
    (R : SelectedFrameFiniteLabelBadAdjacencyIncidenceRows.{u}) :
    SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    Nonempty.intro
      (badAdjacencyCommonNeighborObstructionFamilyOfFiniteLabelIncidenceRows
        R H componentClosure frameSource)

theorem selectedFrameK23WitnessRowsSourceTheorem_of_finiteLabelBadAdjacencyIncidenceRows
    (R : SelectedFrameFiniteLabelBadAdjacencyIncidenceRows.{u}) :
    SelectedFrameK23WitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    Nonempty.intro
      (k23ObstructionFamilyOfFiniteLabelBadAdjacencyIncidenceRows
        R H componentClosure frameSource)

end

end BoundaryLabelBadAdjacencyRoute
end Swanepoel
end ErdosProblems1066
