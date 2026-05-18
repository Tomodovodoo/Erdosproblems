import ErdosProblems1066.Swanepoel.M8BoundaryLabelsConcrete
import ErdosProblems1066.Swanepoel.M8LabelsFromBoundaryInterface

set_option autoImplicit false

/-!
# Boundary label extraction reducers

This module records checked projection lemmas for the `m = 8`
boundary-label route.  It only unfolds already supplied fields from
`M8LabelsFromBoundaryInterface` and `M8BoundaryLabelsConcrete`; the geometric
existence inputs remain explicit data.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelExtractionTasks

open CutVertexClosure
open GraphBridge
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

noncomputable section

namespace M8BoundaryCutDegreeContext

variable {n : Nat} {C : _root_.UDConfig n}

@[simp]
theorem of_minimalClearedFailure_outerBoundary
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    (M8BoundaryCutDegreeContext.of_minimalClearedFailure
      outerBoundary connectedNoCut hmin).outerBoundary =
        outerBoundary :=
  rfl

@[simp]
theorem of_minimalClearedFailure_connectedNoCut
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    (M8BoundaryCutDegreeContext.of_minimalClearedFailure
      outerBoundary connectedNoCut hmin).connectedNoCut =
        connectedNoCut :=
  rfl

@[simp]
theorem of_minimalClearedFailure_degreeRange
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    (M8BoundaryCutDegreeContext.of_minimalClearedFailure
      outerBoundary connectedNoCut hmin).degreeRange =
        UnitDistanceDegreeRange.of_minimalClearedFailure hmin :=
  rfl

@[simp]
theorem of_connectedNoCutVertexClosureData_outerBoundary
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (H : ConnectedNoCutVertexClosureData C) :
    (M8BoundaryCutDegreeContext.of_connectedNoCutVertexClosureData
      outerBoundary H).outerBoundary =
        outerBoundary :=
  rfl

@[simp]
theorem of_connectedNoCutVertexClosureData_connectedNoCut
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (H : ConnectedNoCutVertexClosureData C) :
    (M8BoundaryCutDegreeContext.of_connectedNoCutVertexClosureData
      outerBoundary H).connectedNoCut =
        H.preconnectedNoCutVertexCertificate :=
  rfl

@[simp]
theorem of_connectedNoCutVertexClosureData_degreeRange
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (H : ConnectedNoCutVertexClosureData C) :
    (M8BoundaryCutDegreeContext.of_connectedNoCutVertexClosureData
      outerBoundary H).degreeRange =
        UnitDistanceDegreeRange.of_minimalClearedFailure H.minimalFailure :=
  rfl

theorem spine_label_onBoundary
    (H : M8BoundaryCutDegreeContext C)
    (S : M8BoundarySpine H) (i : M8BoundaryIndex) :
    H.outerBoundary.outerEnclosure.onBoundary (S.p i) :=
  S.p_onBoundary i

theorem spine_boundaryEdge
    (H : M8BoundaryCutDegreeContext C)
    (S : M8BoundarySpine H) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (S.p (m8BoundaryIndexLeft i)) (S.p (m8BoundaryIndexRight i)) :=
  S.boundaryEdge i

theorem spine_triangleWitness
    (H : M8BoundaryCutDegreeContext C)
    (S : M8BoundarySpine H) (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (S.p (m8BoundaryIndexLeft i)) (S.p (m8BoundaryIndexRight i)) (S.q i) :=
  S.triangleWitness i

end M8BoundaryCutDegreeContext

namespace M8BoundarySpine

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}

@[simp]
theorem leftP_eq (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    S.leftP i = S.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i)) :=
  rfl

@[simp]
theorem rightP_eq (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    S.rightP i = S.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i)) :=
  rfl

@[simp]
theorem centerQ_eq (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    S.centerQ i = S.q (m8TriangleIndexOfExtra i) :=
  rfl

@[simp]
theorem prevQ_eq (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    S.prevQ i = S.q (m8TriangleIndexPrevOfExtra i) :=
  rfl

@[simp]
theorem nextQ_eq (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    S.nextQ i = S.q (m8TriangleIndexNextOfExtra i) :=
  rfl

theorem p_onBoundary_holds (S : M8BoundarySpine H)
    (i : M8BoundaryIndex) :
    H.outerBoundary.outerEnclosure.onBoundary (S.p i) :=
  S.p_onBoundary i

theorem extra_center_triangleWitness (S : M8BoundarySpine H)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (S.leftP i) (S.rightP i) (S.centerQ i) := by
  exact S.triangleWitness (m8TriangleIndexOfExtra i)

theorem extra_boundaryEdge (S : M8BoundarySpine H)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.leftP i) (S.rightP i) := by
  exact S.boundaryEdge (m8TriangleIndexOfExtra i)

theorem forbiddenExtraNeighbor_iff (S : M8BoundarySpine H)
    (i : M8ExtraIndex) (x : Fin n) :
    S.forbiddenExtraNeighbor i x <->
      x = S.leftP i \/ x = S.rightP i \/
        x = S.prevQ i \/ x = S.nextQ i :=
  Iff.rfl

theorem not_forbidden_of_ne_all (S : M8BoundarySpine H)
    {i : M8ExtraIndex} {x : Fin n}
    (hleft : Not (x = S.leftP i))
    (hright : Not (x = S.rightP i))
    (hprev : Not (x = S.prevQ i))
    (hnext : Not (x = S.nextQ i)) :
    Not (S.forbiddenExtraNeighbor i x) := by
  intro hforbidden
  rcases hforbidden with h | h | h | h
  · exact hleft h
  · exact hright h
  · exact hprev h
  · exact hnext h

theorem ne_leftP_of_not_forbidden (S : M8BoundarySpine H)
    {i : M8ExtraIndex} {x : Fin n}
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    Not (x = S.leftP i) := by
  intro h
  exact hnot (Or.inl h)

theorem ne_rightP_of_not_forbidden (S : M8BoundarySpine H)
    {i : M8ExtraIndex} {x : Fin n}
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    Not (x = S.rightP i) := by
  intro h
  exact hnot (Or.inr (Or.inl h))

theorem ne_prevQ_of_not_forbidden (S : M8BoundarySpine H)
    {i : M8ExtraIndex} {x : Fin n}
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    Not (x = S.prevQ i) := by
  intro h
  exact hnot (Or.inr (Or.inr (Or.inl h)))

theorem ne_nextQ_of_not_forbidden (S : M8BoundarySpine H)
    {i : M8ExtraIndex} {x : Fin n}
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    Not (x = S.nextQ i) := by
  intro h
  exact hnot (Or.inr (Or.inr (Or.inr h)))

end M8BoundarySpine

namespace M8Lemma8Combinatorics

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

theorem r_neighbor_holds (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (E.r i) :=
  E.r_neighbor i

theorem s_neighbor_holds (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (E.s i) :=
  E.s_neighbor i

theorem r_not_forbidden_holds (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (E.r i)) :=
  E.r_not_forbidden i

theorem s_not_forbidden_holds (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (E.s i)) :=
  E.s_not_forbidden i

theorem r_ne_s_holds (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (E.r i = E.s i) :=
  E.r_ne_s i

theorem extraNeighborWitness_iff_fields
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    E.extraNeighborWitness i <->
      (unitDistanceLocalGraph C).Adj (S.centerQ i) (E.r i) /\
        (unitDistanceLocalGraph C).Adj (S.centerQ i) (E.s i) /\
        Not (S.forbiddenExtraNeighbor i (E.r i)) /\
        Not (S.forbiddenExtraNeighbor i (E.s i)) /\
        Not (E.r i = E.s i) :=
  Iff.rfl

theorem named_left_or_right
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    x = E.r i \/ x = E.s i :=
  E.named_of_extra_neighbor hadj hnot

theorem r_ne_leftP (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (E.r i = S.leftP i) :=
  M8BoundarySpine.ne_leftP_of_not_forbidden S (E.r_not_forbidden i)

theorem r_ne_rightP (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (E.r i = S.rightP i) :=
  M8BoundarySpine.ne_rightP_of_not_forbidden S (E.r_not_forbidden i)

theorem r_ne_prevQ (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (E.r i = S.prevQ i) :=
  M8BoundarySpine.ne_prevQ_of_not_forbidden S (E.r_not_forbidden i)

theorem r_ne_nextQ (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (E.r i = S.nextQ i) :=
  M8BoundarySpine.ne_nextQ_of_not_forbidden S (E.r_not_forbidden i)

theorem s_ne_leftP (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (E.s i = S.leftP i) :=
  M8BoundarySpine.ne_leftP_of_not_forbidden S (E.s_not_forbidden i)

theorem s_ne_rightP (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (E.s i = S.rightP i) :=
  M8BoundarySpine.ne_rightP_of_not_forbidden S (E.s_not_forbidden i)

theorem s_ne_prevQ (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (E.s i = S.prevQ i) :=
  M8BoundarySpine.ne_prevQ_of_not_forbidden S (E.s_not_forbidden i)

theorem s_ne_nextQ (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    Not (E.s i = S.nextQ i) :=
  M8BoundarySpine.ne_nextQ_of_not_forbidden S (E.s_not_forbidden i)

end M8Lemma8Combinatorics

namespace M8LabelsFromBoundaryData

variable {n : Nat} {C : _root_.UDConfig n}

@[simp]
theorem predicates_labels
    (D : M8LabelsFromBoundaryData C) :
    D.predicates.labels = D.labels :=
  rfl

theorem predicates_boundaryEdge_iff
    (D : M8LabelsFromBoundaryData C) (i : M8TriangleIndex) :
    D.predicates.boundaryEdge i <->
      (unitDistanceLocalGraph C).Adj
        (D.spine.p (m8BoundaryIndexLeft i))
        (D.spine.p (m8BoundaryIndexRight i)) :=
  Iff.rfl

theorem predicates_triangleWitness_iff
    (D : M8LabelsFromBoundaryData C) (i : M8TriangleIndex) :
    D.predicates.triangleWitness i <->
      (unitDistanceLocalGraph C).CommonNeighbor
        (D.spine.p (m8BoundaryIndexLeft i))
        (D.spine.p (m8BoundaryIndexRight i)) (D.spine.q i) :=
  Iff.rfl

theorem predicates_extraNeighborWitness_iff
    (D : M8LabelsFromBoundaryData C) (i : M8ExtraIndex) :
    D.predicates.extraNeighborWitness i <->
      D.lemma8.extraNeighborWitness i :=
  Iff.rfl

theorem predicates_lemma10Equality_iff
    (D : M8LabelsFromBoundaryData C)
    (i : Lemma10Bridge.M8Lemma10Index) :
    D.predicates.lemma10Equality i <->
      Lemma10Bridge.M8LabelEquality D.labels i :=
  Iff.rfl

theorem predicates_tripleEquality_iff
    (D : M8LabelsFromBoundaryData C)
    (i : Lemma10Bridge.M8TripleStartIndex) :
    D.predicates.tripleEquality i <->
      Lemma10Bridge.M8LabelTriple D.labels i :=
  Iff.rfl

@[simp]
theorem toHonestLocalPredicates_data
    (D : M8LabelsFromBoundaryData C) :
    D.toHonestLocalPredicates.data = D.predicates :=
  rfl

@[simp]
theorem toM8LocalLabels_predicates
    (D : M8LabelsFromBoundaryData C) :
    D.toM8LocalLabels.predicates = D.toHonestLocalPredicates :=
  rfl

@[simp]
theorem toM8ConstructionData_lateTriples
    {hmin : IsMinimalClearedFailure C}
    (D : M8LabelsFromBoundaryData C)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData (hmin := hmin)
      turnBounds lateTriples windowGeometry).lateTriples =
        lateTriples :=
  rfl

@[simp]
theorem toM8ConstructionData_windowGeometry
    {hmin : IsMinimalClearedFailure C}
    (D : M8LabelsFromBoundaryData C)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData (hmin := hmin)
      turnBounds lateTriples windowGeometry).windowGeometry =
        windowGeometry :=
  rfl

end M8LabelsFromBoundaryData

namespace M8BoundaryLabelPackage

variable {n : Nat} {C : _root_.UDConfig n}

@[simp]
theorem ofMinimalClearedFailure_context
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (spine :
      M8BoundarySpine
        (M8BoundaryCutDegreeContext.of_minimalClearedFailure
          outerBoundary connectedNoCut hmin))
    (lemma8 : M8Lemma8Combinatorics spine) :
    (M8BoundaryLabelPackage.ofMinimalClearedFailure
      outerBoundary connectedNoCut hmin spine lemma8).context =
        M8BoundaryCutDegreeContext.of_minimalClearedFailure
          outerBoundary connectedNoCut hmin :=
  rfl

@[simp]
theorem ofMinimalClearedFailure_spine
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (spine :
      M8BoundarySpine
        (M8BoundaryCutDegreeContext.of_minimalClearedFailure
          outerBoundary connectedNoCut hmin))
    (lemma8 : M8Lemma8Combinatorics spine) :
    (M8BoundaryLabelPackage.ofMinimalClearedFailure
      outerBoundary connectedNoCut hmin spine lemma8).spine =
        spine :=
  rfl

@[simp]
theorem ofMinimalClearedFailure_lemma8
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (spine :
      M8BoundarySpine
        (M8BoundaryCutDegreeContext.of_minimalClearedFailure
          outerBoundary connectedNoCut hmin))
    (lemma8 : M8Lemma8Combinatorics spine) :
    (M8BoundaryLabelPackage.ofMinimalClearedFailure
      outerBoundary connectedNoCut hmin spine lemma8).lemma8 =
        lemma8 :=
  rfl

@[simp]
theorem ofConnectedNoCutVertexClosureData_context
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (H : ConnectedNoCutVertexClosureData C)
    (spine :
      M8BoundarySpine
        (M8BoundaryCutDegreeContext.of_connectedNoCutVertexClosureData
          outerBoundary H))
    (lemma8 : M8Lemma8Combinatorics spine) :
    (M8BoundaryLabelPackage.ofConnectedNoCutVertexClosureData
      outerBoundary H spine lemma8).context =
        M8BoundaryCutDegreeContext.of_connectedNoCutVertexClosureData
          outerBoundary H :=
  rfl

@[simp]
theorem ofConnectedNoCutVertexClosureData_spine
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (H : ConnectedNoCutVertexClosureData C)
    (spine :
      M8BoundarySpine
        (M8BoundaryCutDegreeContext.of_connectedNoCutVertexClosureData
          outerBoundary H))
    (lemma8 : M8Lemma8Combinatorics spine) :
    (M8BoundaryLabelPackage.ofConnectedNoCutVertexClosureData
      outerBoundary H spine lemma8).spine =
        spine :=
  rfl

@[simp]
theorem ofConnectedNoCutVertexClosureData_lemma8
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (H : ConnectedNoCutVertexClosureData C)
    (spine :
      M8BoundarySpine
        (M8BoundaryCutDegreeContext.of_connectedNoCutVertexClosureData
          outerBoundary H))
    (lemma8 : M8Lemma8Combinatorics spine) :
    (M8BoundaryLabelPackage.ofConnectedNoCutVertexClosureData
      outerBoundary H spine lemma8).lemma8 =
        lemma8 :=
  rfl

@[simp]
theorem toLabelsFromBoundaryData_labels
    (D : M8BoundaryLabelPackage C) :
    D.toLabelsFromBoundaryData.labels = D.labels :=
  rfl

@[simp]
theorem toLabelsFromBoundaryData_predicates
    (D : M8BoundaryLabelPackage C) :
    D.toLabelsFromBoundaryData.toHonestLocalPredicates = D.predicates :=
  rfl

@[simp]
theorem toLabelsFromBoundaryData_toM8LocalLabels
    (D : M8BoundaryLabelPackage C) :
    D.toLabelsFromBoundaryData.toM8LocalLabels = D.toM8LocalLabels :=
  rfl

theorem preconnected
    (D : M8BoundaryLabelPackage C) :
    (unitDistanceSimpleGraph C).Preconnected :=
  D.context.preconnected

theorem noCutVertex
    (D : M8BoundaryLabelPackage C) :
    CutVertexInterface.NoCutVertex C :=
  D.context.noCutVertex

theorem minDegree
    (D : M8BoundaryLabelPackage C) (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
  D.context.minDegree v

theorem maxDegree
    (D : M8BoundaryLabelPackage C) (v : Fin n) :
    (DegreePipeline.unitDistanceNeighborSet C v).card <= 6 :=
  D.context.maxDegree v

theorem p_onBoundary
    (D : M8BoundaryLabelPackage C) (i : M8BoundaryIndex) :
    D.context.outerBoundary.outerEnclosure.onBoundary (D.spine.p i) :=
  D.spine.p_onBoundary i

theorem center_adj_left
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (D.spine.centerQ i) (D.spine.leftP i) :=
  D.spine.centerQ_adj_leftP i

theorem center_adj_right
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (D.spine.centerQ i) (D.spine.rightP i) :=
  D.spine.centerQ_adj_rightP i

@[simp]
theorem predicates_data_labels
    (D : M8BoundaryLabelPackage C) :
    D.predicates.data.labels = D.labels :=
  rfl

theorem predicates_boundaryEdge_iff
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    D.predicates.data.boundaryEdge i <->
      (unitDistanceLocalGraph C).Adj
        (D.spine.p (m8BoundaryIndexLeft i))
        (D.spine.p (m8BoundaryIndexRight i)) :=
  Iff.rfl

theorem predicates_triangleWitness_iff
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    D.predicates.data.triangleWitness i <->
      (unitDistanceLocalGraph C).CommonNeighbor
        (D.spine.p (m8BoundaryIndexLeft i))
        (D.spine.p (m8BoundaryIndexRight i)) (D.spine.q i) :=
  Iff.rfl

theorem predicates_extraNeighborWitness_iff
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    D.predicates.data.extraNeighborWitness i <->
      D.lemma8.extraNeighborWitness i :=
  Iff.rfl

theorem predicates_lemma10Equality_iff
    (D : M8BoundaryLabelPackage C) (i : Lemma10Bridge.M8Lemma10Index) :
    D.predicates.data.lemma10Equality i <->
      Lemma10Bridge.M8LabelEquality D.labels i :=
  Iff.rfl

theorem predicates_tripleEquality_iff
    (D : M8BoundaryLabelPackage C) (i : Lemma10Bridge.M8TripleStartIndex) :
    D.predicates.data.tripleEquality i <->
      Lemma10Bridge.M8LabelTriple D.labels i :=
  Iff.rfl

@[simp]
theorem localLabels_p (D : M8BoundaryLabelPackage C)
    (i : M8BoundaryIndex) :
    D.toM8LocalLabels.labels.p i = D.spine.p i :=
  rfl

@[simp]
theorem localLabels_q (D : M8BoundaryLabelPackage C)
    (i : M8TriangleIndex) :
    D.toM8LocalLabels.labels.q i = D.spine.q i :=
  rfl

@[simp]
theorem localLabels_r (D : M8BoundaryLabelPackage C)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem localLabels_s (D : M8BoundaryLabelPackage C)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.s i = D.lemma8.s i :=
  rfl

@[simp]
theorem toM8ConstructionData_lateTriples
    {hmin : IsMinimalClearedFailure C}
    (D : M8BoundaryLabelPackage C)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData (hmin := hmin)
      turnBounds lateTriples windowGeometry).lateTriples =
        lateTriples :=
  rfl

@[simp]
theorem toM8ConstructionData_windowGeometry
    {hmin : IsMinimalClearedFailure C}
    (D : M8BoundaryLabelPackage C)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData (hmin := hmin)
      turnBounds lateTriples windowGeometry).windowGeometry =
        windowGeometry :=
  rfl

end M8BoundaryLabelPackage

namespace M8BoundaryConstructionPackage

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

theorem preconnected
    (D : M8BoundaryConstructionPackage C hmin) :
    (unitDistanceSimpleGraph C).Preconnected :=
  M8BoundaryLabelPackage.preconnected D.boundaryLabels

theorem noCutVertex
    (D : M8BoundaryConstructionPackage C hmin) :
    CutVertexInterface.NoCutVertex C :=
  M8BoundaryLabelPackage.noCutVertex D.boundaryLabels

theorem minDegree
    (D : M8BoundaryConstructionPackage C hmin) (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
  M8BoundaryLabelPackage.minDegree D.boundaryLabels v

theorem maxDegree
    (D : M8BoundaryConstructionPackage C hmin) (v : Fin n) :
    (DegreePipeline.unitDistanceNeighborSet C v).card <= 6 :=
  M8BoundaryLabelPackage.maxDegree D.boundaryLabels v

@[simp]
theorem localLabels_labels
    (D : M8BoundaryConstructionPackage C hmin) :
    D.localLabels.labels = D.boundaryLabels.labels :=
  rfl

@[simp]
theorem predicates_data_labels
    (D : M8BoundaryConstructionPackage C hmin) :
    D.predicates.data.labels = D.boundaryLabels.labels :=
  rfl

theorem boundaryEdge
    (D : M8BoundaryConstructionPackage C hmin)
    (i : M8TriangleIndex) :
    D.predicates.data.boundaryEdge i :=
  D.boundaryLabels.boundaryEdge i

theorem triangleWitness
    (D : M8BoundaryConstructionPackage C hmin)
    (i : M8TriangleIndex) :
    D.predicates.data.triangleWitness i :=
  D.boundaryLabels.triangleWitness i

theorem extraNeighborWitness
    (D : M8BoundaryConstructionPackage C hmin)
    (i : M8ExtraIndex) :
    D.predicates.data.extraNeighborWitness i :=
  D.boundaryLabels.extraNeighborWitness i

@[simp]
theorem localLabels_p
    (D : M8BoundaryConstructionPackage C hmin)
    (i : M8BoundaryIndex) :
    D.localLabels.labels.p i = D.boundaryLabels.spine.p i :=
  rfl

@[simp]
theorem localLabels_q
    (D : M8BoundaryConstructionPackage C hmin)
    (i : M8TriangleIndex) :
    D.localLabels.labels.q i = D.boundaryLabels.spine.q i :=
  rfl

@[simp]
theorem localLabels_r
    (D : M8BoundaryConstructionPackage C hmin)
    (i : M8ExtraIndex) :
    D.localLabels.labels.r i = D.boundaryLabels.lemma8.r i :=
  rfl

@[simp]
theorem localLabels_s
    (D : M8BoundaryConstructionPackage C hmin)
    (i : M8ExtraIndex) :
    D.localLabels.labels.s i = D.boundaryLabels.lemma8.s i :=
  rfl

@[simp]
theorem toM8ConstructionData_lateTriples
    (D : M8BoundaryConstructionPackage C hmin) :
    D.toM8ConstructionData.lateTriples = D.lateTriples :=
  rfl

@[simp]
theorem toM8ConstructionData_windowGeometry
    (D : M8BoundaryConstructionPackage C hmin) :
    D.toM8ConstructionData.windowGeometry = D.windowGeometry :=
  rfl

end M8BoundaryConstructionPackage

end

end BoundaryLabelExtractionTasks
end Swanepoel
end ErdosProblems1066
