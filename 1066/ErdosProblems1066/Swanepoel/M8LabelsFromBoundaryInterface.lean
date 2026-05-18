import ErdosProblems1066.Swanepoel.BoundaryWalkConstruction
import ErdosProblems1066.Swanepoel.CutVertexClosure
import ErdosProblems1066.Swanepoel.M8ConstructionInterface
import ErdosProblems1066.Swanepoel.MinimalFailureDegreeRange

/-!
# Boundary-to-label interface for the `m = 8` construction

This file is an adapter layer.  It records exactly which boundary, no-cut, and
minimum-degree data are being used before the missing paper Lemma 8
combinatorics is supplied as explicit data.  From that explicit Lemma 8 package
it constructs the local-label field required by `M8ConstructionInterface`.

No boundary arc, rotation-system, or Lemma 8 existence theorem is proved here.
Those remain honest inputs; the checked content is the conversion into the
existing `M8LocalLabels` and `M8ConstructionData` interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8LabelsFromBoundaryInterface

open CutVertexClosure
open CutVertexInterface
open GraphBridge
open Lemma10Bridge
open LocalConfigurations
open M8ConstructionInterface
open MinimalGraphFacts

noncomputable section

/-! ## The structural context: boundary, no cut vertex, and degree range -/

/-- The unit-distance degree range used by the Lemma 8 construction route. -/
structure UnitDistanceDegreeRange {n : Nat} (C : _root_.UDConfig n) : Prop where
  minDegree :
    forall v : Fin n, 3 <= (DegreePipeline.unitDistanceNeighborSet C v).card
  maxDegree :
    forall v : Fin n, (DegreePipeline.unitDistanceNeighborSet C v).card <= 6

namespace UnitDistanceDegreeRange

variable {n : Nat} {C : _root_.UDConfig n}

/-- Minimal cleared failures have the degree range used by the boundary route. -/
theorem of_minimalClearedFailure (hmin : IsMinimalClearedFailure C) :
    UnitDistanceDegreeRange C where
  minDegree :=
    MinimalFailureDegreeRange.unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure
      hmin
  maxDegree := MinimalFailureDegreeRange.unitDistanceNeighborSet_card_le_six C

/-- Projection of the lower degree bound. -/
theorem min_degree (H : UnitDistanceDegreeRange C) (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
  H.minDegree v

/-- Projection of the upper degree bound. -/
theorem max_degree (H : UnitDistanceDegreeRange C) (v : Fin n) :
    (DegreePipeline.unitDistanceNeighborSet C v).card <= 6 :=
  H.maxDegree v

end UnitDistanceDegreeRange

/--
The structural hypotheses from which the paper derives the broken-lattice
boundary labels.

The outer boundary is the selected boundary core for the canonical
unit-distance graph of `C`; the cut-vertex field packages connectedness and
absence of supplied cut-vertex partitions; and the degree field packages the
`3..6` unit-distance degree range.
-/
structure M8BoundaryCutDegreeContext {n : Nat}
    (C : _root_.UDConfig n) where
  outerBoundary :
    OuterBoundaryCore
      (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C)
  connectedNoCut : PreconnectedNoCutVertexCertificate C
  degreeRange : UnitDistanceDegreeRange C

namespace M8BoundaryCutDegreeContext

variable {n : Nat} {C : _root_.UDConfig n}

/-- Build the structural context from an outer boundary, no-cut certificate,
and minimal-failure proof. -/
def of_minimalClearedFailure
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    M8BoundaryCutDegreeContext C where
  outerBoundary := outerBoundary
  connectedNoCut := connectedNoCut
  degreeRange := UnitDistanceDegreeRange.of_minimalClearedFailure hmin

/-- Build the structural context from the connected/no-cut closure data. -/
def of_connectedNoCutVertexClosureData
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (H : ConnectedNoCutVertexClosureData C) :
    M8BoundaryCutDegreeContext C :=
  of_minimalClearedFailure outerBoundary
    H.preconnectedNoCutVertexCertificate H.minimalFailure

/-- The unit-distance graph is preconnected in the structural context. -/
theorem preconnected (H : M8BoundaryCutDegreeContext C) :
    (unitDistanceSimpleGraph C).Preconnected :=
  H.connectedNoCut.preconnected

/-- The structural context includes the no-cut-vertex certificate. -/
theorem noCutVertex (H : M8BoundaryCutDegreeContext C) :
    NoCutVertex C :=
  H.connectedNoCut.noCutVertex

/-- Projection of the lower degree bound. -/
theorem minDegree (H : M8BoundaryCutDegreeContext C) (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
  H.degreeRange.minDegree v

/-- Projection of the upper degree bound. -/
theorem maxDegree (H : M8BoundaryCutDegreeContext C) (v : Fin n) :
    (DegreePipeline.unitDistanceNeighborSet C v).card <= 6 :=
  H.degreeRange.maxDegree v

end M8BoundaryCutDegreeContext

/-! ## `m = 8` index helpers -/

/-- Boundary indices `p_0, ..., p_13` for the `m = 8` specialization. -/
abbrev M8BoundaryIndex : Type :=
  BoundaryIndex 8

/-- Triangle/common-neighbor indices `q_0, ..., q_12` for `m = 8`. -/
abbrev M8TriangleIndex : Type :=
  TriangleIndex 8

/-- Extra-neighbor indices `1, ..., 11` for `m = 8`. -/
abbrev M8ExtraIndex : Type :=
  ExtraIndex 8

/-- The left boundary index of the triangle edge indexed by `i`. -/
def m8BoundaryIndexLeft (i : M8TriangleIndex) : M8BoundaryIndex :=
  Subtype.mk i.1 (by
    have hi := i.2
    omega)

/-- The right boundary index of the triangle edge indexed by `i`. -/
def m8BoundaryIndexRight (i : M8TriangleIndex) : M8BoundaryIndex :=
  Subtype.mk (i.1 + 1) (by
    have hi := i.2
    omega)

/-- The central `q_i` index attached to an extra-neighbor index. -/
def m8TriangleIndexOfExtra (i : M8ExtraIndex) : M8TriangleIndex :=
  Subtype.mk i.1 (by
    have hi := i.2
    omega)

/-- The previous `q_{i-1}` index attached to an extra-neighbor index. -/
def m8TriangleIndexPrevOfExtra (i : M8ExtraIndex) : M8TriangleIndex :=
  Subtype.mk (i.1 - 1) (by
    have hi := i.2
    omega)

/-- The next `q_{i+1}` index attached to an extra-neighbor index. -/
def m8TriangleIndexNextOfExtra (i : M8ExtraIndex) : M8TriangleIndex :=
  Subtype.mk (i.1 + 1) (by
    have hi := i.2
    omega)

@[simp]
theorem m8BoundaryIndexLeft_val (i : M8TriangleIndex) :
    (m8BoundaryIndexLeft i).1 = i.1 :=
  rfl

@[simp]
theorem m8BoundaryIndexRight_val (i : M8TriangleIndex) :
    (m8BoundaryIndexRight i).1 = i.1 + 1 :=
  rfl

@[simp]
theorem m8TriangleIndexOfExtra_val (i : M8ExtraIndex) :
    (m8TriangleIndexOfExtra i).1 = i.1 :=
  rfl

@[simp]
theorem m8TriangleIndexPrevOfExtra_val (i : M8ExtraIndex) :
    (m8TriangleIndexPrevOfExtra i).1 = i.1 - 1 :=
  rfl

@[simp]
theorem m8TriangleIndexNextOfExtra_val (i : M8ExtraIndex) :
    (m8TriangleIndexNextOfExtra i).1 = i.1 + 1 :=
  rfl

/-! ## Boundary spine and explicit Lemma 8 combinatorics -/

/--
The boundary part of the broken-lattice labels.

The fields record the consecutive boundary labels `p_i`, their common
neighbors `q_i`, and the local facts needed to view the relevant boundary
edges as triangle edges in the unit-distance local graph.
-/
structure M8BoundarySpine {n : Nat} {C : _root_.UDConfig n}
    (H : M8BoundaryCutDegreeContext C) where
  p : M8BoundaryIndex -> Fin n
  q : M8TriangleIndex -> Fin n
  p_onBoundary :
    forall i : M8BoundaryIndex,
      H.outerBoundary.outerEnclosure.onBoundary (p i)
  boundaryEdge :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).Adj
        (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i))
  triangleWitness :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).CommonNeighbor
        (p (m8BoundaryIndexLeft i)) (p (m8BoundaryIndexRight i)) (q i)

namespace M8BoundarySpine

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}

/-- The left endpoint of the boundary edge supporting `q_i`. -/
def leftP (S : M8BoundarySpine H) (i : M8ExtraIndex) : Fin n :=
  S.p (m8BoundaryIndexLeft (m8TriangleIndexOfExtra i))

/-- The right endpoint of the boundary edge supporting `q_i`. -/
def rightP (S : M8BoundarySpine H) (i : M8ExtraIndex) : Fin n :=
  S.p (m8BoundaryIndexRight (m8TriangleIndexOfExtra i))

/-- The central common-neighbor label `q_i`. -/
def centerQ (S : M8BoundarySpine H) (i : M8ExtraIndex) : Fin n :=
  S.q (m8TriangleIndexOfExtra i)

/-- The previous common-neighbor label `q_{i-1}`. -/
def prevQ (S : M8BoundarySpine H) (i : M8ExtraIndex) : Fin n :=
  S.q (m8TriangleIndexPrevOfExtra i)

/-- The next common-neighbor label `q_{i+1}`. -/
def nextQ (S : M8BoundarySpine H) (i : M8ExtraIndex) : Fin n :=
  S.q (m8TriangleIndexNextOfExtra i)

/-- Vertices not counted as "extra" around the center `q_i` in Lemma 8. -/
def forbiddenExtraNeighbor (S : M8BoundarySpine H)
    (i : M8ExtraIndex) (x : Fin n) : Prop :=
  x = S.leftP i \/ x = S.rightP i \/ x = S.prevQ i \/ x = S.nextQ i

/-- The boundary edge predicate attached to the spine holds by construction. -/
theorem boundaryEdge_holds (S : M8BoundarySpine H)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (S.p (m8BoundaryIndexLeft i)) (S.p (m8BoundaryIndexRight i)) :=
  S.boundaryEdge i

/-- The common-neighbor predicate attached to the spine holds by construction. -/
theorem triangleWitness_holds (S : M8BoundarySpine H)
    (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).CommonNeighbor
      (S.p (m8BoundaryIndexLeft i)) (S.p (m8BoundaryIndexRight i)) (S.q i) :=
  S.triangleWitness i

/-- The central `q_i` is adjacent to the left boundary endpoint. -/
theorem centerQ_adj_leftP (S : M8BoundarySpine H)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (S.leftP i) :=
  (S.triangleWitness (m8TriangleIndexOfExtra i)).1

/-- The central `q_i` is adjacent to the right boundary endpoint. -/
theorem centerQ_adj_rightP (S : M8BoundarySpine H)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (S.rightP i) :=
  (S.triangleWitness (m8TriangleIndexOfExtra i)).2

end M8BoundarySpine

/--
Explicit package for the missing paper Lemma 8 combinatorics.

For every `i = 1, ..., 11`, the package names the two extra neighbors
`r_i, s_i` of `q_i`, proves that they are outside the forbidden list
`p_i, p_{i+1}, q_{i-1}, q_{i+1}`, proves the "at most two" exhaustiveness
statement, and records whichever positive cyclic-order predicate the geometric
layer chooses to use.
-/
structure M8Lemma8Combinatorics {n : Nat} {C : _root_.UDConfig n}
    {H : M8BoundaryCutDegreeContext C} (S : M8BoundarySpine H) where
  r : M8ExtraIndex -> Fin n
  s : M8ExtraIndex -> Fin n
  r_neighbor :
    forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj (S.centerQ i) (r i)
  s_neighbor :
    forall i : M8ExtraIndex,
      (unitDistanceLocalGraph C).Adj (S.centerQ i) (s i)
  r_not_forbidden :
    forall i : M8ExtraIndex, Not (S.forbiddenExtraNeighbor i (r i))
  s_not_forbidden :
    forall i : M8ExtraIndex, Not (S.forbiddenExtraNeighbor i (s i))
  r_ne_s : forall i : M8ExtraIndex, Not (r i = s i)
  all_extra_neighbors_are_named :
    forall i : M8ExtraIndex, forall x : Fin n,
      (unitDistanceLocalGraph C).Adj (S.centerQ i) x ->
      Not (S.forbiddenExtraNeighbor i x) ->
        x = r i \/ x = s i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i (s i) (r i) (S.prevQ i)
        (S.leftP i) (S.rightP i) (S.nextQ i)

namespace M8Lemma8Combinatorics

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-- The local predicate stored for the extra-neighbor witnesses. -/
def extraNeighborWitness (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) : Prop :=
  (unitDistanceLocalGraph C).Adj (S.centerQ i) (E.r i) /\
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (E.s i) /\
    Not (S.forbiddenExtraNeighbor i (E.r i)) /\
    Not (S.forbiddenExtraNeighbor i (E.s i)) /\
    Not (E.r i = E.s i)

/-- The explicit Lemma 8 package satisfies the local extra-neighbor predicate. -/
theorem extraNeighborWitness_holds (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    E.extraNeighborWitness i :=
  And.intro (E.r_neighbor i)
    (And.intro (E.s_neighbor i)
      (And.intro (E.r_not_forbidden i)
        (And.intro (E.s_not_forbidden i) (E.r_ne_s i))))

/-- Projection of the exhaustive "at most the named two extra neighbors" fact. -/
theorem named_of_extra_neighbor (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    x = E.r i \/ x = E.s i :=
  E.all_extra_neighbors_are_named i x hadj hnot

/-- Projection of the recorded cyclic order around `q_i`. -/
theorem positiveCyclicOrder_holds (E : M8Lemma8Combinatorics S)
    (i : M8ExtraIndex) :
    E.positiveCyclicOrderAt i (E.s i) (E.r i) (S.prevQ i)
      (S.leftP i) (S.rightP i) (S.nextQ i) :=
  E.positiveCyclicOrder i

end M8Lemma8Combinatorics

/-! ## Conversion to the M8 local-label field -/

/--
Boundary-derived local label data for `m = 8`.

The `context` field records the boundary/cut/degree hypotheses, `spine`
records the `p_i, q_i` boundary labels, and `lemma8` supplies the missing
`r_i, s_i` labels.
-/
structure M8LabelsFromBoundaryData {n : Nat}
    (C : _root_.UDConfig n) where
  context : M8BoundaryCutDegreeContext C
  spine : M8BoundarySpine context
  lemma8 : M8Lemma8Combinatorics spine

namespace M8LabelsFromBoundaryData

variable {n : Nat} {C : _root_.UDConfig n}

/-- The broken-lattice labels obtained from boundary and Lemma 8 data. -/
def labels (D : M8LabelsFromBoundaryData C) :
    BrokenLatticeLabels (Fin n) 8 where
  p := D.spine.p
  q := D.spine.q
  r := D.lemma8.r
  s := D.lemma8.s

/-- The broken-lattice predicates obtained from the boundary-derived labels. -/
def predicates (D : M8LabelsFromBoundaryData C) :
    BrokenLatticePredicates (unitDistanceLocalGraph C) 8 where
  labels := D.labels
  boundaryEdge := fun i =>
    (unitDistanceLocalGraph C).Adj
      (D.spine.p (m8BoundaryIndexLeft i))
      (D.spine.p (m8BoundaryIndexRight i))
  triangleWitness := fun i =>
    (unitDistanceLocalGraph C).CommonNeighbor
      (D.spine.p (m8BoundaryIndexLeft i))
      (D.spine.p (m8BoundaryIndexRight i))
      (D.spine.q i)
  extraNeighborWitness := D.lemma8.extraNeighborWitness
  lemma10Equality := M8LabelEquality D.labels
  tripleEquality := M8LabelTriple D.labels

@[simp]
theorem labels_p (D : M8LabelsFromBoundaryData C) (i : M8BoundaryIndex) :
    D.labels.p i = D.spine.p i :=
  rfl

@[simp]
theorem labels_q (D : M8LabelsFromBoundaryData C) (i : M8TriangleIndex) :
    D.labels.q i = D.spine.q i :=
  rfl

@[simp]
theorem labels_r (D : M8LabelsFromBoundaryData C) (i : M8ExtraIndex) :
    D.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem labels_s (D : M8LabelsFromBoundaryData C) (i : M8ExtraIndex) :
    D.labels.s i = D.lemma8.s i :=
  rfl

/-- The stored boundary-edge predicate is satisfied by the boundary spine. -/
theorem boundaryEdge_holds (D : M8LabelsFromBoundaryData C)
    (i : M8TriangleIndex) :
    D.predicates.boundaryEdge i :=
  D.spine.boundaryEdge i

/-- The stored triangle-witness predicate is satisfied by the boundary spine. -/
theorem triangleWitness_holds (D : M8LabelsFromBoundaryData C)
    (i : M8TriangleIndex) :
    D.predicates.triangleWitness i :=
  D.spine.triangleWitness i

/-- The stored extra-neighbor predicate is satisfied by the Lemma 8 package. -/
theorem extraNeighborWitness_holds (D : M8LabelsFromBoundaryData C)
    (i : M8ExtraIndex) :
    D.predicates.extraNeighborWitness i :=
  D.lemma8.extraNeighborWitness_holds i

/-- The named local Lemma 10 predicate is exactly the label equality. -/
theorem good_iff_labelGood (D : M8LabelsFromBoundaryData C) (i : Nat) :
    M8BrokenLatticeGood D.predicates i <-> M8LabelGood D.labels i := by
  by_cases hi : 1 <= i /\ i <= 10
  case pos =>
    simp [M8BrokenLatticeGood, M8LabelGood, predicates, hi]
  case neg =>
    simp [M8BrokenLatticeGood, M8LabelGood, hi]

/-- The named local triple predicate is exactly three consecutive local
Lemma 10 predicates. -/
theorem tripleEquality_iff_threeComparisons
    (D : M8LabelsFromBoundaryData C) (a : M8TripleStartIndex) :
    D.predicates.tripleEquality a <->
      M8BrokenLatticeTriple D.predicates a := by
  simp [predicates, M8LabelTriple, M8BrokenLatticeTriple,
    M8BrokenLatticeGood, M8LabelGood]

/-- Convert the boundary-derived labels to an honest local predicate package. -/
def toHonestLocalPredicates (D : M8LabelsFromBoundaryData C) :
    M8HonestLocalPredicates (unitDistanceLocalGraph C) where
  data := D.predicates
  lemma10Equality_iff_labels := by
    intro i
    rfl
  tripleEquality_iff_threeComparisons :=
    D.tripleEquality_iff_threeComparisons

/-- Convert the boundary-derived labels to the local-label field expected by
`M8ConstructionInterface`. -/
def toM8LocalLabels (D : M8LabelsFromBoundaryData C) :
    M8LocalLabels C where
  predicates := D.toHonestLocalPredicates

@[simp]
theorem toM8LocalLabels_labels (D : M8LabelsFromBoundaryData C) :
    D.toM8LocalLabels.labels = D.labels :=
  rfl

/-- Fill the `localLabels` field of the clean construction interface from
boundary-derived labels. -/
def toM8ConstructionData
    {hmin : IsMinimalClearedFailure C}
    (D : M8LabelsFromBoundaryData C)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    M8ConstructionData C hmin where
  localLabels := D.toM8LocalLabels
  turnBounds := turnBounds
  lateTriples := lateTriples
  windowGeometry := windowGeometry

@[simp]
theorem toM8ConstructionData_localLabels
    {hmin : IsMinimalClearedFailure C}
    (D : M8LabelsFromBoundaryData C)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData (hmin := hmin)
      turnBounds lateTriples windowGeometry).localLabels =
        D.toM8LocalLabels :=
  rfl

end M8LabelsFromBoundaryData

end

end M8LabelsFromBoundaryInterface
end Swanepoel
end ErdosProblems1066
