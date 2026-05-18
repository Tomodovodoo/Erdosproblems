import ErdosProblems1066.Swanepoel.Lemma8ExistenceConcrete
import ErdosProblems1066.Swanepoel.Lemma8NeighborExtractionConcrete
import ErdosProblems1066.Swanepoel.MinimalFailureDegreeRange
import ErdosProblems1066.Swanepoel.MinimalFailureLocalExclusions

set_option autoImplicit false

/-!
# Degree-six reducers for concrete Lemma 8

This file isolates the remaining non-cyclic degree-six payload around the
vertices `q_i` in the `m = 8` boundary route.

The checked content is deterministic:
* the existing degree range gives only `3 <= deg(q_i) <= 6`;
* a four-forbidden-neighbor frame identifies the local degree as
  `4 + extraNeighborFinset.card`;
* under that frame, `deg(q_i) = 6` is equivalent to exactly two extra
  neighbors;
* the exact-two data is routed to `M8ExtraNeighborData`, and then to
  `M8Lemma8Combinatorics` once the remaining cyclic-order field is supplied.

No Euclidean rotation-system existence theorem is asserted here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8DegreeSixConcrete

open GraphBridge
open Lemma8ExistenceConcrete
open M8BoundaryLabelsConcrete
open M8LabelsFromBoundaryInterface
open Lemma8NeighborExtractionConcrete

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-! ## Degree range and local-exclusion routes -/

/-- The existing structural context gives only the `3..6` range at `q_i`. -/
theorem centerDegree_between_three_and_six (i : M8ExtraIndex) :
    3 <= centerDegree S i /\ centerDegree S i <= 6 :=
  And.intro (centerDegree_ge_three S i) (centerDegree_le_six S i)

/-- The upper endpoint of the existing degree range at `q_i`. -/
theorem centerDegree_le_six_from_degreeRange (i : M8ExtraIndex) :
    centerDegree S i <= 6 :=
  centerDegree_le_six S i

/-- The lower endpoint of the existing degree range at `q_i`. -/
theorem centerDegree_ge_three_from_degreeRange (i : M8ExtraIndex) :
    3 <= centerDegree S i :=
  centerDegree_ge_three S i

/-- The supporting boundary edge common-neighbor cap routed through an
explicit finite local-exclusion package. -/
theorem boundary_commonNeighborFinset_card_le_two_of_localExclusionPackage
    (P :
      MinimalFailureLocalExclusions.FiniteLocalExclusionPackage
        (unitDistanceLocalGraph C))
    (i : M8ExtraIndex) :
    (LocalExclusions.LocalGraph.commonNeighborFinset
      (unitDistanceLocalGraph C) (S.leftP i) (S.rightP i)).card <= 2 :=
  P.commonNeighborCard_le_two (leftP_ne_rightP S i)

/-- The geometric unit-distance local-exclusion package gives the same
boundary-edge common-neighbor cap unconditionally. -/
theorem boundary_commonNeighborFinset_card_le_two_from_unitDistance
    (i : M8ExtraIndex) :
    (LocalExclusions.LocalGraph.commonNeighborFinset
      (unitDistanceLocalGraph C) (S.leftP i) (S.rightP i)).card <= 2 :=
  boundary_commonNeighborFinset_card_le_two S i

/-! ## Degree-six arithmetic under the forbidden-neighbor frame -/

variable {i : M8ExtraIndex}

/-- Under a four-forbidden-neighbor frame, the degree at `q_i` is exactly the
four forbidden neighbors plus the extra-neighbor finset. -/
theorem centerDegree_eq_four_add_extraNeighborFinset_card
    (F : FourForbiddenNeighborFrame S i) :
    centerDegree S i = 4 + (extraNeighborFinset S i).card := by
  have hcard := F.neighborFinset_card_eq_forbidden_add_extra
  have hfor := F.forbidden_card_eq_four
  simpa [centerDegree, LocalExclusions.LocalGraph.degree, hfor] using hcard

/-- With the forbidden-neighbor frame, degree six is exactly the statement
that there are two extra neighbors. -/
theorem centerDegree_eq_six_iff_extraNeighborFinset_card_eq_two
    (F : FourForbiddenNeighborFrame S i) :
    centerDegree S i = 6 <-> (extraNeighborFinset S i).card = 2 := by
  constructor
  · intro hdegree
    exact F.extraNeighborFinset_card_eq_two_of_centerDegree_eq_six hdegree
  · intro hcard
    have hdecomp := centerDegree_eq_four_add_extraNeighborFinset_card
      (S := S) F
    omega

/-- Exact-two extra-neighbor data really has extra-neighbor finset cardinality
two. -/
theorem extraNeighborFinset_card_eq_two_of_exactTwo
    (P : ExactTwoExtraNeighbors S i) :
    (extraNeighborFinset S i).card = 2 := by
  classical
  have hsubset :
      extraNeighborFinset S i <= ({P.r, P.s} : Finset (Fin n)) := by
    intro x hx
    rcases P.all_mem x hx with h | h
    · simp [h]
    · simp [h]
  have hsupset :
      ({P.r, P.s} : Finset (Fin n)) <= extraNeighborFinset S i := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · simpa [h] using P.r_mem
    · simpa [h] using P.s_mem
  have hset :
      extraNeighborFinset S i = ({P.r, P.s} : Finset (Fin n)) :=
    Finset.Subset.antisymm hsubset hsupset
  rw [hset]
  simp [P.r_ne_s]

/-- An already supplied Lemma 8 combinatorics package determines the exact
two extra neighbors as a finite object. -/
def exactTwoExtraNeighbors_of_combinatorics
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    ExactTwoExtraNeighbors S i where
  r := E.r i
  s := E.s i
  r_mem := by
    exact (mem_extraNeighborFinset S i (E.r i)).2
      ⟨E.r_neighbor i, E.r_not_forbidden i⟩
  s_mem := by
    exact (mem_extraNeighborFinset S i (E.s i)).2
      ⟨E.s_neighbor i, E.s_not_forbidden i⟩
  r_ne_s := E.r_ne_s i
  all_mem := by
    intro x hx
    exact E.named_of_extra_neighbor
      ((mem_extraNeighborFinset S i x).1 hx).1
      ((mem_extraNeighborFinset S i x).1 hx).2

@[simp]
theorem exactTwoExtraNeighbors_of_combinatorics_r
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (exactTwoExtraNeighbors_of_combinatorics E i).r = E.r i :=
  rfl

@[simp]
theorem exactTwoExtraNeighbors_of_combinatorics_s
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (exactTwoExtraNeighbors_of_combinatorics E i).s = E.s i :=
  rfl

/-- The `r_i` label supplied by Lemma 8 is a member of the concrete
extra-neighbor finset. -/
theorem combinatorics_r_mem_extraNeighborFinset
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    E.r i ∈ extraNeighborFinset S i := by
  simpa using (exactTwoExtraNeighbors_of_combinatorics E i).r_mem

/-- The `s_i` label supplied by Lemma 8 is a member of the concrete
extra-neighbor finset. -/
theorem combinatorics_s_mem_extraNeighborFinset
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    E.s i ∈ extraNeighborFinset S i := by
  simpa using (exactTwoExtraNeighbors_of_combinatorics E i).s_mem

/-- Lemma 8 exhaustiveness, expressed directly as a finset membership
case split. -/
theorem extraNeighborFinset_mem_eq_r_or_s_of_combinatorics
    (E : M8Lemma8Combinatorics S) {i : M8ExtraIndex} {x : Fin n}
    (hx : x ∈ extraNeighborFinset S i) :
    x = E.r i ∨ x = E.s i := by
  simpa using (exactTwoExtraNeighbors_of_combinatorics E i).all_mem x hx

/-- The concrete extra-neighbor finset is exactly the two Lemma 8 labels. -/
theorem extraNeighborFinset_eq_pair_of_combinatorics
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    extraNeighborFinset S i = ({E.r i, E.s i} : Finset (Fin n)) := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    rcases extraNeighborFinset_mem_eq_r_or_s_of_combinatorics E hx with h | h
    · simp [h]
    · simp [h]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · simpa [h] using combinatorics_r_mem_extraNeighborFinset E i
    · simpa [h] using combinatorics_s_mem_extraNeighborFinset E i

/-- Lemma 8 combinatorics makes the extra-neighbor finset have cardinality
two. -/
theorem extraNeighborFinset_card_eq_two_of_combinatorics
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (extraNeighborFinset S i).card = 2 :=
  extraNeighborFinset_card_eq_two_of_exactTwo
    (exactTwoExtraNeighbors_of_combinatorics E i)

/-- If Lemma 8 combinatorics is already supplied and the forbidden four are
known to be a genuine neighbor frame, then the center degree is forced to be
six. -/
theorem centerDegree_eq_six_of_combinatorics_and_forbiddenFrame
    (E : M8Lemma8Combinatorics S)
    (F : FourForbiddenNeighborFrame S i) :
    centerDegree S i = 6 :=
  (centerDegree_eq_six_iff_extraNeighborFinset_card_eq_two F).2
    (extraNeighborFinset_card_eq_two_of_combinatorics E i)

/-- Lemma 8 combinatorics plus the forbidden-neighbor frame gives both the
honest degree-six conclusion and the exact concrete extra-neighbor finset. -/
theorem centerDegree_eq_six_and_extraNeighborFinset_eq_pair_of_combinatorics_and_forbiddenFrame
    (E : M8Lemma8Combinatorics S)
    (F : FourForbiddenNeighborFrame S i) :
    centerDegree S i = 6 ∧
      extraNeighborFinset S i = ({E.r i, E.s i} : Finset (Fin n)) :=
  And.intro
    (centerDegree_eq_six_of_combinatorics_and_forbiddenFrame E F)
    (extraNeighborFinset_eq_pair_of_combinatorics E i)

/-! ## The isolated non-cyclic degree-six fields -/

/-- The exact non-cyclic fields needed to turn degree six into named extra
neighbors for all `q_i`.  The cyclic-order assertion is deliberately absent. -/
structure M8DegreeSixNoncyclicFields
    (S : M8BoundarySpine H) where
  centerDegreeSix : forall i : M8ExtraIndex, centerDegree S i = 6
  forbiddenFrame : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i

namespace M8DegreeSixNoncyclicFields

/-- Projection of the isolated degree-six field. -/
theorem centerDegreeSix_holds
    (D : M8DegreeSixNoncyclicFields S) (i : M8ExtraIndex) :
    centerDegree S i = 6 :=
  D.centerDegreeSix i

/-- Projection of the isolated four-forbidden-neighbor frame. -/
theorem forbiddenFrame_holds
    (D : M8DegreeSixNoncyclicFields S) (i : M8ExtraIndex) :
    FourForbiddenNeighborFrame S i :=
  D.forbiddenFrame i

/-- Repackage an already supplied Lemma 8 combinatorics record and a
forbidden-frame family as the non-cyclic degree-six fields. -/
def ofLemma8CombinatoricsAndForbiddenFrame
    (E : M8Lemma8Combinatorics S)
    (F : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i) :
    M8DegreeSixNoncyclicFields S where
  centerDegreeSix := fun i =>
    centerDegree_eq_six_of_combinatorics_and_forbiddenFrame E (F i)
  forbiddenFrame := F

/-- The isolated non-cyclic fields force exactly two extra neighbors at every
`q_i`. -/
theorem extraNeighborFinset_card_eq_two
    (D : M8DegreeSixNoncyclicFields S) (i : M8ExtraIndex) :
    (extraNeighborFinset S i).card = 2 :=
  (D.forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
    (D.centerDegreeSix i)

/-- The chosen exact-two pair obtained from the deterministic degree-six
fields. -/
def pair
    (D : M8DegreeSixNoncyclicFields S) (i : M8ExtraIndex) :
    ExactTwoExtraNeighbors S i :=
  ExactTwoExtraNeighbors.of_card_eq_two (D.extraNeighborFinset_card_eq_two i)

@[simp]
theorem pair_r_mem
    (D : M8DegreeSixNoncyclicFields S) (i : M8ExtraIndex) :
    (D.pair i).r ∈ extraNeighborFinset S i :=
  (D.pair i).r_mem

@[simp]
theorem pair_s_mem
    (D : M8DegreeSixNoncyclicFields S) (i : M8ExtraIndex) :
    (D.pair i).s ∈ extraNeighborFinset S i :=
  (D.pair i).s_mem

/-- The deterministic degree-six fields produce the non-cyclic extraction
record used by the neighbor-extraction file. -/
def toExtraNeighborData
    (D : M8DegreeSixNoncyclicFields S) :
    M8ExtraNeighborData S where
  r := fun i => (D.pair i).r
  s := fun i => (D.pair i).s
  r_neighbor := fun i => (D.pair i).r_neighbor
  s_neighbor := fun i => (D.pair i).s_neighbor
  r_not_forbidden := fun i => (D.pair i).r_not_forbidden
  s_not_forbidden := fun i => (D.pair i).s_not_forbidden
  r_ne_s := fun i => (D.pair i).r_ne_s
  all_extra_neighbors_are_named := fun i _x hadj hnot =>
    (D.pair i).named_of_extra_neighbor hadj hnot

@[simp]
theorem toExtraNeighborData_r
    (D : M8DegreeSixNoncyclicFields S) (i : M8ExtraIndex) :
    D.toExtraNeighborData.r i = (D.pair i).r :=
  rfl

@[simp]
theorem toExtraNeighborData_s
    (D : M8DegreeSixNoncyclicFields S) (i : M8ExtraIndex) :
    D.toExtraNeighborData.s i = (D.pair i).s :=
  rfl

/-- The constructed extraction record preserves the local witness predicate. -/
theorem toExtraNeighborData_extraNeighborWitness
    (D : M8DegreeSixNoncyclicFields S) (i : M8ExtraIndex) :
    D.toExtraNeighborData.extraNeighborWitness i :=
  D.toExtraNeighborData.extraNeighborWitness_holds i

/-- With the remaining cyclic-order record, the deterministic degree-six
fields assemble the full Lemma 8 combinatorics package. -/
def toLemma8Combinatorics
    (D : M8DegreeSixNoncyclicFields S)
    (O : M8ExtraNeighborData.CyclicOrder D.toExtraNeighborData) :
    M8Lemma8Combinatorics S :=
  D.toExtraNeighborData.toLemma8Combinatorics O

@[simp]
theorem toLemma8Combinatorics_r
    (D : M8DegreeSixNoncyclicFields S)
    (O : M8ExtraNeighborData.CyclicOrder D.toExtraNeighborData)
    (i : M8ExtraIndex) :
    (D.toLemma8Combinatorics O).r i = (D.pair i).r :=
  rfl

@[simp]
theorem toLemma8Combinatorics_s
    (D : M8DegreeSixNoncyclicFields S)
    (O : M8ExtraNeighborData.CyclicOrder D.toExtraNeighborData)
    (i : M8ExtraIndex) :
    (D.toLemma8Combinatorics O).s i = (D.pair i).s :=
  rfl

end M8DegreeSixNoncyclicFields

/-! ## Exact degree-six data preserving named Lemma 8 pairs -/

/-- Degree-six data together with a specified exact pair of extra neighbors at
every `q_i`.

Unlike `M8DegreeSixNoncyclicFields.pair`, this record can preserve an existing
Lemma 8 choice of labels definitionally. -/
structure M8DegreeSixExactExtraNeighborData
    (S : M8BoundarySpine H) where
  centerDegreeSix : forall i : M8ExtraIndex, centerDegree S i = 6
  forbiddenFrame : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i
  pair : forall i : M8ExtraIndex, ExactTwoExtraNeighbors S i

namespace M8DegreeSixExactExtraNeighborData

/-- Forget the specified exact pairs back to the non-cyclic degree-six fields.
-/
def toNoncyclicFields
    (D : M8DegreeSixExactExtraNeighborData S) :
    M8DegreeSixNoncyclicFields S where
  centerDegreeSix := D.centerDegreeSix
  forbiddenFrame := D.forbiddenFrame

/-- Add the deterministic exact pairs to the non-cyclic degree-six fields. -/
def ofNoncyclicFields
    (D : M8DegreeSixNoncyclicFields S) :
    M8DegreeSixExactExtraNeighborData S where
  centerDegreeSix := D.centerDegreeSix
  forbiddenFrame := D.forbiddenFrame
  pair := fun i => D.pair i

/-- Build exact degree-six data from Lemma 8 combinatorics and the
forbidden-neighbor frame family, preserving the Lemma 8 labels as the exact
pair. -/
def ofLemma8CombinatoricsAndForbiddenFrame
    (E : M8Lemma8Combinatorics S)
    (F : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i) :
    M8DegreeSixExactExtraNeighborData S where
  centerDegreeSix := fun i =>
    centerDegree_eq_six_of_combinatorics_and_forbiddenFrame E (F i)
  forbiddenFrame := F
  pair := fun i => exactTwoExtraNeighbors_of_combinatorics E i

/-- The specified exact pair gives the concrete cardinality-two conclusion. -/
theorem extraNeighborFinset_card_eq_two
    (D : M8DegreeSixExactExtraNeighborData S) (i : M8ExtraIndex) :
    (extraNeighborFinset S i).card = 2 :=
  extraNeighborFinset_card_eq_two_of_exactTwo (D.pair i)

/-- The specified exact pairs produce the non-cyclic extraction record. -/
def toExtraNeighborData
    (D : M8DegreeSixExactExtraNeighborData S) :
    M8ExtraNeighborData S where
  r := fun i => (D.pair i).r
  s := fun i => (D.pair i).s
  r_neighbor := fun i => (D.pair i).r_neighbor
  s_neighbor := fun i => (D.pair i).s_neighbor
  r_not_forbidden := fun i => (D.pair i).r_not_forbidden
  s_not_forbidden := fun i => (D.pair i).s_not_forbidden
  r_ne_s := fun i => (D.pair i).r_ne_s
  all_extra_neighbors_are_named := fun i _x hadj hnot =>
    (D.pair i).named_of_extra_neighbor hadj hnot

@[simp]
theorem toExtraNeighborData_r
    (D : M8DegreeSixExactExtraNeighborData S) (i : M8ExtraIndex) :
    D.toExtraNeighborData.r i = (D.pair i).r :=
  rfl

@[simp]
theorem toExtraNeighborData_s
    (D : M8DegreeSixExactExtraNeighborData S) (i : M8ExtraIndex) :
    D.toExtraNeighborData.s i = (D.pair i).s :=
  rfl

/-- The extracted record preserves the exact local witness predicate. -/
theorem toExtraNeighborData_extraNeighborWitness
    (D : M8DegreeSixExactExtraNeighborData S) (i : M8ExtraIndex) :
    D.toExtraNeighborData.extraNeighborWitness i :=
  D.toExtraNeighborData.extraNeighborWitness_holds i

@[simp]
theorem ofLemma8CombinatoricsAndForbiddenFrame_pair_r
    (E : M8Lemma8Combinatorics S)
    (F : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i)
    (i : M8ExtraIndex) :
    ((ofLemma8CombinatoricsAndForbiddenFrame E F).pair i).r = E.r i :=
  rfl

@[simp]
theorem ofLemma8CombinatoricsAndForbiddenFrame_pair_s
    (E : M8Lemma8Combinatorics S)
    (F : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i)
    (i : M8ExtraIndex) :
    ((ofLemma8CombinatoricsAndForbiddenFrame E F).pair i).s = E.s i :=
  rfl

@[simp]
theorem ofLemma8CombinatoricsAndForbiddenFrame_toExtraNeighborData_r
    (E : M8Lemma8Combinatorics S)
    (F : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i)
    (i : M8ExtraIndex) :
    (ofLemma8CombinatoricsAndForbiddenFrame E F).toExtraNeighborData.r i =
      E.r i :=
  rfl

@[simp]
theorem ofLemma8CombinatoricsAndForbiddenFrame_toExtraNeighborData_s
    (E : M8Lemma8Combinatorics S)
    (F : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i)
    (i : M8ExtraIndex) :
    (ofLemma8CombinatoricsAndForbiddenFrame E F).toExtraNeighborData.s i =
      E.s i :=
  rfl

end M8DegreeSixExactExtraNeighborData

/-! ## A single packaged interface toward `M8Lemma8Combinatorics` -/

/-- The remaining fields for Lemma 8 after deterministic degree-six extraction:
the non-cyclic degree-six data plus the cyclic order for the extracted pair. -/
structure M8DegreeSixLemma8Fields
    (S : M8BoundarySpine H) where
  noncyclic : M8DegreeSixNoncyclicFields S
  cyclic : M8ExtraNeighborData.CyclicOrder noncyclic.toExtraNeighborData

namespace M8DegreeSixLemma8Fields

/-- Assemble the full Lemma 8 combinatorics package from the isolated
degree-six fields and cyclic order. -/
def toLemma8Combinatorics
    (D : M8DegreeSixLemma8Fields S) :
    M8Lemma8Combinatorics S :=
  D.noncyclic.toLemma8Combinatorics D.cyclic

@[simp]
theorem toLemma8Combinatorics_r
    (D : M8DegreeSixLemma8Fields S) (i : M8ExtraIndex) :
    D.toLemma8Combinatorics.r i = (D.noncyclic.pair i).r :=
  rfl

@[simp]
theorem toLemma8Combinatorics_s
    (D : M8DegreeSixLemma8Fields S) (i : M8ExtraIndex) :
    D.toLemma8Combinatorics.s i = (D.noncyclic.pair i).s :=
  rfl

/-- The assembled package satisfies the stored extra-neighbor witness. -/
theorem toLemma8Combinatorics_extraNeighborWitness
    (D : M8DegreeSixLemma8Fields S) (i : M8ExtraIndex) :
    D.toLemma8Combinatorics.extraNeighborWitness i :=
  D.toLemma8Combinatorics.extraNeighborWitness_holds i

/-- The assembled package keeps the isolated cyclic-order predicate. -/
theorem toLemma8Combinatorics_positiveCyclicOrder
    (D : M8DegreeSixLemma8Fields S) (i : M8ExtraIndex) :
    D.cyclic.positiveCyclicOrderAt i
      (D.toLemma8Combinatorics.s i) (D.toLemma8Combinatorics.r i)
      (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i) := by
  simpa [toLemma8Combinatorics] using
    D.toLemma8Combinatorics.positiveCyclicOrder_holds i

end M8DegreeSixLemma8Fields

end

end Lemma8DegreeSixConcrete
end Swanepoel
end ErdosProblems1066
