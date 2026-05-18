import ErdosProblems1066.Swanepoel.CommonNeighborGeometry
import ErdosProblems1066.Swanepoel.M8BoundaryLabelsConcrete

set_option autoImplicit false

/-!
# Concrete existence reducers for Lemma 8

This standalone module attacks the existence side of
`M8Lemma8Combinatorics`.  The checked content is finite: extra-neighbor
finsets, degree-six reducers, common-neighbor caps on the supporting boundary
edge, and an exact interface for the remaining geometric/minimality facts.

The full paper Lemma 8 is not derivable from the current boundary spine alone:
the spine gives the two boundary adjacencies of `q_i`, but it does not yet give
adjacency to `q_{i-1}, q_{i+1}`, degree six at `q_i`, or a rotation-system
choice of the positive cyclic order.  Those are recorded below as explicit
conditions.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8ExistenceConcrete

open GraphBridge
open LocalConfigurations
open M8BoundaryLabelsConcrete
open M8LabelsFromBoundaryInterface

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-! ## Finite extra-neighbor sets -/

/-- The local degree of the center `q_i`. -/
def centerDegree (S : M8BoundarySpine H) (i : M8ExtraIndex) : Nat :=
  LocalExclusions.LocalGraph.degree (unitDistanceLocalGraph C) (S.centerQ i)

/-- The four vertices excluded from the "extra neighbor" count around `q_i`. -/
def forbiddenNeighborFinset (S : M8BoundarySpine H)
    (i : M8ExtraIndex) : Finset (Fin n) :=
  {S.leftP i, S.rightP i, S.prevQ i, S.nextQ i}

/-- Neighbors of `q_i` outside the four forbidden labels. -/
def extraNeighborFinset (S : M8BoundarySpine H)
    (i : M8ExtraIndex) : Finset (Fin n) :=
  by
    classical
    exact
      (LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i)).filter
        fun x => Not (S.forbiddenExtraNeighbor i x)

@[simp]
theorem mem_forbiddenNeighborFinset
    (S : M8BoundarySpine H) (i : M8ExtraIndex) (x : Fin n) :
    x ∈ forbiddenNeighborFinset S i <->
      S.forbiddenExtraNeighbor i x := by
  classical
  simp [forbiddenNeighborFinset, M8BoundarySpine.forbiddenExtraNeighbor]

@[simp]
theorem mem_extraNeighborFinset
    (S : M8BoundarySpine H) (i : M8ExtraIndex) (x : Fin n) :
    x ∈ extraNeighborFinset S i <->
      (unitDistanceLocalGraph C).Adj (S.centerQ i) x /\
        Not (S.forbiddenExtraNeighbor i x) := by
  classical
  simp [extraNeighborFinset, LocalExclusions.LocalGraph.mem_neighborFinset]

/-- The boundary-edge endpoints supporting `q_i` are distinct. -/
theorem leftP_ne_rightP (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    Not (S.leftP i = S.rightP i) := by
  intro h
  have hadj : (unitDistanceLocalGraph C).Adj (S.leftP i) (S.rightP i) :=
    S.boundaryEdge (m8TriangleIndexOfExtra i)
  rw [h] at hadj
  exact (unitDistanceLocalGraph C).loopless (S.rightP i) hadj

/-- The context supplies the lower degree bound at each `q_i`. -/
theorem centerDegree_ge_three (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    3 <= centerDegree S i := by
  have hmin := H.minDegree (S.centerQ i)
  simpa [centerDegree, LocalExclusions.LocalGraph.degree,
    LocalExclusions.UnitDistance.unitDistance_neighborFinset_eq,
    DegreePipeline.unitDistanceNeighborSet] using hmin

/-- The Euclidean unit-distance degree bound supplies the upper degree bound
at each `q_i`. -/
theorem centerDegree_le_six (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    centerDegree S i <= 6 := by
  simpa [centerDegree] using
    LocalExclusions.UnitDistance.unitDistanceLocalGraph_degree_le_six
      C (S.centerQ i)

/-! ## Common-neighbor cap on the supporting boundary edge -/

/-- The supporting boundary edge has at most two common neighbors. -/
theorem boundary_commonNeighborFinset_card_le_two
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    (LocalExclusions.LocalGraph.commonNeighborFinset
      (unitDistanceLocalGraph C) (S.leftP i) (S.rightP i)).card <= 2 :=
  CommonNeighborGeometry.unitDistance_commonNeighborFinset_card_le_two
    C (leftP_ne_rightP S i)

/-- Besides the recorded `q_i`, the supporting boundary edge cannot have two
further distinct common neighbors. -/
theorem false_of_two_commonNeighbors_ne_center
    (S : M8BoundarySpine H) (i : M8ExtraIndex)
    {x y : Fin n}
    (hxy : Not (x = y))
    (hx_center : Not (x = S.centerQ i))
    (hy_center : Not (y = S.centerQ i))
    (hx :
      (unitDistanceLocalGraph C).CommonNeighbor
        (S.leftP i) (S.rightP i) x)
    (hy :
      (unitDistanceLocalGraph C).CommonNeighbor
        (S.leftP i) (S.rightP i) y) :
    False := by
  have hcenter_x : Not (S.centerQ i = x) := by
    intro h
    exact hx_center h.symm
  have hcenter_y : Not (S.centerQ i = y) := by
    intro h
    exact hy_center h.symm
  exact CommonNeighborGeometry.no_three_commonNeighbors_unitDistanceLocalGraph
    C (leftP_ne_rightP S i) hcenter_x hcenter_y hxy
    (S.triangleWitness (m8TriangleIndexOfExtra i)) hx hy

/-! ## Degree-six reducers -/

/-- The four forbidden vertices are a genuine adjacent frame around `q_i`.

The spine already supplies adjacency to `leftP` and `rightP`; the remaining
payload is adjacency to `prevQ` and `nextQ`, plus pairwise distinctness of all
four forbidden labels.
-/
structure FourForbiddenNeighborFrame
    (S : M8BoundarySpine H) (i : M8ExtraIndex) : Prop where
  prev_adj : (unitDistanceLocalGraph C).Adj (S.centerQ i) (S.prevQ i)
  next_adj : (unitDistanceLocalGraph C).Adj (S.centerQ i) (S.nextQ i)
  left_ne_prev : Not (S.leftP i = S.prevQ i)
  left_ne_next : Not (S.leftP i = S.nextQ i)
  right_ne_prev : Not (S.rightP i = S.prevQ i)
  right_ne_next : Not (S.rightP i = S.nextQ i)
  prev_ne_next : Not (S.prevQ i = S.nextQ i)

namespace FourForbiddenNeighborFrame

variable {i : M8ExtraIndex}

theorem forbidden_card_eq_four
    (F : FourForbiddenNeighborFrame S i) :
    (forbiddenNeighborFinset S i).card = 4 := by
  classical
  have h_lr : Not (S.leftP i = S.rightP i) := leftP_ne_rightP S i
  simp [forbiddenNeighborFinset, h_lr, F.left_ne_prev, F.left_ne_next,
    F.right_ne_prev, F.right_ne_next, F.prev_ne_next]

theorem forbidden_subset_neighborFinset
    (F : FourForbiddenNeighborFrame S i) :
    forbiddenNeighborFinset S i <=
      LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i) := by
  classical
  intro x hx
  rcases (mem_forbiddenNeighborFinset S i x).1 hx with h | h | h | h
  · subst x
    exact (LocalExclusions.LocalGraph.mem_neighborFinset
      (unitDistanceLocalGraph C) (S.centerQ i) (S.leftP i)).2
      (S.centerQ_adj_leftP i)
  · subst x
    exact (LocalExclusions.LocalGraph.mem_neighborFinset
      (unitDistanceLocalGraph C) (S.centerQ i) (S.rightP i)).2
      (S.centerQ_adj_rightP i)
  · subst x
    exact (LocalExclusions.LocalGraph.mem_neighborFinset
      (unitDistanceLocalGraph C) (S.centerQ i) (S.prevQ i)).2
      F.prev_adj
  · subst x
    exact (LocalExclusions.LocalGraph.mem_neighborFinset
      (unitDistanceLocalGraph C) (S.centerQ i) (S.nextQ i)).2
      F.next_adj

theorem disjoint_forbidden_extra :
    Disjoint (forbiddenNeighborFinset S i) (extraNeighborFinset S i) := by
  classical
  rw [Finset.disjoint_left]
  intro x hfor hextra
  exact ((mem_extraNeighborFinset S i x).1 hextra).2
    ((mem_forbiddenNeighborFinset S i x).1 hfor)

theorem neighborFinset_subset_forbidden_union_extra :
    LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i) <=
      forbiddenNeighborFinset S i ∪ extraNeighborFinset S i := by
  classical
  intro x hx
  by_cases hfor : S.forbiddenExtraNeighbor i x
  · exact Finset.mem_union_left _ ((mem_forbiddenNeighborFinset S i x).2 hfor)
  · exact Finset.mem_union_right _ ((mem_extraNeighborFinset S i x).2
      ⟨(LocalExclusions.LocalGraph.mem_neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i) x).1 hx, hfor⟩)

theorem neighborFinset_eq_forbidden_union_extra
    (F : FourForbiddenNeighborFrame S i) :
    LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i) =
      forbiddenNeighborFinset S i ∪ extraNeighborFinset S i := by
  classical
  apply Finset.Subset.antisymm
  · exact neighborFinset_subset_forbidden_union_extra
  · intro x hx
    rcases Finset.mem_union.1 hx with hfor | hextra
    · exact F.forbidden_subset_neighborFinset hfor
    · exact (LocalExclusions.LocalGraph.mem_neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i) x).2
        (((mem_extraNeighborFinset S i x).1 hextra).1)

theorem neighborFinset_card_eq_forbidden_add_extra
    (F : FourForbiddenNeighborFrame S i) :
    (LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i)).card =
      (forbiddenNeighborFinset S i).card +
        (extraNeighborFinset S i).card := by
  classical
  calc
    (LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i)).card =
        (forbiddenNeighborFinset S i ∪ extraNeighborFinset S i).card := by
          rw [F.neighborFinset_eq_forbidden_union_extra]
    _ = (forbiddenNeighborFinset S i).card +
        (extraNeighborFinset S i).card :=
          Finset.card_union_of_disjoint disjoint_forbidden_extra

/-- With a four-forbidden-neighbor frame, the degree-six bound gives the
"at most two extra neighbors" half of Lemma 8. -/
theorem extraNeighborFinset_card_le_two
    (F : FourForbiddenNeighborFrame S i) :
    (extraNeighborFinset S i).card <= 2 := by
  have hcard := F.neighborFinset_card_eq_forbidden_add_extra
  have hfor := F.forbidden_card_eq_four
  have hdeg : (LocalExclusions.LocalGraph.neighborFinset
      (unitDistanceLocalGraph C) (S.centerQ i)).card <= 6 := by
    simpa [centerDegree, LocalExclusions.LocalGraph.degree] using
      centerDegree_le_six S i
  omega

/-- If the center really has degree six, the four-forbidden-neighbor frame
gives the exact two-extra-neighbor count. -/
theorem extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
    (F : FourForbiddenNeighborFrame S i)
    (hdegree : centerDegree S i = 6) :
    (extraNeighborFinset S i).card = 2 := by
  have hcard := F.neighborFinset_card_eq_forbidden_add_extra
  have hfor := F.forbidden_card_eq_four
  have hdegree' :
      (LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i)).card = 6 := by
    simpa [centerDegree, LocalExclusions.LocalGraph.degree] using hdegree
  omega

end FourForbiddenNeighborFrame

/-! ## From exact finite counts to the Lemma 8 structure -/

/-- A chosen ordered pair of the two extra neighbors of `q_i`. -/
structure ExactTwoExtraNeighbors
    (S : M8BoundarySpine H) (i : M8ExtraIndex) where
  r : Fin n
  s : Fin n
  r_mem : r ∈ extraNeighborFinset S i
  s_mem : s ∈ extraNeighborFinset S i
  r_ne_s : Not (r = s)
  all_mem : forall x : Fin n,
    x ∈ extraNeighborFinset S i -> x = r \/ x = s

namespace ExactTwoExtraNeighbors

variable {i : M8ExtraIndex}

noncomputable def of_card_eq_two
    (hcard : (extraNeighborFinset S i).card = 2) :
    ExactTwoExtraNeighbors S i := by
  classical
  let hexists := Finset.card_eq_two.mp hcard
  let r : Fin n := Classical.choose hexists
  let hexists_r := Classical.choose_spec hexists
  let s : Fin n := Classical.choose hexists_r
  have hs : r ≠ s ∧ extraNeighborFinset S i = {r, s} :=
    Classical.choose_spec hexists_r
  have hrs : r ≠ s := hs.1
  have hset : extraNeighborFinset S i = {r, s} := hs.2
  refine
    { r := r
      s := s
      r_mem := ?_
      s_mem := ?_
      r_ne_s := hrs
      all_mem := ?_ }
  · rw [hset]
    simp
  · rw [hset]
    simp
  · intro x hx
    have hx' : x ∈ ({r, s} : Finset (Fin n)) := by
      simpa [hset] using hx
    simpa using hx'

theorem r_neighbor (P : ExactTwoExtraNeighbors S i) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) P.r :=
  ((mem_extraNeighborFinset S i P.r).1 P.r_mem).1

theorem s_neighbor (P : ExactTwoExtraNeighbors S i) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) P.s :=
  ((mem_extraNeighborFinset S i P.s).1 P.s_mem).1

theorem r_not_forbidden (P : ExactTwoExtraNeighbors S i) :
    Not (S.forbiddenExtraNeighbor i P.r) :=
  ((mem_extraNeighborFinset S i P.r).1 P.r_mem).2

theorem s_not_forbidden (P : ExactTwoExtraNeighbors S i) :
    Not (S.forbiddenExtraNeighbor i P.s) :=
  ((mem_extraNeighborFinset S i P.s).1 P.s_mem).2

theorem named_of_extra_neighbor
    (P : ExactTwoExtraNeighbors S i) {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    x = P.r \/ x = P.s :=
  P.all_mem x ((mem_extraNeighborFinset S i x).2 ⟨hadj, hnot⟩)

/-- The concrete extra-neighbor finset is exactly the two chosen witnesses. -/
theorem extraNeighborFinset_eq_pair
    (P : ExactTwoExtraNeighbors S i) :
    extraNeighborFinset S i = ({P.r, P.s} : Finset (Fin n)) := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    rcases P.all_mem x hx with h | h
    · simp [h]
    · simp [h]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · simpa [h] using P.r_mem
    · simpa [h] using P.s_mem

/-- Membership in the extra-neighbor finset is the same as being one of the
two chosen witnesses. -/
theorem mem_extraNeighborFinset_iff_eq_pair
    (P : ExactTwoExtraNeighbors S i) (x : Fin n) :
    x ∈ extraNeighborFinset S i <-> x = P.r \/ x = P.s := by
  classical
  rw [P.extraNeighborFinset_eq_pair]
  simp

/-- Exact-two witness data certifies cardinality two of the concrete
extra-neighbor finset. -/
theorem extraNeighborFinset_card_eq_two
    (P : ExactTwoExtraNeighbors S i) :
    (extraNeighborFinset S i).card = 2 := by
  classical
  rw [P.extraNeighborFinset_eq_pair]
  simp [P.r_ne_s]

end ExactTwoExtraNeighbors

namespace FourForbiddenNeighborFrame

variable {i : M8ExtraIndex}

/-- Under degree six, a four-forbidden-neighbor frame canonically chooses the
two concrete extra neighbors. -/
def exactTwoExtraNeighbors_of_centerDegree_eq_six
    (F : FourForbiddenNeighborFrame S i)
    (hdegree : centerDegree S i = 6) :
    ExactTwoExtraNeighbors S i :=
  ExactTwoExtraNeighbors.of_card_eq_two
    (F.extraNeighborFinset_card_eq_two_of_centerDegree_eq_six hdegree)

/-- The canonical exact-two witnesses from a degree-six frame exhaust the
extra-neighbor finset. -/
theorem extraNeighborFinset_eq_pair_of_centerDegree_eq_six
    (F : FourForbiddenNeighborFrame S i)
    (hdegree : centerDegree S i = 6) :
    extraNeighborFinset S i =
      ({(F.exactTwoExtraNeighbors_of_centerDegree_eq_six hdegree).r,
        (F.exactTwoExtraNeighbors_of_centerDegree_eq_six hdegree).s} :
        Finset (Fin n)) :=
  (F.exactTwoExtraNeighbors_of_centerDegree_eq_six hdegree).extraNeighborFinset_eq_pair

end FourForbiddenNeighborFrame

/-- The finite existence conditions that exactly build
`M8Lemma8Combinatorics`: an ordered pair of extra neighbors for each `i`, plus
the geometric cyclic-order predicate for those chosen pairs. -/
structure M8Lemma8FiniteExistenceConditions
    (S : M8BoundarySpine H) where
  pair : forall i : M8ExtraIndex, ExactTwoExtraNeighbors S i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i ((pair i).s) ((pair i).r)
        (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)

namespace M8Lemma8FiniteExistenceConditions

/-- Build the original Lemma 8 combinatorics package from the exact finite
conditions. -/
def toLemma8Combinatorics
    (E : M8Lemma8FiniteExistenceConditions S) :
    M8Lemma8Combinatorics S where
  r := fun i => (E.pair i).r
  s := fun i => (E.pair i).s
  r_neighbor := fun i => (E.pair i).r_neighbor
  s_neighbor := fun i => (E.pair i).s_neighbor
  r_not_forbidden := fun i => (E.pair i).r_not_forbidden
  s_not_forbidden := fun i => (E.pair i).s_not_forbidden
  r_ne_s := fun i => (E.pair i).r_ne_s
  all_extra_neighbors_are_named := by
    intro i x hadj hnot
    exact (E.pair i).named_of_extra_neighbor hadj hnot
  positiveCyclicOrderAt := E.positiveCyclicOrderAt
  positiveCyclicOrder := E.positiveCyclicOrder

end M8Lemma8FiniteExistenceConditions

/-- Construct the finite conditions from exact cardinalities and a cyclic-order
choice for the generated ordered pairs. -/
def finiteExistenceConditions_of_card_eq_two
    (hcard : forall i : M8ExtraIndex,
      (extraNeighborFinset S i).card = 2)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Prop)
    (horder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i
          (ExactTwoExtraNeighbors.of_card_eq_two (S := S) (i := i)
            (hcard i)).s
          (ExactTwoExtraNeighbors.of_card_eq_two (S := S) (i := i)
            (hcard i)).r
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)) :
    M8Lemma8FiniteExistenceConditions S where
  pair := fun i => ExactTwoExtraNeighbors.of_card_eq_two (hcard i)
  positiveCyclicOrderAt := positiveCyclicOrderAt
  positiveCyclicOrder := horder

/-- Direct finite-condition constructor from the degree-six field and the
four-forbidden-neighbor frame family. -/
def finiteExistenceConditions_of_degreeSix_forbiddenFrame
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Prop)
    (horder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i
          (ExactTwoExtraNeighbors.of_card_eq_two
            ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
              (hdegree i))).s
          (ExactTwoExtraNeighbors.of_card_eq_two
            ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
              (hdegree i))).r
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)) :
    M8Lemma8FiniteExistenceConditions S :=
  finiteExistenceConditions_of_card_eq_two
    (fun i =>
      (forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
        (hdegree i))
    positiveCyclicOrderAt horder

/-- Direct adapter from degree-six/forbidden-frame data and the remaining
cyclic-order assertion to the original Lemma 8 combinatorics package. -/
def lemma8Combinatorics_of_degreeSix_forbiddenFrame
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Prop)
    (horder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i
          (ExactTwoExtraNeighbors.of_card_eq_two
            ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
              (hdegree i))).s
          (ExactTwoExtraNeighbors.of_card_eq_two
            ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
              (hdegree i))).r
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)) :
    M8Lemma8Combinatorics S :=
  (finiteExistenceConditions_of_degreeSix_forbiddenFrame
    hdegree forbiddenFrame positiveCyclicOrderAt horder).toLemma8Combinatorics

@[simp]
theorem lemma8Combinatorics_of_degreeSix_forbiddenFrame_r
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Prop)
    (horder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i
          (ExactTwoExtraNeighbors.of_card_eq_two
            ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
              (hdegree i))).s
          (ExactTwoExtraNeighbors.of_card_eq_two
            ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
              (hdegree i))).r
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i))
    (i : M8ExtraIndex) :
    (lemma8Combinatorics_of_degreeSix_forbiddenFrame
      hdegree forbiddenFrame positiveCyclicOrderAt horder).r i =
      (ExactTwoExtraNeighbors.of_card_eq_two
        ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
          (hdegree i))).r :=
  rfl

@[simp]
theorem lemma8Combinatorics_of_degreeSix_forbiddenFrame_s
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Prop)
    (horder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i
          (ExactTwoExtraNeighbors.of_card_eq_two
            ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
              (hdegree i))).s
          (ExactTwoExtraNeighbors.of_card_eq_two
            ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
              (hdegree i))).r
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i))
    (i : M8ExtraIndex) :
    (lemma8Combinatorics_of_degreeSix_forbiddenFrame
      hdegree forbiddenFrame positiveCyclicOrderAt horder).s i =
      (ExactTwoExtraNeighbors.of_card_eq_two
        ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
          (hdegree i))).s :=
  rfl

/-! ## Exact remaining existence conditions -/

/-- The exact missing payload needed by this finite file to construct the full
Lemma 8 package from the present boundary spine.

`centerDegreeSix` is the "at least two" side not provided by the current
`3..6` range.  `forbiddenFrame` is the adjacency/distinctness data needed to
turn degree six into "exactly two".  `positiveCyclicOrder` is the missing
rotation-system/geometric order choice.
-/
structure M8Lemma8MissingExistenceConditions
    (S : M8BoundarySpine H) where
  centerDegreeSix : forall i : M8ExtraIndex, centerDegree S i = 6
  forbiddenFrame : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i
        (ExactTwoExtraNeighbors.of_card_eq_two
          ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
            (centerDegreeSix i))).s
        (ExactTwoExtraNeighbors.of_card_eq_two
          ((forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
            (centerDegreeSix i))).r
        (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)

namespace M8Lemma8MissingExistenceConditions

theorem extraNeighborFinset_card_eq_two
    (E : M8Lemma8MissingExistenceConditions S)
    (i : M8ExtraIndex) :
    (extraNeighborFinset S i).card = 2 :=
  (E.forbiddenFrame i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
    (E.centerDegreeSix i)

def toFiniteExistenceConditions
    (E : M8Lemma8MissingExistenceConditions S) :
    M8Lemma8FiniteExistenceConditions S :=
  finiteExistenceConditions_of_card_eq_two
    E.extraNeighborFinset_card_eq_two E.positiveCyclicOrderAt
    E.positiveCyclicOrder

/-- The exact missing conditions are sufficient for
`M8Lemma8Combinatorics`. -/
def toLemma8Combinatorics
    (E : M8Lemma8MissingExistenceConditions S) :
    M8Lemma8Combinatorics S :=
  E.toFiniteExistenceConditions.toLemma8Combinatorics

end M8Lemma8MissingExistenceConditions

end

end Lemma8ExistenceConcrete
end Swanepoel
end ErdosProblems1066
