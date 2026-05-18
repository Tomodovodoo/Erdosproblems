import ErdosProblems1066.Swanepoel.Lemma8ForbiddenDistinctConcrete
import ErdosProblems1066.Swanepoel.M8BoundaryLabelsConcrete

set_option autoImplicit false

/-!
# Concrete helpers for Lemma 8 combinatorics

This module is a standalone projection layer around
`M8LabelsFromBoundaryInterface.M8Lemma8Combinatorics`.  It proves only finite
bookkeeping facts from the explicit Lemma 8 package: named-neighbor
projections, adjacency symmetry routes, exhaustive reducers for extra
neighbors, and cyclic-order routing through the label packages.

The paper content remains exactly the data fields of `M8Lemma8Combinatorics`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8CombinatoricsConcrete

open GraphBridge
open Lemma8ExistenceConcrete
open Lemma8ForbiddenDistinctConcrete
open LocalConfigurations
open M8BoundaryLabelsConcrete
open M8LabelsFromBoundaryInterface

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-! ## Basic field projections -/

/-- Projection of the named `r_i` neighbor field. -/
theorem r_neighbor
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (E.r i) :=
  E.r_neighbor i

/-- Projection of the named `s_i` neighbor field. -/
theorem s_neighbor
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (E.s i) :=
  E.s_neighbor i

/-- Projection of the `r_i` non-forbidden field. -/
theorem r_not_forbidden
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (E.r i)) :=
  E.r_not_forbidden i

/-- Projection of the `s_i` non-forbidden field. -/
theorem s_not_forbidden
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (E.s i)) :=
  E.s_not_forbidden i

/-- Projection of the distinctness of the two named extra neighbors. -/
theorem r_ne_s
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.r i = E.s i) :=
  E.r_ne_s i

/-- The reverse distinctness of the two named extra neighbors. -/
theorem s_ne_r
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.s i = E.r i) := by
  intro h
  exact E.r_ne_s i h.symm

/-! ## Symmetric adjacency routes -/

/-- Adjacency to the central vertex can be reversed. -/
theorem centerQ_adj_comm
    (i : M8ExtraIndex) (x : Fin n) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) x <->
      (unitDistanceLocalGraph C).Adj x (S.centerQ i) :=
  Iff.intro
    (fun h => (unitDistanceLocalGraph C).symm h)
    (fun h => (unitDistanceLocalGraph C).symm h)

/-- Symmetric form of the `r_i` neighbor field. -/
theorem r_adj_centerQ
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (E.r i) (S.centerQ i) :=
  (unitDistanceLocalGraph C).symm (E.r_neighbor i)

/-- Symmetric form of the `s_i` neighbor field. -/
theorem s_adj_centerQ
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (E.s i) (S.centerQ i) :=
  (unitDistanceLocalGraph C).symm (E.s_neighbor i)

/-- Exhaustiveness also applies when the adjacency is supplied in the reverse
orientation. -/
theorem named_of_extra_neighbor_symm
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj x (S.centerQ i))
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    x = E.r i \/ x = E.s i :=
  E.named_of_extra_neighbor ((unitDistanceLocalGraph C).symm hadj) hnot

/-! ## Non-forbidden component projections -/

/-- `r_i` is not the left boundary endpoint. -/
theorem r_ne_leftP
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.r i = S.leftP i) := by
  intro h
  exact E.r_not_forbidden i (Or.inl h)

/-- `r_i` is not the right boundary endpoint. -/
theorem r_ne_rightP
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.r i = S.rightP i) := by
  intro h
  exact E.r_not_forbidden i (Or.inr (Or.inl h))

/-- `r_i` is not the previous common-neighbor label. -/
theorem r_ne_prevQ
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.r i = S.prevQ i) := by
  intro h
  exact E.r_not_forbidden i (Or.inr (Or.inr (Or.inl h)))

/-- `r_i` is not the next common-neighbor label. -/
theorem r_ne_nextQ
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.r i = S.nextQ i) := by
  intro h
  exact E.r_not_forbidden i (Or.inr (Or.inr (Or.inr h)))

/-- `s_i` is not the left boundary endpoint. -/
theorem s_ne_leftP
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.s i = S.leftP i) := by
  intro h
  exact E.s_not_forbidden i (Or.inl h)

/-- `s_i` is not the right boundary endpoint. -/
theorem s_ne_rightP
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.s i = S.rightP i) := by
  intro h
  exact E.s_not_forbidden i (Or.inr (Or.inl h))

/-- `s_i` is not the previous common-neighbor label. -/
theorem s_ne_prevQ
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.s i = S.prevQ i) := by
  intro h
  exact E.s_not_forbidden i (Or.inr (Or.inr (Or.inl h)))

/-- `s_i` is not the next common-neighbor label. -/
theorem s_ne_nextQ
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    Not (E.s i = S.nextQ i) := by
  intro h
  exact E.s_not_forbidden i (Or.inr (Or.inr (Or.inr h)))

/-! ## Exhaustive named-neighbor reducers -/

/-- An extra neighbor different from `s_i` must be `r_i`. -/
theorem eq_r_of_extra_neighbor_ne_s
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x))
    (hne : Not (x = E.s i)) :
    x = E.r i := by
  cases E.named_of_extra_neighbor hadj hnot with
  | inl h => exact h
  | inr h => exact False.elim (hne h)

/-- An extra neighbor different from `r_i` must be `s_i`. -/
theorem eq_s_of_extra_neighbor_ne_r
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x))
    (hne : Not (x = E.r i)) :
    x = E.s i := by
  cases E.named_of_extra_neighbor hadj hnot with
  | inl h => exact False.elim (hne h)
  | inr h => exact h

/-- Reverse-adjacency version of the `r_i` reducer. -/
theorem eq_r_of_extra_neighbor_symm_ne_s
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj x (S.centerQ i))
    (hnot : Not (S.forbiddenExtraNeighbor i x))
    (hne : Not (x = E.s i)) :
    x = E.r i :=
  eq_r_of_extra_neighbor_ne_s E
    ((unitDistanceLocalGraph C).symm hadj) hnot hne

/-- Reverse-adjacency version of the `s_i` reducer. -/
theorem eq_s_of_extra_neighbor_symm_ne_r
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj x (S.centerQ i))
    (hnot : Not (S.forbiddenExtraNeighbor i x))
    (hne : Not (x = E.r i)) :
    x = E.s i :=
  eq_s_of_extra_neighbor_ne_r E
    ((unitDistanceLocalGraph C).symm hadj) hnot hne

/-- For an extra neighbor, being different from `s_i` is equivalent to being
`r_i`. -/
theorem extra_neighbor_ne_s_iff_eq_r
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    Not (x = E.s i) <-> x = E.r i :=
  Iff.intro
    (fun hne => eq_r_of_extra_neighbor_ne_s E hadj hnot hne)
    (fun hx hxs => E.r_ne_s i (hx.symm.trans hxs))

/-- For an extra neighbor, being different from `r_i` is equivalent to being
`s_i`. -/
theorem extra_neighbor_ne_r_iff_eq_s
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    Not (x = E.r i) <-> x = E.s i :=
  Iff.intro
    (fun hne => eq_s_of_extra_neighbor_ne_r E hadj hnot hne)
    (fun hx hxr => E.r_ne_s i (hxr.symm.trans hx))

/-- There is no third extra neighbor distinct from both named ones. -/
theorem false_of_extra_neighbor_ne_r_ne_s
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x))
    (hne_r : Not (x = E.r i))
    (hne_s : Not (x = E.s i)) :
    False :=
  hne_r (eq_r_of_extra_neighbor_ne_s E hadj hnot hne_s)

/-- Equality with `r_i` follows from eliminating the `s_i` branch of the named
case split. -/
theorem named_cases_reduce_to_r
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hnamed : x = E.r i \/ x = E.s i)
    (hne : Not (x = E.s i)) :
    x = E.r i := by
  cases hnamed with
  | inl h => exact h
  | inr h => exact False.elim (hne h)

/-- Equality with `s_i` follows from eliminating the `r_i` branch of the named
case split. -/
theorem named_cases_reduce_to_s
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hnamed : x = E.r i \/ x = E.s i)
    (hne : Not (x = E.r i)) :
    x = E.s i := by
  cases hnamed with
  | inl h => exact False.elim (hne h)
  | inr h => exact h

/-! ## Degree-six and forbidden-frame closure -/

/-- The exact ordered pair of extra neighbors determined by a Lemma 8 package.
-/
def exactTwoExtraNeighbors_of_combinatorics
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    ExactTwoExtraNeighbors S i where
  r := E.r i
  s := E.s i
  r_mem := by
    exact (mem_extraNeighborFinset S i (E.r i)).2
      (And.intro (E.r_neighbor i) (E.r_not_forbidden i))
  s_mem := by
    exact (mem_extraNeighborFinset S i (E.s i)).2
      (And.intro (E.s_neighbor i) (E.s_not_forbidden i))
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

/-- Lemma 8 combinatorics, viewed as the finite-existence package with the
same ordered labels and cyclic-order predicate. -/
def finiteExistenceConditions_of_combinatorics
    (E : M8Lemma8Combinatorics S) :
    M8Lemma8FiniteExistenceConditions S where
  pair := fun i => exactTwoExtraNeighbors_of_combinatorics E i
  positiveCyclicOrderAt := E.positiveCyclicOrderAt
  positiveCyclicOrder := E.positiveCyclicOrder

@[simp]
theorem finiteExistenceConditions_of_combinatorics_pair_r
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    ((finiteExistenceConditions_of_combinatorics E).pair i).r = E.r i :=
  rfl

@[simp]
theorem finiteExistenceConditions_of_combinatorics_pair_s
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    ((finiteExistenceConditions_of_combinatorics E).pair i).s = E.s i :=
  rfl

/-- The concrete extra-neighbor finset is exactly the two Lemma 8 labels. -/
theorem extraNeighborFinset_eq_pair_of_combinatorics
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    extraNeighborFinset S i = ({E.r i, E.s i} : Finset (Fin n)) := by
  classical
  refine Finset.Subset.antisymm ?subset ?supset
  case subset =>
    intro x hx
    cases (exactTwoExtraNeighbors_of_combinatorics E i).all_mem x hx with
    | inl h => simp [h]
    | inr h => simp [h]
  case supset =>
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    cases hx with
    | inl h =>
        subst x
        exact (exactTwoExtraNeighbors_of_combinatorics E i).r_mem
    | inr h =>
        subst x
        exact (exactTwoExtraNeighbors_of_combinatorics E i).s_mem

/-- Lemma 8 combinatorics makes the concrete extra-neighbor finset have
cardinality two. -/
theorem extraNeighborFinset_card_eq_two_of_combinatorics
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (extraNeighborFinset S i).card = 2 := by
  classical
  rw [extraNeighborFinset_eq_pair_of_combinatorics E i]
  simp [E.r_ne_s i]

/-- A negated cardinality-two conclusion contradicts the stored Lemma 8
combinatorics. -/
theorem false_of_extraNeighborFinset_card_ne_two_of_combinatorics
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex)
    (hne : Not ((extraNeighborFinset S i).card = 2)) :
    False :=
  hne (extraNeighborFinset_card_eq_two_of_combinatorics E i)

/-- Lemma 8 combinatorics plus a genuine four-forbidden-neighbor frame forces
degree six at the center. -/
theorem centerDegree_eq_six_of_combinatorics_and_forbiddenFrame
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame S i) :
    centerDegree S i = 6 := by
  have hcard := extraNeighborFinset_card_eq_two_of_combinatorics E i
  have hdecomp : centerDegree S i = 4 + (extraNeighborFinset S i).card := by
    have hneighbor := F.neighborFinset_card_eq_forbidden_add_extra
    have hforbidden := F.forbidden_card_eq_four
    simpa [centerDegree, LocalExclusions.LocalGraph.degree, hforbidden]
      using hneighbor
  omega

/-- The combined degree-six and exact-pair conclusion from Lemma 8
combinatorics plus the forbidden-neighbor frame. -/
theorem centerDegree_eq_six_and_extraNeighborFinset_eq_pair_of_combinatorics_and_forbiddenFrame
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame S i) :
    centerDegree S i = 6 /\
      extraNeighborFinset S i = ({E.r i, E.s i} : Finset (Fin n)) :=
  And.intro
    (centerDegree_eq_six_of_combinatorics_and_forbiddenFrame E F)
    (extraNeighborFinset_eq_pair_of_combinatorics E i)

/-- A negated center-degree-six conclusion contradicts Lemma 8 combinatorics
and the forbidden-neighbor frame. -/
theorem false_of_centerDegree_ne_six_of_combinatorics_and_forbiddenFrame
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame S i)
    (hne : Not (centerDegree S i = 6)) :
    False :=
  hne (centerDegree_eq_six_of_combinatorics_and_forbiddenFrame E F)

/-- The forbidden-neighbor frame also gives the compact pairwise-distinct
forbidden-label package used by cyclic-order consumers. -/
theorem forbiddenLabelsPairwiseDistinct_of_forbiddenFrame
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame S i) :
    FourForbiddenLabelsPairwiseDistinct S i :=
  FourForbiddenLabelsPairwiseDistinct.ofFrame F

/-! ## Cyclic-order field routing -/

/-- The cyclic-order field as a reusable routed proposition. -/
def cyclicOrderRoute
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) : Prop :=
  E.positiveCyclicOrderAt i (E.s i) (E.r i)
    (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)

/-- The routed cyclic-order proposition is exactly the stored field. -/
theorem cyclicOrderRoute_holds
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    cyclicOrderRoute E i :=
  E.positiveCyclicOrder i

/-- Distinctness facts for the six arguments in the routed cyclic-order
statement, with the forbidden-label distinctness kept as one compact field. -/
structure CyclicOrderArgumentsDistinct
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) : Prop where
  s_ne_r : Not (E.s i = E.r i)
  s_ne_prevQ : Not (E.s i = S.prevQ i)
  s_ne_leftP : Not (E.s i = S.leftP i)
  s_ne_rightP : Not (E.s i = S.rightP i)
  s_ne_nextQ : Not (E.s i = S.nextQ i)
  r_ne_prevQ : Not (E.r i = S.prevQ i)
  r_ne_leftP : Not (E.r i = S.leftP i)
  r_ne_rightP : Not (E.r i = S.rightP i)
  r_ne_nextQ : Not (E.r i = S.nextQ i)
  forbiddenDistinct : FourForbiddenLabelsPairwiseDistinct S i

/-- Build the cyclic-order argument distinctness package from Lemma 8
non-forbidden fields and a forbidden-label distinctness certificate. -/
theorem cyclicOrderArgumentsDistinct_of_forbiddenDistinct
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex}
    (D : FourForbiddenLabelsPairwiseDistinct S i) :
    CyclicOrderArgumentsDistinct E i where
  s_ne_r := Lemma8CombinatoricsConcrete.s_ne_r E i
  s_ne_prevQ := Lemma8CombinatoricsConcrete.s_ne_prevQ E i
  s_ne_leftP := Lemma8CombinatoricsConcrete.s_ne_leftP E i
  s_ne_rightP := Lemma8CombinatoricsConcrete.s_ne_rightP E i
  s_ne_nextQ := Lemma8CombinatoricsConcrete.s_ne_nextQ E i
  r_ne_prevQ := Lemma8CombinatoricsConcrete.r_ne_prevQ E i
  r_ne_leftP := Lemma8CombinatoricsConcrete.r_ne_leftP E i
  r_ne_rightP := Lemma8CombinatoricsConcrete.r_ne_rightP E i
  r_ne_nextQ := Lemma8CombinatoricsConcrete.r_ne_nextQ E i
  forbiddenDistinct := D

/-- The forbidden-neighbor frame is enough to build the cyclic-order argument
distinctness package. -/
theorem cyclicOrderArgumentsDistinct_of_forbiddenFrame
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame S i) :
    CyclicOrderArgumentsDistinct E i :=
  cyclicOrderArgumentsDistinct_of_forbiddenDistinct E
    (forbiddenLabelsPairwiseDistinct_of_forbiddenFrame F)

/-- The compact per-index closure facts obtained by combining cyclic order,
degree six, and forbidden distinctness. -/
structure M8Lemma8IndexClosureFacts
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) : Prop where
  centerDegreeSix : centerDegree S i = 6
  extraNeighborCardTwo : (extraNeighborFinset S i).card = 2
  cyclicOrder : cyclicOrderRoute E i
  argumentsDistinct : CyclicOrderArgumentsDistinct E i

/-- Build the compact per-index closure facts from a Lemma 8 package and the
four-forbidden-neighbor frame. -/
theorem indexClosureFacts_of_combinatorics_and_forbiddenFrame
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame S i) :
    M8Lemma8IndexClosureFacts E i where
  centerDegreeSix :=
    centerDegree_eq_six_of_combinatorics_and_forbiddenFrame E F
  extraNeighborCardTwo :=
    extraNeighborFinset_card_eq_two_of_combinatorics E i
  cyclicOrder := cyclicOrderRoute_holds E i
  argumentsDistinct :=
    cyclicOrderArgumentsDistinct_of_forbiddenFrame E F

/-- A failure of the compact closure facts is already a contradiction once the
Lemma 8 package and forbidden-neighbor frame are supplied. -/
theorem false_of_not_indexClosureFacts_of_combinatorics_and_forbiddenFrame
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame S i)
    (hbad : Not (M8Lemma8IndexClosureFacts E i)) :
    False :=
  hbad (indexClosureFacts_of_combinatorics_and_forbiddenFrame E F)

/-- Witness version of the per-index closure: the exact extra-neighbor pair is
kept together with the combined closure facts. -/
structure M8Lemma8IndexClosureWitness
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) where
  pair : ExactTwoExtraNeighbors S i
  pair_r : pair.r = E.r i
  pair_s : pair.s = E.s i
  facts : M8Lemma8IndexClosureFacts E i

/-- Build the per-index closure witness from Lemma 8 combinatorics and a
forbidden-neighbor frame. -/
def indexClosureWitness_of_combinatorics_and_forbiddenFrame
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame S i) :
    M8Lemma8IndexClosureWitness E i where
  pair := exactTwoExtraNeighbors_of_combinatorics E i
  pair_r := rfl
  pair_s := rfl
  facts := indexClosureFacts_of_combinatorics_and_forbiddenFrame E F

/-- Family version of the closure witness over all Lemma 8 indices. -/
structure M8Lemma8ClosureWitness
    (E : M8Lemma8Combinatorics S) where
  index : forall i : M8ExtraIndex, M8Lemma8IndexClosureWitness E i

/-- Build all per-index closure witnesses from a frame family. -/
def closureWitness_of_combinatorics_and_forbiddenFrame
    (E : M8Lemma8Combinatorics S)
    (F : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i) :
    M8Lemma8ClosureWitness E where
  index := fun i =>
    indexClosureWitness_of_combinatorics_and_forbiddenFrame E (F i)

namespace M8LabelsFromBoundaryData

variable (D : M8LabelsFromBoundaryData C)

/-- Route Lemma 8 cyclic order through the raw broken-lattice labels. -/
theorem positiveCyclicOrder_labels
    (i : M8ExtraIndex) :
    D.lemma8.positiveCyclicOrderAt i
      (D.labels.s i) (D.labels.r i)
      (D.spine.prevQ i) (D.spine.leftP i)
      (D.spine.rightP i) (D.spine.nextQ i) := by
  simpa [M8LabelsFromBoundaryData.labels] using
    D.lemma8.positiveCyclicOrder_holds i

/-- Route Lemma 8 cyclic order through the predicate package labels. -/
theorem positiveCyclicOrder_predicateLabels
    (i : M8ExtraIndex) :
    D.lemma8.positiveCyclicOrderAt i
      (D.predicates.labels.s i) (D.predicates.labels.r i)
      (D.spine.prevQ i) (D.spine.leftP i)
      (D.spine.rightP i) (D.spine.nextQ i) := by
  simpa [M8LabelsFromBoundaryData.predicates,
    M8LabelsFromBoundaryData.labels] using
    D.lemma8.positiveCyclicOrder_holds i

/-- Route the exhaustiveness reducer through boundary-derived data. -/
theorem eq_r_of_extra_neighbor_ne_s
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (D.spine.centerQ i) x)
    (hnot : Not (D.spine.forbiddenExtraNeighbor i x))
    (hne : Not (x = D.labels.s i)) :
    x = D.labels.r i := by
  simpa [M8LabelsFromBoundaryData.labels] using
    Lemma8CombinatoricsConcrete.eq_r_of_extra_neighbor_ne_s
      D.lemma8 hadj hnot hne

/-- Route the symmetric exhaustiveness reducer through boundary-derived data. -/
theorem eq_s_of_extra_neighbor_ne_r
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (D.spine.centerQ i) x)
    (hnot : Not (D.spine.forbiddenExtraNeighbor i x))
    (hne : Not (x = D.labels.r i)) :
    x = D.labels.s i := by
  simpa [M8LabelsFromBoundaryData.labels] using
    Lemma8CombinatoricsConcrete.eq_s_of_extra_neighbor_ne_r
      D.lemma8 hadj hnot hne

/-- Route the exact extra-neighbor pair through boundary-derived data. -/
def exactTwoExtraNeighbors
    (i : M8ExtraIndex) :
    ExactTwoExtraNeighbors D.spine i :=
  Lemma8CombinatoricsConcrete.exactTwoExtraNeighbors_of_combinatorics
    D.lemma8 i

/-- Route the compact closure facts through boundary-derived data. -/
theorem indexClosureFacts_of_forbiddenFrame
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame D.spine i) :
    M8Lemma8IndexClosureFacts D.lemma8 i :=
  Lemma8CombinatoricsConcrete.indexClosureFacts_of_combinatorics_and_forbiddenFrame
    D.lemma8 F

/-- Route the compact closure witness through boundary-derived data. -/
def indexClosureWitness_of_forbiddenFrame
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame D.spine i) :
    M8Lemma8IndexClosureWitness D.lemma8 i :=
  Lemma8CombinatoricsConcrete.indexClosureWitness_of_combinatorics_and_forbiddenFrame
    D.lemma8 F

/-- Route the all-index closure witness through boundary-derived data. -/
def closureWitness_of_forbiddenFrame
    (F : forall i : M8ExtraIndex, FourForbiddenNeighborFrame D.spine i) :
    M8Lemma8ClosureWitness D.lemma8 :=
  Lemma8CombinatoricsConcrete.closureWitness_of_combinatorics_and_forbiddenFrame
    D.lemma8 F

end M8LabelsFromBoundaryData

namespace M8BoundaryLabelPackage

variable (D : M8BoundaryLabelPackage C)

/-- Route Lemma 8 cyclic order through the concrete boundary-label package. -/
theorem positiveCyclicOrder_labels
    (i : M8ExtraIndex) :
    D.lemma8.positiveCyclicOrderAt i
      (D.labels.s i) (D.labels.r i)
      (D.spine.prevQ i) (D.spine.leftP i)
      (D.spine.rightP i) (D.spine.nextQ i) := by
  simpa [M8BoundaryLabelPackage.labels,
    M8BoundaryLabelPackage.toLabelsFromBoundaryData,
    M8LabelsFromBoundaryData.labels] using
    D.lemma8.positiveCyclicOrder_holds i

/-- Route Lemma 8 cyclic order through the concrete predicate package labels. -/
theorem positiveCyclicOrder_predicateLabels
    (i : M8ExtraIndex) :
    D.lemma8.positiveCyclicOrderAt i
      (D.predicates.data.labels.s i) (D.predicates.data.labels.r i)
      (D.spine.prevQ i) (D.spine.leftP i)
      (D.spine.rightP i) (D.spine.nextQ i) := by
  simpa [M8BoundaryLabelPackage.predicates,
    M8BoundaryLabelPackage.toLabelsFromBoundaryData,
    M8LabelsFromBoundaryData.toHonestLocalPredicates,
    M8LabelsFromBoundaryData.predicates,
    M8LabelsFromBoundaryData.labels] using
    D.lemma8.positiveCyclicOrder_holds i

/-- Route the `r_i` exhaustive reducer through the concrete boundary-label
package. -/
theorem eq_r_of_extra_neighbor_ne_s
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (D.spine.centerQ i) x)
    (hnot : Not (D.spine.forbiddenExtraNeighbor i x))
    (hne : Not (x = D.labels.s i)) :
    x = D.labels.r i := by
  simpa [M8BoundaryLabelPackage.labels,
    M8BoundaryLabelPackage.toLabelsFromBoundaryData,
    M8LabelsFromBoundaryData.labels] using
    Lemma8CombinatoricsConcrete.eq_r_of_extra_neighbor_ne_s
      D.lemma8 hadj hnot hne

/-- Route the `s_i` exhaustive reducer through the concrete boundary-label
package. -/
theorem eq_s_of_extra_neighbor_ne_r
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (D.spine.centerQ i) x)
    (hnot : Not (D.spine.forbiddenExtraNeighbor i x))
    (hne : Not (x = D.labels.r i)) :
    x = D.labels.s i := by
  simpa [M8BoundaryLabelPackage.labels,
    M8BoundaryLabelPackage.toLabelsFromBoundaryData,
    M8LabelsFromBoundaryData.labels] using
    Lemma8CombinatoricsConcrete.eq_s_of_extra_neighbor_ne_r
      D.lemma8 hadj hnot hne

/-- Route the exact extra-neighbor pair through the concrete boundary-label
package. -/
def exactTwoExtraNeighbors
    (i : M8ExtraIndex) :
    ExactTwoExtraNeighbors D.spine i :=
  Lemma8CombinatoricsConcrete.exactTwoExtraNeighbors_of_combinatorics
    D.lemma8 i

/-- Route the compact closure facts through the concrete boundary-label
package. -/
theorem indexClosureFacts_of_forbiddenFrame
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame D.spine i) :
    M8Lemma8IndexClosureFacts D.lemma8 i :=
  Lemma8CombinatoricsConcrete.indexClosureFacts_of_combinatorics_and_forbiddenFrame
    D.lemma8 F

/-- Route the compact closure witness through the concrete boundary-label
package. -/
def indexClosureWitness_of_forbiddenFrame
    {i : M8ExtraIndex}
    (F : FourForbiddenNeighborFrame D.spine i) :
    M8Lemma8IndexClosureWitness D.lemma8 i :=
  Lemma8CombinatoricsConcrete.indexClosureWitness_of_combinatorics_and_forbiddenFrame
    D.lemma8 F

/-- Route the all-index closure witness through the concrete boundary-label
package. -/
def closureWitness_of_forbiddenFrame
    (F : forall i : M8ExtraIndex, FourForbiddenNeighborFrame D.spine i) :
    M8Lemma8ClosureWitness D.lemma8 :=
  Lemma8CombinatoricsConcrete.closureWitness_of_combinatorics_and_forbiddenFrame
    D.lemma8 F

end M8BoundaryLabelPackage

end

end Lemma8CombinatoricsConcrete
end Swanepoel
end ErdosProblems1066
