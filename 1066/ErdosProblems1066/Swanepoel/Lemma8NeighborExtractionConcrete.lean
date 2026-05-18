import ErdosProblems1066.Swanepoel.BoundarySpineConcrete
import ErdosProblems1066.Swanepoel.Lemma8CombinatoricsConcrete
import ErdosProblems1066.Swanepoel.Lemma8ExistenceConcrete
import ErdosProblems1066.Swanepoel.LocalExclusions
import ErdosProblems1066.Swanepoel.MinimalFailureLocalExclusions

set_option autoImplicit false

/-!
# Concrete extraction of the Lemma 8 extra-neighbor package

This file separates the non-cyclic `r_i, s_i` neighbor data from the remaining
cyclic-order assertion in the `m = 8` boundary route.

The checked content is deliberately finite and local:
* a concrete record for the named extra neighbors and their exhaustiveness;
* projections and local degree consequences for the named neighbors;
* the smallest cyclic-order record needed to assemble
  `M8Lemma8Combinatorics`;
* routing through the planar boundary-spine skeleton from
  `BoundarySpineConcrete`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8NeighborExtractionConcrete

open BoundarySpineConcrete
open BoundaryFaceCountingToM8
open GraphBridge
open Lemma8CombinatoricsConcrete
open Lemma8ExistenceConcrete
open LocalConfigurations
open M8BoundaryLabelsConcrete
open M8LabelsFromBoundaryInterface

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-! ## The non-cyclic extra-neighbor package -/

/--
The part of Lemma 8 that names the two extra neighbors of each `q_i`, before
any cyclic-order claim is attached.
-/
structure M8ExtraNeighborData
    {n : Nat} {C : _root_.UDConfig n}
    {H : M8BoundaryCutDegreeContext C}
    (S : M8BoundarySpine H) where
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

namespace M8ExtraNeighborData

variable (D : M8ExtraNeighborData S)

/-- The local witness predicate already used by the downstream label package. -/
def extraNeighborWitness (i : M8ExtraIndex) : Prop :=
  (unitDistanceLocalGraph C).Adj (S.centerQ i) (D.r i) /\
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (D.s i) /\
    Not (S.forbiddenExtraNeighbor i (D.r i)) /\
    Not (S.forbiddenExtraNeighbor i (D.s i)) /\
    Not (D.r i = D.s i)

theorem extraNeighborWitness_holds (i : M8ExtraIndex) :
    D.extraNeighborWitness i :=
  And.intro (D.r_neighbor i)
    (And.intro (D.s_neighbor i)
      (And.intro (D.r_not_forbidden i)
        (And.intro (D.s_not_forbidden i) (D.r_ne_s i))))

/-- Projection of the named `r_i` neighbor field. -/
theorem r_neighbor_holds (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (D.r i) :=
  D.r_neighbor i

/-- Projection of the named `s_i` neighbor field. -/
theorem s_neighbor_holds (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (D.s i) :=
  D.s_neighbor i

/-- Symmetric form of the `r_i` neighbor field. -/
theorem r_adj_centerQ (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (D.r i) (S.centerQ i) :=
  (unitDistanceLocalGraph C).symm (D.r_neighbor i)

/-- Symmetric form of the `s_i` neighbor field. -/
theorem s_adj_centerQ (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (D.s i) (S.centerQ i) :=
  (unitDistanceLocalGraph C).symm (D.s_neighbor i)

/-- Projection of the `r_i` non-forbidden field. -/
theorem r_not_forbidden_holds (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (D.r i)) :=
  D.r_not_forbidden i

/-- Projection of the `s_i` non-forbidden field. -/
theorem s_not_forbidden_holds (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (D.s i)) :=
  D.s_not_forbidden i

/-- Projection of the distinctness of the two named extra neighbors. -/
theorem r_ne_s_holds (i : M8ExtraIndex) :
    Not (D.r i = D.s i) :=
  D.r_ne_s i

/-- The two named extra neighbors are distinct in the reverse direction. -/
theorem s_ne_r_holds (i : M8ExtraIndex) :
    Not (D.s i = D.r i) := by
  intro h
  exact D.r_ne_s i h.symm

/-- `r_i` is not the left boundary endpoint. -/
theorem r_ne_leftP (i : M8ExtraIndex) :
    Not (D.r i = S.leftP i) :=
  BoundaryLabelExtractionTasks.M8BoundarySpine.ne_leftP_of_not_forbidden
    S (D.r_not_forbidden i)

/-- `r_i` is not the right boundary endpoint. -/
theorem r_ne_rightP (i : M8ExtraIndex) :
    Not (D.r i = S.rightP i) :=
  BoundaryLabelExtractionTasks.M8BoundarySpine.ne_rightP_of_not_forbidden
    S (D.r_not_forbidden i)

/-- `r_i` is not the previous common-neighbor label. -/
theorem r_ne_prevQ (i : M8ExtraIndex) :
    Not (D.r i = S.prevQ i) :=
  BoundaryLabelExtractionTasks.M8BoundarySpine.ne_prevQ_of_not_forbidden
    S (D.r_not_forbidden i)

/-- `r_i` is not the next common-neighbor label. -/
theorem r_ne_nextQ (i : M8ExtraIndex) :
    Not (D.r i = S.nextQ i) :=
  BoundaryLabelExtractionTasks.M8BoundarySpine.ne_nextQ_of_not_forbidden
    S (D.r_not_forbidden i)

/-- `s_i` is not the left boundary endpoint. -/
theorem s_ne_leftP (i : M8ExtraIndex) :
    Not (D.s i = S.leftP i) :=
  BoundaryLabelExtractionTasks.M8BoundarySpine.ne_leftP_of_not_forbidden
    S (D.s_not_forbidden i)

/-- `s_i` is not the right boundary endpoint. -/
theorem s_ne_rightP (i : M8ExtraIndex) :
    Not (D.s i = S.rightP i) :=
  BoundaryLabelExtractionTasks.M8BoundarySpine.ne_rightP_of_not_forbidden
    S (D.s_not_forbidden i)

/-- `s_i` is not the previous common-neighbor label. -/
theorem s_ne_prevQ (i : M8ExtraIndex) :
    Not (D.s i = S.prevQ i) :=
  BoundaryLabelExtractionTasks.M8BoundarySpine.ne_prevQ_of_not_forbidden
    S (D.s_not_forbidden i)

/-- `s_i` is not the next common-neighbor label. -/
theorem s_ne_nextQ (i : M8ExtraIndex) :
    Not (D.s i = S.nextQ i) :=
  BoundaryLabelExtractionTasks.M8BoundarySpine.ne_nextQ_of_not_forbidden
    S (D.s_not_forbidden i)

/-- Exhaustiveness projection: every non-forbidden neighbor is one of the two
named extra neighbors. -/
theorem named_of_extra_neighbor
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    x = D.r i \/ x = D.s i :=
  D.all_extra_neighbors_are_named i x hadj hnot

/-- Exhaustiveness also applies when adjacency is supplied in the reverse
orientation. -/
theorem named_of_extra_neighbor_symm
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj x (S.centerQ i))
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    x = D.r i \/ x = D.s i :=
  D.named_of_extra_neighbor ((unitDistanceLocalGraph C).symm hadj) hnot

/-- An extra neighbor different from `s_i` must be `r_i`. -/
theorem eq_r_of_extra_neighbor_ne_s
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x))
    (hne : Not (x = D.s i)) :
    x = D.r i := by
  cases D.named_of_extra_neighbor hadj hnot with
  | inl h => exact h
  | inr h => exact False.elim (hne h)

/-- An extra neighbor different from `r_i` must be `s_i`. -/
theorem eq_s_of_extra_neighbor_ne_r
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x))
    (hne : Not (x = D.r i)) :
    x = D.s i := by
  cases D.named_of_extra_neighbor hadj hnot with
  | inl h => exact False.elim (hne h)
  | inr h => exact h

/-- There is no third non-forbidden neighbor distinct from both named ones. -/
theorem false_of_extra_neighbor_ne_r_ne_s
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x))
    (hne_r : Not (x = D.r i))
    (hne_s : Not (x = D.s i)) :
    False :=
  hne_r (D.eq_r_of_extra_neighbor_ne_s hadj hnot hne_s)

/-- The named neighbor pair is a nonempty, explicit extraction result for
each extra index. -/
theorem exists_named_pair
    (D : M8ExtraNeighborData S) (i : M8ExtraIndex) :
    Exists fun r : Fin n =>
      Exists fun s : Fin n =>
        (unitDistanceLocalGraph C).Adj (S.centerQ i) r /\
        (unitDistanceLocalGraph C).Adj (S.centerQ i) s /\
        Not (S.forbiddenExtraNeighbor i r) /\
        Not (S.forbiddenExtraNeighbor i s) /\
        Not (r = s) :=
  Exists.intro (D.r i) <|
    Exists.intro (D.s i) <|
      And.intro (D.r_neighbor i) <|
        And.intro (D.s_neighbor i) <|
          And.intro (D.r_not_forbidden i) <|
            And.intro (D.s_not_forbidden i) (D.r_ne_s i)

/-- The two named extra neighbors force degree at least two at the center. -/
theorem centerQ_degree_ge_two
    (D : M8ExtraNeighborData S) (i : M8ExtraIndex) :
    2 <=
      LocalExclusions.LocalGraph.degree (unitDistanceLocalGraph C)
        (S.centerQ i) :=
  LocalExclusions.LocalGraph.degree_ge_two_of_two_neighbors
    (unitDistanceLocalGraph C) (D.r_neighbor i) (D.s_neighbor i)
    (D.r_ne_s i)

/-- Together with the left boundary endpoint, a named `r_i` gives three
distinct neighbors of the central `q_i`. -/
theorem centerQ_degree_ge_three_left_r
    (D : M8ExtraNeighborData S) (i : M8ExtraIndex) :
    3 <=
      LocalExclusions.LocalGraph.degree (unitDistanceLocalGraph C)
        (S.centerQ i) := by
  have hleft_ne_r : Not (S.leftP i = D.r i) := by
    intro h
    exact D.r_ne_leftP i h.symm
  exact LocalExclusions.LocalGraph.degree_ge_three_of_three_neighbors
    (unitDistanceLocalGraph C)
    (M8BoundarySpine.centerQ_adj_leftP S i)
    (D.r_neighbor i)
    (D.s_neighbor i)
    hleft_ne_r
    (by
      intro h
      exact D.s_ne_leftP i h.symm)
    (D.r_ne_s i)

/-- The finite local degree bound in the boundary context is compatible with
the extracted named-neighbor pair. -/
theorem centerQ_degree_le_six
    (_D : M8ExtraNeighborData S) (i : M8ExtraIndex) :
    (DegreePipeline.unitDistanceNeighborSet C (S.centerQ i)).card <= 6 :=
  H.maxDegree (S.centerQ i)

/-! ## Isolating the remaining cyclic-order assertion -/

/--
The only cyclic-order input needed to turn the non-cyclic neighbor data into
`M8Lemma8Combinatorics`.
-/
structure CyclicOrder
    (D : M8ExtraNeighborData S) where
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i (D.s i) (D.r i) (S.prevQ i)
        (S.leftP i) (S.rightP i) (S.nextQ i)

namespace CyclicOrder

variable {D : M8ExtraNeighborData S}
variable (O : CyclicOrder D)

/-- Projection of the isolated cyclic-order predicate. -/
theorem positiveCyclicOrder_holds (i : M8ExtraIndex) :
    O.positiveCyclicOrderAt i (D.s i) (D.r i) (S.prevQ i)
      (S.leftP i) (S.rightP i) (S.nextQ i) :=
  O.positiveCyclicOrder i

end CyclicOrder

/-- Assemble the full Lemma 8 combinatorics package from non-cyclic neighbor
data plus the isolated cyclic-order record. -/
def toLemma8Combinatorics
    (O : CyclicOrder D) :
    M8Lemma8Combinatorics S where
  r := D.r
  s := D.s
  r_neighbor := D.r_neighbor
  s_neighbor := D.s_neighbor
  r_not_forbidden := D.r_not_forbidden
  s_not_forbidden := D.s_not_forbidden
  r_ne_s := D.r_ne_s
  all_extra_neighbors_are_named := D.all_extra_neighbors_are_named
  positiveCyclicOrderAt := O.positiveCyclicOrderAt
  positiveCyclicOrder := O.positiveCyclicOrder

@[simp]
theorem toLemma8Combinatorics_r
    (O : CyclicOrder D) (i : M8ExtraIndex) :
    (D.toLemma8Combinatorics O).r i = D.r i :=
  rfl

@[simp]
theorem toLemma8Combinatorics_s
    (O : CyclicOrder D) (i : M8ExtraIndex) :
    (D.toLemma8Combinatorics O).s i = D.s i :=
  rfl

@[simp]
theorem toLemma8Combinatorics_positiveCyclicOrderAt
    (O : CyclicOrder D) :
    (D.toLemma8Combinatorics O).positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

/-- The assembled package preserves the non-cyclic witness predicate. -/
theorem toLemma8Combinatorics_extraNeighborWitness
    (O : CyclicOrder D) (i : M8ExtraIndex) :
    (D.toLemma8Combinatorics O).extraNeighborWitness i :=
  D.extraNeighborWitness_holds i

/-- Convert an already supplied Lemma 8 package back to the non-cyclic record.
-/
def ofLemma8Combinatorics
    (E : M8Lemma8Combinatorics S) :
    M8ExtraNeighborData S where
  r := E.r
  s := E.s
  r_neighbor := E.r_neighbor
  s_neighbor := E.s_neighbor
  r_not_forbidden := E.r_not_forbidden
  s_not_forbidden := E.s_not_forbidden
  r_ne_s := E.r_ne_s
  all_extra_neighbors_are_named := E.all_extra_neighbors_are_named

/-- Extract the cyclic-order record from an already supplied Lemma 8 package.
-/
def cyclicOrderOfLemma8Combinatorics
    (E : M8Lemma8Combinatorics S) :
    CyclicOrder (ofLemma8Combinatorics E) where
  positiveCyclicOrderAt := E.positiveCyclicOrderAt
  positiveCyclicOrder := E.positiveCyclicOrder

@[simp]
theorem ofLemma8Combinatorics_r
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (ofLemma8Combinatorics E).r i = E.r i :=
  rfl

@[simp]
theorem ofLemma8Combinatorics_s
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (ofLemma8Combinatorics E).s i = E.s i :=
  rfl

/-- Existing Lemma 8 data decomposes into the new non-cyclic extraction record
and the minimal cyclic-order record. -/
theorem exists_extraction_and_cyclic_order
    (E : M8Lemma8Combinatorics S) :
    Exists fun D : M8ExtraNeighborData S => Nonempty (CyclicOrder D) :=
  Exists.intro (ofLemma8Combinatorics E) <|
    Nonempty.intro (cyclicOrderOfLemma8Combinatorics E)

/-! ## Adapters from concrete existence witnesses -/

/-- Convert a family of exact-two finite witnesses into the non-cyclic
neighbor-extraction record. -/
def ofExactTwoExtraNeighborFamily
    (P : forall i : M8ExtraIndex, ExactTwoExtraNeighbors S i) :
    M8ExtraNeighborData S where
  r := fun i => (P i).r
  s := fun i => (P i).s
  r_neighbor := fun i => (P i).r_neighbor
  s_neighbor := fun i => (P i).s_neighbor
  r_not_forbidden := fun i => (P i).r_not_forbidden
  s_not_forbidden := fun i => (P i).s_not_forbidden
  r_ne_s := fun i => (P i).r_ne_s
  all_extra_neighbors_are_named := fun i _x hadj hnot =>
    (P i).named_of_extra_neighbor hadj hnot

@[simp]
theorem ofExactTwoExtraNeighborFamily_r
    (P : forall i : M8ExtraIndex, ExactTwoExtraNeighbors S i)
    (i : M8ExtraIndex) :
    (ofExactTwoExtraNeighborFamily P).r i = (P i).r :=
  rfl

@[simp]
theorem ofExactTwoExtraNeighborFamily_s
    (P : forall i : M8ExtraIndex, ExactTwoExtraNeighbors S i)
    (i : M8ExtraIndex) :
    (ofExactTwoExtraNeighborFamily P).s i = (P i).s :=
  rfl

/-- Exact-two witness families still expose the local witness predicate after
conversion to neighbor-extraction data. -/
theorem ofExactTwoExtraNeighborFamily_extraNeighborWitness
    (P : forall i : M8ExtraIndex, ExactTwoExtraNeighbors S i)
    (i : M8ExtraIndex) :
    (ofExactTwoExtraNeighborFamily P).extraNeighborWitness i :=
  (ofExactTwoExtraNeighborFamily P).extraNeighborWitness_holds i

/-- Forget finite existence conditions to their non-cyclic extracted
neighbor data. -/
def ofFiniteExistenceConditions
    (E : M8Lemma8FiniteExistenceConditions S) :
    M8ExtraNeighborData S :=
  ofExactTwoExtraNeighborFamily E.pair

@[simp]
theorem ofFiniteExistenceConditions_r
    (E : M8Lemma8FiniteExistenceConditions S) (i : M8ExtraIndex) :
    (ofFiniteExistenceConditions E).r i = (E.pair i).r :=
  rfl

@[simp]
theorem ofFiniteExistenceConditions_s
    (E : M8Lemma8FiniteExistenceConditions S) (i : M8ExtraIndex) :
    (ofFiniteExistenceConditions E).s i = (E.pair i).s :=
  rfl

/-- Extract the cyclic-order record carried by finite existence conditions. -/
def cyclicOrderOfFiniteExistenceConditions
    (E : M8Lemma8FiniteExistenceConditions S) :
    CyclicOrder (ofFiniteExistenceConditions E) where
  positiveCyclicOrderAt := E.positiveCyclicOrderAt
  positiveCyclicOrder := E.positiveCyclicOrder

/-- Reassemble `M8Lemma8Combinatorics` through the neighbor-extraction
adapter from finite existence conditions. -/
def toLemma8CombinatoricsOfFiniteExistenceConditions
    (E : M8Lemma8FiniteExistenceConditions S) :
    M8Lemma8Combinatorics S :=
  (ofFiniteExistenceConditions E).toLemma8Combinatorics
    (cyclicOrderOfFiniteExistenceConditions E)

@[simp]
theorem toLemma8CombinatoricsOfFiniteExistenceConditions_r
    (E : M8Lemma8FiniteExistenceConditions S) (i : M8ExtraIndex) :
    (toLemma8CombinatoricsOfFiniteExistenceConditions E).r i =
      (E.pair i).r :=
  rfl

@[simp]
theorem toLemma8CombinatoricsOfFiniteExistenceConditions_s
    (E : M8Lemma8FiniteExistenceConditions S) (i : M8ExtraIndex) :
    (toLemma8CombinatoricsOfFiniteExistenceConditions E).s i =
      (E.pair i).s :=
  rfl

/-- Forget the exact missing-existence package to extracted non-cyclic
neighbor data. -/
def ofMissingExistenceConditions
    (E : M8Lemma8MissingExistenceConditions S) :
    M8ExtraNeighborData S :=
  ofFiniteExistenceConditions E.toFiniteExistenceConditions

@[simp]
theorem ofMissingExistenceConditions_r
    (E : M8Lemma8MissingExistenceConditions S) (i : M8ExtraIndex) :
    (ofMissingExistenceConditions E).r i =
      (E.toFiniteExistenceConditions.pair i).r :=
  rfl

@[simp]
theorem ofMissingExistenceConditions_s
    (E : M8Lemma8MissingExistenceConditions S) (i : M8ExtraIndex) :
    (ofMissingExistenceConditions E).s i =
      (E.toFiniteExistenceConditions.pair i).s :=
  rfl

/-- Extract the cyclic-order record carried by the exact missing-existence
package. -/
def cyclicOrderOfMissingExistenceConditions
    (E : M8Lemma8MissingExistenceConditions S) :
    CyclicOrder (ofMissingExistenceConditions E) :=
  cyclicOrderOfFiniteExistenceConditions E.toFiniteExistenceConditions

/-- Reassemble `M8Lemma8Combinatorics` through the neighbor-extraction
adapter from the exact missing-existence package. -/
def toLemma8CombinatoricsOfMissingExistenceConditions
    (E : M8Lemma8MissingExistenceConditions S) :
    M8Lemma8Combinatorics S :=
  (ofMissingExistenceConditions E).toLemma8Combinatorics
    (cyclicOrderOfMissingExistenceConditions E)

/-- Degree-six plus a four-forbidden-neighbor frame family determines the
non-cyclic extraction data by the concrete exact-two finset construction. -/
def ofDegreeSixForbiddenFrame
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i) :
    M8ExtraNeighborData S :=
  ofExactTwoExtraNeighborFamily fun i =>
    (forbiddenFrame i).exactTwoExtraNeighbors_of_centerDegree_eq_six
      (hdegree i)

@[simp]
theorem ofDegreeSixForbiddenFrame_r
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (i : M8ExtraIndex) :
    (ofDegreeSixForbiddenFrame hdegree forbiddenFrame).r i =
      ((forbiddenFrame i).exactTwoExtraNeighbors_of_centerDegree_eq_six
        (hdegree i)).r :=
  rfl

@[simp]
theorem ofDegreeSixForbiddenFrame_s
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (i : M8ExtraIndex) :
    (ofDegreeSixForbiddenFrame hdegree forbiddenFrame).s i =
      ((forbiddenFrame i).exactTwoExtraNeighbors_of_centerDegree_eq_six
        (hdegree i)).s :=
  rfl

/-- Attach the remaining cyclic-order assertion to the degree-six/frame
extraction record. -/
def cyclicOrderOfDegreeSixForbiddenFrame
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i
          ((ofDegreeSixForbiddenFrame hdegree forbiddenFrame).s i)
          ((ofDegreeSixForbiddenFrame hdegree forbiddenFrame).r i)
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)) :
    CyclicOrder (ofDegreeSixForbiddenFrame hdegree forbiddenFrame) where
  positiveCyclicOrderAt := positiveCyclicOrderAt
  positiveCyclicOrder := positiveCyclicOrder

/-- Direct neighbor-extraction adapter from degree-six/forbidden-frame data
and the remaining cyclic-order assertion to `M8Lemma8Combinatorics`. -/
def toLemma8CombinatoricsOfDegreeSixForbiddenFrame
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i
          ((ofDegreeSixForbiddenFrame hdegree forbiddenFrame).s i)
          ((ofDegreeSixForbiddenFrame hdegree forbiddenFrame).r i)
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)) :
    M8Lemma8Combinatorics S :=
  (ofDegreeSixForbiddenFrame hdegree forbiddenFrame).toLemma8Combinatorics
    (cyclicOrderOfDegreeSixForbiddenFrame
      hdegree forbiddenFrame positiveCyclicOrderAt positiveCyclicOrder)

@[simp]
theorem toLemma8CombinatoricsOfDegreeSixForbiddenFrame_r
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i
          ((ofDegreeSixForbiddenFrame hdegree forbiddenFrame).s i)
          ((ofDegreeSixForbiddenFrame hdegree forbiddenFrame).r i)
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i))
    (i : M8ExtraIndex) :
    (toLemma8CombinatoricsOfDegreeSixForbiddenFrame
      hdegree forbiddenFrame positiveCyclicOrderAt positiveCyclicOrder).r i =
      ((forbiddenFrame i).exactTwoExtraNeighbors_of_centerDegree_eq_six
        (hdegree i)).r :=
  rfl

@[simp]
theorem toLemma8CombinatoricsOfDegreeSixForbiddenFrame_s
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i
          ((ofDegreeSixForbiddenFrame hdegree forbiddenFrame).s i)
          ((ofDegreeSixForbiddenFrame hdegree forbiddenFrame).r i)
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i))
    (i : M8ExtraIndex) :
    (toLemma8CombinatoricsOfDegreeSixForbiddenFrame
      hdegree forbiddenFrame positiveCyclicOrderAt positiveCyclicOrder).s i =
      ((forbiddenFrame i).exactTwoExtraNeighbors_of_centerDegree_eq_six
        (hdegree i)).s :=
  rfl

end M8ExtraNeighborData

/-! ## Boundary-spine skeleton routing -/

namespace PlanarSkeletonRoute

variable {Dplanar : PlanarBoundaryClosure.PlanarBoundaryData
  (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
variable {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

/-- Attach extracted neighbor data and cyclic order to a valid finite boundary
spine skeleton. -/
def toLemma8Combinatorics
    (X : BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton Dplanar)
    (hvalid :
      BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton.Valid
        connectedNoCut hmin X)
    (neighbors : M8ExtraNeighborData (X.toM8BoundarySpine hvalid))
    (cyclic : M8ExtraNeighborData.CyclicOrder neighbors) :
    M8Lemma8Combinatorics (X.toM8BoundarySpine hvalid) :=
  neighbors.toLemma8Combinatorics cyclic

/-- The skeleton route can now use the extracted neighbor package directly;
only the isolated cyclic-order record remains as a separate input. -/
def toM8BoundaryRouteDataFromExtraction
    (X : BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton Dplanar)
    (hvalid :
      BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton.Valid
        connectedNoCut hmin X)
    (neighbors : M8ExtraNeighborData (X.toM8BoundarySpine hvalid))
    (cyclic : M8ExtraNeighborData.CyclicOrder neighbors) :
    BoundaryFaceCountingToM8.M8BoundaryRouteData C hmin :=
  X.toM8BoundaryRouteData hvalid
    (toLemma8Combinatorics X hvalid neighbors cyclic)

@[simp]
theorem toM8BoundaryRouteDataFromExtraction_spine
    (X : BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton Dplanar)
    (hvalid :
      BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton.Valid
        connectedNoCut hmin X)
    (neighbors : M8ExtraNeighborData (X.toM8BoundarySpine hvalid))
    (cyclic : M8ExtraNeighborData.CyclicOrder neighbors) :
    (toM8BoundaryRouteDataFromExtraction X hvalid neighbors cyclic).spine =
      X.toM8BoundarySpine hvalid :=
  rfl

@[simp]
theorem toM8BoundaryRouteDataFromExtraction_labels_r
    (X : BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton Dplanar)
    (hvalid :
      BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton.Valid
        connectedNoCut hmin X)
    (neighbors : M8ExtraNeighborData (X.toM8BoundarySpine hvalid))
    (cyclic : M8ExtraNeighborData.CyclicOrder neighbors)
    (i : M8ExtraIndex) :
    LocalConfigurations.BrokenLatticeLabels.r
      (M8ConstructionInterface.M8LocalLabels.labels
        (BoundaryFaceCountingToM8.M8BoundaryRouteData.toM8LocalLabels
          (toM8BoundaryRouteDataFromExtraction X hvalid neighbors cyclic)))
      i = neighbors.r i :=
  rfl

@[simp]
theorem toM8BoundaryRouteDataFromExtraction_labels_s
    (X : BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton Dplanar)
    (hvalid :
      BoundarySpineConcrete.M8PlanarBoundarySpineSkeleton.Valid
        connectedNoCut hmin X)
    (neighbors : M8ExtraNeighborData (X.toM8BoundarySpine hvalid))
    (cyclic : M8ExtraNeighborData.CyclicOrder neighbors)
    (i : M8ExtraIndex) :
    LocalConfigurations.BrokenLatticeLabels.s
      (M8ConstructionInterface.M8LocalLabels.labels
        (BoundaryFaceCountingToM8.M8BoundaryRouteData.toM8LocalLabels
          (toM8BoundaryRouteDataFromExtraction X hvalid neighbors cyclic)))
      i = neighbors.s i :=
  rfl

end PlanarSkeletonRoute

end

end Lemma8NeighborExtractionConcrete
end Swanepoel
end ErdosProblems1066
