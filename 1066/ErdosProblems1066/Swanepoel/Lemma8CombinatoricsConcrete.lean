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
  E.eq_r_of_extra_neighbor_ne_s
    ((unitDistanceLocalGraph C).symm hadj) hnot hne

/-- Reverse-adjacency version of the `s_i` reducer. -/
theorem eq_s_of_extra_neighbor_symm_ne_r
    (E : M8Lemma8Combinatorics S)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj x (S.centerQ i))
    (hnot : Not (S.forbiddenExtraNeighbor i x))
    (hne : Not (x = E.r i)) :
    x = E.s i :=
  E.eq_s_of_extra_neighbor_ne_r
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
    (fun hne => E.eq_r_of_extra_neighbor_ne_s hadj hnot hne)
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
    (fun hne => E.eq_s_of_extra_neighbor_ne_r hadj hnot hne)
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
  hne_r (E.eq_r_of_extra_neighbor_ne_s hadj hnot hne_s)

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

/-! ## Cyclic-order field routing -/

/-- The cyclic-order field as a reusable routed proposition. -/
def cyclicOrderRoute
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) : Prop :=
  E.positiveCyclicOrderAt i (E.s i) (E.r i)
    (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)

/-- The routed cyclic-order proposition is exactly the stored field. -/
theorem cyclicOrderRoute_holds
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    E.cyclicOrderRoute i :=
  E.positiveCyclicOrder i

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
    D.lemma8.eq_r_of_extra_neighbor_ne_s hadj hnot hne

/-- Route the symmetric exhaustiveness reducer through boundary-derived data. -/
theorem eq_s_of_extra_neighbor_ne_r
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (D.spine.centerQ i) x)
    (hnot : Not (D.spine.forbiddenExtraNeighbor i x))
    (hne : Not (x = D.labels.r i)) :
    x = D.labels.s i := by
  simpa [M8LabelsFromBoundaryData.labels] using
    D.lemma8.eq_s_of_extra_neighbor_ne_r hadj hnot hne

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
    D.lemma8.eq_r_of_extra_neighbor_ne_s hadj hnot hne

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
    D.lemma8.eq_s_of_extra_neighbor_ne_r hadj hnot hne

end M8BoundaryLabelPackage

end

end Lemma8CombinatoricsConcrete
end Swanepoel
end ErdosProblems1066
