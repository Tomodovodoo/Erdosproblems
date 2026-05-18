import ErdosProblems1066.Swanepoel.CounterexamplePipeline
import ErdosProblems1066.Swanepoel.DegreeBound

/-!
# Swanepoel degree-bound pipeline

This module connects the checked Euclidean degree bound to the existing
minimal-counterexample deletion/reinsertion pipeline.  The local geometric
choice of a deletion and reinsertion is still explicit, but the cardinal
hypothesis `deleted.card <= 4 * reinsertion.card - 1` can now be supplied from
the proved unit-distance neighbor bound whenever the deleted set is contained
in a closed neighborhood of one vertex and at least two vertices are reinserted.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace DegreePipeline

open CounterexamplePipeline
open MinimalCounterexample

noncomputable section

/-! ## Closed-neighborhood cardinality from the degree theorem -/

/-- The unit-distance neighbors of a vertex, in the orientation used by
`DegreeBound.UDConfig.unitDistanceNeighborSet_card_le_six`. -/
def unitDistanceNeighborSet {n : Nat} (C : _root_.UDConfig n)
    (center : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    fun j => j != center /\ _root_.eucDist (C.pts j) (C.pts center) = 1

/-- The closed unit-neighborhood of a single vertex. -/
def closedUnitNeighborhood {n : Nat} (C : _root_.UDConfig n)
    (center : Fin n) : Finset (Fin n) :=
  insert center (unitDistanceNeighborSet C center)

@[simp]
lemma mem_unitDistanceNeighborSet {n : Nat} (C : _root_.UDConfig n)
    (center j : Fin n) :
    j ∈ unitDistanceNeighborSet C center <->
      j != center /\ _root_.eucDist (C.pts j) (C.pts center) = 1 := by
  simp [unitDistanceNeighborSet]

lemma unitDistanceNeighborSet_card_le_six {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n) :
    (unitDistanceNeighborSet C center).card <= 6 := by
  simpa [unitDistanceNeighborSet] using
    DegreeBound.UDConfig.unitDistanceNeighborSet_card_le_six C center

lemma center_not_mem_unitDistanceNeighborSet {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n) :
    center ∉ unitDistanceNeighborSet C center := by
  simp [unitDistanceNeighborSet]

lemma closedUnitNeighborhood_card_eq_neighborSet_card_add_one {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n) :
    (closedUnitNeighborhood C center).card =
      (unitDistanceNeighborSet C center).card + 1 := by
  simp [closedUnitNeighborhood, center_not_mem_unitDistanceNeighborSet C center]

lemma closedUnitNeighborhood_card_le_seven {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n) :
    (closedUnitNeighborhood C center).card <= 7 := by
  have hneighbor := unitDistanceNeighborSet_card_le_six C center
  have hcard := closedUnitNeighborhood_card_eq_neighborSet_card_add_one C center
  omega

/-- A set contained in one closed unit-neighborhood has at most seven vertices. -/
lemma card_le_seven_of_subset_closedUnitNeighborhood {n : Nat}
    (C : _root_.UDConfig n) {deleted : Finset (Fin n)} {center : Fin n}
    (hsubset : deleted <= closedUnitNeighborhood C center) :
    deleted.card <= 7 :=
  le_trans (Finset.card_le_card hsubset)
    (closedUnitNeighborhood_card_le_seven C center)

/-- The explicit `IsClosedNeighborhood` predicate agrees with
`closedUnitNeighborhood` for a singleton center. -/
lemma closedNeighborhood_singleton_eq_closedUnitNeighborhood {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n) (deleted : Finset (Fin n))
    (hclosed :
      IsClosedNeighborhood C ({center} : Finset (Fin n)) deleted) :
    deleted = closedUnitNeighborhood C center := by
  ext v
  rw [hclosed v]
  by_cases hv : v = center
  · subst v
    simp [closedUnitNeighborhood, unitDistanceNeighborSet]
  · simp [closedUnitNeighborhood, unitDistanceNeighborSet, hv, _root_.eucDist_comm]

lemma deleted_card_le_seven_of_singleton_closedNeighborhood {n : Nat}
    (C : _root_.UDConfig n) {center : Fin n} {deleted : Finset (Fin n)}
    (hclosed :
      IsClosedNeighborhood C ({center} : Finset (Fin n)) deleted) :
    deleted.card <= 7 := by
  rw [closedNeighborhood_singleton_eq_closedUnitNeighborhood C center deleted hclosed]
  exact closedUnitNeighborhood_card_le_seven C center

/-! ## The cleared `8 / 31` deletion arithmetic hypothesis from degree <= 6 -/

lemma deletedCard_bound_of_card_le_seven_and_two_le {n : Nat}
    {deleted reinsertion : Finset (Fin n)}
    (hdeleted : deleted.card <= 7)
    (htwo : 2 <= reinsertion.card) :
    (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 := by
  have hdeletedInt : (deleted.card : Int) <= 7 := by
    exact_mod_cast hdeleted
  have hthreshold : (7 : Int) <= 4 * (reinsertion.card : Int) - 1 := by
    omega
  omega

lemma deletedCard_bound_of_subset_closedUnitNeighborhood_and_two_le {n : Nat}
    (C : _root_.UDConfig n) {deleted reinsertion : Finset (Fin n)}
    {center : Fin n}
    (hsubset : deleted <= closedUnitNeighborhood C center)
    (htwo : 2 <= reinsertion.card) :
    (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 :=
  deletedCard_bound_of_card_le_seven_and_two_le
    (card_le_seven_of_subset_closedUnitNeighborhood C hsubset) htwo

lemma deletedCard_bound_of_singleton_closedNeighborhood_and_two_le {n : Nat}
    (C : _root_.UDConfig n) {center : Fin n}
    {deleted reinsertion : Finset (Fin n)}
    (hclosed :
      IsClosedNeighborhood C ({center} : Finset (Fin n)) deleted)
    (htwo : 2 <= reinsertion.card) :
    (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 :=
  deletedCard_bound_of_card_le_seven_and_two_le
    (deleted_card_le_seven_of_singleton_closedNeighborhood C hclosed) htwo

/-! ## Deletion/reinsertion wrapper with the degree-supplied cardinal bound -/

variable {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}

/-- The existing pipeline hypotheses with the deleted-card arithmetic replaced
by a degree-controlled deletion witness.  The remaining assumptions are the
minimal-counterexample data not supplied by the degree theorem. -/
structure DegreeHypotheses
    (D : DeletionReinsertionData C Csmall) : Prop where
  keptInjective : Function.Injective D.kept
  keptDeletedDisjoint :
    Disjoint ((Finset.univ.image D.kept) : Finset (Fin n)) D.deleted
  cover : ((Finset.univ.image D.kept) : Finset (Fin n)) ∪ D.deleted =
    Finset.univ
  closedNeighborhood : IsClosedNeighborhood C D.reinsertion D.deleted
  deletedSubsetClosedUnitNeighborhood :
    Exists fun center : Fin n => D.deleted <= closedUnitNeighborhood C center
  reinsertionCardLower : 2 <= D.reinsertion.card
  reinsertionCardUpper : D.reinsertion.card <= 8
  reinsertionIndep : C.IsIndep D.reinsertion
  preservesDistances : PreservesDistancesOn Csmall C D.kept D.small

lemma deletedCard_of_degreeHypotheses
    (D : DeletionReinsertionData C Csmall) (hD : DegreeHypotheses D) :
    (D.deleted.card : Int) <= 4 * (D.reinsertion.card : Int) - 1 := by
  rcases hD.deletedSubsetClosedUnitNeighborhood with ⟨center, hsubset⟩
  exact deletedCard_bound_of_subset_closedUnitNeighborhood_and_two_le C
    hsubset hD.reinsertionCardLower

lemma hypotheses_of_degreeHypotheses
    (D : DeletionReinsertionData C Csmall) (hD : DegreeHypotheses D) :
    D.Hypotheses where
  keptInjective := hD.keptInjective
  keptDeletedDisjoint := hD.keptDeletedDisjoint
  cover := hD.cover
  closedNeighborhood := hD.closedNeighborhood
  deletedCard := deletedCard_of_degreeHypotheses D hD
  reinsertionCard := hD.reinsertionCardUpper
  reinsertionIndep := hD.reinsertionIndep
  preservesDistances := hD.preservesDistances

/-- Degree-bound entry point for the existing deletion/reinsertion pipeline. -/
theorem hasCleared_of_degreeDeletionReinsertion
    (D : DeletionReinsertionData C Csmall)
    (hD : DegreeHypotheses D)
    (hsmall : D.SmallerBound) :
    HasClearedEightThirtyOneIndependentSet C :=
  D.hasCleared_of_deletionReinsertion
    (hypotheses_of_degreeHypotheses D hD) hsmall

/-- Degree-bound entry point when the smaller independent set is supplied in
the graph language. -/
theorem hasCleared_of_degreeDeletionReinsertion_graphSmall
    (D : DeletionReinsertionData C Csmall)
    (hD : DegreeHypotheses D)
    (hsmall : D.SmallerGraphBound) :
    HasClearedEightThirtyOneIndependentSet C :=
  D.hasCleared_of_deletionReinsertion_graphSmall
    (hypotheses_of_degreeHypotheses D hD) hsmall

/-- Graph-language conclusion form of the degree-bound pipeline. -/
theorem graphHasCleared_of_degreeDeletionReinsertion
    (D : DeletionReinsertionData C Csmall)
    (hD : DegreeHypotheses D)
    (hsmall : D.SmallerBound) :
    HasClearedEightThirtyOneGraphIndependentSet C :=
  D.graphHasCleared_of_deletionReinsertion
    (hypotheses_of_degreeHypotheses D hD) hsmall

/-! ## E1/E5-facing aliases -/

theorem e1_pipeline_of_degree_deletion
    {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}
    (D : DeletionReinsertionData C Csmall)
    (hD : DegreeHypotheses D)
    (hsmall : D.SmallerBound) :
    HasClearedEightThirtyOneIndependentSet C :=
  hasCleared_of_degreeDeletionReinsertion D hD hsmall

theorem e5_pipeline_of_degree_deletion_graphSmall
    {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}
    (D : DeletionReinsertionData C Csmall)
    (hD : DegreeHypotheses D)
    (hsmall : D.SmallerGraphBound) :
    HasClearedEightThirtyOneIndependentSet C :=
  hasCleared_of_degreeDeletionReinsertion_graphSmall D hD hsmall

end

end DegreePipeline
end Swanepoel
end ErdosProblems1066
