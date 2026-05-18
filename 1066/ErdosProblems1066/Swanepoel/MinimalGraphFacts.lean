import ErdosProblems1066.Swanepoel.DegreePipeline

/-!
# Swanepoel minimal graph facts

This file collects small graph and finite-set facts used around the
minimal-counterexample deletion pipeline.  The statements stay deliberately
conditional: connectivity, planarity, and local geometric structure are still
explicit hypotheses in the higher-level pipeline.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalGraphFacts

open CounterexamplePipeline
open DegreePipeline
open MinimalCounterexample

noncomputable section

/-! ## Closed-neighborhood membership and deletion facts -/

lemma center_subset_deleted_of_isClosedNeighborhood {n : Nat}
    {C : _root_.UDConfig n} {center deleted : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C center deleted) :
    center <= deleted := by
  intro v hv
  exact (hclosed v).2 (Or.inl hv)

lemma mem_deleted_of_mem_center_of_unit {n : Nat}
    {C : _root_.UDConfig n} {center deleted : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C center deleted)
    {u v : Fin n} (hu : u ∈ center)
    (hunit : eucDist (C.pts u) (C.pts v) = 1) :
    v ∈ deleted := by
  exact (hclosed v).2 (Or.inr ⟨u, hu, hunit⟩)

lemma center_card_le_deleted_card_of_isClosedNeighborhood {n : Nat}
    {C : _root_.UDConfig n} {center deleted : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C center deleted) :
    center.card <= deleted.card :=
  Finset.card_le_card (center_subset_deleted_of_isClosedNeighborhood hclosed)

lemma deleted_nonempty_of_center_nonempty {n : Nat}
    {C : _root_.UDConfig n} {center deleted : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C center deleted)
    (hcenter : center.Nonempty) :
    deleted.Nonempty := by
  rcases hcenter with ⟨v, hv⟩
  exact ⟨v, center_subset_deleted_of_isClosedNeighborhood hclosed hv⟩

lemma deleted_card_pos_of_center_card_pos {n : Nat}
    {C : _root_.UDConfig n} {center deleted : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C center deleted)
    (hcenter : 0 < center.card) :
    0 < deleted.card := by
  exact Finset.card_pos.mpr
    (deleted_nonempty_of_center_nonempty hclosed
      (Finset.card_pos.mp hcenter))

lemma disjoint_left_center_of_disjoint_left_deleted {n : Nat}
    {C : _root_.UDConfig n}
    {kept center deleted : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C center deleted)
    (hdisjoint : Disjoint kept deleted) :
    Disjoint kept center := by
  rw [Finset.disjoint_left]
  intro v hvKept hvCenter
  exact (Finset.disjoint_left.mp hdisjoint) hvKept
    (center_subset_deleted_of_isClosedNeighborhood hclosed hvCenter)

lemma disjoint_right_center_of_disjoint_right_deleted {n : Nat}
    {C : _root_.UDConfig n}
    {kept center deleted : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C center deleted)
    (hdisjoint : Disjoint deleted kept) :
    Disjoint center kept := by
  rw [Finset.disjoint_left]
  intro v hvCenter hvKept
  exact (Finset.disjoint_left.mp hdisjoint)
    (center_subset_deleted_of_isClosedNeighborhood hclosed hvCenter) hvKept

lemma not_mem_kept_of_mem_center_of_disjoint_deleted {n : Nat}
    {C : _root_.UDConfig n}
    {kept center deleted : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C center deleted)
    (hdisjoint : Disjoint kept deleted)
    {v : Fin n} (hvCenter : v ∈ center) :
    v ∉ kept := by
  intro hvKept
  exact (Finset.disjoint_left.mp hdisjoint) hvKept
    (center_subset_deleted_of_isClosedNeighborhood hclosed hvCenter)

lemma no_unit_from_center_to_kept_of_disjoint_deleted {n : Nat}
    {C : _root_.UDConfig n}
    {kept center deleted : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C center deleted)
    (hdisjoint : Disjoint kept deleted) :
    forall x : Fin n, x ∈ center ->
      forall y : Fin n, y ∈ kept ->
        eucDist (C.pts x) (C.pts y) ≠ 1 := by
  intro x hx y hy hunit
  have hyDeleted : y ∈ deleted :=
    mem_deleted_of_mem_center_of_unit hclosed hx hunit
  exact (Finset.disjoint_left.mp hdisjoint) hy hyDeleted

/-! ## Singleton closed neighborhoods and degree-controlled cardinality -/

lemma singleton_closedNeighborhood_eq_closedUnitNeighborhood {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n)
    (deleted : Finset (Fin n))
    (hclosed : IsClosedNeighborhood C ({center} : Finset (Fin n)) deleted) :
    deleted = closedUnitNeighborhood C center :=
  closedNeighborhood_singleton_eq_closedUnitNeighborhood C center deleted hclosed

lemma singleton_closedNeighborhood_card_le_seven {n : Nat}
    (C : _root_.UDConfig n) {center : Fin n}
    {deleted : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C ({center} : Finset (Fin n)) deleted) :
    deleted.card <= 7 :=
  deleted_card_le_seven_of_singleton_closedNeighborhood C hclosed

lemma deleted_card_le_seven_of_subset_single_closedNeighborhood {n : Nat}
    (C : _root_.UDConfig n) {deleted : Finset (Fin n)}
    {center : Fin n}
    (hsubset : deleted <= closedUnitNeighborhood C center) :
    deleted.card <= 7 :=
  card_le_seven_of_subset_closedUnitNeighborhood C hsubset

lemma deletedCard_bound_of_single_center_degree_and_two_le {n : Nat}
    (C : _root_.UDConfig n) {deleted reinsertion : Finset (Fin n)}
    {center : Fin n}
    (hsubset : deleted <= closedUnitNeighborhood C center)
    (htwo : 2 <= reinsertion.card) :
    (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 :=
  deletedCard_bound_of_subset_closedUnitNeighborhood_and_two_le C hsubset htwo

/-! ## Deletion/reinsertion package consequences -/

variable {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}

lemma reinsertion_subset_deleted_of_hypotheses
    (D : DeletionReinsertionData C Csmall) (hD : D.Hypotheses) :
    D.reinsertion <= D.deleted :=
  center_subset_deleted_of_isClosedNeighborhood hD.closedNeighborhood

lemma reinsertion_card_le_deleted_card_of_hypotheses
    (D : DeletionReinsertionData C Csmall) (hD : D.Hypotheses) :
    D.reinsertion.card <= D.deleted.card :=
  Finset.card_le_card (reinsertion_subset_deleted_of_hypotheses D hD)

lemma kept_disjoint_reinsertion_of_hypotheses
    (D : DeletionReinsertionData C Csmall) (hD : D.Hypotheses) :
    Disjoint ((Finset.univ.image D.kept) : Finset (Fin n)) D.reinsertion :=
  disjoint_left_center_of_disjoint_left_deleted
    hD.closedNeighborhood hD.keptDeletedDisjoint

lemma deleted_nonempty_of_reinsertion_nonempty
    (D : DeletionReinsertionData C Csmall) (hD : D.Hypotheses)
    (hreinsertion : D.reinsertion.Nonempty) :
    D.deleted.Nonempty :=
  deleted_nonempty_of_center_nonempty hD.closedNeighborhood hreinsertion

lemma deleted_card_pos_of_two_le_reinsertion
    (D : DeletionReinsertionData C Csmall) (hD : D.Hypotheses)
    (htwo : 2 <= D.reinsertion.card) :
    0 < D.deleted.card := by
  have hcenter : 0 < D.reinsertion.card := by omega
  exact deleted_card_pos_of_center_card_pos hD.closedNeighborhood hcenter

lemma original_card_eq_small_add_deleted_of_hypotheses
    (D : DeletionReinsertionData C Csmall) (hD : D.Hypotheses) :
    n = nSmall + D.deleted.card :=
  original_card_eq_small_add_deleted_of_partition D.kept hD.keptInjective
    D.deleted hD.keptDeletedDisjoint hD.cover

lemma nSmall_le_original_of_hypotheses
    (D : DeletionReinsertionData C Csmall) (hD : D.Hypotheses) :
    nSmall <= n := by
  have hcount := original_card_eq_small_add_deleted_of_hypotheses D hD
  omega

lemma nSmall_lt_original_of_deleted_nonempty
    (D : DeletionReinsertionData C Csmall) (hD : D.Hypotheses)
    (hdeleted : D.deleted.Nonempty) :
    nSmall < n := by
  have hcount := original_card_eq_small_add_deleted_of_hypotheses D hD
  have hpos : 0 < D.deleted.card := Finset.card_pos.mpr hdeleted
  omega

lemma nSmall_lt_original_of_two_le_reinsertion
    (D : DeletionReinsertionData C Csmall) (hD : D.Hypotheses)
    (htwo : 2 <= D.reinsertion.card) :
    nSmall < n := by
  have hdeleted : 0 < D.deleted.card :=
    deleted_card_pos_of_two_le_reinsertion D hD htwo
  have hcount := original_card_eq_small_add_deleted_of_hypotheses D hD
  omega

/-! ## Minimality consequences without planarity -/

/-- `C` is a minimal failure for the cleared `8 / 31` independent-set
predicate if `C` itself fails it and every strictly smaller configuration
satisfies it. -/
def IsMinimalClearedFailure {n : Nat} (C : _root_.UDConfig n) : Prop :=
  ¬ HasClearedEightThirtyOneIndependentSet C ∧
    forall {m : Nat} (Csmall : _root_.UDConfig m), m < n ->
      HasClearedEightThirtyOneIndependentSet Csmall

lemma not_hasCleared_of_minimalClearedFailure {n : Nat}
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C) :
    ¬ HasClearedEightThirtyOneIndependentSet C :=
  hmin.1

lemma smaller_hasCleared_of_minimalClearedFailure {n m : Nat}
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C)
    (Csmall : _root_.UDConfig m) (hlt : m < n) :
    HasClearedEightThirtyOneIndependentSet Csmall :=
  hmin.2 Csmall hlt

lemma smaller_hasCleared_of_minimalFailure_and_deleted_nonempty
    (D : DeletionReinsertionData C Csmall)
    (hmin : IsMinimalClearedFailure C)
    (hD : D.Hypotheses) (hdeleted : D.deleted.Nonempty) :
    HasClearedEightThirtyOneIndependentSet Csmall :=
  smaller_hasCleared_of_minimalClearedFailure hmin Csmall
    (nSmall_lt_original_of_deleted_nonempty D hD hdeleted)

lemma smaller_hasCleared_of_minimalFailure_and_two_le_reinsertion
    (D : DeletionReinsertionData C Csmall)
    (hmin : IsMinimalClearedFailure C)
    (hD : D.Hypotheses) (htwo : 2 <= D.reinsertion.card) :
    HasClearedEightThirtyOneIndependentSet Csmall :=
  smaller_hasCleared_of_minimalClearedFailure hmin Csmall
    (nSmall_lt_original_of_two_le_reinsertion D hD htwo)

lemma exists_smallerBound_data_of_hasCleared
    (D : DeletionReinsertionData C Csmall)
    (hsmall : HasClearedEightThirtyOneIndependentSet Csmall) :
    Exists fun small : Finset (Fin nSmall) =>
      ({ kept := D.kept, deleted := D.deleted, reinsertion := D.reinsertion,
          small := small } : DeletionReinsertionData C Csmall).SmallerBound := by
  rcases hsmall with ⟨small, hsmallIndep, hsmallBound⟩
  exact ⟨small, ⟨hsmallIndep, hsmallBound⟩⟩

lemma exists_smallerBound_data_of_minimalFailure_and_deleted_nonempty
    (D : DeletionReinsertionData C Csmall)
    (hmin : IsMinimalClearedFailure C)
    (hD : D.Hypotheses) (hdeleted : D.deleted.Nonempty) :
    Exists fun small : Finset (Fin nSmall) =>
      ({ kept := D.kept, deleted := D.deleted, reinsertion := D.reinsertion,
          small := small } : DeletionReinsertionData C Csmall).SmallerBound :=
  exists_smallerBound_data_of_hasCleared D
    (smaller_hasCleared_of_minimalFailure_and_deleted_nonempty
      D hmin hD hdeleted)

lemma exists_smallerBound_data_of_minimalFailure_and_two_le_reinsertion
    (D : DeletionReinsertionData C Csmall)
    (hmin : IsMinimalClearedFailure C)
    (hD : D.Hypotheses) (htwo : 2 <= D.reinsertion.card) :
    Exists fun small : Finset (Fin nSmall) =>
      ({ kept := D.kept, deleted := D.deleted, reinsertion := D.reinsertion,
          small := small } : DeletionReinsertionData C Csmall).SmallerBound :=
  exists_smallerBound_data_of_hasCleared D
    (smaller_hasCleared_of_minimalFailure_and_two_le_reinsertion
      D hmin hD htwo)

end

end MinimalGraphFacts
end Swanepoel
end ErdosProblems1066
