import ErdosProblems1066.Swanepoel.GraphBridge
import ErdosProblems1066.Swanepoel.InducedSubconfiguration
import ErdosProblems1066.Swanepoel.Lemma10Bridge
import ErdosProblems1066.Swanepoel.MinimalCounterexample

/-!
# Swanepoel counterexample pipeline wrappers

This module packages the already-checked graph bridge and minimal-counterexample
deletion step into conditional pipeline lemmas.  The hypotheses are intentionally
explicit: the file does not prove any local geometry, any deletion/reinsertion
fact, or the final `8 / 31` theorem.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CounterexamplePipeline

open Combinatorics
open GraphBridge
open InducedSubconfiguration
open MinimalCounterexample

noncomputable section

/-! ## Cleared bound and independence views -/

/-- A `UDConfig` has a cleared `8 / 31` independent set. -/
def HasClearedEightThirtyOneIndependentSet {n : Nat}
    (C : _root_.UDConfig n) : Prop :=
  Exists fun s : Finset (Fin n) =>
    C.IsIndep s /\ ClearedEightThirtyOneBound n s.card

/-- A graph-language version of the same cleared independent-set predicate. -/
def HasClearedEightThirtyOneGraphIndependentSet {n : Nat}
    (C : _root_.UDConfig n) : Prop :=
  Exists fun s : Finset (Fin n) =>
    IsIndependentOn (unitDistanceLocalGraph C).Adj s /\
      ClearedEightThirtyOneBound n s.card

/-- Move a `UDConfig` independent set into the graph language. -/
lemma graphIndependent_of_udConfigIndependent {n : Nat}
    (C : _root_.UDConfig n) {s : Finset (Fin n)}
    (h : C.IsIndep s) :
    IsIndependentOn (unitDistanceLocalGraph C).Adj s :=
  (isIndep_iff_localGraph_independent C).1 h

/-- Move a graph independent set back into the `UDConfig` language. -/
lemma udConfigIndependent_of_graphIndependent {n : Nat}
    (C : _root_.UDConfig n) {s : Finset (Fin n)}
    (h : IsIndependentOn (unitDistanceLocalGraph C).Adj s) :
    C.IsIndep s :=
  (isIndep_iff_localGraph_independent C).2 h

/-- The `UDConfig` and local-graph views of the cleared predicate agree. -/
lemma hasCleared_iff_graphHasCleared {n : Nat} (C : _root_.UDConfig n) :
    HasClearedEightThirtyOneIndependentSet C <->
      HasClearedEightThirtyOneGraphIndependentSet C := by
  constructor
  · rintro ⟨s, hs, hbound⟩
    exact ⟨s, graphIndependent_of_udConfigIndependent C hs, hbound⟩
  · rintro ⟨s, hs, hbound⟩
    exact ⟨s, udConfigIndependent_of_graphIndependent C hs, hbound⟩

/-- The finite-edge graph view agrees with the direct `UDConfig` view. -/
lemma hasCleared_iff_edgesHaveCleared {n : Nat} (C : _root_.UDConfig n) :
    HasClearedEightThirtyOneIndependentSet C <->
      Exists fun s : Finset (Fin n) =>
        IsIndependentOn (AdjFromEdges (unitDistanceEdges C)) s /\
          ClearedEightThirtyOneBound n s.card := by
  constructor
  · rintro ⟨s, hs, hbound⟩
    exact ⟨s, (isIndep_iff_edges_independent C).1 hs, hbound⟩
  · rintro ⟨s, hs, hbound⟩
    exact ⟨s, (isIndep_iff_edges_independent C).2 hs, hbound⟩

/-! ## Explicit deletion/reinsertion packages -/

/-- The concrete data for deleting a closed unit-neighborhood from `C` and
keeping a copy of a smaller configuration. -/
structure DeletionReinsertionData
    {n nSmall : Nat} (C : _root_.UDConfig n)
    (Csmall : _root_.UDConfig nSmall) where
  kept : Fin nSmall -> Fin n
  deleted : Finset (Fin n)
  reinsertion : Finset (Fin n)
  small : Finset (Fin nSmall)

namespace DeletionReinsertionData

variable {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}

/-- All non-arithmetic, non-smaller-bound hypotheses needed by the deletion
pipeline.  These are assumptions, not hidden lemmas. -/
structure Hypotheses (D : DeletionReinsertionData C Csmall) : Prop where
  keptInjective : Function.Injective D.kept
  keptDeletedDisjoint :
    Disjoint ((Finset.univ.image D.kept) : Finset (Fin n)) D.deleted
  cover : ((Finset.univ.image D.kept) : Finset (Fin n)) ∪ D.deleted =
    Finset.univ
  closedNeighborhood : IsClosedNeighborhood C D.reinsertion D.deleted
  deletedCard :
    (D.deleted.card : Int) <= 4 * (D.reinsertion.card : Int) - 1
  reinsertionCard : D.reinsertion.card <= 8
  reinsertionIndep : C.IsIndep D.reinsertion
  preservesDistances : PreservesDistancesOn Csmall C D.kept D.small

/-- The smaller-side independent-set hypotheses, separated so callers can get
them from a smaller counterexample bound or from graph language. -/
structure SmallerBound (D : DeletionReinsertionData C Csmall) : Prop where
  smallIndep : Csmall.IsIndep D.small
  smallBound : ClearedEightThirtyOneBound nSmall D.small.card

/-- Same smaller-side hypotheses, but with independence supplied by the
associated local graph of the smaller `UDConfig`. -/
structure SmallerGraphBound (D : DeletionReinsertionData C Csmall) : Prop where
  smallIndep :
    IsIndependentOn (unitDistanceLocalGraph Csmall).Adj D.small
  smallBound : ClearedEightThirtyOneBound nSmall D.small.card

lemma smallerBound_of_graphBound (D : DeletionReinsertionData C Csmall)
    (h : D.SmallerGraphBound) :
    D.SmallerBound where
  smallIndep := udConfigIndependent_of_graphIndependent Csmall h.smallIndep
  smallBound := h.smallBound

/-- The core conditional pipeline: deletion/reinsertion data plus the smaller
cleared bound produces the original cleared `8 / 31` independent set. -/
theorem hasCleared_of_deletionReinsertion
    (D : DeletionReinsertionData C Csmall)
    (hD : D.Hypotheses)
    (hsmall : D.SmallerBound) :
    HasClearedEightThirtyOneIndependentSet C := by
  exact
    exists_independent_with_cleared_bound_of_closedNeighborhood_deletion
      C Csmall D.kept D.deleted D.reinsertion D.small
      hD.keptInjective hD.keptDeletedDisjoint hD.cover
      hD.closedNeighborhood hD.deletedCard hD.reinsertionCard
      hD.reinsertionIndep hsmall.smallIndep hsmall.smallBound
      hD.preservesDistances

/-- Graph-language entry point for the smaller independent set. -/
theorem hasCleared_of_deletionReinsertion_graphSmall
    (D : DeletionReinsertionData C Csmall)
    (hD : D.Hypotheses)
    (hsmall : D.SmallerGraphBound) :
    HasClearedEightThirtyOneIndependentSet C :=
  hasCleared_of_deletionReinsertion D hD
    (smallerBound_of_graphBound D hsmall)

/-- Graph-language conclusion form of the same pipeline. -/
theorem graphHasCleared_of_deletionReinsertion
    (D : DeletionReinsertionData C Csmall)
    (hD : D.Hypotheses)
    (hsmall : D.SmallerBound) :
    HasClearedEightThirtyOneGraphIndependentSet C :=
  (hasCleared_iff_graphHasCleared C).1
    (hasCleared_of_deletionReinsertion D hD hsmall)

end DeletionReinsertionData

/-! ## Concrete induced deletion bridge -/

namespace InducedDeletionBridge

variable {n : Nat} {C : _root_.UDConfig n}

/-- The ambient vertices kept after deleting `deleted`. -/
def keptVertices (deleted : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)) \ deleted

lemma keptVertices_disjoint (deleted : Finset (Fin n)) :
    Disjoint (keptVertices deleted) deleted := by
  rw [Finset.disjoint_left]
  intro v hv hdel
  exact (Finset.mem_sdiff.mp hv).2 hdel

lemma keptVertices_union_deleted (deleted : Finset (Fin n)) :
    keptVertices deleted ∪ deleted = (Finset.univ : Finset (Fin n)) := by
  ext v
  simp [keptVertices]

lemma keptVertices_card_add_deleted_card (deleted : Finset (Fin n)) :
    (keptVertices deleted).card + deleted.card = n := by
  have hsubset : deleted <= (Finset.univ : Finset (Fin n)) := by
    intro v _
    simp
  have h := Finset.card_sdiff_add_card_eq_card hsubset
  simpa [keptVertices, Finset.card_univ, Fintype.card_fin] using h

lemma keptVertices_card_lt_original {deleted : Finset (Fin n)}
    (hdeleted : deleted.Nonempty) :
    (keptVertices deleted).card < n := by
  have hpartition := keptVertices_card_add_deleted_card deleted
  have hpos : 0 < deleted.card := Finset.card_pos.mpr hdeleted
  omega

/-- The actual induced smaller configuration on the vertices outside
`deleted`. -/
def induced (C : _root_.UDConfig n) (deleted : Finset (Fin n)) :
    InducedSubconfiguration.Induced
      (m := (keptVertices deleted).card) C (keptVertices deleted) :=
  InducedSubconfiguration.ofFinset C (keptVertices deleted)

/-- The deletion/reinsertion data determined by the induced kept-side
configuration. -/
def data (C : _root_.UDConfig n) (deleted reinsertion : Finset (Fin n))
    (small : Finset (Fin (keptVertices deleted).card)) :
    DeletionReinsertionData C ((induced C deleted).config) where
  kept := (induced C deleted).embed
  deleted := deleted
  reinsertion := reinsertion
  small := small

/-- Local deletion facts plus the induced kept-side configuration supply the
full deletion/reinsertion hypotheses, including distance preservation. -/
lemma hypotheses
    (deleted reinsertion : Finset (Fin n))
    (small : Finset (Fin (keptVertices deleted).card))
    (hclosed : IsClosedNeighborhood C reinsertion deleted)
    (hdeletedCard :
      (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1)
    (hreinsertionCard : reinsertion.card <= 8)
    (hreinsertionIndep : C.IsIndep reinsertion) :
    (data C deleted reinsertion small).Hypotheses where
  keptInjective := (induced C deleted).embed_injective
  keptDeletedDisjoint := by
    have h :
        Disjoint
          (((Finset.univ : Finset (Fin (keptVertices deleted).card)).image
            (induced C deleted).embed) : Finset (Fin n))
          deleted := by
      rw [(induced C deleted).image_univ]
      exact keptVertices_disjoint deleted
    simpa [data] using h
  cover := by
    have h :
        (((Finset.univ : Finset (Fin (keptVertices deleted).card)).image
            (induced C deleted).embed) : Finset (Fin n)) ∪ deleted =
          Finset.univ := by
      rw [(induced C deleted).image_univ]
      exact keptVertices_union_deleted deleted
    simpa [data] using h
  closedNeighborhood := hclosed
  deletedCard := hdeletedCard
  reinsertionCard := hreinsertionCard
  reinsertionIndep := hreinsertionIndep
  preservesDistances := by
    exact (induced C deleted).preservesDistancesOn small

/-- Concrete induced-deletion route: once the smaller induced configuration
has a cleared independent set, the original configuration is cleared. -/
theorem hasCleared_of_induced_deletion_hasCleared
    (deleted reinsertion : Finset (Fin n))
    (hclosed : IsClosedNeighborhood C reinsertion deleted)
    (hdeletedCard :
      (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1)
    (hreinsertionCard : reinsertion.card <= 8)
    (hreinsertionIndep : C.IsIndep reinsertion)
    (hsmall :
      HasClearedEightThirtyOneIndependentSet
        ((induced C deleted).config)) :
    HasClearedEightThirtyOneIndependentSet C := by
  rcases hsmall with ⟨small, hsmallIndep, hsmallBound⟩
  let D := data C deleted reinsertion small
  have hD : D.Hypotheses :=
    hypotheses deleted reinsertion small hclosed hdeletedCard
      hreinsertionCard hreinsertionIndep
  have hsmallD : D.SmallerBound := by
    exact
      { smallIndep := hsmallIndep
        smallBound := hsmallBound }
  exact D.hasCleared_of_deletionReinsertion hD hsmallD

/-- Version with the chosen smaller independent set supplied directly. -/
theorem hasCleared_of_induced_deletion
    (deleted reinsertion : Finset (Fin n))
    (small : Finset (Fin (keptVertices deleted).card))
    (hclosed : IsClosedNeighborhood C reinsertion deleted)
    (hdeletedCard :
      (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1)
    (hreinsertionCard : reinsertion.card <= 8)
    (hreinsertionIndep : C.IsIndep reinsertion)
    (hsmallIndep : ((induced C deleted).config).IsIndep small)
    (hsmallBound :
      ClearedEightThirtyOneBound (keptVertices deleted).card small.card) :
    HasClearedEightThirtyOneIndependentSet C := by
  let D := data C deleted reinsertion small
  have hD : D.Hypotheses :=
    hypotheses deleted reinsertion small hclosed hdeletedCard
      hreinsertionCard hreinsertionIndep
  have hsmallD : D.SmallerBound := by
    exact
      { smallIndep := hsmallIndep
        smallBound := hsmallBound }
  exact D.hasCleared_of_deletionReinsertion hD hsmallD

end InducedDeletionBridge

/-! ## E1/E5-facing aliases -/

/-- E1 pipeline entry point.  The local E1 facts are represented exactly by the
explicit deletion/reinsertion hypotheses. -/
theorem e1_pipeline_of_explicit_deletion
    {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}
    (D : DeletionReinsertionData C Csmall)
    (hD : D.Hypotheses)
    (hsmall : D.SmallerBound) :
    HasClearedEightThirtyOneIndependentSet C :=
  D.hasCleared_of_deletionReinsertion hD hsmall

/-- E5 pipeline entry point, with the smaller independent set supplied in graph
language. -/
theorem e5_pipeline_of_explicit_deletion_graphSmall
    {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}
    (D : DeletionReinsertionData C Csmall)
    (hD : D.Hypotheses)
    (hsmall : D.SmallerGraphBound) :
    HasClearedEightThirtyOneIndependentSet C :=
  D.hasCleared_of_deletionReinsertion_graphSmall hD hsmall

end

end CounterexamplePipeline
end Swanepoel
end ErdosProblems1066
