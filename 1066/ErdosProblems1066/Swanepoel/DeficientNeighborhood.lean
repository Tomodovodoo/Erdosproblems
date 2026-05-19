import ErdosProblems1066.Swanepoel.SmallIndependentNeighborhood
import ErdosProblems1066.Swanepoel.MinimalFailureLocalExclusions

set_option autoImplicit false

/-!
# Deficient canonical neighborhoods

This module packages the cardinal arithmetic for a canonical deletion by the
closed neighborhood of a small independent set whose outside neighborhood is
deficient.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace DeficientNeighborhood

open MinimalCounterexample
open MinimalFailureLocalExclusions
open SmallIndependentNeighborhood

noncomputable section

/-- The canonical closed neighborhood is the disjoint union of the center set
and its outside neighborhood, so its cardinality splits accordingly. -/
lemma card_closedNeighborhoodOf_eq_card_add_outside {n : Nat}
    (C : _root_.UDConfig n) (S : Finset (Fin n)) :
    (closedNeighborhoodOf C S).card =
      S.card + (outsideNeighborhoodOf C S).card := by
  classical
  rw [closedNeighborhoodOf_eq_union]
  rw [Finset.card_union_of_disjoint]
  exact (disjoint_outsideNeighborhoodOf C S).symm

/-- If the outside neighborhood has fewer than `3 * |S|` vertices and `S` is
nonempty, then deleting the canonical closed neighborhood satisfies the direct
`4 * |S| - 1` cardinal bound. -/
lemma closedNeighborhoodOf_card_le_four_mul_card_sub_one {n : Nat}
    (C : _root_.UDConfig n) {S : Finset (Fin n)}
    (hS : S.Nonempty)
    (houtside : (outsideNeighborhoodOf C S).card < 3 * S.card) :
    ((closedNeighborhoodOf C S).card : Int) <= 4 * (S.card : Int) - 1 := by
  have hcard :
      (closedNeighborhoodOf C S).card =
        S.card + (outsideNeighborhoodOf C S).card :=
    card_closedNeighborhoodOf_eq_card_add_outside C S
  have hSpos : 0 < S.card := Finset.card_pos.mpr hS
  rw [hcard]
  omega

/-- The canonical deletion `closedNeighborhoodOf C S` and reinsertion `S`
satisfy the direct local-deletion inputs: closed-neighborhood identity,
deletion-cardinality bound, nonempty reinsertion, upper cardinal bound, and
independence. -/
theorem canonicalDeletion_satisfies_directLocalDeletionInputs {n : Nat}
    (C : _root_.UDConfig n) {S : Finset (Fin n)}
    (hS : S.Nonempty) (hindep : C.IsIndep S) (hupper : S.card <= 8)
    (houtside : (outsideNeighborhoodOf C S).card < 3 * S.card) :
    let deleted := closedNeighborhoodOf C S
    let reinsertion := S
    IsClosedNeighborhood C reinsertion deleted /\
      (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 /\
      reinsertion.Nonempty /\
      reinsertion.card <= 8 /\
      C.IsIndep reinsertion := by
  dsimp
  exact
    And.intro (isClosedNeighborhood_closedNeighborhoodOf C S)
      (And.intro
        (closedNeighborhoodOf_card_le_four_mul_card_sub_one C hS houtside)
        (And.intro hS (And.intro hupper hindep)))

/-- Existence form: the same canonical deficient-neighborhood deletion can be
attached to the induced kept-side configuration, producing a general
`LocalDeletionCertificate` with direct cardinal control. -/
theorem exists_localDeletionCertificate_of_deficientNeighborhood {n : Nat}
    (C : _root_.UDConfig n) {S : Finset (Fin n)}
    (hS : S.Nonempty) (hindep : C.IsIndep S) (hupper : S.card <= 8)
    (houtside : (outsideNeighborhoodOf C S).card < 3 * S.card) :
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (LocalDeletionCertificate C Csmall) := by
  classical
  let deleted := closedNeighborhoodOf C S
  let kept := keptAfterDeletion deleted
  let I := InducedSubconfiguration.ofFinset C kept
  refine Exists.intro kept.card ?_
  refine Exists.intro I.config ?_
  refine Nonempty.intro ?_
  exact
    { kept := I.embed
      deleted := deleted
      reinsertion := S
      keptInjective := I.embed_injective
      keptDeletedDisjoint := by
        rw [I.image_univ]
        exact keptAfterDeletion_disjoint deleted
      cover := by
        rw [I.image_univ]
        exact keptAfterDeletion_union_deleted deleted
      closedNeighborhood := isClosedNeighborhood_closedNeighborhoodOf C S
      deletedCard :=
        closedNeighborhoodOf_card_le_four_mul_card_sub_one C hS houtside
      reinsertionNonempty := hS
      reinsertionCardUpper := hupper
      reinsertionIndep := hindep
      preservesDistances := by
        intro small
        exact I.preservesDistancesOn small }

/-- Concrete data for a small independent set whose outside neighborhood is too small. -/
structure DeficientIndependentSetData {n : Nat} (C : _root_.UDConfig n) where
  carrier : Finset (Fin n)
  nonempty : carrier.Nonempty
  independent : C.IsIndep carrier
  card_le_eight : carrier.card <= 8
  outside_card_lt : (outsideNeighborhoodOf C carrier).card < 3 * carrier.card

namespace DeficientIndependentSetData

theorem toExists {n : Nat} {C : _root_.UDConfig n}
    (D : DeficientIndependentSetData C) :
    Exists fun S : Finset (Fin n) =>
      S.Nonempty /\
      C.IsIndep S /\
      S.card <= 8 /\
      (outsideNeighborhoodOf C S).card < 3 * S.card := by
  exact
    Exists.intro D.carrier
      (And.intro D.nonempty
        (And.intro D.independent
          (And.intro D.card_le_eight D.outside_card_lt)))

end DeficientIndependentSetData

/-- In a minimal cleared failure, every nonempty independent set of size at
most eight has outside neighborhood at least three times as large.  Otherwise
the canonical closed-neighborhood deletion gives a local deletion certificate,
which is impossible in a minimal failure. -/
theorem outsideNeighborhood_card_ge_three_mul_of_minimalFailure {n : Nat}
    {C : _root_.UDConfig n} {S : Finset (Fin n)}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hS : S.Nonempty) (hindep : C.IsIndep S) (hupper : S.card <= 8) :
    3 * S.card <= (outsideNeighborhoodOf C S).card := by
  by_contra hnot
  have houtside : (outsideNeighborhoodOf C S).card < 3 * S.card :=
    Nat.lt_of_not_ge hnot
  exact
    Exists.elim
      (exists_localDeletionCertificate_of_deficientNeighborhood
        C hS hindep hupper houtside)
      (fun _nSmall hrest =>
        Exists.elim hrest
          (fun Csmall hcert =>
            LocalDeletionCertificate.not_nonempty_localDeletionCertificate_of_minimalFailure
              (Csmall := Csmall) hmin hcert))

/-- A minimal cleared failure has no deficient small independent set.  This is
the common contradiction used by the no-cut deletion branch and by the
boundary-walk Lemma 6 deficient-independent-set reduction. -/
theorem false_of_minimalFailure_deficientIndependentSet {n : Nat}
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hdef :
      Exists fun S : Finset (Fin n) =>
        S.Nonempty /\
        C.IsIndep S /\
        S.card <= 8 /\
        (outsideNeighborhoodOf C S).card < 3 * S.card) :
    False := by
  rcases hdef with ⟨S, hS, hindep, hupper, houtside_lt⟩
  exact
    (not_lt_of_ge
      (outsideNeighborhood_card_ge_three_mul_of_minimalFailure
        hmin hS hindep hupper))
      houtside_lt

theorem false_of_minimalFailure_deficientIndependentSetData {n : Nat}
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (D : DeficientIndependentSetData C) :
    False := by
  exact
    false_of_minimalFailure_deficientIndependentSet hmin
      (DeficientIndependentSetData.toExists D)

end

end DeficientNeighborhood
end Swanepoel
end ErdosProblems1066
