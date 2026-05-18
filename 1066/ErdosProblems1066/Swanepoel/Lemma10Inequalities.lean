import Mathlib

/-!
# Swanepoel Lemma 10 turn inequalities

This module isolates the finite/real reduction behind Swanepoel's Lemma 10.
It assumes a real-valued turn function, nonnegative turns, a total turn bound
below `pi / 3`, and explicit local hypotheses saying that two failed Lemma 10
comparisons force at least `pi / 3` turn.  The conclusion is exactly the
cardinal "at most one failure in `1, ..., 10`" form used by
`Swanepoel.Lemma10Bridge`.

No geometric or analytic estimate is hidden here: those enter only through the
two force-turn hypotheses and the global total-turn bound.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma10Inequalities

open scoped BigOperators

noncomputable section

/-! ## Finite index sets and turn sums -/

/-- The ten comparison indices appearing in the `m = 8` form of Lemma 10. -/
def lemma10IndexSet : Finset Nat :=
  Finset.Icc 1 10

/-- The turn indices `1, ..., 13` for the surrounding `m = 8` arc. -/
def turnIndexSet : Finset Nat :=
  Finset.Icc 1 13

/-- The failed Lemma 10 comparisons in the range `1, ..., 10`. -/
def failureSet (good : Nat -> Prop) [DecidablePred good] : Finset Nat :=
  lemma10IndexSet.filter fun i => Not (good i)

/-- The total turn available on the `m = 8` arc. -/
def totalTurn (turn : Nat -> Real) : Real :=
  turnIndexSet.sum turn

/-- The turn window used when two failed comparisons are separated. -/
def separatedTurn (turn : Nat -> Real) (i j : Nat) : Real :=
  (Finset.Icc (i + 1) j).sum turn

/-- The turn window used when two failed comparisons are adjacent. -/
def adjacentTurn (turn : Nat -> Real) (i : Nat) : Real :=
  (Finset.Icc i (i + 2)).sum turn

/-! ## Explicit analytic/geometric hypotheses -/

/-- Any two separated failures force at least `pi / 3` turn on the intervening
window. -/
def SeparatedFailuresForceTurn (good : Nat -> Prop) (turn : Nat -> Real) :
    Prop :=
  forall {i j : Nat},
    1 <= i -> i + 1 < j -> j <= 10 ->
      Not (good i) -> Not (good j) ->
        Real.pi / 3 <= separatedTurn turn i j

/-- Any two adjacent failures force at least `pi / 3` turn on the adjacent
window. -/
def AdjacentFailuresForceTurn (good : Nat -> Prop) (turn : Nat -> Real) :
    Prop :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
        Real.pi / 3 <= adjacentTurn turn i

/-! ## Local turn windows sit inside the global turn budget -/

lemma sum_le_totalTurn_of_subset {turn : Nat -> Real} {s : Finset Nat}
    (hsub : s <= turnIndexSet) (hnonneg : forall k : Nat, 0 <= turn k) :
    s.sum turn <= totalTurn turn := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => hnonneg k)

lemma separatedTurn_le_totalTurn {turn : Nat -> Real} {i j : Nat}
    (hi : 1 <= i) (hj : j <= 10)
    (hnonneg : forall k : Nat, 0 <= turn k) :
    separatedTurn turn i j <= totalTurn turn := by
  refine sum_le_totalTurn_of_subset (s := Finset.Icc (i + 1) j) ?_ hnonneg
  exact Finset.Icc_subset_Icc (by omega) (by omega)

lemma adjacentTurn_le_totalTurn {turn : Nat -> Real} {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hnonneg : forall k : Nat, 0 <= turn k) :
    adjacentTurn turn i <= totalTurn turn := by
  refine sum_le_totalTurn_of_subset (s := Finset.Icc i (i + 2)) ?_ hnonneg
  exact Finset.Icc_subset_Icc hi (by omega)

/-! ## The finite/real contradiction -/

lemma ordered_two_failures_impossible
    (good : Nat -> Prop) (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hseparated : SeparatedFailuresForceTurn good turn)
    (hadjacent : AdjacentFailuresForceTurn good turn)
    {i j : Nat}
    (hi1 : 1 <= i) (hj10 : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j))
    (hij : i < j) :
    False := by
  have hsucc_le : i + 1 <= j := Nat.succ_le_of_lt hij
  rcases lt_or_eq_of_le hsucc_le with hseparated_indices | hadjacent_indices
  · have hlocal : Real.pi / 3 <= separatedTurn turn i j :=
      hseparated hi1 hseparated_indices hj10 hbad_i hbad_j
    have hglobal : separatedTurn turn i j <= totalTurn turn :=
      separatedTurn_le_totalTurn hi1 hj10 hnonneg
    linarith
  · have hi_next : i + 1 <= 10 := by
      omega
    have hbad_next : Not (good (i + 1)) := by
      simpa [hadjacent_indices] using hbad_j
    have hlocal : Real.pi / 3 <= adjacentTurn turn i :=
      hadjacent hi1 hi_next hbad_i hbad_next
    have hglobal : adjacentTurn turn i <= totalTurn turn :=
      adjacentTurn_le_totalTurn hi1 hi_next hnonneg
    linarith

lemma failure_indices_eq_of_turn_hypotheses
    (good : Nat -> Prop) [DecidablePred good] (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hseparated : SeparatedFailuresForceTurn good turn)
    (hadjacent : AdjacentFailuresForceTurn good turn)
    {i j : Nat}
    (hi_mem : i ∈ failureSet good) (hj_mem : j ∈ failureSet good) :
    i = j := by
  classical
  have hi_filter := Finset.mem_filter.mp hi_mem
  have hj_filter := Finset.mem_filter.mp hj_mem
  have hi_range := Finset.mem_Icc.mp hi_filter.1
  have hj_range := Finset.mem_Icc.mp hj_filter.1
  by_cases hEq : i = j
  · exact hEq
  · exfalso
    rcases Nat.lt_or_gt_of_ne hEq with hlt | hgt
    · exact ordered_two_failures_impossible good turn hnonneg htotal
        hseparated hadjacent hi_range.1 hj_range.2 hi_filter.2
        hj_filter.2 hlt
    · exact ordered_two_failures_impossible good turn hnonneg htotal
        hseparated hadjacent hj_range.1 hi_range.2 hj_filter.2
        hi_filter.2 hgt

/-- Abstract Lemma 10 inequality reduction: the turn hypotheses imply at most
one failed comparison among indices `1, ..., 10`. -/
theorem failureSet_card_le_one_of_turn_hypotheses
    (good : Nat -> Prop) [DecidablePred good] (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hseparated : SeparatedFailuresForceTurn good turn)
    (hadjacent : AdjacentFailuresForceTurn good turn) :
    (failureSet good).card <= 1 := by
  classical
  refine Finset.card_le_one.2 ?_
  intro i hi_mem j hj_mem
  exact failure_indices_eq_of_turn_hypotheses good turn hnonneg htotal
    hseparated hadjacent hi_mem hj_mem

/-- Bridge-ready cardinal form over `(Finset.Icc 1 10).filter ...`. -/
theorem card_le_one_failures_of_turn_hypotheses
    (good : Nat -> Prop) [DecidablePred good] (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hseparated : SeparatedFailuresForceTurn good turn)
    (hadjacent : AdjacentFailuresForceTurn good turn) :
    ((Finset.Icc 1 10).filter fun i => Not (good i)).card <= 1 := by
  simpa [failureSet, lemma10IndexSet] using
    failureSet_card_le_one_of_turn_hypotheses good turn hnonneg htotal
      hseparated hadjacent

end

end Lemma10Inequalities
end Swanepoel
end ErdosProblems1066
