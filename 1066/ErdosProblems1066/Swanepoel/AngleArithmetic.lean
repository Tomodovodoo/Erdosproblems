import ErdosProblems1066.Swanepoel.Lemma10Inequalities

/-!
# Swanepoel angle arithmetic glue

This module records small finite arithmetic lemmas used to connect local
angle/turn estimates for the `m = 8` Lemma 10 configuration with the abstract
turn-budget interface in `Swanepoel.Lemma10Inequalities`.

No Euclidean analytic estimate is proved here.  Those estimates enter as
explicit hypotheses such as a lower bound on the weighted three-turn quantity
attached to a failed comparison.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace AngleArithmetic

open scoped BigOperators
open Lemma10Inequalities

noncomputable section

/-! ## Local turn expressions -/

/-- The unweighted three-turn window `tau_i + tau_{i+1} + tau_{i+2}`. -/
def threeTurn (turn : Nat -> Real) (i : Nat) : Real :=
  turn i + turn (i + 1) + turn (i + 2)

/-- The weighted three-turn expression from Swanepoel Lemma 10 inequality (5):
`tau_i + 2*tau_{i+1} + tau_{i+2}`. -/
def weightedThreeTurn (turn : Nat -> Real) (i : Nat) : Real :=
  turn i + 2 * turn (i + 1) + turn (i + 2)

/-- A local analytic hypothesis: a failed comparison forces the weighted
three-turn lower bound. -/
def FailedComparisonForcesWeightedTurn
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i : Nat},
    1 <= i -> i <= 10 -> Not (good i) ->
      Real.pi / 3 <= weightedThreeTurn turn i

/-- A separated-pair hypothesis stated directly on the window used by the
abstract Lemma 10 inequality interface. -/
def SeparatedWindowLower (good : Nat -> Prop) (turn : Nat -> Real) :
    Prop :=
  forall {i j : Nat},
    1 <= i -> i + 1 < j -> j <= 10 ->
      Not (good i) -> Not (good j) ->
        Real.pi / 3 <= separatedTurn turn i j

/-- An adjacent-pair hypothesis stated directly on the window used by the
abstract Lemma 10 inequality interface. -/
def AdjacentWindowLower (good : Nat -> Prop) (turn : Nat -> Real) :
    Prop :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
        Real.pi / 3 <= adjacentTurn turn i

lemma adjacentTurn_eq_threeTurn (turn : Nat -> Real) (i : Nat) :
    adjacentTurn turn i = threeTurn turn i := by
  unfold adjacentTurn threeTurn
  have hset : Finset.Icc i (i + 2) = ({i, i + 1, i + 2} : Finset Nat) := by
    ext k
    simp
    omega
  rw [hset]
  simp [add_assoc]

lemma totalTurn_eq_sum_thirteen (turn : Nat -> Real) :
    totalTurn turn =
      turn 1 + turn 2 + turn 3 + turn 4 + turn 5 + turn 6 + turn 7 +
      turn 8 + turn 9 + turn 10 + turn 11 + turn 12 + turn 13 := by
  unfold totalTurn turnIndexSet
  norm_num [Finset.sum_Icc_succ_top, add_assoc]

/-! ## Direct conversion into the abstract force-turn interface -/

theorem separatedFailuresForceTurn_of_windowLower
    {good : Nat -> Prop} {turn : Nat -> Real}
    (h : SeparatedWindowLower good turn) :
    SeparatedFailuresForceTurn good turn := by
  intro i j hi hij hj hbad_i hbad_j
  exact h hi hij hj hbad_i hbad_j

theorem adjacentFailuresForceTurn_of_windowLower
    {good : Nat -> Prop} {turn : Nat -> Real}
    (h : AdjacentWindowLower good turn) :
    AdjacentFailuresForceTurn good turn := by
  intro i hi hi_next hbad_i hbad_next
  exact h hi hi_next hbad_i hbad_next

/-- Window lower bounds are exactly the hypotheses needed by the existing
abstract cardinal theorem. -/
theorem card_le_one_failures_of_window_lowers
    (good : Nat -> Prop) [DecidablePred good] (turn : Nat -> Real)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hseparated : SeparatedWindowLower good turn)
    (hadjacent : AdjacentWindowLower good turn) :
    ((Finset.Icc 1 10).filter fun i => Not (good i)).card <= 1 := by
  exact card_le_one_failures_of_turn_hypotheses good turn hnonneg htotal
    (separatedFailuresForceTurn_of_windowLower hseparated)
    (adjacentFailuresForceTurn_of_windowLower hadjacent)

/-! ## Weighted separated-failure arithmetic -/

lemma weightedThreeTurn_half_le_threeTurn
    {turn : Nat -> Real} (hnonneg : forall k : Nat, 0 <= turn k)
    (i : Nat) :
    weightedThreeTurn turn i / 2 <= threeTurn turn i := by
  unfold weightedThreeTurn threeTurn
  nlinarith [hnonneg i, hnonneg (i + 2)]

lemma weightedThreeTurn_pair_average_le_fiveTurn
    {turn : Nat -> Real} (hnonneg : forall k : Nat, 0 <= turn k)
    (i : Nat) :
    (weightedThreeTurn turn i + weightedThreeTurn turn (i + 2)) / 2
      <= (Finset.Icc i (i + 4)).sum turn := by
  have hset :
      Finset.Icc i (i + 4) =
        ({i, i + 1, i + 2, i + 3, i + 4} : Finset Nat) := by
    ext k
    simp
    omega
  rw [hset]
  simp [weightedThreeTurn]
  nlinarith [hnonneg i, hnonneg (i + 4)]

lemma weightedThreeTurn_pair_average_le_disjoint_threeTurns
    {turn : Nat -> Real} (hnonneg : forall k : Nat, 0 <= turn k)
    {i j : Nat} :
    (weightedThreeTurn turn i + weightedThreeTurn turn j) / 2
      <= (Finset.Icc i (i + 2)).sum turn +
        (Finset.Icc j (j + 2)).sum turn := by
  have hi := weightedThreeTurn_half_le_threeTurn hnonneg i
  have hj := weightedThreeTurn_half_le_threeTurn hnonneg j
  have hti :
      (Finset.Icc i (i + 2)).sum turn = threeTurn turn i := by
    simpa [adjacentTurn, threeTurn] using adjacentTurn_eq_threeTurn turn i
  have htj :
      (Finset.Icc j (j + 2)).sum turn = threeTurn turn j := by
    simpa [adjacentTurn, threeTurn] using adjacentTurn_eq_threeTurn turn j
  rw [hti, htj]
  nlinarith

/-- For two separated failed comparisons, the average of the two weighted
three-turn lower bounds is still bounded by the global turn sum.  This is the
finite arithmetic behind the separated case of Swanepoel Lemma 10. -/
lemma weightedThreeTurn_pair_average_le_totalTurn_of_separated
    {turn : Nat -> Real} {i j : Nat}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10) :
    (weightedThreeTurn turn i + weightedThreeTurn turn j) / 2
      <= totalTurn turn := by
  by_cases hgap : j = i + 2
  · subst j
    have hlocal :
        (weightedThreeTurn turn i + weightedThreeTurn turn (i + 2)) / 2
          <= (Finset.Icc i (i + 4)).sum turn :=
      weightedThreeTurn_pair_average_le_fiveTurn hnonneg i
    have hglobal :
        (Finset.Icc i (i + 4)).sum turn <= totalTurn turn := by
      refine sum_le_totalTurn_of_subset ?_ hnonneg
      exact Finset.Icc_subset_Icc hi (by omega)
    linarith
  · have hfar : i + 3 <= j := by omega
    have hlocal :
        (weightedThreeTurn turn i + weightedThreeTurn turn j) / 2
          <= (Finset.Icc i (i + 2)).sum turn +
            (Finset.Icc j (j + 2)).sum turn :=
      weightedThreeTurn_pair_average_le_disjoint_threeTurns hnonneg
    have hdisjoint :
        Disjoint (Finset.Icc i (i + 2)) (Finset.Icc j (j + 2)) := by
      rw [Finset.disjoint_left]
      intro x hx_i hx_j
      have hx_i' := Finset.mem_Icc.mp hx_i
      have hx_j' := Finset.mem_Icc.mp hx_j
      omega
    have hsum_union :
        (Finset.Icc i (i + 2)).sum turn +
          (Finset.Icc j (j + 2)).sum turn =
            ((Finset.Icc i (i + 2)) ∪ (Finset.Icc j (j + 2))).sum turn := by
      exact (Finset.sum_union hdisjoint).symm
    have hglobal :
        ((Finset.Icc i (i + 2)) ∪ (Finset.Icc j (j + 2))).sum turn
          <= totalTurn turn := by
      refine sum_le_totalTurn_of_subset ?_ hnonneg
      intro x hx
      simp only [Finset.mem_union] at hx
      rcases hx with hx | hx
      · have hx' := Finset.mem_Icc.mp hx
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · have hx' := Finset.mem_Icc.mp hx
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    linarith

/-- The local weighted lower bound for each failure implies that two separated
failures force at least `pi / 3` total turn. -/
lemma totalTurn_ge_of_separated_failed_weightedTurn
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (hweighted : FailedComparisonForcesWeightedTurn good turn)
    {i j : Nat}
    (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Real.pi / 3 <= totalTurn turn := by
  have hi10 : i <= 10 := by omega
  have hwi : Real.pi / 3 <= weightedThreeTurn turn i :=
    hweighted hi hi10 hbad_i
  have hj1 : 1 <= j := by omega
  have hwj : Real.pi / 3 <= weightedThreeTurn turn j :=
    hweighted hj1 hj hbad_j
  have havg :
      Real.pi / 3 <=
        (weightedThreeTurn turn i + weightedThreeTurn turn j) / 2 := by
    linarith
  have hle :
      (weightedThreeTurn turn i + weightedThreeTurn turn j) / 2
        <= totalTurn turn :=
    weightedThreeTurn_pair_average_le_totalTurn_of_separated
      hnonneg hi hsep hj
  linarith

/-- Separated failures are impossible when the total turn is below `pi / 3`
and each individual failure satisfies the weighted three-turn lower bound. -/
lemma separated_failures_impossible_of_weightedTurn
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (htotal : totalTurn turn < Real.pi / 3)
    (hweighted : FailedComparisonForcesWeightedTurn good turn)
    {i j : Nat}
    (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    False := by
  have hforce : Real.pi / 3 <= totalTurn turn :=
    totalTurn_ge_of_separated_failed_weightedTurn hnonneg hweighted
      hi hsep hj hbad_i hbad_j
  linarith

end

end AngleArithmetic
end Swanepoel
end ErdosProblems1066
