import Mathlib

/-!
# Arithmetic helpers for Swanepoel's `8 / 31` argument

This file records the parts of the Swanepoel proof plan that are purely
arithmetic.  The geometric and graph-theoretic claims remain outside this
module; these lemmas are intended to be reusable once those hypotheses have
been formalized.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Arithmetic

/-! ## Minimal-counterexample deletion arithmetic -/

/-- The density used in the minimal-counterexample argument. -/
def density (m : Rat) : Rat :=
  m / (4 * m - 1)

/-- The exact cleared-denominator identity behind the deletion step in E5. -/
lemma deletion_density_identity_cleared (m k n : Rat) :
    m * (n - 4 * k + 1) + k * (4 * m - 1) =
      m * n + (m - k) := by
  ring_nf

/-- If the independent set removed has size at most `m`, the cleared deletion
step does not lower the target numerator. -/
lemma deletion_density_cleared_le_after_reinserting
    {m k n : Rat} (hk : k <= m) :
    m * n <= m * (n - 4 * k + 1) + k * (4 * m - 1) := by
  nlinarith

/-- Integer cleared-denominator form of the same deletion arithmetic. -/
lemma deletion_cleared_denominator_int
    {m k n t : Int} (hk : k <= m)
    (ht : (4 * m - 1) * t >= m * (n - 4 * k + 1)) :
    (4 * m - 1) * (t + k) >= m * n := by
  nlinarith

/-! ## Generic arithmetic around `m / (4m - 1)` -/

/-- The denominator `4m - 1` is positive for all positive natural `m`. -/
lemma four_mul_nat_sub_one_pos {m : Nat} (hm : 1 <= m) :
    (0 : Rat) < 4 * (m : Rat) - 1 := by
  have hm_rat : (1 : Rat) <= m := by exact_mod_cast hm
  nlinarith

/-- Swanepoel's general coefficient is strictly larger than `1 / 4`. -/
lemma one_fourth_lt_density_of_pos_nat {m : Nat} (hm : 1 <= m) :
    (1 : Rat) / 4 < density (m : Rat) := by
  have hden_pos : (0 : Rat) < 4 * (m : Rat) - 1 :=
    four_mul_nat_sub_one_pos hm
  unfold density
  field_simp [hden_pos.ne']
  nlinarith

/-! ## The `m = 8` specializations used for the `8 / 31` bound -/

@[simp] lemma m8_denominator_nat : 4 * (8 : Nat) - 1 = 31 := by
  norm_num

@[simp] lemma m8_denominator_rat : 4 * (8 : Rat) - 1 = 31 := by
  norm_num

@[simp] lemma m8_density : density (8 : Rat) = (8 : Rat) / 31 := by
  unfold density
  norm_num

@[simp] lemma m8_long_arc_length : 2 * (8 : Nat) - 3 = 13 := by
  norm_num

@[simp] lemma m8_r_s_range_end : 2 * (8 : Nat) - 5 = 11 := by
  norm_num

@[simp] lemma m8_lemma10_range_end : 2 * (8 : Nat) - 6 = 10 := by
  norm_num

@[simp] lemma m8_late_triple_bound : 2 * (8 : Nat) - 10 = 6 := by
  norm_num

/-- The last arithmetic step in Lemma 9. -/
lemma floor_half_plus_six_gt_imp_late (a m : Nat)
    (h : m < a / 2 + 6) :
    2 * m - 10 <= a := by
  omega

/-! ## Finite index arithmetic for the final `m = 8` contradiction -/

/-- A cardinal statement of "at most one failure" implies uniqueness of any
two failures in the index range `1, ..., 10`. -/
lemma unique_failure_of_card_le_one
    (good : Nat -> Prop) [DecidablePred good]
    (hcard : ((Finset.Icc 1 10).filter fun i => Not (good i)).card <= 1) :
    forall {i j : Nat}, 1 <= i -> i <= 10 -> 1 <= j -> j <= 10 ->
      Not (good i) -> Not (good j) -> i = j := by
  intro i j hi1 hi10 hj1 hj10 hbi hbj
  by_contra hne
  let failures := (Finset.Icc 1 10).filter fun i => Not (good i)
  have hfail_card : failures.card <= 1 := by
    simpa [failures] using hcard
  have hpair_subset : ({i, j} : Finset Nat) <= failures := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [failures, hi1, hi10, hbi]
    · simp [failures, hj1, hj10, hbj]
  have hpair_card : ({i, j} : Finset Nat).card = 2 := by
    simp [hne]
  have htwo_le : 2 <= failures.card := by
    rw [<- hpair_card]
    exact Finset.card_le_card hpair_subset
  have : 2 <= 1 := le_trans htwo_le hfail_card
  omega

/-- If at most one of the indices `1, ..., 10` fails, then there is a triple of
consecutive good indices starting no later than `4`. -/
lemma early_triple_of_at_most_one_failure
    (good : Nat -> Prop)
    (huniq :
      forall {i j : Nat}, 1 <= i -> i <= 10 -> 1 <= j -> j <= 10 ->
        Not (good i) -> Not (good j) -> i = j) :
    exists a : Nat, 1 <= a /\ a <= 4 /\
      good a /\ good (a + 1) /\ good (a + 2) := by
  classical
  by_cases h1 : good 1
  · by_cases h2 : good 2
    · by_cases h3 : good 3
      · exact ⟨1, by norm_num, by norm_num, h1, by simpa using h2,
          by simpa using h3⟩
      · have h4 : good 4 := by
          by_contra h4
          have : (3 : Nat) = 4 :=
            huniq (i := 3) (j := 4)
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) h3 h4
          omega
        have h5 : good 5 := by
          by_contra h5
          have : (3 : Nat) = 5 :=
            huniq (i := 3) (j := 5)
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) h3 h5
          omega
        have h6 : good 6 := by
          by_contra h6
          have : (3 : Nat) = 6 :=
            huniq (i := 3) (j := 6)
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) h3 h6
          omega
        exact ⟨4, by norm_num, by norm_num, h4, by simpa using h5,
          by simpa using h6⟩
    · have h3 : good 3 := by
        by_contra h3
        have : (2 : Nat) = 3 :=
          huniq (i := 2) (j := 3)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) h2 h3
        omega
      have h4 : good 4 := by
        by_contra h4
        have : (2 : Nat) = 4 :=
          huniq (i := 2) (j := 4)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) h2 h4
        omega
      have h5 : good 5 := by
        by_contra h5
        have : (2 : Nat) = 5 :=
          huniq (i := 2) (j := 5)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) h2 h5
        omega
      exact ⟨3, by norm_num, by norm_num, h3, by simpa using h4,
        by simpa using h5⟩
  · have h2 : good 2 := by
      by_contra h2
      have : (1 : Nat) = 2 :=
        huniq (i := 1) (j := 2)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2
      omega
    have h3 : good 3 := by
      by_contra h3
      have : (1 : Nat) = 3 :=
        huniq (i := 1) (j := 3)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h3
      omega
    have h4 : good 4 := by
      by_contra h4
      have : (1 : Nat) = 4 :=
        huniq (i := 1) (j := 4)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h4
      omega
    exact ⟨2, by norm_num, by norm_num, h2, by simpa using h3,
      by simpa using h4⟩

/-- Cardinal form of the finite pigeonhole step in E24. -/
lemma early_triple_of_card_le_one_failure
    (good : Nat -> Prop) [DecidablePred good]
    (hcard : ((Finset.Icc 1 10).filter fun i => Not (good i)).card <= 1) :
    exists a : Nat, 1 <= a /\ a <= 4 /\
      good a /\ good (a + 1) /\ good (a + 2) := by
  exact early_triple_of_at_most_one_failure good
    (unique_failure_of_card_le_one good hcard)

/-- The pure index contradiction used after setting `m = 8`: Lemma 10 gives at
most one failure in `1, ..., 10`, while Lemma 9 makes every good triple start
at least at `6`. -/
theorem final_m8_index_contradiction
    (good : Nat -> Prop) [DecidablePred good]
    (hcard : ((Finset.Icc 1 10).filter fun i => Not (good i)).card <= 1)
    (hlate : forall a : Nat, good a -> good (a + 1) -> good (a + 2) -> 6 <= a) :
    False := by
  obtain ⟨a, _ha1, ha4, hga, hga1, hga2⟩ :=
    early_triple_of_card_le_one_failure good hcard
  have hlate_a : 6 <= a := hlate a hga hga1 hga2
  omega

end Arithmetic
end Swanepoel
end ErdosProblems1066
