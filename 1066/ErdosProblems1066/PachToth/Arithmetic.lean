import Mathlib

set_option autoImplicit false

/-!
# Pach--Toth finite arithmetic

Small arithmetic lemmas extracted from the Pach--Toth plan.  These lemmas do
not use the geometric realization or the Figure 2 graph transcription.
-/

namespace ErdosProblems1066
namespace PachToth
namespace Arithmetic

/-- A local ASCII spelling of natural-number ceiling division. -/
def ceilDiv (a b : Nat) : Nat :=
  (a + b - 1) / b

/-- The cyclic successor on `Fin k`, used for block chains. -/
def cyclicSucc {k : Nat} (hk : 0 < k) (i : Fin k) : Fin k := by
  haveI : NeZero k := NeZero.of_pos hk
  exact i + (1 : Fin k)

lemma cyclicSucc_injective {k : Nat} (hk : 0 < k) :
    Function.Injective (cyclicSucc hk) := by
  haveI : NeZero k := NeZero.of_pos hk
  intro i j h
  exact (Equiv.addRight (1 : Fin k)).injective h

/-- After `t` cyclic-successor steps, the underlying `Fin` value has advanced
by `t` modulo the block count. -/
lemma cyclicSucc_iterate_val {k : Nat} (hk : 0 < k)
    (t : Nat) (i : Fin k) :
    (((cyclicSucc hk)^[t]) i).val = (i.val + t) % k := by
  haveI : NeZero k := NeZero.of_pos hk
  induction t with
  | zero =>
      simp [Nat.mod_eq_of_lt i.isLt]
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      calc
        (cyclicSucc hk (((cyclicSucc hk)^[t]) i)).val =
            ((((cyclicSucc hk)^[t]) i).val + 1) % k := by
          simp [cyclicSucc, Fin.val_add]
        _ = (((i.val + t) % k) + 1) % k := by
          rw [ih]
        _ = (i.val + (t + 1)) % k := by
          rw [Nat.mod_add_mod]
          simp [Nat.add_assoc]

/-- Walking once around the cyclic successor on `Fin k` returns to the
starting block. -/
theorem cyclicSucc_iterate_card {k : Nat} (hk : 0 < k) (i : Fin k) :
    ((cyclicSucc hk)^[k]) i = i := by
  apply Fin.ext
  rw [cyclicSucc_iterate_val hk k i]
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt i.isLt

/--
If every block has size at most `6`, and every full block has a successor of
size at most `4`, then the average block size is at most `5`.

The successor is kept abstract here; closed cyclic chains can instantiate it
with their block-successor permutation.
-/
lemma cyclicAverageSixFourOfInjective
    {alpha : Type} [Fintype alpha]
    (next : alpha -> alpha) (hnext : Function.Injective next)
    (a : alpha -> Nat)
    (hle6 : forall i, a i <= 6)
    (hfull : forall i, a i = 6 -> a (next i) <= 4) :
    (Finset.univ.sum a) <= 5 * Fintype.card alpha := by
  classical
  let fullSet : Finset alpha := Finset.univ.filter fun i => a i = 6
  let deficitSet : Finset alpha := Finset.univ.filter fun i => a i <= 4
  have hfull_card : fullSet.card <= deficitSet.card := by
    refine Finset.card_le_card_of_injOn next ?_ hnext.injOn
    intro i hi
    simp only [fullSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
    simp only [deficitSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hfull i hi
  let fullIndicator : alpha -> Nat := fun i => if a i = 6 then 1 else 0
  let deficitIndicator : alpha -> Nat := fun i => if a i <= 4 then 1 else 0
  have hpoint : forall i, a i + deficitIndicator i <= 5 + fullIndicator i := by
    intro i
    have hi6 : a i <= 6 := hle6 i
    dsimp [fullIndicator, deficitIndicator]
    by_cases h6 : a i = 6
    case pos =>
      simp [h6]
    case neg =>
      by_cases h4 : a i <= 4
      case pos =>
        simp [h6, h4]
        omega
      case neg =>
        simp [h6, h4]
        omega
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset alpha)) (fun i _ => hpoint i)
  have hdef_sum : (Finset.univ.sum deficitIndicator) = deficitSet.card := by
    dsimp [deficitIndicator, deficitSet]
    rw [show
      (Finset.univ.sum fun i : alpha => if a i <= 4 then (1 : Nat) else 0) =
        (Finset.univ.filter fun i : alpha => a i <= 4).card by
      exact (Finset.card_filter (fun i : alpha => a i <= 4) Finset.univ).symm]
  have hfull_sum : (Finset.univ.sum fullIndicator) = fullSet.card := by
    dsimp [fullIndicator, fullSet]
    rw [show
      (Finset.univ.sum fun i : alpha => if a i = 6 then (1 : Nat) else 0) =
        (Finset.univ.filter fun i : alpha => a i = 6).card by
      exact (Finset.card_filter (fun i : alpha => a i = 6) Finset.univ).symm]
  have hleft :
      (Finset.univ.sum fun i : alpha => a i + deficitIndicator i) =
        Finset.univ.sum a + deficitSet.card := by
    rw [Finset.sum_add_distrib, hdef_sum]
  have hconst :
      (Finset.univ.sum fun _ : alpha => (5 : Nat)) =
        5 * Fintype.card alpha := by
    simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]
  have hright :
      (Finset.univ.sum fun i : alpha => 5 + fullIndicator i) =
        5 * Fintype.card alpha + fullSet.card := by
    rw [Finset.sum_add_distrib, hconst, hfull_sum]
  rw [hleft, hright] at hsum
  omega

/-- The cyclic averaging lemma for the standard successor on `Fin k`. -/
lemma CyclicAverageSixFour
    {k : Nat} (hk : 0 < k) (a : Fin k -> Nat)
    (hle6 : forall i, a i <= 6)
    (hfull : forall i, a i = 6 -> a (cyclicSucc hk i) <= 4) :
    (Finset.univ.sum a) <= 5 * k := by
  simpa [Fintype.card_fin] using
    cyclicAverageSixFourOfInjective (cyclicSucc hk) (cyclicSucc_injective hk)
      a hle6 hfull

/-- The residue arithmetic used when adding the `n % 16` remainder vertices. -/
lemma RemainderArithmetic (n : Nat) :
    5 * (n / 16) + ceilDiv (n % 16) 3 <= ceilDiv (5 * n) 16 := by
  unfold ceilDiv
  omega

end Arithmetic
end PachToth
end ErdosProblems1066
