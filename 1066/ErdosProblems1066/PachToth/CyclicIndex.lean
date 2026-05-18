import ErdosProblems1066.PachToth.Arithmetic

set_option autoImplicit false

/-!
# Reusable cyclic-index lemmas

This module packages arithmetic facts about the Pach--Toth cyclic successor.
It deliberately stays independent of the geometric realization layers.
-/

namespace ErdosProblems1066
namespace PachToth
namespace Arithmetic

/-- One cyclic-successor step is the first iterate. -/
@[simp]
theorem cyclicSucc_iterate_one {k : Nat} (hk : 0 < k) (i : Fin k) :
    ((cyclicSucc hk)^[1]) i = cyclicSucc hk i := by
  rfl

/-- The successor can be pulled out on the left of an iterate. -/
theorem cyclicSucc_iterate_succ_apply' {k : Nat} (hk : 0 < k)
    (n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[n + 1]) i =
      cyclicSucc hk (((cyclicSucc hk)^[n]) i) := by
  change ((cyclicSucc hk)^[Nat.succ n]) i =
    cyclicSucc hk (((cyclicSucc hk)^[n]) i)
  exact Function.iterate_succ_apply' (cyclicSucc hk) n i

/-- The successor can be pulled out on the right of an iterate. -/
theorem cyclicSucc_iterate_succ_apply {k : Nat} (hk : 0 < k)
    (n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[n + 1]) i =
      ((cyclicSucc hk)^[n]) (cyclicSucc hk i) := by
  change ((cyclicSucc hk)^[Nat.succ n]) i =
    ((cyclicSucc hk)^[n]) (cyclicSucc hk i)
  exact Function.iterate_succ_apply (cyclicSucc hk) n i

/-- Splitting a cyclic-successor iterate into two consecutive walks. -/
theorem cyclicSucc_iterate_add_apply {k : Nat} (hk : 0 < k)
    (m n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[m + n]) i =
      ((cyclicSucc hk)^[m]) (((cyclicSucc hk)^[n]) i) :=
  Function.iterate_add_apply (cyclicSucc hk) m n i

/-- Composition form of `cyclicSucc_iterate_add_apply`. -/
theorem cyclicSucc_iterate_add {k : Nat} (hk : 0 < k)
    (m n : Nat) :
    (cyclicSucc hk)^[m + n] =
      Function.comp ((cyclicSucc hk)^[m]) ((cyclicSucc hk)^[n]) :=
  Function.iterate_add (cyclicSucc hk) m n

/-- Two iterates of the same cyclic successor commute. -/
theorem cyclicSucc_iterate_comm {k : Nat} (hk : 0 < k)
    (m n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[m]) (((cyclicSucc hk)^[n]) i) =
      ((cyclicSucc hk)^[n]) (((cyclicSucc hk)^[m]) i) := by
  rw [<- Function.iterate_add_apply, Nat.add_comm,
    Function.iterate_add_apply]

/-- Walking once around the cycle, as a simp-normalized rewrite. -/
@[simp]
theorem cyclicSucc_iterate_card_apply {k : Nat} (hk : 0 < k) (i : Fin k) :
    ((cyclicSucc hk)^[k]) i = i :=
  cyclicSucc_iterate_card hk i

/-- `m` full turns around the cycle return to the starting index. -/
@[simp]
theorem cyclicSucc_iterate_mul_card_apply {k : Nat} (hk : 0 < k)
    (m : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[m * k]) i = i := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hmul : (m + 1) * k = m * k + k := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_mul m k)
      rw [hmul, Function.iterate_add_apply, cyclicSucc_iterate_card hk i, ih]

/-- `m` full turns around the cycle return to the starting index. -/
@[simp]
theorem cyclicSucc_iterate_card_mul_apply {k : Nat} (hk : 0 < k)
    (m : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[k * m]) i = i := by
  rw [Nat.mul_comm]
  exact cyclicSucc_iterate_mul_card_apply hk m i

/-- Any iterate whose length is divisible by the cycle length is the identity
on indices. -/
theorem cyclicSucc_iterate_eq_self_of_dvd {k : Nat} (hk : 0 < k)
    {n : Nat} (hn : k ∣ n) (i : Fin k) :
    ((cyclicSucc hk)^[n]) i = i := by
  rcases hn with ⟨m, rfl⟩
  exact cyclicSucc_iterate_card_mul_apply hk m i

/-- Appending full turns after a walk does not change the endpoint. -/
@[simp]
theorem cyclicSucc_iterate_add_mul_card_apply {k : Nat} (hk : 0 < k)
    (n m : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[n + m * k]) i =
      ((cyclicSucc hk)^[n]) i := by
  rw [Function.iterate_add_apply, cyclicSucc_iterate_mul_card_apply hk m i]

/-- Prepending full turns before a walk does not change the endpoint. -/
@[simp]
theorem cyclicSucc_iterate_mul_card_add_apply {k : Nat} (hk : 0 < k)
    (m n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[m * k + n]) i =
      ((cyclicSucc hk)^[n]) i := by
  rw [Function.iterate_add_apply,
    cyclicSucc_iterate_mul_card_apply hk m (((cyclicSucc hk)^[n]) i)]

/-- Appending full turns, with the full-turn count written as `k * m`. -/
@[simp]
theorem cyclicSucc_iterate_add_card_mul_apply {k : Nat} (hk : 0 < k)
    (n m : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[n + k * m]) i =
      ((cyclicSucc hk)^[n]) i := by
  rw [Nat.mul_comm]
  exact cyclicSucc_iterate_add_mul_card_apply hk n m i

/-- Prepending full turns, with the full-turn count written as `k * m`. -/
@[simp]
theorem cyclicSucc_iterate_card_mul_add_apply {k : Nat} (hk : 0 < k)
    (m n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[k * m + n]) i =
      ((cyclicSucc hk)^[n]) i := by
  rw [Nat.mul_comm]
  exact cyclicSucc_iterate_mul_card_add_apply hk m n i

/-- Adding one full turn after a walk does not change the endpoint. -/
@[simp]
theorem cyclicSucc_iterate_add_card_apply {k : Nat} (hk : 0 < k)
    (n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[n + k]) i =
      ((cyclicSucc hk)^[n]) i := by
  simpa using cyclicSucc_iterate_add_mul_card_apply hk n 1 i

/-- Adding one full turn before a walk does not change the endpoint. -/
@[simp]
theorem cyclicSucc_iterate_card_add_apply {k : Nat} (hk : 0 < k)
    (n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[k + n]) i =
      ((cyclicSucc hk)^[n]) i := by
  simpa using cyclicSucc_iterate_mul_card_add_apply hk 1 n i

/-- Appending any divisible-by-`k` walk does not change the endpoint. -/
theorem cyclicSucc_iterate_add_of_dvd {k : Nat} (hk : 0 < k)
    (n : Nat) {p : Nat} (hp : k ∣ p) (i : Fin k) :
    ((cyclicSucc hk)^[n + p]) i =
      ((cyclicSucc hk)^[n]) i := by
  rcases hp with ⟨m, rfl⟩
  exact cyclicSucc_iterate_add_card_mul_apply hk n m i

/-- Prepending any divisible-by-`k` walk does not change the endpoint. -/
theorem cyclicSucc_iterate_dvd_add_apply {k : Nat} (hk : 0 < k)
    {p : Nat} (hp : k ∣ p) (n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[p + n]) i =
      ((cyclicSucc hk)^[n]) i := by
  rcases hp with ⟨m, rfl⟩
  exact cyclicSucc_iterate_card_mul_add_apply hk m n i

/-- Any cyclic-successor walk may be reduced modulo the cycle length. -/
theorem cyclicSucc_iterate_eq_iterate_mod_card {k : Nat} (hk : 0 < k)
    (n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[n]) i =
      ((cyclicSucc hk)^[n % k]) i := by
  have hdecomp : k * (n / k) + n % k = n := Nat.div_add_mod n k
  calc
    ((cyclicSucc hk)^[n]) i =
        ((cyclicSucc hk)^[k * (n / k) + n % k]) i := by
      rw [hdecomp]
    _ = ((cyclicSucc hk)^[n % k]) i := by
      rw [cyclicSucc_iterate_card_mul_add_apply hk]

/-- A modulo-reduced cyclic-successor walk has the same endpoint. -/
@[simp]
theorem cyclicSucc_iterate_mod_card_apply {k : Nat} (hk : 0 < k)
    (n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[n % k]) i =
      ((cyclicSucc hk)^[n]) i :=
  (cyclicSucc_iterate_eq_iterate_mod_card hk n i).symm

/-- The endpoint of a cyclic-successor walk as a canonical `Fin` constructor. -/
theorem cyclicSucc_iterate_eq_mk {k : Nat} (hk : 0 < k)
    (n : Nat) (i : Fin k) :
    ((cyclicSucc hk)^[n]) i =
      Fin.mk ((i.val + n) % k) (Nat.mod_lt (i.val + n) hk) := by
  apply Fin.ext
  exact cyclicSucc_iterate_val hk n i

/-- A closed form for generated chains beginning at `0`. -/
theorem cyclicSucc_iterate_zero_eq_mk {k : Nat} (hk : 0 < k)
    (n : Nat) :
    ((cyclicSucc hk)^[n]) (Fin.mk 0 hk : Fin k) =
      Fin.mk (n % k) (Nat.mod_lt n hk) := by
  simpa using cyclicSucc_iterate_eq_mk hk n (Fin.mk 0 hk : Fin k)

/-- A short generated chain beginning at `0` lands at the matching index. -/
theorem cyclicSucc_iterate_zero_eq_mk_of_lt {k : Nat} (hk : 0 < k)
    {n : Nat} (hn : n < k) :
    ((cyclicSucc hk)^[n]) (Fin.mk 0 hk : Fin k) = Fin.mk n hn := by
  simpa [Nat.mod_eq_of_lt hn] using cyclicSucc_iterate_zero_eq_mk hk n

/-- A generated chain whose length is divisible by `k` closes at `0`. -/
theorem cyclicSucc_iterate_zero_eq_zero_of_dvd {k : Nat} (hk : 0 < k)
    {n : Nat} (hn : k ∣ n) :
    ((cyclicSucc hk)^[n]) (Fin.mk 0 hk : Fin k) = Fin.mk 0 hk :=
  cyclicSucc_iterate_eq_self_of_dvd hk hn (Fin.mk 0 hk : Fin k)

/-- Two walks with congruent lengths modulo `k` end at the same index. -/
theorem cyclicSucc_iterate_eq_of_mod_eq {k : Nat} (hk : 0 < k)
    {m n : Nat} (hmod : m % k = n % k) (i : Fin k) :
    ((cyclicSucc hk)^[m]) i =
      ((cyclicSucc hk)^[n]) i := by
  rw [cyclicSucc_iterate_eq_iterate_mod_card hk m i,
    cyclicSucc_iterate_eq_iterate_mod_card hk n i, hmod]

end Arithmetic
end PachToth
end ErdosProblems1066
