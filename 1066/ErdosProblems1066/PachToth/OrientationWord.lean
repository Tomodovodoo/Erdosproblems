import ErdosProblems1066.PachToth.PeriodInterface

set_option autoImplicit false

/-!
# Finite orientation words

This module packages the finite same/opposite orientation data used by
generated Pach--Toth chains.  It deliberately contains only pure finite data:
no computed search result, external certificate, or geometric assumption is
introduced here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace OrientationWord

open Arithmetic
open FiniteGraph

abbrev Orientation := OrientationData.BlockOrientation
abbrev R2 := Prod Real Real

/-- The cyclic index reached after reading `n` letters from the first block. -/
def natIndex {k : Nat} (hk : 0 < k) (n : Nat) : Fin k :=
  ((cyclicSucc hk)^[n]) (Fin.mk 0 hk : Fin k)

@[simp]
theorem natIndex_zero {k : Nat} (hk : 0 < k) :
    natIndex hk 0 = (Fin.mk 0 hk : Fin k) :=
  rfl

/-- The next natural position is the cyclic successor of the current index. -/
theorem natIndex_succ {k : Nat} (hk : 0 < k) (n : Nat) :
    natIndex hk (n + 1) = cyclicSucc hk (natIndex hk n) :=
  cyclicSucc_iterate_succ_apply' hk n (Fin.mk 0 hk : Fin k)

/-- Split a natural read into a prefix walk and a remaining cyclic walk. -/
theorem natIndex_add {k : Nat} (hk : 0 < k) (m n : Nat) :
    natIndex hk (m + n) = ((cyclicSucc hk)^[m]) (natIndex hk n) :=
  cyclicSucc_iterate_add_apply hk m n (Fin.mk 0 hk : Fin k)

/-- Closed form for `natIndex`. -/
theorem natIndex_eq_mk {k : Nat} (hk : 0 < k) (n : Nat) :
    natIndex hk n = Fin.mk (n % k) (Nat.mod_lt n hk) :=
  cyclicSucc_iterate_zero_eq_mk hk n

/-- Before the first wraparound, natural and finite indices agree. -/
theorem natIndex_of_lt {k : Nat} (hk : 0 < k) {n : Nat} (hn : n < k) :
    natIndex hk n = (Fin.mk n hn : Fin k) :=
  cyclicSucc_iterate_zero_eq_mk_of_lt hk hn

@[simp]
theorem natIndex_card {k : Nat} (hk : 0 < k) :
    natIndex hk k = (Fin.mk 0 hk : Fin k) :=
  cyclicSucc_iterate_card hk (Fin.mk 0 hk : Fin k)

@[simp]
theorem natIndex_add_card {k : Nat} (hk : 0 < k) (n : Nat) :
    natIndex hk (n + k) = natIndex hk n :=
  cyclicSucc_iterate_add_card_apply hk n (Fin.mk 0 hk : Fin k)

@[simp]
theorem natIndex_card_add {k : Nat} (hk : 0 < k) (n : Nat) :
    natIndex hk (k + n) = natIndex hk n :=
  cyclicSucc_iterate_card_add_apply hk n (Fin.mk 0 hk : Fin k)

@[simp]
theorem natIndex_add_mul_card {k : Nat} (hk : 0 < k) (n m : Nat) :
    natIndex hk (n + m * k) = natIndex hk n :=
  cyclicSucc_iterate_add_mul_card_apply hk n m (Fin.mk 0 hk : Fin k)

@[simp]
theorem natIndex_mul_card_add {k : Nat} (hk : 0 < k) (m n : Nat) :
    natIndex hk (m * k + n) = natIndex hk n :=
  cyclicSucc_iterate_mul_card_add_apply hk m n (Fin.mk 0 hk : Fin k)

/-- Natural positions with the same residue modulo `k` read the same index. -/
theorem natIndex_eq_of_mod_eq {k : Nat} (hk : 0 < k) {m n : Nat}
    (hmod : m % k = n % k) :
    natIndex hk m = natIndex hk n :=
  cyclicSucc_iterate_eq_of_mod_eq hk hmod (Fin.mk 0 hk : Fin k)

/-- Any natural position may be reduced modulo the word length. -/
theorem natIndex_eq_natIndex_mod {k : Nat} (hk : 0 < k) (n : Nat) :
    natIndex hk n = natIndex hk (n % k) :=
  cyclicSucc_iterate_eq_iterate_mod_card hk n (Fin.mk 0 hk : Fin k)

@[simp]
theorem natIndex_mod {k : Nat} (hk : 0 < k) (n : Nat) :
    natIndex hk (n % k) = natIndex hk n :=
  (natIndex_eq_natIndex_mod hk n).symm

/-- A generated-chain length divisible by `k` returns to the first index. -/
theorem natIndex_eq_zero_of_dvd {k : Nat} (hk : 0 < k) {n : Nat}
    (hn : k ∣ n) :
    natIndex hk n = (Fin.mk 0 hk : Fin k) :=
  cyclicSucc_iterate_zero_eq_zero_of_dvd hk hn

/-- A finite word of relative block orientations. -/
structure Word (k : Nat) where
  letter : Fin k -> Orientation

namespace Word

instance instCoeFun {k : Nat} : CoeFun (Word k) (fun _ => Fin k -> Orientation) where
  coe W := W.letter

/-- Two words are equal when all their finite positions agree. -/
theorem ext {k : Nat} {A B : Word k}
    (h : forall i : Fin k, A i = B i) : A = B := by
  cases A with
  | mk Aletter =>
      cases B with
      | mk Bletter =>
          congr
          funext i
          exact h i

/-- Build a word from the raw finite function expected by generated chains. -/
def ofFin {k : Nat} (orientation : Fin k -> Orientation) : Word k where
  letter := orientation

@[simp]
theorem ofFin_apply {k : Nat} (orientation : Fin k -> Orientation)
    (i : Fin k) :
    (ofFin orientation) i = orientation i :=
  rfl

/-- Forget a word to the raw finite function expected by generated chains. -/
def toFin {k : Nat} (W : Word k) : Fin k -> Orientation :=
  W.letter

@[simp]
theorem toFin_apply {k : Nat} (W : Word k) (i : Fin k) :
    W.toFin i = W i :=
  rfl

/-- Read the word at a finite cyclic index. -/
def atFin {k : Nat} (W : Word k) (i : Fin k) : Orientation :=
  W i

@[simp]
theorem atFin_apply {k : Nat} (W : Word k) (i : Fin k) :
    W.atFin i = W i :=
  rfl

/-- Periodically read the word at a natural-number position. -/
def toNat {k : Nat} (W : Word k) (hk : 0 < k) : Nat -> Orientation :=
  fun n => W (natIndex hk n)

@[simp]
theorem toNat_apply {k : Nat} (W : Word k) (hk : 0 < k) (n : Nat) :
    W.toNat hk n = W (natIndex hk n) :=
  rfl

@[simp]
theorem toNat_zero {k : Nat} (W : Word k) (hk : 0 < k) :
    W.toNat hk 0 = W (Fin.mk 0 hk : Fin k) :=
  rfl

/-- Before wraparound, periodic natural reading agrees with direct finite
reading. -/
theorem toNat_of_lt {k : Nat} (W : Word k) (hk : 0 < k)
    {n : Nat} (hn : n < k) :
    W.toNat hk n = W (Fin.mk n hn : Fin k) := by
  rw [toNat_apply, natIndex_of_lt hk hn]

/-- Natural reading may be reduced modulo the word length. -/
theorem toNat_eq_toNat_mod {k : Nat} (W : Word k) (hk : 0 < k) (n : Nat) :
    W.toNat hk n = W.toNat hk (n % k) := by
  rw [toNat_apply, toNat_apply, natIndex_eq_natIndex_mod hk n]

@[simp]
theorem toNat_mod {k : Nat} (W : Word k) (hk : 0 < k) (n : Nat) :
    W.toNat hk (n % k) = W.toNat hk n :=
  (toNat_eq_toNat_mod W hk n).symm

@[simp]
theorem toNat_add_card {k : Nat} (W : Word k) (hk : 0 < k) (n : Nat) :
    W.toNat hk (n + k) = W.toNat hk n := by
  simp [toNat]

@[simp]
theorem toNat_card_add {k : Nat} (W : Word k) (hk : 0 < k) (n : Nat) :
    W.toNat hk (k + n) = W.toNat hk n := by
  simp [toNat]

@[simp]
theorem toNat_add_mul_card {k : Nat} (W : Word k) (hk : 0 < k)
    (n m : Nat) :
    W.toNat hk (n + m * k) = W.toNat hk n := by
  simp [toNat]

@[simp]
theorem toNat_mul_card_add {k : Nat} (W : Word k) (hk : 0 < k)
    (m n : Nat) :
    W.toNat hk (m * k + n) = W.toNat hk n := by
  simp [toNat]

/-- Natural positions with the same residue modulo `k` read the same letter. -/
theorem toNat_eq_of_mod_eq {k : Nat} (W : Word k) (hk : 0 < k)
    {m n : Nat} (hmod : m % k = n % k) :
    W.toNat hk m = W.toNat hk n := by
  rw [toNat_apply, toNat_apply, natIndex_eq_of_mod_eq hk hmod]

/-- The generated-chain reader used in `GeneratedClosedChain`: positions past
the finite word default to the first letter. -/
def toGeneratedNat {k : Nat} (W : Word k) (hk : 0 < k) :
    Nat -> Orientation :=
  fun n => if h : n < k then W (Fin.mk n h) else W (Fin.mk 0 hk)

@[simp]
theorem toGeneratedNat_of_lt {k : Nat} (W : Word k) (hk : 0 < k)
    {n : Nat} (hn : n < k) :
    W.toGeneratedNat hk n = W (Fin.mk n hn : Fin k) := by
  simp [toGeneratedNat, hn]

@[simp]
theorem toGeneratedNat_zero {k : Nat} (W : Word k) (hk : 0 < k) :
    W.toGeneratedNat hk 0 = W (Fin.mk 0 hk : Fin k) := by
  simp [toGeneratedNat, hk]

theorem toGeneratedNat_eq_toNat_of_lt {k : Nat} (W : Word k) (hk : 0 < k)
    {n : Nat} (hn : n < k) :
    W.toGeneratedNat hk n = W.toNat hk n := by
  rw [toGeneratedNat_of_lt W hk hn, toNat_of_lt W hk hn]

/-- The generated-chain `orientationAt` reader is the generated reader of the
word record. -/
theorem generated_orientationAt_eq_toGeneratedNat {k : Nat} (W : Word k)
    (hk : 0 < k) (n : Nat) :
    GeneratedClosedChain.orientationAt hk W.toFin n =
      W.toGeneratedNat hk n := by
  simp [GeneratedClosedChain.orientationAt, toGeneratedNat, toFin]

theorem generated_orientationAt_eq_toNat_of_lt {k : Nat} (W : Word k)
    (hk : 0 < k) {n : Nat} (hn : n < k) :
    GeneratedClosedChain.orientationAt hk W.toFin n = W.toNat hk n := by
  rw [generated_orientationAt_eq_toGeneratedNat W hk n,
    toGeneratedNat_eq_toNat_of_lt W hk hn]

/-- Generated block using the word wrapper. -/
def generatedBlock
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : Word k) :
    Nat -> LocalVertex -> R2 :=
  GeneratedClosedChain.generatedBlock O hk base W.toFin

/-- Generated point map using the word wrapper. -/
def generatedPoint
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : Word k) :
    Fin k -> LocalVertex -> R2 :=
  GeneratedClosedChain.generatedPoint O hk base W.toFin

/-- Generated period equation using the word wrapper. -/
def generatedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : Word k) : Prop :=
  PeriodInterface.GeneratedPeriodEquation O hk base W.toFin

/-- Algebraic generated closure equation using the word wrapper. -/
def generatedClosureEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : Word k) : Prop :=
  PeriodInterface.GeneratedClosureEquation O hk base W.toFin

/-- Word-wrapper form of the period/closure equivalence. -/
theorem generatedPeriodEquation_iff_generatedClosureEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : Word k) :
    generatedPeriodEquation O hk base W <->
      generatedClosureEquation O hk base W :=
  PeriodInterface.generatedPeriodEquation_iff_generatedClosureEquation
    O hk base W.toFin

theorem generatedClosureEquation_of_generatedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : Word k)
    (hperiod : generatedPeriodEquation O hk base W) :
    generatedClosureEquation O hk base W :=
  (generatedPeriodEquation_iff_generatedClosureEquation O hk base W).mp
    hperiod

theorem generatedPeriodEquation_of_generatedClosureEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : Word k)
    (hclosure : generatedClosureEquation O hk base W) :
    generatedPeriodEquation O hk base W :=
  (generatedPeriodEquation_iff_generatedClosureEquation O hk base W).mpr
    hclosure

end Word

/-- Positive-length orientation-word data in the shape expected by a period
search interface. -/
structure SearchData where
  k : Nat
  hk : 0 < k
  word : Word k

namespace SearchData

/-- Build search data from the raw finite function used by generated chains. -/
def ofFin {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> Orientation) : SearchData where
  k := k
  hk := hk
  word := Word.ofFin orientation

/-- The raw finite orientation function expected by generated-chain APIs. -/
def orientation (D : SearchData) : Fin D.k -> Orientation :=
  D.word.toFin

@[simp]
theorem orientation_apply (D : SearchData) (i : Fin D.k) :
    D.orientation i = D.word i :=
  rfl

@[simp]
theorem ofFin_orientation_apply {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> Orientation) (i : Fin k) :
    (ofFin hk orientation).orientation i = orientation i :=
  rfl

/-- Periodic natural-number reader for period-search style data. -/
def periodicOrientation (D : SearchData) : Nat -> Orientation :=
  D.word.toNat D.hk

@[simp]
theorem periodicOrientation_apply (D : SearchData) (n : Nat) :
    D.periodicOrientation n = D.word (natIndex D.hk n) :=
  rfl

/-- Generated-chain reader, matching `GeneratedClosedChain.orientationAt`. -/
def generatedOrientation (D : SearchData) : Nat -> Orientation :=
  D.word.toGeneratedNat D.hk

theorem generatedOrientation_eq_orientationAt (D : SearchData) (n : Nat) :
    D.generatedOrientation n =
      GeneratedClosedChain.orientationAt D.hk D.orientation n := by
  exact (Word.generated_orientationAt_eq_toGeneratedNat D.word D.hk n).symm

theorem periodicOrientation_of_lt (D : SearchData)
    {n : Nat} (hn : n < D.k) :
    D.periodicOrientation n = D.orientation (Fin.mk n hn) :=
  Word.toNat_of_lt D.word D.hk hn

theorem generatedOrientation_eq_periodicOrientation_of_lt (D : SearchData)
    {n : Nat} (hn : n < D.k) :
    D.generatedOrientation n = D.periodicOrientation n :=
  Word.toGeneratedNat_eq_toNat_of_lt D.word D.hk hn

@[simp]
theorem periodicOrientation_add_card (D : SearchData) (n : Nat) :
    D.periodicOrientation (n + D.k) = D.periodicOrientation n :=
  Word.toNat_add_card D.word D.hk n

@[simp]
theorem periodicOrientation_card_add (D : SearchData) (n : Nat) :
    D.periodicOrientation (D.k + n) = D.periodicOrientation n :=
  Word.toNat_card_add D.word D.hk n

@[simp]
theorem periodicOrientation_add_mul_card (D : SearchData) (n m : Nat) :
    D.periodicOrientation (n + m * D.k) = D.periodicOrientation n :=
  Word.toNat_add_mul_card D.word D.hk n m

theorem periodicOrientation_eq_of_mod_eq (D : SearchData)
    {m n : Nat} (hmod : m % D.k = n % D.k) :
    D.periodicOrientation m = D.periodicOrientation n :=
  Word.toNat_eq_of_mod_eq D.word D.hk hmod

/-- Period equation for the stored finite word. -/
def generatedPeriodEquation
    (D : SearchData)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2) : Prop :=
  Word.generatedPeriodEquation O D.hk base D.word

/-- Algebraic closure equation for the stored finite word. -/
def generatedClosureEquation
    (D : SearchData)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2) : Prop :=
  Word.generatedClosureEquation O D.hk base D.word

theorem generatedPeriodEquation_iff_generatedClosureEquation
    (D : SearchData)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2) :
    D.generatedPeriodEquation O base <->
      D.generatedClosureEquation O base :=
  Word.generatedPeriodEquation_iff_generatedClosureEquation O D.hk base D.word

theorem generatedClosureEquation_of_generatedPeriodEquation
    (D : SearchData)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2)
    (hperiod : D.generatedPeriodEquation O base) :
    D.generatedClosureEquation O base :=
  (D.generatedPeriodEquation_iff_generatedClosureEquation O base).mp hperiod

theorem generatedPeriodEquation_of_generatedClosureEquation
    (D : SearchData)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2)
    (hclosure : D.generatedClosureEquation O base) :
    D.generatedPeriodEquation O base :=
  (D.generatedPeriodEquation_iff_generatedClosureEquation O base).mpr hclosure

end SearchData

end OrientationWord
end PachToth
end ErdosProblems1066
