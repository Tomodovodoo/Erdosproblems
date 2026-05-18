import ErdosProblems1066.PachToth.Arithmetic
import ErdosProblems1066.UnitDistanceBounds

set_option autoImplicit false

/-!
# Explicit Pach--Toth Remainder Configurations

The remainder part of the Pach--Toth arbitrary-`n` construction needs, for
each `r`, a configuration on `r` vertices whose independent sets have size at
most `ceilDiv r 3`.

Rather than reprove triangle geometry here, this module reuses the checked
`upper_bound_third` equilateral-triangle construction on
`3 * ceilDiv r 3` vertices and takes the first `r` vertices as an induced
subconfiguration.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace RemainderConstruction

open Arithmetic

lemma le_three_mul_ceilDiv_three (r : Nat) :
    r <= 3 * ceilDiv r 3 := by
  unfold ceilDiv
  omega

lemma ceilDiv_three_pos_of_pos {r : Nat} (hr : 0 < r) :
    0 < ceilDiv r 3 := by
  unfold ceilDiv
  omega

/-- Restrict a unit-distance configuration along an injective vertex map. -/
def restrictConfig {n m : Nat} (C : _root_.UDConfig m)
    (f : Fin n -> Fin m) (hf : Function.Injective f) :
    _root_.UDConfig n where
  pts := fun i => C.pts (f i)
  sep := by
    intro i j hij
    exact C.sep (f i) (f j) (fun h => hij (hf h))

lemma image_indep_of_restrictConfig {n m : Nat} (C : _root_.UDConfig m)
    {f : Fin n -> Fin m} {hf : Function.Injective f}
    {s : Finset (Fin n)}
    (hs : (restrictConfig C f hf).IsIndep s) :
    C.IsIndep (s.image f) := by
  intro x hx y hy hxy hunit
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
  have hij : i ≠ j := by
    intro hij
    exact hxy (by rw [hij])
  exact hs i hi j hj hij hunit

/-- The first `r` vertices inside a larger `3 * k` configuration. -/
def initialEmbedding (r k : Nat) (h : r <= 3 * k) : Fin r -> Fin (3 * k) :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩

lemma initialEmbedding_injective {r k : Nat} {h : r <= 3 * k} :
    Function.Injective (initialEmbedding r k h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin (3 * k) => x.val) hij)

/-- The empty remainder configuration. -/
def emptyConfig : _root_.UDConfig 0 where
  pts := fun i => nomatch i
  sep := by
    intro i
    exact Fin.elim0 i

lemma empty_independent_card_le (s : Finset (Fin 0)) :
    s.card <= ceilDiv 0 3 := by
  have hs : s = ∅ := by
    ext x
    exact Fin.elim0 x
  simp [hs, ceilDiv]

/-- There is a checked remainder configuration on `r` vertices whose
independent sets have size at most `ceilDiv r 3`. -/
theorem exists_remainder_config (r : Nat) :
    Exists fun C : _root_.UDConfig r =>
      forall s : Finset (Fin r), C.IsIndep s -> s.card <= ceilDiv r 3 := by
  by_cases hr : r = 0
  · subst r
    exact ⟨emptyConfig, fun s _hs => empty_independent_card_le s⟩
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let k := ceilDiv r 3
    have hk : 0 < k := ceilDiv_three_pos_of_pos hrpos
    have hle : r <= 3 * k := le_three_mul_ceilDiv_three r
    obtain ⟨Cfull, hCfull⟩ := _root_.upper_bound_third k hk
    let f : Fin r -> Fin (3 * k) := initialEmbedding r k hle
    have hf : Function.Injective f := initialEmbedding_injective
    refine ⟨restrictConfig Cfull f hf, ?_⟩
    intro s hs
    have himage : Cfull.IsIndep (s.image f) :=
      image_indep_of_restrictConfig Cfull hs
    have hbound := hCfull (s.image f) himage
    have hcard : (s.image f).card = s.card := by
      rw [Finset.card_image_of_injective]
      exact hf
    simpa [k, hcard] using hbound

/-- The finite Pach--Toth remainder range used by the `n % 16` split. -/
theorem exists_remainder_config_mod_sixteen {r : Nat} (_hr : r < 16) :
    Exists fun C : _root_.UDConfig r =>
      forall s : Finset (Fin r), C.IsIndep s -> s.card <= ceilDiv r 3 :=
  exists_remainder_config r

end RemainderConstruction
end PachToth
end ErdosProblems1066

end
