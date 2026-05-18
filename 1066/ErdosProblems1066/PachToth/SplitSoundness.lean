import ErdosProblems1066.PachToth.ArbitraryN
import ErdosProblems1066.PachToth.Bridge
import ErdosProblems1066.PachToth.RemainderConstruction

set_option autoImplicit false

/-!
# Pach--Toth split soundness

This module proves the checked combinatorial part of the arbitrary-`n`
chain/remainder bridge.

The geometry of placing the exact `16 * k` chain and the `r`-vertex
remainder far apart is kept explicit in `CanonicalSplitRealization`: it
supplies an actual combined `UDConfig (16 * k + r)` and states that the two
canonical blocks preserve the chain and remainder coordinates.  The proof
below then derives the independent-set bound by genuine finite-set splitting
and cardinal accounting.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SplitSoundness

open Arithmetic

/-- A checked upper-bound configuration on exactly `16 * k` vertices. -/
structure ExactChainUpper (k : Nat) where
  config : _root_.UDConfig (16 * k)
  independent_card_le_five_mul :
    forall s : Finset (Fin (16 * k)), config.IsIndep s -> s.card <= 5 * k

/-- A checked upper-bound configuration for a remainder block. -/
structure RemainderUpper (r : Nat) where
  config : _root_.UDConfig r
  independent_card_le_ceil_third :
    forall s : Finset (Fin r), config.IsIndep s -> s.card <= ceilDiv r 3

/-- The empty exact-chain upper certificate. -/
def emptyExactChainUpper : ExactChainUpper 0 where
  config :=
    { pts := fun i => Fin.elim0 i
      sep := by
        intro i
        exact Fin.elim0 i }
  independent_card_le_five_mul := by
    intro s _hs
    have hs : s = ∅ := by
      ext x
      exact Fin.elim0 x
    simp [hs]

/-- Convert the exact-multiple Pach--Toth target into an `ExactChainUpper`
certificate, with the zero case supplied by `emptyExactChainUpper`. -/
noncomputable def exactChainUpperOfTarget
    (H : targetUpperConstructionFiveSixteen) (k : Nat) : ExactChainUpper k := by
  by_cases hk : 0 < k
  · exact
      { config := Classical.choose (H k hk)
        independent_card_le_five_mul := Classical.choose_spec (H k hk) }
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    exact emptyExactChainUpper

/-- Use the checked remainder construction as a `RemainderUpper` certificate. -/
noncomputable def remainderUpperOfConstruction (r : Nat) : RemainderUpper r := by
  exact
    { config := Classical.choose (RemainderConstruction.exists_remainder_config r)
      independent_card_le_ceil_third :=
        Classical.choose_spec (RemainderConstruction.exists_remainder_config r) }

/--
A concrete combined configuration whose first `16 * k` canonical vertices are
the exact chain and whose last `r` canonical vertices are the remainder.

The `cross_far` field is the explicit geometric "far away" obligation: no
chain vertex and remainder vertex form a unit edge in the combined
configuration.  The counting theorem below does not need cross edges to be
absent for an upper bound, but the field records the intended geometric
separation needed by an actual construction.
-/
structure CanonicalSplitRealization (k r : Nat) where
  chain : ExactChainUpper k
  remainder : RemainderUpper r
  config : _root_.UDConfig (16 * k + r)
  chain_points :
    forall i : Fin (16 * k),
      config.pts (Fin.castAdd r i) = chain.config.pts i
  remainder_points :
    forall j : Fin r,
      config.pts (Fin.natAdd (16 * k) j) = remainder.config.pts j
  cross_far :
    forall (i : Fin (16 * k)) (j : Fin r),
      eucDist (config.pts (Fin.castAdd r i))
        (config.pts (Fin.natAdd (16 * k) j)) ≠ 1

/-- The vertices of an ambient independent set lying in the chain block,
pulled back to the chain index type. -/
def chainPart {k r : Nat} (_S : CanonicalSplitRealization k r)
    (s : Finset (Fin (16 * k + r))) : Finset (Fin (16 * k)) :=
  Finset.univ.filter fun i : Fin (16 * k) => Fin.castAdd r i ∈ s

/-- The vertices of an ambient independent set lying in the remainder block,
pulled back to the remainder index type. -/
def remainderPart {k r : Nat} (_S : CanonicalSplitRealization k r)
    (s : Finset (Fin (16 * k + r))) : Finset (Fin r) :=
  Finset.univ.filter fun j : Fin r => Fin.natAdd (16 * k) j ∈ s

lemma mem_chainPart {k r : Nat} {S : CanonicalSplitRealization k r}
    {s : Finset (Fin (16 * k + r))} {i : Fin (16 * k)} :
    i ∈ chainPart S s ↔ Fin.castAdd r i ∈ s := by
  simp [chainPart]

lemma mem_remainderPart {k r : Nat} {S : CanonicalSplitRealization k r}
    {s : Finset (Fin (16 * k + r))} {j : Fin r} :
    j ∈ remainderPart S s ↔ Fin.natAdd (16 * k) j ∈ s := by
  simp [remainderPart]

lemma chain_image_eq_filter {k r : Nat} (S : CanonicalSplitRealization k r)
    (s : Finset (Fin (16 * k + r))) :
    (chainPart S s).image (Fin.castAdd r) =
      s.filter fun v : Fin (16 * k + r) => v.val < 16 * k := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact Finset.mem_filter.mpr ⟨mem_chainPart.mp hi, by simp⟩
  · intro hv
    rcases Finset.mem_filter.mp hv with ⟨hvs, hvleft⟩
    let i : Fin (16 * k) := ⟨v.val, hvleft⟩
    refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
    · exact mem_chainPart.mpr (by simpa [i] using hvs)
    · exact Fin.ext (by simp [i])

lemma remainder_image_eq_filter {k r : Nat} (S : CanonicalSplitRealization k r)
    (s : Finset (Fin (16 * k + r))) :
    (remainderPart S s).image (Fin.natAdd (16 * k)) =
      s.filter fun v : Fin (16 * k + r) => ¬ v.val < 16 * k := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
    exact Finset.mem_filter.mpr ⟨mem_remainderPart.mp hj, by simp [Fin.val_natAdd]⟩
  · intro hv
    rcases Finset.mem_filter.mp hv with ⟨hvs, hvright⟩
    have hle : 16 * k <= v.val := Nat.le_of_not_lt hvright
    have hlt : v.val - 16 * k < r := by
      omega
    let j : Fin r := ⟨v.val - 16 * k, hlt⟩
    refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
    · exact mem_remainderPart.mpr (by
        have hval : (Fin.natAdd (16 * k) j).val = v.val := by
          simp [j]
          omega
        have heq : Fin.natAdd (16 * k) j = v := Fin.ext hval
        simpa [heq] using hvs)
    · exact Fin.ext (by
        simp [j]
        omega)

lemma card_filter_left_eq_chainPart {k r : Nat}
    (S : CanonicalSplitRealization k r) (s : Finset (Fin (16 * k + r))) :
    (s.filter fun v : Fin (16 * k + r) => v.val < 16 * k).card =
      (chainPart S s).card := by
  rw [← chain_image_eq_filter S s, Finset.card_image_of_injective]
  exact Fin.castAdd_injective (16 * k) r

lemma card_filter_right_eq_remainderPart {k r : Nat}
    (S : CanonicalSplitRealization k r) (s : Finset (Fin (16 * k + r))) :
    (s.filter fun v : Fin (16 * k + r) => ¬ v.val < 16 * k).card =
      (remainderPart S s).card := by
  rw [← remainder_image_eq_filter S s, Finset.card_image_of_injective]
  exact Fin.natAdd_injective r (16 * k)

lemma card_eq_chainPart_add_remainderPart {k r : Nat}
    (S : CanonicalSplitRealization k r) (s : Finset (Fin (16 * k + r))) :
    s.card = (chainPart S s).card + (remainderPart S s).card := by
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := s) (p := fun v : Fin (16 * k + r) => v.val < 16 * k)
  rw [card_filter_left_eq_chainPart S s,
    card_filter_right_eq_remainderPart S s] at hsplit
  exact hsplit.symm

lemma chainPart_isIndep {k r : Nat} (S : CanonicalSplitRealization k r)
    {s : Finset (Fin (16 * k + r))} (hs : S.config.IsIndep s) :
    S.chain.config.IsIndep (chainPart S s) := by
  intro i hi j hj hij hunit
  have hi' : Fin.castAdd r i ∈ s := mem_chainPart.mp hi
  have hj' : Fin.castAdd r j ∈ s := mem_chainPart.mp hj
  have hij' : Fin.castAdd r i ≠ Fin.castAdd r j := by
    intro h
    exact hij (Fin.castAdd_inj.mp h)
  have hunit' :
      eucDist (S.config.pts (Fin.castAdd r i))
        (S.config.pts (Fin.castAdd r j)) = 1 := by
    simpa [S.chain_points i, S.chain_points j] using hunit
  exact hs (Fin.castAdd r i) hi' (Fin.castAdd r j) hj' hij' hunit'

lemma remainderPart_isIndep {k r : Nat} (S : CanonicalSplitRealization k r)
    {s : Finset (Fin (16 * k + r))} (hs : S.config.IsIndep s) :
    S.remainder.config.IsIndep (remainderPart S s) := by
  intro i hi j hj hij hunit
  have hi' : Fin.natAdd (16 * k) i ∈ s := mem_remainderPart.mp hi
  have hj' : Fin.natAdd (16 * k) j ∈ s := mem_remainderPart.mp hj
  have hij' : Fin.natAdd (16 * k) i ≠ Fin.natAdd (16 * k) j := by
    intro h
    exact hij ((Fin.natAdd_inj (16 * k)).mp h)
  have hunit' :
      eucDist (S.config.pts (Fin.natAdd (16 * k) i))
        (S.config.pts (Fin.natAdd (16 * k) j)) = 1 := by
    simpa [S.remainder_points i, S.remainder_points j] using hunit
  exact hs (Fin.natAdd (16 * k) i) hi' (Fin.natAdd (16 * k) j) hj' hij' hunit'

lemma split_card_le_five_mul_add_ceil_third {k r : Nat}
    (S : CanonicalSplitRealization k r)
    {s : Finset (Fin (16 * k + r))} (hs : S.config.IsIndep s) :
    s.card <= 5 * k + ceilDiv r 3 := by
  calc
    s.card = (chainPart S s).card + (remainderPart S s).card :=
      card_eq_chainPart_add_remainderPart S s
    _ <= 5 * k + ceilDiv r 3 :=
      Nat.add_le_add
        (S.chain.independent_card_le_five_mul
          (chainPart S s) (chainPart_isIndep S hs))
        (S.remainder.independent_card_le_ceil_third
          (remainderPart S s) (remainderPart_isIndep S hs))

lemma splitArithmetic (k r : Nat) (hr : r < 16) :
    5 * k + ceilDiv r 3 <= ceilDiv (5 * (16 * k + r)) 16 := by
  unfold ceilDiv
  omega

/-- The sound split/count theorem for a canonical exact-chain plus remainder
realization. -/
theorem independent_card_le_five_sixteen {k r : Nat}
    (S : CanonicalSplitRealization k r) (hr : r < 16)
    (s : Finset (Fin (16 * k + r))) (hs : S.config.IsIndep s) :
    s.card <= ceilDiv (5 * (16 * k + r)) 16 := by
  exact le_trans (split_card_le_five_mul_add_ceil_third S hs)
    (splitArithmetic k r hr)

/-- Existence form of `independent_card_le_five_sixteen`. -/
theorem targetUpperConstructionFiveSixteenAt_of_canonicalSplitRealization
    {k r : Nat} (hr : r < 16) (S : CanonicalSplitRealization k r) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact ⟨S.config, independent_card_le_five_sixteen S hr⟩

end SplitSoundness
end PachToth
end ErdosProblems1066
