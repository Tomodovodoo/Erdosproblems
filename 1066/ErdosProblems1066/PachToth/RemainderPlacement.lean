import ErdosProblems1066.PachToth.AffineLocalGeometry
import ErdosProblems1066.PachToth.SplitCertificateBridge

set_option autoImplicit false

/-!
# Far-apart placement for Pach--Toth remainders

This module removes the explicit "far apart" hypothesis from the arbitrary
`n` split route.  Given any finite chain configuration and any finite
remainder configuration, it translates the remainder far enough in the
positive `x` direction that every chain/remainder cross distance is strictly
larger than one, while preserving all internal unit-distance data of the
remainder.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RemainderPlacement

open Arithmetic

noncomputable section

/-- A crude finite coordinate budget for the horizontal coordinates of a
configuration.  A sum of absolute values is intentionally used instead of a
maximum so that the endpoint bounds are elementary. -/
def xBudget {n : Nat} (C : _root_.UDConfig n) : Real :=
  ∑ i : Fin n, |(C.pts i).1|

lemma xCoord_le_xBudget {n : Nat} (C : _root_.UDConfig n) (i : Fin n) :
    (C.pts i).1 <= xBudget C := by
  calc
    (C.pts i).1 <= |(C.pts i).1| := le_abs_self _
    _ <= xBudget C := by
      unfold xBudget
      exact Finset.single_le_sum
        (fun x _ => abs_nonneg ((C.pts x).1)) (Finset.mem_univ i)

lemma neg_xCoord_le_xBudget {n : Nat} (C : _root_.UDConfig n) (i : Fin n) :
    -(C.pts i).1 <= xBudget C := by
  calc
    -(C.pts i).1 <= |(C.pts i).1| := neg_le_abs _
    _ <= xBudget C := by
      unfold xBudget
      exact Finset.single_le_sum
        (fun x _ => abs_nonneg ((C.pts x).1)) (Finset.mem_univ i)

/-- If the second point is at least one unit to the right, then the Euclidean
distance is at least one. -/
lemma one_le_eucDist_of_one_le_fst_sub {p q : Real × Real}
    (h : 1 <= q.1 - p.1) :
    1 <= _root_.eucDist p q := by
  rw [_root_.eucDist_ge_one_iff]
  have hx : (p.1 - q.1) ^ 2 = (q.1 - p.1) ^ 2 := by ring
  have hxone : 1 <= (q.1 - p.1) ^ 2 := by
    nlinarith [sq_nonneg (q.1 - p.1 - 1)]
  nlinarith [sq_nonneg (p.2 - q.2)]

/-- If the second point is more than one unit to the right, then the two
points are not at unit distance. -/
lemma eucDist_ne_one_of_one_lt_fst_sub {p q : Real × Real}
    (h : 1 < q.1 - p.1) :
    _root_.eucDist p q ≠ 1 := by
  intro hdist
  rw [_root_.eucDist_eq_one_iff] at hdist
  have hx : (p.1 - q.1) ^ 2 = (q.1 - p.1) ^ 2 := by ring
  have hxone : 1 < (q.1 - p.1) ^ 2 := by
    nlinarith [sq_nonneg (q.1 - p.1 - 1)]
  nlinarith [sq_nonneg (p.2 - q.2)]

/-- The horizontal translation amount used to separate a chain from a
remainder. -/
def separatingOffset {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) : Real :=
  xBudget chain + xBudget remainder + 3

/-- The translated copy of a remainder configuration used in the split
construction. -/
def translatedRemainder {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) :
    _root_.UDConfig r :=
  AffineLocalGeometry.UDConfig.translate
    (separatingOffset chain remainder, 0) remainder

@[simp]
lemma translatedRemainder_pts {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (j : Fin r) :
    (translatedRemainder chain remainder).pts j =
      AffineLocalGeometry.translatePoint
        (separatingOffset chain remainder, 0) (remainder.pts j) := by
  rfl

lemma one_lt_translatedRemainder_fst_sub {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (i : Fin m) (j : Fin r) :
    1 < ((translatedRemainder chain remainder).pts j).1 -
      (chain.pts i).1 := by
  have hchain := xCoord_le_xBudget chain i
  have hrem := neg_xCoord_le_xBudget remainder j
  simp [translatedRemainder, AffineLocalGeometry.UDConfig.translate,
    AffineLocalGeometry.translatePoint, separatingOffset]
  nlinarith

lemma chain_translatedRemainder_separated {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (i : Fin m) (j : Fin r) :
    1 <= _root_.eucDist (chain.pts i)
      ((translatedRemainder chain remainder).pts j) := by
  exact one_le_eucDist_of_one_le_fst_sub
    (le_of_lt (one_lt_translatedRemainder_fst_sub chain remainder i j))

lemma chain_translatedRemainder_ne_unit {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (i : Fin m) (j : Fin r) :
    _root_.eucDist (chain.pts i)
      ((translatedRemainder chain remainder).pts j) ≠ 1 := by
  exact eucDist_ne_one_of_one_lt_fst_sub
    (one_lt_translatedRemainder_fst_sub chain remainder i j)

/-- The combined configuration formed by appending a chain and a translated
remainder. -/
def combinedConfig {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) :
    _root_.UDConfig (m + r) where
  pts := Fin.append chain.pts (translatedRemainder chain remainder).pts
  sep := by
    intro a b hab
    induction a using Fin.addCases with
    | left i =>
        induction b using Fin.addCases with
        | left j =>
            have hij : i ≠ j := by
              intro h
              apply hab
              simp [h]
            simpa using chain.sep i j hij
        | right j =>
            simpa using chain_translatedRemainder_separated chain remainder i j
    | right i =>
        induction b using Fin.addCases with
        | left j =>
            have hsep := chain_translatedRemainder_separated chain remainder j i
            simpa [_root_.eucDist_comm] using hsep
        | right j =>
            have hij : i ≠ j := by
              intro h
              apply hab
              simp [h]
            simpa using (translatedRemainder chain remainder).sep i j hij

@[simp]
lemma combinedConfig_chain_pts {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (i : Fin m) :
    (combinedConfig chain remainder).pts (Fin.castAdd r i) = chain.pts i := by
  simp [combinedConfig]

@[simp]
lemma combinedConfig_remainder_pts {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (j : Fin r) :
    (combinedConfig chain remainder).pts (Fin.natAdd m j) =
      (translatedRemainder chain remainder).pts j := by
  simp [combinedConfig]

/-- A universal far-apart certificate after translating the remainder. -/
def farApartRemainderCertificate {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) :
    SplitCertificateBridge.FarApartRemainderCertificate
      chain (translatedRemainder chain remainder) where
  config := combinedConfig chain remainder
  chain_points := by
    intro i
    simp [combinedConfig]
  remainder_points := by
    intro j
    simp [combinedConfig]
  cross_far := by
    intro i j
    simpa using chain_translatedRemainder_ne_unit chain remainder i j

/-- Translating a checked remainder certificate preserves its independent-set
upper bound. -/
def translatedRemainderUpper {m r : Nat}
    (chain : _root_.UDConfig m) (R : SplitSoundness.RemainderUpper r) :
    SplitSoundness.RemainderUpper r where
  config := translatedRemainder chain R.config
  independent_card_le_ceil_third := by
    intro s hs
    exact R.independent_card_le_ceil_third s
      ((AffineLocalGeometry.UDConfig.isIndep_translate
        (separatingOffset chain R.config, 0) R.config s).mp hs)

/-- Exact-chain data and a checked remainder can always be placed in a
canonical split realization by translating the remainder far away. -/
def canonicalSplitRealizationOfExactChainTranslatedRemainder {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r) :
    SplitSoundness.CanonicalSplitRealization k r :=
  SplitCertificateBridge.canonicalSplitRealizationOfExactChainFarApart
    chain
    (translatedRemainderUpper chain.config remainder)
    (farApartRemainderCertificate chain.config remainder.config)

/-- The arbitrary-`n` split target at `16 * k + r` follows from exact-chain
data and the checked finite remainder construction; the spatial separation is
constructed here. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
    {k r : Nat} (hr : r < 16)
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitSoundness.targetUpperConstructionFiveSixteenAt_of_canonicalSplitRealization
      hr
      (canonicalSplitRealizationOfExactChainTranslatedRemainder chain remainder)

end

end RemainderPlacement
end PachToth
end ErdosProblems1066
