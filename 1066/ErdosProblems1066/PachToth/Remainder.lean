import ErdosProblems1066.PachToth.Arithmetic
import ErdosProblems1066.UnitDistanceBounds

set_option autoImplicit false

/-!
# Pach--Toth remainder split arithmetic

This module is deliberately conditional.  It does not construct a
Pach--Toth configuration for arbitrary `n`; it only records the arithmetic
bridge from an explicit chain/remainder split of independent sets to the
claimed ceiling bound.
-/

namespace ErdosProblems1066
namespace PachToth
namespace Remainder

open Arithmetic

/-- The unit-distance configuration determined by explicit points and their
separation proof. -/
def explicitConfig {n : Nat}
    (pts : Fin n -> Real × Real)
    (sep : forall i j : Fin n, i ≠ j -> 1 <= eucDist (pts i) (pts j)) :
    _root_.UDConfig n where
  pts := pts
  sep := sep

/--
Conditional Pach--Toth remainder/split upper arithmetic.

All construction data are hypotheses:

* `pts` and `sep` are the geometric configuration on `n` vertices;
* `chainPart` and `remainderPart` split every independent set;
* the split is set-theoretically visible through subset, cover, and
  disjointness hypotheses;
* `exact_card_split` says the two parts account for the independent set
  exactly;
* the chain and remainder cardinals satisfy the advertised bounds.

Under those hypotheses, every independent set has size at most
`ceilDiv (5 * n) 16`.
-/
theorem independent_card_le_of_split
    {n : Nat}
    (pts : Fin n -> Real × Real)
    (sep : forall i j : Fin n, i ≠ j -> 1 <= eucDist (pts i) (pts j))
    (chainPart remainderPart : Finset (Fin n) -> Finset (Fin n))
    (chain_subset :
      forall s : Finset (Fin n),
        (explicitConfig pts sep).IsIndep s -> chainPart s ⊆ s)
    (remainder_subset :
      forall s : Finset (Fin n),
        (explicitConfig pts sep).IsIndep s -> remainderPart s ⊆ s)
    (split_cover :
      forall s : Finset (Fin n),
        (explicitConfig pts sep).IsIndep s ->
          s ⊆ chainPart s ∪ remainderPart s)
    (chain_remainder_disjoint :
      forall s : Finset (Fin n),
        (explicitConfig pts sep).IsIndep s ->
          forall v : Fin n, v ∈ chainPart s -> v ∈ remainderPart s -> False)
    (exact_card_split :
      forall s : Finset (Fin n),
        (explicitConfig pts sep).IsIndep s ->
          s.card = (chainPart s).card + (remainderPart s).card)
    (chain_card_le :
      forall s : Finset (Fin n),
        (explicitConfig pts sep).IsIndep s ->
          (chainPart s).card <= 5 * (n / 16))
    (remainder_card_le :
      forall s : Finset (Fin n),
        (explicitConfig pts sep).IsIndep s ->
          (remainderPart s).card <= ceilDiv (n % 16) 3)
    (s : Finset (Fin n))
    (hs : (explicitConfig pts sep).IsIndep s) :
    s.card <= ceilDiv (5 * n) 16 := by
  have _ : chainPart s ⊆ s := chain_subset s hs
  have _ : remainderPart s ⊆ s := remainder_subset s hs
  have _ : s ⊆ chainPart s ∪ remainderPart s := split_cover s hs
  have _ : forall v : Fin n, v ∈ chainPart s -> v ∈ remainderPart s -> False :=
    chain_remainder_disjoint s hs
  have hchain := chain_card_le s hs
  have hremainder := remainder_card_le s hs
  calc
    s.card = (chainPart s).card + (remainderPart s).card :=
      exact_card_split s hs
    _ <= 5 * (n / 16) + ceilDiv (n % 16) 3 :=
      Nat.add_le_add hchain hremainder
    _ <= ceilDiv (5 * n) 16 :=
      RemainderArithmetic n

end Remainder
end PachToth
end ErdosProblems1066
