import ErdosProblems1066.PachToth.Remainder

set_option autoImplicit false

/-!
# Pach--Toth arbitrary-`n` target reduction

This module names the full arbitrary-vertex-count upper-construction target
and proves only a conditional reduction from explicit split constructions.
It does not construct those split configurations.
-/

namespace ErdosProblems1066
namespace PachToth

open Arithmetic

/-- The Pach--Toth `5 / 16` upper-construction target at a fixed vertex count. -/
def targetUpperConstructionFiveSixteenAt (n : Nat) : Prop :=
  Exists fun C : _root_.UDConfig n =>
    forall s : Finset (Fin n), C.IsIndep s -> s.card <= ceilDiv (5 * n) 16

/-- The full arbitrary-`n` proposition-valued Pach--Toth upper target. -/
def targetUpperConstructionFiveSixteenArbitrary : Prop :=
  forall n : Nat, targetUpperConstructionFiveSixteenAt n

/-- Source-faithful eventual form: from some vertex threshold onward, the
`5 / 16` construction is available at every vertex count. -/
def targetUpperConstructionFiveSixteenEventually : Prop :=
  Exists fun N0 : Nat =>
    forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n

/-- The finite small-case complement needed to upgrade an eventual construction
to the stronger all-`n` target. -/
def targetUpperConstructionFiveSixteenSmallUpTo (N0 : Nat) : Prop :=
  forall n : Nat, n < N0 -> targetUpperConstructionFiveSixteenAt n

/-- Eventual constructions plus finitely many small cases imply the stronger
arbitrary-`n` target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
    (N0 : Nat)
    (Hlarge :
      forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n)
    (Hsmall : targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  by_cases hlarge : N0 <= n
  · exact Hlarge n hlarge
  · exact Hsmall n (Nat.lt_of_not_ge hlarge)

/--
An explicit split construction for the arbitrary-`n` Pach--Toth target.

The fields are exactly the data consumed by
`Remainder.independent_card_le_of_split`: a genuine separated point set,
two parts assigned to each independent set, exact cardinal accounting, and
the chain/remainder cardinal bounds.  Supplying this structure for every `n`
is still the unproved construction work.
-/
structure ExplicitSplitConstruction (n : Nat) where
  pts : Fin n -> Prod Real Real
  sep :
    forall i j : Fin n, i ≠ j -> 1 <= eucDist (pts i) (pts j)
  chainPart : Finset (Fin n) -> Finset (Fin n)
  remainderPart : Finset (Fin n) -> Finset (Fin n)
  chain_subset :
    forall s : Finset (Fin n),
      (Remainder.explicitConfig pts sep).IsIndep s -> chainPart s ⊆ s
  remainder_subset :
    forall s : Finset (Fin n),
      (Remainder.explicitConfig pts sep).IsIndep s -> remainderPart s ⊆ s
  split_cover :
    forall s : Finset (Fin n),
      (Remainder.explicitConfig pts sep).IsIndep s ->
        s ⊆ chainPart s ∪ remainderPart s
  chain_remainder_disjoint :
    forall s : Finset (Fin n),
      (Remainder.explicitConfig pts sep).IsIndep s ->
        forall v : Fin n, v ∈ chainPart s -> v ∈ remainderPart s -> False
  exact_card_split :
    forall s : Finset (Fin n),
      (Remainder.explicitConfig pts sep).IsIndep s ->
        s.card = (chainPart s).card + (remainderPart s).card
  chain_card_le :
    forall s : Finset (Fin n),
      (Remainder.explicitConfig pts sep).IsIndep s ->
        (chainPart s).card <= 5 * (n / 16)
  remainder_card_le :
    forall s : Finset (Fin n),
      (Remainder.explicitConfig pts sep).IsIndep s ->
        (remainderPart s).card <= ceilDiv (n % 16) 3

/--
A single explicit split construction yields the arbitrary-`n` target at its
own vertex count.
-/
theorem targetUpperConstructionFiveSixteenAt_of_explicitSplitConstruction
    {n : Nat} (S : ExplicitSplitConstruction n) :
    targetUpperConstructionFiveSixteenAt n := by
  refine Exists.intro (Remainder.explicitConfig S.pts S.sep) ?_
  intro s hs
  exact Remainder.independent_card_le_of_split
    S.pts
    S.sep
    S.chainPart
    S.remainderPart
    S.chain_subset
    S.remainder_subset
    S.split_cover
    S.chain_remainder_disjoint
    S.exact_card_split
    S.chain_card_le
    S.remainder_card_le
    s
    hs

/--
Conditional arbitrary-`n` target reduction: if explicit split constructions
are available for all vertex counts, then the proposition-valued arbitrary
Pach--Toth target follows.
-/
theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitSplitConstructions
    (H : forall n : Nat, ExplicitSplitConstruction n) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  exact targetUpperConstructionFiveSixteenAt_of_explicitSplitConstruction (H n)

end PachToth
end ErdosProblems1066
