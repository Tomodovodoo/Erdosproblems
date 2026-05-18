import ErdosProblems1066.Swanepoel.Arithmetic
import ErdosProblems1066.UnitDistanceBounds

/-!
# Swanepoel minimal-counterexample deletion arithmetic

This module isolates the checked part of the minimal-counterexample deletion
step used in Swanepoel's `8 / 31` argument.  The statements are conditional:
the geometric facts saying that a particular set is a closed neighborhood, that
the smaller configuration is represented by the kept vertices, and that the
closed neighborhood is small enough are all explicit hypotheses.

No Euclidean `8 / 31` theorem is stated here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalCounterexample

/-! ## Cleared `8 / 31` deletion arithmetic -/

/-- The cleared `8 / 31` lower-bound predicate for a set of size `a` in an
`n`-vertex configuration. -/
def ClearedEightThirtyOneBound (n a : Nat) : Prop :=
  31 * a >= 8 * n

/-- Integer form of the `m = 8` deletion arithmetic, using the existing generic
Swanepoel deletion lemma.  Here `r` is the size of the independent set that is
reinserted after deleting its closed neighborhood. -/
lemma m8_deletion_arithmetic_int
    {n nSmall t r : Int}
    (hr : r <= 8)
    (hnSmall : n - 4 * r + 1 <= nSmall)
    (hsmall : 31 * t >= 8 * nSmall) :
    31 * (t + r) >= 8 * n := by
  have hsmallExact :
      (4 * (8 : Int) - 1) * t >= (8 : Int) * (n - 4 * r + 1) := by
    norm_num
    nlinarith
  have h :=
    Arithmetic.deletion_cleared_denominator_int
      (m := (8 : Int)) (k := r) (n := n) (t := t) hr hsmallExact
  norm_num at h
  exact h

/-- If the deleted set has cardinality at most `4 * r - 1`, then the smaller
configuration has at least the vertex count required by the deletion
arithmetic. -/
lemma remaining_count_threshold_of_deleted_card_bound
    {n nSmall deletedCard r : Nat}
    (hcount : n = nSmall + deletedCard)
    (hdeleted : (deletedCard : Int) <= 4 * (r : Int) - 1) :
    (n : Int) - 4 * (r : Int) + 1 <= (nSmall : Int) := by
  have hcountInt : (n : Int) = (nSmall : Int) + (deletedCard : Int) := by
    exact_mod_cast hcount
  nlinarith

/-- Natural-number specialization of the cleared `8 / 31` deletion arithmetic.
If the smaller configuration satisfies the cleared bound, the deleted closed
neighborhood has size at most `4r - 1`, and the independent reinsertion has
size `r <= 8`, then the original cleared bound follows for the combined
independent set size. -/
lemma m8_cleared_bound_after_deletion
    {n nSmall deletedCard smallSize r : Nat}
    (hr : r <= 8)
    (hcount : n = nSmall + deletedCard)
    (hdeleted : (deletedCard : Int) <= 4 * (r : Int) - 1)
    (hsmall : ClearedEightThirtyOneBound nSmall smallSize) :
    ClearedEightThirtyOneBound n (smallSize + r) := by
  have hnSmall :
      (n : Int) - 4 * (r : Int) + 1 <= (nSmall : Int) :=
    remaining_count_threshold_of_deleted_card_bound hcount hdeleted
  have hsmallInt : (31 : Int) * (smallSize : Int) >= 8 * (nSmall : Int) := by
    exact_mod_cast hsmall
  have harith :=
    m8_deletion_arithmetic_int
      (n := (n : Int)) (nSmall := (nSmall : Int))
      (t := (smallSize : Int)) (r := (r : Int))
      (by exact_mod_cast hr) hnSmall hsmallInt
  exact_mod_cast harith

/-! ## Explicit deletion and reinsertion hypotheses -/

/-- The closed unit-neighborhood of `center`, represented by a finite set
`deleted`.  This is a hypothesis, not a theorem about any particular local
configuration. -/
def IsClosedNeighborhood {n : Nat} (C : _root_.UDConfig n)
    (center deleted : Finset (Fin n)) : Prop :=
  forall v : Fin n,
    v ∈ deleted <->
      v ∈ center \/ Exists fun u : Fin n =>
        u ∈ center /\ eucDist (C.pts u) (C.pts v) = 1

/-- The kept copy of the smaller configuration preserves the distances needed
on the smaller independent set. -/
def PreservesDistancesOn {n nSmall : Nat}
    (Csmall : _root_.UDConfig nSmall) (C : _root_.UDConfig n)
    (kept : Fin nSmall -> Fin n) (small : Finset (Fin nSmall)) : Prop :=
  forall i : Fin nSmall, i ∈ small ->
    forall j : Fin nSmall, j ∈ small ->
      eucDist (C.pts (kept i)) (C.pts (kept j)) =
        eucDist (Csmall.pts i) (Csmall.pts j)

/-- A closed-neighborhood hypothesis makes the reinserted vertices nonadjacent
to every kept vertex outside the deleted set. -/
lemma cross_nonunit_of_closedNeighborhood_disjoint
    {n : Nat} {C : _root_.UDConfig n}
    {deleted reinsertion keptSet : Finset (Fin n)}
    (hclosed : IsClosedNeighborhood C reinsertion deleted)
    (hdisjoint : Disjoint keptSet deleted) :
    forall x : Fin n, x ∈ reinsertion ->
      forall y : Fin n, y ∈ keptSet -> x ≠ y ->
        eucDist (C.pts x) (C.pts y) ≠ 1 := by
  intro x hx y hy _ hunit
  have hyDeleted : y ∈ deleted :=
    (hclosed y).2 (Or.inr (Exists.intro x (And.intro hx hunit)))
  exact (Finset.disjoint_left.mp hdisjoint) hy hyDeleted

/-- Independence transfers from the smaller configuration to its kept image
when the relevant pairwise distances are preserved. -/
lemma image_indep_of_preservesDistancesOn
    {n nSmall : Nat} {Csmall : _root_.UDConfig nSmall} {C : _root_.UDConfig n}
    {kept : Fin nSmall -> Fin n} {small : Finset (Fin nSmall)}
    (hsmall : Csmall.IsIndep small)
    (hpreserve : PreservesDistancesOn Csmall C kept small) :
    C.IsIndep (small.image kept) := by
  intro x hx y hy hxy hunit
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
  by_cases hij : i = j
  · subst j
    exact hxy rfl
  · exact hsmall i hi j hj hij ((hpreserve i hi j hj).symm.trans hunit)

/-- Two independent sets with no cross unit-distance edges have independent
union. -/
lemma union_indep_of_cross_nonunit
    {n : Nat} {C : _root_.UDConfig n}
    {left right : Finset (Fin n)}
    (hleft : C.IsIndep left)
    (hright : C.IsIndep right)
    (hcross :
      forall x : Fin n, x ∈ left ->
        forall y : Fin n, y ∈ right -> x ≠ y ->
          eucDist (C.pts x) (C.pts y) ≠ 1) :
    C.IsIndep (left ∪ right) := by
  intro x hx y hy hxy hunit
  simp only [Finset.mem_union] at hx hy
  rcases hx with hxLeft | hxRight
  · rcases hy with hyLeft | hyRight
    · exact hleft x hxLeft y hyLeft hxy hunit
    · exact hcross x hxLeft y hyRight hxy hunit
  · rcases hy with hyLeft | hyRight
    · exact hcross y hyLeft x hxRight hxy.symm (by
        simpa [eucDist_comm] using hunit)
    · exact hright x hxRight y hyRight hxy hunit

/-- If the kept vertices and the deleted closed neighborhood partition the
original vertex set, then the original vertex count is the smaller count plus
the deleted count. -/
lemma original_card_eq_small_add_deleted_of_partition
    {n nSmall : Nat} (kept : Fin nSmall -> Fin n)
    (hkeptInjective : Function.Injective kept)
    (deleted : Finset (Fin n))
    (hdisjoint : Disjoint ((Finset.univ.image kept) : Finset (Fin n)) deleted)
    (hcover : ((Finset.univ.image kept) : Finset (Fin n)) ∪ deleted =
      Finset.univ) :
    n = nSmall + deleted.card := by
  have hcard :=
    Finset.card_union_of_disjoint hdisjoint
  rw [hcover] at hcard
  simpa [Finset.card_image_of_injective _ hkeptInjective] using hcard

/-- Conditional Swanepoel deletion step for a concrete smaller configuration.
The theorem assumes:

* the kept smaller vertices and the deleted closed neighborhood partition the
  original vertices;
* the deleted set is the closed unit-neighborhood of the reinserted independent
  set;
* the deleted closed neighborhood has size at most `4r - 1`, where `r` is the
  reinsertion size, and `r <= 8`;
* the smaller configuration has an independent set satisfying the cleared
  `8 / 31` bound;
* the kept copy preserves all distances needed on that smaller independent set.

It concludes only the corresponding cleared bound for the original
configuration. -/
theorem exists_independent_with_cleared_bound_of_closedNeighborhood_deletion
    {n nSmall : Nat} (C : _root_.UDConfig n) (Csmall : _root_.UDConfig nSmall)
    (kept : Fin nSmall -> Fin n)
    (deleted reinsertion : Finset (Fin n))
    (small : Finset (Fin nSmall))
    (hkeptInjective : Function.Injective kept)
    (hkeptDeletedDisjoint :
      Disjoint ((Finset.univ.image kept) : Finset (Fin n)) deleted)
    (hcover : ((Finset.univ.image kept) : Finset (Fin n)) ∪ deleted =
      Finset.univ)
    (hclosed : IsClosedNeighborhood C reinsertion deleted)
    (hdeletedCard :
      (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1)
    (hreinsertionCard : reinsertion.card <= 8)
    (hreinsertionIndep : C.IsIndep reinsertion)
    (hsmallIndep : Csmall.IsIndep small)
    (hsmallBound : ClearedEightThirtyOneBound nSmall small.card)
    (hpreserve : PreservesDistancesOn Csmall C kept small) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ ClearedEightThirtyOneBound n s.card := by
  let keptSmall : Finset (Fin n) := small.image kept
  have hkeptSmall_subset : keptSmall <=
      ((Finset.univ.image kept) : Finset (Fin n)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    exact Finset.mem_image_of_mem kept (Finset.mem_univ i)
  have hkeptSmall_deleted_disjoint : Disjoint keptSmall deleted := by
    rw [Finset.disjoint_left]
    intro x hxSmall hxDeleted
    exact (Finset.disjoint_left.mp hkeptDeletedDisjoint)
      (hkeptSmall_subset hxSmall) hxDeleted
  have hcross :
      forall x : Fin n, x ∈ reinsertion ->
        forall y : Fin n, y ∈ keptSmall -> x ≠ y ->
          eucDist (C.pts x) (C.pts y) ≠ 1 :=
    cross_nonunit_of_closedNeighborhood_disjoint hclosed
      hkeptSmall_deleted_disjoint
  have hkeptSmallIndep : C.IsIndep keptSmall := by
    exact image_indep_of_preservesDistancesOn hsmallIndep hpreserve
  let combined : Finset (Fin n) := reinsertion ∪ keptSmall
  have hcombinedIndep : C.IsIndep combined := by
    exact union_indep_of_cross_nonunit hreinsertionIndep hkeptSmallIndep hcross
  have hreinsertion_keptSmall_disjoint : Disjoint reinsertion keptSmall := by
    rw [Finset.disjoint_left]
    intro x hxReinsert hxSmall
    have hxDeleted : x ∈ deleted := (hclosed x).2 (Or.inl hxReinsert)
    exact (Finset.disjoint_left.mp hkeptSmall_deleted_disjoint)
      hxSmall hxDeleted
  have hcombinedCard :
      combined.card = reinsertion.card + small.card := by
    have hcard :=
      Finset.card_union_of_disjoint hreinsertion_keptSmall_disjoint
    simp [keptSmall, Finset.card_image_of_injective _ hkeptInjective]
      at hcard
    simpa [Nat.add_comm] using hcard
  have hcount : n = nSmall + deleted.card :=
    original_card_eq_small_add_deleted_of_partition kept hkeptInjective
      deleted hkeptDeletedDisjoint hcover
  have harith :
      ClearedEightThirtyOneBound n (small.card + reinsertion.card) :=
    m8_cleared_bound_after_deletion
      (n := n) (nSmall := nSmall) (deletedCard := deleted.card)
      (smallSize := small.card) (r := reinsertion.card)
      hreinsertionCard hcount hdeletedCard hsmallBound
  refine Exists.intro combined ?_
  constructor
  · exact hcombinedIndep
  · simpa [ClearedEightThirtyOneBound, hcombinedCard, Nat.add_comm] using harith

end MinimalCounterexample
end Swanepoel
end ErdosProblems1066
