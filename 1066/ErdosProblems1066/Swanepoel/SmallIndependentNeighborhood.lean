import ErdosProblems1066.Swanepoel.MinimalCounterexample

set_option autoImplicit false

/-!
# Canonical finite closed neighborhoods

This module provides the finite-set closed-neighborhood definitions needed for
local deletion arguments.  The construction is purely by filtering
`Finset.univ`; it does not assert any paper-specific reducible configuration.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SmallIndependentNeighborhood

open MinimalCounterexample

noncomputable section

/-- The closed unit-neighborhood of a finite vertex set: the set itself plus
all vertices at unit distance from a vertex of the set. -/
def closedNeighborhoodOf {n : Nat} (C : _root_.UDConfig n)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun v =>
    v ∈ S ∨ Exists fun u : Fin n =>
      u ∈ S ∧ eucDist (C.pts u) (C.pts v) = 1

/-- The open outside part of a finite closed neighborhood. -/
def outsideNeighborhoodOf {n : Nat} (C : _root_.UDConfig n)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  closedNeighborhoodOf C S \ S

@[simp]
lemma mem_closedNeighborhoodOf {n : Nat} (C : _root_.UDConfig n)
    (S : Finset (Fin n)) (v : Fin n) :
    v ∈ closedNeighborhoodOf C S ↔
      v ∈ S ∨ Exists fun u : Fin n =>
        u ∈ S ∧ eucDist (C.pts u) (C.pts v) = 1 := by
  classical
  simp [closedNeighborhoodOf]

/-- The canonical filtered closed neighborhood satisfies the explicit
`IsClosedNeighborhood` predicate. -/
theorem isClosedNeighborhood_closedNeighborhoodOf {n : Nat}
    (C : _root_.UDConfig n) (S : Finset (Fin n)) :
    IsClosedNeighborhood C S (closedNeighborhoodOf C S) := by
  intro v
  exact mem_closedNeighborhoodOf C S v

/-- The center set is contained in its canonical closed neighborhood. -/
lemma subset_closedNeighborhoodOf {n : Nat} (C : _root_.UDConfig n)
    (S : Finset (Fin n)) :
    S <= closedNeighborhoodOf C S := by
  intro v hv
  exact (mem_closedNeighborhoodOf C S v).2 (Or.inl hv)

@[simp]
lemma mem_outsideNeighborhoodOf {n : Nat} (C : _root_.UDConfig n)
    (S : Finset (Fin n)) (v : Fin n) :
    v ∈ outsideNeighborhoodOf C S ↔
      v ∉ S ∧ Exists fun u : Fin n =>
        u ∈ S ∧ eucDist (C.pts u) (C.pts v) = 1 := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_sdiff.mp hv with ⟨hclosed, hnotS⟩
    rcases (mem_closedNeighborhoodOf C S v).1 hclosed with hS | hunit
    · exact False.elim (hnotS hS)
    · exact ⟨hnotS, hunit⟩
  · rintro ⟨hnotS, hunit⟩
    exact Finset.mem_sdiff.mpr
      ⟨(mem_closedNeighborhoodOf C S v).2 (Or.inr hunit), hnotS⟩

/-- The outside part is disjoint from the center set. -/
lemma disjoint_outsideNeighborhoodOf {n : Nat} (C : _root_.UDConfig n)
    (S : Finset (Fin n)) :
    Disjoint (outsideNeighborhoodOf C S) S := by
  rw [Finset.disjoint_left]
  intro v hv hS
  exact ((mem_outsideNeighborhoodOf C S v).1 hv).1 hS

/-- A canonical closed neighborhood splits into its center set and outside
neighbors. -/
theorem closedNeighborhoodOf_eq_union {n : Nat} (C : _root_.UDConfig n)
    (S : Finset (Fin n)) :
    closedNeighborhoodOf C S = S ∪ outsideNeighborhoodOf C S := by
  classical
  ext v
  constructor
  · intro hv
    by_cases hS : v ∈ S
    · exact Finset.mem_union.mpr (Or.inl hS)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hv, hS⟩))
  · intro hv
    rcases Finset.mem_union.mp hv with hS | hout
    · exact subset_closedNeighborhoodOf C S hS
    · exact (Finset.mem_sdiff.mp hout).1

/-- The outside part is contained in the canonical closed neighborhood. -/
lemma outsideNeighborhoodOf_subset_closedNeighborhoodOf {n : Nat}
    (C : _root_.UDConfig n) (S : Finset (Fin n)) :
    outsideNeighborhoodOf C S <= closedNeighborhoodOf C S := by
  intro v hv
  exact (Finset.mem_sdiff.mp hv).1

/-- Nonempty center sets have nonempty canonical closed neighborhoods. -/
lemma closedNeighborhoodOf_nonempty_of_nonempty {n : Nat}
    (C : _root_.UDConfig n) {S : Finset (Fin n)}
    (hS : S.Nonempty) :
    (closedNeighborhoodOf C S).Nonempty :=
  hS.mono (subset_closedNeighborhoodOf C S)

/-- Cardinality split for the canonical closed neighborhood. -/
theorem closedNeighborhoodOf_card_eq_add_outsideNeighborhoodOf_card {n : Nat}
    (C : _root_.UDConfig n) (S : Finset (Fin n)) :
    (closedNeighborhoodOf C S).card =
      S.card + (outsideNeighborhoodOf C S).card := by
  rw [closedNeighborhoodOf_eq_union C S]
  exact Finset.card_union_of_disjoint
    (Disjoint.symm (disjoint_outsideNeighborhoodOf C S))

/-- Integer form of the canonical closed-neighborhood cardinality split. -/
lemma closedNeighborhoodOf_card_int_eq_add_outsideNeighborhoodOf_card {n : Nat}
    (C : _root_.UDConfig n) (S : Finset (Fin n)) :
    ((closedNeighborhoodOf C S).card : Int) =
      (S.card : Int) + ((outsideNeighborhoodOf C S).card : Int) := by
  exact_mod_cast
    (closedNeighborhoodOf_card_eq_add_outsideNeighborhoodOf_card C S)

/-- An integer upper bound on the outside part gives the direct deletion
cardinality inequality for the canonical closed neighborhood. -/
lemma closedNeighborhoodOf_card_le_four_mul_sub_one_of_outside_card_le_int
    {n : Nat} (C : _root_.UDConfig n) (S : Finset (Fin n))
    (houtside :
      ((outsideNeighborhoodOf C S).card : Int) <=
        3 * (S.card : Int) - 1) :
    ((closedNeighborhoodOf C S).card : Int) <=
      4 * (S.card : Int) - 1 := by
  have hcard :=
    closedNeighborhoodOf_card_int_eq_add_outsideNeighborhoodOf_card C S
  nlinarith

/-- Natural-number version of the outside-cardinality criterion.  The
hypothesis `outside.card + 1 <= 3 * S.card` is the subtraction-free form of
`outside.card <= 3 * S.card - 1`. -/
lemma closedNeighborhoodOf_card_le_four_mul_sub_one_of_outside_card_add_one_le
    {n : Nat} (C : _root_.UDConfig n) (S : Finset (Fin n))
    (houtside :
      (outsideNeighborhoodOf C S).card + 1 <= 3 * S.card) :
    ((closedNeighborhoodOf C S).card : Int) <=
      4 * (S.card : Int) - 1 := by
  have houtsideInt :
      ((outsideNeighborhoodOf C S).card : Int) + 1 <=
        3 * (S.card : Int) := by
    exact_mod_cast houtside
  exact
    closedNeighborhoodOf_card_le_four_mul_sub_one_of_outside_card_le_int
      C S (by nlinarith)

end

end SmallIndependentNeighborhood
end Swanepoel
end ErdosProblems1066
