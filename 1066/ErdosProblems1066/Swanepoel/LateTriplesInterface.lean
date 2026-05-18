import ErdosProblems1066.Swanepoel.Lemma10Bridge

/-!
# Swanepoel late-triples interface

This module isolates the remaining Lemma 9 input needed by the `m = 8`
Lemma 10 bridge.  It does not prove the paper combinatorics.  Instead it gives
small, finite-index packages that turn explicit early-triple exclusions or
caller-supplied finite predicates into the existing `P.LateTriples` hypothesis.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LateTriplesInterface

open Lemma10Bridge
open LocalConfigurations

universe u

variable {V : Type u} {G : LocalGraph V}

/-! ## The `m = 8` triple-start split -/

/-- A triple start is late enough for the `m = 8` Lemma 9 bound. -/
def M8TripleStartLate (a : M8TripleStartIndex) : Prop :=
  6 <= a.1

/-- The complementary early range for `m = 8` triple starts. -/
def M8TripleStartEarly (a : M8TripleStartIndex) : Prop :=
  a.1 <= 5

/-- The range proof carried by an `m = 8` triple-start index. -/
theorem m8TripleStartIndex_bounds (a : M8TripleStartIndex) :
    1 <= a.1 /\ a.1 + 2 <= 10 :=
  a.2

/-- Every `m = 8` triple-start index is at most `8`. -/
theorem m8TripleStartIndex_le_eight (a : M8TripleStartIndex) :
    a.1 <= 8 := by
  have ha := m8TripleStartIndex_bounds a
  omega

/-- Every `m = 8` triple-start index is either late or early. -/
theorem m8TripleStart_late_or_early (a : M8TripleStartIndex) :
    M8TripleStartLate a \/ M8TripleStartEarly a := by
  unfold M8TripleStartLate M8TripleStartEarly
  omega

/-- A triple start is late once the early alternative is ruled out. -/
theorem m8TripleStartLate_of_not_early {a : M8TripleStartIndex}
    (hnot : Not (M8TripleStartEarly a)) :
    M8TripleStartLate a := by
  unfold M8TripleStartLate M8TripleStartEarly at *
  omega

/-- A triple start is early once the late alternative is ruled out. -/
theorem m8TripleStartEarly_of_not_late {a : M8TripleStartIndex}
    (hnot : Not (M8TripleStartLate a)) :
    M8TripleStartEarly a := by
  unfold M8TripleStartLate M8TripleStartEarly at *
  omega

/-- The late and early alternatives are exact complements in the finite range. -/
theorem m8TripleStartLate_iff_not_early (a : M8TripleStartIndex) :
    M8TripleStartLate a <-> Not (M8TripleStartEarly a) := by
  constructor
  case mp =>
    intro hlate hearly
    unfold M8TripleStartLate M8TripleStartEarly at *
    omega
  case mpr =>
    exact m8TripleStartLate_of_not_early

/-! ## Direct early-triple exclusions -/

/-- A direct finite-index Lemma 9 input: no named triple equality may start in
the early range `1, ..., 5`. -/
def M8NoEarlyTripleEquality (P : BrokenLatticePredicates G 8) : Prop :=
  forall a : M8TripleStartIndex,
    M8TripleStartEarly a -> Not (P.tripleEquality a)

/-- Excluding all early triple equalities gives the raw late-triples predicate. -/
theorem m8BrokenLatticeLateTriples_of_noEarlyTripleEquality
    (P : BrokenLatticePredicates G 8)
    (hno : M8NoEarlyTripleEquality P) :
    M8BrokenLatticeLateTriples P := by
  intro a htriple
  exact m8TripleStartLate_of_not_early (a := a) (by
    intro hearly
    exact hno a hearly htriple)

/-! ## Predicate packages for the missing paper combinatorics -/

/-- A finite-index predicate package for the Lemma 9 step.

The field `tripleStartPredicate` is the caller's explicit combinatorial
predicate.  The package only asks for two facts: every named triple equality
implies that predicate at the corresponding natural index, and that predicate
is late in the finite range `1, ..., 8`. -/
structure M8NatLateTripleInputs (P : BrokenLatticePredicates G 8) where
  tripleStartPredicate : Nat -> Prop
  predicate_of_tripleEquality :
    forall a : M8TripleStartIndex,
      P.tripleEquality a -> tripleStartPredicate a.1
  late_of_predicate :
    forall a : Nat,
      1 <= a -> a + 2 <= 10 -> tripleStartPredicate a -> 6 <= a

namespace M8NatLateTripleInputs

variable {P : BrokenLatticePredicates G 8}

/-- Projection: a named triple equality supplies the recorded finite predicate. -/
theorem predicate_of_triple {a : M8TripleStartIndex}
    (H : M8NatLateTripleInputs P) (htriple : P.tripleEquality a) :
    H.tripleStartPredicate a.1 :=
  H.predicate_of_tripleEquality a htriple

/-- Projection: the recorded finite predicate is late on subtype indices. -/
theorem late_of_predicate_at_index {a : M8TripleStartIndex}
    (H : M8NatLateTripleInputs P)
    (hpred : H.tripleStartPredicate a.1) :
    6 <= a.1 :=
  H.late_of_predicate a.1 a.2.1 a.2.2 hpred

/-- Projection: a named triple equality starts late. -/
theorem late_of_tripleEquality {a : M8TripleStartIndex}
    (H : M8NatLateTripleInputs P) (htriple : P.tripleEquality a) :
    6 <= a.1 :=
  H.late_of_predicate_at_index (H.predicate_of_triple htriple)

/-- The finite predicate package gives the raw late-triples predicate. -/
theorem lateTriples (H : M8NatLateTripleInputs P) :
    M8BrokenLatticeLateTriples P := by
  intro a htriple
  exact H.late_of_tripleEquality htriple

end M8NatLateTripleInputs

/-- Direct theorem form of `M8NatLateTripleInputs.lateTriples`. -/
theorem m8BrokenLatticeLateTriples_of_natPredicate
    (P : BrokenLatticePredicates G 8)
    (tripleStartPredicate : Nat -> Prop)
    (hpred :
      forall a : M8TripleStartIndex,
        P.tripleEquality a -> tripleStartPredicate a.1)
    (hlate :
      forall a : Nat,
        1 <= a -> a + 2 <= 10 -> tripleStartPredicate a -> 6 <= a) :
    M8BrokenLatticeLateTriples P :=
  (M8NatLateTripleInputs.mk tripleStartPredicate hpred hlate).lateTriples

/-- A structured early-obstruction package.

This is useful when the paper combinatorics proves an intermediate obstruction
from an early triple, then proves that obstruction impossible in the same
finite index range. -/
structure M8EarlyTripleObstructionInputs
    (P : BrokenLatticePredicates G 8) where
  obstruction : M8TripleStartIndex -> Prop
  obstruction_of_early_triple :
    forall a : M8TripleStartIndex,
      M8TripleStartEarly a -> P.tripleEquality a -> obstruction a
  obstruction_false :
    forall a : M8TripleStartIndex,
      M8TripleStartEarly a -> Not (obstruction a)

namespace M8EarlyTripleObstructionInputs

variable {P : BrokenLatticePredicates G 8}

/-- Projection: an early triple equality gives the recorded obstruction. -/
theorem obstruction_of_triple {a : M8TripleStartIndex}
    (H : M8EarlyTripleObstructionInputs P)
    (hearly : M8TripleStartEarly a) (htriple : P.tripleEquality a) :
    H.obstruction a :=
  H.obstruction_of_early_triple a hearly htriple

/-- The obstruction package rules out all early triple equalities. -/
theorem noEarlyTripleEquality (H : M8EarlyTripleObstructionInputs P) :
    M8NoEarlyTripleEquality P := by
  intro a hearly htriple
  exact H.obstruction_false a hearly
    (H.obstruction_of_triple hearly htriple)

/-- The obstruction package gives the raw late-triples predicate. -/
theorem lateTriples (H : M8EarlyTripleObstructionInputs P) :
    M8BrokenLatticeLateTriples P :=
  m8BrokenLatticeLateTriples_of_noEarlyTripleEquality P
    H.noEarlyTripleEquality

end M8EarlyTripleObstructionInputs

/-! ## Honest-package wrappers -/

namespace M8HonestLocalPredicates

variable (P : M8HonestLocalPredicates G)

/-- Honest-package wrapper for a direct early-triple exclusion. -/
theorem lateTriples_of_noEarlyTripleEquality
    (hno : M8NoEarlyTripleEquality P.data) :
    P.LateTriples :=
  m8BrokenLatticeLateTriples_of_noEarlyTripleEquality P.data hno

/-- Honest-package wrapper for finite natural-index late-triple inputs. -/
theorem lateTriples_of_natLateTripleInputs
    (H : M8NatLateTripleInputs P.data) :
    P.LateTriples :=
  H.lateTriples

/-- Honest-package wrapper for an early-obstruction package. -/
theorem lateTriples_of_earlyTripleObstructionInputs
    (H : M8EarlyTripleObstructionInputs P.data) :
    P.LateTriples :=
  H.lateTriples

end M8HonestLocalPredicates

/-- A small package pairing an honest local predicate package with the finite
inputs needed to obtain its late-triples field. -/
structure M8HonestLateTriplesPackage (G : LocalGraph V) where
  predicates : M8HonestLocalPredicates G
  lateInputs : M8NatLateTripleInputs predicates.data

namespace M8HonestLateTriplesPackage

variable {G : LocalGraph V}

/-- Projection to the honest local predicates. -/
def toHonestLocalPredicates (H : M8HonestLateTriplesPackage G) :
    M8HonestLocalPredicates G :=
  H.predicates

/-- Projection to the finite natural-index inputs. -/
def toNatLateTripleInputs (H : M8HonestLateTriplesPackage G) :
    M8NatLateTripleInputs H.predicates.data :=
  H.lateInputs

/-- The packaged finite inputs provide the honest `P.LateTriples` hypothesis. -/
theorem lateTriples (H : M8HonestLateTriplesPackage G) :
    H.predicates.LateTriples :=
  H.lateInputs.lateTriples

/-- Projection: a named triple equality in the packaged predicates starts late. -/
theorem late_of_tripleEquality (H : M8HonestLateTriplesPackage G)
    {a : M8TripleStartIndex}
    (htriple : H.predicates.data.tripleEquality a) :
    6 <= a.1 :=
  H.lateInputs.late_of_tripleEquality htriple

end M8HonestLateTriplesPackage

end LateTriplesInterface
end Swanepoel
end ErdosProblems1066
