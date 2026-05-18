import ErdosProblems1066.Swanepoel.Arithmetic
import ErdosProblems1066.Swanepoel.LocalConfigurations

/-!
# Swanepoel Lemma 10 index bridge

This module connects the already-checked finite `m = 8` index contradiction
from `Swanepoel.Arithmetic` to the local broken-lattice vocabulary in
`Swanepoel.LocalConfigurations`.

It deliberately does not state the Euclidean `8 / 31` theorem.  The hypotheses
below are local finite hypotheses: Lemma 10 has at most one failed equality,
and Lemma 9 makes every triple of equalities start late.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma10Bridge

open LocalConfigurations

universe u

/-! ## The `m = 8` local index ranges -/

/-- The Lemma 10 comparison indices for the `m = 8` specialization. -/
abbrev M8Lemma10Index : Type :=
  Lemma10Index 8

/-- The starts of three consecutive Lemma 10 comparisons for `m = 8`. -/
abbrev M8TripleStartIndex : Type :=
  TripleStartIndex 8

/-- Turn an in-range natural number into a Lemma 10 comparison index. -/
def m8Lemma10IndexOfNat (i : Nat) (hi : 1 <= i /\ i <= 10) :
    M8Lemma10Index :=
  Subtype.mk i (by simpa [M8Lemma10Index, Lemma10Index] using hi)

/-- Turn an in-range natural number into a triple-start index. -/
def m8TripleStartIndexOfNat (a : Nat) (ha : 1 <= a /\ a + 2 <= 10) :
    M8TripleStartIndex :=
  Subtype.mk a (by simpa [M8TripleStartIndex, TripleStartIndex] using ha)

/-- The left extra-neighbor index used by the comparison `s_i = r_{i+1}`. -/
def m8LeftExtraIndex (i : M8Lemma10Index) : ExtraIndex 8 :=
  Subtype.mk i.1 (by
    have hi := i.2
    constructor
    case left => exact hi.1
    case right => omega)

/-- The right extra-neighbor index used by the comparison `s_i = r_{i+1}`. -/
def m8RightExtraIndex (i : M8Lemma10Index) : ExtraIndex 8 :=
  Subtype.mk (i.1 + 1) (by
    have hi := i.2
    constructor
    case left => omega
    case right => omega)

/-! ## Honest equality predicates on local labels -/

variable {V : Type u}

/-- The actual label equality appearing in Swanepoel Lemma 10. -/
def M8LabelEquality (labels : BrokenLatticeLabels V 8)
    (i : M8Lemma10Index) : Prop :=
  labels.s (m8LeftExtraIndex i) = labels.r (m8RightExtraIndex i)

/-- A natural-number view of the actual `m = 8` Lemma 10 equality. -/
def M8LabelGood (labels : BrokenLatticeLabels V 8) (i : Nat) : Prop :=
  if hi : 1 <= i /\ i <= 10 then
    M8LabelEquality labels (m8Lemma10IndexOfNat i hi)
  else
    False

/-- Three consecutive actual Lemma 10 equalities. -/
def M8LabelTriple (labels : BrokenLatticeLabels V 8)
    (a : M8TripleStartIndex) : Prop :=
  M8LabelGood labels a.1 /\
    M8LabelGood labels (a.1 + 1) /\
    M8LabelGood labels (a.1 + 2)

/-- Any true natural-number Lemma 10 equality carries its range proof. -/
lemma m8LabelGood_bounds {labels : BrokenLatticeLabels V 8} {i : Nat}
    (hgood : M8LabelGood labels i) :
    1 <= i /\ i <= 10 := by
  by_cases hi : 1 <= i /\ i <= 10
  case pos => exact hi
  case neg => simp [M8LabelGood, hi] at hgood

/-! ## Local broken-lattice predicates -/

variable {G : LocalGraph V}

/-- A natural-number view of a local Lemma 10 predicate. -/
def M8BrokenLatticeGood (P : BrokenLatticePredicates G 8) (i : Nat) : Prop :=
  if hi : 1 <= i /\ i <= 10 then
    P.lemma10Equality (m8Lemma10IndexOfNat i hi)
  else
    False

/-- Three consecutive local Lemma 10 predicates. -/
def M8BrokenLatticeTriple (P : BrokenLatticePredicates G 8)
    (a : M8TripleStartIndex) : Prop :=
  M8BrokenLatticeGood P a.1 /\
    M8BrokenLatticeGood P (a.1 + 1) /\
    M8BrokenLatticeGood P (a.1 + 2)

/-- The failed Lemma 10 comparisons in the finite range `1, ..., 10`. -/
def M8BrokenLatticeFailures (P : BrokenLatticePredicates G 8)
    [DecidablePred (M8BrokenLatticeGood P)] : Finset Nat :=
  (Finset.Icc 1 10).filter fun i => Not (M8BrokenLatticeGood P i)

/-- The local Lemma 10 conclusion: at most one comparison fails. -/
def M8AtMostOneBrokenLatticeFailure
    (P : BrokenLatticePredicates G 8)
    [DecidablePred (M8BrokenLatticeGood P)] : Prop :=
  (M8BrokenLatticeFailures P).card <= 1

/-- The local Lemma 9 conclusion specialized to `m = 8`: triples start late. -/
def M8BrokenLatticeLateTriples (P : BrokenLatticePredicates G 8) : Prop :=
  forall a : M8TripleStartIndex, P.tripleEquality a -> 6 <= a.1

/-- Any true local Lemma 10 predicate carries its range proof. -/
lemma m8BrokenLatticeGood_bounds {P : BrokenLatticePredicates G 8} {i : Nat}
    (hgood : M8BrokenLatticeGood P i) :
    1 <= i /\ i <= 10 := by
  by_cases hi : 1 <= i /\ i <= 10
  case pos => exact hi
  case neg => simp [M8BrokenLatticeGood, hi] at hgood

/-- Local late-triple hypotheses give the natural-number late-triple predicate
needed by the finite arithmetic contradiction. -/
lemma m8_nat_late_triples_of_local
    (P : BrokenLatticePredicates G 8)
    (htriple :
      forall a : M8TripleStartIndex,
        P.tripleEquality a <-> M8BrokenLatticeTriple P a)
    (hlate : M8BrokenLatticeLateTriples P) :
    forall a : Nat,
      M8BrokenLatticeGood P a ->
      M8BrokenLatticeGood P (a + 1) ->
      M8BrokenLatticeGood P (a + 2) ->
      6 <= a := by
  intro a ha ha1 ha2
  have ha_bounds := m8BrokenLatticeGood_bounds (P := P) ha
  have ha2_bounds := m8BrokenLatticeGood_bounds (P := P) ha2
  let A : M8TripleStartIndex :=
    m8TripleStartIndexOfNat a (And.intro ha_bounds.1 ha2_bounds.2)
  have hA : M8BrokenLatticeTriple P A := by
    simpa [M8BrokenLatticeTriple, A] using And.intro ha (And.intro ha1 ha2)
  exact hlate A ((htriple A).2 hA)

/-- The local `m = 8` finite contradiction: Lemma 10 leaves at most one failed
comparison, while Lemma 9 forces every triple of comparisons to start at least
at `6`. -/
theorem contradiction_of_atMostOneFailure_and_lateTriples
    (P : BrokenLatticePredicates G 8)
    [DecidablePred (M8BrokenLatticeGood P)]
    (htriple :
      forall a : M8TripleStartIndex,
        P.tripleEquality a <-> M8BrokenLatticeTriple P a)
    (hcard : M8AtMostOneBrokenLatticeFailure P)
    (hlate : M8BrokenLatticeLateTriples P) :
    False := by
  exact ErdosProblems1066.Swanepoel.Arithmetic.final_m8_index_contradiction
    (M8BrokenLatticeGood P)
    (by
      simpa [M8AtMostOneBrokenLatticeFailure, M8BrokenLatticeFailures]
        using hcard)
    (m8_nat_late_triples_of_local P htriple hlate)

/-! ## A package for honest local predicates -/

/-- A local `m = 8` broken-lattice package whose named predicates are tied to
the actual label equalities used in Lemma 10. -/
structure M8HonestLocalPredicates (G : LocalGraph V) where
  data : BrokenLatticePredicates G 8
  lemma10Equality_iff_labels :
    forall i : M8Lemma10Index,
      data.lemma10Equality i <-> M8LabelEquality data.labels i
  tripleEquality_iff_threeComparisons :
    forall a : M8TripleStartIndex,
      data.tripleEquality a <-> M8BrokenLatticeTriple data a

namespace M8HonestLocalPredicates

/-- At most one Lemma 10 failure, phrased for an honest local package. -/
def AtMostOneFailure (P : M8HonestLocalPredicates G)
    [DecidablePred (M8BrokenLatticeGood P.data)] : Prop :=
  M8AtMostOneBrokenLatticeFailure P.data

/-- The late-triple predicate, phrased for an honest local package. -/
def LateTriples (P : M8HonestLocalPredicates G) : Prop :=
  M8BrokenLatticeLateTriples P.data

/-- The actual label equality and the named local predicate agree at every
natural-number index in `1, ..., 10`. -/
lemma good_iff_labelGood (P : M8HonestLocalPredicates G) (i : Nat) :
    M8BrokenLatticeGood P.data i <-> M8LabelGood P.data.labels i := by
  by_cases hi : 1 <= i /\ i <= 10
  case pos =>
    simp [M8BrokenLatticeGood, M8LabelGood, hi,
      P.lemma10Equality_iff_labels (m8Lemma10IndexOfNat i hi)]
  case neg =>
    simp [M8BrokenLatticeGood, M8LabelGood, hi]

/-- The honest-package form of the local finite contradiction. -/
theorem contradiction
    (P : M8HonestLocalPredicates G)
    [DecidablePred (M8BrokenLatticeGood P.data)]
    (hcard : P.AtMostOneFailure)
    (hlate : P.LateTriples) :
    False :=
  contradiction_of_atMostOneFailure_and_lateTriples P.data
    P.tripleEquality_iff_threeComparisons hcard hlate

end M8HonestLocalPredicates

end Lemma10Bridge
end Swanepoel
end ErdosProblems1066
