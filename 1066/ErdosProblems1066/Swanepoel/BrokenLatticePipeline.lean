import ErdosProblems1066.Swanepoel.Lemma10Bridge

/-!
# Swanepoel broken-lattice pipeline

This module strengthens the finite broken-lattice obstruction interface.  It
keeps the geometric content outside the file: callers provide honest labelled
local predicates and finite label-level consequences, and this file transports
those consequences to the existing `m = 8` contradiction.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticePipeline

open Lemma10Bridge
open LocalConfigurations

universe u

variable {V : Type u}

/-! ## Label-level finite predicates -/

/-- The failed labelled Lemma 10 comparisons in the finite range `1, ..., 10`. -/
noncomputable def M8LabelFailures (labels : BrokenLatticeLabels V 8) :
    Finset Nat := by
  classical
  exact (Finset.Icc 1 10).filter fun i => Not (M8LabelGood labels i)

/-- Lemma 10's finite consequence, phrased directly for labelled equalities. -/
def M8AtMostOneLabelFailure (labels : BrokenLatticeLabels V 8) : Prop :=
  (M8LabelFailures labels).card <= 1

/-- Lemma 9's finite consequence, phrased directly for labelled equalities:
every three consecutive true labelled Lemma 10 comparisons start late. -/
def M8LabelLateTriples (labels : BrokenLatticeLabels V 8) : Prop :=
  forall a : Nat,
    M8LabelGood labels a ->
    M8LabelGood labels (a + 1) ->
    M8LabelGood labels (a + 2) ->
    6 <= a

/-! ## Transport through honest local packages -/

namespace M8HonestLocalPredicates

variable {G : LocalGraph V}

/-- Label failures and named local-predicate failures are the same finite set
for an honest package. -/
lemma brokenLatticeFailures_eq_labelFailures
    (P : M8HonestLocalPredicates G)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    M8BrokenLatticeFailures P.data = M8LabelFailures P.data.labels := by
  classical
  apply Finset.ext
  intro i
  simp [M8BrokenLatticeFailures, M8LabelFailures, P.good_iff_labelGood i]

/-- At most one labelled failure gives at most one named local-predicate
failure for an honest package. -/
lemma atMostOneFailure_of_labelFailures
    (P : M8HonestLocalPredicates G)
    [DecidablePred (M8BrokenLatticeGood P.data)]
    (hlabel : M8AtMostOneLabelFailure P.data.labels) :
    Lemma10Bridge.M8HonestLocalPredicates.AtMostOneFailure P := by
  classical
  simpa [Lemma10Bridge.M8HonestLocalPredicates.AtMostOneFailure,
    M8AtMostOneBrokenLatticeFailure,
    M8AtMostOneLabelFailure, brokenLatticeFailures_eq_labelFailures P]
    using hlabel

/-- A true named local-predicate triple is a true labelled triple for an honest
package. -/
lemma labelTriple_of_tripleEquality
    (P : M8HonestLocalPredicates G) {a : M8TripleStartIndex}
    (htriple : P.data.tripleEquality a) :
    M8LabelGood P.data.labels a.1 /\
      M8LabelGood P.data.labels (a.1 + 1) /\
      M8LabelGood P.data.labels (a.1 + 2) := by
  have hlocal : M8BrokenLatticeTriple P.data a :=
    (P.tripleEquality_iff_threeComparisons a).1 htriple
  exact And.intro
    ((P.good_iff_labelGood a.1).1 hlocal.1)
    (And.intro
      ((P.good_iff_labelGood (a.1 + 1)).1 hlocal.2.1)
      ((P.good_iff_labelGood (a.1 + 2)).1 hlocal.2.2))

/-- Label-level late triples imply the existing local late-triple predicate for
an honest package. -/
lemma lateTriples_of_labelLateTriples
    (P : M8HonestLocalPredicates G)
    (hlabel : M8LabelLateTriples P.data.labels) :
    Lemma10Bridge.M8HonestLocalPredicates.LateTriples P := by
  intro a htriple
  have hlabels := labelTriple_of_tripleEquality P htriple
  exact hlabel a.1 hlabels.1 hlabels.2.1 hlabels.2.2

/-- Label-level finite consequences feed the existing honest local
contradiction. -/
theorem contradiction_of_labelFailures_and_labelLateTriples
    (P : M8HonestLocalPredicates G)
    (hcard : M8AtMostOneLabelFailure P.data.labels)
    (hlate : M8LabelLateTriples P.data.labels) :
    False := by
  classical
  exact Lemma10Bridge.M8HonestLocalPredicates.contradiction P
    (atMostOneFailure_of_labelFailures P hcard)
    (lateTriples_of_labelLateTriples P hlate)

end M8HonestLocalPredicates

end BrokenLatticePipeline
end Swanepoel
end ErdosProblems1066
