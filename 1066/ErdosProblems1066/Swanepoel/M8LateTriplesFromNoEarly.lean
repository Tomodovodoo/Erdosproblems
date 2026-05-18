import ErdosProblems1066.Swanepoel.LateTriplesInterface
import ErdosProblems1066.Swanepoel.M8ConstructionInterface
import ErdosProblems1066.Swanepoel.M8PipelineClosure

/-!
# M8 late triples from no-early-triple exclusions

This module is a bridge layer from the explicit finite no-early-triple
combinatorics packaged in `LateTriplesInterface` to the late-triples fields
used by `M8ConstructionInterface` and `M8PipelineClosure`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8LateTriplesFromNoEarly

open LateTriplesInterface
open Lemma10Bridge
open LocalConfigurations

universe u

variable {V : Type u} {G : LocalGraph V}

/-! ## Label-level bridge -/

/-- A labelled triple of true Lemma 10 comparisons gives the corresponding
honest local named triple equality. -/
theorem tripleEquality_of_labelTriple
    (P : M8HonestLocalPredicates G) {a : M8TripleStartIndex}
    (h0 : M8LabelGood P.data.labels a.1)
    (h1 : M8LabelGood P.data.labels (a.1 + 1))
    (h2 : M8LabelGood P.data.labels (a.1 + 2)) :
    P.data.tripleEquality a := by
  apply (P.tripleEquality_iff_threeComparisons a).2
  exact And.intro
    ((P.good_iff_labelGood a.1).2 h0)
    (And.intro
      ((P.good_iff_labelGood (a.1 + 1)).2 h1)
      ((P.good_iff_labelGood (a.1 + 2)).2 h2))

/-- Direct no-early-triple exclusions imply the label-level late-triples
field used by `M8ConstructionInterface`. -/
theorem labelLateTriples_of_noEarlyTripleEquality
    (P : M8HonestLocalPredicates G)
    (hno : M8NoEarlyTripleEquality P.data) :
    BrokenLatticePipeline.M8LabelLateTriples P.data.labels := by
  intro a h0 h1 h2
  have hb0 := m8LabelGood_bounds (labels := P.data.labels) h0
  have hb2 := m8LabelGood_bounds (labels := P.data.labels) h2
  let A : M8TripleStartIndex :=
    m8TripleStartIndexOfNat a (And.intro hb0.1 hb2.2)
  have htriple : P.data.tripleEquality A := by
    exact tripleEquality_of_labelTriple P (a := A) h0 h1 h2
  exact M8HonestLocalPredicates.lateTriples_of_noEarlyTripleEquality P hno
    A htriple

/-! ## `M8ConstructionInterface` bridge -/

/-- Explicit no-early-triple input for the construction-interface late-triples
field. -/
structure M8ConstructionNoEarlyTriples {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C) : Prop where
  noEarlyTripleEquality :
    M8NoEarlyTripleEquality localLabels.predicates.data

namespace M8ConstructionNoEarlyTriples

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8ConstructionInterface.M8LocalLabels C}

/-- Projection to the raw no-early-triple exclusion. -/
theorem toNoEarlyTripleEquality
    (H : M8ConstructionNoEarlyTriples localLabels) :
    M8NoEarlyTripleEquality localLabels.predicates.data :=
  H.noEarlyTripleEquality

/-- Projection to the honest local late-triples field. -/
theorem toHonestLateTriples
    (H : M8ConstructionNoEarlyTriples localLabels) :
    localLabels.predicates.LateTriples :=
  M8HonestLocalPredicates.lateTriples_of_noEarlyTripleEquality
    localLabels.predicates H.noEarlyTripleEquality

/-- Projection to the label-level late-triples field. -/
theorem toLabelLateTriples
    (H : M8ConstructionNoEarlyTriples localLabels) :
    BrokenLatticePipeline.M8LabelLateTriples localLabels.labels :=
  labelLateTriples_of_noEarlyTripleEquality
    localLabels.predicates H.noEarlyTripleEquality

/-- Projection to `M8ConstructionInterface.M8LateTriples`. -/
theorem toM8LateTriples
    (H : M8ConstructionNoEarlyTriples localLabels) :
    M8ConstructionInterface.M8LateTriples localLabels where
  labelLateTriples := H.toLabelLateTriples

/-- A named triple equality in the construction labels starts late. -/
theorem late_of_tripleEquality
    (H : M8ConstructionNoEarlyTriples localLabels)
    {a : M8TripleStartIndex}
    (htriple : localLabels.predicates.data.tripleEquality a) :
    6 <= a.1 :=
  H.toHonestLateTriples a htriple

end M8ConstructionNoEarlyTriples

/-! ## `M8PipelineClosure` bridge -/

/-- Explicit no-early-triple input for the pipeline-closure late-triples
field. -/
structure M8PipelineNoEarlyTriples
    (P : M8HonestLocalPredicates G) : Prop where
  noEarlyTripleEquality : M8NoEarlyTripleEquality P.data

namespace M8PipelineNoEarlyTriples

variable {P : M8HonestLocalPredicates G}

/-- Projection to the raw no-early-triple exclusion. -/
theorem toNoEarlyTripleEquality
    (H : M8PipelineNoEarlyTriples P) :
    M8NoEarlyTripleEquality P.data :=
  H.noEarlyTripleEquality

/-- Projection to the honest local late-triples field. -/
theorem toHonestLateTriples
    (H : M8PipelineNoEarlyTriples P) :
    P.LateTriples :=
  M8HonestLocalPredicates.lateTriples_of_noEarlyTripleEquality
    P H.noEarlyTripleEquality

/-- Projection to the pipeline-closure late-triples field. -/
theorem toM8LateTriplesField
    (H : M8PipelineNoEarlyTriples P) :
    M8PipelineClosure.M8LateTriplesField P where
  lateTriples := H.toHonestLateTriples

/-- Projection to the label-level late-triples field, useful when the same
input is fed into `M8ConstructionInterface`. -/
theorem toLabelLateTriples
    (H : M8PipelineNoEarlyTriples P) :
    BrokenLatticePipeline.M8LabelLateTriples P.data.labels :=
  labelLateTriples_of_noEarlyTripleEquality P H.noEarlyTripleEquality

/-- A named triple equality in the pipeline predicates starts late. -/
theorem late_of_tripleEquality
    (H : M8PipelineNoEarlyTriples P) {a : M8TripleStartIndex}
    (htriple : P.data.tripleEquality a) :
    6 <= a.1 :=
  H.toHonestLateTriples a htriple

end M8PipelineNoEarlyTriples

/-! ## Direct theorem forms -/

/-- Direct constructor for the construction-interface late-triples field from
no-early-triple exclusions. -/
theorem m8ConstructionLateTriples_of_noEarlyTripleEquality
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C)
    (hno : M8NoEarlyTripleEquality localLabels.predicates.data) :
    M8ConstructionInterface.M8LateTriples localLabels :=
  (M8ConstructionNoEarlyTriples.mk hno).toM8LateTriples

/-- Direct constructor for the pipeline-closure late-triples field from
no-early-triple exclusions. -/
theorem m8PipelineLateTriplesField_of_noEarlyTripleEquality
    (P : M8HonestLocalPredicates G)
    (hno : M8NoEarlyTripleEquality P.data) :
    M8PipelineClosure.M8LateTriplesField P :=
  (M8PipelineNoEarlyTriples.mk hno).toM8LateTriplesField

end M8LateTriplesFromNoEarly
end Swanepoel
end ErdosProblems1066
