import ErdosProblems1066.Swanepoel.LateTriplesInterface
import ErdosProblems1066.Swanepoel.M8LateTriplesFromNoEarly

/-!
# Concrete no-early-triple helpers

This module supplies the finite `m = 8` bookkeeping behind the
`M8NoEarlyTripleEquality` input used by `M8LateTriplesFromNoEarly`.

The abstract interface says that every triple-start index with value at most
`5` is excluded.  Here we expose the equivalent concrete five obligations,
one for each early start `1, ..., 5`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyTripleConcrete

open LateTriplesInterface
open Lemma10Bridge
open LocalConfigurations

universe u

variable {V : Type u} {G : LocalGraph V}

/-! ## Concrete early starts -/

/-- The concrete triple-start index at `1`. -/
def start1 : M8TripleStartIndex :=
  m8TripleStartIndexOfNat 1 (by omega)

/-- The concrete triple-start index at `2`. -/
def start2 : M8TripleStartIndex :=
  m8TripleStartIndexOfNat 2 (by omega)

/-- The concrete triple-start index at `3`. -/
def start3 : M8TripleStartIndex :=
  m8TripleStartIndexOfNat 3 (by omega)

/-- The concrete triple-start index at `4`. -/
def start4 : M8TripleStartIndex :=
  m8TripleStartIndexOfNat 4 (by omega)

/-- The concrete triple-start index at `5`. -/
def start5 : M8TripleStartIndex :=
  m8TripleStartIndexOfNat 5 (by omega)

@[simp] theorem start1_val : (start1 : M8TripleStartIndex).1 = 1 := rfl
@[simp] theorem start2_val : (start2 : M8TripleStartIndex).1 = 2 := rfl
@[simp] theorem start3_val : (start3 : M8TripleStartIndex).1 = 3 := rfl
@[simp] theorem start4_val : (start4 : M8TripleStartIndex).1 = 4 := rfl
@[simp] theorem start5_val : (start5 : M8TripleStartIndex).1 = 5 := rfl

/-- Every early `m = 8` triple start is one of the five concrete starts. -/
theorem early_start_cases (a : M8TripleStartIndex)
    (hearly : M8TripleStartEarly a) :
    a = start1 \/ a = start2 \/ a = start3 \/ a = start4 \/ a = start5 := by
  have hbounds := m8TripleStartIndex_bounds a
  unfold M8TripleStartEarly at hearly
  have hcases : a.1 = 1 \/ a.1 = 2 \/ a.1 = 3 \/ a.1 = 4 \/ a.1 = 5 := by
    omega
  match hcases with
  | Or.inl h =>
      left
      apply Subtype.ext
      exact h
  | Or.inr (Or.inl h) =>
      right
      left
      apply Subtype.ext
      exact h
  | Or.inr (Or.inr (Or.inl h)) =>
      right
      right
      left
      apply Subtype.ext
      exact h
  | Or.inr (Or.inr (Or.inr (Or.inl h))) =>
      right
      right
      right
      left
      apply Subtype.ext
      exact h
  | Or.inr (Or.inr (Or.inr (Or.inr h))) =>
      right
      right
      right
      right
      apply Subtype.ext
      exact h

/-- A proof by cases over the five concrete early triple starts. -/
theorem early_start_induction
    {motive : M8TripleStartIndex -> Prop}
    (a : M8TripleStartIndex)
    (hearly : M8TripleStartEarly a)
    (h1 : motive start1)
    (h2 : motive start2)
    (h3 : motive start3)
    (h4 : motive start4)
    (h5 : motive start5) :
    motive a := by
  match early_start_cases a hearly with
  | Or.inl h => simpa [h] using h1
  | Or.inr (Or.inl h) => simpa [h] using h2
  | Or.inr (Or.inr (Or.inl h)) => simpa [h] using h3
  | Or.inr (Or.inr (Or.inr (Or.inl h))) => simpa [h] using h4
  | Or.inr (Or.inr (Or.inr (Or.inr h))) => simpa [h] using h5

/-! ## Five concrete exclusions as the abstract no-early input -/

/-- The five concrete early triple-equality exclusions. -/
structure M8ConcreteNoEarlyTripleEquality
    (P : BrokenLatticePredicates G 8) : Prop where
  no_start1 : Not (P.tripleEquality start1)
  no_start2 : Not (P.tripleEquality start2)
  no_start3 : Not (P.tripleEquality start3)
  no_start4 : Not (P.tripleEquality start4)
  no_start5 : Not (P.tripleEquality start5)

namespace M8ConcreteNoEarlyTripleEquality

variable {P : BrokenLatticePredicates G 8}

/-- The concrete five-exclusion package implies the abstract no-early
triple-equality predicate used by `LateTriplesInterface`. -/
theorem toNoEarlyTripleEquality
    (H : M8ConcreteNoEarlyTripleEquality P) :
    M8NoEarlyTripleEquality P := by
  intro a hearly
  exact early_start_induction (motive := fun a => Not (P.tripleEquality a)) a hearly
    H.no_start1 H.no_start2 H.no_start3 H.no_start4 H.no_start5

/-- The concrete five-exclusion package gives the raw late-triples predicate. -/
theorem toBrokenLatticeLateTriples
    (H : M8ConcreteNoEarlyTripleEquality P) :
    M8BrokenLatticeLateTriples P :=
  m8BrokenLatticeLateTriples_of_noEarlyTripleEquality P
    H.toNoEarlyTripleEquality

/-- The concrete five-exclusion package rules out an arbitrary early named
triple equality. -/
theorem not_tripleEquality_of_early
    (H : M8ConcreteNoEarlyTripleEquality P)
    {a : M8TripleStartIndex}
    (hearly : M8TripleStartEarly a) :
    Not (P.tripleEquality a) :=
  H.toNoEarlyTripleEquality a hearly

end M8ConcreteNoEarlyTripleEquality

/-! ## Honest-package and bridge-facing wrappers -/

namespace M8HonestLocalPredicates

variable {P : M8HonestLocalPredicates G}

/-- Concrete early exclusions give the honest local late-triples field. -/
theorem lateTriples_of_concreteNoEarlyTripleEquality
    (H : M8ConcreteNoEarlyTripleEquality P.data) :
    P.LateTriples :=
  H.toBrokenLatticeLateTriples

/-- Concrete early exclusions give the bridge package expected by
`M8LateTriplesFromNoEarly`. -/
theorem pipelineNoEarlyTriples_of_concrete
    (H : M8ConcreteNoEarlyTripleEquality P.data) :
    M8LateTriplesFromNoEarly.M8PipelineNoEarlyTriples P where
  noEarlyTripleEquality := H.toNoEarlyTripleEquality

/-- Concrete early exclusions give the pipeline late-triples field used by
`M8PipelineClosure`. -/
theorem pipelineLateTriplesField_of_concrete
    (H : M8ConcreteNoEarlyTripleEquality P.data) :
    M8PipelineClosure.M8LateTriplesField P :=
  (pipelineNoEarlyTriples_of_concrete H).toM8LateTriplesField

end M8HonestLocalPredicates

/-- Direct theorem form: five concrete exclusions imply late triples. -/
theorem m8BrokenLatticeLateTriples_of_concreteNoEarlyTripleEquality
    (P : BrokenLatticePredicates G 8)
    (H : M8ConcreteNoEarlyTripleEquality P) :
    M8BrokenLatticeLateTriples P :=
  H.toBrokenLatticeLateTriples

end NoEarlyTripleConcrete
end Swanepoel
end ErdosProblems1066
