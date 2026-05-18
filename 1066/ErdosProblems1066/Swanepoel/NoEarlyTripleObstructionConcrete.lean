import ErdosProblems1066.Swanepoel.MinimalFailureLocalExclusions
import ErdosProblems1066.Swanepoel.M8TurnWindowNoEarlyFinal
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Concrete no-early-triple obstruction wrappers

This module is a finite bookkeeping layer.  It packages explicit local
contradictions at the five early `m = 8` triple starts and turns them into the
`M8ConcreteNoEarlyTripleEquality` and Lemma 9 no-early interfaces.

The local-exclusion-facing wrappers are intentionally conditional: a caller
supplies the checked local route from a triple equality to a forbidden local
pattern, while this file checks the finite reduction from those five local
contradictions to the no-early-triple and final `m = 8` contradiction
interfaces.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyTripleObstructionConcrete

open LateTriplesInterface
open Lemma10Bridge
open LocalConfigurations
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9

universe u

variable {V : Type u} {G : LocalGraph V}

/-! ## Five explicit local contradictions -/

/-- Five start-by-start implications from an early triple equality to `False`.

This is the most direct concrete obstruction format: each local exclusion has
already been discharged, and the only remaining task is finite packaging. -/
structure M8ConcreteFalseStartImplications
    (P : BrokenLatticePredicates G 8) : Prop where
  false_start1 : P.tripleEquality start1 -> False
  false_start2 : P.tripleEquality start2 -> False
  false_start3 : P.tripleEquality start3 -> False
  false_start4 : P.tripleEquality start4 -> False
  false_start5 : P.tripleEquality start5 -> False

namespace M8ConcreteFalseStartImplications

variable {P : BrokenLatticePredicates G 8}

/-- A concrete no-early package can be viewed as five explicit
contradictions. -/
def ofConcreteNoEarlyTripleEquality
    (H : M8ConcreteNoEarlyTripleEquality P) :
    M8ConcreteFalseStartImplications P where
  false_start1 := H.no_start1
  false_start2 := H.no_start2
  false_start3 := H.no_start3
  false_start4 := H.no_start4
  false_start5 := H.no_start5

/-- Package five explicit contradictions as the concrete no-early triple
input. -/
def toConcreteNoEarlyTripleEquality
    (H : M8ConcreteFalseStartImplications P) :
    M8ConcreteNoEarlyTripleEquality P where
  no_start1 := H.false_start1
  no_start2 := H.false_start2
  no_start3 := H.false_start3
  no_start4 := H.false_start4
  no_start5 := H.false_start5

/-- Five explicit contradictions imply the abstract no-early predicate. -/
theorem toNoEarlyTripleEquality
    (H : M8ConcreteFalseStartImplications P) :
    M8NoEarlyTripleEquality P :=
  H.toConcreteNoEarlyTripleEquality.toNoEarlyTripleEquality

/-- Five explicit contradictions imply the raw late-triples predicate. -/
theorem toBrokenLatticeLateTriples
    (H : M8ConcreteFalseStartImplications P) :
    M8BrokenLatticeLateTriples P :=
  H.toConcreteNoEarlyTripleEquality.toBrokenLatticeLateTriples

end M8ConcreteFalseStartImplications

/-- The false-start and concrete no-early packages contain exactly the same
five obligations. -/
theorem falseStartImplications_iff_concreteNoEarlyTripleEquality
    {P : BrokenLatticePredicates G 8} :
    M8ConcreteFalseStartImplications P <->
      M8ConcreteNoEarlyTripleEquality P := by
  constructor
  · intro H
    exact H.toConcreteNoEarlyTripleEquality
  · intro H
    exact M8ConcreteFalseStartImplications.ofConcreteNoEarlyTripleEquality H

/-- Direct theorem form for the false-start wrapper. -/
theorem concreteNoEarlyTripleEquality_of_falseStartImplications
    {P : BrokenLatticePredicates G 8}
    (H : M8ConcreteFalseStartImplications P) :
    M8ConcreteNoEarlyTripleEquality P :=
  H.toConcreteNoEarlyTripleEquality

/-! ## Indexed finite obstructions -/

/-- A concrete finite obstruction package indexed by the five early starts. -/
structure M8ConcreteIndexedObstructionInputs
    (P : BrokenLatticePredicates G 8) where
  obstruction : M8TripleStartIndex -> Prop
  obstruction_start1 : P.tripleEquality start1 -> obstruction start1
  obstruction_start2 : P.tripleEquality start2 -> obstruction start2
  obstruction_start3 : P.tripleEquality start3 -> obstruction start3
  obstruction_start4 : P.tripleEquality start4 -> obstruction start4
  obstruction_start5 : P.tripleEquality start5 -> obstruction start5
  obstruction_false_start1 : Not (obstruction start1)
  obstruction_false_start2 : Not (obstruction start2)
  obstruction_false_start3 : Not (obstruction start3)
  obstruction_false_start4 : Not (obstruction start4)
  obstruction_false_start5 : Not (obstruction start5)

namespace M8ConcreteIndexedObstructionInputs

variable {P : BrokenLatticePredicates G 8}

/-- Forget indexed obstructions to explicit contradictions. -/
def toFalseStartImplications
    (H : M8ConcreteIndexedObstructionInputs P) :
    M8ConcreteFalseStartImplications P where
  false_start1 h := H.obstruction_false_start1 (H.obstruction_start1 h)
  false_start2 h := H.obstruction_false_start2 (H.obstruction_start2 h)
  false_start3 h := H.obstruction_false_start3 (H.obstruction_start3 h)
  false_start4 h := H.obstruction_false_start4 (H.obstruction_start4 h)
  false_start5 h := H.obstruction_false_start5 (H.obstruction_start5 h)

/-- Indexed finite obstructions give the concrete no-early package. -/
def toConcreteNoEarlyTripleEquality
    (H : M8ConcreteIndexedObstructionInputs P) :
    M8ConcreteNoEarlyTripleEquality P :=
  H.toFalseStartImplications.toConcreteNoEarlyTripleEquality

/-- Indexed finite obstructions give the abstract no-early predicate. -/
theorem toNoEarlyTripleEquality
    (H : M8ConcreteIndexedObstructionInputs P) :
    M8NoEarlyTripleEquality P :=
  H.toConcreteNoEarlyTripleEquality.toNoEarlyTripleEquality

/-- Indexed finite obstructions give the raw late-triples predicate. -/
theorem toBrokenLatticeLateTriples
    (H : M8ConcreteIndexedObstructionInputs P) :
    M8BrokenLatticeLateTriples P :=
  H.toConcreteNoEarlyTripleEquality.toBrokenLatticeLateTriples

/-- Projection: an early triple equality gives the indexed obstruction. -/
theorem obstruction_of_early_triple
    (H : M8ConcreteIndexedObstructionInputs P)
    {a : M8TripleStartIndex}
    (hearly : M8TripleStartEarly a)
    (htriple : P.tripleEquality a) :
    H.obstruction a := by
  exact early_start_induction
    (motive := fun a => P.tripleEquality a -> H.obstruction a)
    a hearly
    H.obstruction_start1 H.obstruction_start2 H.obstruction_start3
    H.obstruction_start4 H.obstruction_start5 htriple

/-- Projection: the indexed obstruction is impossible at every early start. -/
theorem not_obstruction_of_early
    (H : M8ConcreteIndexedObstructionInputs P)
    {a : M8TripleStartIndex}
    (hearly : M8TripleStartEarly a) :
    Not (H.obstruction a) := by
  exact early_start_induction
    (motive := fun a => Not (H.obstruction a))
    a hearly
    H.obstruction_false_start1 H.obstruction_false_start2
    H.obstruction_false_start3 H.obstruction_false_start4
    H.obstruction_false_start5

/-- Projection: indexed obstructions rule out every early triple equality. -/
theorem false_of_early_triple
    (H : M8ConcreteIndexedObstructionInputs P)
    {a : M8TripleStartIndex}
    (hearly : M8TripleStartEarly a)
    (htriple : P.tripleEquality a) :
    False :=
  H.not_obstruction_of_early hearly
    (H.obstruction_of_early_triple hearly htriple)

/-- Indexed finite obstructions also provide the abstract obstruction package
from `LateTriplesInterface`. -/
def toEarlyTripleObstructionInputs
    (H : M8ConcreteIndexedObstructionInputs P) :
    M8EarlyTripleObstructionInputs P where
  obstruction := H.obstruction
  obstruction_of_early_triple := by
    intro a hearly htriple
    exact H.obstruction_of_early_triple hearly htriple
  obstruction_false := by
    intro a hearly
    exact H.not_obstruction_of_early hearly

end M8ConcreteIndexedObstructionInputs

/-- Abstract Lemma 9 early-obstruction inputs restrict to the five concrete
early starts. -/
def indexedObstructionInputs_of_earlyTripleObstructionInputs
    {P : BrokenLatticePredicates G 8}
    (H : M8EarlyTripleObstructionInputs P) :
    M8ConcreteIndexedObstructionInputs P where
  obstruction := H.obstruction
  obstruction_start1 :=
    H.obstruction_of_early_triple start1 (by simp [M8TripleStartEarly])
  obstruction_start2 :=
    H.obstruction_of_early_triple start2 (by simp [M8TripleStartEarly])
  obstruction_start3 :=
    H.obstruction_of_early_triple start3 (by simp [M8TripleStartEarly])
  obstruction_start4 :=
    H.obstruction_of_early_triple start4 (by simp [M8TripleStartEarly])
  obstruction_start5 :=
    H.obstruction_of_early_triple start5 (by simp [M8TripleStartEarly])
  obstruction_false_start1 :=
    H.obstruction_false start1 (by simp [M8TripleStartEarly])
  obstruction_false_start2 :=
    H.obstruction_false start2 (by simp [M8TripleStartEarly])
  obstruction_false_start3 :=
    H.obstruction_false start3 (by simp [M8TripleStartEarly])
  obstruction_false_start4 :=
    H.obstruction_false start4 (by simp [M8TripleStartEarly])
  obstruction_false_start5 :=
    H.obstruction_false start5 (by simp [M8TripleStartEarly])

/-- Lemma 9 five-start late facts are themselves an indexed obstruction:
the forbidden obstruction at an early start is the impossible inequality
`6 <= a`. -/
def indexedObstructionInputs_of_fiveStartLateFacts
    {P : BrokenLatticePredicates G 8}
    (H : M8Lemma9FiveStartLateFacts P) :
    M8ConcreteIndexedObstructionInputs P where
  obstruction a := 6 <= a.1
  obstruction_start1 := H.late_start1
  obstruction_start2 := H.late_start2
  obstruction_start3 := H.late_start3
  obstruction_start4 := H.late_start4
  obstruction_start5 := H.late_start5
  obstruction_false_start1 := by
    intro h
    have hlate : 6 <= (1 : Nat) := h
    omega
  obstruction_false_start2 := by
    intro h
    have hlate : 6 <= (2 : Nat) := h
    omega
  obstruction_false_start3 := by
    intro h
    have hlate : 6 <= (3 : Nat) := h
    omega
  obstruction_false_start4 := by
    intro h
    have hlate : 6 <= (4 : Nat) := h
    omega
  obstruction_false_start5 := by
    intro h
    have hlate : 6 <= (5 : Nat) := h
    omega

/-- Lemma 9 five-start late facts as abstract early-obstruction inputs. -/
def earlyTripleObstructionInputs_of_fiveStartLateFacts
    {P : BrokenLatticePredicates G 8}
    (H : M8Lemma9FiveStartLateFacts P) :
    M8EarlyTripleObstructionInputs P :=
  (indexedObstructionInputs_of_fiveStartLateFacts H).toEarlyTripleObstructionInputs

/-- Lemma 9 five-start late facts as explicit false-start contradictions. -/
def falseStartImplications_of_fiveStartLateFacts
    {P : BrokenLatticePredicates G 8}
    (H : M8Lemma9FiveStartLateFacts P) :
    M8ConcreteFalseStartImplications P :=
  (indexedObstructionInputs_of_fiveStartLateFacts H).toFalseStartImplications

/-- The indexed-obstruction view of Lemma 9 facts gives the abstract
no-early predicate. -/
theorem noEarlyTripleEquality_of_fiveStartLateFacts_via_obstruction
    {P : BrokenLatticePredicates G 8}
    (H : M8Lemma9FiveStartLateFacts P) :
    M8NoEarlyTripleEquality P :=
  (earlyTripleObstructionInputs_of_fiveStartLateFacts H).noEarlyTripleEquality

/-- The indexed-obstruction view of Lemma 9 facts gives the same concrete
no-early package. -/
theorem concreteNoEarlyTripleEquality_of_fiveStartLateFacts_via_obstruction
    {P : BrokenLatticePredicates G 8}
    (H : M8Lemma9FiveStartLateFacts P) :
    M8ConcreteNoEarlyTripleEquality P :=
  (indexedObstructionInputs_of_fiveStartLateFacts H).toConcreteNoEarlyTripleEquality

/-! ## Single forbidden local pattern -/

/-- Five early triple equalities all force one forbidden local pattern. -/
structure M8ConcreteForbiddenObstructionInputs
    (P : BrokenLatticePredicates G 8) (forbidden : Prop) : Prop where
  forbidden_start1 : P.tripleEquality start1 -> forbidden
  forbidden_start2 : P.tripleEquality start2 -> forbidden
  forbidden_start3 : P.tripleEquality start3 -> forbidden
  forbidden_start4 : P.tripleEquality start4 -> forbidden
  forbidden_start5 : P.tripleEquality start5 -> forbidden

namespace M8ConcreteForbiddenObstructionInputs

variable {P : BrokenLatticePredicates G 8} {forbidden : Prop}

/-- Projection: any early triple equality forces the single forbidden local
pattern. -/
theorem forbidden_of_early_triple
    (H : M8ConcreteForbiddenObstructionInputs P forbidden)
    {a : M8TripleStartIndex}
    (hearly : M8TripleStartEarly a)
    (htriple : P.tripleEquality a) :
    forbidden := by
  exact early_start_induction
    (motive := fun a => P.tripleEquality a -> forbidden)
    a hearly
    H.forbidden_start1 H.forbidden_start2 H.forbidden_start3
    H.forbidden_start4 H.forbidden_start5 htriple

/-- Projection: a forbidden local pattern exclusion rules out any early
triple equality. -/
theorem false_of_early_triple
    (H : M8ConcreteForbiddenObstructionInputs P forbidden)
    (hforbidden : Not forbidden)
    {a : M8TripleStartIndex}
    (hearly : M8TripleStartEarly a)
    (htriple : P.tripleEquality a) :
    False :=
  hforbidden (H.forbidden_of_early_triple hearly htriple)

/-- A proof that the local pattern is forbidden turns the five implications
into explicit contradictions. -/
def toFalseStartImplications
    (H : M8ConcreteForbiddenObstructionInputs P forbidden)
    (hforbidden : Not forbidden) :
    M8ConcreteFalseStartImplications P where
  false_start1 h := hforbidden (H.forbidden_start1 h)
  false_start2 h := hforbidden (H.forbidden_start2 h)
  false_start3 h := hforbidden (H.forbidden_start3 h)
  false_start4 h := hforbidden (H.forbidden_start4 h)
  false_start5 h := hforbidden (H.forbidden_start5 h)

/-- A forbidden local pattern gives the concrete no-early package. -/
def toConcreteNoEarlyTripleEquality
    (H : M8ConcreteForbiddenObstructionInputs P forbidden)
    (hforbidden : Not forbidden) :
    M8ConcreteNoEarlyTripleEquality P :=
  (H.toFalseStartImplications hforbidden).toConcreteNoEarlyTripleEquality

/-- A single forbidden local pattern is an index-independent obstruction. -/
def toIndexedObstructionInputs
    (H : M8ConcreteForbiddenObstructionInputs P forbidden)
    (hforbidden : Not forbidden) :
    M8ConcreteIndexedObstructionInputs P where
  obstruction := fun _ => forbidden
  obstruction_start1 := H.forbidden_start1
  obstruction_start2 := H.forbidden_start2
  obstruction_start3 := H.forbidden_start3
  obstruction_start4 := H.forbidden_start4
  obstruction_start5 := H.forbidden_start5
  obstruction_false_start1 := hforbidden
  obstruction_false_start2 := hforbidden
  obstruction_false_start3 := hforbidden
  obstruction_false_start4 := hforbidden
  obstruction_false_start5 := hforbidden

/-- A single forbidden local pattern also supplies the abstract Lemma
9-style early-obstruction package. -/
def toEarlyTripleObstructionInputs
    (H : M8ConcreteForbiddenObstructionInputs P forbidden)
    (hforbidden : Not forbidden) :
    M8EarlyTripleObstructionInputs P :=
  (H.toIndexedObstructionInputs hforbidden).toEarlyTripleObstructionInputs

/-- A forbidden local pattern gives the abstract no-early predicate. -/
theorem toNoEarlyTripleEquality
    (H : M8ConcreteForbiddenObstructionInputs P forbidden)
    (hforbidden : Not forbidden) :
    M8NoEarlyTripleEquality P :=
  (H.toConcreteNoEarlyTripleEquality hforbidden).toNoEarlyTripleEquality

end M8ConcreteForbiddenObstructionInputs

/-! ## Local-exclusion specializations -/

/-- A `K_{2,3}` obstruction package for the five early starts. -/
abbrev M8ConcreteK23ObstructionInputs
    (P : BrokenLatticePredicates G 8) : Prop :=
  M8ConcreteForbiddenObstructionInputs P (HasK23 G)

/-- Five implications to `K_{2,3}`, plus an explicit no-`K_{2,3}` local
exclusion, give the concrete no-early package. -/
def concreteNoEarlyTripleEquality_of_K23Obstruction
    {P : BrokenLatticePredicates G 8}
    (H : M8ConcreteK23ObstructionInputs P)
    (hnoK23 : Not (HasK23 G)) :
    M8ConcreteNoEarlyTripleEquality P :=
  H.toConcreteNoEarlyTripleEquality hnoK23

/-- Finite local exclusions include no `K_{2,3}`, so a `K_{2,3}` obstruction
closes the concrete no-early package. -/
def concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
    {P : BrokenLatticePredicates G 8}
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8ConcreteNoEarlyTripleEquality P :=
  concreteNoEarlyTripleEquality_of_K23Obstruction H E.noK23

/-- A `K_{2,3}` obstruction plus no-`K_{2,3}` gives the abstract Lemma
9-style early-obstruction package. -/
def earlyTripleObstructionInputs_of_K23Obstruction
    {P : BrokenLatticePredicates G 8}
    (H : M8ConcreteK23ObstructionInputs P)
    (hnoK23 : Not (HasK23 G)) :
    M8EarlyTripleObstructionInputs P :=
  H.toEarlyTripleObstructionInputs hnoK23

/-- Finite local exclusions route a `K_{2,3}` obstruction into the abstract
Lemma 9-style early-obstruction package. -/
def earlyTripleObstructionInputs_of_K23Obstruction_and_finiteLocalExclusions
    {P : BrokenLatticePredicates G 8}
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8EarlyTripleObstructionInputs P :=
  earlyTripleObstructionInputs_of_K23Obstruction H E.noK23

/-- The geometric finite local-exclusion package for a unit-distance
configuration closes a `K_{2,3}` obstruction directly. -/
def concreteNoEarlyTripleEquality_of_K23Obstruction_and_unitDistanceConfig
    {n : Nat} {C : _root_.UDConfig n}
    {P : BrokenLatticePredicates
      (GraphBridge.unitDistanceLocalGraph C) 8}
    (H : M8ConcreteK23ObstructionInputs P) :
    M8ConcreteNoEarlyTripleEquality P :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
    H (finiteLocalExclusionPackage_of_unitDistanceConfig C)

/-- Direct construction-interface wrapper for `K_{2,3}` obstructions under a
finite local-exclusion package. -/
def constructionNoEarlyTriples_of_K23Obstruction_and_finiteLocalExclusions
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (E : FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C)) :
    M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples localLabels :=
  constructionNoEarlyTriples_of_concreteNoEarlyTripleEquality
    (concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
      H E)

/-- Direct construction-interface wrapper for `K_{2,3}` obstructions using
the unit-distance finite local exclusions. -/
def constructionNoEarlyTriples_of_K23Obstruction_and_unitDistanceConfig
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data) :
    M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples localLabels :=
  constructionNoEarlyTriples_of_K23Obstruction_and_finiteLocalExclusions
    H (finiteLocalExclusionPackage_of_unitDistanceConfig C)

/-! ## Late-triple-facing K23 obstruction wrappers -/

/-- A `K_{2,3}` obstruction plus finite local exclusions supplies the
abstract no-early predicate consumed by the late-triples bridge. -/
theorem noEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
    {P : BrokenLatticePredicates G 8}
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8NoEarlyTripleEquality P :=
  (concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
    H E).toNoEarlyTripleEquality

/-- A `K_{2,3}` obstruction plus finite local exclusions supplies the raw
Lemma 9 late-triples predicate. -/
theorem brokenLatticeLateTriples_of_K23Obstruction_and_finiteLocalExclusions
    {P : BrokenLatticePredicates G 8}
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8BrokenLatticeLateTriples P :=
  (concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
    H E).toBrokenLatticeLateTriples

/-- K23 obstruction data and finite local exclusions as the pipeline
no-early package. -/
def pipelineNoEarlyTriples_of_K23Obstruction_and_finiteLocalExclusions
    (P : M8HonestLocalPredicates G)
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs P.data)
    (E : FiniteLocalExclusionPackage G) :
    M8LateTriplesFromNoEarly.M8PipelineNoEarlyTriples P where
  noEarlyTripleEquality :=
    noEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions H E

/-- K23 obstruction data and finite local exclusions as the pipeline
late-triples field. -/
def pipelineLateTriplesField_of_K23Obstruction_and_finiteLocalExclusions
    (P : M8HonestLocalPredicates G)
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs P.data)
    (E : FiniteLocalExclusionPackage G) :
    M8PipelineClosure.M8LateTriplesField P :=
  (pipelineNoEarlyTriples_of_K23Obstruction_and_finiteLocalExclusions
    P H E).toM8LateTriplesField

/-- K23 obstruction data and finite local exclusions as the honest
late-triples predicate. -/
theorem honestLateTriples_of_K23Obstruction_and_finiteLocalExclusions
    (P : M8HonestLocalPredicates G)
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs P.data)
    (E : FiniteLocalExclusionPackage G) :
    P.LateTriples :=
  (pipelineNoEarlyTriples_of_K23Obstruction_and_finiteLocalExclusions
    P H E).toHonestLateTriples

/-- K23 obstruction data and finite local exclusions as the construction
late-triples field. -/
def constructionLateTriples_of_K23Obstruction_and_finiteLocalExclusions
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (E : FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C)) :
    M8ConstructionInterface.M8LateTriples localLabels :=
  (constructionNoEarlyTriples_of_K23Obstruction_and_finiteLocalExclusions
    H E).toM8LateTriples

/-- Minimal-failure finite local exclusions route a `K_{2,3}` obstruction into
the concrete no-early package. -/
def concreteNoEarlyTripleEquality_of_K23Obstruction_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {P : BrokenLatticePredicates (GraphBridge.unitDistanceLocalGraph C) 8}
    (H : M8ConcreteK23ObstructionInputs P)
    (hmin : IsMinimalClearedFailure C)
    (hred : K23DegreeReducible C) :
    M8ConcreteNoEarlyTripleEquality P :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
    H (finiteLocalExclusionPackage_of_minimalFailure_and_K23DegreeReducible
      hmin hred)

/-- Minimal-failure finite local exclusions route a `K_{2,3}` obstruction into
the raw late-triples predicate. -/
theorem brokenLatticeLateTriples_of_K23Obstruction_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {P : BrokenLatticePredicates (GraphBridge.unitDistanceLocalGraph C) 8}
    (H : M8ConcreteK23ObstructionInputs P)
    (hmin : IsMinimalClearedFailure C)
    (hred : K23DegreeReducible C) :
    M8BrokenLatticeLateTriples P :=
  (concreteNoEarlyTripleEquality_of_K23Obstruction_minimalFailure
    H hmin hred).toBrokenLatticeLateTriples

/-! ## Packaged K23 obstruction plus arc-angle data -/

/-- One package containing the current K23 obstruction route, finite local
exclusions, and arc/angle data. -/
structure M8ConcreteK23ArcAngleObstructionData
    (P : M8HonestLocalPredicates G) [Fintype V] [DecidableEq V] where
  k23Obstruction : M8ConcreteK23ObstructionInputs P.data
  finiteLocalExclusions : FiniteLocalExclusionPackage G
  arcAngleData : M8TurnBoundsFromArc.M8ArcAngleData P

namespace M8ConcreteK23ArcAngleObstructionData

variable {P : M8HonestLocalPredicates G} [Fintype V] [DecidableEq V]

/-- The packaged data supplies the concrete no-early package. -/
def toConcreteNoEarlyTripleEquality
    (D : M8ConcreteK23ArcAngleObstructionData P) :
    M8ConcreteNoEarlyTripleEquality P.data :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
    D.k23Obstruction D.finiteLocalExclusions

/-- The packaged data supplies the abstract no-early predicate. -/
theorem toNoEarlyTripleEquality
    (D : M8ConcreteK23ArcAngleObstructionData P) :
    M8NoEarlyTripleEquality P.data :=
  D.toConcreteNoEarlyTripleEquality.toNoEarlyTripleEquality

/-- The packaged data supplies Lemma 9-style early-obstruction inputs. -/
def toEarlyTripleObstructionInputs
    (D : M8ConcreteK23ArcAngleObstructionData P) :
    M8EarlyTripleObstructionInputs P.data :=
  earlyTripleObstructionInputs_of_K23Obstruction
    D.k23Obstruction D.finiteLocalExclusions.noK23

/-- The packaged data supplies the raw late-triples predicate. -/
theorem lateTriples
    (D : M8ConcreteK23ArcAngleObstructionData P) :
    P.LateTriples :=
  D.toConcreteNoEarlyTripleEquality.toBrokenLatticeLateTriples

/-- The packaged data supplies the pipeline no-early package. -/
def toPipelineNoEarlyTriples
    (D : M8ConcreteK23ArcAngleObstructionData P) :
    M8LateTriplesFromNoEarly.M8PipelineNoEarlyTriples P where
  noEarlyTripleEquality := D.toNoEarlyTripleEquality

/-- The packaged data supplies the pipeline late-triples field. -/
def toPipelineLateTriplesField
    (D : M8ConcreteK23ArcAngleObstructionData P) :
    M8PipelineClosure.M8LateTriplesField P :=
  D.toPipelineNoEarlyTriples.toM8LateTriplesField

/-- The packaged data supplies the no-early-plus-turn contradiction package. -/
def toNoEarlyTurnData
    (D : M8ConcreteK23ArcAngleObstructionData P) :
    M8LateTriplesConcrete.M8NoEarlyTurnData P where
  noEarlyTripleEquality := D.toNoEarlyTripleEquality
  arcAngleData := D.arcAngleData

/-- The packaged K23 obstruction, finite local exclusions, and arc/angle data
close the local finite `m = 8` contradiction. -/
theorem contradiction
    (D : M8ConcreteK23ArcAngleObstructionData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  D.toNoEarlyTurnData.contradiction

end M8ConcreteK23ArcAngleObstructionData

/-- Unit-distance finite local exclusions package K23 obstruction and
arc/angle data directly. -/
def k23ArcAngleObstructionData_of_unitDistanceConfig
    {n : Nat} {C : _root_.UDConfig n}
    {P : M8HonestLocalPredicates (GraphBridge.unitDistanceLocalGraph C)}
    (H : M8ConcreteK23ObstructionInputs P.data)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P) :
    M8ConcreteK23ArcAngleObstructionData P where
  k23Obstruction := H
  finiteLocalExclusions := finiteLocalExclusionPackage_of_unitDistanceConfig C
  arcAngleData := D

/-- Minimal-failure finite local exclusions package K23 obstruction and
arc/angle data directly. -/
def k23ArcAngleObstructionData_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {P : M8HonestLocalPredicates (GraphBridge.unitDistanceLocalGraph C)}
    (H : M8ConcreteK23ObstructionInputs P.data)
    (hmin : IsMinimalClearedFailure C)
    (hred : K23DegreeReducible C)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P) :
    M8ConcreteK23ArcAngleObstructionData P where
  k23Obstruction := H
  finiteLocalExclusions :=
    finiteLocalExclusionPackage_of_minimalFailure_and_K23DegreeReducible
      hmin hred
  arcAngleData := D

/-! ## Packaged K23 obstruction plus turn/window data -/

/-- One fixed `m = 8` construction package where the no-early field is
derived from a `K_{2,3}` obstruction and finite local exclusions.

This is the pipeline-facing version of the K23 route: callers provide the
same local labels, nonconcave-arc turn data, and window-containment data as in
`M8TurnWindowNoEarlyFinal`, but the no-early triple package is constructed
here from the actual local obstruction route. -/
structure M8ConcreteK23TurnWindowObstructionData {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localLabels : M8ConstructionInterface.M8LocalLabels C
  arc : M8TurnBoundsFromArc.NonconcaveArcTurnData
  k23Obstruction : M8ConcreteK23ObstructionInputs localLabels.predicates.data
  finiteLocalExclusions :
    FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C)
  windowContainment :
    M8WindowGeometryFromContainment.M8WindowContainment
      localLabels arc.toM8TurnBounds

namespace M8ConcreteK23TurnWindowObstructionData

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The K23 obstruction and finite local exclusions supply the concrete
five-start no-early package. -/
def noEarlyTriples
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8ConcreteNoEarlyTripleEquality D.localLabels.predicates.data :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
    D.k23Obstruction D.finiteLocalExclusions

/-- The same derived no-early fact as the raw abstract predicate consumed by
the late-triples bridge. -/
theorem noEarlyTripleEquality
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8NoEarlyTripleEquality D.localLabels.predicates.data :=
  D.noEarlyTriples.toNoEarlyTripleEquality

/-- The derived no-early fact packaged for the construction interface. -/
def constructionNoEarlyTriples
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples D.localLabels :=
  constructionNoEarlyTriples_of_K23Obstruction_and_finiteLocalExclusions
    D.k23Obstruction D.finiteLocalExclusions

/-- The derived no-early fact packaged for the pipeline closure. -/
def pipelineNoEarlyTriples
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8LateTriplesFromNoEarly.M8PipelineNoEarlyTriples
      D.localLabels.predicates :=
  pipelineNoEarlyTriples_of_K23Obstruction_and_finiteLocalExclusions
    D.localLabels.predicates D.k23Obstruction D.finiteLocalExclusions

/-- K23 obstruction data and finite local exclusions produce the
construction-level late-triples field. -/
def lateTriples
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8ConstructionInterface.M8LateTriples D.localLabels :=
  D.constructionNoEarlyTriples.toM8LateTriples

/-- K23 obstruction data and finite local exclusions produce the honest
late-triples predicate. -/
theorem honestLateTriples
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    D.localLabels.predicates.LateTriples :=
  D.pipelineNoEarlyTriples.toHonestLateTriples

/-- K23 obstruction data and finite local exclusions produce the separated
pipeline late-triples field. -/
def pipelineLateTriplesField
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8PipelineClosure.M8LateTriplesField D.localLabels.predicates :=
  D.pipelineNoEarlyTriples.toM8LateTriplesField

/-- Forget the K23 route after deriving no-early triples, producing the
turn/window/no-early package used by the current M8 closure. -/
def toTurnWindowNoEarlyPackage
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin where
  localLabels := D.localLabels
  arc := D.arc
  noEarlyTriples := D.noEarlyTriples
  windowContainment := D.windowContainment

/-- The K23 route supplies the strongest current pipeline gate: window
geometry plus no-early triples. -/
def toM8WindowNoEarlyConstructionFields
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8PipelineClosure.M8WindowNoEarlyConstructionFields C hmin :=
  D.toTurnWindowNoEarlyPackage.toM8WindowNoEarlyConstructionFields

/-- The K23 route supplies direct E22/E23 plus no-early construction fields. -/
def toM8E22E23NoEarlyConstructionFields
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8PipelineClosure.M8E22E23NoEarlyConstructionFields C hmin :=
  D.toTurnWindowNoEarlyPackage.toM8E22E23NoEarlyConstructionFields

/-- The K23 route supplies separated construction fields, with late triples
derived from the obstruction rather than assumed separately. -/
def toM8SeparatedConstructionFields
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  D.toTurnWindowNoEarlyPackage.toM8SeparatedConstructionFields

/-- The K23 route supplies clean construction-interface data. -/
def toM8ConstructionData
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8ConstructionInterface.M8ConstructionData C hmin :=
  D.toTurnWindowNoEarlyPackage.toM8ConstructionData

/-- A fixed minimal cleared failure equipped with the K23 obstruction route,
finite local exclusions, nonconcave-arc turn data, and window containment is
contradictory. -/
theorem contradiction
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    False :=
  D.toTurnWindowNoEarlyPackage.contradiction

end M8ConcreteK23TurnWindowObstructionData

/-- Unit-distance finite local exclusions package the K23 obstruction and
turn/window data directly. -/
def k23TurnWindowObstructionData_of_unitDistanceConfig
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8ConcreteK23TurnWindowObstructionData C hmin where
  localLabels := localLabels
  arc := A
  k23Obstruction := H
  finiteLocalExclusions := finiteLocalExclusionPackage_of_unitDistanceConfig C
  windowContainment := W

/-- Minimal-failure finite local exclusions package the K23 obstruction and
turn/window data directly once the K23 degree-reduction rule is available. -/
def k23TurnWindowObstructionData_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (hred : K23DegreeReducible C)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8ConcreteK23TurnWindowObstructionData C hmin where
  localLabels := localLabels
  arc := A
  k23Obstruction := H
  finiteLocalExclusions :=
    finiteLocalExclusionPackage_of_minimalFailure_and_K23DegreeReducible
      hmin hred
  windowContainment := W

/-! ## Direct turn/window composition from K23 obstruction data -/

/-- Direct composition theorem: K23 obstruction data, finite local exclusions,
nonconcave-arc turn data, and window containment assemble the exact
turn/window/no-early package consumed by `M8TurnWindowNoEarlyFinal`. -/
def turnWindowNoEarlyPackage_of_K23Obstruction_and_finiteLocalExclusions
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (E : FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C))
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  ({ localLabels := localLabels
     arc := A
     k23Obstruction := H
     finiteLocalExclusions := E
     windowContainment := W } :
    M8ConcreteK23TurnWindowObstructionData C hmin).toTurnWindowNoEarlyPackage

/-- Direct unit-distance specialization of the K23 obstruction route into the
turn/window/no-early package. -/
def turnWindowNoEarlyPackage_of_K23Obstruction_and_unitDistanceConfig
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  turnWindowNoEarlyPackage_of_K23Obstruction_and_finiteLocalExclusions
    A H (finiteLocalExclusionPackage_of_unitDistanceConfig C) W

/-- Direct minimal-failure specialization of the K23 obstruction route into the
turn/window/no-early package, using the supplied K23 degree-reduction rule only
to obtain finite local exclusions. -/
def turnWindowNoEarlyPackage_of_K23Obstruction_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (hred : K23DegreeReducible C)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  (k23TurnWindowObstructionData_of_minimalFailure
    (C := C) (hmin := hmin) (localLabels := localLabels) A H hred W).toTurnWindowNoEarlyPackage

/-- The direct finite-local-exclusion K23 route supplies the strongest current
window/no-early construction fields. -/
def windowNoEarlyConstructionFields_of_K23Obstruction_and_finiteLocalExclusions
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (E : FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C))
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8PipelineClosure.M8WindowNoEarlyConstructionFields C hmin :=
  (turnWindowNoEarlyPackage_of_K23Obstruction_and_finiteLocalExclusions
    A H E W).toM8WindowNoEarlyConstructionFields

/-- The direct finite-local-exclusion K23 route supplies separated construction
fields, with late triples derived from no-early triples. -/
def separatedConstructionFields_of_K23Obstruction_and_finiteLocalExclusions
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (E : FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C))
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  (turnWindowNoEarlyPackage_of_K23Obstruction_and_finiteLocalExclusions
    A H E W).toM8SeparatedConstructionFields

/-- The direct finite-local-exclusion K23 route supplies clean construction
interface data. -/
def constructionData_of_K23Obstruction_and_finiteLocalExclusions
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (E : FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C))
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8ConstructionInterface.M8ConstructionData C hmin :=
  (turnWindowNoEarlyPackage_of_K23Obstruction_and_finiteLocalExclusions
    A H E W).toM8ConstructionData

/-- K23 obstruction data, finite local exclusions, turn data, and window
containment contradict a fixed minimal cleared failure. -/
theorem contradiction_of_K23Obstruction_finiteLocalExclusions_and_turnWindow
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (E : FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C))
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    False :=
  (turnWindowNoEarlyPackage_of_K23Obstruction_and_finiteLocalExclusions
    (hmin := hmin) A H E W).contradiction

/-- Unit-distance finite local exclusions close the direct K23 turn/window
route for a fixed minimal cleared failure. -/
theorem contradiction_of_K23Obstruction_unitDistanceConfig_and_turnWindow
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    False :=
  contradiction_of_K23Obstruction_finiteLocalExclusions_and_turnWindow
    (hmin := hmin) A H (finiteLocalExclusionPackage_of_unitDistanceConfig C) W

/-- A K23 degree-reduction rule closes the direct K23 turn/window route for a
fixed minimal cleared failure. -/
theorem contradiction_of_K23Obstruction_minimalFailure_and_turnWindow
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (hred : K23DegreeReducible C)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    False :=
  (turnWindowNoEarlyPackage_of_K23Obstruction_minimalFailure
    (hmin := hmin) A H hred W).contradiction

/-! ## Uniform K23 turn/window eliminator -/

/-- Uniform M8 eliminator whose no-early/late-triples field is derived from
K23 obstruction data and finite local exclusions for each minimal failure. -/
def MinimalFailureM8K23TurnWindowEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (M8ConcreteK23TurnWindowObstructionData C hmin)

/-- The K23 turn/window eliminator supplies the exact
turn/window/no-early package family used by `M8TurnWindowNoEarlyFinal`. -/
theorem turnWindowNoEarlyEliminator_of_K23TurnWindowEliminator
    (hbuild : MinimalFailureM8K23TurnWindowEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Nonempty
          (M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin) := by
  intro n C hmin
  rcases hbuild C hmin with ⟨D⟩
  exact Nonempty.intro D.toTurnWindowNoEarlyPackage

/-- The K23 turn/window eliminator supplies the window/no-early eliminator
used by `M8PipelineClosure`. -/
theorem windowNoEarlyConstructionEliminator_of_K23TurnWindowEliminator
    (hbuild : MinimalFailureM8K23TurnWindowEliminator) :
    M8PipelineClosure.MinimalFailureM8WindowNoEarlyConstructionEliminator := by
  intro n C hmin
  rcases hbuild C hmin with ⟨D⟩
  exact Nonempty.intro D.toM8WindowNoEarlyConstructionFields

/-- The K23 turn/window eliminator also supplies the separated-field
eliminator, with late triples derived from the obstruction route. -/
theorem separatedConstructionEliminator_of_K23TurnWindowEliminator
    (hbuild : MinimalFailureM8K23TurnWindowEliminator) :
    M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator := by
  intro n C hmin
  rcases hbuild C hmin with ⟨D⟩
  exact Nonempty.intro D.toM8SeparatedConstructionFields

/-- Uniform K23 obstruction, finite local exclusions, turn data, and window
containment rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure_of_K23TurnWindowEliminator
    (hbuild : MinimalFailureM8K23TurnWindowEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  exact M8PipelineClosure.no_minimalClearedFailure_of_windowNoEarlyConstructionEliminator
    (windowNoEarlyConstructionEliminator_of_K23TurnWindowEliminator hbuild)

/-! ## Final contradiction wrappers -/

/-- Explicit start contradictions plus arc/angle data close the local finite
`m = 8` contradiction. -/
theorem contradiction_of_falseStartImplications_and_arcAngleData
    (P : M8HonestLocalPredicates G)
    (H : M8ConcreteFalseStartImplications P.data)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  contradiction_of_concreteNoEarlyTripleEquality_and_arcAngleData
    P H.toConcreteNoEarlyTripleEquality D

/-- Indexed finite obstructions plus arc/angle data close the local finite
`m = 8` contradiction. -/
theorem contradiction_of_indexedObstructionInputs_and_arcAngleData
    (P : M8HonestLocalPredicates G)
    (H : M8ConcreteIndexedObstructionInputs P.data)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  contradiction_of_concreteNoEarlyTripleEquality_and_arcAngleData
    P H.toConcreteNoEarlyTripleEquality D

/-- A single forbidden local pattern plus arc/angle data closes the local
finite `m = 8` contradiction. -/
theorem contradiction_of_forbiddenObstruction_and_arcAngleData
    (P : M8HonestLocalPredicates G) {forbidden : Prop}
    (H : M8ConcreteForbiddenObstructionInputs P.data forbidden)
    (hforbidden : Not forbidden)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  contradiction_of_concreteNoEarlyTripleEquality_and_arcAngleData
    P (H.toConcreteNoEarlyTripleEquality hforbidden) D

/-- A `K_{2,3}` obstruction plus an explicit no-`K_{2,3}` local exclusion and
arc/angle data close the local finite `m = 8` contradiction. -/
theorem contradiction_of_K23Obstruction_and_arcAngleData
    (P : M8HonestLocalPredicates G)
    (H : M8ConcreteK23ObstructionInputs P.data)
    (hnoK23 : Not (HasK23 G))
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  contradiction_of_forbiddenObstruction_and_arcAngleData
    P H hnoK23 D

/-- A `K_{2,3}` obstruction, the finite local-exclusion package, and
arc/angle data close the local finite `m = 8` contradiction. -/
theorem contradiction_of_K23Obstruction_finiteLocalExclusions_and_arcAngleData
    (P : M8HonestLocalPredicates G)
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs P.data)
    (E : FiniteLocalExclusionPackage G)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  contradiction_of_K23Obstruction_and_arcAngleData
    P H E.noK23 D

/-- Packaged `K_{2,3}` obstruction data, finite local exclusions, and
arc/angle data close the local finite `m = 8` contradiction. -/
theorem contradiction_of_K23ArcAngleObstructionData
    (P : M8HonestLocalPredicates G)
    [Fintype V] [DecidableEq V]
    (D : M8ConcreteK23ArcAngleObstructionData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  D.contradiction

/-- A `K_{2,3}` obstruction and the unit-distance finite local exclusions
close the local finite `m = 8` contradiction. -/
theorem contradiction_of_K23Obstruction_unitDistanceConfig_and_arcAngleData
    {n : Nat} {C : _root_.UDConfig n}
    (P : M8HonestLocalPredicates (GraphBridge.unitDistanceLocalGraph C))
    (H : M8ConcreteK23ObstructionInputs P.data)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  contradiction_of_K23Obstruction_finiteLocalExclusions_and_arcAngleData
    P H (finiteLocalExclusionPackage_of_unitDistanceConfig C) D

/-- A `K_{2,3}` obstruction, minimal-failure local exclusions from a
degree-reduction rule, and arc/angle data close the local finite `m = 8`
contradiction. -/
theorem contradiction_of_K23Obstruction_minimalFailure_and_arcAngleData
    {n : Nat} {C : _root_.UDConfig n}
    (P : M8HonestLocalPredicates (GraphBridge.unitDistanceLocalGraph C))
    (H : M8ConcreteK23ObstructionInputs P.data)
    (hmin : IsMinimalClearedFailure C)
    (hred : K23DegreeReducible C)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  (k23ArcAngleObstructionData_of_minimalFailure H hmin hred D).contradiction

end NoEarlyTripleObstructionConcrete
end Swanepoel
end ErdosProblems1066

end
