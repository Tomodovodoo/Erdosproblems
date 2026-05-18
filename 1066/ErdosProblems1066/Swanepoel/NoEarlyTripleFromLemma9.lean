import ErdosProblems1066.Swanepoel.M8LateTriplesConcrete
import ErdosProblems1066.Swanepoel.NoEarlyTripleConcrete

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# No-early triples from Lemma 9-style late-triple facts

This module is a standalone bridge from Lemma 9-shaped inputs to the concrete
five-start no-early package used by the `m = 8` construction interfaces.

The paper-specific Lemma 9 content is still supplied as data: either a late
triple theorem, finite natural-index inputs, or an early-obstruction package.
The checked part here is the finite bookkeeping that turns those inputs into
`M8ConcreteNoEarlyTripleEquality` and then into
`M8ConstructionNoEarlyTriples`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyTripleFromLemma9

open LateTriplesInterface
open Lemma10Bridge
open LocalConfigurations
open M8ConstructionInterface
open M8LateTriplesFromNoEarly
open NoEarlyTripleConcrete

universe u

variable {V : Type u} {G : LocalGraph V}

/-! ## Five concrete starts from late-triple facts -/

/-- Lemma 9's late-triple conclusion restricted to the five concrete early
starts.  Each field is intentionally phrased as a late-start implication so
the impossible inequalities are checked in this file. -/
structure M8Lemma9FiveStartLateFacts
    (P : BrokenLatticePredicates G 8) : Prop where
  late_start1 : P.tripleEquality start1 -> 6 <= start1.1
  late_start2 : P.tripleEquality start2 -> 6 <= start2.1
  late_start3 : P.tripleEquality start3 -> 6 <= start3.1
  late_start4 : P.tripleEquality start4 -> 6 <= start4.1
  late_start5 : P.tripleEquality start5 -> 6 <= start5.1

namespace M8Lemma9FiveStartLateFacts

variable {P : BrokenLatticePredicates G 8}

/-- Full Lemma 9 late triples restrict to the five concrete early starts. -/
def ofLateTriples
    (hlate : M8BrokenLatticeLateTriples P) :
    M8Lemma9FiveStartLateFacts P where
  late_start1 := hlate start1
  late_start2 := hlate start2
  late_start3 := hlate start3
  late_start4 := hlate start4
  late_start5 := hlate start5

/-- Finite natural-index Lemma 9 inputs restrict to the five concrete early
starts. -/
def ofNatLateTripleInputs
    (H : M8NatLateTripleInputs P) :
    M8Lemma9FiveStartLateFacts P where
  late_start1 := H.late_of_tripleEquality
  late_start2 := H.late_of_tripleEquality
  late_start3 := H.late_of_tripleEquality
  late_start4 := H.late_of_tripleEquality
  late_start5 := H.late_of_tripleEquality

/-- The restricted Lemma 9 facts rule out triple equality at start `1`. -/
theorem not_start1
    (H : M8Lemma9FiveStartLateFacts P) :
    Not (P.tripleEquality start1) := by
  intro htriple
  have hlate : 6 <= (1 : Nat) := by
    simpa using H.late_start1 htriple
  omega

/-- The restricted Lemma 9 facts rule out triple equality at start `2`. -/
theorem not_start2
    (H : M8Lemma9FiveStartLateFacts P) :
    Not (P.tripleEquality start2) := by
  intro htriple
  have hlate : 6 <= (2 : Nat) := by
    simpa using H.late_start2 htriple
  omega

/-- The restricted Lemma 9 facts rule out triple equality at start `3`. -/
theorem not_start3
    (H : M8Lemma9FiveStartLateFacts P) :
    Not (P.tripleEquality start3) := by
  intro htriple
  have hlate : 6 <= (3 : Nat) := by
    simpa using H.late_start3 htriple
  omega

/-- The restricted Lemma 9 facts rule out triple equality at start `4`. -/
theorem not_start4
    (H : M8Lemma9FiveStartLateFacts P) :
    Not (P.tripleEquality start4) := by
  intro htriple
  have hlate : 6 <= (4 : Nat) := by
    simpa using H.late_start4 htriple
  omega

/-- The restricted Lemma 9 facts rule out triple equality at start `5`. -/
theorem not_start5
    (H : M8Lemma9FiveStartLateFacts P) :
    Not (P.tripleEquality start5) := by
  intro htriple
  have hlate : 6 <= (5 : Nat) := by
    simpa using H.late_start5 htriple
  omega

/-- Package the five impossible early starts as the concrete no-early-triple
input. -/
def toConcreteNoEarlyTripleEquality
    (H : M8Lemma9FiveStartLateFacts P) :
    M8ConcreteNoEarlyTripleEquality P where
  no_start1 := H.not_start1
  no_start2 := H.not_start2
  no_start3 := H.not_start3
  no_start4 := H.not_start4
  no_start5 := H.not_start5

/-- The five-start package also gives the abstract no-early predicate. -/
theorem toNoEarlyTripleEquality
    (H : M8Lemma9FiveStartLateFacts P) :
    M8NoEarlyTripleEquality P :=
  H.toConcreteNoEarlyTripleEquality.toNoEarlyTripleEquality

/-- The five-start package gives the raw late-triples predicate via the
no-early route. -/
theorem toBrokenLatticeLateTriples
    (H : M8Lemma9FiveStartLateFacts P) :
    M8BrokenLatticeLateTriples P :=
  H.toConcreteNoEarlyTripleEquality.toBrokenLatticeLateTriples

end M8Lemma9FiveStartLateFacts

/-! ## Direct concrete package constructors -/

/-- Lemma 9 late triples imply the concrete five-start no-early package. -/
def concreteNoEarlyTripleEquality_of_lateTriples
    {P : BrokenLatticePredicates G 8}
    (hlate : M8BrokenLatticeLateTriples P) :
    M8ConcreteNoEarlyTripleEquality P :=
  (M8Lemma9FiveStartLateFacts.ofLateTriples hlate).toConcreteNoEarlyTripleEquality

/-- Finite natural-index Lemma 9 inputs imply the concrete five-start
no-early package. -/
def concreteNoEarlyTripleEquality_of_natLateTripleInputs
    {P : BrokenLatticePredicates G 8}
    (H : M8NatLateTripleInputs P) :
    M8ConcreteNoEarlyTripleEquality P :=
  (M8Lemma9FiveStartLateFacts.ofNatLateTripleInputs H).toConcreteNoEarlyTripleEquality

/-- Early-obstruction Lemma 9 inputs imply the concrete five-start no-early
package. -/
def concreteNoEarlyTripleEquality_of_earlyTripleObstructionInputs
    {P : BrokenLatticePredicates G 8}
    (H : M8EarlyTripleObstructionInputs P) :
    M8ConcreteNoEarlyTripleEquality P where
  no_start1 := H.noEarlyTripleEquality start1 (by simp [M8TripleStartEarly])
  no_start2 := H.noEarlyTripleEquality start2 (by simp [M8TripleStartEarly])
  no_start3 := H.noEarlyTripleEquality start3 (by simp [M8TripleStartEarly])
  no_start4 := H.noEarlyTripleEquality start4 (by simp [M8TripleStartEarly])
  no_start5 := H.noEarlyTripleEquality start5 (by simp [M8TripleStartEarly])

/-! ## Construction-interface no-early packages -/

/-- Concrete five-start exclusions give the construction-interface no-early
package. -/
def constructionNoEarlyTriples_of_concreteNoEarlyTripleEquality
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8ConcreteNoEarlyTripleEquality localLabels.predicates.data) :
    M8ConstructionNoEarlyTriples localLabels where
  noEarlyTripleEquality := H.toNoEarlyTripleEquality

/-- Restricted Lemma 9 five-start late facts give the construction-interface
no-early package. -/
def constructionNoEarlyTriples_of_fiveStartLateFacts
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8Lemma9FiveStartLateFacts localLabels.predicates.data) :
    M8ConstructionNoEarlyTriples localLabels :=
  constructionNoEarlyTriples_of_concreteNoEarlyTripleEquality
    H.toConcreteNoEarlyTripleEquality

/-- Lemma 9 late triples give the construction-interface no-early package. -/
def constructionNoEarlyTriples_of_lateTriples
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (hlate : localLabels.predicates.LateTriples) :
    M8ConstructionNoEarlyTriples localLabels :=
  constructionNoEarlyTriples_of_fiveStartLateFacts
    (M8Lemma9FiveStartLateFacts.ofLateTriples hlate)

/-- Finite natural-index Lemma 9 inputs give the construction-interface
no-early package. -/
def constructionNoEarlyTriples_of_natLateTripleInputs
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8NatLateTripleInputs localLabels.predicates.data) :
    M8ConstructionNoEarlyTriples localLabels :=
  constructionNoEarlyTriples_of_fiveStartLateFacts
    (M8Lemma9FiveStartLateFacts.ofNatLateTripleInputs H)

/-- Early-obstruction Lemma 9 inputs give the construction-interface no-early
package. -/
def constructionNoEarlyTriples_of_earlyTripleObstructionInputs
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8EarlyTripleObstructionInputs localLabels.predicates.data) :
    M8ConstructionNoEarlyTriples localLabels :=
  constructionNoEarlyTriples_of_concreteNoEarlyTripleEquality
    (concreteNoEarlyTripleEquality_of_earlyTripleObstructionInputs H)

/-! ## Available contradictions -/

/-- A construction no-early package rules out the first concrete early start.
-/
theorem construction_not_start1
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8ConstructionNoEarlyTriples localLabels) :
    Not (localLabels.predicates.data.tripleEquality start1) :=
  H.toNoEarlyTripleEquality start1 (by simp [M8TripleStartEarly])

/-- A construction no-early package rules out the second concrete early start.
-/
theorem construction_not_start2
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8ConstructionNoEarlyTriples localLabels) :
    Not (localLabels.predicates.data.tripleEquality start2) :=
  H.toNoEarlyTripleEquality start2 (by simp [M8TripleStartEarly])

/-- A construction no-early package rules out the third concrete early start.
-/
theorem construction_not_start3
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8ConstructionNoEarlyTriples localLabels) :
    Not (localLabels.predicates.data.tripleEquality start3) :=
  H.toNoEarlyTripleEquality start3 (by simp [M8TripleStartEarly])

/-- A construction no-early package rules out the fourth concrete early start.
-/
theorem construction_not_start4
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8ConstructionNoEarlyTriples localLabels) :
    Not (localLabels.predicates.data.tripleEquality start4) :=
  H.toNoEarlyTripleEquality start4 (by simp [M8TripleStartEarly])

/-- A construction no-early package rules out the fifth concrete early start.
-/
theorem construction_not_start5
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8ConstructionNoEarlyTriples localLabels) :
    Not (localLabels.predicates.data.tripleEquality start5) :=
  H.toNoEarlyTripleEquality start5 (by simp [M8TripleStartEarly])

/-- Concrete no-early triples plus the arc/angle input close the local finite
`m = 8` contradiction. -/
theorem contradiction_of_concreteNoEarlyTripleEquality_and_arcAngleData
    (P : M8HonestLocalPredicates G)
    (H : M8ConcreteNoEarlyTripleEquality P.data)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  M8LateTriplesConcrete.contradiction_of_noEarlyTripleEquality_and_arcAngleData
    P H.toNoEarlyTripleEquality D

/-- Restricted five-start Lemma 9 late facts plus the arc/angle input close
the local finite `m = 8` contradiction. -/
theorem contradiction_of_fiveStartLateFacts_and_arcAngleData
    (P : M8HonestLocalPredicates G)
    (H : M8Lemma9FiveStartLateFacts P.data)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  contradiction_of_concreteNoEarlyTripleEquality_and_arcAngleData
    P H.toConcreteNoEarlyTripleEquality D

/-- Finite natural-index Lemma 9 inputs plus the arc/angle input close the
local finite `m = 8` contradiction. -/
theorem contradiction_of_natLateTripleInputs_and_arcAngleData
    (P : M8HonestLocalPredicates G)
    (H : M8NatLateTripleInputs P.data)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  contradiction_of_fiveStartLateFacts_and_arcAngleData
    P (M8Lemma9FiveStartLateFacts.ofNatLateTripleInputs H) D

/-- Early-obstruction Lemma 9 inputs plus the arc/angle input close the local
finite `m = 8` contradiction. -/
theorem contradiction_of_earlyTripleObstructionInputs_and_arcAngleData
    (P : M8HonestLocalPredicates G)
    (H : M8EarlyTripleObstructionInputs P.data)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  contradiction_of_concreteNoEarlyTripleEquality_and_arcAngleData
    P (concreteNoEarlyTripleEquality_of_earlyTripleObstructionInputs H) D

end NoEarlyTripleFromLemma9
end Swanepoel
end ErdosProblems1066

end
