import ErdosProblems1066.Swanepoel.Lemma10Bridge
import ErdosProblems1066.Swanepoel.M8RefinedInputConcrete
import ErdosProblems1066.Swanepoel.MinimalFailureConcreteDataMatrix
import ErdosProblems1066.Swanepoel.MinimalFailureToTargetConcrete
import ErdosProblems1066.Swanepoel.NoEarlyTripleObstructionConcrete

set_option autoImplicit false

/-!
# Concrete Lemma 9 no-start adapters

This file isolates the no-start/LateTriples side of the current
minimal-failure route.  It starts from exactly five explicit `no_start`
fields, routes them through the existing no-early obstruction package, and
exposes the construction-interface and LateTriples adapters used downstream.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9NoStartConcrete

open LateTriplesInterface
open Lemma10Bridge
open LocalConfigurations
open M8ConstructionInterface
open M8LateTriplesFromNoEarly
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NoEarlyTripleObstructionConcrete

universe u

noncomputable section

variable {V : Type u} {G : LocalGraph V}

/-! ## Predicate-level explicit no-start package -/

/-- The exact five no-start fields for one `m = 8` broken-lattice predicate
package. -/
structure M8ExplicitNoStartFields
    (P : BrokenLatticePredicates G 8) : Prop where
  no_start1 : Not (P.tripleEquality start1)
  no_start2 : Not (P.tripleEquality start2)
  no_start3 : Not (P.tripleEquality start3)
  no_start4 : Not (P.tripleEquality start4)
  no_start5 : Not (P.tripleEquality start5)

namespace M8ExplicitNoStartFields

variable {P : BrokenLatticePredicates G 8}

/-- View the explicit no-start fields as the false-start obstruction package.
-/
def toFalseStartImplications
    (H : M8ExplicitNoStartFields P) :
    M8ConcreteFalseStartImplications P where
  false_start1 := H.no_start1
  false_start2 := H.no_start2
  false_start3 := H.no_start3
  false_start4 := H.no_start4
  false_start5 := H.no_start5

/-- View the explicit no-start fields as concrete no-early triples. -/
def toConcreteNoEarlyTripleEquality
    (H : M8ExplicitNoStartFields P) :
    M8ConcreteNoEarlyTripleEquality P :=
  H.toFalseStartImplications.toConcreteNoEarlyTripleEquality

/-- View the explicit no-start fields as the abstract no-early predicate. -/
theorem toNoEarlyTripleEquality
    (H : M8ExplicitNoStartFields P) :
    M8NoEarlyTripleEquality P :=
  H.toConcreteNoEarlyTripleEquality.toNoEarlyTripleEquality

/-- The explicit no-start fields imply the raw Lemma 9 late-triples
predicate. -/
theorem toBrokenLatticeLateTriples
    (H : M8ExplicitNoStartFields P) :
    M8BrokenLatticeLateTriples P :=
  H.toConcreteNoEarlyTripleEquality.toBrokenLatticeLateTriples

@[simp]
theorem toFalseStartImplications_false_start1
    (H : M8ExplicitNoStartFields P) :
    H.toFalseStartImplications.false_start1 = H.no_start1 :=
  rfl

@[simp]
theorem toFalseStartImplications_false_start2
    (H : M8ExplicitNoStartFields P) :
    H.toFalseStartImplications.false_start2 = H.no_start2 :=
  rfl

@[simp]
theorem toFalseStartImplications_false_start3
    (H : M8ExplicitNoStartFields P) :
    H.toFalseStartImplications.false_start3 = H.no_start3 :=
  rfl

@[simp]
theorem toFalseStartImplications_false_start4
    (H : M8ExplicitNoStartFields P) :
    H.toFalseStartImplications.false_start4 = H.no_start4 :=
  rfl

@[simp]
theorem toFalseStartImplications_false_start5
    (H : M8ExplicitNoStartFields P) :
    H.toFalseStartImplications.false_start5 = H.no_start5 :=
  rfl

@[simp]
theorem toConcreteNoEarlyTripleEquality_no_start1
    (H : M8ExplicitNoStartFields P) :
    H.toConcreteNoEarlyTripleEquality.no_start1 = H.no_start1 :=
  rfl

@[simp]
theorem toConcreteNoEarlyTripleEquality_no_start2
    (H : M8ExplicitNoStartFields P) :
    H.toConcreteNoEarlyTripleEquality.no_start2 = H.no_start2 :=
  rfl

@[simp]
theorem toConcreteNoEarlyTripleEquality_no_start3
    (H : M8ExplicitNoStartFields P) :
    H.toConcreteNoEarlyTripleEquality.no_start3 = H.no_start3 :=
  rfl

@[simp]
theorem toConcreteNoEarlyTripleEquality_no_start4
    (H : M8ExplicitNoStartFields P) :
    H.toConcreteNoEarlyTripleEquality.no_start4 = H.no_start4 :=
  rfl

@[simp]
theorem toConcreteNoEarlyTripleEquality_no_start5
    (H : M8ExplicitNoStartFields P) :
    H.toConcreteNoEarlyTripleEquality.no_start5 = H.no_start5 :=
  rfl

end M8ExplicitNoStartFields

/-! ## Construction-label adapters -/

/-- The same five no-start fields, attached to construction local labels. -/
structure M8ConstructionExplicitNoStartFields {n : Nat}
    {C : _root_.UDConfig n} (localLabels : M8LocalLabels C) : Prop where
  no_start1 :
    Not (localLabels.predicates.data.tripleEquality start1)
  no_start2 :
    Not (localLabels.predicates.data.tripleEquality start2)
  no_start3 :
    Not (localLabels.predicates.data.tripleEquality start3)
  no_start4 :
    Not (localLabels.predicates.data.tripleEquality start4)
  no_start5 :
    Not (localLabels.predicates.data.tripleEquality start5)

namespace M8ConstructionExplicitNoStartFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}

/-- Forget construction labels to the predicate-level explicit no-start
package. -/
def toExplicitNoStartFields
    (H : M8ConstructionExplicitNoStartFields localLabels) :
    M8ExplicitNoStartFields localLabels.predicates.data where
  no_start1 := H.no_start1
  no_start2 := H.no_start2
  no_start3 := H.no_start3
  no_start4 := H.no_start4
  no_start5 := H.no_start5

/-- Concrete no-early triples from the five explicit no-start fields. -/
def toConcreteNoEarlyTripleEquality
    (H : M8ConstructionExplicitNoStartFields localLabels) :
    M8ConcreteNoEarlyTripleEquality localLabels.predicates.data :=
  H.toExplicitNoStartFields.toConcreteNoEarlyTripleEquality

/-- Exact adapter to the construction no-early package. -/
def constructionNoEarlyTriples
    (H : M8ConstructionExplicitNoStartFields localLabels) :
    M8ConstructionNoEarlyTriples localLabels :=
  constructionNoEarlyTriples_of_concreteNoEarlyTripleEquality
    H.toConcreteNoEarlyTripleEquality

/-- Exact adapter to construction-interface late triples. -/
def lateTriples
    (H : M8ConstructionExplicitNoStartFields localLabels) :
    M8LateTriples localLabels :=
  H.constructionNoEarlyTriples.toM8LateTriples

/-- Exact adapter to the honest predicate-level LateTriples field. -/
theorem honestLateTriples
    (H : M8ConstructionExplicitNoStartFields localLabels) :
    localLabels.predicates.LateTriples :=
  H.constructionNoEarlyTriples.toHonestLateTriples

@[simp]
theorem constructionNoEarlyTriples_noEarlyTripleEquality
    (H : M8ConstructionExplicitNoStartFields localLabels) :
    H.constructionNoEarlyTriples.noEarlyTripleEquality =
      H.toConcreteNoEarlyTripleEquality.toNoEarlyTripleEquality :=
  rfl

@[simp]
theorem lateTriples_labelLateTriples
    (H : M8ConstructionExplicitNoStartFields localLabels) :
    H.lateTriples.labelLateTriples =
      H.constructionNoEarlyTriples.toLabelLateTriples :=
  rfl

end M8ConstructionExplicitNoStartFields

/-! ## Recovering no-start fields from checked late triples -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}

/-- Recover the five explicit no-start fields from a construction no-early
package. -/
def noStartFields_of_constructionNoEarlyTriples
    (H : M8ConstructionNoEarlyTriples localLabels) :
    M8ConstructionExplicitNoStartFields localLabels where
  no_start1 :=
    H.toNoEarlyTripleEquality start1 (by simp [M8TripleStartEarly])
  no_start2 :=
    H.toNoEarlyTripleEquality start2 (by simp [M8TripleStartEarly])
  no_start3 :=
    H.toNoEarlyTripleEquality start3 (by simp [M8TripleStartEarly])
  no_start4 :=
    H.toNoEarlyTripleEquality start4 (by simp [M8TripleStartEarly])
  no_start5 :=
    H.toNoEarlyTripleEquality start5 (by simp [M8TripleStartEarly])

/-- The construction no-early package and the five explicit no-start fields
are equivalent finite data. -/
theorem constructionNoEarlyTriples_iff_noStartFields :
    M8ConstructionNoEarlyTriples localLabels <->
      M8ConstructionExplicitNoStartFields localLabels := by
  constructor
  case mp =>
    intro H
    exact noStartFields_of_constructionNoEarlyTriples H
  case mpr =>
    intro H
    exact H.constructionNoEarlyTriples

/-- Recover the five explicit no-start fields from construction-interface late
triples.  This is the finite `m = 8` arithmetic behind the "late triples imply
no early starts" direction. -/
def noStartFields_of_lateTriples
    (H : M8LateTriples localLabels) :
    M8ConstructionExplicitNoStartFields localLabels where
  no_start1 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples
      H.toHonestLateTriples).not_start1
  no_start2 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples
      H.toHonestLateTriples).not_start2
  no_start3 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples
      H.toHonestLateTriples).not_start3
  no_start4 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples
      H.toHonestLateTriples).not_start4
  no_start5 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples
      H.toHonestLateTriples).not_start5

/-- Construction-interface late triples rebuild the construction no-early
package through the explicit no-start fields. -/
def constructionNoEarlyTriples_of_lateTriples
    (H : M8LateTriples localLabels) :
    M8ConstructionNoEarlyTriples localLabels :=
  (noStartFields_of_lateTriples H).constructionNoEarlyTriples

/-- Checked M8 construction data exposes the five explicit no-start fields
carried implicitly by its late-triples component. -/
def noStartFields_of_constructionData
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConstructionData C hmin) :
    M8ConstructionExplicitNoStartFields D.localLabels :=
  noStartFields_of_lateTriples D.lateTriples

/-- Checked M8 construction data rebuilds the no-early package through those
explicit no-start fields. -/
def constructionNoEarlyTriples_of_constructionData
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConstructionData C hmin) :
    M8ConstructionNoEarlyTriples D.localLabels :=
  (noStartFields_of_constructionData D).constructionNoEarlyTriples

/-- The late-triples component of checked M8 construction data can be routed
back through the explicit no-start package. -/
def lateTriples_of_constructionData_noStartFields
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConstructionData C hmin) :
    M8LateTriples D.localLabels :=
  (noStartFields_of_constructionData D).lateTriples

/-- Checked broken-lattice construction data exposes the five explicit
predicate-level no-start fields carried by its late-triples field. -/
def noStartFields_of_brokenLatticeConstructionData
    {hmin : IsMinimalClearedFailure C}
    (D : BrokenLatticeMinimalFailure.M8ConstructionData C hmin) :
    M8ExplicitNoStartFields D.predicates.data where
  no_start1 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples D.lateTriples).not_start1
  no_start2 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples D.lateTriples).not_start2
  no_start3 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples D.lateTriples).not_start3
  no_start4 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples D.lateTriples).not_start4
  no_start5 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples D.lateTriples).not_start5

/-- Checked broken-lattice construction data rebuilds the concrete no-early
package through its recovered no-start fields. -/
def concreteNoEarlyTripleEquality_of_brokenLatticeConstructionData
    {hmin : IsMinimalClearedFailure C}
    (D : BrokenLatticeMinimalFailure.M8ConstructionData C hmin) :
    M8ConcreteNoEarlyTripleEquality D.predicates.data :=
  (noStartFields_of_brokenLatticeConstructionData D).toConcreteNoEarlyTripleEquality

/-- The recovered no-start fields from checked broken-lattice construction
data route back to the late-triples predicate. -/
theorem lateTriples_of_brokenLatticeConstructionData_noStartFields
    {hmin : IsMinimalClearedFailure C}
    (D : BrokenLatticeMinimalFailure.M8ConstructionData C hmin) :
    D.predicates.LateTriples :=
  (noStartFields_of_brokenLatticeConstructionData D).toBrokenLatticeLateTriples

/-- The full broken-lattice minimal-failure interface package exposes the same
five predicate-level no-start fields. -/
def noStartFields_of_minimalFailureBrokenLatticeData
    (D : BrokenLatticeInterface.M8MinimalFailureBrokenLatticeData C) :
    M8ExplicitNoStartFields D.predicates.data where
  no_start1 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples D.lateTriples).not_start1
  no_start2 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples D.lateTriples).not_start2
  no_start3 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples D.lateTriples).not_start3
  no_start4 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples D.lateTriples).not_start4
  no_start5 :=
    (M8Lemma9FiveStartLateFacts.ofLateTriples D.lateTriples).not_start5

/-- The full broken-lattice minimal-failure interface package rebuilds the
concrete no-early package through its recovered no-start fields. -/
def concreteNoEarlyTripleEquality_of_minimalFailureBrokenLatticeData
    (D : BrokenLatticeInterface.M8MinimalFailureBrokenLatticeData C) :
    M8ConcreteNoEarlyTripleEquality D.predicates.data :=
  (noStartFields_of_minimalFailureBrokenLatticeData D).toConcreteNoEarlyTripleEquality

/-! ## Minimal-failure target-row adapters -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The five explicit no-start fields extracted from a target concrete row. -/
def toConstructionExplicitNoStartFields
    (D :
      MinimalFailureToTargetConcrete.MinimalFailureConcreteRow C hmin) :
    M8ConstructionExplicitNoStartFields D.labels.toM8LocalLabels where
  no_start1 := D.no_start1
  no_start2 := D.no_start2
  no_start3 := D.no_start3
  no_start4 := D.no_start4
  no_start5 := D.no_start5

/-- The target concrete row's construction no-early package is exactly the
adapter from its five explicit no-start fields. -/
theorem constructionNoEarlyTriples_eq_from_noStartFields
    (D :
      MinimalFailureToTargetConcrete.MinimalFailureConcreteRow C hmin) :
    D.constructionNoEarlyTriples =
      (toConstructionExplicitNoStartFields D).constructionNoEarlyTriples :=
  rfl

/-- The target concrete row supplies construction-interface late triples from
only its explicit no-start fields. -/
def lateTriplesFromNoStartFields
    (D :
      MinimalFailureToTargetConcrete.MinimalFailureConcreteRow C hmin) :
    M8LateTriples D.labels.toM8LocalLabels :=
  (toConstructionExplicitNoStartFields D).lateTriples

/-- The target concrete row supplies honest LateTriples from only its explicit
no-start fields. -/
theorem honestLateTriplesFromNoStartFields
    (D :
      MinimalFailureToTargetConcrete.MinimalFailureConcreteRow C hmin) :
    D.labels.toM8LocalLabels.predicates.LateTriples :=
  (toConstructionExplicitNoStartFields D).honestLateTriples

/-! ## Matrix/refined-row adapters -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Extract the explicit no-start fields from a derived matrix. -/
def concreteDerivedFieldMatrixNoStartFields
    (M :
      MinimalFailureConcreteDataMatrix.ConcreteDerivedFieldMatrix C hmin) :
    M8ConstructionExplicitNoStartFields M.localLabels where
  no_start1 := M.noEarlyTripleEquality.no_start1
  no_start2 := M.noEarlyTripleEquality.no_start2
  no_start3 := M.noEarlyTripleEquality.no_start3
  no_start4 := M.noEarlyTripleEquality.no_start4
  no_start5 := M.noEarlyTripleEquality.no_start5

/-- The no-early package of a matrix built from obligations is exactly rebuilt
from the five explicit no-start fields. -/
theorem ofObligations_noEarlyTriples_eq_from_noStartFields
    (P :
      MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations
        C hmin) :
    (MinimalFailureConcreteDataMatrix.ConcreteDerivedFieldMatrix.ofObligations
        P).noEarlyTriples =
      (concreteDerivedFieldMatrixNoStartFields
        (MinimalFailureConcreteDataMatrix.ConcreteDerivedFieldMatrix.ofObligations
          P)).constructionNoEarlyTriples :=
  rfl

/-- The late-triples field of a matrix built from obligations is exactly
rebuilt from the five explicit no-start fields. -/
theorem ofObligations_lateTriples_eq_from_noStartFields
    (P :
      MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations
        C hmin) :
    (MinimalFailureConcreteDataMatrix.ConcreteDerivedFieldMatrix.ofObligations
        P).lateTriples =
      (concreteDerivedFieldMatrixNoStartFields
        (MinimalFailureConcreteDataMatrix.ConcreteDerivedFieldMatrix.ofObligations
          P)).lateTriples :=
  rfl

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Extract the explicit no-start fields from a refined no-early row. -/
def concreteNoEarlyRefinedInputRowNoStartFields
    (R :
      M8RefinedInputConcrete.M8ConcreteNoEarlyRefinedInputRow C hmin) :
    M8ConstructionExplicitNoStartFields R.base.localLabels where
  no_start1 := R.noEarlyTripleEquality.no_start1
  no_start2 := R.noEarlyTripleEquality.no_start2
  no_start3 := R.noEarlyTripleEquality.no_start3
  no_start4 := R.noEarlyTripleEquality.no_start4
  no_start5 := R.noEarlyTripleEquality.no_start5

/-- The refined row's construction no-early package rebuilt from its five
explicit no-start fields. -/
def concreteNoEarlyRefinedInputRowConstructionNoEarlyTriples
    (R :
      M8RefinedInputConcrete.M8ConcreteNoEarlyRefinedInputRow C hmin) :
    M8ConstructionNoEarlyTriples R.base.localLabels :=
  (concreteNoEarlyRefinedInputRowNoStartFields R).constructionNoEarlyTriples

/-- The refined row's construction-interface LateTriples field rebuilt from
its five explicit no-start fields. -/
def concreteNoEarlyRefinedInputRowLateTriples
    (R :
      M8RefinedInputConcrete.M8ConcreteNoEarlyRefinedInputRow C hmin) :
    M8LateTriples R.base.localLabels :=
  (concreteNoEarlyRefinedInputRowNoStartFields R).lateTriples

/-- The refined row supplies honest LateTriples from only its five explicit
no-start fields. -/
theorem concreteNoEarlyRefinedInputRowHonestLateTriples
    (R :
      M8RefinedInputConcrete.M8ConcreteNoEarlyRefinedInputRow C hmin) :
    R.base.localLabels.predicates.LateTriples :=
  (concreteNoEarlyRefinedInputRowNoStartFields R).honestLateTriples

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Lemma 9 five-start late facts give the exact no-start package used by the
construction adapters. -/
def lemma9RefinedInputRowNoStartFields
    (R : M8RefinedInputConcrete.M8Lemma9RefinedInputRow C hmin) :
    M8ConstructionExplicitNoStartFields R.base.localLabels where
  no_start1 := R.noEarlyTripleEquality.no_start1
  no_start2 := R.noEarlyTripleEquality.no_start2
  no_start3 := R.noEarlyTripleEquality.no_start3
  no_start4 := R.noEarlyTripleEquality.no_start4
  no_start5 := R.noEarlyTripleEquality.no_start5

/-- Lemma 9 source rows supply construction-interface LateTriples through the
explicit no-start adapter. -/
def lemma9RefinedInputRowLateTriples
    (R : M8RefinedInputConcrete.M8Lemma9RefinedInputRow C hmin) :
    M8LateTriples R.base.localLabels :=
  (lemma9RefinedInputRowNoStartFields R).lateTriples

end

end Lemma9NoStartConcrete
end Swanepoel
end ErdosProblems1066
