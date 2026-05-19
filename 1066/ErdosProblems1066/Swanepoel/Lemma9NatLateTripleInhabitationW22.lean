import ErdosProblems1066.Swanepoel.Lemma9SourceInhabitationW21
import ErdosProblems1066.Swanepoel.Lemma9NatLateTripleProducerW19
import ErdosProblems1066.Swanepoel.Lemma9CoverageProducerW18
import ErdosProblems1066.Swanepoel.Lemma9CoverageConcreteW17
import ErdosProblems1066.Swanepoel.M8LateTriplesConcrete
import ErdosProblems1066.Swanepoel.M8LateTriplesFromNoEarly
import ErdosProblems1066.Swanepoel.NoEarlyTripleConcrete
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9
import ErdosProblems1066.Swanepoel.NoEarlyTripleObstructionConcrete

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W22 Lemma 9 natural late-triple inhabitation

This module continues the W21 Lemma 9 source-field reduction past the checked
coverage data.  The finite natural-index field is identified with the already
available no-early and late-triples packages, then lifted back through the W17,
W18, W19, and W20 row and family interfaces.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9NatLateTripleInhabitationW22

open LateTriplesInterface
open Lemma10Bridge
open Lemma6Lemma7AssemblyW13
open Lemma9CoverageConcreteW17
open Lemma9CoverageProducerW18
open Lemma9NatLateTripleProducerW19
open Lemma9ProducerFamilyW20
open Lemma9SourceInhabitationW21
open LocalConfigurations
open M8LateTriplesFromNoEarly
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NoEarlyTripleObstructionConcrete

universe u

variable {V : Type u} {G : LocalGraph V}
variable {P : BrokenLatticePredicates G 8}

/-! ## Finite natural inputs versus no-early and late triples -/

/-- Build the finite natural-index Lemma 9 package from raw late triples. -/
def natLateTripleInputs_of_lateTriples
    (hlate : M8BrokenLatticeLateTriples P) :
    M8NatLateTripleInputs P where
  tripleStartPredicate := fun a => 6 <= a
  predicate_of_tripleEquality := by
    intro a htriple
    exact hlate a htriple
  late_of_predicate := by
    intro a _ha1 _ha2 hlate
    exact hlate

/-- The finite natural-index Lemma 9 package is exactly the raw
late-triples predicate. -/
theorem nonempty_natLateTripleInputs_iff_lateTriples :
    Nonempty (M8NatLateTripleInputs P) <->
      M8BrokenLatticeLateTriples P := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact H.lateTriples
  case mpr =>
    intro hlate
    exact Nonempty.intro (natLateTripleInputs_of_lateTriples hlate)

/-- Build the finite natural-index Lemma 9 package from the abstract no-early
triple-equality predicate. -/
def natLateTripleInputs_of_noEarlyTripleEquality
    (hno : M8NoEarlyTripleEquality P) :
    M8NatLateTripleInputs P :=
  natLateTripleInputs_of_lateTriples
    (m8BrokenLatticeLateTriples_of_noEarlyTripleEquality P hno)

/-- Finite natural-index Lemma 9 data rules out every early triple equality.
-/
theorem noEarlyTripleEquality_of_natLateTripleInputs
    (H : M8NatLateTripleInputs P) :
    M8NoEarlyTripleEquality P := by
  intro a hearly htriple
  exact
    (m8TripleStartLate_iff_not_early a).mp
      (H.late_of_tripleEquality htriple) hearly

/-- The finite natural-index Lemma 9 package is exactly the abstract no-early
triple-equality predicate. -/
theorem nonempty_natLateTripleInputs_iff_noEarlyTripleEquality :
    Nonempty (M8NatLateTripleInputs P) <->
      M8NoEarlyTripleEquality P := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact noEarlyTripleEquality_of_natLateTripleInputs H
  case mpr =>
    intro hno
    exact Nonempty.intro (natLateTripleInputs_of_noEarlyTripleEquality hno)

/-- Build finite natural-index Lemma 9 data from the concrete five-start
no-early package. -/
def natLateTripleInputs_of_concreteNoEarlyTripleEquality
    (H : M8ConcreteNoEarlyTripleEquality P) :
    M8NatLateTripleInputs P :=
  natLateTripleInputs_of_noEarlyTripleEquality H.toNoEarlyTripleEquality

/-- Direct theorem form: concrete five-start exclusions are positive
finite natural-index Lemma 9 rows. -/
theorem nonempty_natLateTripleInputs_of_concreteNoEarlyTripleEquality
    (H : M8ConcreteNoEarlyTripleEquality P) :
    Nonempty (M8NatLateTripleInputs P) :=
  Nonempty.intro (natLateTripleInputs_of_concreteNoEarlyTripleEquality H)

/-- Direct constructor from the five concrete early-start exclusions.  This is
the pointwise row shape needed by selected-frame incidence packages: prove the
five early triple equalities impossible, and the finite nat-late rows follow. -/
def natLateTripleInputs_of_fiveStartExclusions
    (no_start1 : Not (P.tripleEquality start1))
    (no_start2 : Not (P.tripleEquality start2))
    (no_start3 : Not (P.tripleEquality start3))
    (no_start4 : Not (P.tripleEquality start4))
    (no_start5 : Not (P.tripleEquality start5)) :
    M8NatLateTripleInputs P :=
  natLateTripleInputs_of_concreteNoEarlyTripleEquality
    { no_start1 := no_start1
      no_start2 := no_start2
      no_start3 := no_start3
      no_start4 := no_start4
      no_start5 := no_start5 }

/-- Direct theorem form for five concrete early-start exclusions. -/
theorem nonempty_natLateTripleInputs_of_fiveStartExclusions
    (no_start1 : Not (P.tripleEquality start1))
    (no_start2 : Not (P.tripleEquality start2))
    (no_start3 : Not (P.tripleEquality start3))
    (no_start4 : Not (P.tripleEquality start4))
    (no_start5 : Not (P.tripleEquality start5)) :
    Nonempty (M8NatLateTripleInputs P) :=
  Nonempty.intro
    (natLateTripleInputs_of_fiveStartExclusions
      no_start1 no_start2 no_start3 no_start4 no_start5)

/-- Package the five explicit early-start exclusions as concrete no-early
triple equality. -/
def concreteNoEarlyTripleEquality_of_fiveStartExclusions
    (no_start1 : Not (P.tripleEquality start1))
    (no_start2 : Not (P.tripleEquality start2))
    (no_start3 : Not (P.tripleEquality start3))
    (no_start4 : Not (P.tripleEquality start4))
    (no_start5 : Not (P.tripleEquality start5)) :
    M8ConcreteNoEarlyTripleEquality P where
  no_start1 := no_start1
  no_start2 := no_start2
  no_start3 := no_start3
  no_start4 := no_start4
  no_start5 := no_start5

/-- Concrete no-early triple equality is exactly the five explicit early-start
exclusions. -/
theorem concreteNoEarlyTripleEquality_iff_fiveStartExclusions :
    M8ConcreteNoEarlyTripleEquality P <->
      Not (P.tripleEquality start1) /\
      Not (P.tripleEquality start2) /\
      Not (P.tripleEquality start3) /\
      Not (P.tripleEquality start4) /\
      Not (P.tripleEquality start5) := by
  constructor
  case mp =>
    intro H
    exact
      And.intro H.no_start1
        (And.intro H.no_start2
          (And.intro H.no_start3
            (And.intro H.no_start4 H.no_start5)))
  case mpr =>
    intro H
    exact
      concreteNoEarlyTripleEquality_of_fiveStartExclusions
        H.1 H.2.1 H.2.2.1 H.2.2.2.1 H.2.2.2.2

/-- Finite natural-index Lemma 9 data is exactly the five explicit
early-start exclusions. -/
theorem nonempty_natLateTripleInputs_iff_fiveStartExclusions :
    Nonempty (M8NatLateTripleInputs P) <->
      Not (P.tripleEquality start1) /\
      Not (P.tripleEquality start2) /\
      Not (P.tripleEquality start3) /\
      Not (P.tripleEquality start4) /\
      Not (P.tripleEquality start5) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact
          (concreteNoEarlyTripleEquality_iff_fiveStartExclusions
            (P := P)).mp
            (NoEarlyTripleFromLemma9.concreteNoEarlyTripleEquality_of_natLateTripleInputs H)
  case mpr =>
    intro h
    exact
      nonempty_natLateTripleInputs_of_fiveStartExclusions
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- Extract the concrete five-start no-early package from finite natural
Lemma 9 data. -/
def concreteNoEarlyTripleEquality_of_natLateTripleInputs
    (H : M8NatLateTripleInputs P) :
    M8ConcreteNoEarlyTripleEquality P :=
  NoEarlyTripleFromLemma9.concreteNoEarlyTripleEquality_of_natLateTripleInputs H

/-- Finite natural-index Lemma 9 data is equivalent to the concrete five-start
no-early package. -/
theorem nonempty_natLateTripleInputs_iff_concreteNoEarlyTripleEquality :
    Nonempty (M8NatLateTripleInputs P) <->
      M8ConcreteNoEarlyTripleEquality P := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact concreteNoEarlyTripleEquality_of_natLateTripleInputs H
  case mpr =>
    intro H
    exact
      Nonempty.intro
        (natLateTripleInputs_of_concreteNoEarlyTripleEquality H)

/-- Selected-frame five-start exclusions give the finite natural-index
Lemma 9 rows, pointwise over actual minimal-failure configurations. -/
def actualSelectedNatLateTripleInputRows_of_fiveStartExclusions
    {Pred : ActualSelectedPredicateFamily}
    (H : ActualSelectedFiveStartExclusionRows Pred) :
    ActualSelectedNatLateTripleInputRows Pred :=
  fun {n} C hmin =>
    let hrow := H C hmin
    natLateTripleInputs_of_fiveStartExclusions
      (P := Pred (n := n) C hmin)
      hrow.1 hrow.2.1 hrow.2.2.1 hrow.2.2.2.1 hrow.2.2.2.2

/-- On the selected-frame surface, finite natural-index Lemma 9 rows are
exactly the five explicit early-start exclusions. -/
theorem nonempty_actualSelectedNatLateTripleInputRows_iff_fiveStartExclusions
    {Pred : ActualSelectedPredicateFamily} :
    Nonempty (ActualSelectedNatLateTripleInputRows Pred) <->
      ActualSelectedFiveStartExclusionRows Pred := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact actualSelectedFiveStartExclusionRows_of_natLateTripleInputs H
  case mpr =>
    intro H
    exact
      Nonempty.intro
        (actualSelectedNatLateTripleInputRows_of_fiveStartExclusions H)

/-- Build finite natural-index Lemma 9 data from explicit false-start
implications. -/
def natLateTripleInputs_of_falseStartImplications
    (H : M8ConcreteFalseStartImplications P) :
    M8NatLateTripleInputs P :=
  natLateTripleInputs_of_concreteNoEarlyTripleEquality
    H.toConcreteNoEarlyTripleEquality

/-- Finite natural-index Lemma 9 data is equivalent to explicit false-start
implications. -/
theorem nonempty_natLateTripleInputs_iff_falseStartImplications :
    Nonempty (M8NatLateTripleInputs P) <->
      M8ConcreteFalseStartImplications P := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact
          M8ConcreteFalseStartImplications.ofConcreteNoEarlyTripleEquality
            (concreteNoEarlyTripleEquality_of_natLateTripleInputs H)
  case mpr =>
    intro H
    exact
      Nonempty.intro
        (natLateTripleInputs_of_falseStartImplications H)

/-- Build finite natural-index Lemma 9 data from indexed early obstructions.
-/
def natLateTripleInputs_of_indexedObstructionInputs
    (H : M8ConcreteIndexedObstructionInputs P) :
    M8NatLateTripleInputs P :=
  natLateTripleInputs_of_noEarlyTripleEquality H.toNoEarlyTripleEquality

/-- Finite natural-index Lemma 9 data produces the indexed obstruction view.
-/
def indexedObstructionInputs_of_natLateTripleInputs
    (H : M8NatLateTripleInputs P) :
    M8ConcreteIndexedObstructionInputs P :=
  indexedObstructionInputs_of_fiveStartLateFacts
    (M8Lemma9FiveStartLateFacts.ofNatLateTripleInputs H)

/-- Finite natural-index Lemma 9 data is equivalent to indexed early
obstruction data. -/
theorem nonempty_natLateTripleInputs_iff_indexedObstructionInputs :
    Nonempty (M8NatLateTripleInputs P) <->
      Nonempty (M8ConcreteIndexedObstructionInputs P) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact Nonempty.intro (indexedObstructionInputs_of_natLateTripleInputs H)
  case mpr =>
    intro H
    cases H with
    | intro I =>
        exact
          Nonempty.intro
            (natLateTripleInputs_of_indexedObstructionInputs I)

/-- Abstract no-early data is an abstract early-obstruction package. -/
def earlyTripleObstructionInputs_of_noEarlyTripleEquality
    (hno : M8NoEarlyTripleEquality P) :
    M8EarlyTripleObstructionInputs P where
  obstruction := fun _ => False
  obstruction_of_early_triple := by
    intro a hearly htriple
    exact False.elim (hno a hearly htriple)
  obstruction_false := by
    intro a _hearly hfalse
    exact hfalse

/-- Finite natural-index Lemma 9 data produces the abstract early-obstruction
view. -/
def earlyTripleObstructionInputs_of_natLateTripleInputs
    (H : M8NatLateTripleInputs P) :
    M8EarlyTripleObstructionInputs P :=
  earlyTripleObstructionInputs_of_noEarlyTripleEquality
    (noEarlyTripleEquality_of_natLateTripleInputs H)

/-- Build finite natural-index Lemma 9 data from abstract early obstructions.
-/
def natLateTripleInputs_of_earlyTripleObstructionInputs
    (H : M8EarlyTripleObstructionInputs P) :
    M8NatLateTripleInputs P where
  tripleStartPredicate := fun a => 6 <= a
  predicate_of_tripleEquality := by
    intro a htriple
    exact
      match m8TripleStart_late_or_early a with
      | Or.inl hlate => hlate
      | Or.inr hearly =>
          False.elim
            (H.obstruction_false a hearly
              (H.obstruction_of_early_triple a hearly htriple))
  late_of_predicate := by
    intro _a _ha1 _ha2 hlate
    exact hlate

/-- Build finite natural-index Lemma 9 data directly from a single forbidden
local pattern: an early triple equality gives the pattern, while the source
geometry excludes the pattern.  This avoids packaging the argument through
the concrete no-early equality interface. -/
def natLateTripleInputs_of_forbiddenObstruction
    {forbidden : Prop}
    (H : M8ConcreteForbiddenObstructionInputs P forbidden)
    (hforbidden : Not forbidden) :
    M8NatLateTripleInputs P where
  tripleStartPredicate := fun a => 6 <= a
  predicate_of_tripleEquality := by
    intro a htriple
    exact
      match m8TripleStart_late_or_early a with
      | Or.inl hlate => hlate
      | Or.inr hearly =>
          False.elim
            (H.false_of_early_triple hforbidden hearly htriple)
  late_of_predicate := by
    intro _a _ha1 _ha2 hlate
    exact hlate

/-- Direct theorem form for a single forbidden local pattern: if every early
triple equality produces the forbidden pattern, and the pattern is impossible,
then the positive finite nat-late rows are inhabited. -/
theorem nonempty_natLateTripleInputs_of_forbiddenObstruction
    {forbidden : Prop}
    (H : M8ConcreteForbiddenObstructionInputs P forbidden)
    (hforbidden : Not forbidden) :
    Nonempty (M8NatLateTripleInputs P) :=
  Nonempty.intro (natLateTripleInputs_of_forbiddenObstruction H hforbidden)

/-- Finite natural-index Lemma 9 data is equivalent to abstract early
obstruction data. -/
theorem nonempty_natLateTripleInputs_iff_earlyTripleObstructionInputs :
    Nonempty (M8NatLateTripleInputs P) <->
      Nonempty (M8EarlyTripleObstructionInputs P) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact Nonempty.intro (earlyTripleObstructionInputs_of_natLateTripleInputs H)
  case mpr =>
    intro H
    cases H with
    | intro I =>
        exact
          Nonempty.intro
            (natLateTripleInputs_of_earlyTripleObstructionInputs I)

/-! ## Pipeline and construction-facing packages -/

variable {Q : M8HonestLocalPredicates G}

/-- Finite natural-index Lemma 9 data gives the no-early package used by
`M8LateTriplesFromNoEarly`. -/
def pipelineNoEarlyTriples_of_natLateTripleInputs
    (H : M8NatLateTripleInputs Q.data) :
    M8PipelineNoEarlyTriples Q where
  noEarlyTripleEquality := noEarlyTripleEquality_of_natLateTripleInputs H

/-- A pipeline no-early package gives finite natural-index Lemma 9 data. -/
def natLateTripleInputs_of_pipelineNoEarlyTriples
    (H : M8PipelineNoEarlyTriples Q) :
    M8NatLateTripleInputs Q.data :=
  natLateTripleInputs_of_noEarlyTripleEquality H.toNoEarlyTripleEquality

/-- Finite natural-index Lemma 9 data is equivalent to the pipeline no-early
package. -/
theorem nonempty_natLateTripleInputs_iff_pipelineNoEarlyTriples :
    Nonempty (M8NatLateTripleInputs Q.data) <->
      M8PipelineNoEarlyTriples Q := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact pipelineNoEarlyTriples_of_natLateTripleInputs H
  case mpr =>
    intro H
    exact
      Nonempty.intro
        (natLateTripleInputs_of_pipelineNoEarlyTriples H)

/-- Finite natural-index Lemma 9 data gives the pipeline late-triples field,
using the checked no-early bridge. -/
def lateTriplesField_of_natLateTripleInputs
    (H : M8NatLateTripleInputs Q.data) :
    M8PipelineClosure.M8LateTriplesField Q :=
  M8LateTriplesConcrete.lateTriplesField_of_noEarlyTripleEquality Q
    (noEarlyTripleEquality_of_natLateTripleInputs H)

/-- The pipeline late-triples field gives finite natural-index Lemma 9 data.
-/
def natLateTripleInputs_of_lateTriplesField
    (H : M8PipelineClosure.M8LateTriplesField Q) :
    M8NatLateTripleInputs Q.data :=
  natLateTripleInputs_of_lateTriples H.lateTriples

/-- Finite natural-index Lemma 9 data is equivalent to the pipeline
late-triples field. -/
theorem nonempty_natLateTripleInputs_iff_lateTriplesField :
    Nonempty (M8NatLateTripleInputs Q.data) <->
      M8PipelineClosure.M8LateTriplesField Q := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact lateTriplesField_of_natLateTripleInputs H
  case mpr =>
    intro H
    exact
      Nonempty.intro
        (natLateTripleInputs_of_lateTriplesField H)

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8ConstructionInterface.M8LocalLabels C}

/-- Finite natural-index Lemma 9 data gives the construction-interface
no-early package. -/
def constructionNoEarlyTriples_of_natLateTripleInputs
    (H : M8NatLateTripleInputs localLabels.predicates.data) :
    M8ConstructionNoEarlyTriples localLabels :=
  NoEarlyTripleFromLemma9.constructionNoEarlyTriples_of_natLateTripleInputs H

/-- A construction-interface no-early package gives finite natural-index
Lemma 9 data. -/
def natLateTripleInputs_of_constructionNoEarlyTriples
    (H : M8ConstructionNoEarlyTriples localLabels) :
    M8NatLateTripleInputs localLabels.predicates.data :=
  natLateTripleInputs_of_noEarlyTripleEquality H.toNoEarlyTripleEquality

/-- Finite natural-index Lemma 9 data is equivalent to the
construction-interface no-early package. -/
theorem nonempty_natLateTripleInputs_iff_constructionNoEarlyTriples :
    Nonempty (M8NatLateTripleInputs localLabels.predicates.data) <->
      M8ConstructionNoEarlyTriples localLabels := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact constructionNoEarlyTriples_of_natLateTripleInputs H
  case mpr =>
    intro H
    exact
      Nonempty.intro
        (natLateTripleInputs_of_constructionNoEarlyTriples H)

/-- Finite natural-index Lemma 9 data gives construction-interface late
triples. -/
def constructionLateTriples_of_natLateTripleInputs
    (H : M8NatLateTripleInputs localLabels.predicates.data) :
    M8ConstructionInterface.M8LateTriples localLabels :=
  (constructionNoEarlyTriples_of_natLateTripleInputs H).toM8LateTriples

/-! ## W19, W17, and W18 row reductions -/

variable {hmin : IsMinimalClearedFailure C}
variable {B : Lemma9LateTriplesW16.PointwiseLemma89PreLateBase.{u} C hmin}

/-- W19 coverage rows are exactly coverage plus no-early triples. -/
theorem nonempty_natCoverageInputs_iff_exists_coverage_and_noEarly :
    Nonempty (M8NatLateTripleCoverageInputs B) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            B.arcBoundaryBudget.planarBoundary longArcCount) /\
          M8NoEarlyTripleEquality
            B.localLabels.predicates.data := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro I =>
        exact
          Exists.intro I.longArcCount
            (And.intro
              (Nonempty.intro I.coverage)
              (noEarlyTripleEquality_of_natLateTripleInputs
                I.natLateTripleInputs))
  case mpr =>
    intro h
    cases h with
    | intro longArcCount hrow =>
        cases hrow.1 with
        | intro coverage =>
            exact
              Nonempty.intro
                ({ longArcCount := longArcCount
                   coverage := coverage
                   natLateTripleInputs :=
                    natLateTripleInputs_of_noEarlyTripleEquality hrow.2 } :
                  M8NatLateTripleCoverageInputs B)

/-- W19 coverage rows are exactly coverage plus raw late triples. -/
theorem nonempty_natCoverageInputs_iff_exists_coverage_and_lateTriples :
    Nonempty (M8NatLateTripleCoverageInputs B) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            B.arcBoundaryBudget.planarBoundary longArcCount) /\
          M8BrokenLatticeLateTriples
            B.localLabels.predicates.data := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro I =>
        exact
          Exists.intro I.longArcCount
            (And.intro
              (Nonempty.intro I.coverage)
              I.natLateTripleInputs.lateTriples)
  case mpr =>
    intro h
    cases h with
    | intro longArcCount hrow =>
        cases hrow.1 with
        | intro coverage =>
            exact
              Nonempty.intro
                ({ longArcCount := longArcCount
                   coverage := coverage
                   natLateTripleInputs :=
                    natLateTripleInputs_of_lateTriples hrow.2 } :
                  M8NatLateTripleCoverageInputs B)

/-- Build W19 coverage rows directly from coverage and the five explicit
early-start exclusions. -/
def natCoverageInputs_of_coverage_and_fiveStartExclusions
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        B.arcBoundaryBudget.planarBoundary longArcCount)
    (no_start1 :
      Not (B.localLabels.predicates.data.tripleEquality start1))
    (no_start2 :
      Not (B.localLabels.predicates.data.tripleEquality start2))
    (no_start3 :
      Not (B.localLabels.predicates.data.tripleEquality start3))
    (no_start4 :
      Not (B.localLabels.predicates.data.tripleEquality start4))
    (no_start5 :
      Not (B.localLabels.predicates.data.tripleEquality start5)) :
    M8NatLateTripleCoverageInputs B where
  longArcCount := longArcCount
  coverage := coverage
  natLateTripleInputs :=
    natLateTripleInputs_of_fiveStartExclusions
      no_start1 no_start2 no_start3 no_start4 no_start5

/-- Constructor form for W19 coverage rows from coverage plus five explicit
early-start exclusions. -/
theorem nonempty_natCoverageInputs_of_coverage_and_fiveStartExclusions
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        B.arcBoundaryBudget.planarBoundary longArcCount)
    (no_start1 :
      Not (B.localLabels.predicates.data.tripleEquality start1))
    (no_start2 :
      Not (B.localLabels.predicates.data.tripleEquality start2))
    (no_start3 :
      Not (B.localLabels.predicates.data.tripleEquality start3))
    (no_start4 :
      Not (B.localLabels.predicates.data.tripleEquality start4))
    (no_start5 :
      Not (B.localLabels.predicates.data.tripleEquality start5)) :
    Nonempty (M8NatLateTripleCoverageInputs B) :=
  Nonempty.intro
    (natCoverageInputs_of_coverage_and_fiveStartExclusions
      (B := B) longArcCount coverage
      no_start1 no_start2 no_start3 no_start4 no_start5)

/-- W19 coverage rows are exactly coverage plus the five explicit early-start
exclusions. -/
theorem nonempty_natCoverageInputs_iff_exists_coverage_and_fiveStartExclusions :
    Nonempty (M8NatLateTripleCoverageInputs B) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            B.arcBoundaryBudget.planarBoundary longArcCount) /\
          Not (B.localLabels.predicates.data.tripleEquality start1) /\
          Not (B.localLabels.predicates.data.tripleEquality start2) /\
          Not (B.localLabels.predicates.data.tripleEquality start3) /\
          Not (B.localLabels.predicates.data.tripleEquality start4) /\
          Not (B.localLabels.predicates.data.tripleEquality start5) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro I =>
        exact
          Exists.intro I.longArcCount
            (And.intro
              (Nonempty.intro I.coverage)
              ((nonempty_natLateTripleInputs_iff_fiveStartExclusions
                (P := B.localLabels.predicates.data)).mp
                (Nonempty.intro I.natLateTripleInputs)))
  case mpr =>
    intro h
    cases h with
    | intro longArcCount hrow =>
        cases hrow.1 with
        | intro coverage =>
            exact
              nonempty_natCoverageInputs_of_coverage_and_fiveStartExclusions
                (B := B) longArcCount coverage
                hrow.2.1 hrow.2.2.1 hrow.2.2.2.1
                hrow.2.2.2.2.1 hrow.2.2.2.2.2

/-- W17 concrete coverage rows are exactly coverage plus no-early triples. -/
theorem nonempty_coverageConcreteRow_iff_exists_coverage_and_noEarly :
    Nonempty (Lemma9CoverageConcreteRow B) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            B.arcBoundaryBudget.planarBoundary longArcCount) /\
          M8NoEarlyTripleEquality
            B.localLabels.predicates.data :=
  nonempty_coverageConcreteRow_iff_natCoverageInputs.trans
    nonempty_natCoverageInputs_iff_exists_coverage_and_noEarly

/-- W17 concrete coverage rows are exactly coverage plus raw late triples. -/
theorem nonempty_coverageConcreteRow_iff_exists_coverage_and_lateTriples :
    Nonempty (Lemma9CoverageConcreteRow B) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            B.arcBoundaryBudget.planarBoundary longArcCount) /\
          M8BrokenLatticeLateTriples
            B.localLabels.predicates.data :=
  nonempty_coverageConcreteRow_iff_natCoverageInputs.trans
    nonempty_natCoverageInputs_iff_exists_coverage_and_lateTriples

/-- Build a W17 concrete coverage row directly from coverage and the five
explicit early-start exclusions. -/
def coverageConcreteRow_of_coverage_and_fiveStartExclusions
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        B.arcBoundaryBudget.planarBoundary longArcCount)
    (no_start1 :
      Not (B.localLabels.predicates.data.tripleEquality start1))
    (no_start2 :
      Not (B.localLabels.predicates.data.tripleEquality start2))
    (no_start3 :
      Not (B.localLabels.predicates.data.tripleEquality start3))
    (no_start4 :
      Not (B.localLabels.predicates.data.tripleEquality start4))
    (no_start5 :
      Not (B.localLabels.predicates.data.tripleEquality start5)) :
    Lemma9CoverageConcreteRow B :=
  (natCoverageInputs_of_coverage_and_fiveStartExclusions
    (B := B) longArcCount coverage
    no_start1 no_start2 no_start3 no_start4 no_start5).toCoverageConcreteRow

/-- Constructor form for W17 concrete coverage rows from coverage plus five
explicit early-start exclusions. -/
theorem nonempty_coverageConcreteRow_of_coverage_and_fiveStartExclusions
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        B.arcBoundaryBudget.planarBoundary longArcCount)
    (no_start1 :
      Not (B.localLabels.predicates.data.tripleEquality start1))
    (no_start2 :
      Not (B.localLabels.predicates.data.tripleEquality start2))
    (no_start3 :
      Not (B.localLabels.predicates.data.tripleEquality start3))
    (no_start4 :
      Not (B.localLabels.predicates.data.tripleEquality start4))
    (no_start5 :
      Not (B.localLabels.predicates.data.tripleEquality start5)) :
    Nonempty (Lemma9CoverageConcreteRow B) :=
  Nonempty.intro
    (coverageConcreteRow_of_coverage_and_fiveStartExclusions
      (B := B) longArcCount coverage
      no_start1 no_start2 no_start3 no_start4 no_start5)

/-- W17 concrete coverage rows are exactly coverage plus the five explicit
early-start exclusions. -/
theorem nonempty_coverageConcreteRow_iff_exists_coverage_and_fiveStartExclusions :
    Nonempty (Lemma9CoverageConcreteRow B) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            B.arcBoundaryBudget.planarBoundary longArcCount) /\
          Not (B.localLabels.predicates.data.tripleEquality start1) /\
          Not (B.localLabels.predicates.data.tripleEquality start2) /\
          Not (B.localLabels.predicates.data.tripleEquality start3) /\
          Not (B.localLabels.predicates.data.tripleEquality start4) /\
          Not (B.localLabels.predicates.data.tripleEquality start5) :=
  nonempty_coverageConcreteRow_iff_natCoverageInputs.trans
    nonempty_natCoverageInputs_iff_exists_coverage_and_fiveStartExclusions

variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (Lemma67ToBoundaryArcW14.CanonicalGraph C)}
variable {R : Lemma67ToBoundaryArcW14.Lemma67BoundaryArcInput C D}

/-- W18 boundary-arc predicate fields are exactly budget equality plus
no-early triples. -/
theorem nonempty_boundaryArcPredicateFields_iff_budgetEq_and_noEarly :
    Nonempty (Lemma67BoundaryArcPredicateFields B R) <->
      R.arcBoundaryBudget = B.arcBoundaryBudget /\
        M8NoEarlyTripleEquality B.localLabels.predicates.data := by
  constructor
  case mp =>
    intro h
    have hnat :=
      (nonempty_boundaryArcPredicateFields_iff_budgetEq_and_nat
        (B := B) (Q := R)).mp h
    exact
      And.intro hnat.1
        ((nonempty_natLateTripleInputs_iff_noEarlyTripleEquality
          (P := B.localLabels.predicates.data)).mp hnat.2)
  case mpr =>
    intro h
    exact
      (nonempty_boundaryArcPredicateFields_iff_budgetEq_and_nat
        (B := B) (Q := R)).mpr
        (And.intro h.1
          ((nonempty_natLateTripleInputs_iff_noEarlyTripleEquality
            (P := B.localLabels.predicates.data)).mpr h.2))

/-- W18 boundary-arc predicate fields are exactly budget equality plus raw
late triples. -/
theorem nonempty_boundaryArcPredicateFields_iff_budgetEq_and_lateTriples :
    Nonempty (Lemma67BoundaryArcPredicateFields B R) <->
      R.arcBoundaryBudget = B.arcBoundaryBudget /\
        M8BrokenLatticeLateTriples B.localLabels.predicates.data := by
  constructor
  case mp =>
    intro h
    have hnat :=
      (nonempty_boundaryArcPredicateFields_iff_budgetEq_and_nat
        (B := B) (Q := R)).mp h
    exact
      And.intro hnat.1
        ((nonempty_natLateTripleInputs_iff_lateTriples
          (P := B.localLabels.predicates.data)).mp hnat.2)
  case mpr =>
    intro h
    exact
      (nonempty_boundaryArcPredicateFields_iff_budgetEq_and_nat
        (B := B) (Q := R)).mpr
        (And.intro h.1
          ((nonempty_natLateTripleInputs_iff_lateTriples
            (P := B.localLabels.predicates.data)).mpr h.2))

/-! ## W21 source-field reductions past coverage -/

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}
variable {Cw : _root_.UDConfig n}
variable {hminw : IsMinimalClearedFailure Cw}

/-- Build W20 Lemma 9 source fields from coverage and no-early triples. -/
def sourceFieldsOfCoverageAndNoEarly
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
        longArcCount)
    (hno :
      M8NoEarlyTripleEquality
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data) :
    Lemma9NatLateTripleSourceFields.{u}
      payForCut topologyArc lemma8 Cw hminw where
  longArcCount := longArcCount
  coverage := coverage
  natLateTripleInputs := natLateTripleInputs_of_noEarlyTripleEquality hno

/-- Build W20 Lemma 9 source fields from coverage and raw late triples. -/
def sourceFieldsOfCoverageAndLateTriples
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
        longArcCount)
    (hlate :
      M8BrokenLatticeLateTriples
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data) :
    Lemma9NatLateTripleSourceFields.{u}
      payForCut topologyArc lemma8 Cw hminw where
  longArcCount := longArcCount
  coverage := coverage
  natLateTripleInputs := natLateTripleInputs_of_lateTriples hlate

/-- Build W20 Lemma 9 source fields from coverage and positive finite
natural-index Lemma 9 rows. -/
def sourceFieldsOfCoverageAndNatLateTripleInputs
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
        longArcCount)
    (H :
      M8NatLateTripleInputs
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data) :
    Lemma9NatLateTripleSourceFields.{u}
      payForCut topologyArc lemma8 Cw hminw where
  longArcCount := longArcCount
  coverage := coverage
  natLateTripleInputs := H

/-- Build W20 Lemma 9 source fields from coverage and the concrete five-start
no-early package. -/
def sourceFieldsOfCoverageAndConcreteNoEarly
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
        longArcCount)
    (H :
      M8ConcreteNoEarlyTripleEquality
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data) :
    Lemma9NatLateTripleSourceFields.{u}
      payForCut topologyArc lemma8 Cw hminw :=
  sourceFieldsOfCoverageAndNoEarly
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)
    longArcCount coverage H.toNoEarlyTripleEquality

/-- Build W20 Lemma 9 source fields from coverage and the five explicit
early-start exclusions. -/
def sourceFieldsOfCoverageAndFiveStartExclusions
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
        longArcCount)
    (no_start1 :
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
        start1))
    (no_start2 :
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
        start2))
    (no_start3 :
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
        start3))
    (no_start4 :
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
        start4))
    (no_start5 :
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
        start5)) :
    Lemma9NatLateTripleSourceFields.{u}
      payForCut topologyArc lemma8 Cw hminw :=
  sourceFieldsOfCoverageAndNatLateTripleInputs
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)
    longArcCount coverage
    (natLateTripleInputs_of_fiveStartExclusions
      no_start1 no_start2 no_start3 no_start4 no_start5)

/-- Constructor form for W20 Lemma 9 source fields from coverage and the five
explicit early-start exclusions. -/
theorem nonempty_sourceFields_of_coverage_and_fiveStartExclusions
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
        longArcCount)
    (no_start1 :
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
        start1))
    (no_start2 :
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
        start2))
    (no_start3 :
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
        start3))
    (no_start4 :
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
        start4))
    (no_start5 :
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
        start5)) :
    Nonempty
      (Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) :=
  Nonempty.intro
    (sourceFieldsOfCoverageAndFiveStartExclusions
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)
      longArcCount coverage
      no_start1 no_start2 no_start3 no_start4 no_start5)

/-- W20 Lemma 9 source fields expose the selected gap-negative coverage row. -/
def gapNegativeCoverageDataOfSourceFields
    (S :
      Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) :
    GapNegativeCoverageData
      (AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
      S.longArcCount :=
  S.coverage

/-- W20 Lemma 9 source fields expose the finite natural-index Lemma 9 rows.
This is the import-safe W22 projection used after any later route has produced
the matching source fields. -/
def natLateTripleInputsOfSourceFields
    (S :
      Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) :
    M8NatLateTripleInputs
      (AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data :=
  S.natLateTripleInputs

/-- Source fields produce the abstract no-early triple-equality row. -/
def noEarlyTripleEqualityOfSourceFields
    (S :
      Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) :
    M8NoEarlyTripleEquality
      (AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data :=
  noEarlyTripleEquality_of_natLateTripleInputs
    (natLateTripleInputsOfSourceFields
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) (Cw := Cw) (hminw := hminw) S)

/-- Source fields produce the concrete five-start no-early row. -/
def concreteNoEarlyTripleEqualityOfSourceFields
    (S :
      Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) :
    M8ConcreteNoEarlyTripleEquality
      (AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data :=
  concreteNoEarlyTripleEquality_of_natLateTripleInputs
    (natLateTripleInputsOfSourceFields
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) (Cw := Cw) (hminw := hminw) S)

/-- Source fields produce raw late triples. -/
def lateTriplesOfSourceFields
    (S :
      Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) :
    M8BrokenLatticeLateTriples
      (AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data :=
  (natLateTripleInputsOfSourceFields
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Cw := Cw) (hminw := hminw) S).lateTriples

/-- Source fields reduce to the five explicit early-start exclusions. -/
theorem fiveStartExclusionsOfSourceFields
    (S :
      Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) :
    Not (((AssembledLemma9PreLateBase
      payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
      start1) /\
    Not (((AssembledLemma9PreLateBase
      payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
      start2) /\
    Not (((AssembledLemma9PreLateBase
      payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
      start3) /\
    Not (((AssembledLemma9PreLateBase
      payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
      start4) /\
    Not (((AssembledLemma9PreLateBase
      payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
      start5) :=
  (concreteNoEarlyTripleEquality_iff_fiveStartExclusions
    (P :=
      (AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data)).mp
    (concreteNoEarlyTripleEqualityOfSourceFields
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) (Cw := Cw) (hminw := hminw) S)

/-- Source fields directly inhabit the finite natural-index Lemma 9 row. -/
theorem nonempty_natLateTripleInputs_of_sourceFields
    (S :
      Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) :
    Nonempty
      (M8NatLateTripleInputs
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data) :=
  Nonempty.intro
    (natLateTripleInputsOfSourceFields
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) (Cw := Cw) (hminw := hminw) S)

/-- Nonempty source fields directly inhabit the finite natural-index Lemma 9
row. -/
theorem nonempty_natLateTripleInputs_of_nonempty_sourceFields
    (h :
      Nonempty
        (Lemma9NatLateTripleSourceFields.{u}
          payForCut topologyArc lemma8 Cw hminw)) :
    Nonempty
      (M8NatLateTripleInputs
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data) := by
  cases h with
  | intro S =>
      exact
        nonempty_natLateTripleInputs_of_sourceFields
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8) (Cw := Cw) (hminw := hminw) S

/-- Source fields directly expose coverage plus five-start exclusions, the
same payload consumed by the compact route-coverage constructors. -/
theorem exists_coverage_and_fiveStartExclusionsOfSourceFields
    (S :
      Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) :
    exists longArcCount : Nat,
      Nonempty
        (GapNegativeCoverageData
          (AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
          longArcCount) /\
        Not (((AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
          start1) /\
        Not (((AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
          start2) /\
        Not (((AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
          start3) /\
        Not (((AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
          start4) /\
        Not (((AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
          start5) :=
  Exists.intro S.longArcCount
    (And.intro (Nonempty.intro S.coverage)
      (fiveStartExclusionsOfSourceFields
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) (Cw := Cw) (hminw := hminw) S))

/-- Uniform assembled-row constructor: pointwise concrete five-start
no-early rows provide the positive finite nat-late Lemma 9 rows for the whole
W20 source family surface.  Downstream selected-frame packages instantiate
this with their concrete row predicates. -/
def assembledNatLateTripleInputsFamilyOfConcreteNoEarly
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8ConcreteNoEarlyTripleEquality
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8NatLateTripleInputs
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 C hmin).localLabels.predicates.data :=
  fun C hmin =>
    natLateTripleInputs_of_concreteNoEarlyTripleEquality (H C hmin)

/-- Nonempty family form of
`assembledNatLateTripleInputsFamilyOfConcreteNoEarly`. -/
theorem nonempty_assembledNatLateTripleInputsFamily_of_concreteNoEarly
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8ConcreteNoEarlyTripleEquality
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) :
    Nonempty
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8NatLateTripleInputs
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) :=
  Nonempty.intro
    (assembledNatLateTripleInputsFamilyOfConcreteNoEarly
      (payForCut := payForCut)
      (topologyArc := topologyArc)
      (lemma8 := lemma8) H)

/-- Pointwise concrete five-start exclusions for every assembled W20 row. -/
abbrev AssembledFiveStartExclusionRows
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
        start1) /\
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
        start2) /\
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
        start3) /\
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
        start4) /\
      Not (((AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
        start5)

/-- Pointwise five-start exclusions repackage as concrete no-early rows for
the assembled W20 source-family surface. -/
def assembledConcreteNoEarlyFamilyOfFiveStartExclusions
    (H :
      AssembledFiveStartExclusionRows
        payForCut topologyArc lemma8) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8ConcreteNoEarlyTripleEquality
          (AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 C hmin).localLabels.predicates.data :=
  fun C hmin =>
    let hrow := H C hmin
    { no_start1 := hrow.1
      no_start2 := hrow.2.1
      no_start3 := hrow.2.2.1
      no_start4 := hrow.2.2.2.1
      no_start5 := hrow.2.2.2.2 }

/-- Uniform assembled-row constructor from explicit five-start exclusions:
the five pointwise no-start rows provide positive finite nat-late Lemma 9
inputs for every assembled minimal-failure row. -/
def assembledNatLateTripleInputsFamilyOfFiveStartExclusions
    (H :
      AssembledFiveStartExclusionRows
        payForCut topologyArc lemma8) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8NatLateTripleInputs
          (AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 C hmin).localLabels.predicates.data :=
  assembledNatLateTripleInputsFamilyOfConcreteNoEarly
    (payForCut := payForCut)
    (topologyArc := topologyArc)
    (lemma8 := lemma8)
    (assembledConcreteNoEarlyFamilyOfFiveStartExclusions
      (payForCut := payForCut)
      (topologyArc := topologyArc)
      (lemma8 := lemma8) H)

/-- Nonempty family form of
`assembledNatLateTripleInputsFamilyOfFiveStartExclusions`. -/
theorem nonempty_assembledNatLateTripleInputsFamily_of_fiveStartExclusions
    (H :
      AssembledFiveStartExclusionRows
        payForCut topologyArc lemma8) :
    Nonempty
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8NatLateTripleInputs
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) :=
  Nonempty.intro
    (assembledNatLateTripleInputsFamilyOfFiveStartExclusions
      (payForCut := payForCut)
      (topologyArc := topologyArc)
      (lemma8 := lemma8) H)

/-- Exact assembled-row handoff: pointwise finite natural-index Lemma 9 rows
are equivalent to the five explicit early-start exclusions for the selected
W20 source-family surface. -/
theorem nonempty_assembledNatLateTripleInputsFamily_iff_fiveStartExclusions :
    Nonempty
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8NatLateTripleInputs
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) <->
      AssembledFiveStartExclusionRows
        payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        intro n C hmin
        exact
          fiveStartExclusions_of_natLateTripleInputs
            (P :=
              (AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data)
            (H C hmin)
  case mpr =>
    intro H
    exact
      nonempty_assembledNatLateTripleInputsFamily_of_fiveStartExclusions
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) H

/-- A W20 source family projects to its pointwise finite natural-index
Lemma 9 input rows.  This is the source-field-level counterpart to the later
route-data projections. -/
def assembledNatLateTripleInputsFamilyOfSourceFamily
    (F :
      Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8NatLateTripleInputs
          (AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 C hmin).localLabels.predicates.data :=
  fun C hmin =>
    natLateTripleInputsOfSourceFields
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) (Cw := C) (hminw := hmin)
      (F.row C hmin)

/-- Nonempty W20 source-family rows project to nonempty pointwise nat-late
input rows. -/
theorem nonempty_assembledNatLateTripleInputsFamily_of_sourceFamily
    (h :
      Nonempty
        (Lemma9NatLateTripleSourceFamily.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          M8NatLateTripleInputs
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) := by
  cases h with
  | intro F =>
      exact
        Nonempty.intro
          (assembledNatLateTripleInputsFamilyOfSourceFamily
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8) F)

/-- A W20 source family projects to the concrete five-start no-early rows. -/
def assembledConcreteNoEarlyFamilyOfSourceFamily
    (F :
      Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8ConcreteNoEarlyTripleEquality
          (AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 C hmin).localLabels.predicates.data :=
  fun C hmin =>
    concreteNoEarlyTripleEqualityOfSourceFields
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) (Cw := C) (hminw := hmin)
      (F.row C hmin)

/-- A W20 source family projects to pointwise five-start exclusions. -/
def assembledFiveStartExclusionRowsOfSourceFamily
    (F :
      Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :
    AssembledFiveStartExclusionRows
      payForCut topologyArc lemma8 :=
  fun C hmin =>
    fiveStartExclusionsOfSourceFields
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) (Cw := C) (hminw := hmin)
      (F.row C hmin)

/-- W20 Lemma 9 source fields are exactly coverage plus no-early triples. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_noEarly :
    Nonempty
      (Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
            longArcCount) /\
          M8NoEarlyTripleEquality
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.longArcCount
            (And.intro
              (Nonempty.intro S.coverage)
              (noEarlyTripleEquality_of_natLateTripleInputs
                S.natLateTripleInputs))
  case mpr =>
    intro h
    cases h with
    | intro longArcCount hrow =>
        cases hrow.1 with
        | intro coverage =>
            exact
              Nonempty.intro
                (sourceFieldsOfCoverageAndNoEarly
                  (payForCut := payForCut)
                  (topologyArc := topologyArc)
                  (lemma8 := lemma8)
                  (Cw := Cw) (hminw := hminw)
                  longArcCount coverage hrow.2)

/-- W20 Lemma 9 source fields are exactly coverage plus positive finite
natural-index Lemma 9 rows. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_natLateTripleInputs :
    Nonempty
      (Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
            longArcCount) /\
          Nonempty
            (M8NatLateTripleInputs
              (AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.longArcCount
            (And.intro
              (Nonempty.intro S.coverage)
              (Nonempty.intro S.natLateTripleInputs))
  case mpr =>
    intro h
    cases h with
    | intro longArcCount hrow =>
        cases hrow.1 with
        | intro coverage =>
            cases hrow.2 with
            | intro natLateTripleInputs =>
                exact
                  Nonempty.intro
                    (sourceFieldsOfCoverageAndNatLateTripleInputs
                      (payForCut := payForCut)
                      (topologyArc := topologyArc)
                      (lemma8 := lemma8)
                      (Cw := Cw) (hminw := hminw)
                      longArcCount coverage natLateTripleInputs)

/-- W20 Lemma 9 source fields are exactly coverage plus raw late triples. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_lateTriples :
    Nonempty
      (Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
            longArcCount) /\
          M8BrokenLatticeLateTriples
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.longArcCount
            (And.intro
              (Nonempty.intro S.coverage)
              S.natLateTripleInputs.lateTriples)
  case mpr =>
    intro h
    cases h with
    | intro longArcCount hrow =>
        cases hrow.1 with
        | intro coverage =>
            exact
              Nonempty.intro
                (sourceFieldsOfCoverageAndLateTriples
                  (payForCut := payForCut)
                  (topologyArc := topologyArc)
                  (lemma8 := lemma8)
                  (Cw := Cw) (hminw := hminw)
                  longArcCount coverage hrow.2)

/-- W20 Lemma 9 source fields are exactly coverage plus the concrete
five-start no-early package. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_concreteNoEarly :
    Nonempty
      (Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
            longArcCount) /\
          M8ConcreteNoEarlyTripleEquality
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.longArcCount
            (And.intro
              (Nonempty.intro S.coverage)
              (concreteNoEarlyTripleEquality_of_natLateTripleInputs
                S.natLateTripleInputs))
  case mpr =>
    intro h
    cases h with
    | intro longArcCount hrow =>
        cases hrow.1 with
        | intro coverage =>
            exact
              Nonempty.intro
                (sourceFieldsOfCoverageAndConcreteNoEarly
                  (payForCut := payForCut)
                  (topologyArc := topologyArc)
                  (lemma8 := lemma8)
            (Cw := Cw) (hminw := hminw)
            longArcCount coverage hrow.2)

/-- W20 Lemma 9 source fields are exactly coverage plus the five explicit
early-start exclusions. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_fiveStartExclusions :
    Nonempty
      (Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 Cw hminw).arcBoundaryBudget.planarBoundary
            longArcCount) /\
          Not (((AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
            start1) /\
          Not (((AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
            start2) /\
          Not (((AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
            start3) /\
          Not (((AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
            start4) /\
          Not (((AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data).tripleEquality
            start5) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        have hno :
            M8ConcreteNoEarlyTripleEquality
              (AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data :=
          concreteNoEarlyTripleEquality_of_natLateTripleInputs
            S.natLateTripleInputs
        exact
          Exists.intro S.longArcCount
            (And.intro
              (Nonempty.intro S.coverage)
              (And.intro hno.no_start1
                (And.intro hno.no_start2
                  (And.intro hno.no_start3
                    (And.intro hno.no_start4 hno.no_start5)))))
  case mpr =>
    intro h
    cases h with
    | intro longArcCount hrow =>
        obtain ⟨hcoverage, h1, h2, h3, h4, h5⟩ := hrow
        cases hcoverage with
        | intro coverage =>
            exact
              Nonempty.intro
                (sourceFieldsOfCoverageAndFiveStartExclusions
                  (payForCut := payForCut)
                  (topologyArc := topologyArc)
                  (lemma8 := lemma8)
                  (Cw := Cw) (hminw := hminw)
                  longArcCount coverage h1 h2 h3 h4 h5)

/-- Source-family inhabitance is exactly pointwise coverage plus no-early
triples. -/
theorem nonempty_sourceFamily_iff_forall_exists_coverage_and_noEarly :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              M8NoEarlyTripleEquality
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) := by
  constructor
  case mp =>
    intro h n C hmin
    have hsource :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp h C hmin
    exact
      (nonempty_sourceFields_iff_exists_coverage_and_noEarly
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (Cw := C) (hminw := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_noEarly
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (Cw := C) (hminw := hmin)).mpr (h C hmin))

/-- Source-family inhabitance is exactly pointwise coverage plus positive
finite natural-index Lemma 9 rows. -/
theorem nonempty_sourceFamily_iff_forall_exists_coverage_and_natLateTripleInputs :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              Nonempty
                (M8NatLateTripleInputs
                  (AssembledLemma9PreLateBase
                    payForCut topologyArc lemma8 C hmin).localLabels.predicates.data)) := by
  constructor
  case mp =>
    intro h n C hmin
    have hsource :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp h C hmin
    exact
      (nonempty_sourceFields_iff_exists_coverage_and_natLateTripleInputs
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (Cw := C) (hminw := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_natLateTripleInputs
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (Cw := C) (hminw := hmin)).mpr (h C hmin))

/-- Source-family inhabitance is exactly pointwise coverage plus raw late
triples. -/
theorem nonempty_sourceFamily_iff_forall_exists_coverage_and_lateTriples :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              M8BrokenLatticeLateTriples
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) := by
  constructor
  case mp =>
    intro h n C hmin
    have hsource :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp h C hmin
    exact
      (nonempty_sourceFields_iff_exists_coverage_and_lateTriples
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (Cw := C) (hminw := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_lateTriples
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (Cw := C) (hminw := hmin)).mpr (h C hmin))

/-- Source-family inhabitance is exactly pointwise coverage plus the concrete
five-start no-early package. -/
theorem nonempty_sourceFamily_iff_forall_exists_coverage_and_concreteNoEarly :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              M8ConcreteNoEarlyTripleEquality
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) := by
  constructor
  case mp =>
    intro h n C hmin
    have hsource :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp h C hmin
    exact
      (nonempty_sourceFields_iff_exists_coverage_and_concreteNoEarly
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (Cw := C) (hminw := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_concreteNoEarly
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (Cw := C) (hminw := hmin)).mpr (h C hmin))

/-- Source-family inhabitance is exactly pointwise coverage plus the five
explicit early-start exclusions. -/
theorem nonempty_sourceFamily_iff_forall_exists_coverage_and_fiveStartExclusions :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start1) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start2) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start3) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start4) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start5)) := by
  constructor
  case mp =>
    intro h n C hmin
    have hsource :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp h C hmin
    exact
      (nonempty_sourceFields_iff_exists_coverage_and_fiveStartExclusions
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (Cw := C) (hminw := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_fiveStartExclusions
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (Cw := C) (hminw := hmin)).mpr (h C hmin))

/-- Constructor form of
`nonempty_sourceFamily_iff_forall_exists_coverage_and_fiveStartExclusions`. -/
theorem nonempty_sourceFamily_of_forall_exists_coverage_and_fiveStartExclusions
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start1) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start2) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start3) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start4) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start5)) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  (nonempty_sourceFamily_iff_forall_exists_coverage_and_fiveStartExclusions
    (payForCut := payForCut)
    (topologyArc := topologyArc)
    (lemma8 := lemma8)).mpr H

/-- The W20 Lemma 9 producer family is exactly pointwise coverage plus
no-early triples. -/
theorem nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_exists_coverage_and_noEarly :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              M8NoEarlyTripleEquality
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) := by
  constructor
  case mp =>
    intro h n C hmin
    have hsource :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp h C hmin
    exact
      (nonempty_sourceFields_iff_exists_coverage_and_noEarly
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (Cw := C) (hminw := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_noEarly
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (Cw := C) (hminw := hmin)).mpr (h C hmin))

/-- The W20 Lemma 9 producer family is exactly pointwise coverage plus
positive finite natural-index Lemma 9 rows. -/
theorem nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_exists_coverage_and_natLateTripleInputs :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              Nonempty
                (M8NatLateTripleInputs
                  (AssembledLemma9PreLateBase
                    payForCut topologyArc lemma8 C hmin).localLabels.predicates.data)) := by
  constructor
  case mp =>
    intro h n C hmin
    have hsource :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp h C hmin
    exact
      (nonempty_sourceFields_iff_exists_coverage_and_natLateTripleInputs
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (Cw := C) (hminw := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_natLateTripleInputs
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (Cw := C) (hminw := hmin)).mpr (h C hmin))

/-- The W20 Lemma 9 producer family is exactly pointwise coverage plus the
concrete five-start no-early package. -/
theorem
    nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_exists_coverage_and_concreteNoEarly :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              M8ConcreteNoEarlyTripleEquality
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) := by
  constructor
  case mp =>
    intro h n C hmin
    have hsource :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp h C hmin
    exact
      (nonempty_sourceFields_iff_exists_coverage_and_concreteNoEarly
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (Cw := C) (hminw := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_concreteNoEarly
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (Cw := C) (hminw := hmin)).mpr (h C hmin))

/-- The W20 Lemma 9 producer family is exactly pointwise coverage plus the
five explicit early-start exclusions. -/
theorem
    nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_exists_coverage_and_fiveStartExclusions :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start1) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start2) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start3) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start4) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start5)) := by
  constructor
  case mp =>
    intro h n C hmin
    have hsource :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp h C hmin
    exact
      (nonempty_sourceFields_iff_exists_coverage_and_fiveStartExclusions
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (Cw := C) (hminw := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_fiveStartExclusions
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (Cw := C) (hminw := hmin)).mpr (h C hmin))

/-- Constructor form of
`nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_exists_coverage_and_fiveStartExclusions`.
-/
theorem
    nonempty_lemma9CoverageConcreteProducerFamily_of_forall_exists_coverage_and_fiveStartExclusions
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start1) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start2) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start3) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start4) /\
              Not (((AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data).tripleEquality
                start5)) :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_exists_coverage_and_fiveStartExclusions
    (payForCut := payForCut)
    (topologyArc := topologyArc)
    (lemma8 := lemma8)).mpr H

/-- The W20 Lemma 9 producer family is exactly pointwise coverage plus raw
late triples. -/
theorem nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_exists_coverage_and_lateTriples :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          exists longArcCount : Nat,
            Nonempty
              (GapNegativeCoverageData
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
                longArcCount) /\
              M8BrokenLatticeLateTriples
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) := by
  constructor
  case mp =>
    intro h n C hmin
    have hsource :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp h C hmin
    exact
      (nonempty_sourceFields_iff_exists_coverage_and_lateTriples
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (Cw := C) (hminw := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_lateTriples
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (Cw := C) (hminw := hmin)).mpr (h C hmin))

/-! ## No-go lemmas for the residual finite-natural side -/

/-- If no-early triples are unavailable, finite natural Lemma 9 data is
unavailable. -/
theorem not_natLateTripleInputs_of_not_noEarlyTripleEquality
    (hno :
      Not (M8NoEarlyTripleEquality P)) :
    Not (Nonempty (M8NatLateTripleInputs P)) := by
  intro h
  exact hno
    ((nonempty_natLateTripleInputs_iff_noEarlyTripleEquality
      (P := P)).mp h)

/-- If no-early triples are unavailable for a row, the W20 Lemma 9 source row
is unavailable regardless of coverage. -/
theorem not_sourceFields_of_not_noEarlyTripleEquality
    (hno :
      Not
        (M8NoEarlyTripleEquality
          (AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 Cw hminw).localLabels.predicates.data)) :
    Not
      (Nonempty
        (Lemma9NatLateTripleSourceFields.{u}
          payForCut topologyArc lemma8 Cw hminw)) := by
  intro h
  exact hno
    ((nonempty_sourceFields_iff_exists_coverage_and_noEarly
      (payForCut := payForCut)
      (topologyArc := topologyArc)
      (lemma8 := lemma8)
      (Cw := Cw) (hminw := hminw)).mp h |>.choose_spec).2

/-- A single row with missing no-early triples rules out the whole W20 source
family. -/
theorem not_sourceFamily_of_exists_not_noEarlyTripleEquality
    (hbad :
      exists n : Nat,
        exists C : _root_.UDConfig n,
          exists hmin : IsMinimalClearedFailure C,
            Not
              (M8NoEarlyTripleEquality
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).localLabels.predicates.data)) :
    Not
      (Nonempty
        (Lemma9NatLateTripleSourceFamily.{u}
          payForCut topologyArc lemma8)) := by
  intro hsource
  cases hbad with
  | intro n hrest =>
      cases hrest with
      | intro C hrestC =>
          cases hrestC with
          | intro hmin hno =>
              have hrow :
                  Nonempty
                    (Lemma9NatLateTripleSourceFields.{u}
                      payForCut topologyArc lemma8 C hmin) :=
                (nonempty_sourceFamily_iff_forall_sourceFields
                  (payForCut := payForCut)
                  (topologyArc := topologyArc)
                  (lemma8 := lemma8)).mp hsource C hmin
              exact
                not_sourceFields_of_not_noEarlyTripleEquality
                  (payForCut := payForCut)
                  (topologyArc := topologyArc)
                  (lemma8 := lemma8)
                  (Cw := C) (hminw := hmin)
                  hno hrow

/-- A single row with missing no-early triples rules out the W20 Lemma 9
concrete producer family. -/
theorem not_lemma9CoverageConcreteProducerFamily_of_exists_not_noEarlyTripleEquality
    (hbad :
      exists n : Nat,
        exists C : _root_.UDConfig n,
          exists hmin : IsMinimalClearedFailure C,
            Not
              (M8NoEarlyTripleEquality
                (AssembledLemma9PreLateBase
                  payForCut topologyArc lemma8 C hmin).localLabels.predicates.data)) :
    Not
      (Nonempty
        (W18Lemma9CoverageConcreteProducerFamily.{u}
          payForCut topologyArc lemma8)) := by
  intro hproducer
  cases hbad with
  | intro n hrest =>
      cases hrest with
      | intro C hrestC =>
          cases hrestC with
          | intro hmin hno =>
              have hrow :
                  Nonempty
                    (Lemma9NatLateTripleSourceFields.{u}
                      payForCut topologyArc lemma8 C hmin) :=
                (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
                  (payForCut := payForCut)
                  (topologyArc := topologyArc)
                  (lemma8 := lemma8)).mp hproducer C hmin
              exact
                not_sourceFields_of_not_noEarlyTripleEquality
                  (payForCut := payForCut)
                  (topologyArc := topologyArc)
                  (lemma8 := lemma8)
                  (Cw := C) (hminw := hmin)
                  hno hrow

end Lemma9NatLateTripleInhabitationW22
end Swanepoel
end ErdosProblems1066

end
