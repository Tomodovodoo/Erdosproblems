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

/-- Extract the concrete five-start no-early package from finite natural
Lemma 9 data. -/
def concreteNoEarlyTripleEquality_of_natLateTripleInputs
    (H : M8NatLateTripleInputs P) :
    M8ConcreteNoEarlyTripleEquality P :=
  concreteNoEarlyTripleEquality_of_natLateTripleInputs H

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
      M8ConcreteIndexedObstructionInputs P := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact indexedObstructionInputs_of_natLateTripleInputs H
  case mpr =>
    intro H
    exact
      Nonempty.intro
        (natLateTripleInputs_of_indexedObstructionInputs H)

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
    M8NatLateTripleInputs P :=
  natLateTripleInputs_of_noEarlyTripleEquality H.noEarlyTripleEquality

/-- Finite natural-index Lemma 9 data is equivalent to abstract early
obstruction data. -/
theorem nonempty_natLateTripleInputs_iff_earlyTripleObstructionInputs :
    Nonempty (M8NatLateTripleInputs P) <->
      M8EarlyTripleObstructionInputs P := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact earlyTripleObstructionInputs_of_natLateTripleInputs H
  case mpr =>
    intro H
    exact
      Nonempty.intro
        (natLateTripleInputs_of_earlyTripleObstructionInputs H)

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
