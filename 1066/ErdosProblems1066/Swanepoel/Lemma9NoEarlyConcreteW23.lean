import ErdosProblems1066.Swanepoel.K23NoEarlyClosure
import ErdosProblems1066.Swanepoel.Lemma9NatLateTripleInhabitationW22

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W23 concrete no-early reductions for Lemma 9

This file keeps the W22 Lemma 9 natural late-triple package as the central
interface and routes concrete no-early evidence into it.  The row-level
constructors below turn false-start, indexed obstruction, K23 obstruction,
common-neighbor, and K23 closure packages into the no-early side consumed by
`Lemma9NatLateTripleInhabitationW22`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9NoEarlyConcreteW23

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
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NoEarlyTripleObstructionConcrete

universe u

variable {V : Type u} {G : LocalGraph V}
variable {P : BrokenLatticePredicates G 8}

/-! ## Pointwise no-early interfaces -/

/-- The abstract no-early predicate is equivalent to the concrete five-start
package. -/
theorem noEarlyTripleEquality_iff_concreteNoEarlyTripleEquality :
    M8NoEarlyTripleEquality P <->
      M8ConcreteNoEarlyTripleEquality P := by
  constructor
  case mp =>
    intro hno
    exact
      (Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_concreteNoEarlyTripleEquality
        (P := P)).mp
        ((Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_noEarlyTripleEquality
          (P := P)).mpr hno)
  case mpr =>
    intro H
    exact H.toNoEarlyTripleEquality

/-- The abstract no-early predicate is equivalent to explicit false-start
implications. -/
theorem noEarlyTripleEquality_iff_falseStartImplications :
    M8NoEarlyTripleEquality P <->
      M8ConcreteFalseStartImplications P := by
  constructor
  case mp =>
    intro hno
    exact
      (Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_falseStartImplications
        (P := P)).mp
        ((Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_noEarlyTripleEquality
          (P := P)).mpr hno)
  case mpr =>
    intro H
    exact H.toNoEarlyTripleEquality

/-- The abstract no-early predicate is equivalent to inhabited indexed
early-obstruction data. -/
theorem noEarlyTripleEquality_iff_indexedObstructionInputs :
    M8NoEarlyTripleEquality P <->
      Nonempty (M8ConcreteIndexedObstructionInputs P) := by
  constructor
  case mp =>
    intro hno
    exact
      (Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_indexedObstructionInputs
        (P := P)).mp
        ((Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_noEarlyTripleEquality
          (P := P)).mpr hno)
  case mpr =>
    intro H
    exact
      (Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_noEarlyTripleEquality
        (P := P)).mp
        ((Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_indexedObstructionInputs
          (P := P)).mpr H)

/-- Explicit false-start implications build finite natural Lemma 9 inputs. -/
def natLateTripleInputs_from_falseStartImplications
    (H : M8ConcreteFalseStartImplications P) :
    M8NatLateTripleInputs P :=
  Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_falseStartImplications
    H

/-- Indexed early obstructions build finite natural Lemma 9 inputs. -/
def natLateTripleInputs_from_indexedObstructionInputs
    (H : M8ConcreteIndexedObstructionInputs P) :
    M8NatLateTripleInputs P :=
  Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_indexedObstructionInputs
    H

/-- K23 obstruction data plus finite local exclusions build finite natural
Lemma 9 inputs. -/
def natLateTripleInputs_from_K23Obstruction
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8NatLateTripleInputs P :=
  Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_concreteNoEarlyTripleEquality
    (concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
      H E)

/-- Common-neighbor lower-bound obstruction data plus finite local exclusions
build finite natural Lemma 9 inputs. -/
def natLateTripleInputs_from_commonNeighborCardObstruction
    [Fintype V] [DecidableEq V]
    (H : K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8NatLateTripleInputs P :=
  Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_concreteNoEarlyTripleEquality
    (K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs.toConcreteNoEarlyTripleEquality
      H E)

/-- A packaged K23 obstruction plus arc/angle data gives the W22 finite
natural Lemma 9 input through its no-early component. -/
def natLateTripleInputs_from_K23ArcAngleObstructionData
    (Q : M8HonestLocalPredicates G)
    [Fintype V] [DecidableEq V]
    (D : M8ConcreteK23ArcAngleObstructionData Q) :
    M8NatLateTripleInputs Q.data :=
  Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_concreteNoEarlyTripleEquality
    D.toConcreteNoEarlyTripleEquality

/-- K23 turn/window obstruction data gives the W22 finite natural Lemma 9
input for its local labels. -/
def natLateTripleInputs_from_K23TurnWindowObstructionData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8NatLateTripleInputs D.localLabels.predicates.data :=
  Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_noEarlyTripleEquality
    D.noEarlyTripleEquality

/-- Exact K23 closure fields give the W22 finite natural Lemma 9 input for
their local labels. -/
def natLateTripleInputs_from_minimalFailureK23TurnWindowFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : K23NoEarlyClosure.MinimalFailureK23TurnWindowFields C hmin) :
    M8NatLateTripleInputs D.localLabels.predicates.data :=
  Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_concreteNoEarlyTripleEquality
    D.noEarlyTriples

/-- Exact common-neighbor closure fields give the W22 finite natural Lemma 9
input for their local labels. -/
def natLateTripleInputs_from_minimalFailureCommonNeighborTurnWindowFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D :
      K23NoEarlyClosure.MinimalFailureCommonNeighborTurnWindowFields C hmin) :
    M8NatLateTripleInputs D.localLabels.predicates.data :=
  Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_concreteNoEarlyTripleEquality
    D.noEarlyTriples

/-- K23 obstruction data plus finite local exclusions give the pipeline
late-triples field through `M8LateTriplesConcrete`. -/
def lateTriplesField_from_K23Obstruction
    (Q : M8HonestLocalPredicates G)
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs Q.data)
    (E : FiniteLocalExclusionPackage G) :
    M8PipelineClosure.M8LateTriplesField Q :=
  M8LateTriplesConcrete.lateTriplesField_of_noEarlyTripleEquality Q
    (noEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions H E)

/-- Common-neighbor lower-bound obstruction data plus finite local exclusions
give the pipeline late-triples field through `M8LateTriplesConcrete`. -/
def lateTriplesField_from_commonNeighborCardObstruction
    (Q : M8HonestLocalPredicates G)
    [Fintype V] [DecidableEq V]
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs Q.data)
    (E : FiniteLocalExclusionPackage G) :
    M8PipelineClosure.M8LateTriplesField Q :=
  M8LateTriplesConcrete.lateTriplesField_of_noEarlyTripleEquality Q
    (K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs.toNoEarlyTripleEquality
      H E)

/-! ## Row-level W22 source reductions -/

abbrev rowBoundary
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  (AssembledLemma9PreLateBase
    payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary

abbrev rowPredicates
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  (AssembledLemma9PreLateBase
    payForCut topologyArc lemma8 C hmin).localLabels.predicates.data

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}
variable {nw : Nat} {Cw : _root_.UDConfig nw}
variable {hminw : IsMinimalClearedFailure Cw}

/-- W22 source fields are exactly coverage plus explicit false-start
implications. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_falseStartImplications :
    Nonempty
      (Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (rowBoundary payForCut topologyArc lemma8 Cw hminw)
            longArcCount) /\
          M8ConcreteFalseStartImplications
            (rowPredicates payForCut topologyArc lemma8 Cw hminw) := by
  constructor
  case mp =>
    intro hsource
    have hrow :=
      (Lemma9NatLateTripleInhabitationW22.nonempty_sourceFields_iff_exists_coverage_and_noEarly
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)).mp hsource
    cases hrow with
    | intro longArcCount hspec =>
        exact
          Exists.intro longArcCount
            (And.intro hspec.1
              ((noEarlyTripleEquality_iff_falseStartImplications
                (P := rowPredicates payForCut topologyArc lemma8 Cw hminw)).mp
                hspec.2))
  case mpr =>
    intro hrow
    cases hrow with
    | intro longArcCount hspec =>
        exact
          (Lemma9NatLateTripleInhabitationW22.nonempty_sourceFields_iff_exists_coverage_and_noEarly
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)).mpr
            (Exists.intro longArcCount
              (And.intro hspec.1
                ((noEarlyTripleEquality_iff_falseStartImplications
                  (P := rowPredicates payForCut topologyArc lemma8 Cw hminw)).mpr
                  hspec.2)))

/-- W22 source fields are exactly coverage plus inhabited indexed
early-obstruction data. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_indexedObstructionInputs :
    Nonempty
      (Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 Cw hminw) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (rowBoundary payForCut topologyArc lemma8 Cw hminw)
            longArcCount) /\
          Nonempty
            (M8ConcreteIndexedObstructionInputs
              (rowPredicates payForCut topologyArc lemma8 Cw hminw)) := by
  constructor
  case mp =>
    intro hsource
    have hrow :=
      (Lemma9NatLateTripleInhabitationW22.nonempty_sourceFields_iff_exists_coverage_and_noEarly
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)).mp hsource
    cases hrow with
    | intro longArcCount hspec =>
        exact
          Exists.intro longArcCount
            (And.intro hspec.1
              ((noEarlyTripleEquality_iff_indexedObstructionInputs
                (P := rowPredicates payForCut topologyArc lemma8 Cw hminw)).mp
                hspec.2))
  case mpr =>
    intro hrow
    cases hrow with
    | intro longArcCount hspec =>
        exact
          (Lemma9NatLateTripleInhabitationW22.nonempty_sourceFields_iff_exists_coverage_and_noEarly
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)).mpr
            (Exists.intro longArcCount
              (And.intro hspec.1
                ((noEarlyTripleEquality_iff_indexedObstructionInputs
                  (P := rowPredicates payForCut topologyArc lemma8 Cw hminw)).mpr
                  hspec.2)))

/-- Build a W22 source row from coverage and explicit false-start
implications. -/
def sourceFieldsFromCoverageAndFalseStartImplications
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (rowBoundary payForCut topologyArc lemma8 Cw hminw)
        longArcCount)
    (H :
      M8ConcreteFalseStartImplications
        (rowPredicates payForCut topologyArc lemma8 Cw hminw)) :
    Lemma9NatLateTripleSourceFields.{u}
      payForCut topologyArc lemma8 Cw hminw :=
  Lemma9NatLateTripleInhabitationW22.sourceFieldsOfCoverageAndNoEarly
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)
    longArcCount coverage H.toNoEarlyTripleEquality

/-- Build a W22 source row from coverage and indexed early obstructions. -/
def sourceFieldsFromCoverageAndIndexedObstructionInputs
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (rowBoundary payForCut topologyArc lemma8 Cw hminw)
        longArcCount)
    (H :
      M8ConcreteIndexedObstructionInputs
        (rowPredicates payForCut topologyArc lemma8 Cw hminw)) :
    Lemma9NatLateTripleSourceFields.{u}
      payForCut topologyArc lemma8 Cw hminw :=
  Lemma9NatLateTripleInhabitationW22.sourceFieldsOfCoverageAndNoEarly
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)
    longArcCount coverage H.toNoEarlyTripleEquality

/-- Build a W22 source row from coverage and a K23 obstruction, using the
unit-distance finite local exclusions for the row configuration. -/
def sourceFieldsFromCoverageAndK23Obstruction
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (rowBoundary payForCut topologyArc lemma8 Cw hminw)
        longArcCount)
    (H :
      M8ConcreteK23ObstructionInputs
        (rowPredicates payForCut topologyArc lemma8 Cw hminw)) :
    Lemma9NatLateTripleSourceFields.{u}
      payForCut topologyArc lemma8 Cw hminw :=
  Lemma9NatLateTripleInhabitationW22.sourceFieldsOfCoverageAndConcreteNoEarly
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)
    longArcCount coverage
    (concreteNoEarlyTripleEquality_of_K23Obstruction_and_unitDistanceConfig
      (C := Cw) H)

/-- Build a W22 source row from coverage and common-neighbor obstruction data,
using the minimal-failure local exclusions for the row. -/
def sourceFieldsFromCoverageAndCommonNeighborCardObstruction
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (rowBoundary payForCut topologyArc lemma8 Cw hminw)
        longArcCount)
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
        (rowPredicates payForCut topologyArc lemma8 Cw hminw)) :
    Lemma9NatLateTripleSourceFields.{u}
      payForCut topologyArc lemma8 Cw hminw :=
  Lemma9NatLateTripleInhabitationW22.sourceFieldsOfCoverageAndConcreteNoEarly
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)
    longArcCount coverage
    (K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs.toConcreteNoEarlyTripleEquality
      H
      (K23ObstructionConcrete.finiteLocalExclusionPackage_of_minimalFailure_noAssumptions
        hminw))

/-! ## Contrapositive no-go forms -/

/-- If the concrete five-start package is unavailable, W22 finite natural
Lemma 9 inputs are unavailable. -/
theorem not_natLateTripleInputs_of_not_concreteNoEarlyTripleEquality
    (hbad : Not (M8ConcreteNoEarlyTripleEquality P)) :
    Not (Nonempty (M8NatLateTripleInputs P)) := by
  intro hnat
  exact hbad
    ((Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_concreteNoEarlyTripleEquality
      (P := P)).mp hnat)

/-- If explicit false-start implications are unavailable, W22 finite natural
Lemma 9 inputs are unavailable. -/
theorem not_natLateTripleInputs_of_not_falseStartImplications
    (hbad : Not (M8ConcreteFalseStartImplications P)) :
    Not (Nonempty (M8NatLateTripleInputs P)) := by
  intro hnat
  exact hbad
    ((Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_falseStartImplications
      (P := P)).mp hnat)

/-- If indexed early-obstruction data is unavailable, W22 finite natural
Lemma 9 inputs are unavailable. -/
theorem not_natLateTripleInputs_of_not_indexedObstructionInputs
    (hbad : Not (Nonempty (M8ConcreteIndexedObstructionInputs P))) :
    Not (Nonempty (M8NatLateTripleInputs P)) := by
  intro hnat
  exact hbad
    ((Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_indexedObstructionInputs
      (P := P)).mp hnat)

/-- If explicit false-start implications are unavailable for the assembled
row, the W22 source row is unavailable. -/
theorem not_sourceFields_of_not_falseStartImplications
    (hbad :
      Not
        (M8ConcreteFalseStartImplications
          (rowPredicates payForCut topologyArc lemma8 Cw hminw))) :
    Not
      (Nonempty
        (Lemma9NatLateTripleSourceFields.{u}
          payForCut topologyArc lemma8 Cw hminw)) := by
  intro hsource
  exact hbad
    ((nonempty_sourceFields_iff_exists_coverage_and_falseStartImplications
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)).mp
      hsource |>.choose_spec).2

/-- If indexed early-obstruction data is unavailable for the assembled row,
the W22 source row is unavailable. -/
theorem not_sourceFields_of_not_indexedObstructionInputs
    (hbad :
      Not
        (Nonempty
          (M8ConcreteIndexedObstructionInputs
            (rowPredicates payForCut topologyArc lemma8 Cw hminw)))) :
    Not
      (Nonempty
        (Lemma9NatLateTripleSourceFields.{u}
          payForCut topologyArc lemma8 Cw hminw)) := by
  intro hsource
  exact hbad
    ((nonempty_sourceFields_iff_exists_coverage_and_indexedObstructionInputs
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)).mp
      hsource |>.choose_spec).2

/-- Under finite local exclusions, failure of the abstract no-early predicate
rules out the K23 obstruction route. -/
theorem not_K23Obstruction_of_not_noEarlyTripleEquality
    [Fintype V] [DecidableEq V]
    (E : FiniteLocalExclusionPackage G)
    (hbad : Not (M8NoEarlyTripleEquality P)) :
    Not (M8ConcreteK23ObstructionInputs P) := by
  intro H
  exact hbad
    (noEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions H E)

/-- Under finite local exclusions, failure of the abstract no-early predicate
rules out the common-neighbor obstruction route. -/
theorem not_commonNeighborCardObstruction_of_not_noEarlyTripleEquality
    [Fintype V] [DecidableEq V]
    (E : FiniteLocalExclusionPackage G)
    (hbad : Not (M8NoEarlyTripleEquality P)) :
    Not
      (Nonempty
        (K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs P)) := by
  intro H
  cases H with
  | intro Hrow =>
      exact hbad
        (K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs.toNoEarlyTripleEquality
          Hrow E)

/-- If a covered W22 row is still impossible, then the K23 obstruction route
cannot supply the missing no-early side for that row. -/
theorem not_K23Obstruction_of_coverage_and_not_sourceFields
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (rowBoundary payForCut topologyArc lemma8 Cw hminw)
        longArcCount)
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 Cw hminw))) :
    Not
      (M8ConcreteK23ObstructionInputs
        (rowPredicates payForCut topologyArc lemma8 Cw hminw)) := by
  intro H
  exact hbad
    (Nonempty.intro
      (sourceFieldsFromCoverageAndK23Obstruction
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)
        longArcCount coverage H))

/-- If a covered W22 row is still impossible, then the common-neighbor route
cannot supply the missing no-early side for that row. -/
theorem not_commonNeighborCardObstruction_of_coverage_and_not_sourceFields
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (rowBoundary payForCut topologyArc lemma8 Cw hminw)
        longArcCount)
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 Cw hminw))) :
    Not
      (Nonempty
        (K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
          (rowPredicates payForCut topologyArc lemma8 Cw hminw))) := by
  intro H
  cases H with
  | intro Hrow =>
      exact hbad
        (Nonempty.intro
          (sourceFieldsFromCoverageAndCommonNeighborCardObstruction
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8) (Cw := Cw) (hminw := hminw)
            longArcCount coverage Hrow))

end Lemma9NoEarlyConcreteW23
end Swanepoel
end ErdosProblems1066

end
