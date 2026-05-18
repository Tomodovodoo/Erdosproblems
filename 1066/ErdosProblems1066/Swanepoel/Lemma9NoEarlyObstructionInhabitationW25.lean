import ErdosProblems1066.Swanepoel.Lemma9NoEarlyInhabitationW24

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W25 Lemma 9 no-early obstruction inhabitation

This file keeps the W24 `M8ConcreteNoEarlyObstructionPackage` as the no-early
interface and pushes it to the W20 Lemma 9 source rows.  The source-row
boundary is exact: a source row is inhabited precisely by a checked coverage
row together with the W24 obstruction package.  The K23/common-neighbor
constructors use the existing minimal-failure finite local exclusions.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9NoEarlyObstructionInhabitationW25

open LateTriplesInterface
open Lemma10Bridge
open Lemma6Lemma7AssemblyW13
open Lemma9NoEarlyInhabitationW24
open Lemma9ProducerFamilyW20
open LocalConfigurations
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoEarlyTripleObstructionConcrete

universe u

variable {V : Type u} {G : LocalGraph V}
variable {P : BrokenLatticePredicates G 8}

/-! ## Pointwise W24 obstruction package routes -/

/-- The W24 obstruction package is exactly the explicit false-start package. -/
theorem obstructionPackage_iff_falseStartImplications
    [Fintype V] [DecidableEq V] :
    M8ConcreteNoEarlyObstructionPackage P <->
      M8ConcreteFalseStartImplications P :=
  M8ConcreteNoEarlyObstructionPackage.iff_falseStartImplications

/-- The W24 obstruction package is exactly inhabited indexed finite
early-obstruction data. -/
theorem obstructionPackage_iff_indexedObstructionInputs
    [Fintype V] [DecidableEq V] :
    M8ConcreteNoEarlyObstructionPackage P <->
      Nonempty (M8ConcreteIndexedObstructionInputs P) :=
  M8ConcreteNoEarlyObstructionPackage.iff_indexedObstructionInputs

/-- K23 obstruction data plus finite local exclusions inhabit the W24
obstruction package. -/
def obstructionPackageOfK23AndFiniteLocalExclusions
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteK23ObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8ConcreteNoEarlyObstructionPackage P :=
  M8ConcreteNoEarlyObstructionPackage.k23 H E

/-- Three-common-neighbor data plus finite local exclusions inhabit the W24
obstruction package through K23. -/
def obstructionPackageOfThreeCommonNeighborAndFiniteLocalExclusions
    [Fintype V] [DecidableEq V]
    (H : K23ObstructionConcrete.M8ConcreteThreeCommonNeighborObstructionInputs
      P)
    (E : FiniteLocalExclusionPackage G) :
    M8ConcreteNoEarlyObstructionPackage P :=
  M8ConcreteNoEarlyObstructionPackage.k23 H.toK23ObstructionInputs E

/-- Common-neighbor-card lower bounds plus finite local exclusions inhabit
the W24 obstruction package. -/
def obstructionPackageOfCommonNeighborAndFiniteLocalExclusions
    [Fintype V] [DecidableEq V]
    (H : K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8ConcreteNoEarlyObstructionPackage P :=
  M8ConcreteNoEarlyObstructionPackage.commonNeighbor H E

/-! ## Row-level source packages -/

abbrev RowBoundary
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  Lemma9NoEarlyConcreteW23.rowBoundary
    payForCut topologyArc lemma8 C hmin

abbrev RowPredicates
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  Lemma9NoEarlyConcreteW23.rowPredicates
    payForCut topologyArc lemma8 C hmin

abbrev SourceFields
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  Lemma9NatLateTripleSourceFields.{u}
    payForCut topologyArc lemma8 C hmin

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}
variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Coverage plus the W24 obstruction package gives the actual W20 Lemma 9
source row. -/
def sourceFieldsFromCoverageAndObstructionPackage
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (RowBoundary payForCut topologyArc lemma8 C hmin)
        longArcCount)
    (H :
      M8ConcreteNoEarlyObstructionPackage
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  Lemma9NatLateTripleInhabitationW22.sourceFieldsOfCoverageAndConcreteNoEarly
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Cw := C) (hminw := hmin)
    longArcCount coverage H.toConcreteNoEarlyTripleEquality

/-- Coverage plus false-start implications gives the actual W20 Lemma 9
source row. -/
def sourceFieldsFromCoverageAndFalseStartImplications
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (RowBoundary payForCut topologyArc lemma8 C hmin)
        longArcCount)
    (H :
      M8ConcreteFalseStartImplications
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  sourceFieldsFromCoverageAndObstructionPackage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (C := C) (hmin := hmin)
    longArcCount coverage
    (M8ConcreteNoEarlyObstructionPackage.falseStart H)

/-- Coverage plus indexed finite obstructions gives the actual W20 Lemma 9
source row. -/
def sourceFieldsFromCoverageAndIndexedObstructionInputs
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (RowBoundary payForCut topologyArc lemma8 C hmin)
        longArcCount)
    (H :
      M8ConcreteIndexedObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  sourceFieldsFromCoverageAndObstructionPackage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (C := C) (hmin := hmin)
    longArcCount coverage
    (M8ConcreteNoEarlyObstructionPackage.indexed H)

/-- Coverage plus K23 obstruction data gives the actual W20 Lemma 9 source
row, using the finite local exclusions already available for minimal
unit-distance failures. -/
def sourceFieldsFromCoverageAndK23Obstruction
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (RowBoundary payForCut topologyArc lemma8 C hmin)
        longArcCount)
    (H :
      M8ConcreteK23ObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  sourceFieldsFromCoverageAndObstructionPackage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (C := C) (hmin := hmin)
    longArcCount coverage
    (M8ConcreteNoEarlyObstructionPackage.k23 H
      (K23ObstructionConcrete.finiteLocalExclusionPackage_of_minimalFailure_noAssumptions
        hmin))

/-- Coverage plus three-common-neighbor obstruction data gives the actual W20
Lemma 9 source row through K23. -/
def sourceFieldsFromCoverageAndThreeCommonNeighborObstruction
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (RowBoundary payForCut topologyArc lemma8 C hmin)
        longArcCount)
    (H :
      K23ObstructionConcrete.M8ConcreteThreeCommonNeighborObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  sourceFieldsFromCoverageAndK23Obstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (C := C) (hmin := hmin)
    longArcCount coverage H.toK23ObstructionInputs

/-- Coverage plus common-neighbor-card lower-bound data gives the actual W20
Lemma 9 source row, using the finite local exclusions already available for
minimal unit-distance failures. -/
def sourceFieldsFromCoverageAndCommonNeighborCardObstruction
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (RowBoundary payForCut topologyArc lemma8 C hmin)
        longArcCount)
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  sourceFieldsFromCoverageAndObstructionPackage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (C := C) (hmin := hmin)
    longArcCount coverage
    (M8ConcreteNoEarlyObstructionPackage.commonNeighbor H
      (K23ObstructionConcrete.finiteLocalExclusionPackage_of_minimalFailure_noAssumptions
        hmin))

/-- The exact W25 row package: checked coverage plus the W24 no-early
obstruction package. -/
structure M8ConcreteNoEarlySourceRow
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) where
  longArcCount : Nat
  coverage :
    GapNegativeCoverageData
      (RowBoundary payForCut topologyArc lemma8 C hmin)
      longArcCount
  obstruction :
    M8ConcreteNoEarlyObstructionPackage
      (RowPredicates payForCut topologyArc lemma8 C hmin)

namespace M8ConcreteNoEarlySourceRow

/-- Forget the W25 row package to the W20 Lemma 9 source row. -/
def toSourceFields
    (R : M8ConcreteNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  sourceFieldsFromCoverageAndObstructionPackage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (C := C) (hmin := hmin)
    R.longArcCount R.coverage R.obstruction

end M8ConcreteNoEarlySourceRow

/-- Exact source-row boundary: W20 Lemma 9 source fields are inhabited iff
there is checked coverage and the W24 obstruction package. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_obstructionPackage :
    Nonempty (SourceFields payForCut topologyArc lemma8 C hmin) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (RowBoundary payForCut topologyArc lemma8 C hmin)
            longArcCount) /\
          M8ConcreteNoEarlyObstructionPackage
            (RowPredicates payForCut topologyArc lemma8 C hmin) := by
  constructor
  case mp =>
    intro hsource
    have hrow :=
      (Lemma9NatLateTripleInhabitationW22.nonempty_sourceFields_iff_exists_coverage_and_concreteNoEarly
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) (Cw := C) (hminw := hmin)).mp hsource
    rcases hrow with ⟨longArcCount, hcoverage, hnoEarly⟩
    exact
      ⟨longArcCount, hcoverage,
        (M8ConcreteNoEarlyObstructionPackage.iff_concreteNoEarlyTripleEquality
          (P := RowPredicates payForCut topologyArc lemma8 C hmin)).mpr
          hnoEarly⟩
  case mpr =>
    intro hrow
    rcases hrow with ⟨longArcCount, hcoverage, Hobstruction⟩
    rcases hcoverage with ⟨coverage⟩
    exact
      Nonempty.intro
        (sourceFieldsFromCoverageAndObstructionPackage
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8) (C := C) (hmin := hmin)
          longArcCount coverage Hobstruction)

/-- The W25 source-row package has exactly the same inhabitation content as
the W20 Lemma 9 source row. -/
theorem nonempty_sourceFields_iff_obstructionSourceRow :
    Nonempty (SourceFields payForCut topologyArc lemma8 C hmin) <->
      Nonempty
        (M8ConcreteNoEarlySourceRow
          payForCut topologyArc lemma8 C hmin) := by
  constructor
  case mp =>
    intro hsource
    have hrow :=
      (nonempty_sourceFields_iff_exists_coverage_and_obstructionPackage
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) (C := C) (hmin := hmin)).mp hsource
    rcases hrow with ⟨longArcCount, hcoverage, Hobstruction⟩
    rcases hcoverage with ⟨coverage⟩
    exact
      Nonempty.intro
        { longArcCount := longArcCount
          coverage := coverage
          obstruction := Hobstruction }
  case mpr =>
    intro hrow
    rcases hrow with ⟨R⟩
    exact Nonempty.intro R.toSourceFields

/-- Fully explicit false-start boundary inherited by the W25 source row. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_falseStartImplications :
    Nonempty (SourceFields payForCut topologyArc lemma8 C hmin) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (RowBoundary payForCut topologyArc lemma8 C hmin)
            longArcCount) /\
          M8ConcreteFalseStartImplications
            (RowPredicates payForCut topologyArc lemma8 C hmin) :=
  Lemma9NoEarlyConcreteW23.nonempty_sourceFields_iff_exists_coverage_and_falseStartImplications
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Cw := C) (hminw := hmin)

/-- Fully explicit indexed-obstruction boundary inherited by the W25 source
row. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_indexedObstructionInputs :
    Nonempty (SourceFields payForCut topologyArc lemma8 C hmin) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (RowBoundary payForCut topologyArc lemma8 C hmin)
            longArcCount) /\
          Nonempty
            (M8ConcreteIndexedObstructionInputs
              (RowPredicates payForCut topologyArc lemma8 C hmin)) :=
  Lemma9NoEarlyConcreteW23.nonempty_sourceFields_iff_exists_coverage_and_indexedObstructionInputs
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Cw := C) (hminw := hmin)

/-! ## Family-level source packages -/

/-- A W25 source family: every minimal-failure row carries checked coverage
and the W24 no-early obstruction package. -/
structure M8ConcreteNoEarlySourceFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8ConcreteNoEarlySourceRow
          payForCut topologyArc lemma8 C hmin

namespace M8ConcreteNoEarlySourceFamily

/-- Forget the W25 family to the W20 Lemma 9 source family. -/
def toSourceFamily
    (F : M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin => (F.row C hmin).toSourceFields

/-- Forget the W25 family directly to the W18 concrete producer family. -/
def toLemma9CoverageConcreteProducerFamily
    (F : M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    W18Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 :=
  F.toSourceFamily.toLemma9CoverageConcreteProducerFamily

end M8ConcreteNoEarlySourceFamily

/-- Exact family boundary: a W20 source family is inhabited iff every row has
the W25 coverage-plus-obstruction package. -/
theorem nonempty_sourceFamily_iff_forall_obstructionSourceRow :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Nonempty
            (M8ConcreteNoEarlySourceRow
              payForCut topologyArc lemma8 C hmin)) := by
  constructor
  case mp =>
    intro hsource n C hmin
    have hrow :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (Lemma9SourceInhabitationW21.nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp hsource C hmin
    exact
      (nonempty_sourceFields_iff_obstructionSourceRow
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) (C := C) (hmin := hmin)).mp hrow
  case mpr =>
    intro hrows
    exact
      (Lemma9SourceInhabitationW21.nonempty_sourceFamily_iff_forall_sourceFields
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_obstructionSourceRow
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8) (C := C) (hmin := hmin)).mpr
            (hrows C hmin))

/-- Exact W18 producer boundary in W25 terms. -/
theorem nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_obstructionSourceRow :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          Nonempty
            (M8ConcreteNoEarlySourceRow
              payForCut topologyArc lemma8 C hmin)) := by
  constructor
  case mp =>
    intro hproducer n C hmin
    have hrow :
        Nonempty
          (Lemma9NatLateTripleSourceFields.{u}
            payForCut topologyArc lemma8 C hmin) :=
      (Lemma9SourceInhabitationW21.nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp hproducer C hmin
    exact
      (nonempty_sourceFields_iff_obstructionSourceRow
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) (C := C) (hmin := hmin)).mp hrow
  case mpr =>
    intro hrows
    exact
      (Lemma9SourceInhabitationW21.nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_obstructionSourceRow
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8) (C := C) (hmin := hmin)).mpr
            (hrows C hmin))

end Lemma9NoEarlyObstructionInhabitationW25
end Swanepoel
end ErdosProblems1066

end
