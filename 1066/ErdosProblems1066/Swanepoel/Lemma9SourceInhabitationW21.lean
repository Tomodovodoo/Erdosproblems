import ErdosProblems1066.Swanepoel.Lemma9ProducerFamilyW20

set_option autoImplicit false

/-!
# W21 Lemma 9 source inhabitation boundary

This module tries the natural W21 inhabitation route for the Lemma 9
nat-late-triple coverage family.  The checked Lemma 6/7 modules supply the
coverage field `GapNegativeCoverageData`; the remaining field is exactly the
finite natural-index Lemma 9 package `M8NatLateTripleInputs`.

Accordingly, the file records constructors from those two source fields and
proves exact nonempty equivalences for rows and producer families.  No
stronger unconditional inhabitant is introduced.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9SourceInhabitationW21

open LateTriplesInterface
open Lemma6Lemma7AssemblyW13
open Lemma9CoverageConcreteW17
open Lemma9NatLateTripleProducerW19
open Lemma9ProducerFamilyW20

universe u

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}
variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

/-- The row-level source fields are inhabited by exactly a Lemma 6/7 coverage
row together with the finite natural-index Lemma 9 package. -/
def sourceFieldsOfCoverageAndNat
    (longArcCount : Nat)
    (coverage :
      GapNegativeCoverageData
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
        longArcCount)
    (natLateTripleInputs :
      M8NatLateTripleInputs
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) :
    Lemma9NatLateTripleSourceFields.{u}
      payForCut topologyArc lemma8 C hmin where
  longArcCount := longArcCount
  coverage := coverage
  natLateTripleInputs := natLateTripleInputs

/-- The explicit W20 row fields and the W19 row package have the same
inhabitation content. -/
theorem nonempty_natCoverageInputs_iff_sourceFields :
    Nonempty
      (M8NatLateTripleCoverageInputs
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 C hmin)) <->
      Nonempty
        (Lemma9NatLateTripleSourceFields.{u}
          payForCut topologyArc lemma8 C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro I =>
        exact
          Nonempty.intro
            (sourceFieldsOfCoverageAndNat
              (C := C) (hmin := hmin)
              I.longArcCount I.coverage I.natLateTripleInputs)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toNatLateTripleCoverageInputs

/-- Fully unfolded row-level source-field equivalence: Lemma 6/7 coverage is
one field, and the finite natural-index Lemma 9 package is the other. -/
theorem nonempty_sourceFields_iff_exists_coverage_and_nat :
    Nonempty
      (Lemma9NatLateTripleSourceFields.{u}
        payForCut topologyArc lemma8 C hmin) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            (AssembledLemma9PreLateBase
              payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
            longArcCount) /\
          Nonempty
            (M8NatLateTripleInputs
              (AssembledLemma9PreLateBase
                payForCut topologyArc lemma8 C hmin).localLabels.predicates.data) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro P.longArcCount
            (And.intro
              (Nonempty.intro P.coverage)
              (Nonempty.intro P.natLateTripleInputs))
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
                    (sourceFieldsOfCoverageAndNat
                      (C := C) (hmin := hmin)
                      longArcCount coverage natLateTripleInputs)

/-- The W17 concrete coverage row is equivalent to the same explicit W21
source fields. -/
theorem nonempty_coverageConcreteRow_iff_sourceFields :
    Nonempty
      (Lemma9CoverageConcreteRow
        (AssembledLemma9PreLateBase
          payForCut topologyArc lemma8 C hmin)) <->
      Nonempty
        (Lemma9NatLateTripleSourceFields.{u}
          payForCut topologyArc lemma8 C hmin) :=
  nonempty_coverageConcreteRow_iff_natCoverageInputs.trans
    nonempty_natCoverageInputs_iff_sourceFields

/-- A producer source family is exactly a source row for every minimal-failure
configuration. -/
theorem nonempty_sourceFamily_iff_forall_sourceFields :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Nonempty
            (Lemma9NatLateTripleSourceFields.{u}
              payForCut topologyArc lemma8 C hmin)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        intro n C hmin
        exact Nonempty.intro (F.row C hmin)
  case mpr =>
    intro h
    exact
      Nonempty.intro
        ({ row := fun C hmin => Classical.choice (h C hmin) } :
          Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8)

/-- Exact source-field equivalence for the W20 Lemma 9 concrete producer
family. -/
theorem nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Nonempty
            (Lemma9NatLateTripleSourceFields.{u}
              payForCut topologyArc lemma8 C hmin)) :=
  nonempty_lemma9CoverageConcreteProducerFamily_iff_sourceFamily.trans
    nonempty_sourceFamily_iff_forall_sourceFields

/-- Fully unfolded family-level equivalence.  The earlier Lemma 6/7 modules
account for the coverage side; the remaining content is exactly the finite
natural-index Lemma 9 input on each row. -/
theorem nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_exists_coverage_and_nat :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      (forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
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
      (nonempty_sourceFields_iff_exists_coverage_and_nat
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)
        (C := C) (hmin := hmin)).mp hsource
  case mpr =>
    intro h
    exact
      (nonempty_lemma9CoverageConcreteProducerFamily_iff_forall_sourceFields
        (payForCut := payForCut)
        (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (fun C hmin =>
          (nonempty_sourceFields_iff_exists_coverage_and_nat
            (payForCut := payForCut)
            (topologyArc := topologyArc)
            (lemma8 := lemma8)
            (C := C) (hmin := hmin)).mpr (h C hmin))

end Lemma9SourceInhabitationW21
end Swanepoel
end ErdosProblems1066

end
