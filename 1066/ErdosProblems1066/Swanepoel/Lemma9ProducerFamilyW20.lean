import ErdosProblems1066.Swanepoel.PointwiseFamilyProducerW18
import ErdosProblems1066.Swanepoel.Lemma9NatLateTripleProducerW19
import ErdosProblems1066.Swanepoel.Lemma9CoverageProducerW18

set_option autoImplicit false

/-!
# W20 Lemma 9 producer family

This file adapts the W19 row-level Lemma 9 nat-late-triple closure to the
W18 pointwise producer-family field
`PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily`.

The honest source fields are exposed explicitly as the W19 row package:
a long-arc count, checked Lemma 6/7 coverage for that count, and finite
natural-index Lemma 9 late-triple inputs for the assembled pre-late base.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9ProducerFamilyW20

open LateTriplesInterface
open Lemma6Lemma7AssemblyW13
open Lemma9CoverageConcreteW17
open Lemma9NatLateTripleProducerW19

universe u

abbrev W18PayForCutConcreteProducerFamily :=
  PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily

abbrev W18TopologyArcConcreteProducerFamily :=
  PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily

abbrev W18Lemma8ConcreteProducerFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u}) :=
  PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
    payForCut topologyArc

abbrev W18Lemma9CoverageConcreteProducerFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) :=
  PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily.{u}
    payForCut topologyArc lemma8

/-- The assembled W18 base row before Lemma 9 late-triple data is inserted. -/
abbrev AssembledLemma9PreLateBase
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  (PointwiseFamilyProducerW18.baseInputs
    payForCut topologyArc lemma8 C hmin).toPreLateBase

/-- Exact row-level W20 source fields for the W18 Lemma 9 producer row. -/
structure Lemma9NatLateTripleSourceFields
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  longArcCount : Nat
  coverage :
    GapNegativeCoverageData
      (AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin).arcBoundaryBudget.planarBoundary
      longArcCount
  natLateTripleInputs :
    M8NatLateTripleInputs
      (AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin).localLabels.predicates.data

/-- Packaged W19 source rows for every minimal-failure pointwise W18 row. -/
structure Lemma9NatLateTripleCoverageProducerFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        M8NatLateTripleCoverageInputs
          (AssembledLemma9PreLateBase
            payForCut topologyArc lemma8 C hmin)

/-- W19 nat-late-triple source rows build the W18 concrete Lemma 9 producer
family. -/
def lemma9CoverageConcreteProducerFamilyOfNatLateTripleCoverageFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc}
    (F : Lemma9NatLateTripleCoverageProducerFamily.{u}
      payForCut topologyArc lemma8) :
    W18Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toCoverageConcreteRow

namespace Lemma9NatLateTripleCoverageProducerFamily

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}
variable
  (F : Lemma9NatLateTripleCoverageProducerFamily.{u}
    payForCut topologyArc lemma8)

/-- Method form of the W20 adapter to the W18 producer-family field. -/
def toLemma9CoverageConcreteProducerFamily :
    W18Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 :=
  lemma9CoverageConcreteProducerFamilyOfNatLateTripleCoverageFamily F

theorem nonempty_lemma9CoverageConcreteProducerFamily
    (F : Lemma9NatLateTripleCoverageProducerFamily.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro (toLemma9CoverageConcreteProducerFamily F)

@[simp]
theorem toLemma9CoverageConcreteProducerFamily_row
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (toLemma9CoverageConcreteProducerFamily F).row C hmin =
      (F.row C hmin).toCoverageConcreteRow :=
  rfl

end Lemma9NatLateTripleCoverageProducerFamily

namespace Lemma9NatLateTripleSourceFields

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}
variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
variable
  (P : Lemma9NatLateTripleSourceFields.{u}
    payForCut topologyArc lemma8 C hmin)

/-- Repackage the exposed source fields as the W19 row package. -/
def toNatLateTripleCoverageInputs :
    M8NatLateTripleCoverageInputs
      (AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin) where
  longArcCount := P.longArcCount
  coverage := P.coverage
  natLateTripleInputs := P.natLateTripleInputs

/-- Build the W17 concrete row from the exposed source fields. -/
def toCoverageConcreteRow :
    Lemma9CoverageConcreteRow
      (AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin) :=
  P.toNatLateTripleCoverageInputs.toCoverageConcreteRow

@[simp]
theorem toNatLateTripleCoverageInputs_longArcCount :
    P.toNatLateTripleCoverageInputs.longArcCount = P.longArcCount :=
  rfl

@[simp]
theorem toNatLateTripleCoverageInputs_coverage :
    P.toNatLateTripleCoverageInputs.coverage = P.coverage :=
  rfl

@[simp]
theorem toNatLateTripleCoverageInputs_natLateTripleInputs :
    P.toNatLateTripleCoverageInputs.natLateTripleInputs =
      P.natLateTripleInputs :=
  rfl

@[simp]
theorem toCoverageConcreteRow_longArcCount :
    P.toCoverageConcreteRow.longArcCount = P.longArcCount :=
  rfl

@[simp]
theorem toCoverageConcreteRow_coverage :
    P.toCoverageConcreteRow.coverage = P.coverage :=
  rfl

end Lemma9NatLateTripleSourceFields

/-- The explicit-field source family, one row for every minimal-failure
pointwise W18 row. -/
structure Lemma9NatLateTripleSourceFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Lemma9NatLateTripleSourceFields.{u}
          payForCut topologyArc lemma8 C hmin

namespace Lemma9NatLateTripleSourceFamily

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}
variable
  (F : Lemma9NatLateTripleSourceFamily.{u}
    payForCut topologyArc lemma8)

/-- Package the exposed source fields as W19 nat-late-triple coverage rows. -/
def toNatLateTripleCoverageProducerFamily :
    Lemma9NatLateTripleCoverageProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toNatLateTripleCoverageInputs

/-- The explicit source family directly supplies the W18 Lemma 9 producer. -/
def toLemma9CoverageConcreteProducerFamily :
    W18Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 :=
  Lemma9NatLateTripleCoverageProducerFamily.toLemma9CoverageConcreteProducerFamily
    (toNatLateTripleCoverageProducerFamily F)

theorem nonempty_natLateTripleCoverageProducerFamily
    (F : Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleCoverageProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro (toNatLateTripleCoverageProducerFamily F)

theorem nonempty_lemma9CoverageConcreteProducerFamily
    (F : Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro (toLemma9CoverageConcreteProducerFamily F)

@[simp]
theorem toNatLateTripleCoverageProducerFamily_row
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (toNatLateTripleCoverageProducerFamily F).row C hmin =
      (F.row C hmin).toNatLateTripleCoverageInputs :=
  rfl

@[simp]
theorem toLemma9CoverageConcreteProducerFamily_row
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (toLemma9CoverageConcreteProducerFamily F).row C hmin =
      (F.row C hmin).toCoverageConcreteRow :=
  rfl

end Lemma9NatLateTripleSourceFamily

/-- Extract the exact W19 nat-late-triple coverage family from any W18
concrete Lemma 9 producer family. -/
def natLateTripleCoverageProducerFamilyOfCoverageConcreteProducerFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc}
    (F : W18Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleCoverageProducerFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    natLateTripleCoverageInputs_of_coverageConcreteRow
      (B := AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin)
      (F.row C hmin)

/-- Forget the packaged W19 source rows to their explicit source fields. -/
def natLateTripleSourceFamilyOfCoverageFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc}
    (F : Lemma9NatLateTripleCoverageProducerFamily.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    { longArcCount := (F.row C hmin).longArcCount
      coverage := (F.row C hmin).coverage
      natLateTripleInputs := (F.row C hmin).natLateTripleInputs }

/-- Extract the explicit W20 source fields from any W18 concrete Lemma 9
producer family. -/
def natLateTripleSourceFamilyOfCoverageConcreteProducerFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc}
    (F : W18Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  natLateTripleSourceFamilyOfCoverageFamily
    (natLateTripleCoverageProducerFamilyOfCoverageConcreteProducerFamily F)

@[simp]
theorem natLateTripleCoverageProducerFamilyOfCoverageConcreteProducerFamily_row_longArcCount
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc}
    (F : W18Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ((natLateTripleCoverageProducerFamilyOfCoverageConcreteProducerFamily
      F).row C hmin).longArcCount =
        (F.row C hmin).longArcCount :=
  rfl

@[simp]
theorem natLateTripleCoverageProducerFamilyOfCoverageConcreteProducerFamily_row_coverage
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc}
    (F : W18Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ((natLateTripleCoverageProducerFamilyOfCoverageConcreteProducerFamily
      F).row C hmin).coverage =
        (F.row C hmin).coverage :=
  rfl

theorem nonempty_lemma9CoverageConcreteProducerFamily_iff_natLateTripleCoverageFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc} :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (Lemma9NatLateTripleCoverageProducerFamily.{u}
          payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact
          Nonempty.intro
            (natLateTripleCoverageProducerFamilyOfCoverageConcreteProducerFamily
              F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact
          Nonempty.intro
            (Lemma9NatLateTripleCoverageProducerFamily.toLemma9CoverageConcreteProducerFamily
              F)

theorem nonempty_natLateTripleCoverageFamily_iff_sourceFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc} :
    Nonempty
      (Lemma9NatLateTripleCoverageProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (Lemma9NatLateTripleSourceFamily.{u}
          payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact
          Nonempty.intro
            (natLateTripleSourceFamilyOfCoverageFamily F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact
          Nonempty.intro
            (Lemma9NatLateTripleSourceFamily.toNatLateTripleCoverageProducerFamily
              F)

theorem nonempty_lemma9CoverageConcreteProducerFamily_iff_sourceFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc} :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (Lemma9NatLateTripleSourceFamily.{u}
          payForCut topologyArc lemma8) :=
  nonempty_lemma9CoverageConcreteProducerFamily_iff_natLateTripleCoverageFamily.trans
    nonempty_natLateTripleCoverageFamily_iff_sourceFamily

theorem lemma9CoverageConcreteProducerFamily_nonempty_of_natLateTripleCoverageFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc}
    (F : Lemma9NatLateTripleCoverageProducerFamily.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Lemma9NatLateTripleCoverageProducerFamily.nonempty_lemma9CoverageConcreteProducerFamily
    F

theorem lemma9CoverageConcreteProducerFamily_nonempty_of_sourceFamily
    {payForCut : W18PayForCutConcreteProducerFamily}
    {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc}
    (F : Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Lemma9NatLateTripleSourceFamily.nonempty_lemma9CoverageConcreteProducerFamily
    F

end Lemma9ProducerFamilyW20

namespace Verified

universe u

abbrev SwanepoelW20Lemma9NatLateTripleSourceFamily
    (payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :=
  Swanepoel.Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
    payForCut topologyArc lemma8

abbrev SwanepoelW20Lemma9CoverageConcreteProducerFamily
    (payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :=
  Swanepoel.Lemma9ProducerFamilyW20.W18Lemma9CoverageConcreteProducerFamily.{u}
    payForCut topologyArc lemma8

theorem swanepoelW20Lemma9CoverageConcreteProducerFamily_nonempty_of_sourceFamily
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F :
      SwanepoelW20Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (SwanepoelW20Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.Lemma9ProducerFamilyW20.lemma9CoverageConcreteProducerFamily_nonempty_of_sourceFamily
    F

end Verified
end Swanepoel
end ErdosProblems1066

end
