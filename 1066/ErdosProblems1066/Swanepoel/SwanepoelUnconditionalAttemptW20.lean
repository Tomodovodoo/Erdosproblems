import ErdosProblems1066.Swanepoel.AngleContainmentBridgeProducerW19
import ErdosProblems1066.Swanepoel.Lemma8ConcreteGeometryProducerW19
import ErdosProblems1066.Swanepoel.Lemma9NatLateTripleProducerW19
import ErdosProblems1066.Swanepoel.NoCutPayForCutProducerW18
import ErdosProblems1066.Swanepoel.PointwiseAssemblyClosureW19
import ErdosProblems1066.Swanepoel.SwanepoelFinalClosureW19
import ErdosProblems1066.Swanepoel.TopologyArcProducerFamilyW20

set_option autoImplicit false

/-!
# W20 unconditional Swanepoel endpoint attempt

This file tries the W20 Swanepoel endpoint without adding a public
`KnownBounds` theorem.  The W19/W20 sources close the target only after the
remaining pointwise producer families below are supplied.  The theorem at the
end is therefore the honest reduction: no unconditional endpoint is asserted.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelUnconditionalAttemptW20

open AngleContainmentBridgeProducerW19
open FigureWitnessConcreteAssemblyW17
open Lemma9NatLateTripleProducerW19
open MinimalGraphFacts
open NoCutPayForCutProducerW18
open PointwiseAssemblyClosureW19
open PointwiseFamilyProducerW18
open TopologyArcProducerFamilyW20

noncomputable section

abbrev Target : Prop :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

abbrev PayForCutConcreteProducerFamily :=
  PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily

abbrev ConcreteSideCardFamily : Prop :=
  NoCutPayForCutProducerW18.MinimalFailureConcreteSideCardFamily

abbrev TopologyArcSourceFamily : Type 1 :=
  TopologyArcProducerFamilyW20.MinimalFailureTopologyArcSourceFamily.{0}

abbrev TopologyArcConcreteProducerFamily : Type 1 :=
  TopologyArcProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{0}

abbrev Lemma8GeometryFieldFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily) : Type 1 :=
  Lemma8ConcreteGeometryProducerW19.PointwiseLemma8GeometryFieldFamily.{0}
    payForCut topologyArc

abbrev Lemma8ConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily) : Type 1 :=
  PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{0}
    payForCut topologyArc

abbrev Lemma9CoverageConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily)
    (lemma8 : Lemma8ConcreteProducerFamily payForCut topologyArc) :
    Type 1 :=
  PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily.{0}
    payForCut topologyArc lemma8

abbrev FigureWitnessConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily)
    (lemma8 : Lemma8ConcreteProducerFamily payForCut topologyArc) :
    Type 1 :=
  PointwiseFamilyProducerW18.FigureWitnessConcreteProducerFamily.{0}
    payForCut topologyArc lemma8

abbrev ExactAngleContainmentCertificateFamily : Type 1 :=
  AngleContainmentBridgeProducerW19.ExactAngleContainmentCertificateFamily.{0}

/-- The pay-for-cut producer is exactly the concrete side-card family in the
current W18 no-cut surface. -/
def payForCutConcreteProducerFamilyOfSideCardFamily
    (H : ConcreteSideCardFamily) :
    PayForCutConcreteProducerFamily where
  row := fun C hmin => H C hmin

theorem payForCutConcreteProducerFamily_nonempty_of_sideCardFamily
    (H : ConcreteSideCardFamily) :
    Nonempty PayForCutConcreteProducerFamily :=
  Nonempty.intro (payForCutConcreteProducerFamilyOfSideCardFamily H)

/-- The W20 topology source family is already the W18 topology-arc producer
family after forgetting source bookkeeping. -/
def topologyArcConcreteProducerFamilyOfSourceFamily
    (F : TopologyArcSourceFamily) :
    TopologyArcConcreteProducerFamily :=
  F.toTopologyArcConcreteProducerFamily

/-- W19 natural late-triple coverage rows, uniformly over the W18 assembled
pre-late base rows. -/
structure Lemma9NatCoverageFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily)
    (lemma8 : Lemma8ConcreteProducerFamily payForCut topologyArc) :
    Type 1 where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8NatLateTripleCoverageInputs
          ((PointwiseFamilyProducerW18.baseInputs
            payForCut topologyArc lemma8 C hmin).toPreLateBase)

namespace Lemma9NatCoverageFamily

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily}
variable {lemma8 : Lemma8ConcreteProducerFamily payForCut topologyArc}

/-- Forget the W19 finite-natural coverage package to the W18 concrete
Lemma 9 producer family. -/
def toLemma9CoverageConcreteProducerFamily
    (F : Lemma9NatCoverageFamily payForCut topologyArc lemma8) :
    Lemma9CoverageConcreteProducerFamily payForCut topologyArc lemma8 where
  row := fun C hmin => (F.row C hmin).toCoverageConcreteRow

@[simp]
theorem toLemma9CoverageConcreteProducerFamily_row
    (F : Lemma9NatCoverageFamily payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    F.toLemma9CoverageConcreteProducerFamily.row C hmin =
      (F.row C hmin).toCoverageConcreteRow :=
  rfl

end Lemma9NatCoverageFamily

/-- Exact W19 angle-containment certificates supply the W18/W17 figure-witness
producer family once Lemma 9 has chosen the row base. -/
def figureWitnessConcreteProducerFamilyOfExactAngles
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily}
    {lemma8 : Lemma8ConcreteProducerFamily payForCut topologyArc}
    (lemma9 :
      Lemma9CoverageConcreteProducerFamily payForCut topologyArc lemma8)
    (angles : ExactAngleContainmentCertificateFamily) :
    FigureWitnessConcreteProducerFamily payForCut topologyArc lemma8 where
  row := fun C hmin =>
    let coverageLate :=
      (lemma9.row C hmin).toPointwiseLemma9CoverageLateInputs
    (angles.pointwiseFigureWitnessConcreteFields
      coverageLate.toPointwiseLemma89Base).fields

/--
The exact W20 remaining-obligation package.

This is the no-go statement for the unconditional attempt: the current W19/W20
files give adapters between these rows and the endpoint, but they do not give
closed inhabitants for all rows here.
-/
structure RemainingObligations : Type 1 where
  payForCut : PayForCutConcreteProducerFamily
  topologySource : TopologyArcSourceFamily
  lemma8Geometry :
    Lemma8GeometryFieldFamily
      payForCut
      (topologyArcConcreteProducerFamilyOfSourceFamily topologySource)
  lemma9NatCoverage :
    Lemma9NatCoverageFamily
      payForCut
      (topologyArcConcreteProducerFamilyOfSourceFamily topologySource)
      lemma8Geometry.toLemma8ConcreteProducerFamily
  exactAngles : ExactAngleContainmentCertificateFamily

namespace RemainingObligations

def topologyArc (P : RemainingObligations) : TopologyArcConcreteProducerFamily :=
  topologyArcConcreteProducerFamilyOfSourceFamily P.topologySource

def lemma8 (P : RemainingObligations) :
    Lemma8ConcreteProducerFamily P.payForCut P.topologyArc :=
  P.lemma8Geometry.toLemma8ConcreteProducerFamily

def lemma9 (P : RemainingObligations) :
    Lemma9CoverageConcreteProducerFamily P.payForCut P.topologyArc P.lemma8 :=
  P.lemma9NatCoverage.toLemma9CoverageConcreteProducerFamily

def figures (P : RemainingObligations) :
    FigureWitnessConcreteProducerFamily P.payForCut P.topologyArc P.lemma8 :=
  figureWitnessConcreteProducerFamilyOfExactAngles P.lemma9 P.exactAngles

def toPointwiseProducerFamilyFields (P : RemainingObligations) :
    PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields.{0} where
  payForCut := P.payForCut
  topologyArc := P.topologyArc
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

def toPointwiseW16AssemblyFamily (P : RemainingObligations) :
    PointwiseAssemblyClosureW19.PointwiseW16AssemblyFamily.{0} :=
  P.toPointwiseProducerFamilyFields.toPointwiseW16AssemblyFamily

def toConcreteBlockerInputFamily (P : RemainingObligations) :
    PointwiseAssemblyClosureW19.ConcreteBlockerInputFamily.{0} :=
  P.toPointwiseProducerFamilyFields.toConcreteBlockerInputFamily

theorem no_minimalClearedFailure (P : RemainingObligations) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields.no_minimalClearedFailure
    P.toPointwiseProducerFamilyFields

theorem targetLowerBoundEightThirtyOne (P : RemainingObligations) : Target :=
  PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields.targetLowerBoundEightThirtyOne
    P.toPointwiseProducerFamilyFields

end RemainingObligations

/-- The honest endpoint reduction currently available from W19/W20 sources. -/
theorem targetLowerBoundEightThirtyOne_of_remainingObligations
    (P : RemainingObligations) :
    Target :=
  P.targetLowerBoundEightThirtyOne

/-- Nonempty form of the same reduction, useful for future endpoint gates. -/
theorem targetLowerBoundEightThirtyOne_of_nonempty_remainingObligations
    (h : Nonempty RemainingObligations) :
    Target := by
  cases h with
  | intro P => exact P.targetLowerBoundEightThirtyOne

end

end SwanepoelUnconditionalAttemptW20
end Swanepoel
end ErdosProblems1066
