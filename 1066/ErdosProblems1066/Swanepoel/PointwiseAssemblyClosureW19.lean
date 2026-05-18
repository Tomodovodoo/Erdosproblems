import ErdosProblems1066.Swanepoel.PointwiseFamilyProducerW18
import ErdosProblems1066.Swanepoel.ConcreteBlockerFamilyProducerW18

set_option autoImplicit false

/-!
# W19 pointwise assembly closure

This file closes the W18 producer-family interface into the W17 pointwise
assembly family, and then exposes the same assembled family through the W18
concrete-blocker adapter.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseAssemblyClosureW19

open ConcreteBlockerFamilyProducerW18
open PointwiseFamilyProducerW18
open PointwiseRemainingRowAssemblyW17
open SwanepoelConcreteBlockerLedgerW17

universe u

noncomputable section

abbrev PayForCutConcreteProducerFamily :=
  PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily

abbrev TopologyArcConcreteProducerFamily :=
  PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily

abbrev Lemma8ConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :=
  PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
    payForCut topologyArc

abbrev Lemma9CoverageConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily.{u}
    payForCut topologyArc lemma8

abbrev FigureWitnessConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  PointwiseFamilyProducerW18.FigureWitnessConcreteProducerFamily.{u}
    payForCut topologyArc lemma8

abbrev PointwiseW16AssemblyFamily :=
  PointwiseRemainingRowAssemblyW17.PointwiseW16AssemblyFamily

abbrev PointwiseFamilyObligation :=
  ConcreteBlockerFamilyProducerW18.PointwiseFamilyObligation

abbrev ConcreteBlockerInputFamily :=
  SwanepoelConcreteBlockerLedgerW17.ConcreteBlockerInputFamily

/-- Conditional W19 package containing precisely the W18 producer-family rows. -/
structure PointwiseProducerFamilyFields : Type (u + 1) where
  payForCut : PayForCutConcreteProducerFamily
  topologyArc : TopologyArcConcreteProducerFamily.{u}
  lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc
  lemma9 :
    Lemma9CoverageConcreteProducerFamily.{u} payForCut topologyArc lemma8
  figures :
    FigureWitnessConcreteProducerFamily.{u} payForCut topologyArc lemma8

namespace PointwiseProducerFamilyFields

def toPointwiseW16AssemblyFamily
    (P : PointwiseProducerFamilyFields.{u}) :
    PointwiseW16AssemblyFamily.{u} :=
  PointwiseFamilyProducerW18.pointwiseW16AssemblyFamilyOfConcreteProducers
    P.payForCut P.topologyArc P.lemma8 P.lemma9 P.figures

theorem toPointwiseW16AssemblyFamily_nonempty
    (P : PointwiseProducerFamilyFields.{u}) :
    Nonempty PointwiseW16AssemblyFamily.{u} :=
  Nonempty.intro P.toPointwiseW16AssemblyFamily

def toPointwiseFamilyObligation
    (P : PointwiseProducerFamilyFields.{0}) :
    PointwiseFamilyObligation :=
  P.toPointwiseW16AssemblyFamily

def toConcreteBlockerInputFamily
    (P : PointwiseProducerFamilyFields.{0}) :
    ConcreteBlockerInputFamily.{0} :=
  ConcreteBlockerFamilyProducerW18.concreteBlockerInputFamilyOfPointwiseFamily
    P.toPointwiseFamilyObligation

theorem no_minimalClearedFailure
    (P : PointwiseProducerFamilyFields.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (MinimalGraphFacts.IsMinimalClearedFailure C) :=
  ConcreteBlockerFamilyProducerW18.no_minimalClearedFailure_of_pointwiseFamily
    P.toPointwiseFamilyObligation

theorem targetLowerBoundEightThirtyOne
    (P : PointwiseProducerFamilyFields.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  ConcreteBlockerFamilyProducerW18.targetLowerBoundEightThirtyOne_of_pointwiseFamily
    P.toPointwiseFamilyObligation

@[simp]
theorem toConcreteBlockerInputFamily_row
    (P : PointwiseProducerFamilyFields.{0})
    {n : Nat}
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (P.toConcreteBlockerInputFamily.row C hmin) =
      ConcreteBlockerFamilyProducerW18.pointwiseConcreteBlockerFieldsOfW17
        (P.toPointwiseW16AssemblyFamily.row C hmin) := by
  rfl

end PointwiseProducerFamilyFields

def pointwiseW16AssemblyFamily_of_payForCut_topologyArc_lemma8_lemma9_figures
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    (lemma9 :
      Lemma9CoverageConcreteProducerFamily.{u} payForCut topologyArc lemma8)
    (figures :
      FigureWitnessConcreteProducerFamily.{u} payForCut topologyArc lemma8) :
    PointwiseW16AssemblyFamily.{u} :=
  PointwiseFamilyProducerW18.pointwiseW16AssemblyFamilyOfConcreteProducers
    payForCut topologyArc lemma8 lemma9 figures

theorem pointwiseW16AssemblyFamily_nonempty_of_payForCut_topologyArc_lemma8_lemma9_figures
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    (lemma9 :
      Lemma9CoverageConcreteProducerFamily.{u} payForCut topologyArc lemma8)
    (figures :
      FigureWitnessConcreteProducerFamily.{u} payForCut topologyArc lemma8) :
    Nonempty PointwiseW16AssemblyFamily.{u} :=
  PointwiseFamilyProducerW18.pointwiseW16AssemblyFamily_nonempty_of_concreteProducers
    payForCut topologyArc lemma8 lemma9 figures

def concreteBlockerInputFamily_of_payForCut_topologyArc_lemma8_lemma9_figures
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{0})
    (lemma8 : Lemma8ConcreteProducerFamily.{0} payForCut topologyArc)
    (lemma9 :
      Lemma9CoverageConcreteProducerFamily.{0} payForCut topologyArc lemma8)
    (figures :
      FigureWitnessConcreteProducerFamily.{0} payForCut topologyArc lemma8) :
    ConcreteBlockerInputFamily.{0} :=
  ConcreteBlockerFamilyProducerW18.concreteBlockerInputFamilyOfPointwiseFamily
    (pointwiseW16AssemblyFamily_of_payForCut_topologyArc_lemma8_lemma9_figures
      payForCut topologyArc lemma8 lemma9 figures)

theorem no_minimalClearedFailure_of_payForCut_topologyArc_lemma8_lemma9_figures
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{0})
    (lemma8 : Lemma8ConcreteProducerFamily.{0} payForCut topologyArc)
    (lemma9 :
      Lemma9CoverageConcreteProducerFamily.{0} payForCut topologyArc lemma8)
    (figures :
      FigureWitnessConcreteProducerFamily.{0} payForCut topologyArc lemma8) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (MinimalGraphFacts.IsMinimalClearedFailure C) :=
  ConcreteBlockerFamilyProducerW18.no_minimalClearedFailure_of_pointwiseFamily
    (pointwiseW16AssemblyFamily_of_payForCut_topologyArc_lemma8_lemma9_figures
      payForCut topologyArc lemma8 lemma9 figures)

theorem targetLowerBoundEightThirtyOne_of_payForCut_topologyArc_lemma8_lemma9_figures
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{0})
    (lemma8 : Lemma8ConcreteProducerFamily.{0} payForCut topologyArc)
    (lemma9 :
      Lemma9CoverageConcreteProducerFamily.{0} payForCut topologyArc lemma8)
    (figures :
      FigureWitnessConcreteProducerFamily.{0} payForCut topologyArc lemma8) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  ConcreteBlockerFamilyProducerW18.targetLowerBoundEightThirtyOne_of_pointwiseFamily
    (pointwiseW16AssemblyFamily_of_payForCut_topologyArc_lemma8_lemma9_figures
      payForCut topologyArc lemma8 lemma9 figures)

end

end PointwiseAssemblyClosureW19

universe u

open PointwiseAssemblyClosureW19

theorem pointwiseW16AssemblyFamily_nonempty_of_w19_payForCut_topologyArc_lemma8_lemma9_figures
    (payForCut :
      PointwiseAssemblyClosureW19.PayForCutConcreteProducerFamily)
    (topologyArc :
      PointwiseAssemblyClosureW19.TopologyArcConcreteProducerFamily.{u})
    (lemma8 :
      PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc)
    (lemma9 :
      PointwiseAssemblyClosureW19.Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8)
    (figures :
      PointwiseAssemblyClosureW19.FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (PointwiseRemainingRowAssemblyW17.PointwiseW16AssemblyFamily.{u}) :=
  pointwiseW16AssemblyFamily_nonempty_of_payForCut_topologyArc_lemma8_lemma9_figures
    payForCut topologyArc lemma8 lemma9 figures

theorem targetLowerBoundEightThirtyOne_of_w19_payForCut_topologyArc_lemma8_lemma9_figures
    (payForCut :
      PointwiseAssemblyClosureW19.PayForCutConcreteProducerFamily)
    (topologyArc :
      PointwiseAssemblyClosureW19.TopologyArcConcreteProducerFamily.{0})
    (lemma8 :
      PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{0}
        payForCut topologyArc)
    (lemma9 :
      PointwiseAssemblyClosureW19.Lemma9CoverageConcreteProducerFamily.{0}
        payForCut topologyArc lemma8)
    (figures :
      PointwiseAssemblyClosureW19.FigureWitnessConcreteProducerFamily.{0}
        payForCut topologyArc lemma8) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_payForCut_topologyArc_lemma8_lemma9_figures
    payForCut topologyArc lemma8 lemma9 figures

end Swanepoel

namespace Verified

abbrev SwanepoelW19PointwiseProducerFamilyFields :=
  Swanepoel.PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields

theorem targetLowerBoundEightThirtyOne_of_swanepoel_w19_pointwiseProducerFamilyFields
    (P : SwanepoelW19PointwiseProducerFamilyFields.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  P.targetLowerBoundEightThirtyOne

end Verified
end ErdosProblems1066
