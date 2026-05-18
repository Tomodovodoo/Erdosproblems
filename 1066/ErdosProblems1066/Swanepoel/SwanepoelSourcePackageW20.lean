import ErdosProblems1066.Swanepoel.PointwiseAssemblyClosureW19
import ErdosProblems1066.Swanepoel.NoCutMinimalityClosureW19
import ErdosProblems1066.Swanepoel.TopologyArcClosureW19
import ErdosProblems1066.Swanepoel.Lemma8ConcreteGeometryProducerW19
import ErdosProblems1066.Swanepoel.Lemma9NatLateTripleProducerW19
import ErdosProblems1066.Swanepoel.FigureWitnessClosureW19

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W20 Swanepoel source package

This file combines the W20-SW2--SW6 source-field surfaces into one
Swanepoel-facing package.  Supplying the package fills the W19
`PointwiseProducerFamilyFields`; without it, the displayed fields are exactly
the remaining conditional inputs.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelSourcePackageW20

open MinimalGraphFacts

universe u

noncomputable section

abbrev PointwiseProducerFamilyFields :=
  PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields

abbrev PayForCutConcreteProducerFamily :=
  PointwiseAssemblyClosureW19.PayForCutConcreteProducerFamily

abbrev TopologyArcConcreteProducerFamily :=
  PointwiseAssemblyClosureW19.TopologyArcConcreteProducerFamily

abbrev Lemma8ConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :=
  PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
    payForCut topologyArc

abbrev Lemma9CoverageConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  PointwiseAssemblyClosureW19.Lemma9CoverageConcreteProducerFamily.{u}
    payForCut topologyArc lemma8

abbrev FigureWitnessConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  PointwiseAssemblyClosureW19.FigureWitnessConcreteProducerFamily.{u}
    payForCut topologyArc lemma8

abbrev PointwiseW16AssemblyFamily :=
  PointwiseAssemblyClosureW19.PointwiseW16AssemblyFamily

abbrev ConcreteBlockerInputFamily :=
  PointwiseAssemblyClosureW19.ConcreteBlockerInputFamily

/-! ## W20-SW2--SW6 source fields -/

/-- W20-SW2 source field: the exact pay-for-cut/no-cut minimality family. -/
abbrev PayForCutSourceFamily : Prop :=
  NoCutMinimalityClosureW19.PayForCutNoCutFieldFamily

/-- W20-SW3 source fields: topology, boundary budget, long arc, and triangle
run data producing actual topology-arc inputs. -/
abbrev TopologyArcSourceFamily : Type (u + 1) :=
  TopologyArcClosureW19.MinimalFailureTopologyArcSourceFamily.{u}

def payForCutProducerOfSource
    (F : PayForCutSourceFamily) :
    PayForCutConcreteProducerFamily where
  row := fun C hmin =>
    (NoCutPayForCutProducerW18.pointwiseBasePayForCutInput_iff_concreteSideCardInequalityAll
      (C := C) hmin).1 (F C hmin)

def topologyArcProducerOfSource
    (F : TopologyArcSourceFamily.{u}) :
    TopologyArcConcreteProducerFamily.{u} where
  row := fun C hmin => (F.row C hmin).toActualTopologyArcInputs

/-- W20-SW4 source fields: finite Lemma 8 geometry rows for the selected
pay-for-cut and topology-arc producers. -/
abbrev Lemma8SourceFamily
    (payForCut : PayForCutSourceFamily)
    (topologyArc : TopologyArcSourceFamily.{u}) :
    Type (u + 1) :=
  Lemma8ConcreteGeometryProducerW19.PointwiseLemma8GeometryFieldFamily.{u}
    (payForCutProducerOfSource payForCut)
    (topologyArcProducerOfSource topologyArc)

def lemma8ProducerOfSource
    {payForCut : PayForCutSourceFamily}
    {topologyArc : TopologyArcSourceFamily.{u}}
    (F : Lemma8SourceFamily.{u} payForCut topologyArc) :
    Lemma8ConcreteProducerFamily.{u}
      (payForCutProducerOfSource payForCut)
      (topologyArcProducerOfSource topologyArc) :=
  F.toLemma8ConcreteProducerFamily

def baseInputsOfSources
    {payForCut : PayForCutSourceFamily}
    {topologyArc : TopologyArcSourceFamily.{u}}
    (lemma8 : Lemma8SourceFamily.{u} payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    PointwiseRemainingRowAssemblyW17.PointwiseW16BaseInputs.{u} C hmin :=
  PointwiseFamilyProducerW18.baseInputs
    (payForCutProducerOfSource payForCut)
    (topologyArcProducerOfSource topologyArc)
    (lemma8ProducerOfSource lemma8)
    C hmin

/-- W20-SW5 source fields: checked Lemma 6/7 coverage plus finite natural
Lemma 9 late-triple data for the selected pre-late base row. -/
structure Lemma9SourceFamily
    (payForCut : PayForCutSourceFamily)
    (topologyArc : TopologyArcSourceFamily.{u})
    (lemma8 : Lemma8SourceFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Lemma9NatLateTripleProducerW19.M8NatLateTripleCoverageInputs
          ((baseInputsOfSources
            (payForCut := payForCut) (topologyArc := topologyArc)
            lemma8 C hmin).toPreLateBase)

namespace Lemma9SourceFamily

def toLemma9CoverageConcreteProducerFamily
    {payForCut : PayForCutSourceFamily}
    {topologyArc : TopologyArcSourceFamily.{u}}
    {lemma8 : Lemma8SourceFamily.{u} payForCut topologyArc}
    (F : Lemma9SourceFamily.{u} payForCut topologyArc lemma8) :
    Lemma9CoverageConcreteProducerFamily.{u}
      (payForCutProducerOfSource payForCut)
      (topologyArcProducerOfSource topologyArc)
      (lemma8ProducerOfSource lemma8) where
  row := fun C hmin => (F.row C hmin).toCoverageConcreteRow

end Lemma9SourceFamily

def lemma9ProducerOfSource
    {payForCut : PayForCutSourceFamily}
    {topologyArc : TopologyArcSourceFamily.{u}}
    {lemma8 : Lemma8SourceFamily.{u} payForCut topologyArc}
    (F : Lemma9SourceFamily.{u} payForCut topologyArc lemma8) :
    Lemma9CoverageConcreteProducerFamily.{u}
      (payForCutProducerOfSource payForCut)
      (topologyArcProducerOfSource topologyArc)
      (lemma8ProducerOfSource lemma8) :=
  F.toLemma9CoverageConcreteProducerFamily

/-- W20-SW6 source fields: the exact local Figure 8/Figure 9 angle-containment
bridges for the selected Lemma 8 base rows. -/
structure FigureSourceFamily
    (payForCut : PayForCutSourceFamily)
    (topologyArc : TopologyArcSourceFamily.{u})
    (lemma8 : Lemma8SourceFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  angleContainment :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        AngleContainmentInterface.AngleContainmentBridges
          (Lemma10Bridge.M8BrokenLatticeGood
            ((baseInputsOfSources
              (payForCut := payForCut) (topologyArc := topologyArc)
              lemma8 C hmin).localLabels.predicates.data))
          ((baseInputsOfSources
            (payForCut := payForCut) (topologyArc := topologyArc)
            lemma8 C hmin).turnBounds.turn)

namespace FigureSourceFamily

def toFigureWitnessConcreteProducerFamily
    {payForCut : PayForCutSourceFamily}
    {topologyArc : TopologyArcSourceFamily.{u}}
    {lemma8 : Lemma8SourceFamily.{u} payForCut topologyArc}
    (F : FigureSourceFamily.{u} payForCut topologyArc lemma8) :
    FigureWitnessConcreteProducerFamily.{u}
      (payForCutProducerOfSource payForCut)
      (topologyArcProducerOfSource topologyArc)
      (lemma8ProducerOfSource lemma8) where
  row := fun C hmin =>
    FigureWitnessClosureW19.localFigureWitnessConcreteFields_of_angleContainmentBridges
      (localLabels :=
        (baseInputsOfSources
          (payForCut := payForCut) (topologyArc := topologyArc)
          lemma8 C hmin).localLabels)
      (turnBounds :=
        (baseInputsOfSources
          (payForCut := payForCut) (topologyArc := topologyArc)
          lemma8 C hmin).turnBounds)
      (F.angleContainment C hmin)

end FigureSourceFamily

def figureProducerOfSource
    {payForCut : PayForCutSourceFamily}
    {topologyArc : TopologyArcSourceFamily.{u}}
    {lemma8 : Lemma8SourceFamily.{u} payForCut topologyArc}
    (F : FigureSourceFamily.{u} payForCut topologyArc lemma8) :
    FigureWitnessConcreteProducerFamily.{u}
      (payForCutProducerOfSource payForCut)
      (topologyArcProducerOfSource topologyArc)
      (lemma8ProducerOfSource lemma8) :=
  F.toFigureWitnessConcreteProducerFamily

/-! ## Combined package and final adapters -/

/-- The exact remaining W20 source package for the Swanepoel final closure. -/
structure SwanepoelSourcePackage : Type (u + 1) where
  payForCut : PayForCutSourceFamily
  topologyArc : TopologyArcSourceFamily.{u}
  lemma8 : Lemma8SourceFamily.{u} payForCut topologyArc
  lemma9 : Lemma9SourceFamily.{u} payForCut topologyArc lemma8
  figures : FigureSourceFamily.{u} payForCut topologyArc lemma8

abbrev ExactRemainingFields : Type (u + 1) :=
  SwanepoelSourcePackage.{u}

namespace SwanepoelSourcePackage

variable (P : SwanepoelSourcePackage.{u})

def payForCutProducer : PayForCutConcreteProducerFamily :=
  payForCutProducerOfSource P.payForCut

def topologyArcProducer : TopologyArcConcreteProducerFamily.{u} :=
  topologyArcProducerOfSource P.topologyArc

def lemma8Producer :
    Lemma8ConcreteProducerFamily.{u}
      P.payForCutProducer P.topologyArcProducer :=
  lemma8ProducerOfSource P.lemma8

def lemma9Producer :
    Lemma9CoverageConcreteProducerFamily.{u}
      P.payForCutProducer P.topologyArcProducer P.lemma8Producer :=
  lemma9ProducerOfSource P.lemma9

def figureProducer :
    FigureWitnessConcreteProducerFamily.{u}
      P.payForCutProducer P.topologyArcProducer P.lemma8Producer :=
  figureProducerOfSource P.figures

def toPointwiseProducerFamilyFields :
    PointwiseProducerFamilyFields.{u} where
  payForCut := P.payForCutProducer
  topologyArc := P.topologyArcProducer
  lemma8 := P.lemma8Producer
  lemma9 := P.lemma9Producer
  figures := P.figureProducer

def toPointwiseW16AssemblyFamily :
    PointwiseW16AssemblyFamily.{u} :=
  (toPointwiseProducerFamilyFields P).toPointwiseW16AssemblyFamily

theorem nonempty_pointwiseProducerFamilyFields
    (P : SwanepoelSourcePackage.{u}) :
    Nonempty PointwiseProducerFamilyFields.{u} :=
  Nonempty.intro (toPointwiseProducerFamilyFields P)

theorem nonempty_pointwiseW16AssemblyFamily
    (P : SwanepoelSourcePackage.{u}) :
    Nonempty PointwiseW16AssemblyFamily.{u} :=
  (toPointwiseProducerFamilyFields P).toPointwiseW16AssemblyFamily_nonempty

def toConcreteBlockerInputFamily
    (P : SwanepoelSourcePackage.{0}) :
    ConcreteBlockerInputFamily.{0} :=
  (toPointwiseProducerFamilyFields P).toConcreteBlockerInputFamily

theorem no_minimalClearedFailure
    (P : SwanepoelSourcePackage.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  (toPointwiseProducerFamilyFields P).no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (P : SwanepoelSourcePackage.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  (toPointwiseProducerFamilyFields P).targetLowerBoundEightThirtyOne

end SwanepoelSourcePackage

theorem pointwiseProducerFamilyFields_nonempty_of_exactRemainingFields
    (P : ExactRemainingFields.{u}) :
    Nonempty PointwiseProducerFamilyFields.{u} :=
  SwanepoelSourcePackage.nonempty_pointwiseProducerFamilyFields P

def pointwiseProducerFamilyFields_of_exactRemainingFields
    (P : ExactRemainingFields.{u}) :
    PointwiseProducerFamilyFields.{u} :=
  SwanepoelSourcePackage.toPointwiseProducerFamilyFields P

theorem targetLowerBoundEightThirtyOne_of_exactRemainingFields
    (P : ExactRemainingFields.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  SwanepoelSourcePackage.targetLowerBoundEightThirtyOne P

end

end SwanepoelSourcePackageW20
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW20SourcePackage :=
  Swanepoel.SwanepoelSourcePackageW20.SwanepoelSourcePackage

abbrev SwanepoelW20ExactRemainingFields :=
  Swanepoel.SwanepoelSourcePackageW20.ExactRemainingFields

noncomputable def swanepoelW20PointwiseProducerFamilyFields_of_sourcePackage
    (P : SwanepoelW20SourcePackage.{u}) :
    Swanepoel.SwanepoelSourcePackageW20.PointwiseProducerFamilyFields.{u} :=
  Swanepoel.SwanepoelSourcePackageW20.SwanepoelSourcePackage.toPointwiseProducerFamilyFields
    P

theorem targetLowerBoundEightThirtyOne_of_swanepoel_w20_sourcePackage
    (P : SwanepoelW20SourcePackage.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  Swanepoel.SwanepoelSourcePackageW20.SwanepoelSourcePackage.targetLowerBoundEightThirtyOne
    P

end Verified
end ErdosProblems1066
