import ErdosProblems1066.Swanepoel.PointwiseRemainingRowAssemblyW17
import ErdosProblems1066.Swanepoel.PayForCutConcreteInequalityW17
import ErdosProblems1066.Swanepoel.Lemma9CoverageConcreteW17
import ErdosProblems1066.Swanepoel.FigureWitnessConcreteAssemblyW17

set_option autoImplicit false

/-!
# W18 pointwise family producer assembly

This file contains only the W18-facing assembly surface.  It does not assume
an endpoint theorem; its parameters are the concrete row producer families
needed to fill the W17 pointwise assembly row.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseFamilyProducerW18

open BoundaryTopologyArcBridgeW16
open FigureWitnessConcreteAssemblyW17
open Lemma8ExistenceConcrete
open Lemma8NeighborExtractionConcrete
open Lemma9CoverageConcreteW17
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoCutFromMinimalityW16
open PointwiseRemainingRowAssemblyW17

universe u

noncomputable section

/-- Concrete W17 pay-for-cut source, kept in side-cardinality form. -/
structure PayForCutConcreteProducerFamily : Type 1 where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PayForCutConcreteInequalityW17.ConcreteSelectedSideCardInequalityAll
          hmin

namespace PayForCutConcreteProducerFamily

def minimalitySelectedPayForCut
    (F : PayForCutConcreteProducerFamily)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin :=
  (PayForCutConcreteInequalityW17.minimalitySelectedPayForCut_iff_concreteSideCardInequalityAll
      hmin).2
      (F.row C hmin)

def noCutVertex
    (F : PayForCutConcreteProducerFamily)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    CutVertexInterface.NoCutVertex C :=
  noCutVertex_of_minimalitySelectedPayForCut
    (F.minimalitySelectedPayForCut C hmin)

end PayForCutConcreteProducerFamily

/-- Concrete topology/boundary-arc producer rows. -/
structure TopologyArcConcreteProducerFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : IsMinimalClearedFailure C),
        ActualTopologyArcInputs.{u} C

/-- Concrete Lemma 8 producer rows for the selected pay/topology rows. -/
structure Lemma8ConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) where
  centerDegreeSix :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        forall i : M8ExtraIndex,
          centerDegree
            (spineOfBoundaryArc hmin
              (payForCut.noCutVertex C hmin)
              (topologyArc.row C hmin).arcBoundaryBudget
              (topologyArc.row C hmin).boundaryArc) i = 6
  neighborFrame :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        forall i : M8ExtraIndex,
          FourForbiddenNeighborFrame
            (spineOfBoundaryArc hmin
              (payForCut.noCutVertex C hmin)
              (topologyArc.row C hmin).arcBoundaryBudget
              (topologyArc.row C hmin).boundaryArc) i
  positiveCyclicOrderAt :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : IsMinimalClearedFailure C),
        M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
          Fin n -> Prop
  positiveCyclicOrder :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        forall i : M8ExtraIndex,
          positiveCyclicOrderAt C hmin i
            ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
              (centerDegreeSix C hmin)
              (neighborFrame C hmin)).s i)
            ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
              (centerDegreeSix C hmin)
              (neighborFrame C hmin)).r i)
            ((spineOfBoundaryArc hmin
              (payForCut.noCutVertex C hmin)
              (topologyArc.row C hmin).arcBoundaryBudget
              (topologyArc.row C hmin).boundaryArc).prevQ i)
            ((spineOfBoundaryArc hmin
              (payForCut.noCutVertex C hmin)
              (topologyArc.row C hmin).arcBoundaryBudget
              (topologyArc.row C hmin).boundaryArc).leftP i)
            ((spineOfBoundaryArc hmin
              (payForCut.noCutVertex C hmin)
              (topologyArc.row C hmin).arcBoundaryBudget
              (topologyArc.row C hmin).boundaryArc).rightP i)
            ((spineOfBoundaryArc hmin
              (payForCut.noCutVertex C hmin)
              (topologyArc.row C hmin).arcBoundaryBudget
              (topologyArc.row C hmin).boundaryArc).nextQ i)

/-- The W17 base row assembled from the concrete pay, topology, and Lemma 8
producer families. -/
def baseInputs
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    PointwiseW16BaseInputs.{u} C hmin where
  minimalitySelectedPayForCut :=
    payForCut.minimalitySelectedPayForCut C hmin
  topologyArc := topologyArc.row C hmin
  centerDegreeSix := lemma8.centerDegreeSix C hmin
  neighborFrame := lemma8.neighborFrame C hmin
  positiveCyclicOrderAt := lemma8.positiveCyclicOrderAt C hmin
  positiveCyclicOrder := lemma8.positiveCyclicOrder C hmin

/-- Concrete Lemma 9 coverage producer rows, specialized to the assembled
pre-late base row rather than to an endpoint. -/
structure Lemma9CoverageConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Lemma9CoverageConcreteRow
          ((baseInputs payForCut topologyArc lemma8 C hmin).toPreLateBase)

/-- Concrete Figure 8/Figure 9 producer rows, specialized to the assembled
local labels and turn bounds. -/
structure FigureWitnessConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        LocalFigureWitnessConcreteFields
          (baseInputs payForCut topologyArc lemma8 C hmin).localLabels
          (baseInputs payForCut topologyArc lemma8 C hmin).turnBounds

/-- Assemble one pointwise W16 row from the concrete producer rows. -/
def pointwiseW16AssemblyInputsOfConcreteProducers
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    (lemma9 :
      Lemma9CoverageConcreteProducerFamily.{u} payForCut topologyArc lemma8)
    (figures :
      FigureWitnessConcreteProducerFamily.{u} payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    PointwiseW16AssemblyInputs.{u} C hmin where
  base := baseInputs payForCut topologyArc lemma8 C hmin
  coverageLate :=
    (lemma9.row C hmin).toPointwiseLemma9CoverageLateInputs
  figure8 := (figures.row C hmin).figure8
  figure9_left := (figures.row C hmin).figure9_left

/-- Assemble the uniform pointwise W16 family from the concrete producer
families. -/
def pointwiseW16AssemblyFamilyOfConcreteProducers
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    (lemma9 :
      Lemma9CoverageConcreteProducerFamily.{u} payForCut topologyArc lemma8)
    (figures :
      FigureWitnessConcreteProducerFamily.{u} payForCut topologyArc lemma8) :
    PointwiseW16AssemblyFamily.{u} where
  row := fun C hmin =>
    pointwiseW16AssemblyInputsOfConcreteProducers
      payForCut topologyArc lemma8 lemma9 figures C hmin

theorem pointwiseW16AssemblyFamily_nonempty_of_concreteProducers
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc)
    (lemma9 :
      Lemma9CoverageConcreteProducerFamily.{u} payForCut topologyArc lemma8)
    (figures :
      FigureWitnessConcreteProducerFamily.{u} payForCut topologyArc lemma8) :
    Nonempty PointwiseW16AssemblyFamily.{u} :=
  Nonempty.intro
    (pointwiseW16AssemblyFamilyOfConcreteProducers
      payForCut topologyArc lemma8 lemma9 figures)

end

end PointwiseFamilyProducerW18
end Swanepoel
end ErdosProblems1066
