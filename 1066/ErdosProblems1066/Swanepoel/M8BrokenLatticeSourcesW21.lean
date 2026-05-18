import ErdosProblems1066.Swanepoel.FigureProducerFamilyW20
import ErdosProblems1066.Swanepoel.Lemma8ProducerFamilyW20
import ErdosProblems1066.Swanepoel.Lemma9ProducerFamilyW20
import ErdosProblems1066.Swanepoel.M8MinimalFailureEliminatorInterface
import ErdosProblems1066.Swanepoel.M8WindowContainmentConcrete
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9
import ErdosProblems1066.Swanepoel.SwanepoelSourcePackageW20

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W21 M8 broken-lattice sources

This file is a bridge from the W20 Swanepoel source packages to the M8
broken-lattice/minimal-failure closure.  It does not add new geometric
content.  The checked contribution is:

* W20 pointwise rows already give actual honest local predicates;
* W20 Lemma 9 rows give the construction-interface no-early/late-triples
  field;
* W20 Figure rows give construction-interface window geometry;
* the exact remaining blockers are the W20 Lemma 8, Lemma 9, and Figure
  source packages named below.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8BrokenLatticeSourcesW21

open BrokenLatticePipeline
open M8ConstructionInterface
open M8LateTriplesFromNoEarly
open M8MinimalFailureEliminatorInterface
open M8PipelineClosure
open M8WindowContainmentConcrete
open MinimalGraphFacts
open NoEarlyTripleFromLemma9
open PointwiseRemainingRowAssemblyW17

universe u

noncomputable section

/-! ## Exact W20 blocker names -/

abbrev W20PayForCutSourceFamily : Prop :=
  SwanepoelSourcePackageW20.PayForCutSourceFamily

abbrev W20TopologyArcSourceFamily : Type (u + 1) :=
  SwanepoelSourcePackageW20.TopologyArcSourceFamily.{u}

abbrev W20Lemma8SourceFamily
    (payForCut : W20PayForCutSourceFamily)
    (topologyArc : W20TopologyArcSourceFamily.{u}) : Type (u + 1) :=
  SwanepoelSourcePackageW20.Lemma8SourceFamily.{u}
    payForCut topologyArc

abbrev W20Lemma9SourceFamily
    (payForCut : W20PayForCutSourceFamily)
    (topologyArc : W20TopologyArcSourceFamily.{u})
    (lemma8 : W20Lemma8SourceFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  SwanepoelSourcePackageW20.Lemma9SourceFamily.{u}
    payForCut topologyArc lemma8

abbrev W20FigureSourceFamily
    (payForCut : W20PayForCutSourceFamily)
    (topologyArc : W20TopologyArcSourceFamily.{u})
    (lemma8 : W20Lemma8SourceFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  SwanepoelSourcePackageW20.FigureSourceFamily.{u}
    payForCut topologyArc lemma8

/-- The exact blocker package at the M8 broken-lattice boundary.

The fields are intentionally the W20 source fields, with no weaker facade:
pay-for-cut/no-cut, topology arc data, Lemma 8 finite geometry, Lemma 9
finite late triples, and Figure 8/Figure 9 angle containment. -/
structure M8BrokenLatticeSourceBlockers : Type (u + 1) where
  payForCut : W20PayForCutSourceFamily
  topologyArc : W20TopologyArcSourceFamily.{u}
  lemma8 : W20Lemma8SourceFamily.{u} payForCut topologyArc
  lemma9 : W20Lemma9SourceFamily.{u} payForCut topologyArc lemma8
  figures : W20FigureSourceFamily.{u} payForCut topologyArc lemma8

namespace M8BrokenLatticeSourceBlockers

variable (P : M8BrokenLatticeSourceBlockers.{u})

def toW20SourcePackage :
    SwanepoelSourcePackageW20.SwanepoelSourcePackage.{u} where
  payForCut := P.payForCut
  topologyArc := P.topologyArc
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

end M8BrokenLatticeSourceBlockers

abbrev W20SourcePackage : Type (u + 1) :=
  SwanepoelSourcePackageW20.SwanepoelSourcePackage.{u}

/-! ## Local predicates and construction data from W20 rows -/

/-- The assembled W20 pointwise row for one minimal cleared failure. -/
def pointwiseAssemblyInputsOfW20Source
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    PointwiseW16AssemblyInputs.{u} C hmin :=
  (SwanepoelSourcePackageW20.SwanepoelSourcePackage.toPointwiseW16AssemblyFamily
    P).row C hmin

/-- The W20 row's honest local labels. -/
def localLabelsOfW20Source
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    M8LocalLabels C :=
  (pointwiseAssemblyInputsOfW20Source P C hmin).localLabels

/-- The actual honest local predicates supplied by the W20 source row. -/
def honestLocalPredicatesOfW20Source
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    Lemma10Bridge.M8HonestLocalPredicates
      (GraphBridge.unitDistanceLocalGraph C) :=
  (localLabelsOfW20Source P C hmin).predicates

/-- W20 source rows satisfy the existing minimal-failure local-predicate fact. -/
def localPredicateFactsOfW20Source
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    BrokenLatticePipeline.MinimalFailureM8HonestLocalPredicatesFacts C hmin where
  predicates := honestLocalPredicatesOfW20Source P C hmin

/-- Existential form of the actual local predicates supplied by W20 sources. -/
theorem exists_honestLocalPredicates_of_w20Source
    (P : W20SourcePackage.{u})
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C} :
    Exists fun Q :
      Lemma10Bridge.M8HonestLocalPredicates
        (GraphBridge.unitDistanceLocalGraph C) =>
        Q = honestLocalPredicatesOfW20Source P C hmin :=
  BrokenLatticePipeline.exists_m8_honestLocalPredicates_of_minimalFailure
    (localPredicateFactsOfW20Source P C hmin)

/-- The W20 Lemma 9 row, restricted to the five early starts, gives the
construction-interface no-early-triple package. -/
def noEarlyTriplesOfPointwiseAssembly
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (A : PointwiseW16AssemblyInputs.{u} C hmin) :
    M8ConstructionNoEarlyTriples A.localLabels :=
  constructionNoEarlyTriples_of_fiveStartLateFacts
    A.lemma9FiveStartLateFacts

/-- The W20 Figure row gives construction-interface window geometry. -/
def windowGeometryOfPointwiseAssembly
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (A : PointwiseW16AssemblyInputs.{u} C hmin) :
    M8ConstructionInterface.M8WindowGeometry A.localLabels A.turnBounds :=
  A.localWindowContainment.toM8WindowGeometry

/-- W20 pointwise rows assemble to the clean M8 construction interface. -/
def constructionDataOfPointwiseAssembly
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (A : PointwiseW16AssemblyInputs.{u} C hmin) :
    M8ConstructionData C hmin where
  localLabels := A.localLabels
  turnBounds := A.turnBounds
  lateTriples := (noEarlyTriplesOfPointwiseAssembly A).toM8LateTriples
  windowGeometry := windowGeometryOfPointwiseAssembly A

/-- A fixed W20 pointwise row is contradictory through the M8 construction
interface. -/
theorem contradiction_of_pointwiseAssembly
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (A : PointwiseW16AssemblyInputs.{u} C hmin) :
    False :=
  M8PipelineClosure.contradiction_of_constructionInterfaceData
    (constructionDataOfPointwiseAssembly A)

/-- W20 source packages assemble to clean M8 construction data for each
minimal cleared failure. -/
def constructionDataOfW20Source
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    M8ConstructionData C hmin :=
  constructionDataOfPointwiseAssembly
    (pointwiseAssemblyInputsOfW20Source P C hmin)

/-- The W20 source package supplies the M8 construction-interface eliminator. -/
def constructionInterfaceEliminatorOfW20Source
    (P : W20SourcePackage.{u}) :
    M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator := by
  intro n C hmin
  exact Nonempty.intro (constructionDataOfW20Source P C hmin)

/-- The same construction-interface eliminator, starting from the named W21
blocker package. -/
def constructionInterfaceEliminatorOfBlockers
    (P : M8BrokenLatticeSourceBlockers.{u}) :
    M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator :=
  constructionInterfaceEliminatorOfW20Source P.toW20SourcePackage

theorem no_minimalClearedFailure_of_w20Source_via_m8
    (P : W20SourcePackage.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8MinimalFailureEliminatorInterface.no_minimalClearedFailure_of_m8ConstructionInterfaceEliminator
    (constructionInterfaceEliminatorOfW20Source P)

theorem no_minimalClearedFailure_of_blockers_via_m8
    (P : M8BrokenLatticeSourceBlockers.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_w20Source_via_m8 P.toW20SourcePackage

theorem targetLowerBoundEightThirtyOne_of_w20Source_via_m8
    (P : W20SourcePackage.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_m8ConstructionInterfaceEliminator
    (constructionInterfaceEliminatorOfW20Source P)

theorem targetLowerBoundEightThirtyOne_of_blockers_via_m8
    (P : M8BrokenLatticeSourceBlockers.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_w20Source_via_m8 P.toW20SourcePackage

/-! ## Row-level blocker aliases for future closures -/

abbrev Lemma8FrameOrderBlockerPackage
    (payForCut : PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Lemma8ProducerFamilyW20.PointwiseLemma8RemainingFieldPackage.{u}
    payForCut topologyArc

abbrev Lemma9NatLateTripleBlockerFamily
    (payForCut :
      Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily)
    (topologyArc :
      Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 :
      Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
    payForCut topologyArc lemma8

abbrev FigureExactAngleBlockerFamily
    (payForCut :
      FigureProducerFamilyW20.W18PayForCutConcreteProducerFamily)
    (topologyArc :
      FigureProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 :
      FigureProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :
    Type (u + 1) :=
  FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
    payForCut topologyArc lemma8

theorem lemma8Producer_nonempty_of_frameOrderBlocker
    {payForCut : PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc :
      PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}}
    (P :
      Lemma8FrameOrderBlockerPackage.{u} payForCut topologyArc) :
    Nonempty
      (PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :=
  Lemma8ProducerFamilyW20.lemma8ConcreteProducerFamily_nonempty_of_remainingFields
    payForCut topologyArc P

theorem lemma9Producer_nonempty_of_natLateTripleBlocker
    {payForCut :
      Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (P :
      Lemma9NatLateTripleBlockerFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9ProducerFamilyW20.W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Lemma9ProducerFamilyW20.lemma9CoverageConcreteProducerFamily_nonempty_of_sourceFamily
    P

theorem figureProducer_nonempty_of_exactAngleBlocker
    {payForCut :
      FigureProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      FigureProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      FigureProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (P :
      FigureExactAngleBlockerFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (FigureProducerFamilyW20.W18FigureWitnessConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  FigureProducerFamilyW20.figureWitnessConcreteProducerFamily_nonempty_of_exactBaseFamily
    P

end

end M8BrokenLatticeSourcesW21
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW21M8BrokenLatticeSourceBlockers :=
  Swanepoel.M8BrokenLatticeSourcesW21.M8BrokenLatticeSourceBlockers

theorem targetLowerBoundEightThirtyOne_of_swanepoel_w21_m8_blockers
    (P : SwanepoelW21M8BrokenLatticeSourceBlockers.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  Swanepoel.M8BrokenLatticeSourcesW21.targetLowerBoundEightThirtyOne_of_blockers_via_m8
    P

end Verified
end ErdosProblems1066
