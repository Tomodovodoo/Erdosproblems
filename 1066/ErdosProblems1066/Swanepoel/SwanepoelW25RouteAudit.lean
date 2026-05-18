import ErdosProblems1066.Swanepoel.NoCutBlockerEliminationW24
import ErdosProblems1066.Swanepoel.JordanBoundaryConcreteInhabitationW24
import ErdosProblems1066.Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24
import ErdosProblems1066.Swanepoel.Lemma9NoEarlyInhabitationW24
import ErdosProblems1066.Swanepoel.FigureAngleInequalitiesW24
import ErdosProblems1066.Swanepoel.MinimalStillOpenComponentsW24
import ErdosProblems1066.Swanepoel.LaneProductAssemblyW24
import ErdosProblems1066.Swanepoel.W20SourcePackageConcreteW24

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W25 Swanepoel route audit

This module is a CI-facing audit facade over the W24 Swanepoel route modules.
It exposes only checked conditional routes:

* cut-vertex blocker elimination equivalences;
* the concrete boundary witness route into topology-source inputs;
* Lemma 8 frame/order routes;
* Lemma 9 no-early routes;
* selected Figure 8/Figure 9 Euclidean witness routes;
* concrete component and lane-product bridges;
* lower-bound endpoints conditional on supplied components or lanes.

There is intentionally no unconditional public `8 / 31` theorem here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW25RouteAudit

universe u

noncomputable section

abbrev Target : Prop :=
  MinimalStillOpenComponentsW24.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  MinimalStillOpenComponentsW24.LowerBoundAt n C

/-! ## Cut-vertex blocker route -/

namespace CutVertexRoute

abbrev MinimalCutVertexBlocker : Type :=
  NoCutBlockerEliminationW24.MinimalCutVertexBlocker

abbrev MinimalCutVertexBlockerExists : Prop :=
  NoCutBlockerEliminationW24.MinimalCutVertexBlockerExists

abbrev MinimalFailureNoCutVertexFamily : Prop :=
  NoCutBlockerEliminationW24.MinimalFailureNoCutVertexFamily

abbrev MinimalFailureCutVertexContradictionFamily : Prop :=
  NoCutBlockerEliminationW24.MinimalFailureCutVertexContradictionFamily

abbrev MinimalFailureRemainingSlackFamily : Prop :=
  NoCutBlockerEliminationW24.MinimalFailureRemainingSlackFamily

abbrev MinimalFailureDeletionSlackFamily : Prop :=
  NoCutBlockerEliminationW24.MinimalFailureDeletionSlackFamily

theorem blocker_exists_iff_exists_minimalFailure_cutPartition :
    MinimalCutVertexBlockerExists <->
      Exists fun n : Nat =>
        Exists fun C : _root_.UDConfig n =>
          MinimalGraphFacts.IsMinimalClearedFailure C /\
            Nonempty (CutVertexInterface.CutVertexPartition C) :=
  NoCutBlockerEliminationW24.blocker_exists_iff_exists_minimalFailure_cutPartition

theorem not_blocker_iff_noCutVertexFamily :
    Not MinimalCutVertexBlockerExists <->
      MinimalFailureNoCutVertexFamily :=
  NoCutBlockerEliminationW24.not_blocker_iff_noCutVertexFamily

theorem noCutVertexFamily_iff_cutVertexContradictionFamily :
    MinimalFailureNoCutVertexFamily <->
      MinimalFailureCutVertexContradictionFamily :=
  NoCutBlockerEliminationW24.noCutVertexFamily_iff_cutVertexContradictionFamily

theorem not_blocker_iff_partitionContradiction :
    Not (Nonempty MinimalCutVertexBlocker) <->
      MinimalFailureCutVertexContradictionFamily :=
  NoCutBlockerEliminationW24.not_nonempty_minimalCutVertexBlocker_iff_partitionContradiction

theorem not_blocker_iff_remainingSlackFamily :
    Not MinimalCutVertexBlockerExists <->
      MinimalFailureRemainingSlackFamily :=
  NoCutBlockerEliminationW24.not_blocker_iff_remainingSlackFamily

theorem not_blocker_iff_deletionSlackFamily :
    Not MinimalCutVertexBlockerExists <->
      MinimalFailureDeletionSlackFamily :=
  NoCutBlockerEliminationW24.not_blocker_iff_deletionSlackFamily

theorem not_blocker_of_partitionContradiction
    (H : MinimalFailureCutVertexContradictionFamily) :
    Not MinimalCutVertexBlockerExists :=
  NoCutBlockerEliminationW24.not_blocker_of_cutVertexContradictionFamily H

end CutVertexRoute

/-! ## Boundary witness route -/

namespace BoundaryRoute

open JordanBoundaryConcreteInhabitationW24

abbrev MinimalBoundaryTopologyWitnessFamily : Type (u + 1) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.{u}

abbrev ConcreteTriangleRunSourceFamily : Type (u + 1) :=
  JordanBoundaryFamiliesConcreteW23.ConcreteTriangleRunSourceFamily.{u}

abbrev ConcreteExtractionSourceFamily : Type (u + 1) :=
  JordanBoundaryFamiliesConcreteW23.ConcreteExtractionSourceFamily.{u}

abbrev ActualInputsFamily : Type (u + 1) :=
  JordanBoundaryFamiliesConcreteW23.ActualInputsFamily.{u}

abbrev W21NamedDependency : Type (u + 1) :=
  JordanBoundaryConcreteInhabitationW24.W21NamedDependency.{u}

abbrev W21ActualInputsFamily : Type (u + 1) :=
  JordanBoundaryConcreteInhabitationW24.W21ActualInputsFamily.{u}

def concreteTriangleRunSourceFamilyOfBoundaryWitness
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    ConcreteTriangleRunSourceFamily.{u} :=
  F.toConcreteTriangleRunSourceFamily

def concreteExtractionSourceFamilyOfBoundaryWitness
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    ConcreteExtractionSourceFamily.{u} :=
  F.toConcreteExtractionSourceFamily

def actualInputsFamilyOfBoundaryWitness
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    ActualInputsFamily.{u} :=
  F.toActualInputsFamily

def w21NamedDependencyOfBoundaryWitness
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    W21NamedDependency.{u} :=
  F.toW21NamedDependency

def w21ActualInputsFamilyOfBoundaryWitness
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    W21ActualInputsFamily.{u} :=
  F.toW21ActualInputsFamily

theorem concreteTriangleRunSourceFamily_nonempty_of_boundaryWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty ConcreteTriangleRunSourceFamily.{u} :=
  concreteTriangleRunSourceFamily_nonempty_of_minimalBoundaryTopologyWitness h

theorem concreteExtractionSourceFamily_nonempty_of_boundaryWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty ConcreteExtractionSourceFamily.{u} :=
  concreteExtractionSourceFamily_nonempty_of_minimalBoundaryTopologyWitness h

theorem actualInputsFamily_nonempty_of_boundaryWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty ActualInputsFamily.{u} :=
  actualInputsFamily_nonempty_of_minimalBoundaryTopologyWitness h

theorem w21NamedDependency_nonempty_of_boundaryWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty W21NamedDependency.{u} :=
  w21NamedDependency_nonempty_of_minimalBoundaryTopologyWitness h

theorem w21ActualInputsFamily_nonempty_of_boundaryWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty W21ActualInputsFamily.{u} :=
  w21ActualInputsFamily_nonempty_of_minimalBoundaryTopologyWitness h

end BoundaryRoute

/-! ## Lemma 8 frame/order route -/

namespace Lemma8Route

abbrev PayForCutConcreteProducerFamily : Type 1 :=
  PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily

abbrev TopologyArcConcreteProducerFamily : Type (u + 1) :=
  PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}

abbrev ExactPackage
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) : Type (u + 1) :=
  Lemma8ConcreteFrameOrderInhabitationW24.ExactPackage.{u}
    payForCut topologyArc

abbrev ConcreteFrameOrderFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) : Type (u + 1) :=
  Lemma8ConcreteFrameOrderInhabitationW24.ConcreteFrameOrderFamily.{u}
    payForCut topologyArc

abbrev GeometryFieldFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) : Type (u + 1) :=
  Lemma8ConcreteFrameOrderInhabitationW24.GeometryFieldFamily.{u}
    payForCut topologyArc

abbrev FrameRows
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) : Prop :=
  Lemma8ConcreteFrameOrderInhabitationW24.FrameRows.{u}
    payForCut topologyArc

abbrev DegreeSixNoncyclicRows
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) : Prop :=
  Lemma8ConcreteFrameOrderInhabitationW24.DegreeSixNoncyclicRows.{u}
    payForCut topologyArc

theorem concreteFrameOrderFamily_nonempty_iff_exactPackage
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) <->
      Nonempty (ExactPackage.{u} payForCut topologyArc) :=
  Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamily_nonempty_iff_exactPackage
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem concreteFrameOrderFamily_nonempty_iff_geometryFieldFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) <->
      Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) :=
  Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamily_nonempty_iff_geometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem frameRows_iff_degreeSixNoncyclicRows
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :
    FrameRows.{u} payForCut topologyArc <->
      DegreeSixNoncyclicRows.{u} payForCut topologyArc :=
  Lemma8ConcreteFrameOrderInhabitationW24.frameRows_iff_degreeSixNoncyclicRows
    (payForCut := payForCut) (topologyArc := topologyArc)

def concreteFrameOrderFamilyOfRemainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    ConcreteFrameOrderFamily.{u} P.payForCut P.topologyArc :=
  Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamilyOfRemainingLaneProduct
    P

theorem concreteFrameOrderFamily_nonempty_of_remainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    Nonempty (ConcreteFrameOrderFamily.{u} P.payForCut P.topologyArc) :=
  Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamily_nonempty_of_remainingLaneProduct
    P

end Lemma8Route

/-! ## Lemma 9 no-early route -/

namespace Lemma9Route

variable {V : Type u} {G : LocalConfigurations.LocalGraph V}
variable {P : LocalConfigurations.BrokenLatticePredicates G 8}

abbrev ConcreteNoEarlyObstructionPackage
    (P : LocalConfigurations.BrokenLatticePredicates G 8)
    [Fintype V] [DecidableEq V] : Prop :=
  Lemma9NoEarlyInhabitationW24.M8ConcreteNoEarlyObstructionPackage P

abbrev NatLateTripleInputs
    (P : LocalConfigurations.BrokenLatticePredicates G 8) : Type :=
  LateTriplesInterface.M8NatLateTripleInputs P

theorem obstructionPackage_iff_natLateTripleInputs
    [Fintype V] [DecidableEq V] :
    ConcreteNoEarlyObstructionPackage P <->
      Nonempty (NatLateTripleInputs P) :=
  (Lemma9NoEarlyInhabitationW24.nonempty_natLateTripleInputs_iff_obstructionPackage
    (P := P)).symm

def natLateTripleInputs_from_obstructionPackage
    [Fintype V] [DecidableEq V]
    (H : ConcreteNoEarlyObstructionPackage P) :
    NatLateTripleInputs P :=
  Lemma9NoEarlyInhabitationW24.natLateTripleInputs_from_obstructionPackage H

abbrev ConcreteNoEarlyRouteTurnWindowPackage
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Type :=
  Lemma9NoEarlyInhabitationW24.M8ConcreteNoEarlyRouteTurnWindowPackage
    C hmin

def natLateTripleInputs_from_routeTurnWindowPackage
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (D : ConcreteNoEarlyRouteTurnWindowPackage C hmin) :
    LateTriplesInterface.M8NatLateTripleInputs
      D.localLabels.predicates.data :=
  D.natLateTripleInputs

theorem routeTurnWindowPackage_contradiction
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (D : ConcreteNoEarlyRouteTurnWindowPackage C hmin) :
    False :=
  D.contradiction

end Lemma9Route

/-! ## Selected Figure witness route -/

namespace FigureRoute

abbrev SelectedFigureEuclideanWitnessFields :=
  FigureAngleInequalitiesW24.SelectedFigureEuclideanWitnessFields

theorem selectedWitness_E22_E23
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : SelectedFigureEuclideanWitnessFields good turn) :
    Lemma10AnalyticBridge.Figure8SeparatedWindowLowerE22 good turn /\
      Lemma10AnalyticBridge.Figure9AdjacentWindowLowerE23 good turn :=
  FigureAngleInequalitiesW24.SelectedFigureEuclideanWitnessFields.E22_E23 H

theorem selectedWitness_separatedFailuresForceTurn
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : SelectedFigureEuclideanWitnessFields good turn) :
    Lemma10Inequalities.SeparatedFailuresForceTurn good turn :=
  H.separatedFailuresForceTurn

theorem selectedWitness_adjacentFailuresForceTurn
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : SelectedFigureEuclideanWitnessFields good turn) :
    Lemma10Inequalities.AdjacentFailuresForceTurn good turn :=
  H.adjacentFailuresForceTurn

def selectedFields_of_angleContainmentBridges
    {good : Nat -> Prop} {turn : Nat -> Real}
    (A : AngleContainmentInterface.AngleContainmentBridges good turn) :
    SelectedFigureEuclideanWitnessFields good turn :=
  FigureAngleInequalitiesW24.selectedFields_of_angleContainmentBridges A

end FigureRoute

/-! ## Concrete components and lane product -/

namespace ComponentRoute

abbrev ConcreteW23Components : Type 1 :=
  MinimalStillOpenComponentsW24.ConcreteW23Components

abbrev MinimalStillOpenComponents : Type 1 :=
  MinimalStillOpenComponentsW24.MinimalStillOpenComponents

abbrev SourceComponents : Type 1 :=
  MinimalStillOpenComponentsW24.SourceComponents

abbrev LaneProduct : Type 1 :=
  LaneProductAssemblyW24.R.LaneProduct0

abbrev ConcreteComponentLanes : Type (u + 1) :=
  LaneProductAssemblyW24.M8.ConcreteComponentLanes.{u}

abbrev NamedConcreteComponentLanes : Type (u + 1) :=
  LaneProductAssemblyW24.M8.NamedConcreteComponentLanes.{u}

def minimalStillOpenComponentsOfConcreteW23Components
    (P : ConcreteW23Components) :
    MinimalStillOpenComponents :=
  P.toMinimalStillOpenComponents

def sourceComponentsOfConcreteW23Components
    (P : ConcreteW23Components) :
    SourceComponents :=
  P.toSourceComponents

def laneProductOfMinimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    LaneProduct :=
  LaneProductAssemblyW24.laneProductOfMinimalStillOpenComponents P

def laneProductOfConcreteW23Components
    (P : ConcreteW23Components) :
    LaneProduct :=
  laneProductOfMinimalStillOpenComponents P.toMinimalStillOpenComponents

def laneProductOfConcreteComponentLanes
    (P : ConcreteComponentLanes.{u}) :
    RemainingSourceComponentsInhabitationW22.LaneProduct.{u} :=
  LaneProductAssemblyW24.laneProductOfConcreteComponentLanes P

def laneProductOfNamedConcreteComponentLanes
    (P : NamedConcreteComponentLanes.{u}) :
    RemainingSourceComponentsInhabitationW22.LaneProduct.{u} :=
  LaneProductAssemblyW24.laneProductOfNamedConcreteComponentLanes P

theorem minimalStillOpenComponents_nonempty_of_concreteW23Components :
    Nonempty ConcreteW23Components -> Nonempty MinimalStillOpenComponents :=
  MinimalStillOpenComponentsW24.minimalStillOpenComponents_nonempty_of_concreteW23Components

theorem sourceComponents_nonempty_of_concreteW23Components :
    Nonempty ConcreteW23Components -> Nonempty SourceComponents :=
  MinimalStillOpenComponentsW24.sourceComponents_nonempty_of_concreteW23Components

theorem laneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty LaneProduct <-> Nonempty MinimalStillOpenComponents :=
  LaneProductAssemblyW24.laneProduct_nonempty_iff_minimalStillOpenComponents

theorem laneProduct_nonempty_of_concreteW23Components
    (h : Nonempty ConcreteW23Components) :
    Nonempty LaneProduct := by
  cases h with
  | intro P =>
      exact Nonempty.intro (laneProductOfConcreteW23Components P)

theorem laneProduct_nonempty_of_concreteComponentLanes
    (P : ConcreteComponentLanes.{u}) :
    Nonempty (RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :=
  LaneProductAssemblyW24.laneProduct_nonempty_of_concreteComponentLanes P

theorem laneProduct_nonempty_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes.{u}) :
    Nonempty (RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :=
  LaneProductAssemblyW24.laneProduct_nonempty_of_namedConcreteComponentLanes P

end ComponentRoute

/-! ## Conditional lower-bound bridge -/

namespace ConditionalLowerBound

theorem targetLowerBoundEightThirtyOne_of_concreteW23Components
    (P : ComponentRoute.ConcreteW23Components) :
    Target :=
  MinimalStillOpenComponentsW24.targetLowerBoundEightThirtyOne_of_concreteW23Components
    P

theorem targetLowerBoundEightThirtyOne_of_laneProduct
    (P : ComponentRoute.LaneProduct) :
    Target :=
  LaneProductAssemblyW24.targetLowerBoundEightThirtyOne_of_laneProduct P

theorem targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents
    (P : ComponentRoute.MinimalStillOpenComponents) :
    Target :=
  LaneProductAssemblyW24.targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents
    P

theorem targetLowerBoundEightThirtyOne_of_concreteComponentLanes
    (P : ComponentRoute.ConcreteComponentLanes.{0}) :
    Target :=
  LaneProductAssemblyW24.targetLowerBoundEightThirtyOne_of_concreteComponentLanes
    P

theorem targetLowerBoundEightThirtyOne_of_namedConcreteComponentLanes
    (P : ComponentRoute.NamedConcreteComponentLanes.{0}) :
    Target :=
  LaneProductAssemblyW24.targetLowerBoundEightThirtyOne_of_namedConcreteComponentLanes
    P

theorem lower_bound_eight_thirty_one_of_concreteW23Components
    (P : ComponentRoute.ConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_concreteW23Components P n C

theorem lower_bound_eight_thirty_one_of_laneProduct
    (P : ComponentRoute.LaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_laneProduct P n C

theorem lower_bound_eight_thirty_one_of_minimalStillOpenComponents
    (P : ComponentRoute.MinimalStillOpenComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents P n C

theorem lower_bound_eight_thirty_one_of_concreteComponentLanes
    (P : ComponentRoute.ConcreteComponentLanes.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_concreteComponentLanes P n C

theorem lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    (P : ComponentRoute.NamedConcreteComponentLanes.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_namedConcreteComponentLanes P n C

end ConditionalLowerBound

end

end SwanepoelW25RouteAudit
end Swanepoel

namespace Verified

universe u

open Swanepoel.SwanepoelW25RouteAudit

abbrev SwanepoelW25CutVertexBlocker : Type :=
  CutVertexRoute.MinimalCutVertexBlocker

abbrev SwanepoelW25BoundaryWitnessFamily : Type (u + 1) :=
  BoundaryRoute.MinimalBoundaryTopologyWitnessFamily.{u}

abbrev SwanepoelW25AuditConcreteW23Components : Type 1 :=
  ComponentRoute.ConcreteW23Components

abbrev SwanepoelW25AuditLaneProduct : Type 1 :=
  ComponentRoute.LaneProduct

abbrev SwanepoelW25AuditConcreteComponentLanes : Type 1 :=
  ComponentRoute.ConcreteComponentLanes.{0}

abbrev SwanepoelW25AuditNamedConcreteComponentLanes : Type 1 :=
  ComponentRoute.NamedConcreteComponentLanes.{0}

theorem swanepoel_w25_cutVertexBlocker_eliminated_iff_partitionContradiction :
    Not (Nonempty SwanepoelW25CutVertexBlocker) <->
      CutVertexRoute.MinimalFailureCutVertexContradictionFamily :=
  CutVertexRoute.not_blocker_iff_partitionContradiction

theorem swanepoel_w25_boundaryWitness_actualInputsFamily_nonempty
    (h : Nonempty SwanepoelW25BoundaryWitnessFamily.{u}) :
    Nonempty BoundaryRoute.ActualInputsFamily.{u} :=
  BoundaryRoute.actualInputsFamily_nonempty_of_boundaryWitness h

theorem swanepoel_w25_lemma8ConcreteFrameOrderFamily_nonempty_iff_exactPackage
    (payForCut :
      Lemma8Route.PayForCutConcreteProducerFamily)
    (topologyArc :
      Lemma8Route.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (Lemma8Route.ConcreteFrameOrderFamily.{u}
          payForCut topologyArc) <->
      Nonempty
        (Lemma8Route.ExactPackage.{u} payForCut topologyArc) :=
  Lemma8Route.concreteFrameOrderFamily_nonempty_iff_exactPackage
    payForCut topologyArc

theorem swanepoel_w25_lemma9ObstructionPackage_iff_natLateTripleInputs
    {V : Type u} {G : Swanepoel.LocalConfigurations.LocalGraph V}
    {P : Swanepoel.LocalConfigurations.BrokenLatticePredicates G 8}
    [Fintype V] [DecidableEq V] :
    Lemma9Route.ConcreteNoEarlyObstructionPackage P <->
      Nonempty (Lemma9Route.NatLateTripleInputs P) :=
  Lemma9Route.obstructionPackage_iff_natLateTripleInputs (P := P)

theorem swanepoel_w25_selectedFigureWitness_E22_E23
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H :
      FigureRoute.SelectedFigureEuclideanWitnessFields good turn) :
    Swanepoel.Lemma10AnalyticBridge.Figure8SeparatedWindowLowerE22
        good turn /\
      Swanepoel.Lemma10AnalyticBridge.Figure9AdjacentWindowLowerE23
        good turn :=
  FigureRoute.selectedWitness_E22_E23 H

theorem swanepoel_w25_laneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty SwanepoelW25AuditLaneProduct <->
      Nonempty ComponentRoute.MinimalStillOpenComponents :=
  ComponentRoute.laneProduct_nonempty_iff_minimalStillOpenComponents

theorem lower_bound_eight_thirty_one_of_swanepoel_w25_concreteW23Components
    (P : SwanepoelW25AuditConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  ConditionalLowerBound.lower_bound_eight_thirty_one_of_concreteW23Components
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoel_w25_laneProduct
    (P : SwanepoelW25AuditLaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  ConditionalLowerBound.lower_bound_eight_thirty_one_of_laneProduct P n C

theorem lower_bound_eight_thirty_one_of_swanepoel_w25_concreteComponentLanes
    (P : SwanepoelW25AuditConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  ConditionalLowerBound.lower_bound_eight_thirty_one_of_concreteComponentLanes
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoel_w25_namedConcreteComponentLanes
    (P : SwanepoelW25AuditNamedConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  ConditionalLowerBound.lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    P n C

end Verified
end ErdosProblems1066
