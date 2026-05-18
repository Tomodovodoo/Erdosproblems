import ErdosProblems1066.PachToth.DeformedPlacement
import ErdosProblems1066.PachToth.ClosedPlacementInterface
import ErdosProblems1066.PachToth.ClosedChainExistence
import ErdosProblems1066.PachToth.ClosedPlacementAlgebra
import ErdosProblems1066.PachToth.GeneratedSeparationInterface
import ErdosProblems1066.PachToth.RemainderPlacement

set_option autoImplicit false

/-!
# Non-rigid closed-placement interface

This module is a source-faithful interface for non-rigid Pach--Toth closed
placements.  It only repackages explicit cyclic point, orbit, and edge data
into `DeformedPlacement.ClosedPlacement`, then routes that checked placement
to the exact-block and arbitrary-`n` target wrappers.

The same-block and connector unit distances are direct fields of the data
below, or are supplied by transition certificates.  No translated rigid
connector specialization is used.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonRigidClosedPlacementInterface

open Arithmetic
open ClosedPlacementInterface
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The smallest non-rigid coordinate certificate: a cyclic point map with
the exact metric fields required by `DeformedPlacement.ClosedPlacement`. -/
structure ExplicitCyclicPointEdgeData (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1
  cross_connector_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1

namespace ExplicitCyclicPointEdgeData

/-- Repackage direct non-rigid point/edge data as the existing explicit
closed-placement certificate. -/
def toExplicitClosedPlacementCertificate {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicPointEdgeData k hk) :
    ExplicitClosedPlacementCertificate k hk where
  point := D.point
  separated := D.separated
  same_block_edges_unit := D.same_block_edges_unit
  cross_connector_edges_unit := D.cross_connector_edges_unit

/-- Build the checked non-rigid closed placement carried by the data. -/
def toClosedPlacement {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicPointEdgeData k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  D.toExplicitClosedPlacementCertificate.toClosedPlacement

@[simp]
theorem toClosedPlacement_point {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicPointEdgeData k hk)
    (i : Fin k) (v : LocalVertex) :
    D.toClosedPlacement.point i v = D.point i v :=
  rfl

/-- The exact-chain upper certificate obtained from the checked closed
placement. -/
def exactChainUpper {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicPointEdgeData k hk) :
    SplitSoundness.ExactChainUpper k :=
  SplitCertificateBridge.exactChainUpperOfClosedPlacement D.toClosedPlacement

/-- A single closed non-rigid data set gives the exact-block target at
`16 * k`. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicPointEdgeData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  refine Exists.intro D.toClosedPlacement.config ?_
  intro s hs
  have hfive :
      s.card <= 5 * k :=
    IndexedChain.independent_card_le_five_mul hk
      D.toClosedPlacement.toIndexedChainRealization s hs
  have harith : 5 * k <= ceilDiv (5 * (16 * k)) 16 := by
    unfold ceilDiv
    omega
  exact le_trans hfive harith

end ExplicitCyclicPointEdgeData

/-- A cyclic orbit interface with explicit successor transition maps.  The
successor equation records closure of the orbit, including the final wrap
back to block `0`; connector unit distances are certified against the stored
transition target. -/
structure ExplicitCyclicOrbitEdgeData (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  step : Fin k -> OrientationData.OrientedTransition
  successor_eq :
    forall i : Fin k, forall v : LocalVertex,
      point (cyclicSucc hk i) v = (step i).placeNext (point i) v
  connector_unit_edges :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point i u) ((step i).placeNext (point i) v) = 1
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1

namespace ExplicitCyclicOrbitEdgeData

/-- Repackage successor-compatible orbit data through
`ClosedChainExistence`. -/
def toSuccessorCompatibleCyclicPointOrbit {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicOrbitEdgeData k hk) :
    ClosedChainExistence.SuccessorCompatibleCyclicPointOrbit k hk where
  point := D.point
  step := D.step
  successor_compatible := D.successor_eq
  connector_unit_edges := D.connector_unit_edges
  separated := D.separated
  same_block_edges_unit := D.same_block_edges_unit

/-- The orbit data supplies the transition-based closed-placement
certificate. -/
def toExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicOrbitEdgeData k hk) :
    ExplicitTransitionClosedPlacementCertificate k hk :=
  D.toSuccessorCompatibleCyclicPointOrbit
    |>.toExplicitTransitionClosedPlacementCertificate

/-- Forget the transition structure to direct point/edge data. -/
def toExplicitCyclicPointEdgeData {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicOrbitEdgeData k hk) :
    ExplicitCyclicPointEdgeData k hk where
  point := D.point
  separated := D.separated
  same_block_edges_unit := D.same_block_edges_unit
  cross_connector_edges_unit := by
    intro i u v hconn
    rw [D.successor_eq i v]
    exact D.connector_unit_edges i u v hconn

/-- Build the checked non-rigid closed placement from successor-orbit data. -/
def toClosedPlacement {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicOrbitEdgeData k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  D.toSuccessorCompatibleCyclicPointOrbit.toClosedPlacement

@[simp]
theorem toClosedPlacement_point {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicOrbitEdgeData k hk)
    (i : Fin k) (v : LocalVertex) :
    D.toClosedPlacement.point i v = D.point i v :=
  rfl

/-- The one-step successor equation exposed through `ClosedPlacementAlgebra`. -/
theorem transition_target_eq_placeNext {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicOrbitEdgeData k hk)
    (i : Fin k) (v : LocalVertex) :
    D.point (cyclicSucc hk i) v =
      (D.toExplicitTransitionClosedPlacementCertificate.transition i).transition.placeNext
        (D.point i) v :=
  ClosedPlacementAlgebra.transition_target_eq_placeNext
    D.toExplicitTransitionClosedPlacementCertificate i v

/-- The exact-chain upper certificate obtained from the checked closed
placement. -/
def exactChainUpper {k : Nat} {hk : 0 < k}
    (D : ExplicitCyclicOrbitEdgeData k hk) :
    SplitSoundness.ExactChainUpper k :=
  SplitCertificateBridge.exactChainUpperOfClosedPlacement D.toClosedPlacement

end ExplicitCyclicOrbitEdgeData

/-- Same/opposite transition data specialized to a cyclic point orbit.  The
connector-unit obligations live in `obligations`; the remaining fields are
the cyclic successor equation and the global/same-block metric facts. -/
structure SameOppositeCyclicOrbitData
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  orientation : Fin k -> OrientationData.BlockOrientation
  successor_eq :
    forall i : Fin k, forall v : LocalVertex,
      point (cyclicSucc hk i) v =
        (O.transitionFor (orientation i)).placeNext (point i) v
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1

namespace SameOppositeCyclicOrbitData

/-- Build the transition-certificate interface from a same/opposite orbit. -/
def toExplicitTransitionClosedPlacementCertificate
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    (D : SameOppositeCyclicOrbitData O k hk) :
    ExplicitTransitionClosedPlacementCertificate k hk :=
  ClosedChainConstruction.explicitTransitionCertificateOfSameOpposite
    O D.point D.orientation D.successor_eq D.separated
    D.same_block_edges_unit

/-- Build the checked non-rigid closed placement from same/opposite orbit
data. -/
def toClosedPlacement
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    (D : SameOppositeCyclicOrbitData O k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  D.toExplicitTransitionClosedPlacementCertificate.toClosedPlacement

@[simp]
theorem toClosedPlacement_point
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    (D : SameOppositeCyclicOrbitData O k hk)
    (i : Fin k) (v : LocalVertex) :
    D.toClosedPlacement.point i v = D.point i v :=
  rfl

/-- The stored orientation word is retained by the generated transition
certificate. -/
theorem transition_orientation
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    (D : SameOppositeCyclicOrbitData O k hk)
    (i : Fin k) :
    (D.toExplicitTransitionClosedPlacementCertificate.transition i).transition.orientation =
      D.orientation i :=
  ClosedPlacementAlgebra.sameOpposite_transition_orientation
    O D.point D.orientation D.successor_eq D.separated
    D.same_block_edges_unit i

/-- Iterating the stored transition word agrees with the cyclic point orbit. -/
theorem iteratedTransitionBlock_eq_point_iterate
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    (D : SameOppositeCyclicOrbitData O k hk)
    (i : Fin k) (n : Nat) (v : LocalVertex) :
    ClosedPlacementAlgebra.iteratedTransitionBlock
        O hk D.point D.orientation i n v =
      D.point ((cyclicSucc hk)^[n] i) v :=
  ClosedPlacementAlgebra.iteratedTransitionBlock_eq_point_iterate
    O D.point D.orientation D.successor_eq i n v

/-- The exact-chain upper certificate obtained from the checked closed
placement. -/
def exactChainUpper
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    (D : SameOppositeCyclicOrbitData O k hk) :
    SplitSoundness.ExactChainUpper k :=
  SplitCertificateBridge.exactChainUpperOfClosedPlacement D.toClosedPlacement

end SameOppositeCyclicOrbitData

/-- Same-block isometry against the checked one-block certificate gives the
unit same-block edge field required by the non-rigid point interfaces. -/
theorem generated_same_block_edges_unit_of_isometry
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation) :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation i v) =
            1 := by
  intro i u v _huv hadj
  calc
    _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation i v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v)) :=
        same_block_isometry i u v
    _ = 1 :=
        OneBlockSoundness.oneBlockCertificate.same_block_edges_unit u v hadj

/-- Generated-period data with full metric hypotheses supplies the
same/opposite cyclic-orbit interface. -/
def sameOppositeCyclicOrbitData_of_generatedPeriod
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    SameOppositeCyclicOrbitData O k hk where
  point := GeneratedClosedChain.generatedPoint O hk base orientation
  orientation := orientation
  successor_eq :=
    GeneratedClosedChain.generatedPoint_successor_compatible
      O hk base orientation period
  separated := H.separated
  same_block_edges_unit :=
    generated_same_block_edges_unit_of_isometry
      O hk base orientation H.same_block_isometry

/-- Generated-period data with reduced same-block hypotheses supplies the
same/opposite cyclic-orbit interface. -/
def sameOppositeCyclicOrbitData_of_generatedPeriod_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    SameOppositeCyclicOrbitData O k hk :=
  sameOppositeCyclicOrbitData_of_generatedPeriod
    O hk base orientation period
    { separated := H.separated
      same_block_isometry :=
        GeneratedSeparationInterface.same_block_isometry_of_reduced
          O hk base orientation H }

@[simp]
theorem sameOppositeCyclicOrbitData_of_generatedPeriod_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (sameOppositeCyclicOrbitData_of_generatedPeriod
      O hk base orientation period H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- Generated-period data with full metric hypotheses supplies the explicit
successor-orbit edge interface. -/
def explicitCyclicOrbitEdgeData_of_generatedPeriod
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    ExplicitCyclicOrbitEdgeData k hk where
  point := GeneratedClosedChain.generatedPoint O hk base orientation
  step := GeneratedClosedChain.generatedStep O orientation
  successor_eq :=
    GeneratedClosedChain.generatedPoint_successor_compatible
      O hk base orientation period
  connector_unit_edges := by
    intro i u v hconn
    exact
      Figure2Certificate.SameOppositeTransitionObligations.transitionFor_connector_unit_edges
        O (orientation i)
        (GeneratedClosedChain.generatedPoint O hk base orientation i)
        u v hconn
  separated := H.separated
  same_block_edges_unit :=
    generated_same_block_edges_unit_of_isometry
      O hk base orientation H.same_block_isometry

/-- Generated-period data with reduced same-block hypotheses supplies the
explicit successor-orbit edge interface. -/
def explicitCyclicOrbitEdgeData_of_generatedPeriod_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    ExplicitCyclicOrbitEdgeData k hk :=
  explicitCyclicOrbitEdgeData_of_generatedPeriod
    O hk base orientation period
    { separated := H.separated
      same_block_isometry :=
        GeneratedSeparationInterface.same_block_isometry_of_reduced
          O hk base orientation H }

@[simp]
theorem explicitCyclicOrbitEdgeData_of_generatedPeriod_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (explicitCyclicOrbitEdgeData_of_generatedPeriod
      O hk base orientation period H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- Generated-period data with full metric hypotheses supplies the direct
cyclic point/edge interface. -/
def explicitCyclicPointEdgeData_of_generatedPeriod
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    ExplicitCyclicPointEdgeData k hk :=
  (explicitCyclicOrbitEdgeData_of_generatedPeriod
    O hk base orientation period H).toExplicitCyclicPointEdgeData

/-- Generated-period data with reduced same-block hypotheses supplies the
direct cyclic point/edge interface. -/
def explicitCyclicPointEdgeData_of_generatedPeriod_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    ExplicitCyclicPointEdgeData k hk :=
  (explicitCyclicOrbitEdgeData_of_generatedPeriod_reduced
    O hk base orientation period H).toExplicitCyclicPointEdgeData

@[simp]
theorem explicitCyclicPointEdgeData_of_generatedPeriod_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (explicitCyclicPointEdgeData_of_generatedPeriod
      O hk base orientation period H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- Generated-period data with full metric hypotheses builds the checked
non-rigid closed placement. -/
def closedPlacement_of_generatedPeriod
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  (explicitCyclicPointEdgeData_of_generatedPeriod
    O hk base orientation period H).toClosedPlacement

/-- Generated-period data with reduced same-block hypotheses builds the
checked non-rigid closed placement. -/
def closedPlacement_of_generatedPeriod_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  (explicitCyclicPointEdgeData_of_generatedPeriod_reduced
    O hk base orientation period H).toClosedPlacement

@[simp]
theorem closedPlacement_of_generatedPeriod_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacement_of_generatedPeriod
      O hk base orientation period H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- Exact-block target from generated-period data and full metric
hypotheses, routed through the direct non-rigid point/edge interface. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriod
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    ExplicitCyclicPointEdgeData.targetUpperConstructionFiveSixteenAt_exactBlock
      (explicitCyclicPointEdgeData_of_generatedPeriod
        O hk base orientation period H)

/-- Exact-block target from generated-period data with same-block metric
control reduced to base-block isometry and transition preservation. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriod_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    ExplicitCyclicPointEdgeData.targetUpperConstructionFiveSixteenAt_exactBlock
      (explicitCyclicPointEdgeData_of_generatedPeriod_reduced
        O hk base orientation period H)

/-- Exact target wrapper for any family of checked non-rigid closed
placements. -/
theorem targetUpperConstructionFiveSixteen_of_closedPlacements
    (H : forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteen :=
  DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements H

/-- Arbitrary-`n` target wrapper for any family of checked non-rigid closed
placements.  The remainder is handled by the checked far-apart remainder
bridge; the closed chain itself is the supplied non-rigid placement. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    (H : forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  have hr : n % 16 < 16 := by
    exact Nat.mod_lt n (by norm_num)
  have hn : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  have hAt :
      targetUpperConstructionFiveSixteenAt (16 * (n / 16) + n % 16) := by
    by_cases hk : 0 < n / 16
    case pos =>
      exact
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          (SplitCertificateBridge.exactChainUpperOfClosedPlacement
            (H (n / 16) hk))
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
    case neg =>
      have hk0 : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
      have hzero :
          targetUpperConstructionFiveSixteenAt (16 * 0 + n % 16) :=
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          SplitSoundness.emptyExactChainUpper
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
      simpa [hk0] using hzero
  rw [hn]
  exact hAt

/-- Exact target wrapper for direct point/edge data. -/
theorem targetUpperConstructionFiveSixteen_of_explicitCyclicPointEdgeData
    (H : forall (k : Nat) (hk : 0 < k),
      ExplicitCyclicPointEdgeData k hk) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_closedPlacements
    (fun k hk => (H k hk).toClosedPlacement)

/-- Arbitrary target wrapper for direct point/edge data. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitCyclicPointEdgeData
    (H : forall (k : Nat) (hk : 0 < k),
      ExplicitCyclicPointEdgeData k hk) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    (fun k hk => (H k hk).toClosedPlacement)

/-- Exact target wrapper for explicit successor-orbit data. -/
theorem targetUpperConstructionFiveSixteen_of_explicitCyclicOrbitEdgeData
    (H : forall (k : Nat) (hk : 0 < k),
      ExplicitCyclicOrbitEdgeData k hk) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_closedPlacements
    (fun k hk => (H k hk).toClosedPlacement)

/-- Arbitrary target wrapper for explicit successor-orbit data. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitCyclicOrbitEdgeData
    (H : forall (k : Nat) (hk : 0 < k),
      ExplicitCyclicOrbitEdgeData k hk) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    (fun k hk => (H k hk).toClosedPlacement)

/-- Exact target wrapper for same/opposite cyclic-orbit data. -/
theorem targetUpperConstructionFiveSixteen_of_sameOppositeCyclicOrbitData
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    (H : forall (k : Nat) (hk : 0 < k),
      SameOppositeCyclicOrbitData O k hk) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_closedPlacements
    (fun k hk => (H k hk).toClosedPlacement)

/-- Arbitrary target wrapper for same/opposite cyclic-orbit data. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_sameOppositeCyclicOrbitData
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    (H : forall (k : Nat) (hk : 0 < k),
      SameOppositeCyclicOrbitData O k hk) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    (fun k hk => (H k hk).toClosedPlacement)

/-- A generated-period family plus full generated metric hypotheses gives
the exact Pach--Toth target through the non-rigid point/edge interface. -/
theorem targetUpperConstructionFiveSixteen_of_generatedPeriodFamily
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : F.Periods)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_explicitCyclicPointEdgeData
    (fun k hk =>
      explicitCyclicPointEdgeData_of_generatedPeriod
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)
        (period k hk) (H.metric k hk))

/-- A generated-period family gives the exact target when same-block metric
control is reduced to base-block isometry and transition preservation. -/
theorem targetUpperConstructionFiveSixteen_of_generatedPeriodFamily_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : F.Periods)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_explicitCyclicPointEdgeData
    (fun k hk =>
      explicitCyclicPointEdgeData_of_generatedPeriod_reduced
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)
        (period k hk) (H.metric k hk))

/-- A generated-period family plus full generated metric hypotheses gives
the arbitrary vertex-count target through the non-rigid split route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPeriodFamily
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : F.Periods)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_explicitCyclicPointEdgeData
    (fun k hk =>
      explicitCyclicPointEdgeData_of_generatedPeriod
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)
        (period k hk) (H.metric k hk))

/-- A generated-period family gives the arbitrary vertex-count target when
same-block metric control is reduced to base-block isometry and transition
preservation. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPeriodFamily_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : F.Periods)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_explicitCyclicPointEdgeData
    (fun k hk =>
      explicitCyclicPointEdgeData_of_generatedPeriod_reduced
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)
        (period k hk) (H.metric k hk))

end

end NonRigidClosedPlacementInterface
end PachToth
end ErdosProblems1066
