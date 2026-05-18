import ErdosProblems1066.PachToth.DeformedPlacement
import ErdosProblems1066.PachToth.GeneratedClosedChainReduction
import ErdosProblems1066.PachToth.GeneratedSeparationInterface
import ErdosProblems1066.PachToth.PeriodInterface

/-!
# Closed-placement closure bridge

This module closes the generated-chain pipeline at the algebraic period
interface.  A generated closure equation from `PeriodInterface` is converted
to the period equation expected by the generated-chain reduction, producing
closed deformed placements and the corresponding target statements from the
named generated metric hypotheses.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementClosure

open FiniteGraph
open GeneratedClosedChainReduction

noncomputable section

abbrev R2 := Prod Real Real

/-- Algebraic generated closure gives the final-block period equation used by
the generated-chain metric interface. -/
def generatedPeriod_of_generatedClosure
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation) :
    GeneratedSeparationInterface.GeneratedPeriod O hk base orientation :=
  PeriodInterface.generatedPeriodEquation_of_generatedClosureEquation
    O hk base orientation closure

/-- Package a generated chain closed by an explicit generated-period equation
as a transition closed-placement certificate. -/
def explicitTransitionClosedPlacementCertificate_of_generatedPeriod
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  GeneratedSeparationInterface.explicitTransitionClosedPlacementCertificate
    O hk base orientation period H

@[simp]
theorem explicitTransitionClosedPlacementCertificate_of_generatedPeriod_point
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
    (explicitTransitionClosedPlacementCertificate_of_generatedPeriod
      O hk base orientation period H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- Reduced metric data also packages into a transition closed-placement
certificate once the generated-period equation is known. -/
def explicitTransitionClosedPlacementCertificate_of_generatedPeriod_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  GeneratedSeparationInterface.explicitTransitionClosedPlacementCertificate_reduced
    O hk base orientation period H

@[simp]
theorem explicitTransitionClosedPlacementCertificate_of_generatedPeriod_reduced_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (explicitTransitionClosedPlacementCertificate_of_generatedPeriod_reduced
      O hk base orientation period H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- Package a generated chain closed by the algebraic closure equation as a
transition closed-placement certificate. -/
def explicitTransitionClosedPlacementCertificate_of_generatedClosure
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  explicitTransitionClosedPlacementCertificate_of_generatedPeriod
    O hk base orientation
    (generatedPeriod_of_generatedClosure O hk base orientation closure) H

/-- Reduced metric data also packages into a transition closed-placement
certificate once the algebraic generated closure equation is known. -/
def explicitTransitionClosedPlacementCertificate_of_generatedClosure_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  explicitTransitionClosedPlacementCertificate_of_generatedPeriod_reduced
    O hk base orientation
    (generatedPeriod_of_generatedClosure O hk base orientation closure) H

/-- Build the deformed closed placement carried by generated-period and full
generated metric data. -/
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
  (explicitTransitionClosedPlacementCertificate_of_generatedPeriod
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

/-- Build the deformed closed placement carried by generated-period and
reduced generated metric data. -/
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
  (explicitTransitionClosedPlacementCertificate_of_generatedPeriod_reduced
    O hk base orientation period H).toClosedPlacement

@[simp]
theorem closedPlacement_of_generatedPeriod_reduced_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacement_of_generatedPeriod_reduced
      O hk base orientation period H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- Build the deformed closed placement carried by generated closure and full
generated metric data. -/
def closedPlacement_of_generatedClosure
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacement_of_generatedPeriod O hk base orientation
    (generatedPeriod_of_generatedClosure O hk base orientation closure) H

@[simp]
theorem closedPlacement_of_generatedClosure_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacement_of_generatedClosure
      O hk base orientation closure H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- Build the deformed closed placement carried by generated closure and
reduced generated metric data. -/
def closedPlacement_of_generatedClosure_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacement_of_generatedPeriod_reduced O hk base orientation
    (generatedPeriod_of_generatedClosure O hk base orientation closure) H

@[simp]
theorem closedPlacement_of_generatedClosure_reduced_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacement_of_generatedClosure_reduced
      O hk base orientation closure H).point i v =
        GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- A generated-period equation and full metric data produce the downstream
closed-placement existence statement with the generated point map. -/
theorem exists_closedPlacement_of_generatedPeriod
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = GeneratedClosedChain.generatedPoint O hk base orientation := by
  exact
    Exists.intro
      (closedPlacement_of_generatedPeriod O hk base orientation period H)
      rfl

/-- A generated-period equation and reduced metric data produce the downstream
closed-placement existence statement with the generated point map. -/
theorem exists_closedPlacement_of_generatedPeriod_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = GeneratedClosedChain.generatedPoint O hk base orientation := by
  exact
    Exists.intro
      (closedPlacement_of_generatedPeriod_reduced
        O hk base orientation period H)
      rfl

/-- A generated closure equation and full metric data produce the downstream
closed-placement existence statement with the generated point map. -/
theorem exists_closedPlacement_of_generatedClosure
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = GeneratedClosedChain.generatedPoint O hk base orientation := by
  exact
    Exists.intro
      (closedPlacement_of_generatedClosure O hk base orientation closure H)
      rfl

/-- A generated closure equation and reduced metric data produce the
downstream closed-placement existence statement with the generated point map. -/
theorem exists_closedPlacement_of_generatedClosure_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = GeneratedClosedChain.generatedPoint O hk base orientation := by
  exact
    Exists.intro
      (closedPlacement_of_generatedClosure_reduced
        O hk base orientation closure H)
      rfl

/-- Exact-block target from generated-period and full generated metric data. -/
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
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteenAt_exactBlock
      O hk base orientation period H

/-- Exact-block target from generated-period and reduced generated metric
data. -/
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
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteenAt_exactBlock_reduced
      O hk base orientation period H

/-- Exact-block target from generated closure and full generated metric data. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedClosure
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriod
      O hk base orientation
      (generatedPeriod_of_generatedClosure O hk base orientation closure)
      H

/-- Exact-block target from generated closure and reduced generated metric
data. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedClosure_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure : PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriod_reduced
      O hk base orientation
      (generatedPeriod_of_generatedClosure O hk base orientation closure)
      H

/-- Algebraic closure equations for every member of a generated-chain
family. -/
def GeneratedChainFamilyClosures
    (F : GeneratedSeparationInterface.GeneratedChainFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    PeriodInterface.GeneratedClosureEquation (F.O k hk) hk (F.base k hk)
      (F.orientation k hk)

/-- Family closure equations converted to the period hypotheses used by the
generated-chain interface. -/
def generatedChainFamilyPeriodsOfClosures
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F) :
    GeneratedSeparationInterface.GeneratedChainFamily.Periods F :=
  fun k hk =>
    generatedPeriod_of_generatedClosure (F.O k hk) hk (F.base k hk)
      (F.orientation k hk) (closure k hk)

@[simp]
theorem generatedChainFamilyPeriodsOfClosures_apply
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (k : Nat) (hk : 0 < k) :
    generatedChainFamilyPeriodsOfClosures F closure k hk =
      generatedPeriod_of_generatedClosure (F.O k hk) hk (F.base k hk)
        (F.orientation k hk) (closure k hk) :=
  rfl

/-- Generated period and full metric hypotheses give closed placements for
every positive block count in the family. -/
def closedPlacementFamily_of_generatedPeriod
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : GeneratedSeparationInterface.GeneratedChainFamily.Periods F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk =>
    closedPlacement_of_generatedPeriod (F.O k hk) hk (F.base k hk)
      (F.orientation k hk) (period k hk) (H.metric k hk)

/-- Generated period and reduced metric hypotheses give closed placements for
every positive block count in the family. -/
def closedPlacementFamily_of_generatedPeriod_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : GeneratedSeparationInterface.GeneratedChainFamily.Periods F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk =>
    closedPlacement_of_generatedPeriod_reduced (F.O k hk) hk (F.base k hk)
      (F.orientation k hk) (period k hk) (H.metric k hk)

@[simp]
theorem closedPlacementFamily_of_generatedPeriod_point
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : GeneratedSeparationInterface.GeneratedChainFamily.Periods F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementFamily_of_generatedPeriod F period H k hk).point i v =
      GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
        (F.orientation k hk) i v :=
  rfl

@[simp]
theorem closedPlacementFamily_of_generatedPeriod_reduced_point
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : GeneratedSeparationInterface.GeneratedChainFamily.Periods F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementFamily_of_generatedPeriod_reduced F period H k hk).point
        i v =
      GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
        (F.orientation k hk) i v :=
  rfl

/-- Generated closure and full metric hypotheses give closed placements for
every positive block count in the family. -/
def closedPlacementFamily_of_generatedClosure
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk =>
    closedPlacement_of_generatedClosure (F.O k hk) hk (F.base k hk)
      (F.orientation k hk) (closure k hk) (H.metric k hk)

@[simp]
theorem closedPlacementFamily_of_generatedClosure_point
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementFamily_of_generatedClosure F closure H k hk).point i v =
      GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
        (F.orientation k hk) i v :=
  rfl

/-- Generated closure and reduced metric hypotheses give closed placements for
every positive block count in the family. -/
def closedPlacementFamily_of_generatedClosure_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk =>
    closedPlacement_of_generatedClosure_reduced (F.O k hk) hk (F.base k hk)
      (F.orientation k hk) (closure k hk) (H.metric k hk)

@[simp]
theorem closedPlacementFamily_of_generatedClosure_reduced_point
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementFamily_of_generatedClosure_reduced F closure H k hk).point
        i v =
      GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
        (F.orientation k hk) i v :=
  rfl

/-- The exact-block Pach--Toth target follows from a generated-chain family
closed by explicit generated-period equations and full metric data. -/
theorem targetUpperConstructionFiveSixteen_of_generatedPeriod_family
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : GeneratedSeparationInterface.GeneratedChainFamily.Periods F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    targetUpperConstructionFiveSixteen := by
  exact
    DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
      (closedPlacementFamily_of_generatedPeriod F period H)

/-- The exact-block Pach--Toth target follows from a generated-chain family
closed by explicit generated-period equations and reduced metric data. -/
theorem targetUpperConstructionFiveSixteen_of_generatedPeriod_family_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : GeneratedSeparationInterface.GeneratedChainFamily.Periods F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    targetUpperConstructionFiveSixteen := by
  exact
    DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
      (closedPlacementFamily_of_generatedPeriod_reduced F period H)

/-- The exact-block Pach--Toth target follows from a generated-chain family
closed by algebraic generated closure equations and full metric data. -/
theorem targetUpperConstructionFiveSixteen_of_generatedClosure_family
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    targetUpperConstructionFiveSixteen := by
  exact
    DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
      (closedPlacementFamily_of_generatedClosure F closure H)

/-- The exact-block Pach--Toth target follows from a generated-chain family
closed by algebraic generated closure equations and reduced metric data. -/
theorem targetUpperConstructionFiveSixteen_of_generatedClosure_family_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_generated_closed_chains_reducedSameBlock
      F.O F.base F.orientation
      (generatedChainFamilyPeriodsOfClosures F closure)
      (fun k hk => (H.metric k hk).separated)
      (fun k hk => (H.metric k hk).base_same_block_isometry)
      (fun k hk =>
        (H.metric k hk).transition_preserves_same_block_distances)

/-- Combined family period theorem: full generated-chain hypotheses give
closed placements at every positive block count and the exact-block target. -/
theorem exists_closedPlacement_and_target_of_generatedPeriod_family
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : GeneratedSeparationInterface.GeneratedChainFamily.Periods F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
              (F.orientation k hk))
      targetUpperConstructionFiveSixteen := by
  exact
    And.intro
      (fun k hk =>
        exists_closedPlacement_of_generatedPeriod
          (F.O k hk) hk (F.base k hk) (F.orientation k hk)
          (period k hk) (H.metric k hk))
      (targetUpperConstructionFiveSixteen_of_generatedPeriod_family
        F period H)

/-- Combined family period theorem: reduced generated-chain hypotheses give
closed placements at every positive block count and the exact-block target. -/
theorem exists_closedPlacement_and_target_of_generatedPeriod_family_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : GeneratedSeparationInterface.GeneratedChainFamily.Periods F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
              (F.orientation k hk))
      targetUpperConstructionFiveSixteen := by
  exact
    And.intro
      (fun k hk =>
        exists_closedPlacement_of_generatedPeriod_reduced
          (F.O k hk) hk (F.base k hk) (F.orientation k hk)
          (period k hk) (H.metric k hk))
      (targetUpperConstructionFiveSixteen_of_generatedPeriod_family_reduced
        F period H)

/-- Combined family closure theorem: reduced generated-chain hypotheses give
closed placements at every positive block count and the exact-block target. -/
theorem exists_closedPlacement_and_target_of_generatedClosure_family_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
              (F.orientation k hk))
      targetUpperConstructionFiveSixteen := by
  exact
    And.intro
      (fun k hk =>
        exists_closedPlacement_of_generatedClosure_reduced
          (F.O k hk) hk (F.base k hk) (F.orientation k hk)
          (closure k hk) (H.metric k hk))
      (targetUpperConstructionFiveSixteen_of_generatedClosure_family_reduced
        F closure H)

end

end ClosedPlacementClosure
end PachToth
end ErdosProblems1066
