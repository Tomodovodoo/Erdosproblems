import ErdosProblems1066.PachToth.BaseTransitionRealization
import ErdosProblems1066.PachToth.ClosedPlacementClosure

set_option autoImplicit false

/-!
# Generated metric closure from role-hinged transitions

This module packages the metric part of a generated closed chain when the
base block is the checked exact block and the same/opposite transitions are
supplied by `BaseTransitionRealization`.

The orientation word, generated closure equation, and global separation are
still explicit inputs.  The only facts discharged here are the reduced
same-block metric hypotheses: exact base isometry and preservation of
same-block distances by the role-hinged same/opposite transition maps.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedMetricClosure

open ClosedPlacementClosure
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The role-hinged same/opposite transition package built on the exact base. -/
abbrev RoleHingeTransitions :=
  BaseTransitionRealization.BaseSameOppositeTransitionRealization

/-- The checked exact base block is a generated base same-block isometry. -/
theorem exactBase_generatedBaseSameBlockIsometry :
    GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
      BaseTransitionRealization.exactBase := by
  intro u v
  simpa [HingedTransitionInterface.referenceDistance] using
    BaseTransitionRealization.exactBase_same_block_isometry u v

/-- Role-hinged same/opposite transitions preserve same-block distances after
forgetting to the generated-chain Figure 2 transition interface. -/
theorem roleHingeTransitions_preserveSameBlockDistances
    (T : RoleHingeTransitions) :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      T.toFigure2TransitionObligations := by
  intro orientation source u v
  cases orientation
  case same =>
    exact T.same.preserves_same_block_distances source u v
  case opposite =>
    exact T.opposite.preserves_same_block_distances source u v

/-- Reduced generated metric hypotheses for the exact base and role-hinged
transitions.  Global generated separation remains the explicit geometric
input. -/
def generatedReducedMetricHypotheses
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation where
  separated := separated
  base_same_block_isometry := exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances :=
    roleHingeTransitions_preserveSameBlockDistances T

@[simp]
theorem generatedReducedMetricHypotheses_separated
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    (generatedReducedMetricHypotheses T hk orientation separated).separated =
      separated :=
  rfl

@[simp]
theorem generatedReducedMetricHypotheses_baseSameBlock
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    (generatedReducedMetricHypotheses T hk orientation separated).base_same_block_isometry =
      exactBase_generatedBaseSameBlockIsometry :=
  rfl

theorem generatedReducedMetricHypotheses_transitionPreserves
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      T.toFigure2TransitionObligations := by
  let H := generatedReducedMetricHypotheses T hk orientation separated
  exact H.transition_preserves_same_block_distances

/-- Reduced generated metric hypotheses also give the full metric facade
needed by the closed-placement route. -/
def generatedMetricHypotheses_of_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated := H.separated
  same_block_isometry :=
    GeneratedSeparationInterface.same_block_isometry_of_reduced
      O hk base orientation H

/-- Full generated metric hypotheses obtained from the reduced exact-base
role-hinge package. -/
def generatedMetricHypotheses
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation :=
  generatedMetricHypotheses_of_reduced
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase orientation
    (generatedReducedMetricHypotheses T hk orientation separated)

@[simp]
theorem generatedMetricHypotheses_separated
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    (generatedMetricHypotheses T hk orientation separated).separated =
      separated :=
  rfl

/-- Coordinate squared distance for exact-local same-block certificates. -/
def sqDist (p q : R2) : Real :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- A placed block realizes the exact local squared-distance table. -/
def MatchesExactLocalSqDistances (point : LocalVertex -> R2) : Prop :=
  forall u v : LocalVertex,
    sqDist (point u) (point v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

/-- The exact generated base block realizes the exact local squared-distance
table. -/
theorem exactBase_matchesExactLocalSqDistances :
    MatchesExactLocalSqDistances BaseTransitionRealization.exactBase := by
  intro u v
  simpa [BaseTransitionRealization.exactBase] using
    ExactLocalGeometry.local_sqDist' u v

/-- Exact local squared-distance data gives the corresponding Euclidean
same-block distance table. -/
theorem matchesExactLocalDistances_of_sqDistances
    {point : LocalVertex -> R2}
    (hpoint : MatchesExactLocalSqDistances point)
    (u v : LocalVertex) :
    _root_.eucDist (point u) (point v) =
      _root_.eucDist
        (ExactLocalGeometry.localPoint u)
        (ExactLocalGeometry.localPoint v) := by
  have hsq := hpoint u v
  unfold _root_.eucDist
  unfold sqDist at hsq
  rw [hsq, ExactLocalGeometry.local_sqDist' u v]

/-- Any base block matching the exact local squared-distance table has the
checked one-block same-block metric. -/
theorem generatedBaseSameBlockIsometry_of_sqDistances
    {base : LocalVertex -> R2}
    (hbase : MatchesExactLocalSqDistances base) :
    GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base := by
  intro u v
  calc
    _root_.eucDist (base u) (base v) =
      _root_.eucDist
        (ExactLocalGeometry.localPoint u)
        (ExactLocalGeometry.localPoint v) := by
        exact matchesExactLocalDistances_of_sqDistances hbase u v
    _ =
      _root_.eucDist
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 u))
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 v)) := by
        exact exactBase_generatedBaseSameBlockIsometry u v

/-- A transition preserves exact-local squared distances on sources that
already realize the exact local table. -/
def PreservesExactLocalSqDistances
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) : Prop :=
  forall source : LocalVertex -> R2,
    MatchesExactLocalSqDistances source ->
      MatchesExactLocalSqDistances (placeNext source)

/-- Arbitrary-source same-block distance preservation implies exact-local
squared-distance preservation on exact-local sources. -/
theorem preservesExactLocalSqDistances_of_preservesSameBlockDistances
    {placeNext : (LocalVertex -> R2) -> LocalVertex -> R2}
    (hpreserve :
      HingedTransitionInterface.PreservesSameBlockDistances placeNext) :
    PreservesExactLocalSqDistances placeNext := by
  intro source hsource u v
  have hsourceDist :=
    matchesExactLocalDistances_of_sqDistances hsource u v
  have htargetDist :
      _root_.eucDist (placeNext source u) (placeNext source v) =
        _root_.eucDist
          (ExactLocalGeometry.localPoint u)
          (ExactLocalGeometry.localPoint v) := by
    calc
      _root_.eucDist (placeNext source u) (placeNext source v) =
        _root_.eucDist (source u) (source v) := by
          exact hpreserve source u v
      _ =
        _root_.eucDist
          (ExactLocalGeometry.localPoint u)
          (ExactLocalGeometry.localPoint v) := hsourceDist
  have hsq :
      _root_.eucDist (placeNext source u) (placeNext source v) ^ 2 =
        _root_.eucDist
          (ExactLocalGeometry.localPoint u)
          (ExactLocalGeometry.localPoint v) ^ 2 := by
    rw [htargetDist]
  rw [_root_.eucDist_sq, _root_.eucDist_sq] at hsq
  simpa [sqDist, ExactLocalGeometry.local_sqDist' u v] using hsq

/-- The selected same/opposite transitions preserve the exact local
squared-distance table along exact-local sources. -/
def GeneratedTransitionsPreserveExactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations) : Prop :=
  forall (orientation : OrientationData.BlockOrientation)
      (source : LocalVertex -> R2),
    MatchesExactLocalSqDistances source ->
      MatchesExactLocalSqDistances
        ((O.transitionFor orientation).placeNext source)

/-- Branchwise exact-local squared-distance preservation gives the selected
same/opposite preservation obligation. -/
theorem generatedTransitionsPreserveExactLocalSqDistances_of_branches
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (hsame : PreservesExactLocalSqDistances O.samePlaceNext)
    (hopposite : PreservesExactLocalSqDistances O.oppositePlaceNext) :
    GeneratedTransitionsPreserveExactLocalSqDistances O := by
  intro orientation source hsource
  cases orientation
  case same =>
    exact hsame source hsource
  case opposite =>
    exact hopposite source hsource

/-- Strong role-hinged transition packages also preserve exact-local
squared distances on generated-orbit sources. -/
theorem roleHingeTransitions_preserveExactLocalSqDistances
    (T : RoleHingeTransitions) :
    GeneratedTransitionsPreserveExactLocalSqDistances
      T.toFigure2TransitionObligations := by
  exact
    generatedTransitionsPreserveExactLocalSqDistances_of_branches
      T.toFigure2TransitionObligations
      (preservesExactLocalSqDistances_of_preservesSameBlockDistances
        T.same.preserves_same_block_distances)
      (preservesExactLocalSqDistances_of_preservesSameBlockDistances
        T.opposite.preserves_same_block_distances)

/-- The exact-local squared-distance invariant propagates along every
generated block. -/
theorem generatedBlock_matchesExactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hbase : MatchesExactLocalSqDistances base)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances O) :
    forall n : Nat,
      MatchesExactLocalSqDistances
        (GeneratedClosedChain.generatedBlock O hk base orientation n) := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      exact
        htransition
          (GeneratedClosedChain.orientationAt hk orientation n)
          (GeneratedClosedChain.generatedBlock O hk base orientation n)
          ih

/-- The exact-local squared-distance table holds on every generated point
block. -/
theorem generatedPoint_matchesExactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hbase : MatchesExactLocalSqDistances base)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances O)
    (i : Fin k) :
    MatchesExactLocalSqDistances
      (GeneratedClosedChain.generatedPoint O hk base orientation i) := by
  simpa [GeneratedClosedChain.generatedPoint] using
    generatedBlock_matchesExactLocalSqDistances
      O hk base orientation hbase htransition i.val

/-- Exact-base generated orbits inherit the exact-local squared-distance
table from selected transition preservation. -/
theorem generatedOrbit_exactBase_matchesExactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances O) :
    forall i : Fin k,
      MatchesExactLocalSqDistances
        (GeneratedClosedChain.generatedPoint O hk
          BaseTransitionRealization.exactBase orientation i) := by
  intro i
  exact
    generatedPoint_matchesExactLocalSqDistances
      O hk BaseTransitionRealization.exactBase orientation
      exactBase_matchesExactLocalSqDistances htransition i

/-- Exact-local squared-distance preservation supplies the generated
same-block isometry needed by closed placement. -/
theorem generatedSameBlockIsometry_of_exactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hbase : MatchesExactLocalSqDistances base)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances O) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      O hk base orientation := by
  intro i u v
  have hblock :
      MatchesExactLocalSqDistances
        (GeneratedClosedChain.generatedPoint O hk base orientation i) := by
    exact
      generatedPoint_matchesExactLocalSqDistances
        O hk base orientation hbase htransition i
  calc
    _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation i v) =
      _root_.eucDist
        (ExactLocalGeometry.localPoint u)
        (ExactLocalGeometry.localPoint v) := by
        exact matchesExactLocalDistances_of_sqDistances hblock u v
    _ =
      _root_.eucDist
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 u))
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 v)) := by
        exact exactBase_generatedBaseSameBlockIsometry u v

/-- Package global separation and exact-local squared-distance preservation
as the full generated metric hypotheses. -/
def generatedMetricHypotheses_of_exactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (hbase : MatchesExactLocalSqDistances base)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances O) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated := separated
  same_block_isometry :=
    generatedSameBlockIsometry_of_exactLocalSqDistances
      O hk base orientation hbase htransition

@[simp]
theorem generatedMetricHypotheses_of_exactLocalSqDistances_separated
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (hbase : MatchesExactLocalSqDistances base)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances O) :
    (generatedMetricHypotheses_of_exactLocalSqDistances
        O hk base orientation separated hbase htransition).separated =
      separated :=
  rfl

/-- Exact-base role-hinge metric hypotheses from exact-local squared-distance
preservation.  This is the full metric facade, not the reduced facade: the
reduced transition field still asks for arbitrary-source distance
preservation. -/
def roleHingeGeneratedMetricHypotheses_of_exactLocalSqDistances
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances
        T.toFigure2TransitionObligations) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation :=
  generatedMetricHypotheses_of_exactLocalSqDistances
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase orientation separated
    exactBase_matchesExactLocalSqDistances htransition

/-- Exact-base role-hinge metric hypotheses from the strong same-block
preservation fields, routed through the exact-local squared-distance bridge. -/
def roleHingeGeneratedMetricHypotheses_of_preservesSameBlock
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation :=
  roleHingeGeneratedMetricHypotheses_of_exactLocalSqDistances
    T hk orientation separated
    (roleHingeTransitions_preserveExactLocalSqDistances T)

/-- Closed-placement certificate from algebraic closure, separation, and
exact-local squared-distance preservation. -/
def explicitTransitionClosedPlacementCertificate_of_exactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (hbase : MatchesExactLocalSqDistances base)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances O) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk :=
  ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedClosure
    O hk base orientation closure
    (generatedMetricHypotheses_of_exactLocalSqDistances
      O hk base orientation separated hbase htransition)

/-- Closed placement from algebraic closure, separation, and exact-local
squared-distance preservation. -/
def closedPlacement_of_exactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (hbase : MatchesExactLocalSqDistances base)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances O) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementClosure.closedPlacement_of_generatedClosure
    O hk base orientation closure
    (generatedMetricHypotheses_of_exactLocalSqDistances
      O hk base orientation separated hbase htransition)

/-- Existence form of the closed placement obtained from exact-local
squared-distance preservation. -/
theorem exists_closedPlacement_of_exactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (hbase : MatchesExactLocalSqDistances base)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances O) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = GeneratedClosedChain.generatedPoint O hk base orientation := by
  exact
    ClosedPlacementClosure.exists_closedPlacement_of_generatedClosure
      O hk base orientation closure
      (generatedMetricHypotheses_of_exactLocalSqDistances
        O hk base orientation separated hbase htransition)

/-- Exact-block target from algebraic closure, separation, and exact-local
squared-distance preservation. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_exactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (hbase : MatchesExactLocalSqDistances base)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances O) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedClosure
      O hk base orientation closure
      (generatedMetricHypotheses_of_exactLocalSqDistances
        O hk base orientation separated hbase htransition)

/-- Exact-base role-hinge closed-placement certificate from exact-local
squared-distance preservation. -/
def explicitTransitionClosedPlacementCertificate_of_roleHingeExactLocalSqDistances
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances
        T.toFigure2TransitionObligations) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk :=
  explicitTransitionClosedPlacementCertificate_of_exactLocalSqDistances
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase orientation closure separated
    exactBase_matchesExactLocalSqDistances htransition

/-- Exact-base role-hinge closed placement from exact-local squared-distance
preservation. -/
def closedPlacement_of_roleHingeExactLocalSqDistances
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances
        T.toFigure2TransitionObligations) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacement_of_exactLocalSqDistances
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase orientation closure separated
    exactBase_matchesExactLocalSqDistances htransition

/-- Existence form of the exact-base role-hinge closed placement obtained
from exact-local squared-distance preservation. -/
theorem exists_closedPlacement_of_roleHingeExactLocalSqDistances
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances
        T.toFigure2TransitionObligations) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point =
        GeneratedClosedChain.generatedPoint T.toFigure2TransitionObligations
          hk BaseTransitionRealization.exactBase orientation := by
  exact
    exists_closedPlacement_of_exactLocalSqDistances
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation closure separated
      exactBase_matchesExactLocalSqDistances htransition

/-- Exact-block target from exact-base role-hinge closure, separation, and
exact-local squared-distance preservation. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_roleHingeExactLocalSqDistances
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (htransition :
      GeneratedTransitionsPreserveExactLocalSqDistances
        T.toFigure2TransitionObligations) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_exactLocalSqDistances
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation closure separated
      exactBase_matchesExactLocalSqDistances htransition

/-- The explicit transition closed-placement certificate obtained from a
role-hinged generated closure. -/
def explicitTransitionClosedPlacementCertificate
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedClosure_reduced
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation closure
      (generatedReducedMetricHypotheses T hk orientation separated)

/-- The closed placement obtained from a role-hinged generated closure. -/
def closedPlacement
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementClosure.closedPlacement_of_generatedClosure_reduced
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase orientation closure
    (generatedReducedMetricHypotheses T hk orientation separated)

/-- Existence form of the closed placement produced by role-hinged generated
closure and explicit generated separation. -/
theorem exists_closedPlacement
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point =
        GeneratedClosedChain.generatedPoint T.toFigure2TransitionObligations
          hk BaseTransitionRealization.exactBase orientation := by
  exact
    ClosedPlacementClosure.exists_closedPlacement_of_generatedClosure_reduced
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation closure
      (generatedReducedMetricHypotheses T hk orientation separated)

/-- Exact-block target from role-hinged generated closure and explicit
generated separation. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedClosure_reduced
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation closure
        (generatedReducedMetricHypotheses T hk orientation separated)

/-- Bundled one-chain version of role-hinged generated closure data. -/
structure RoleHingedGeneratedClosureData (k : Nat) (hk : 0 < k) where
  transitions : RoleHingeTransitions
  orientation : Fin k -> OrientationData.BlockOrientation
  closure :
    PeriodInterface.GeneratedClosureEquation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
  separated :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation

namespace RoleHingedGeneratedClosureData

/-- Project bundled role-hinged closure data to reduced generated metric
hypotheses. -/
def toGeneratedReducedMetricHypotheses
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      G.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase G.orientation :=
  generatedReducedMetricHypotheses G.transitions hk G.orientation G.separated

@[simp]
theorem toGeneratedReducedMetricHypotheses_separated
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    G.toGeneratedReducedMetricHypotheses.separated = G.separated :=
  rfl

@[simp]
theorem toGeneratedReducedMetricHypotheses_baseSameBlock
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    G.toGeneratedReducedMetricHypotheses.base_same_block_isometry =
      exactBase_generatedBaseSameBlockIsometry :=
  rfl

@[simp]
theorem toGeneratedReducedMetricHypotheses_transitionPreserves
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    G.toGeneratedReducedMetricHypotheses.transition_preserves_same_block_distances =
      roleHingeTransitions_preserveSameBlockDistances G.transitions :=
  rfl

/-- Project bundled data to the explicit transition closed-placement
certificate. -/
def toExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  explicitTransitionClosedPlacementCertificate G.transitions hk G.orientation
    G.closure G.separated

/-- Project bundled data to the closed placement. -/
def toClosedPlacement
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacement G.transitions hk G.orientation G.closure G.separated

/-- Bundled role-hinged generated closure data gives the closed-placement
existence theorem. -/
theorem exists_closedPlacement
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point =
        GeneratedClosedChain.generatedPoint
          G.transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase G.orientation := by
  exact
    GeneratedMetricClosure.exists_closedPlacement G.transitions hk
      G.orientation G.closure G.separated

/-- Bundled role-hinged generated closure data gives the exact-block target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    GeneratedMetricClosure.targetUpperConstructionFiveSixteenAt_exactBlock
      G.transitions hk G.orientation G.closure G.separated

end RoleHingedGeneratedClosureData

/-- Family version with one role-hinged transition package and explicit
orientation, closure, and separation data for every positive block count. -/
structure RoleHingedGeneratedClosureFamily where
  transitions : RoleHingeTransitions
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)

namespace RoleHingedGeneratedClosureFamily

/-- Forget the role-hinged construction to the generated-chain family
interface. -/
def toGeneratedChainFamily
    (F : RoleHingedGeneratedClosureFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => F.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.orientation

@[simp]
theorem toGeneratedChainFamily_O
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.O k hk =
      F.transitions.toFigure2TransitionObligations :=
  rfl

@[simp]
theorem toGeneratedChainFamily_base
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.base k hk =
      BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem toGeneratedChainFamily_orientation
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.orientation k hk = F.orientation k hk :=
  rfl

/-- Project family closure equations to the closed-placement closure
interface. -/
def toGeneratedChainFamilyClosures
    (F : RoleHingedGeneratedClosureFamily) :
    ClosedPlacementClosure.GeneratedChainFamilyClosures
      F.toGeneratedChainFamily :=
  fun k hk => F.closure k hk

/-- Project family separation and role-hinged metric data to reduced
generated metric hypotheses. -/
def toReducedMetricHypotheses
    (F : RoleHingedGeneratedClosureFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
      F.toGeneratedChainFamily where
  metric := fun k hk =>
    generatedReducedMetricHypotheses F.transitions hk (F.orientation k hk)
      (F.separated k hk)

@[simp]
theorem toReducedMetricHypotheses_metric_separated
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    ((F.toReducedMetricHypotheses).metric k hk).separated =
      F.separated k hk :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_baseSameBlock
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    ((F.toReducedMetricHypotheses).metric k hk).base_same_block_isometry =
      exactBase_generatedBaseSameBlockIsometry :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_transitionPreserves
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    ((F.toReducedMetricHypotheses).metric k hk).transition_preserves_same_block_distances =
      roleHingeTransitions_preserveSameBlockDistances F.transitions :=
  rfl

/-- Closed placements for every positive block count in the role-hinged
generated-closure family. -/
def closedPlacementFamily
    (F : RoleHingedGeneratedClosureFamily) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementClosure.closedPlacementFamily_of_generatedClosure_reduced
    F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
    F.toReducedMetricHypotheses

/-- Family target theorem obtained by projecting to `ClosedPlacementClosure`. -/
theorem targetUpperConstructionFiveSixteen
    (F : RoleHingedGeneratedClosureFamily) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteen_of_generatedClosure_family_reduced
        F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
        F.toReducedMetricHypotheses

/-- Combined closed-placement existence and exact-block target for the
role-hinged generated-closure family. -/
theorem exists_closedPlacement_and_target
    (F : RoleHingedGeneratedClosureFamily) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint
              F.transitions.toFigure2TransitionObligations hk
              BaseTransitionRealization.exactBase (F.orientation k hk))
      PachToth.targetUpperConstructionFiveSixteen := by
  simpa [toGeneratedChainFamily] using
    ClosedPlacementClosure.exists_closedPlacement_and_target_of_generatedClosure_family_reduced
        F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
        F.toReducedMetricHypotheses

end RoleHingedGeneratedClosureFamily

/-- Raw-function family wrapper keeping all orientation-dependent closure and
separation hypotheses explicit. -/
theorem targetUpperConstructionFiveSixteen_of_roleHingeTransitions
    (T : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation)
    (closure :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedClosureEquation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase (orientation k hk))
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase (orientation k hk)) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    RoleHingedGeneratedClosureFamily.targetUpperConstructionFiveSixteen
      { transitions := T
        orientation := orientation
        closure := closure
        separated := separated }

end

end GeneratedMetricClosure
end PachToth
end ErdosProblems1066
