import ErdosProblems1066.PachToth.ExactLocalGeometry
import ErdosProblems1066.PachToth.GeneratedSeparationInterface
import ErdosProblems1066.PachToth.RoleHingeTransitionSearch

set_option autoImplicit false

/-!
# Same-block algebra for role-hinged transition searches

This module isolates the algebraic same-block metric obligation for
role-hinged generated chains.

The strong transition interface asks for preservation of all same-block
distances for every source placement.  For finite-search output it is often
more convenient to prove the smaller, exact-local obligation used along the
generated orbit: every produced block satisfies the same squared-distance
formula as `ExactLocalGeometry.localGrid`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeSameBlockAlgebra

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- Squared Euclidean distance, written without the square root. -/
def sqDist (p q : R2) : Real :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- A placed block realizes the exact local squared-distance table. -/
def MatchesExactLocalSqDistances (point : LocalVertex -> R2) : Prop :=
  forall u v : LocalVertex,
    sqDist (point u) (point v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

/-- A placed block realizes the exact local Euclidean-distance table. -/
def MatchesExactLocalDistances (point : LocalVertex -> R2) : Prop :=
  forall u v : LocalVertex,
    _root_.eucDist (point u) (point v) =
      _root_.eucDist
        (ExactLocalGeometry.localPoint u)
        (ExactLocalGeometry.localPoint v)

/-- The exact local block satisfies its own integer-grid squared-distance
formula. -/
theorem exactLocal_matchesExactLocalSqDistances :
    MatchesExactLocalSqDistances ExactLocalGeometry.localPoint := by
  intro u v
  exact ExactLocalGeometry.local_sqDist' u v

/-- The exact grid squared-distance formula implies the corresponding
Euclidean-distance table. -/
theorem matchesExactLocalDistances_of_sqDistances
    {point : LocalVertex -> R2}
    (hpoint : MatchesExactLocalSqDistances point) :
    MatchesExactLocalDistances point := by
  intro u v
  have hsq := hpoint u v
  unfold _root_.eucDist
  unfold sqDist at hsq
  rw [hsq, ExactLocalGeometry.local_sqDist' u v]

/-- The exact local block realizes its own Euclidean-distance table. -/
theorem exactLocal_matchesExactLocalDistances :
    MatchesExactLocalDistances ExactLocalGeometry.localPoint :=
  matchesExactLocalDistances_of_sqDistances
    exactLocal_matchesExactLocalSqDistances

/-- The exact local block is a generated-chain base same-block isometry. -/
theorem exactLocal_generatedBaseSameBlockIsometry :
    GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
      ExactLocalGeometry.localPoint := by
  intro u v
  exact BaseTransitionRealization.exactBase_same_block_isometry u v

/-- Any block matching the exact local squared-distance table is a generated
base same-block isometry. -/
theorem generatedBaseSameBlockIsometry_of_sqDistances
    {base : LocalVertex -> R2}
    (hbase : MatchesExactLocalSqDistances base) :
    GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base := by
  intro u v
  have hdist :=
    matchesExactLocalDistances_of_sqDistances hbase u v
  calc
    _root_.eucDist (base u) (base v) =
      _root_.eucDist
        (ExactLocalGeometry.localPoint u)
        (ExactLocalGeometry.localPoint v) := hdist
    _ =
      _root_.eucDist
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 u))
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 v)) := by
        exact exactLocal_generatedBaseSameBlockIsometry u v

/-- A transition preserves the exact local squared-distance table on the
sources that already satisfy that table. -/
def PreservesExactLocalSqDistances
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) : Prop :=
  forall source : LocalVertex -> R2,
    MatchesExactLocalSqDistances source ->
      MatchesExactLocalSqDistances (placeNext source)

/-- The same exact-local squared-distance preservation obligation, after
selecting same/opposite transitions from a generated-chain interface. -/
def GeneratedTransitionsPreserveExactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations) : Prop :=
  forall (orientation : OrientationData.BlockOrientation)
      (source : LocalVertex -> R2),
    MatchesExactLocalSqDistances source ->
      MatchesExactLocalSqDistances
        ((O.transitionFor orientation).placeNext source)

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

/-- Exact-local squared-distance preservation is enough to recover the full
same-block isometry required by generated closed chains. -/
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
    simpa [GeneratedClosedChain.generatedPoint] using
      generatedBlock_matchesExactLocalSqDistances
        O hk base orientation hbase htransition i.val
  have hdist :=
    matchesExactLocalDistances_of_sqDistances hblock u v
  calc
    _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation i v) =
      _root_.eucDist
        (ExactLocalGeometry.localPoint u)
        (ExactLocalGeometry.localPoint v) := hdist
    _ =
      _root_.eucDist
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 u))
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 v)) := by
        exact exactLocal_generatedBaseSameBlockIsometry u v

/-- Package global separation with the exact-local same-block reduction into
the full generated metric hypotheses. -/
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

/-- Reduced generated metric hypotheses when the base block is checked by the
exact local squared-distance table and the selected transitions preserve all
same-block distances. -/
def generatedReducedMetricHypotheses_of_sqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (hbase : MatchesExactLocalSqDistances base)
    (htransition :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      O hk base orientation where
  separated := separated
  base_same_block_isometry :=
    generatedBaseSameBlockIsometry_of_sqDistances hbase
  transition_preserves_same_block_distances := htransition

/-- Role-hinge-search spelling of the exact-local squared-distance obligation. -/
def RoleHingeTransitionsPreserveExactLocalSqDistances
    (F : RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts) :
    Prop :=
  GeneratedTransitionsPreserveExactLocalSqDistances
    F.toFigure2TransitionObligations

/-- The arbitrary-source same-block preservation fields in
`RoleHingeTransitionSearch` imply the exact-local squared-distance obligation
used by this reduction. -/
theorem roleHingeTransitionsPreserveExactLocalSqDistances_of_preservesSameBlock
    (F : RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts) :
    RoleHingeTransitionsPreserveExactLocalSqDistances F := by
  intro orientation source hsource u v
  have hsourceDist :=
    matchesExactLocalDistances_of_sqDistances hsource u v
  have htargetDist :
      _root_.eucDist
          ((F.toFigure2TransitionObligations.transitionFor orientation).placeNext
            source u)
          ((F.toFigure2TransitionObligations.transitionFor orientation).placeNext
            source v) =
        _root_.eucDist
          (ExactLocalGeometry.localPoint u)
          (ExactLocalGeometry.localPoint v) := by
    calc
      _root_.eucDist
          ((F.toFigure2TransitionObligations.transitionFor orientation).placeNext
            source u)
          ((F.toFigure2TransitionObligations.transitionFor orientation).placeNext
            source v) =
        _root_.eucDist (source u) (source v) := by
          exact F.preservesSameBlockDistances orientation source u v
      _ =
        _root_.eucDist
          (ExactLocalGeometry.localPoint u)
          (ExactLocalGeometry.localPoint v) := hsourceDist
  have hsq :
      _root_.eucDist
          ((F.toFigure2TransitionObligations.transitionFor orientation).placeNext
            source u)
          ((F.toFigure2TransitionObligations.transitionFor orientation).placeNext
            source v) ^ 2 =
        _root_.eucDist
          (ExactLocalGeometry.localPoint u)
          (ExactLocalGeometry.localPoint v) ^ 2 := by
    rw [htargetDist]
  rw [_root_.eucDist_sq, _root_.eucDist_sq] at hsq
  simpa [sqDist, ExactLocalGeometry.local_sqDist' u v] using hsq

/-- Role-hinge-search version of the exact-local same-block isometry
reduction, based at `ExactLocalGeometry.localPoint`. -/
theorem roleHingeGeneratedSameBlockIsometry_of_exactLocalSqDistances
    (F : RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (htransition :
      RoleHingeTransitionsPreserveExactLocalSqDistances F) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      F.toFigure2TransitionObligations hk
      ExactLocalGeometry.localPoint orientation := by
  exact
    generatedSameBlockIsometry_of_exactLocalSqDistances
      F.toFigure2TransitionObligations hk
      ExactLocalGeometry.localPoint orientation
      exactLocal_matchesExactLocalSqDistances htransition

/-- Role-hinge-search version packaged as full generated metric hypotheses.
The only remaining geometric input is global generated separation. -/
def roleHingeGeneratedMetricHypotheses_of_exactLocalSqDistances
    (F : RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        F.toFigure2TransitionObligations hk
        ExactLocalGeometry.localPoint orientation)
    (htransition :
      RoleHingeTransitionsPreserveExactLocalSqDistances F) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      F.toFigure2TransitionObligations hk
      ExactLocalGeometry.localPoint orientation where
  separated := separated
  same_block_isometry :=
    roleHingeGeneratedSameBlockIsometry_of_exactLocalSqDistances
      F hk orientation htransition

/-- Role-hinge-search generated metric hypotheses obtained directly from the
ordinary same-block preservation fields already stored in the search facts. -/
def roleHingeGeneratedMetricHypotheses_of_preservesSameBlock
    (F : RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        F.toFigure2TransitionObligations hk
        ExactLocalGeometry.localPoint orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      F.toFigure2TransitionObligations hk
      ExactLocalGeometry.localPoint orientation :=
  roleHingeGeneratedMetricHypotheses_of_exactLocalSqDistances
    F hk orientation separated
    (roleHingeTransitionsPreserveExactLocalSqDistances_of_preservesSameBlock F)

/-- Role-hinge-search reduced metric hypotheses obtained directly from the
ordinary same-block preservation fields already stored in the search facts. -/
def roleHingeGeneratedReducedMetricHypotheses_of_preservesSameBlock
    (F : RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        F.toFigure2TransitionObligations hk
        ExactLocalGeometry.localPoint orientation) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      F.toFigure2TransitionObligations hk
      ExactLocalGeometry.localPoint orientation :=
  generatedReducedMetricHypotheses_of_sqDistances
    F.toFigure2TransitionObligations hk
    ExactLocalGeometry.localPoint orientation separated
    exactLocal_matchesExactLocalSqDistances
    F.preservesSameBlockDistances

end

end RoleHingeSameBlockAlgebra
end PachToth
end ErdosProblems1066
