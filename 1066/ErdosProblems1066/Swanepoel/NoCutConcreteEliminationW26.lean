import ErdosProblems1066.Swanepoel.CutVertexContradictionInhabitationW25

set_option autoImplicit false

/-!
# W26 concrete no-cut elimination

This file narrows the W25 cut-vertex blocker route to the amount of local
deletion data actually needed for a concrete blocker.  A global local-deletion
eliminator is stronger than necessary: to eliminate a blocker, it is enough to
produce certified local deletion data only after a minimal cleared failure and
one of its cut-vertex partitions have been supplied.

No unconditional no-cut theorem is asserted here.  The checked endpoint is the
real kernel proof that these partition-scoped deletion dependencies eliminate
`MinimalCutVertexBlocker`, and that the existing global deletion eliminators
imply the smaller partition-scoped dependencies.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutConcreteEliminationW26

open CutVertexInterface
open CutVertexContradictionInhabitationW25
open MinimalFailureLocalExclusions
open MinimalGraphFacts

noncomputable section

abbrev MinimalCutVertexBlocker : Type :=
  CutVertexContradictionInhabitationW25.MinimalCutVertexBlocker

abbrev MinimalFailureCutVertexContradictionFamily : Prop :=
  CutVertexContradictionInhabitationW25.MinimalFailureCutVertexContradictionFamily

abbrev MinimalFailurePointwisePayForCutFamily : Prop :=
  CutVertexContradictionInhabitationW25.MinimalFailurePointwisePayForCutFamily

abbrev MinimalFailureNoCutVertexFamily : Prop :=
  NoCutBlockerEliminationW24.MinimalFailureNoCutVertexFamily

/--
The partition-scoped degree-deletion dependency.  This is strictly narrower
than `LocalDeletionConstructors.MinimalFailureDegreeDeletionEliminator`: it is
asked for only when a cut partition of a minimal cleared failure is present.
-/
abbrev CutPartitionDegreeDeletionEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> CutVertexPartition C ->
      Exists fun nSmall : Nat =>
        Exists fun Csmall : _root_.UDConfig nSmall =>
          Nonempty (DegreeLocalDeletionCertificate C Csmall)

/--
Partition-scoped closed-neighborhood deletion data.  The induced smaller
configuration and degree certificate are supplied by
`LocalClosedNeighborhoodDeletion.exists_degreeLocalDeletionCertificate`.
-/
abbrev CutPartitionLocalClosedNeighborhoodDeletionEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> CutVertexPartition C ->
      Nonempty (LocalClosedNeighborhoodDeletion C)

/--
Partition-scoped direct-card-bound local deletion certificates.  This is the
cut-partition-only version of
`LocalDeletionEliminatorWithCardBound.MinimalFailureDirectCardBoundCertificateEliminator`.
-/
abbrev CutPartitionDirectCardBoundCertificateEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> CutVertexPartition C ->
      Exists fun nSmall : Nat =>
        Exists fun Csmall : _root_.UDConfig nSmall =>
          Nonempty (LocalDeletionCertificate C Csmall)

theorem cutPartitionDegreeDeletionEliminator_of_globalDegreeDeletionEliminator
    (hdel : LocalDeletionConstructors.MinimalFailureDegreeDeletionEliminator) :
    CutPartitionDegreeDeletionEliminator := by
  intro n C hmin _P
  exact hdel C hmin

theorem cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_global
    (hdel :
      LocalDeletionConstructors.MinimalFailureLocalClosedNeighborhoodDeletionEliminator) :
    CutPartitionLocalClosedNeighborhoodDeletionEliminator := by
  intro n C hmin _P
  exact hdel C hmin

theorem cutPartitionDirectCardBoundCertificateEliminator_of_global
    (hdel :
      LocalDeletionEliminatorWithCardBound.MinimalFailureDirectCardBoundCertificateEliminator) :
    CutPartitionDirectCardBoundCertificateEliminator := by
  intro n C hmin _P
  exact hdel C hmin

theorem cutPartitionDegreeDeletionEliminator_of_localClosedNeighborhood
    (hdel : CutPartitionLocalClosedNeighborhoodDeletionEliminator) :
    CutPartitionDegreeDeletionEliminator := by
  intro n C hmin P
  rcases hdel C hmin P with ⟨L⟩
  exact L.exists_degreeLocalDeletionCertificate

/--
Partition-scoped degree deletion gives the exact W25 partition contradiction:
the supplied local deletion certificate is impossible in a minimal cleared
failure, so the supplied cut partition is false.
-/
theorem cutVertexContradictionFamily_of_cutPartitionDegreeDeletionEliminator
    (hdel : CutPartitionDegreeDeletionEliminator) :
    MinimalFailureCutVertexContradictionFamily := by
  intro n C hmin P
  rcases hdel C hmin P with ⟨nSmall, Csmall, hcert⟩
  exact
    not_nonempty_degreeLocalDeletionCertificate_of_minimalFailure
      (Csmall := Csmall) hmin hcert

theorem cutVertexContradictionFamily_of_cutPartitionLocalClosedNeighborhood
    (hdel : CutPartitionLocalClosedNeighborhoodDeletionEliminator) :
    MinimalFailureCutVertexContradictionFamily :=
  cutVertexContradictionFamily_of_cutPartitionDegreeDeletionEliminator
    (cutPartitionDegreeDeletionEliminator_of_localClosedNeighborhood hdel)

theorem cutVertexContradictionFamily_of_cutPartitionDirectCardBound
    (hdel : CutPartitionDirectCardBoundCertificateEliminator) :
    MinimalFailureCutVertexContradictionFamily := by
  intro n C hmin P
  rcases hdel C hmin P with ⟨nSmall, Csmall, hcert⟩
  exact
    LocalDeletionCertificate.not_nonempty_localDeletionCertificate_of_minimalFailure
      (Csmall := Csmall) hmin hcert

/--
W25 pointwise pay-for-cut facade obtained from partition-scoped deletion.
This uses the W25 equivalence; the pay-for-cut atom is produced by ex falso
from the local-deletion contradiction for the supplied partition.
-/
theorem pointwisePayForCutFamily_of_cutPartitionDegreeDeletionEliminator
    (hdel : CutPartitionDegreeDeletionEliminator) :
    MinimalFailurePointwisePayForCutFamily :=
  CutVertexContradictionInhabitationW25.cutVertexContradictionFamily_iff_pointwisePayForCutFamily.1
    (cutVertexContradictionFamily_of_cutPartitionDegreeDeletionEliminator hdel)

theorem noCutVertexFamily_of_cutPartitionDegreeDeletionEliminator
    (hdel : CutPartitionDegreeDeletionEliminator) :
    MinimalFailureNoCutVertexFamily :=
  NoCutBlockerEliminationW24.noCutVertexFamily_iff_cutVertexContradictionFamily.2
    (cutVertexContradictionFamily_of_cutPartitionDegreeDeletionEliminator hdel)

theorem not_nonempty_minimalCutVertexBlocker_of_cutPartitionDegreeDeletionEliminator
    (hdel : CutPartitionDegreeDeletionEliminator) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  let hiff :=
    not_nonempty_minimalCutVertexBlocker_iff_pointwisePayForCutFamily
  hiff.2 (pointwisePayForCutFamily_of_cutPartitionDegreeDeletionEliminator hdel)

theorem not_nonempty_minimalCutVertexBlocker_of_cutPartitionLocalClosedNeighborhood
    (hdel : CutPartitionLocalClosedNeighborhoodDeletionEliminator) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDegreeDeletionEliminator
    (cutPartitionDegreeDeletionEliminator_of_localClosedNeighborhood hdel)

theorem not_nonempty_minimalCutVertexBlocker_of_cutPartitionDirectCardBound
    (hdel : CutPartitionDirectCardBoundCertificateEliminator) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  NoCutBlockerEliminationW24.not_blocker_of_cutVertexContradictionFamily
    (cutVertexContradictionFamily_of_cutPartitionDirectCardBound hdel)

theorem not_nonempty_minimalCutVertexBlocker_of_globalDegreeDeletionEliminator
    (hdel : LocalDeletionConstructors.MinimalFailureDegreeDeletionEliminator) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDegreeDeletionEliminator
    (cutPartitionDegreeDeletionEliminator_of_globalDegreeDeletionEliminator hdel)

theorem not_nonempty_minimalCutVertexBlocker_of_globalLocalClosedNeighborhood
    (hdel :
      LocalDeletionConstructors.MinimalFailureLocalClosedNeighborhoodDeletionEliminator) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionLocalClosedNeighborhood
    (cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_global hdel)

theorem not_nonempty_minimalCutVertexBlocker_of_globalDirectCardBound
    (hdel :
      LocalDeletionEliminatorWithCardBound.MinimalFailureDirectCardBoundCertificateEliminator) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDirectCardBound
    (cutPartitionDirectCardBoundCertificateEliminator_of_global hdel)

end

end NoCutConcreteEliminationW26
end Swanepoel
end ErdosProblems1066
