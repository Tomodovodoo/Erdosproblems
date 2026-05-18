import ErdosProblems1066.Swanepoel.NoCutConcreteEliminationW26
import ErdosProblems1066.Swanepoel.DeficientNeighborhood

set_option autoImplicit false

/-!
# W27 partition-local deletion bridge for no-cut

This file is deliberately scoped to the W26 no-cut deletion frontier.  A
cut-vertex partition does not itself contain a closed-neighborhood deletion
rule, so the checked contribution here is the exact local-deletion dependency:
honest partition-scoped local deletion data is packaged into the W26
eliminators, and the smallest certificate-level dependency is shown to be
logically equivalent to eliminating the concrete cut-vertex blocker.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutLocalDeletionConcreteW27

open CutVertexInterface
open MinimalCounterexample
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoCutConcreteEliminationW26

noncomputable section

abbrev MinimalCutVertexBlocker : Type :=
  NoCutConcreteEliminationW26.MinimalCutVertexBlocker

/-- Tupled partition-scoped closed-neighborhood deletion data. -/
abbrev CutPartitionTupledClosedNeighborhoodDeletionData : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> CutVertexPartition C ->
      Exists fun deleted : Finset (Fin n) =>
      Exists fun reinsertion : Finset (Fin n) =>
        IsClosedNeighborhood C reinsertion deleted /\
        (Exists fun center : Fin n =>
          deleted <= DegreePipeline.closedUnitNeighborhood C center) /\
        2 <= reinsertion.card /\
        reinsertion.card <= 8 /\
        C.IsIndep reinsertion

/-- Tupled partition-scoped direct-card-bound local deletion data. -/
abbrev CutPartitionTupledDirectCardBoundDeletionData : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> CutVertexPartition C ->
      Exists fun deleted : Finset (Fin n) =>
      Exists fun reinsertion : Finset (Fin n) =>
        IsClosedNeighborhood C reinsertion deleted /\
        (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 /\
        reinsertion.Nonempty /\
        reinsertion.card <= 8 /\
        C.IsIndep reinsertion

/-- Partition-scoped deficient-neighborhood data, a concrete direct-card
local-deletion source when such a small independent set is supplied. -/
abbrev CutPartitionDeficientNeighborhoodDeletionData : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> CutVertexPartition C ->
      Exists fun S : Finset (Fin n) =>
        S.Nonempty /\
        C.IsIndep S /\
        S.card <= 8 /\
        (SmallIndependentNeighborhood.outsideNeighborhoodOf C S).card <
          3 * S.card

/-- Closed-neighborhood tupled data builds the W26 structure-valued
partition-local deletion eliminator. -/
theorem cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_tupled
    (hdel : CutPartitionTupledClosedNeighborhoodDeletionData) :
    CutPartitionLocalClosedNeighborhoodDeletionEliminator := by
  intro n C hmin P
  cases hdel C hmin P with
  | intro deleted hrest =>
      cases hrest with
      | intro reinsertion hdata =>
          cases hdata with
          | intro hclosed hrest =>
              cases hrest with
              | intro hsubset hrest =>
                  cases hrest with
                  | intro hlower hrest =>
                      cases hrest with
                      | intro hupper hindep =>
                          exact
                            Nonempty.intro
                              { deleted := deleted
                                reinsertion := reinsertion
                                closedNeighborhood := hclosed
                                deletedSubsetClosedUnitNeighborhood := hsubset
                                reinsertionCardLower := hlower
                                reinsertionCardUpper := hupper
                                reinsertionIndep := hindep }

/-- Closed-neighborhood tupled data feeds W26's degree-certificate
eliminator. -/
theorem cutPartitionDegreeDeletionEliminator_of_tupledClosedNeighborhood
    (hdel : CutPartitionTupledClosedNeighborhoodDeletionData) :
    CutPartitionDegreeDeletionEliminator :=
  cutPartitionDegreeDeletionEliminator_of_localClosedNeighborhood
    (cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_tupled hdel)

/-- Direct-card-bound tupled data builds W26's direct local-deletion
certificate eliminator. -/
theorem cutPartitionDirectCardBoundCertificateEliminator_of_tupled
    (hdel : CutPartitionTupledDirectCardBoundDeletionData) :
    CutPartitionDirectCardBoundCertificateEliminator := by
  intro n C hmin P
  cases hdel C hmin P with
  | intro deleted hrest =>
      cases hrest with
      | intro reinsertion hdata =>
          cases hdata with
          | intro hclosed hrest =>
              cases hrest with
              | intro hcard hrest =>
                  cases hrest with
                  | intro hnonempty hrest =>
                      cases hrest with
                      | intro hupper hindep =>
                          exact
                            LocalDeletionWithCardBound.exists_localDeletionCertificate_of_data
                              C deleted reinsertion hclosed hcard hnonempty hupper hindep

/-- Deficient-neighborhood data is a concrete direct-card-bound local deletion
source, using the existing canonical deletion machinery. -/
theorem cutPartitionDirectCardBoundCertificateEliminator_of_deficientNeighborhood
    (hdel : CutPartitionDeficientNeighborhoodDeletionData) :
    CutPartitionDirectCardBoundCertificateEliminator := by
  intro n C hmin P
  cases hdel C hmin P with
  | intro S hdata =>
      cases hdata with
      | intro hS hrest =>
          cases hrest with
          | intro hindep hrest =>
              cases hrest with
              | intro hupper houtside =>
                  exact
                    DeficientNeighborhood.exists_localDeletionCertificate_of_deficientNeighborhood
                      C hS hindep hupper houtside

theorem not_nonempty_minimalCutVertexBlocker_of_tupledClosedNeighborhood
    (hdel : CutPartitionTupledClosedNeighborhoodDeletionData) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDegreeDeletionEliminator
    (cutPartitionDegreeDeletionEliminator_of_tupledClosedNeighborhood hdel)

theorem not_nonempty_minimalCutVertexBlocker_of_tupledDirectCardBound
    (hdel : CutPartitionTupledDirectCardBoundDeletionData) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDirectCardBound
    (cutPartitionDirectCardBoundCertificateEliminator_of_tupled hdel)

theorem not_nonempty_minimalCutVertexBlocker_of_deficientNeighborhood
    (hdel : CutPartitionDeficientNeighborhoodDeletionData) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDirectCardBound
    (cutPartitionDirectCardBoundCertificateEliminator_of_deficientNeighborhood hdel)

/-- The smallest exact certificate-level local-deletion dependency consumed
by W26. -/
abbrev SmallestExactLocalDeletionDependency : Prop :=
  CutPartitionDegreeDeletionEliminator

theorem smallestExactLocalDeletionDependency_of_not_minimalCutVertexBlocker
    (hblocker : Not (Nonempty MinimalCutVertexBlocker)) :
    SmallestExactLocalDeletionDependency := by
  intro n C hmin P
  exact
    False.elim
      (hblocker
        (Nonempty.intro
          (NoCutSourceConcreteW23.MinimalCutVertexBlocker.of_cutVertexPartition
            (C := C) hmin P)))

/-- Exact W27 boundary: W26's smallest partition-scoped local-deletion
dependency is equivalent to eliminating the concrete cut-vertex blocker. -/
theorem smallestExactLocalDeletionDependency_iff_not_minimalCutVertexBlocker :
    SmallestExactLocalDeletionDependency <->
      Not (Nonempty MinimalCutVertexBlocker) := by
  constructor
  case mp =>
    exact
      not_nonempty_minimalCutVertexBlocker_of_cutPartitionDegreeDeletionEliminator
  case mpr =>
    exact smallestExactLocalDeletionDependency_of_not_minimalCutVertexBlocker

/-- Structure-valued closed-neighborhood data has the same exact boundary. -/
theorem cutPartitionLocalClosedNeighborhoodDeletionEliminator_iff_not_minimalCutVertexBlocker :
    CutPartitionLocalClosedNeighborhoodDeletionEliminator <->
      Not (Nonempty MinimalCutVertexBlocker) := by
  constructor
  case mp =>
    exact not_nonempty_minimalCutVertexBlocker_of_cutPartitionLocalClosedNeighborhood
  case mpr =>
    intro hblocker n C hmin P
    exact
      False.elim
        (hblocker
          (Nonempty.intro
            (NoCutSourceConcreteW23.MinimalCutVertexBlocker.of_cutVertexPartition
              (C := C) hmin P)))

/-- Direct-card-bound certificates also have the same exact partition-scoped
boundary. -/
theorem cutPartitionDirectCardBoundCertificateEliminator_iff_not_minimalCutVertexBlocker :
    CutPartitionDirectCardBoundCertificateEliminator <->
      Not (Nonempty MinimalCutVertexBlocker) := by
  constructor
  case mp =>
    exact not_nonempty_minimalCutVertexBlocker_of_cutPartitionDirectCardBound
  case mpr =>
    intro hblocker n C hmin P
    exact
      False.elim
        (hblocker
          (Nonempty.intro
            (NoCutSourceConcreteW23.MinimalCutVertexBlocker.of_cutVertexPartition
              (C := C) hmin P)))

end

end NoCutLocalDeletionConcreteW27
end Swanepoel
end ErdosProblems1066
