import ErdosProblems1066.Swanepoel.MinimalFailureClosure
import ErdosProblems1066.Swanepoel.MinimalFailureLocalExclusions

/-!
# Local deletion constructors for minimal-failure closure

This module sits just above `MinimalFailureLocalExclusions`.  That parent
module already constructs a `DegreeLocalDeletionCertificate` from honest local
closed-neighborhood deletion data using `InducedSubconfiguration`.  The lemmas
below package the next generic closure step: if every minimal cleared failure
supplies such a certificate, then there are no minimal cleared failures, hence
the cleared pipeline and the public Swanepoel target follow.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LocalDeletionConstructors

open CounterexamplePipeline
open MinimalFailureClosure
open MinimalFailureLocalExclusions
open MinimalGraphFacts

noncomputable section

/-- A generic eliminator saying every minimal cleared failure admits a certified
degree-controlled local deletion. -/
def MinimalFailureDegreeDeletionEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C ->
      Exists fun nSmall : Nat =>
        Exists fun Csmall : _root_.UDConfig nSmall =>
          Nonempty (DegreeLocalDeletionCertificate C Csmall)

/-- A generic eliminator saying every minimal cleared failure admits honest
local closed-neighborhood deletion data. -/
def MinimalFailureLocalClosedNeighborhoodDeletionEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C ->
      Nonempty (MinimalFailureLocalExclusions.LocalClosedNeighborhoodDeletion C)

/-- Concrete tupled local closed-neighborhood deletion data gives the
structure-valued eliminator used by the deletion frontier.

This is the generic version of the packaging step that local-rule workers
otherwise have to repeat: provide `deleted`, `reinsertion`, and the five local
facts, and the existing `LocalClosedNeighborhoodDeletion` structure is built
directly. -/
theorem localClosedNeighborhoodDeletionEliminator_of_exists_localClosedNeighborhoodDeletion
    (hdel :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C ->
          Exists fun deleted : Finset (Fin n) =>
          Exists fun reinsertion : Finset (Fin n) =>
            MinimalCounterexample.IsClosedNeighborhood C reinsertion deleted /\
            (Exists fun center : Fin n =>
              deleted <= DegreePipeline.closedUnitNeighborhood C center) /\
            2 <= reinsertion.card /\
            reinsertion.card <= 8 /\
            C.IsIndep reinsertion) :
    MinimalFailureLocalClosedNeighborhoodDeletionEliminator := by
  intro n C hmin
  rcases hdel C hmin with
    ⟨deleted, reinsertion, hclosed, hsubset, hlower, hupper, hindep⟩
  exact
    ⟨{ deleted := deleted
       reinsertion := reinsertion
       closedNeighborhood := hclosed
       deletedSubsetClosedUnitNeighborhood := hsubset
       reinsertionCardLower := hlower
       reinsertionCardUpper := hupper
       reinsertionIndep := hindep }⟩

/-- Honest local closed-neighborhood deletions are enough to supply the
certified degree-deletion eliminator expected by the minimal-failure closure. -/
theorem degreeDeletionEliminator_of_localClosedNeighborhoodDeletionEliminator
    (hdel : MinimalFailureLocalClosedNeighborhoodDeletionEliminator) :
    MinimalFailureDegreeDeletionEliminator := by
  intro n C hmin
  cases hdel C hmin with
  | intro L =>
      exact L.exists_degreeLocalDeletionCertificate

/-- A degree-deletion eliminator rules out each minimal cleared failure. -/
theorem no_minimalClearedFailure_of_degreeDeletionEliminator
    (hdel : MinimalFailureDegreeDeletionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  intro n C hmin
  cases hdel C hmin with
  | intro nSmall hrest =>
      cases hrest with
      | intro Csmall hK =>
          exact not_nonempty_degreeLocalDeletionCertificate_of_minimalFailure
            (Csmall := Csmall) hmin hK

/-- Local closed-neighborhood deletion data rules out each minimal cleared
failure, after the induced smaller configuration has been constructed. -/
theorem no_minimalClearedFailure_of_localClosedNeighborhoodDeletionEliminator
    (hdel : MinimalFailureLocalClosedNeighborhoodDeletionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  exact no_minimalClearedFailure_of_degreeDeletionEliminator
    (degreeDeletionEliminator_of_localClosedNeighborhoodDeletionEliminator hdel)

/-- A degree-deletion eliminator proves the cleared `8 / 31` predicate for
every separated unit-distance configuration. -/
theorem hasCleared_of_degreeDeletionEliminator
    (hdel : MinimalFailureDegreeDeletionEliminator) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C := by
  exact hasCleared_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_degreeDeletionEliminator hdel)

/-- Local closed-neighborhood deletion data proves the cleared `8 / 31`
predicate for every separated unit-distance configuration. -/
theorem hasCleared_of_localClosedNeighborhoodDeletionEliminator
    (hdel : MinimalFailureLocalClosedNeighborhoodDeletionEliminator) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C := by
  exact hasCleared_of_degreeDeletionEliminator
    (degreeDeletionEliminator_of_localClosedNeighborhoodDeletionEliminator hdel)

/-- A degree-deletion eliminator is enough for the public Swanepoel
`8 / 31` lower-bound target. -/
theorem targetLowerBoundEightThirtyOne_of_degreeDeletionEliminator
    (hdel : MinimalFailureDegreeDeletionEliminator) :
    targetLowerBoundEightThirtyOne := by
  exact targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_degreeDeletionEliminator hdel)

/-- Honest local closed-neighborhood deletion data is enough for the public
Swanepoel `8 / 31` lower-bound target. -/
theorem targetLowerBoundEightThirtyOne_of_localClosedNeighborhoodDeletionEliminator
    (hdel : MinimalFailureLocalClosedNeighborhoodDeletionEliminator) :
    targetLowerBoundEightThirtyOne := by
  exact targetLowerBoundEightThirtyOne_of_degreeDeletionEliminator
    (degreeDeletionEliminator_of_localClosedNeighborhoodDeletionEliminator hdel)

end

end LocalDeletionConstructors
end Swanepoel
end ErdosProblems1066
