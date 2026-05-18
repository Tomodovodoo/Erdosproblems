import ErdosProblems1066.Swanepoel.LocalDeletionWithCardBound
import ErdosProblems1066.Swanepoel.MinimalFailureClosure

/-!
# Eliminator from direct-card-bound local deletions

This module is a conditional, non-final closure layer.  It does not prove any
local geometry.  Instead, it says that if every minimal cleared failure supplies
tupled direct-card-bound deletion data, then the existing local-deletion
certificate contradiction eliminates minimal failures and therefore proves the
public Swanepoel `8 / 31` target.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LocalDeletionEliminatorWithCardBound

open MinimalFailureClosure
open MinimalFailureLocalExclusions
open MinimalGraphFacts

noncomputable section

/-- A generic certificate eliminator saying every minimal cleared failure has a
direct-card-bound local deletion certificate. -/
def MinimalFailureDirectCardBoundCertificateEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C ->
      Exists fun nSmall : Nat =>
        Exists fun Csmall : _root_.UDConfig nSmall =>
          Nonempty (LocalDeletionCertificate C Csmall)

/-- Tupled direct-card-bound local deletion data for every minimal cleared
failure supplies the certificate eliminator. -/
theorem directCardBoundCertificateEliminator_of_tupledDeletionData
    (hdel :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C ->
          Exists fun deleted : Finset (Fin n) =>
          Exists fun reinsertion : Finset (Fin n) =>
            MinimalCounterexample.IsClosedNeighborhood C reinsertion deleted /\
            (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 /\
            reinsertion.Nonempty /\
            reinsertion.card <= 8 /\
            C.IsIndep reinsertion) :
    MinimalFailureDirectCardBoundCertificateEliminator := by
  intro n C hmin
  rcases hdel C hmin with
    ⟨deleted, reinsertion, hclosed, hcard, hnonempty, hupper, hindep⟩
  exact
    LocalDeletionWithCardBound.exists_localDeletionCertificate_of_data
      C deleted reinsertion hclosed hcard hnonempty hupper hindep

/-- A direct-card-bound certificate eliminator rules out every minimal cleared
failure via the general `LocalDeletionCertificate` contradiction. -/
theorem no_minimalClearedFailure_of_directCardBoundCertificateEliminator
    (hdel : MinimalFailureDirectCardBoundCertificateEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  intro n C hmin
  rcases hdel C hmin with ⟨nSmall, Csmall, hcert⟩
  exact
    LocalDeletionCertificate.not_nonempty_localDeletionCertificate_of_minimalFailure
      (Csmall := Csmall) hmin hcert

/-- A direct-card-bound certificate eliminator proves the public Swanepoel
`8 / 31` target. -/
theorem targetLowerBoundEightThirtyOne_of_directCardBoundCertificateEliminator
    (hdel : MinimalFailureDirectCardBoundCertificateEliminator) :
    targetLowerBoundEightThirtyOne := by
  exact
    targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
      (no_minimalClearedFailure_of_directCardBoundCertificateEliminator hdel)

/-- Higher-level conditional eliminator from tupled direct-card-bound local
deletion data for every minimal cleared failure to the public Swanepoel
`8 / 31` target. -/
theorem targetLowerBoundEightThirtyOne_of_tupledDirectCardBoundDeletionData
    (hdel :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C ->
          Exists fun deleted : Finset (Fin n) =>
          Exists fun reinsertion : Finset (Fin n) =>
            MinimalCounterexample.IsClosedNeighborhood C reinsertion deleted /\
            (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 /\
            reinsertion.Nonempty /\
            reinsertion.card <= 8 /\
            C.IsIndep reinsertion) :
    targetLowerBoundEightThirtyOne := by
  exact
    targetLowerBoundEightThirtyOne_of_directCardBoundCertificateEliminator
      (directCardBoundCertificateEliminator_of_tupledDeletionData hdel)

end

end LocalDeletionEliminatorWithCardBound
end Swanepoel
end ErdosProblems1066
