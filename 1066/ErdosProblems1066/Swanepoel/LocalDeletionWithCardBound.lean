import ErdosProblems1066.Swanepoel.MinimalFailureLocalExclusions

/-!
# Local deletion certificates with a direct cardinal bound

This module packages concrete local deletion data into the general
`LocalDeletionCertificate` interface.  The smaller configuration is the induced
subconfiguration on the vertices outside the deleted set.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LocalDeletionWithCardBound

open InducedSubconfiguration
open MinimalCounterexample
open MinimalFailureLocalExclusions

noncomputable section

/-- Concrete local deletion data with the deletion-cardinality inequality
supplied directly. -/
structure LocalDeletionData {n : Nat} (C : _root_.UDConfig n) where
  deleted : Finset (Fin n)
  reinsertion : Finset (Fin n)
  closedNeighborhood : IsClosedNeighborhood C reinsertion deleted
  deletedCard : (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1
  reinsertionNonempty : reinsertion.Nonempty
  reinsertionCardUpper : reinsertion.card <= 8
  reinsertionIndep : C.IsIndep reinsertion

namespace LocalDeletionData

variable {n : Nat} {C : _root_.UDConfig n}

/-- The induced smaller configuration on the kept vertices. -/
def induced (L : LocalDeletionData C) :
    Induced (m := (keptAfterDeletion L.deleted).card)
      C (keptAfterDeletion L.deleted) :=
  InducedSubconfiguration.ofFinset C (keptAfterDeletion L.deleted)

/-- Turn concrete direct-card-bound local deletion data into the general
certificate used by the minimal-failure local-exclusion layer. -/
def toLocalDeletionCertificate (L : LocalDeletionData C) :
    LocalDeletionCertificate C L.induced.config where
  kept := L.induced.embed
  deleted := L.deleted
  reinsertion := L.reinsertion
  keptInjective := L.induced.embed_injective
  keptDeletedDisjoint := by
    rw [L.induced.image_univ]
    exact keptAfterDeletion_disjoint L.deleted
  cover := by
    rw [L.induced.image_univ]
    exact keptAfterDeletion_union_deleted L.deleted
  closedNeighborhood := L.closedNeighborhood
  deletedCard := L.deletedCard
  reinsertionNonempty := L.reinsertionNonempty
  reinsertionCardUpper := L.reinsertionCardUpper
  reinsertionIndep := L.reinsertionIndep
  preservesDistances := by
    intro small
    exact L.induced.preservesDistancesOn small

/-- Existence form for downstream local-rule constructors. -/
theorem exists_localDeletionCertificate (L : LocalDeletionData C) :
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (LocalDeletionCertificate C Csmall) := by
  exact
    ⟨(keptAfterDeletion L.deleted).card, L.induced.config,
      ⟨L.toLocalDeletionCertificate⟩⟩

end LocalDeletionData

/-- Tupled-input constructor for concrete local deletion rules with a direct
cardinality bound. -/
theorem exists_localDeletionCertificate_of_data
    {n : Nat} (C : _root_.UDConfig n)
    (deleted reinsertion : Finset (Fin n))
    (hclosed : IsClosedNeighborhood C reinsertion deleted)
    (hcard : (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1)
    (hnonempty : reinsertion.Nonempty)
    (hupper : reinsertion.card <= 8)
    (hindep : C.IsIndep reinsertion) :
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (LocalDeletionCertificate C Csmall) := by
  let L : LocalDeletionData C :=
    { deleted := deleted
      reinsertion := reinsertion
      closedNeighborhood := hclosed
      deletedCard := hcard
      reinsertionNonempty := hnonempty
      reinsertionCardUpper := hupper
      reinsertionIndep := hindep }
  exact L.exists_localDeletionCertificate

end

end LocalDeletionWithCardBound
end Swanepoel
end ErdosProblems1066
