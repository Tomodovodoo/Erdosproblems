import ErdosProblems1066.Swanepoel.NoCutSourceInhabitationW21
import ErdosProblems1066.Swanepoel.PayForCutProducerFamilyW20
import ErdosProblems1066.Swanepoel.NoCutMinimalityProofW15
import ErdosProblems1066.Swanepoel.CutVertexSlackFromDeletion
import ErdosProblems1066.Swanepoel.CutVertexFinal

set_option autoImplicit false

/-!
# W22 no-cut minimality source inhabitation audit

This file records the exact W21 no-cut/pay-for-cut source boundary in the
minimality-selected spelling.  The ledger source, the W20 pay-for-cut producer,
the W19 no-cut field family, and the W15 minimality-selected pay-for-cut family
all carry the same content.

No unconditional no-cut theorem is introduced here.  A concrete supplied
cut-vertex partition still gives the sharp obstruction to each source.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutMinimalitySourceInhabitationW22

open CutVertexInterface
open MinimalGraphFacts

noncomputable section

abbrev SmallestMissingMinimalityNoCutTheorem : Prop :=
  NoCutSourceInhabitationW21.SmallestMissingMinimalityNoCutTheorem

abbrev LedgerNoCutSource : Prop :=
  NoCutSourceInhabitationW21.LedgerNoCutSource

abbrev LedgerPayForCutSource : Type 1 :=
  NoCutSourceInhabitationW21.LedgerPayForCutSource

abbrev W20PayForCutSource : Type 1 :=
  PayForCutProducerFamilyW20.PayForCutConcreteProducerFamily

abbrev W19PayForCutNoCutFieldFamily : Prop :=
  NoCutMinimalityClosureW19.PayForCutNoCutFieldFamily

abbrev W15MinimalitySelectedPayForCutFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      NoCutMinimalityProofW15.MinimalitySelectedPayForCut hmin

variable {n : Nat} {C : _root_.UDConfig n}

/-- The W21 missing theorem is definitionally the W19 family field. -/
theorem smallestMissing_iff_w19FieldFamily :
    SmallestMissingMinimalityNoCutTheorem <->
      W19PayForCutNoCutFieldFamily := by
  rfl

/-- The W21 missing theorem is also exactly the W15 minimality-selected
pay-for-cut family. -/
theorem smallestMissing_iff_w15MinimalitySelectedFamily :
    SmallestMissingMinimalityNoCutTheorem <->
      W15MinimalitySelectedPayForCutFamily := by
  rfl

/-- Ledger no-cut and the W21 named missing theorem are the same source. -/
theorem ledgerNoCutSource_iff_smallestMissing :
    LedgerNoCutSource <-> SmallestMissingMinimalityNoCutTheorem :=
  NoCutSourceInhabitationW21.ledgerNoCutSource_iff_smallestMissing

/-- The W20 producer spelling has the same nonempty content as the W21 named
missing theorem. -/
theorem nonempty_w20PayForCutSource_iff_smallestMissing :
    Nonempty W20PayForCutSource <->
      SmallestMissingMinimalityNoCutTheorem :=
  PayForCutProducerFamilyW20.nonempty_payForCutConcreteProducerFamily_iff_payForCutNoCutFieldFamily

/-- The ledger producer spelling has the same nonempty content as the W21
named missing theorem. -/
theorem nonempty_ledgerPayForCutSource_iff_smallestMissing :
    Nonempty LedgerPayForCutSource <->
      SmallestMissingMinimalityNoCutTheorem :=
  NoCutSourceInhabitationW21.nonempty_ledgerPayForCutSource_iff_smallestMissing

/-- The ledger producer and W20 producer are the same data, up to the consumer
namespace spelling. -/
def ledgerPayForCutSourceEquivW20 :
    Equiv LedgerPayForCutSource W20PayForCutSource where
  toFun := fun F => F
  invFun := fun F => F
  left_inv := by
    intro F
    rfl
  right_inv := by
    intro F
    rfl

def ledgerPayForCutSource_of_smallestMissing
    (H : SmallestMissingMinimalityNoCutTheorem) :
    LedgerPayForCutSource :=
  NoCutSourceInhabitationW21.ledgerPayForCutSource_of_smallestMissing H

def w20PayForCutSource_of_smallestMissing
    (H : SmallestMissingMinimalityNoCutTheorem) :
    W20PayForCutSource :=
  PayForCutProducerFamilyW20.payForCutConcreteProducerFamily_of_payForCutNoCutFieldFamily
    H

theorem smallestMissing_of_ledgerPayForCutSource
    (F : LedgerPayForCutSource) :
    SmallestMissingMinimalityNoCutTheorem :=
  NoCutSourceInhabitationW21.smallestMissing_of_ledgerPayForCutSource F

theorem smallestMissing_of_w20PayForCutSource
    (F : W20PayForCutSource) :
    SmallestMissingMinimalityNoCutTheorem :=
  PayForCutProducerFamilyW20.payForCutNoCutFieldFamily_of_payForCutConcreteProducerFamily
    F

theorem ledgerPayForCutSource_nonempty_iff_w20PayForCutSource_nonempty :
    Nonempty LedgerPayForCutSource <-> Nonempty W20PayForCutSource := by
  constructor
  case mp =>
    intro hF
    cases hF with
    | intro F =>
        exact Nonempty.intro (ledgerPayForCutSourceEquivW20 F)
  case mpr =>
    intro hF
    cases hF with
    | intro F =>
        exact Nonempty.intro (ledgerPayForCutSourceEquivW20.symm F)

theorem noCutVertex_of_smallestMissing
    (H : SmallestMissingMinimalityNoCutTheorem)
    (hmin : IsMinimalClearedFailure C) :
    NoCutVertex C :=
  NoCutMinimalityClosureW19.noCutVertex_of_payForCutNoCutField
    (C := C) (H C hmin)

theorem minimalitySelectedPayForCut_of_smallestMissing
    (H : SmallestMissingMinimalityNoCutTheorem)
    (hmin : IsMinimalClearedFailure C) :
    NoCutMinimalityProofW15.MinimalitySelectedPayForCut hmin :=
  H C hmin

theorem connected_of_smallestMissing
    (H : SmallestMissingMinimalityNoCutTheorem)
    (hmin : IsMinimalClearedFailure C) :
    (GraphBridge.unitDistanceSimpleGraph C).Connected :=
  NoCutMinimalityClosureW19.connected_of_payForCutNoCutField
    (C := C) (H C hmin)

theorem remainingSlackFact_nonempty_of_smallestMissing
    (H : SmallestMissingMinimalityNoCutTheorem)
    (hmin : IsMinimalClearedFailure C) :
    Nonempty (CutVertexFinal.RemainingNoCutSlackFact C) :=
  (CutVertexFinal.remainingNoCutSlackFact_nonempty_iff_noCutVertex_of_minimalFailure
    (C := C) hmin).2
    (noCutVertex_of_smallestMissing (C := C) H hmin)

theorem deletionSlackFact_of_smallestMissing
    (H : SmallestMissingMinimalityNoCutTheorem)
    (hmin : IsMinimalClearedFailure C) :
    CutVertexSlackFromDeletion.CutVertexDeletionSlackFact C :=
  (CutVertexSlackFromDeletion.deletionSlackFact_iff_noCutVertex_of_minimalFailure
    (C := C) hmin).2
    (noCutVertex_of_smallestMissing (C := C) H hmin)

theorem smallestMissing_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    SmallestMissingMinimalityNoCutTheorem :=
  NoCutSourceInhabitationW21.smallestMissing_of_minimalClearedFailureEliminator
    hElim

def ledgerPayForCutSource_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    LedgerPayForCutSource :=
  NoCutSourceInhabitationW21.ledgerPayForCutSource_of_minimalClearedFailureEliminator
    hElim

def w20PayForCutSource_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    W20PayForCutSource :=
  w20PayForCutSource_of_smallestMissing
    (smallestMissing_of_minimalClearedFailureEliminator hElim)

theorem cutVertexPartition_obstructs_smallestMissing
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not SmallestMissingMinimalityNoCutTheorem := by
  intro H
  exact
    (NoCutMinimalityClosureW19.cutVertexPartition_obstructs_payForCutNoCutField
      (C := C) hmin P) (H C hmin)

theorem cutVertexPartition_obstructs_ledgerPayForCutSource
    (F : LedgerPayForCutSource)
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    False :=
  cutVertexPartition_obstructs_smallestMissing (C := C) hmin P
    (smallestMissing_of_ledgerPayForCutSource F)

theorem cutVertexPartition_obstructs_w20PayForCutSource
    (F : W20PayForCutSource)
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    False :=
  PayForCutProducerFamilyW20.cutVertexPartition_obstructs_payForCutConcreteProducerFamily
    (C := C) F hmin P

theorem cutVertexPartition_obstructs_nonempty_ledgerPayForCutSource
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (Nonempty LedgerPayForCutSource) := by
  intro hF
  cases hF with
  | intro F =>
      exact cutVertexPartition_obstructs_ledgerPayForCutSource
        (C := C) F hmin P

theorem cutVertexPartition_obstructs_nonempty_w20PayForCutSource
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (Nonempty W20PayForCutSource) := by
  intro hF
  cases hF with
  | intro F =>
      exact cutVertexPartition_obstructs_w20PayForCutSource
        (C := C) F hmin P

theorem nonempty_cutVertexPartition_obstructs_smallestMissing
    (hmin : IsMinimalClearedFailure C)
    (hcut : Nonempty (CutVertexPartition C)) :
    Not SmallestMissingMinimalityNoCutTheorem := by
  cases hcut with
  | intro P =>
      exact cutVertexPartition_obstructs_smallestMissing (C := C) hmin P

theorem nonempty_cutVertexPartition_obstructs_ledgerPayForCutSource
    (hmin : IsMinimalClearedFailure C)
    (hcut : Nonempty (CutVertexPartition C)) :
    Not (Nonempty LedgerPayForCutSource) := by
  cases hcut with
  | intro P =>
      exact cutVertexPartition_obstructs_nonempty_ledgerPayForCutSource
        (C := C) hmin P

end

end NoCutMinimalitySourceInhabitationW22
end Swanepoel
end ErdosProblems1066
